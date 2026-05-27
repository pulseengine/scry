//! scry-analyzer — the v0.3 scry analyzer as a Wasm component.
//!
//! Implements the `analyzer.analyze` function defined in `wit/scry.wit`
//! (derived from `spar/scry.aadl` per DD-010). The cross-component
//! import of `pulseengine:wasm-lattice/domain` is dogfooded on every
//! call (DD-008): the analyzer never performs a lattice operation
//! locally — every interval transfer (and region transfer, as of
//! v0.3) goes through the WIT boundary.
//!
//! v0.2 (FEAT-001 AC#1) replaced the v0.1.0 scaffold's hardcoded
//! invariant bundle with a real interval-domain abstract-interpretation
//! fixpoint:
//!
//!   1. Parse the input bytes as a Wasm Core Model module via
//!      `wasmparser`.
//!   2. For each function body, initialize abstract locals
//!      (parameters → `domain::top()`, declared locals →
//!      `domain::constant_i32(0)` per Wasm zero-init), walk
//!      straight-line arithmetic operators, and maintain an
//!      abstract operand stack.
//!   3. For every handled operator, emit a `ProgramPoint` snapshot
//!      of the locals after execution.
//!   4. SHA-256 the module bytes and report the digest as
//!      `invariant_bundle.module_sha256`.
//!
//! v0.3 (FEAT-005) adds the region-based memory domain on top of
//! v0.2. The narrow win: when an `i32.load` / `i32.store` (or
//! `i64.load` / `i64.store`) consumes an operand whose abstract
//! shape is a singleton i32 interval — the canonical "base +
//! constant offset" pattern Wasm compilers emit for stack-
//! allocated locals — the analyzer:
//!
//!   * synthesises a `region` (region-id derived from the base
//!     address, offset = singleton address interval) via the
//!     wasm-lattice's new `region-*` transfer functions,
//!   * checks the access `[addr, addr + width)` against the
//!     parsed memory section's declared page count, and
//!   * emits a precise diagnostic instead of v0.2's blanket
//!     `UnsoundnessFallback`:
//!       - `Info`: "bounds-check elision safe at pc=N" if the
//!         access is provably in-region (loom can drop the
//!         runtime bounds check);
//!       - `Warning`: "load at offset interval [X, Y] cannot
//!         be proven in-region — bounds-check elision unsafe"
//!         if the access escapes the declared memory.
//!
//! In both cases the loaded *value* is still `top` for v0.3 —
//! precise per-region content tracking lands with the summary-
//! based interprocedural extension (FEAT-007) or a richer
//! content domain in v0.4+. The locals are *not* scrubbed to
//! top in the region-aware path: soundness is preserved by the
//! `top` return value, and precision on other locals is
//! preserved. Non-singleton addresses still hit the v0.2
//! fallback (scrub + UnsoundnessFallback).
//!
//! Scope discipline (v0.3, this PR):
//!
//!   * Handled precisely: `I32Const`, `I64Const`, `LocalGet`,
//!     `LocalSet`, `LocalTee`, `I32Add`, `I32Sub`, `I32Mul`,
//!     `End`, `Return`. Region-aware: `I32Load`, `I32Store`,
//!     `I64Load`, `I64Store` (when the address operand is a
//!     singleton i32 interval).
//!   * Deferred (emits `UnsoundnessFallback`, locals → top,
//!     operand stack scrubbed): control flow (`If` / `Loop` /
//!     `Block` / `Br*`), `MemoryGrow`, `MemorySize`, calls
//!     (`Call` / `CallIndirect`), and everything outside the
//!     straight-line arithmetic + canonical memory core.
//!     Sound call-graph lands with FEAT-006, summary-based
//!     interprocedural with FEAT-007. The region domain itself
//!     gains per-region content tracking in v0.4+.

#![no_std]
extern crate alloc;

use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use wasmparser::{Operator, Parser, Payload};

use scry_analyzer_component_bindings::exports::pulseengine::scry::analyzer::{
    AbstractValue, AnalysisConfig, AnalysisResult, AnalyzeError, Diagnostic, DiagnosticSeverity,
    Guest, InvariantBundle, LocalInvariant, ProgramPoint,
};
use scry_analyzer_component_bindings::pulseengine::wasm_lattice::domain::{self, Interval};

struct Component;

const SCRY_VERSION: &str = "0.3.0";
const INVARIANT_SCHEMA_URL: &str = "https://pulseengine.eu/scry-invariants/v1";

/// Default Wasm linear-memory page size (64 KiB).
const WASM_PAGE_SIZE: u64 = 65536;

/// Per-region metadata the analyzer tracks alongside the abstract
/// state. v0.3 only records the byte-size upper bound of each
/// region; the per-region "contents" abstraction (what an
/// `i32.load` would actually return) is pessimistically `top`
/// and not tracked here. Lands richer in v0.4+ via FEAT-007
/// summaries or a dedicated content domain.
#[derive(Clone, Copy)]
struct RegionMeta {
    /// Upper bound (in bytes) on the region's size. Used by
    /// `region-in-bounds` to prove `[addr, addr + width)` is
    /// fully inside the region. For v0.3 a single region is
    /// allocated per module to cover all of declared linear
    /// memory; per-stack-frame regions land alongside FEAT-007.
    size_bytes: u64,
}

/// Per-function context for the abstract interpreter.
struct FuncCtx {
    /// Abstract locals (parameters first, then declared locals).
    locals: Vec<AbstractValue>,
    /// Abstract operand stack.
    operand_stack: Vec<AbstractValue>,
    /// Once we see an unsupported construct in a function, we stop
    /// emitting fresh program-points for it — the abstract state has
    /// become uninformative (all-top) and further records would just
    /// be noise.
    degraded: bool,
}

impl FuncCtx {
    fn new(locals: Vec<AbstractValue>) -> Self {
        Self {
            locals,
            operand_stack: Vec::new(),
            degraded: false,
        }
    }

    /// Drop the operand stack and widen every local to top. Used when
    /// we hit any operator outside the v0.2 AC#1 supported set —
    /// soundness over precision (REQ-001 / DD-005).
    fn scrub_to_top(&mut self) {
        for slot in self.locals.iter_mut() {
            *slot = AbstractValue::I32Interval(domain::top());
        }
        self.operand_stack.clear();
        self.degraded = true;
    }
}

/// Extract the inner `Interval` from an `AbstractValue::I32Interval`.
/// A `RegionPointer` also has an i32-shaped offset interval; for
/// arithmetic transfer functions that don't preserve region-ness
/// (`i32-sub`, `i32-mul`, etc.) we project to the plain offset
/// interval. Anything else (i64, unknown) means we lost track of
/// the i32 shape; caller must treat the result as `domain::top()`
/// and emit a fallback diagnostic.
fn as_i32_interval(v: &AbstractValue) -> Option<Interval> {
    match v {
        AbstractValue::I32Interval(iv) => Some(*iv),
        AbstractValue::RegionPointer(r) => Some(r.offset),
        _ => None,
    }
}

/// Snapshot the locals as a list of `LocalInvariant` records.
fn snapshot_locals(locals: &[AbstractValue]) -> Vec<LocalInvariant> {
    locals
        .iter()
        .enumerate()
        .map(|(i, v)| LocalInvariant {
            local_index: i as u32,
            value: clone_value(v),
        })
        .collect()
}

/// `AbstractValue` derives no Copy/Clone in the generated bindings (it
/// carries a Rust enum variant with a payload). Hand-roll a shallow
/// clone because `Interval` and `Region` are both `Copy`.
fn clone_value(v: &AbstractValue) -> AbstractValue {
    match v {
        AbstractValue::I32Interval(iv) => AbstractValue::I32Interval(*iv),
        AbstractValue::I64Interval(iv) => AbstractValue::I64Interval(*iv),
        AbstractValue::RegionPointer(r) => AbstractValue::RegionPointer(*r),
        AbstractValue::Unknown => AbstractValue::Unknown,
    }
}

impl Guest for Component {
    fn analyze(
        module_bytes: Vec<u8>,
        config: AnalysisConfig,
    ) -> Result<AnalysisResult, AnalyzeError> {
        if module_bytes.is_empty() {
            return Err(AnalyzeError::InvalidModule(
                "module bytes are empty".to_string(),
            ));
        }
        if let Some(threshold) = config.widening_threshold {
            if threshold == 0 {
                return Err(AnalyzeError::InvalidConfig(
                    "widening-threshold must be >= 1".to_string(),
                ));
            }
        }

        let mut diagnostics: Vec<Diagnostic> = Vec::new();

        // ───────────────────────────────────────────────────────────
        // Cross-component lattice probe (kept from v0.1 — DD-008).
        // If wac mis-wires the import we want a clear, early signal
        // before the analyzer tries any real transfer functions.
        // ───────────────────────────────────────────────────────────
        let probe = domain::constant_i32(42);
        let lattice_alive = probe.lo == 42 && probe.hi == 42;
        if lattice_alive {
            if config.emit_diagnostics {
                diagnostics.push(Diagnostic {
                    severity: DiagnosticSeverity::Info,
                    func_index: 0,
                    pc: 0,
                    message: format!(
                        "scry {} — wasm-lattice cross-component import alive",
                        SCRY_VERSION,
                    ),
                });
            }
        } else {
            // Mechanical soundness: if the lattice is broken we can't
            // produce sound invariants. Emit fallback and degrade.
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::UnsoundnessFallback,
                func_index: 0,
                pc: 0,
                message: format!(
                    "scry {} — wasm-lattice probe FAILED (constant_i32(42) returned [{}, {}]); \
                     all invariants degraded to top",
                    SCRY_VERSION, probe.lo, probe.hi,
                ),
            });
        }

        // ───────────────────────────────────────────────────────────
        // SHA-256 of the input bytes (FEAT-001 AC#1).
        // ───────────────────────────────────────────────────────────
        let module_sha256 = format!("{:x}", Sha256::digest(&module_bytes));

        // ───────────────────────────────────────────────────────────
        // First pass: collect function-type table + per-function
        // parameter counts (param_count = function-type's params).
        // Imports + locally-defined functions share the function-
        // index space; we only analyze defined functions (from the
        // code section). v0.3 also collects the memory section so
        // the region domain (FEAT-005) can prove `i32.load` /
        // `i32.store` accesses are in-bounds against the declared
        // page count.
        // ───────────────────────────────────────────────────────────
        let mut func_param_counts: Vec<(Vec<wasmparser::ValType>, Vec<wasmparser::ValType>)> =
            Vec::new();
        let mut function_type_indices: Vec<u32> = Vec::new();
        let mut import_func_count: u32 = 0;
        // Default-bound for the v0.3 region domain: when the module
        // has no memory section we leave this at 0 — any memory op
        // will then fall back per `region-in-bounds` returning
        // false, and the analyzer emits an appropriate Warning.
        // The first memory's declared minimum (in pages) is what
        // the region's `size_bytes` floor; we don't widen past it
        // until we see `memory.grow` (which currently still falls
        // back to UnsoundnessFallback per the v0.3 scope).
        let mut memory_min_bytes: u64 = 0;

        for payload in Parser::new(0).parse_all(&module_bytes) {
            let payload = payload.map_err(|e| {
                AnalyzeError::InvalidModule(format!("wasm parse failed (pre-pass): {e}"))
            })?;
            match payload {
                Payload::TypeSection(reader) => {
                    for rec_group in reader {
                        let rec_group = rec_group.map_err(|e| {
                            AnalyzeError::InvalidModule(format!("type section: {e}"))
                        })?;
                        for subtype in rec_group.into_types() {
                            if let wasmparser::CompositeInnerType::Func(ft) =
                                &subtype.composite_type.inner
                            {
                                let params: Vec<_> = ft.params().iter().copied().collect();
                                let results: Vec<_> = ft.results().iter().copied().collect();
                                func_param_counts.push((params, results));
                            } else {
                                // Non-func composite (struct/array) —
                                // pad so type-index arithmetic stays
                                // aligned.
                                func_param_counts.push((Vec::new(), Vec::new()));
                            }
                        }
                    }
                }
                Payload::ImportSection(reader) => {
                    for imp in reader.into_imports() {
                        let imp = imp.map_err(|e| {
                            AnalyzeError::InvalidModule(format!("import section: {e}"))
                        })?;
                        if matches!(imp.ty, wasmparser::TypeRef::Func(_)) {
                            import_func_count = import_func_count.saturating_add(1);
                        }
                    }
                }
                Payload::FunctionSection(reader) => {
                    for ty in reader {
                        let ty = ty.map_err(|e| {
                            AnalyzeError::InvalidModule(format!("function section: {e}"))
                        })?;
                        function_type_indices.push(ty);
                    }
                }
                Payload::MemorySection(reader) => {
                    // v0.3 region domain (FEAT-005): the first
                    // declared memory's minimum-pages count
                    // becomes the lower bound on the single
                    // "default" region's size. Multi-memory
                    // (post-MVP) is not yet supported — we use
                    // the first entry only.
                    let mut first = true;
                    for entry in reader {
                        let mem = entry.map_err(|e| {
                            AnalyzeError::InvalidModule(format!("memory section: {e}"))
                        })?;
                        if first {
                            memory_min_bytes = mem.initial.saturating_mul(WASM_PAGE_SIZE);
                            first = false;
                        }
                    }
                }
                _ => {}
            }
        }

        // The default region for v0.3: a single region representing
        // all of declared linear memory. Future v0.4+ work will
        // split this into per-frame regions via stack-pointer
        // tracking — for v0.3 a single region is enough to
        // demonstrate bounds-check elision on the canonical
        // base+offset pattern (fixture-03).
        let default_region_meta = RegionMeta {
            size_bytes: memory_min_bytes,
        };

        // ───────────────────────────────────────────────────────────
        // Second pass: walk the code section. We re-parse rather than
        // buffer payloads because wasmparser's Payload borrows from
        // the bytes and is awkward to stash.
        // ───────────────────────────────────────────────────────────
        let mut points: Vec<ProgramPoint> = Vec::new();
        let mut defined_func_idx: u32 = 0;

        for payload in Parser::new(0).parse_all(&module_bytes) {
            let payload = payload.map_err(|e| {
                AnalyzeError::InvalidModule(format!("wasm parse failed (code pass): {e}"))
            })?;
            if let Payload::CodeSectionEntry(body) = payload {
                let absolute_func_idx = import_func_count.saturating_add(defined_func_idx);

                // Resolve this function's signature so we know how
                // many params to mark as top.
                let type_idx = function_type_indices
                    .get(defined_func_idx as usize)
                    .copied()
                    .unwrap_or(u32::MAX);
                let (params, _results) = func_param_counts
                    .get(type_idx as usize)
                    .cloned()
                    .unwrap_or_default();

                // Build the initial abstract locals: each param →
                // top (we know nothing about caller-provided
                // arguments yet — v0.4 summary-based AI will
                // strengthen this), each declared local → zero per
                // Wasm semantics.
                let mut locals: Vec<AbstractValue> = Vec::with_capacity(params.len());
                for ty in &params {
                    locals.push(initial_abstract_for(*ty));
                }

                let locals_reader = body.get_locals_reader().map_err(|e| {
                    AnalyzeError::InvalidModule(format!("function {absolute_func_idx} locals: {e}"))
                })?;
                for entry in locals_reader {
                    let (count, ty) = entry.map_err(|e| {
                        AnalyzeError::InvalidModule(format!(
                            "function {absolute_func_idx} local entry: {e}"
                        ))
                    })?;
                    for _ in 0..count {
                        locals.push(zero_for(ty));
                    }
                }

                let mut ctx = FuncCtx::new(locals);

                let ops_reader = body.get_operators_reader().map_err(|e| {
                    AnalyzeError::InvalidModule(format!("function {absolute_func_idx} ops: {e}"))
                })?;

                let mut pc: u32 = 0;
                for op in ops_reader {
                    let op = op.map_err(|e| {
                        AnalyzeError::InvalidModule(format!(
                            "function {absolute_func_idx} op {pc}: {e}"
                        ))
                    })?;

                    let mut stop = false;
                    match interpret_op(
                        &op,
                        &mut ctx,
                        absolute_func_idx,
                        pc,
                        config.emit_diagnostics,
                        &mut diagnostics,
                        &default_region_meta,
                    )? {
                        StepOutcome::Continue => {}
                        StepOutcome::Stop => stop = true,
                    }

                    if !ctx.degraded {
                        points.push(ProgramPoint {
                            func_index: absolute_func_idx,
                            pc,
                            locals: snapshot_locals(&ctx.locals),
                        });
                    }

                    pc = pc.saturating_add(1);
                    if stop {
                        break;
                    }
                }

                defined_func_idx = defined_func_idx.saturating_add(1);
            }
        }

        let invariants = InvariantBundle {
            schema: INVARIANT_SCHEMA_URL.to_string(),
            module_sha256,
            points,
        };

        Ok(AnalysisResult {
            invariants,
            diagnostics,
        })
    }
}

enum StepOutcome {
    Continue,
    Stop,
}

/// Initial abstract value for a Wasm parameter of the given value
/// type. We don't know the caller's argument, so it's top in the
/// matching domain (intervals for i32/i64, Unknown for everything
/// else).
fn initial_abstract_for(ty: wasmparser::ValType) -> AbstractValue {
    match ty {
        wasmparser::ValType::I32 | wasmparser::ValType::I64 => {
            AbstractValue::I32Interval(domain::top())
        }
        _ => AbstractValue::Unknown,
    }
}

/// Initial abstract value for a declared local (Wasm zero-init).
fn zero_for(ty: wasmparser::ValType) -> AbstractValue {
    match ty {
        wasmparser::ValType::I32 => AbstractValue::I32Interval(domain::constant_i32(0)),
        wasmparser::ValType::I64 => AbstractValue::I64Interval(domain::constant_i64(0)),
        _ => AbstractValue::Unknown,
    }
}

/// Interpret one operator. Mutates `ctx` and may push diagnostics.
/// Returns whether the function loop should stop (e.g. `Return`).
fn interpret_op(
    op: &Operator<'_>,
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    default_region: &RegionMeta,
) -> Result<StepOutcome, AnalyzeError> {
    if ctx.degraded {
        // Once degraded, we still need to scan through to keep the
        // operator iterator advancing — but we don't update state.
        return Ok(StepOutcome::Continue);
    }

    match op {
        Operator::I32Const { value } => {
            ctx.operand_stack
                .push(AbstractValue::I32Interval(domain::constant_i32(*value)));
        }
        Operator::I64Const { value } => {
            ctx.operand_stack
                .push(AbstractValue::I64Interval(domain::constant_i64(*value)));
        }
        Operator::LocalGet { local_index } => {
            let v = ctx
                .locals
                .get(*local_index as usize)
                .map(clone_value)
                .ok_or_else(|| {
                    AnalyzeError::Internal(format!(
                        "func {func_index} pc {pc}: local.get {local_index} out of range \
                         (have {} locals)",
                        ctx.locals.len()
                    ))
                })?;
            ctx.operand_stack.push(v);
        }
        Operator::LocalSet { local_index } => {
            let v = ctx.operand_stack.pop().ok_or_else(|| {
                AnalyzeError::Internal(format!(
                    "func {func_index} pc {pc}: local.set on empty stack"
                ))
            })?;
            let local_count = ctx.locals.len();
            let slot = ctx.locals.get_mut(*local_index as usize).ok_or_else(|| {
                AnalyzeError::Internal(format!(
                    "func {func_index} pc {pc}: local.set {local_index} out of range \
                     (have {local_count} locals)"
                ))
            })?;
            *slot = v;
        }
        Operator::LocalTee { local_index } => {
            let v = ctx.operand_stack.last().map(clone_value).ok_or_else(|| {
                AnalyzeError::Internal(format!(
                    "func {func_index} pc {pc}: local.tee on empty stack"
                ))
            })?;
            let local_count = ctx.locals.len();
            let slot = ctx.locals.get_mut(*local_index as usize).ok_or_else(|| {
                AnalyzeError::Internal(format!(
                    "func {func_index} pc {pc}: local.tee {local_index} out of range \
                     (have {local_count} locals)"
                ))
            })?;
            *slot = v;
        }
        Operator::I32Add => {
            i32_binop(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                domain::i32_add,
            )?;
        }
        Operator::I32Sub => {
            i32_binop(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                domain::i32_sub,
            )?;
        }
        Operator::I32Mul => {
            i32_binop(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                domain::i32_mul,
            )?;
        }
        Operator::End => {
            // End of block / function — no state change at v0.2 AC#1.
        }
        Operator::Return => {
            return Ok(StepOutcome::Stop);
        }
        // ── v0.3 region-aware memory ops (FEAT-005) ──────────────
        Operator::I32Load { memarg } => {
            handle_memory_load(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                default_region,
                memarg.offset,
                4,
                /*pushed_kind=*/ MemValKind::I32,
                "i32.load",
            )?;
        }
        Operator::I64Load { memarg } => {
            handle_memory_load(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                default_region,
                memarg.offset,
                8,
                MemValKind::I64,
                "i64.load",
            )?;
        }
        Operator::I32Store { memarg } => {
            handle_memory_store(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                default_region,
                memarg.offset,
                4,
                "i32.store",
            )?;
        }
        Operator::I64Store { memarg } => {
            handle_memory_store(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                default_region,
                memarg.offset,
                8,
                "i64.store",
            )?;
        }
        other => {
            // Anything outside the v0.2 AC#1 set: emit a fallback
            // diagnostic, scrub state to top to preserve soundness
            // (REQ-001), and continue. Control flow, memory ops, and
            // calls all land here at v0.2; FEAT-005 / FEAT-006 /
            // FEAT-007 will replace these with real transfer
            // functions.
            if emit_diagnostics {
                diagnostics.push(Diagnostic {
                    severity: DiagnosticSeverity::UnsoundnessFallback,
                    func_index,
                    pc,
                    message: format!(
                        "unsupported operator at v0.2 AC#1: {} — locals degraded to top",
                        op_name(other)
                    ),
                });
            }
            ctx.scrub_to_top();
        }
    }
    Ok(StepOutcome::Continue)
}

/// Apply an i32 binary transfer function via the wasm-lattice
/// component import. Wasm operand order: top of stack is `b` (the
/// second operand), the one below is `a` (the first operand); the
/// transfer is `f(a, b)`.
fn i32_binop(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    f: fn(Interval, Interval) -> Interval,
) -> Result<(), AnalyzeError> {
    let b = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: i32 binop with empty stack"
        ))
    })?;
    let a = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: i32 binop with single operand"
        ))
    })?;
    match (as_i32_interval(&a), as_i32_interval(&b)) {
        (Some(ai), Some(bi)) => {
            let result = f(ai, bi);
            ctx.operand_stack.push(AbstractValue::I32Interval(result));
        }
        _ => {
            // One of the operands isn't an i32 interval — we lost
            // shape tracking somewhere. Widen to top and report.
            if emit_diagnostics {
                diagnostics.push(Diagnostic {
                    severity: DiagnosticSeverity::UnsoundnessFallback,
                    func_index,
                    pc,
                    message: "i32 binop on non-i32-interval operand — pushing top".to_string(),
                });
            }
            ctx.operand_stack
                .push(AbstractValue::I32Interval(domain::top()));
        }
    }
    Ok(())
}

/// Which kind of value an `i*.load` pushes onto the operand stack.
/// v0.3 always returns `top` for the loaded value (precise per-
/// region content tracking lands in v0.4+); this enum only tells
/// `handle_memory_load` which `AbstractValue` variant to push.
#[derive(Clone, Copy)]
enum MemValKind {
    I32,
    I64,
}

/// Region-id derivation from a singleton base address. v0.3 uses a
/// pure function so the same base address consistently maps to the
/// same region across program points — a future v0.4+ may switch
/// to per-allocation freshness, at which point this becomes a
/// counter maintained on `FuncCtx`.
fn region_id_for(addr: i64) -> u32 {
    addr as u32
}

/// True iff the byte range `[addr_lo, addr_hi + width)` fits
/// entirely inside a region of `size_bytes` bytes (the address
/// interval may be a singleton, in which case `addr_lo ==
/// addr_hi`). Returns `false` for any overflow or out-of-range
/// case — caller treats `false` as "cannot prove in-region".
fn region_in_bounds(addr_lo: i64, addr_hi: i64, width: u64, size_bytes: u64) -> bool {
    if addr_lo < 0 || addr_hi < 0 {
        return false;
    }
    let lo = addr_lo as u64;
    let Some(hi_plus_width) = (addr_hi as u64).checked_add(width) else {
        return false;
    };
    lo < size_bytes && hi_plus_width <= size_bytes
}

/// Handle a v0.3 region-aware load (`i32.load` / `i64.load`).
/// Pops the address operand and:
///
///   * if it's a singleton i32 interval (the canonical
///     base+offset pattern from `i32.const A; i32.const k;
///     i32.add`), synthesises a region pointer via the
///     wasm-lattice's `region-create` + `region-offset` ops,
///     proves the access is in-bounds against the default
///     region, emits an `Info` (in-bounds) or `Warning` (out-
///     of-bounds) diagnostic, and pushes `top` as the loaded
///     value — locals are NOT scrubbed, soundness preserved by
///     the top return value;
///   * if it's a non-singleton i32 interval, conservatively
///     widens the address to its full interval, performs the
///     in-bounds check on `[lo, hi + width)`, emits the same
///     diagnostics, pushes `top`;
///   * otherwise (i64 / unknown address shape), falls through
///     to v0.2 behaviour: scrub locals to top + emit
///     `UnsoundnessFallback`.
#[allow(clippy::too_many_arguments)]
fn handle_memory_load(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    default_region: &RegionMeta,
    static_offset: u64,
    width: u64,
    pushed_kind: MemValKind,
    op_label: &'static str,
) -> Result<(), AnalyzeError> {
    let addr_v = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: {op_label} on empty stack"
        ))
    })?;

    // Pull out the i32-interval shape (region-pointer offsets
    // count, per `as_i32_interval`). i64 / unknown → fallback.
    let Some(addr_iv) = as_i32_interval(&addr_v) else {
        if emit_diagnostics {
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::UnsoundnessFallback,
                func_index,
                pc,
                message: format!(
                    "{op_label} on non-i32-shaped address operand — locals degraded to top"
                ),
            });
        }
        ctx.scrub_to_top();
        return Ok(());
    };

    // Apply the static memarg offset via the wasm-lattice's
    // interval add (dogfooded per DD-008). Result lives in the
    // same i64 space we use for intervals.
    let offset_iv = domain::constant_i32(static_offset as i32);
    let effective = domain::i32_add(addr_iv, offset_iv);

    // Synthesise a region pointer for the access and check
    // bounds. The region-id is derived from the (singleton) base
    // address when one is recoverable; otherwise we still use
    // the default region for in-bounds proof purposes.
    let region = domain::region_create(region_id_for(effective.lo));
    let region = domain::region_offset(region, effective);
    let _ = region; // synthesised for soundness story; not currently consumed past this point.

    let in_bounds = region_in_bounds(effective.lo, effective.hi, width, default_region.size_bytes);

    if in_bounds {
        if emit_diagnostics {
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::Info,
                func_index,
                pc,
                message: format!(
                    "{op_label} bounds-check elision safe at pc={pc}: access \
                     [{}, {}) fits in default region of {} bytes",
                    effective.lo,
                    effective.hi.saturating_add(width as i64),
                    default_region.size_bytes,
                ),
            });
        }
    } else if emit_diagnostics {
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Warning,
            func_index,
            pc,
            message: format!(
                "{op_label} at offset interval [{}, {}] cannot be proven \
                 in-region — bounds-check elision unsafe (default region \
                 size = {} bytes, load width = {})",
                effective.lo, effective.hi, default_region.size_bytes, width,
            ),
        });
    }

    // The loaded value itself is `top` for v0.3 (per-region
    // content tracking lands in v0.4+).
    let loaded = match pushed_kind {
        MemValKind::I32 => AbstractValue::I32Interval(domain::top()),
        MemValKind::I64 => AbstractValue::I64Interval(domain::top()),
    };
    ctx.operand_stack.push(loaded);
    Ok(())
}

/// Handle a v0.3 region-aware store (`i32.store` / `i64.store`).
/// Pops the value (top of stack) then the address (below). On
/// recognised address shape, emits the same Info/Warning
/// diagnostics as the load path; v0.3 doesn't model per-region
/// content so the stored value is dropped on the floor (sound
/// over-approximation: any subsequent load returns `top`
/// anyway). Non-i32-shaped address → v0.2 fallback.
#[allow(clippy::too_many_arguments)]
fn handle_memory_store(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    default_region: &RegionMeta,
    static_offset: u64,
    width: u64,
    op_label: &'static str,
) -> Result<(), AnalyzeError> {
    // Stack order: address is pushed first, value second; pop value first.
    let _value_v = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: {op_label} with empty stack (no value)"
        ))
    })?;
    let addr_v = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: {op_label} missing address operand"
        ))
    })?;

    let Some(addr_iv) = as_i32_interval(&addr_v) else {
        if emit_diagnostics {
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::UnsoundnessFallback,
                func_index,
                pc,
                message: format!(
                    "{op_label} on non-i32-shaped address operand — locals degraded to top"
                ),
            });
        }
        ctx.scrub_to_top();
        return Ok(());
    };

    let offset_iv = domain::constant_i32(static_offset as i32);
    let effective = domain::i32_add(addr_iv, offset_iv);
    // Synthesise the region pointer + check bounds. v0.3 doesn't
    // need the region for anything past this diagnostic, but the
    // dogfooded call exercises the WIT path (DD-008) and keeps
    // wac-composition wiring honest.
    let region = domain::region_create(region_id_for(effective.lo));
    let _ = domain::region_offset(region, effective);

    let in_bounds = region_in_bounds(effective.lo, effective.hi, width, default_region.size_bytes);

    if in_bounds {
        if emit_diagnostics {
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::Info,
                func_index,
                pc,
                message: format!(
                    "{op_label} bounds-check elision safe at pc={pc}: access \
                     [{}, {}) fits in default region of {} bytes",
                    effective.lo,
                    effective.hi.saturating_add(width as i64),
                    default_region.size_bytes,
                ),
            });
        }
    } else if emit_diagnostics {
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Warning,
            func_index,
            pc,
            message: format!(
                "{op_label} at offset interval [{}, {}] cannot be proven \
                 in-region — bounds-check elision unsafe (default region \
                 size = {} bytes, store width = {})",
                effective.lo, effective.hi, default_region.size_bytes, width,
            ),
        });
    }
    // Per v0.3 scope, stored value is not modelled. Sound.
    Ok(())
}

/// Coarse human-readable name for an operator. wasmparser's
/// `Operator` doesn't derive `Display`; the `Debug` impl is verbose
/// (full payloads) and tends to balloon diagnostic strings. The set
/// below is the one we expect to see most often via the fallback
/// path; anything else falls through to a debug-ish label.
fn op_name(op: &Operator<'_>) -> &'static str {
    match op {
        Operator::Unreachable => "unreachable",
        Operator::Nop => "nop",
        Operator::Block { .. } => "block",
        Operator::Loop { .. } => "loop",
        Operator::If { .. } => "if",
        Operator::Else => "else",
        Operator::Br { .. } => "br",
        Operator::BrIf { .. } => "br_if",
        Operator::BrTable { .. } => "br_table",
        Operator::Call { .. } => "call",
        Operator::CallIndirect { .. } => "call_indirect",
        Operator::Drop => "drop",
        Operator::Select => "select",
        Operator::GlobalGet { .. } => "global.get",
        Operator::GlobalSet { .. } => "global.set",
        Operator::I32Load { .. } => "i32.load",
        Operator::I32Store { .. } => "i32.store",
        Operator::MemorySize { .. } => "memory.size",
        Operator::MemoryGrow { .. } => "memory.grow",
        Operator::I32DivS => "i32.div_s",
        Operator::I32DivU => "i32.div_u",
        Operator::I32RemS => "i32.rem_s",
        Operator::I32RemU => "i32.rem_u",
        Operator::I32And => "i32.and",
        Operator::I32Or => "i32.or",
        Operator::I32Xor => "i32.xor",
        Operator::I32Shl => "i32.shl",
        Operator::I32ShrS => "i32.shr_s",
        Operator::I32ShrU => "i32.shr_u",
        Operator::I32Eq => "i32.eq",
        Operator::I32Ne => "i32.ne",
        Operator::I32Eqz => "i32.eqz",
        _ => "<unsupported>",
    }
}

scry_analyzer_component_bindings::export!(Component with_types_in scry_analyzer_component_bindings);
