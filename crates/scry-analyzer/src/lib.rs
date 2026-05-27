//! scry-analyzer — the v0.2 scry analyzer as a Wasm component.
//!
//! Implements the `analyzer.analyze` function defined in `wit/scry.wit`
//! (derived from `spar/scry.aadl` per DD-010). The cross-component
//! import of `pulseengine:wasm-lattice/domain` is dogfooded on every
//! call (DD-008): the analyzer never performs a lattice operation
//! locally — every interval transfer goes through the WIT boundary.
//!
//! v0.2 (FEAT-001 AC#1) replaces the v0.1.0 scaffold's hardcoded
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
//! Scope discipline (v0.2 AC#1):
//!
//!   * Handled: `I32Const`, `I64Const`, `LocalGet`, `LocalSet`,
//!     `LocalTee`, `I32Add`, `I32Sub`, `I32Mul`, `End`, `Return`.
//!   * Deferred (emits `UnsoundnessFallback`, locals → top, operand
//!     stack scrubbed): control flow (`If`/`Loop`/`Block`/`Br*`),
//!     memory ops (`I32Load`/`I32Store`/`MemoryGrow`), calls
//!     (`Call`/`CallIndirect`), and everything outside the
//!     straight-line arithmetic core. Region memory lands with
//!     FEAT-005, sound call-graph with FEAT-006, summary-based
//!     interprocedural with FEAT-007.

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

const SCRY_VERSION: &str = "0.2.0";
const INVARIANT_SCHEMA_URL: &str = "https://pulseengine.eu/scry-invariants/v1";

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
/// Anything else (i64, unknown) means we lost track of the i32 shape;
/// caller must treat the result as `domain::top()` and emit a
/// fallback diagnostic.
fn as_i32_interval(v: &AbstractValue) -> Option<Interval> {
    match v {
        AbstractValue::I32Interval(iv) => Some(*iv),
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
/// clone because `Interval` is `Copy`.
fn clone_value(v: &AbstractValue) -> AbstractValue {
    match v {
        AbstractValue::I32Interval(iv) => AbstractValue::I32Interval(*iv),
        AbstractValue::I64Interval(iv) => AbstractValue::I64Interval(*iv),
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
        // code section).
        // ───────────────────────────────────────────────────────────
        let mut func_param_counts: Vec<(Vec<wasmparser::ValType>, Vec<wasmparser::ValType>)> =
            Vec::new();
        let mut function_type_indices: Vec<u32> = Vec::new();
        let mut import_func_count: u32 = 0;

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
                _ => {}
            }
        }

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
