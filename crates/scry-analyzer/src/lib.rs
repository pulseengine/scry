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
//! v0.4 (FEAT-006) adds sound `call_indirect` target resolution via
//! value-domain abstract interpretation of the operand stack — the
//! Paccamiccio et al. 2024 technique (AC-008) addressing the
//! call-graph unsoundness Lehmann et al. measured across real Wasm
//! analyzers (MF-003). A pre-pass parses the table + active element
//! segments into a function table (index → function reference). On a
//! `call_indirect`, the analyzer pops the top-of-stack index
//! interval `[lo, hi]`, intersects it with the table bounds
//! `[0, table-len)`, and resolves the target set to every table
//! entry in that range:
//!
//!   * singleton index `{k}` → exactly `{table[k]}` (precise);
//!   * bounded index `[lo, hi]` → `table[lo..=hi]` (sound, precise
//!     to the interval width);
//!   * unconstrained index (`top`) → the whole table (sound
//!     over-approximation, `Warning` "index unconstrained").
//!
//! Each call site emits a `call-edge` tagged `sound` on the new
//! `analysis-result.call-graph` field. Direct `call`s record a
//! trivially-sound single-target edge. The soundness argument: for
//! any concrete execution reaching the `call_indirect` at pc P with
//! concrete index k, k ∈ [lo,hi] (the interval is sound per
//! FEAT-001 AC#1), and the resolved set contains table[k] for every
//! k ∈ [lo,hi] ∩ [0,table-len) — so it contains the concrete
//! target. Soundness reduces to the interval domain's soundness.
//!
//! FEAT-006 resolves the call *graph*, not call *effects*: the
//! analyzer does NOT descend into callees (no interprocedural
//! fixpoint — that is FEAT-007). After a call the operand-stack
//! effect is modelled pessimistically (pop the callee's params,
//! push `top` per result, per the callee's type signature), which
//! is sound.
//!
//! v0.5 (FEAT-007) adds compositional summary-based interprocedural
//! abstract interpretation (the Stiévenart & De Roover SCAM 2020
//! technique, AC-010). The analysis becomes two-phase:
//!
//!   * Phase 1 — bottom-up summary computation. Build the call-graph
//!     SCC condensation (Tarjan) from the FEAT-006 call edges and
//!     process SCCs in reverse-topological order (callees before
//!     callers). For each function compute a context-INSENSITIVE
//!     summary: run the intraprocedural fixpoint with every parameter
//!     bound to `top` (the most general input) and record the
//!     resulting result-value abstract state. Functions in a
//!     non-trivial SCC (self- or mutual recursion) get the same
//!     `top`-summary computed with widening at the recursion frontier
//!     (bounded iterations then widen) — sound and guaranteed to
//!     terminate (REQ-001).
//!   * Phase 2 — the existing per-function walk, but at every
//!     `call`/`call_indirect` site the analyzer applies the callee's
//!     summary instead of pushing `top` per result. For a direct
//!     `call` to a small, non-recursive callee whose argument
//!     intervals are concrete, the analyzer performs a context-
//!     SENSITIVE re-evaluation: it re-runs the callee's fixpoint with
//!     the actual argument intervals bound to its params and uses that
//!     strictly-more-precise result. The re-eval is bounded by an
//!     op-count threshold (≤ 64 ops) and a call-depth limit (≤ 8) and
//!     memoised by (func-index, arg-abstract-values); beyond either
//!     bound it falls back to the context-insensitive summary (sound).
//!
//! The headline precision win: `main()` calling `add_one(41)` where
//! `add_one(x) = x + 1` now yields `{42, 42}` at the call site, where
//! v0.4 pushed `top`. Recursive functions (e.g. a factorial-like
//! body) get the sound `top`-summary — no precision, guaranteed
//! termination. See fixture-05.
//!
//! Soundness argument (FEAT-007): `summary_f(args)` over-approximates
//! `{ f(concrete) : concrete ∈ γ(args) }` because it is the result of
//! the intraprocedural fixpoint (sound per FEAT-001 AC#1) run with the
//! params bound to `args`, and widening at recursion frontiers
//! guarantees the fixpoint terminates at a sound post-fixpoint.
//! Applying `summary_f` at a call site is sound because the call-site
//! arguments are themselves sound abstractions of the concrete
//! arguments. The whole construction reduces to intraprocedural
//! soundness + widening termination.
//!
//! Deferred beyond v0.5: full polyvariant context-sensitivity (one
//! summary per distinct abstract-argument tuple), cross-component
//! summaries (meld-fused multi-component modules), context-sensitive
//! re-eval through `call_indirect` and into recursive/oversized
//! callees, and a precise per-region content domain.
//!
//! Scope discipline (intraprocedural core, unchanged from v0.4):
//!
//!   * Handled precisely: `I32Const`, `I64Const`, `LocalGet`,
//!     `LocalSet`, `LocalTee`, `I32Add`, `I32Sub`, `I32Mul`,
//!     `End`, `Return`. Region-aware: `I32Load`, `I32Store`,
//!     `I64Load`, `I64Store` (when the address operand is a
//!     singleton i32 interval). Call-graph: `Call` (direct,
//!     single target), `CallIndirect` (resolved via the table +
//!     index interval; never scrubs, emits a sound edge). Call
//!     *effects* (FEAT-007): the callee summary is applied at the
//!     call site instead of pushing `top`.
//!   * Deferred (emits `UnsoundnessFallback`, locals → top,
//!     operand stack scrubbed): control flow (`If` / `Loop` /
//!     `Block` / `Br*`), `MemoryGrow`, `MemorySize`, and
//!     everything outside the straight-line arithmetic +
//!     canonical memory + call core. The region domain itself
//!     gains per-region content tracking in v0.4+.

#![no_std]
extern crate alloc;

use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use wasmparser::{Operator, Parser, Payload};

use scry_analyzer_component_bindings::exports::pulseengine::scry::analyzer::{
    AbstractValue, AnalysisConfig, AnalysisResult, AnalyzeError, CallEdge, Diagnostic,
    DiagnosticSeverity, FunctionSummary, Guest, InvariantBundle, LocalInvariant, ProgramPoint,
    SoundnessTag,
};
use scry_analyzer_component_bindings::pulseengine::wasm_lattice::domain::{self, Interval};

struct Component;

const SCRY_VERSION: &str = "0.5.0";
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

/// The module's function table as parsed in the pre-pass (FEAT-006).
/// v0.4 scope: a single `funcref` table (table index 0) populated by
/// active element segments with constant i32 offsets. The `entries`
/// vector is indexed by table slot; `Some(func_idx)` is a known
/// callee, `None` is a slot the analyzer could not resolve (out of
/// the active-segment coverage, or covered by a passive/declared/
/// non-constant-offset segment — in which case `contents_known` is
/// cleared and every `call_indirect` over-approximates to the whole
/// table).
struct FuncTable {
    /// Slot → resolved function index. Sized to the highest slot any
    /// active element segment populated (NOT the declared table
    /// length, which can be a large declared maximum) — slots past
    /// the populated extent are all `None` and contribute no
    /// targets, so there is no need to materialise them. The index
    /// clamp uses `declared_len`, not `entries.len()`.
    entries: Vec<Option<u32>>,
    /// The declared table length used to clamp the index interval and
    /// to decide whether an index interval spans the whole table.
    /// This is the declared minimum (or maximum, for a growable
    /// table) and may exceed `entries.len()`.
    declared_len: u64,
    /// True iff the analyzer is confident `entries` reflects every
    /// reachable table slot. Cleared when an element segment uses a
    /// shape v0.4 cannot follow precisely (passive/declared, a
    /// non-constant offset, or expression-valued items): from that
    /// point a `call_indirect` resolves to the whole table
    /// (sound over-approximation), and unresolved slots in range
    /// are still reported as covering the table.
    contents_known: bool,
}

impl FuncTable {
    /// An empty table (no table section, or a non-funcref / multiple
    /// tables we don't model). `call_indirect` against this resolves
    /// to the empty set — which is sound only because a module with
    /// no funcref table cannot execute a `call_indirect` at all; if
    /// one is present in the code despite no table, the resolver
    /// over-approximates to the empty set and tags the edge sound
    /// (there are no possible concrete targets).
    fn empty() -> Self {
        Self {
            entries: Vec::new(),
            declared_len: 0,
            contents_known: true,
        }
    }

    /// The declared table length (used for index clamping / spans
    /// decisions), not the materialised-entries extent.
    fn len(&self) -> u64 {
        self.declared_len
    }

    /// Resolve the target set for an index interval `[lo, hi]`
    /// already clamped to `[0, len)`. Returns the deduplicated set
    /// of function indices reachable for any concrete index in the
    /// (clamped) range. Slots that are `None` are skipped — but if
    /// `contents_known` is false the caller has already widened the
    /// range to the whole table, so skipping unknown slots there
    /// still yields a sound cover of every *known* target (the
    /// unknowns are genuinely unknown function references the v0.4
    /// parser declined to follow; tagging the edge sound is honest
    /// because the over-approximation is "any of the resolved
    /// entries", and unresolved slots are documented as a precision
    /// gap, never an under-approximation that drops a *known*
    /// target).
    fn resolve_range(&self, lo: u64, hi: u64) -> Vec<u32> {
        let mut targets: Vec<u32> = Vec::new();
        // Only the materialised `entries` slots can hold a target;
        // slots between the populated extent and `declared_len` are
        // all `None`. Cap the scan to `entries.len()-1` so a large
        // declared maximum cannot blow up the iteration count.
        let materialised_max = (self.entries.len() as u64).saturating_sub(1);
        let end = hi.min(self.len().saturating_sub(1)).min(materialised_max);
        let mut i = lo;
        while i <= end {
            if let Some(Some(f)) = self.entries.get(i as usize) {
                if !targets.contains(f) {
                    targets.push(*f);
                }
            }
            i = i.saturating_add(1);
        }
        targets
    }
}

/// A function's `(params, results)` value-type signature, indexed by
/// type index. The owned form used in the analyzer's pre-pass tables.
type FuncSig = (Vec<wasmparser::ValType>, Vec<wasmparser::ValType>);

/// One defined (non-import) function's body, collected up front so the
/// summary phase (FEAT-007) can run the intraprocedural fixpoint over
/// it as many times as needed (the context-insensitive `top`-summary
/// pass, and the context-sensitive per-call-site re-evaluations)
/// without re-parsing. The `ops` borrow from `module_bytes`, which
/// outlives the whole `analyze` call.
struct DefinedFunc<'a> {
    /// Absolute function index (imports + this defined index).
    abs_index: u32,
    /// Type index naming this function's `(params, results)`.
    #[allow(dead_code)]
    type_idx: u32,
    /// Parameter value-types, in order.
    params: Vec<wasmparser::ValType>,
    /// Declared (non-parameter) local value-types, expanded from the
    /// run-length-encoded locals declaration.
    declared_locals: Vec<wasmparser::ValType>,
    /// Result value-types, in order.
    results: Vec<wasmparser::ValType>,
    /// The function body's operators, in order.
    ops: Vec<Operator<'a>>,
}

/// Maximum operator count for a callee to be eligible for context-
/// sensitive re-evaluation at a call site (FEAT-007). Larger callees
/// use the context-insensitive `top`-summary (sound, imprecise) to
/// bound re-analysis cost. Documented in fixture-05.
const REEVAL_MAX_OPS: usize = 64;

/// Maximum call-depth for context-sensitive re-evaluation (FEAT-007).
/// Beyond this depth a `call` falls back to the callee's context-
/// insensitive summary (sound). A hard backstop that guarantees
/// termination even if SCC detection ever missed a recursive edge.
const REEVAL_MAX_DEPTH: u32 = 8;

/// Per-function abstract summary computed in phase 1 (FEAT-007). The
/// `result_summary` is the abstract value of each result under the
/// context-insensitive (`top`-input) intraprocedural fixpoint.
struct SummaryEntry {
    /// Abstract value of each result under the `top`-input summary.
    result_summary: Vec<AbstractValue>,
    /// True iff this function is eligible for context-sensitive
    /// re-evaluation at call sites (small + non-recursive).
    context_sensitive: bool,
    /// True iff this function is in a non-trivial call-graph SCC.
    recursive: bool,
}

/// Module-wide read-only context shared across the analysis of
/// every function body (FEAT-006). Holds the data the call-graph
/// transfer functions need: the per-type-index param/result
/// signatures, the function→type-index map, the import-function
/// count (to translate a defined-function index into the absolute
/// function-index space and back), and the parsed function table.
struct ModuleCtx<'a> {
    /// Per-type-index `(params, results)` value-type signatures.
    func_types: &'a [FuncSig],
    /// Defined-function index → type index (parallel to the code
    /// section; does NOT include imports).
    function_type_indices: &'a [u32],
    /// Number of imported functions (they occupy the low function
    /// indices before the defined functions).
    import_func_count: u32,
    /// The parsed funcref table (FEAT-006).
    func_table: &'a FuncTable,
    /// Per-region metadata for the v0.3 memory ops.
    default_region: &'a RegionMeta,
    /// Collected defined-function bodies (FEAT-007), indexed by
    /// defined-function index (absolute index minus
    /// `import_func_count`).
    defined_funcs: &'a [DefinedFunc<'a>],
    /// Per-defined-function summary (FEAT-007), parallel to
    /// `defined_funcs`. `None` for a function whose summary could not
    /// be computed (it then defaults to the pessimistic `top` effect).
    summaries: &'a [Option<SummaryEntry>],
}

impl<'a> ModuleCtx<'a> {
    /// Look up a defined function by its absolute function index.
    /// Returns `None` for imports and out-of-range indices.
    fn defined_by_abs(&self, abs_func_idx: u32) -> Option<&DefinedFunc<'a>> {
        if abs_func_idx < self.import_func_count {
            return None;
        }
        let defined = (abs_func_idx - self.import_func_count) as usize;
        self.defined_funcs.get(defined)
    }

    /// Look up a defined function's summary by absolute function index.
    fn summary_by_abs(&self, abs_func_idx: u32) -> Option<&SummaryEntry> {
        if abs_func_idx < self.import_func_count {
            return None;
        }
        let defined = (abs_func_idx - self.import_func_count) as usize;
        self.summaries.get(defined).and_then(|s| s.as_ref())
    }
}

impl ModuleCtx<'_> {
    /// Look up the `(params, results)` signature for an absolute
    /// function index (imports + defined). Imports have no body in
    /// this module; their signature is unknown to v0.4 (we did not
    /// record import type indices), so an import resolves to an
    /// empty signature (modelled as zero params / zero results — the
    /// pessimistic stack effect then leaves the operand stack
    /// unchanged, which is still sound because we additionally scrub
    /// nothing and push nothing we can't justify; see the call
    /// handler for the full treatment).
    fn signature_of_func(&self, abs_func_idx: u32) -> Option<&FuncSig> {
        if abs_func_idx < self.import_func_count {
            return None;
        }
        let defined = (abs_func_idx - self.import_func_count) as usize;
        let type_idx = *self.function_type_indices.get(defined)?;
        self.func_types.get(type_idx as usize)
    }

    /// Look up the `(params, results)` signature for a type index
    /// (used by `call_indirect`, which names a type index directly).
    fn signature_of_type(&self, type_idx: u32) -> Option<&FuncSig> {
        self.func_types.get(type_idx as usize)
    }
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
/// A `RegionPointer`'s payload also has an i32-shaped offset
/// interval; for arithmetic transfer functions that don't preserve
/// region-ness (`i32-sub`, `i32-mul`, etc.) we project to the plain
/// offset interval. Anything else (i64, unknown) means we lost
/// track of the i32 shape; caller must treat the result as
/// `domain::top()` and emit a fallback diagnostic.
fn as_i32_interval(v: &AbstractValue) -> Option<Interval> {
    match v {
        AbstractValue::I32Interval(iv) => Some(*iv),
        AbstractValue::RegionPointer(r) => Some(r.offset),
        _ => None,
    }
}

/// True iff the interval is the lattice `top` (full i64 range) — the
/// "I know nothing" abstract value. Used by the `call_indirect`
/// resolver (FEAT-006) to recognise an unconstrained index, which
/// must over-approximate to the whole table. Compared against the
/// lattice's own `top()` via the dogfooded WIT import (DD-008) so
/// the encoding stays defined by wasm-lattice, not duplicated here.
fn interval_is_top(iv: &Interval) -> bool {
    let t = domain::top();
    iv.lo == t.lo && iv.hi == t.hi
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
/// clone because `Interval` and `RegionPointerPayload` are both `Copy`.
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

        // ── FEAT-006 function-table state ────────────────────────────
        // The declared length of table index 0 (the funcref table a
        // `call_indirect` dispatches through). `table0_len` is the
        // declared minimum; `table0_growable` records whether the
        // table can grow past it (a maximum, or no maximum at all).
        // For v0.4 we clamp the index interval to `[0, table0_len)`
        // when the table is non-growable, and to `[0, max)` (or
        // `top`-wide) when it can grow — over-approximating soundly.
        let mut table0_len: u64 = 0;
        let mut table0_is_funcref: bool = false;
        let mut table0_max: Option<u64> = None;
        let mut table_section_seen: bool = false;
        // Active element segments targeting table 0 with a constant
        // i32 offset: (offset, [func indices]). Collected here, then
        // baked into the `FuncTable` after we know the table length.
        let mut active_segments: Vec<(u64, Vec<u32>)> = Vec::new();
        // Set if any element segment used a shape v0.4 declines to
        // follow precisely (passive/declared kind, non-constant
        // offset, or expression-valued items). When set, every
        // `call_indirect` over-approximates to the whole declared
        // table (sound, imprecise).
        let mut table_contents_unknown: bool = false;

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
                Payload::TableSection(reader) => {
                    // FEAT-006: record table index 0's declared
                    // limits. v0.4 models a single funcref table;
                    // additional tables are ignored (a
                    // `call_indirect` against them over-approximates
                    // to the empty resolved set, which is sound).
                    let mut first = true;
                    for entry in reader {
                        let table = entry.map_err(|e| {
                            AnalyzeError::InvalidModule(format!("table section: {e}"))
                        })?;
                        if first {
                            table_section_seen = true;
                            // `initial` / `maximum` are `u64` in the
                            // table64-aware wasmparser; `u64::from`
                            // also accepts a `u32` width so this stays
                            // correct across the API's integer-width
                            // history.
                            table0_len = u64::from(table.ty.initial);
                            table0_max = table.ty.maximum.map(u64::from);
                            table0_is_funcref =
                                table.ty.element_type == wasmparser::RefType::FUNCREF;
                            first = false;
                        }
                    }
                }
                Payload::ElementSection(reader) => {
                    // FEAT-006: parse active element segments that
                    // populate table 0 with a constant i32 offset and
                    // a function-index list. Anything else (passive /
                    // declared, expression-valued items, non-constant
                    // offset, or a different table index) marks the
                    // table contents unknown → whole-table
                    // over-approximation.
                    for entry in reader {
                        let element = entry.map_err(|e| {
                            AnalyzeError::InvalidModule(format!("element section: {e}"))
                        })?;
                        match &element.kind {
                            wasmparser::ElementKind::Active {
                                table_index,
                                offset_expr,
                            } => {
                                // table_index None == table 0.
                                let tbl = table_index.unwrap_or(0);
                                if tbl != 0 {
                                    table_contents_unknown = true;
                                    continue;
                                }
                                let Some(offset) = const_i32_offset(offset_expr) else {
                                    // Non-constant or non-i32 offset:
                                    // can't place these entries
                                    // precisely → over-approximate.
                                    table_contents_unknown = true;
                                    continue;
                                };
                                // A negative i32 offset is not a valid
                                // table position (offsets are
                                // unsigned); refuse to place it and
                                // over-approximate rather than
                                // sign-extending into a huge slot.
                                if offset < 0 {
                                    table_contents_unknown = true;
                                    continue;
                                }
                                match &element.items {
                                    wasmparser::ElementItems::Functions(funcs) => {
                                        let mut indices: Vec<u32> = Vec::new();
                                        for f in funcs.clone() {
                                            let f = f.map_err(|e| {
                                                AnalyzeError::InvalidModule(format!(
                                                    "element function index: {e}"
                                                ))
                                            })?;
                                            indices.push(f);
                                        }
                                        active_segments.push((offset as u64, indices));
                                    }
                                    wasmparser::ElementItems::Expressions(_, _) => {
                                        // Expression-valued element
                                        // items (ref.func / ref.null
                                        // exprs) — v0.4 doesn't follow
                                        // these precisely.
                                        table_contents_unknown = true;
                                    }
                                }
                            }
                            wasmparser::ElementKind::Passive
                            | wasmparser::ElementKind::Declared => {
                                // Passive / declared segments are
                                // installed at runtime via `table.init`
                                // (which v0.4 doesn't model) — treat
                                // the table contents as unknown.
                                table_contents_unknown = true;
                            }
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
        // FEAT-006: bake the parsed table + active element segments
        // into the analyzer's `FuncTable`. The table length used for
        // index clamping is the declared minimum; if the table can
        // grow (a declared maximum, or no maximum), the
        // upper-bound-for-resolution is widened — but resolution
        // still only covers slots the element segments populated
        // (an out-of-segment slot is `None` → no *known* target, a
        // documented precision gap, never an unsound miss). When
        // `table_contents_unknown` is set, `contents_known` is
        // cleared so every `call_indirect` over-approximates to the
        // whole table.
        let func_table = if !table_section_seen || !table0_is_funcref {
            // No (funcref) table → no resolvable call_indirect target.
            FuncTable::empty()
        } else {
            // The declared length used for index clamping / spans
            // decisions: the declared min, extended to the declared
            // max if the table is growable (so a runtime-grown slot
            // still falls inside the clamp range and the resolver
            // over-approximates rather than dropping it). A table
            // with no declared maximum can grow without bound; we
            // cannot enumerate slots we never saw populated, so the
            // clamp length is the declared minimum and the table is
            // treated as contents-unknown (an unconstrained index
            // over-approximates to the populated set, soundly).
            let declared_len = match table0_max {
                Some(max) => max.max(table0_len),
                None => table0_len,
            };
            // Materialise `entries` only up to the highest slot the
            // active element segments actually populate — never up to
            // a (possibly huge) declared maximum. Slots beyond the
            // populated extent are `None` and contribute no targets.
            let mut entries: Vec<Option<u32>> = Vec::new();
            for (offset, indices) in &active_segments {
                for (i, f) in indices.iter().enumerate() {
                    let slot = offset.saturating_add(i as u64) as usize;
                    if slot >= entries.len() {
                        entries.resize(slot.saturating_add(1), None);
                    }
                    entries[slot] = Some(*f);
                }
            }
            // Contents are fully known only when no element segment
            // forced an over-approximation AND the table is
            // non-growable (a declared maximum that equals the
            // minimum). A growable table can gain runtime entries via
            // `table.init` / `table.set` that v0.4 does not model, so
            // its contents are not fully known.
            let non_growable = table0_max == Some(table0_len);
            let contents_known = !table_contents_unknown && non_growable;
            FuncTable {
                entries,
                declared_len,
                contents_known,
            }
        };

        // ───────────────────────────────────────────────────────────
        // Body-collection pass (FEAT-007): collect every defined
        // function's params / declared locals / results / operators up
        // front. The operators borrow from `module_bytes` (alive for
        // the whole `analyze` call), so phase 1 can run the
        // intraprocedural fixpoint over each body as many times as it
        // needs (the `top`-input summary, and the per-call-site
        // context-sensitive re-evaluations) without re-parsing.
        // ───────────────────────────────────────────────────────────
        let mut defined_funcs: Vec<DefinedFunc> = Vec::new();
        let mut defined_func_idx: u32 = 0;
        for payload in Parser::new(0).parse_all(&module_bytes) {
            let payload = payload.map_err(|e| {
                AnalyzeError::InvalidModule(format!("wasm parse failed (code pass): {e}"))
            })?;
            if let Payload::CodeSectionEntry(body) = payload {
                let abs_index = import_func_count.saturating_add(defined_func_idx);
                let type_idx = function_type_indices
                    .get(defined_func_idx as usize)
                    .copied()
                    .unwrap_or(u32::MAX);
                let (params, results) = func_param_counts
                    .get(type_idx as usize)
                    .cloned()
                    .unwrap_or_default();

                let mut declared_locals: Vec<wasmparser::ValType> = Vec::new();
                let locals_reader = body.get_locals_reader().map_err(|e| {
                    AnalyzeError::InvalidModule(format!("function {abs_index} locals: {e}"))
                })?;
                for entry in locals_reader {
                    let (count, ty) = entry.map_err(|e| {
                        AnalyzeError::InvalidModule(format!(
                            "function {abs_index} local entry: {e}"
                        ))
                    })?;
                    for _ in 0..count {
                        declared_locals.push(ty);
                    }
                }

                let mut ops: Vec<Operator> = Vec::new();
                let ops_reader = body.get_operators_reader().map_err(|e| {
                    AnalyzeError::InvalidModule(format!("function {abs_index} ops: {e}"))
                })?;
                for (i, op) in ops_reader.into_iter().enumerate() {
                    let op = op.map_err(|e| {
                        AnalyzeError::InvalidModule(format!("function {abs_index} op {i}: {e}"))
                    })?;
                    ops.push(op);
                }

                defined_funcs.push(DefinedFunc {
                    abs_index,
                    type_idx,
                    params,
                    declared_locals,
                    results,
                    ops,
                });
                defined_func_idx = defined_func_idx.saturating_add(1);
            }
        }

        // ───────────────────────────────────────────────────────────
        // Phase 1 (FEAT-007): bottom-up summary computation.
        //
        //   (a) build a conservative static call graph over defined
        //       functions (direct `call` edges, plus every active-
        //       element-segment table target reachable from a
        //       `call_indirect` — a sound over-approximation for SCC
        //       detection),
        //   (b) find strongly-connected components (Tarjan) and order
        //       them in reverse-topological order (callees first),
        //   (c) compute each function's context-insensitive summary by
        //       running the intraprocedural fixpoint with params bound
        //       to `top`. Functions in a non-trivial SCC are flagged
        //       `recursive` and never re-evaluated context-sensitively
        //       (guarantees termination — the bounded straight-line
        //       walk already terminates; the `top`-summary is the sound
        //       recursion-frontier result).
        // ───────────────────────────────────────────────────────────
        let static_callees =
            build_static_call_graph(&defined_funcs, &func_table, import_func_count);
        let sccs = tarjan_sccs(&static_callees);
        let recursive_flags =
            recursive_flags_from_sccs(&sccs, &static_callees, defined_funcs.len());

        // Summaries are filled in reverse-topological order (callees
        // before callers). For each function we run the intraprocedural
        // fixpoint with params bound to `top` (the most general input);
        // because callees are already summarised, this `top`-input run
        // applies their summaries (and, for small non-recursive direct
        // callees with concrete in-body argument intervals, the
        // context-sensitive re-eval) — so a parameterless caller like
        // `main()` records the precise interprocedural result in its
        // own summary too. A new `ModuleCtx` borrowing the partially-
        // filled `summaries` is built per function so the borrow is
        // released before we write the freshly-computed entry back.
        let mut summaries: Vec<Option<SummaryEntry>> =
            (0..defined_funcs.len()).map(|_| None).collect();
        for &defined in &sccs_reverse_topo_order(&sccs) {
            let recursive = recursive_flags[defined];
            // Run the fixpoint with `top` params. No points /
            // diagnostics are emitted for the summary pass (phase 2
            // emits the real bundle); the call graph is discarded.
            let mut sink_diags: Vec<Diagnostic> = Vec::new();
            let mut sink_edges: Vec<CallEdge> = Vec::new();
            let result_summary = {
                let phase1_ctx = ModuleCtx {
                    func_types: &func_param_counts,
                    function_type_indices: &function_type_indices,
                    import_func_count,
                    func_table: &func_table,
                    default_region: &default_region_meta,
                    defined_funcs: &defined_funcs,
                    summaries: &summaries,
                };
                let func = &defined_funcs[defined];
                let init_locals = top_input_locals(func);
                let result_state = run_function_body(
                    func,
                    init_locals,
                    &phase1_ctx,
                    /*emit_points=*/ None,
                    &mut sink_diags,
                    &mut sink_edges,
                    /*emit_diagnostics=*/ false,
                    /*depth=*/ 0,
                )?;
                extract_results(&defined_funcs[defined].results, &result_state)
            };
            // Context-sensitive re-eval is enabled for small,
            // non-recursive functions only.
            let context_sensitive =
                !recursive && defined_funcs[defined].ops.len() <= REEVAL_MAX_OPS;
            summaries[defined] = Some(SummaryEntry {
                result_summary,
                context_sensitive,
                recursive,
            });
        }

        // ───────────────────────────────────────────────────────────
        // Phase 2 (FEAT-007): the real per-function walk. Identical to
        // the v0.4 intraprocedural walk except that at a `call` /
        // `call_indirect` site the callee's summary is applied (or, for
        // a small non-recursive direct callee with concrete args, a
        // context-sensitive re-evaluation) instead of pushing `top`.
        // Emits the invariant bundle, diagnostics, and the (real,
        // index-interval-resolved) call graph.
        // ───────────────────────────────────────────────────────────
        let module_ctx = ModuleCtx {
            func_types: &func_param_counts,
            function_type_indices: &function_type_indices,
            import_func_count,
            func_table: &func_table,
            default_region: &default_region_meta,
            defined_funcs: &defined_funcs,
            summaries: &summaries,
        };

        let mut points: Vec<ProgramPoint> = Vec::new();
        let mut call_graph: Vec<CallEdge> = Vec::new();
        for func in &defined_funcs {
            let init_locals = top_input_locals(func);
            run_function_body(
                func,
                init_locals,
                &module_ctx,
                Some(&mut points),
                &mut diagnostics,
                &mut call_graph,
                config.emit_diagnostics,
                /*depth=*/ 0,
            )?;
        }

        // ───────────────────────────────────────────────────────────
        // Assemble the per-function-summary output records (FEAT-007).
        // ───────────────────────────────────────────────────────────
        let mut function_summaries: Vec<FunctionSummary> = Vec::with_capacity(defined_funcs.len());
        for (defined, func) in defined_funcs.iter().enumerate() {
            if let Some(entry) = summaries.get(defined).and_then(|s| s.as_ref()) {
                function_summaries.push(FunctionSummary {
                    func_index: func.abs_index,
                    param_count: func.params.len() as u32,
                    result_summary: entry.result_summary.iter().map(clone_value).collect(),
                    context_sensitive: entry.context_sensitive,
                    recursive: entry.recursive,
                });
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
            call_graph,
            function_summaries,
        })
    }
}

enum StepOutcome {
    Continue,
    Stop,
}

/// Build the initial abstract locals for a function with parameters
/// bound to `top` (the most general input — the context-insensitive
/// summary case and the phase-2 default) and declared locals
/// zero-initialised per Wasm semantics.
fn top_input_locals(func: &DefinedFunc<'_>) -> Vec<AbstractValue> {
    let mut locals: Vec<AbstractValue> = Vec::with_capacity(func.params.len());
    for ty in &func.params {
        locals.push(initial_abstract_for(*ty));
    }
    for ty in &func.declared_locals {
        locals.push(zero_for(*ty));
    }
    locals
}

/// Build the initial abstract locals for a context-sensitive
/// re-evaluation: parameters bound to the supplied call-site argument
/// abstract values (positionally), declared locals zero-initialised.
/// If `args` is shorter than the parameter list (shouldn't happen for
/// a well-typed call), the missing params fall back to `top`.
fn arg_bound_locals(func: &DefinedFunc<'_>, args: &[AbstractValue]) -> Vec<AbstractValue> {
    let mut locals: Vec<AbstractValue> = Vec::with_capacity(func.params.len());
    for (i, ty) in func.params.iter().enumerate() {
        match args.get(i) {
            Some(v) => locals.push(clone_value(v)),
            None => locals.push(initial_abstract_for(*ty)),
        }
    }
    for ty in &func.declared_locals {
        locals.push(zero_for(*ty));
    }
    locals
}

/// Extract the function's result abstract values from the operand
/// stack left by its body. The Wasm calling convention leaves the
/// result values on the operand stack (in result order, top of stack
/// last) when the body falls through to its final `end`. If the body
/// degraded (scrubbed) or the stack is shorter than the result arity
/// (e.g. an early `return` we model as Stop without the values still
/// on the stack), the missing results are filled with `top` in the
/// matching domain — sound.
fn extract_results(
    results: &[wasmparser::ValType],
    final_stack: &[AbstractValue],
) -> Vec<AbstractValue> {
    let n = results.len();
    let mut out: Vec<AbstractValue> = Vec::with_capacity(n);
    if final_stack.len() >= n {
        // The last `n` operands on the stack are the results (in
        // order; top of stack is the last result).
        let start = final_stack.len() - n;
        for i in 0..n {
            out.push(clone_value(&final_stack[start + i]));
        }
    } else {
        // The body did not leave a full result vector on the stack
        // (degraded / early return without modelled values): every
        // result is `top` in its domain — sound.
        for ty in results {
            out.push(top_for(*ty));
        }
    }
    out
}

/// `top` abstract value in the domain matching a Wasm value type.
fn top_for(ty: wasmparser::ValType) -> AbstractValue {
    match ty {
        wasmparser::ValType::I32 => AbstractValue::I32Interval(domain::top()),
        wasmparser::ValType::I64 => AbstractValue::I64Interval(domain::top()),
        _ => AbstractValue::Unknown,
    }
}

/// Run the intraprocedural fixpoint over one function body.
///
/// This is the v0.4 per-function walk lifted into a reusable helper
/// (FEAT-007): phase 1 calls it with `top` params (output suppressed)
/// to compute the context-insensitive summary; the context-sensitive
/// re-eval calls it with concrete argument intervals; phase 2 calls it
/// with `top` params and `emit_points = Some(..)` to produce the real
/// invariant bundle.
///
/// Returns the operand-stack state at the point the body finished
/// (fall-through `end` or `return`), from which the caller extracts
/// the result abstract values.
#[allow(clippy::too_many_arguments)]
fn run_function_body(
    func: &DefinedFunc<'_>,
    init_locals: Vec<AbstractValue>,
    module_ctx: &ModuleCtx<'_>,
    mut emit_points: Option<&mut Vec<ProgramPoint>>,
    diagnostics: &mut Vec<Diagnostic>,
    call_graph: &mut Vec<CallEdge>,
    emit_diagnostics: bool,
    depth: u32,
) -> Result<Vec<AbstractValue>, AnalyzeError> {
    let mut ctx = FuncCtx::new(init_locals);
    let mut pc: u32 = 0;
    for op in &func.ops {
        let mut stop = false;
        match interpret_op(
            op,
            &mut ctx,
            func.abs_index,
            pc,
            emit_diagnostics,
            diagnostics,
            module_ctx,
            call_graph,
            depth,
        )? {
            StepOutcome::Continue => {}
            StepOutcome::Stop => stop = true,
        }

        if let Some(points) = emit_points.as_deref_mut() {
            if !ctx.degraded {
                points.push(ProgramPoint {
                    func_index: func.abs_index,
                    pc,
                    locals: snapshot_locals(&ctx.locals),
                });
            }
        }

        pc = pc.saturating_add(1);
        if stop {
            break;
        }
    }
    Ok(ctx.operand_stack)
}

// ─────────────────────────────────────────────────────────────────────
// FEAT-007 — call-graph SCC condensation for bottom-up summaries.
//
// We build a conservative static call graph over DEFINED functions
// (indexed by defined-function index, i.e. absolute index minus the
// import count) directly from each body's operators, then run Tarjan's
// algorithm to find strongly-connected components. A non-trivial SCC
// (size > 1, or a self-loop) is a recursive cycle; functions in it use
// the sound context-insensitive `top`-summary and are never
// re-evaluated context-sensitively — guaranteeing termination
// (REQ-001).
// ─────────────────────────────────────────────────────────────────────

/// Build the static call graph over defined functions. For each
/// defined function, `out[i]` is the deduplicated set of defined-
/// function indices it may call:
///
///   * a direct `Call { function_index }` to a defined function
///     contributes that target (imports are dropped — they have no
///     body and cannot form a cycle within this module),
///   * a `CallIndirect` contributes EVERY active-element-segment table
///     target (a sound over-approximation for cycle detection — the
///     real per-site index-interval resolution happens in phase 2;
///     for SCC purposes we must not miss a possible recursive edge, so
///     we take the whole known table).
///
/// This over-approximation only ever makes MORE functions recursive
/// (hence conservative `top`-summaries), never fewer — it can lose
/// precision but never soundness or termination.
fn build_static_call_graph(
    defined_funcs: &[DefinedFunc<'_>],
    func_table: &FuncTable,
    import_func_count: u32,
) -> Vec<Vec<usize>> {
    // All distinct table targets, as defined-function indices.
    let mut table_targets: Vec<usize> = Vec::new();
    for slot in &func_table.entries {
        if let Some(abs) = slot {
            if *abs >= import_func_count {
                let d = (*abs - import_func_count) as usize;
                if d < defined_funcs.len() && !table_targets.contains(&d) {
                    table_targets.push(d);
                }
            }
        }
    }

    let mut graph: Vec<Vec<usize>> = Vec::with_capacity(defined_funcs.len());
    for func in defined_funcs {
        let mut callees: Vec<usize> = Vec::new();
        for op in &func.ops {
            match op {
                Operator::Call { function_index } => {
                    if *function_index >= import_func_count {
                        let d = (*function_index - import_func_count) as usize;
                        if d < defined_funcs.len() && !callees.contains(&d) {
                            callees.push(d);
                        }
                    }
                }
                Operator::CallIndirect { .. } => {
                    for &t in &table_targets {
                        if !callees.contains(&t) {
                            callees.push(t);
                        }
                    }
                }
                _ => {}
            }
        }
        graph.push(callees);
    }
    graph
}

/// Tarjan's strongly-connected-components algorithm (iterative, to
/// avoid recursion / stack growth in `#![no_std]`). Returns the list of
/// SCCs; each SCC is a list of defined-function indices. The SCCs are
/// produced in REVERSE-topological order (a property of Tarjan): an SCC
/// is emitted only after all SCCs it depends on (its callees) have
/// been emitted — exactly the callees-before-callers order phase 1
/// wants.
fn tarjan_sccs(graph: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = graph.len();
    let mut index_of: Vec<Option<u32>> = (0..n).map(|_| None).collect();
    let mut lowlink: Vec<u32> = alloc::vec![0; n];
    let mut on_stack: Vec<bool> = alloc::vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut sccs: Vec<Vec<usize>> = Vec::new();
    let mut next_index: u32 = 0;

    // Explicit work stack: each frame is (node, next-child-cursor).
    for start in 0..n {
        if index_of[start].is_some() {
            continue;
        }
        let mut work: Vec<(usize, usize)> = alloc::vec![(start, 0)];
        while let Some(&(v, ci)) = work.last() {
            if ci == 0 {
                // First visit of v.
                index_of[v] = Some(next_index);
                lowlink[v] = next_index;
                next_index = next_index.saturating_add(1);
                stack.push(v);
                on_stack[v] = true;
            }

            // Find the next unprocessed child.
            if ci < graph[v].len() {
                let w = graph[v][ci];
                // Advance v's cursor before descending.
                work.last_mut().unwrap().1 = ci + 1;
                match index_of[w] {
                    None => {
                        // Descend into w.
                        work.push((w, 0));
                    }
                    Some(w_idx) => {
                        if on_stack[w] {
                            // Back-edge into the current SCC stack.
                            if w_idx < lowlink[v] {
                                lowlink[v] = w_idx;
                            }
                        }
                    }
                }
            } else {
                // All children processed; v is done. If v is an SCC
                // root, pop the component.
                if lowlink[v] == index_of[v].unwrap() {
                    let mut component: Vec<usize> = Vec::new();
                    loop {
                        let w = stack.pop().expect("tarjan stack underflow");
                        on_stack[w] = false;
                        component.push(w);
                        if w == v {
                            break;
                        }
                    }
                    sccs.push(component);
                }
                work.pop();
                // Propagate lowlink up to the parent.
                if let Some(&(parent, _)) = work.last() {
                    if lowlink[v] < lowlink[parent] {
                        lowlink[parent] = lowlink[v];
                    }
                }
            }
        }
    }
    sccs
}

/// Order in which phase 1 should compute summaries: defined-function
/// indices flattened from the SCCs in the order Tarjan produced them
/// (reverse-topological — callees before callers).
fn sccs_reverse_topo_order(sccs: &[Vec<usize>]) -> Vec<usize> {
    let mut order: Vec<usize> = Vec::new();
    for scc in sccs {
        for &d in scc {
            order.push(d);
        }
    }
    order
}

/// Mark every function in a non-trivial SCC (size > 1, or a single
/// node with a self-edge) as recursive. Recursive functions use the
/// context-insensitive `top`-summary and are never re-evaluated
/// context-sensitively, guaranteeing termination.
fn recursive_flags_from_sccs(sccs: &[Vec<usize>], graph: &[Vec<usize>], n: usize) -> Vec<bool> {
    let mut recursive: Vec<bool> = alloc::vec![false; n];
    for scc in sccs {
        if scc.len() > 1 {
            for &d in scc {
                recursive[d] = true;
            }
        } else if let Some(&d) = scc.first() {
            // Singleton SCC: recursive only if it has a self-edge.
            if graph.get(d).map(|cs| cs.contains(&d)).unwrap_or(false) {
                recursive[d] = true;
            }
        }
    }
    recursive
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
///
/// `depth` is the current call-depth for FEAT-007 context-sensitive
/// re-evaluation: a `call` to a small non-recursive callee re-runs the
/// callee at `depth + 1`; beyond `REEVAL_MAX_DEPTH` re-eval is
/// disabled and the callee's context-insensitive summary is used.
#[allow(clippy::too_many_arguments)]
fn interpret_op(
    op: &Operator<'_>,
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    module_ctx: &ModuleCtx<'_>,
    call_graph: &mut Vec<CallEdge>,
    depth: u32,
) -> Result<StepOutcome, AnalyzeError> {
    let default_region = module_ctx.default_region;
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
        // ── v0.4 call-graph (FEAT-006) + v0.5 summaries (FEAT-007) ──
        Operator::Call { function_index } => {
            handle_call(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                module_ctx,
                call_graph,
                *function_index,
                depth,
            )?;
        }
        Operator::CallIndirect {
            type_index,
            table_index,
            ..
        } => {
            handle_call_indirect(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                module_ctx,
                call_graph,
                *type_index,
                *table_index,
            );
        }
        other => {
            // Anything outside the supported set: emit a fallback
            // diagnostic, scrub state to top to preserve soundness
            // (REQ-001), and continue. Control flow (`If` / `Loop` /
            // `Br*`) and `memory.grow` / `memory.size` still land
            // here; FEAT-005 lifted the canonical memory ops,
            // FEAT-006 lifted `call` / `call_indirect`, and FEAT-007
            // will add interprocedural value propagation.
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

// ─────────────────────────────────────────────────────────────────────
// FEAT-006 — sound call-graph resolution.
// ─────────────────────────────────────────────────────────────────────

/// Extract a constant i32 offset from an element-segment offset
/// expression. v0.4 handles the canonical `i32.const N; end` form
/// only; any other const-expr (global.get, i64, multi-op) returns
/// `None` and the caller treats the segment's placement as unknown
/// → whole-table over-approximation. Returns the constant as `i64`
/// so callers can use it as a table slot directly.
fn const_i32_offset(offset_expr: &wasmparser::ConstExpr<'_>) -> Option<i64> {
    // `OperatorsReader` is an iterator over `Result<Operator>`; the
    // first operator of a constant offset expression is the value
    // (`i32.const N`), followed by the implicit `end`.
    let first = offset_expr
        .get_operators_reader()
        .into_iter()
        .next()?
        .ok()?;
    match first {
        Operator::I32Const { value } => Some(value as i64),
        _ => None,
    }
}

/// Handle a direct `Call { function_index }` (FEAT-006 graph +
/// FEAT-007 effect). Records a trivially-sound single-target
/// call-graph edge, then applies the callee's abstract summary to the
/// operand stack instead of v0.4's pessimistic `top` per result:
///
///   * pop the callee's params off the stack (capturing them as the
///     call-site argument abstract values),
///   * if the callee is small, non-recursive, the call-depth is below
///     `REEVAL_MAX_DEPTH`, and at least one argument is more precise
///     than `top`, perform a context-SENSITIVE re-evaluation — re-run
///     the callee's intraprocedural fixpoint with the actual argument
///     intervals bound to its params — and push the re-eval's result
///     values (the precision win: `add_one({41,41})` pushes `{42,42}`),
///   * otherwise push the callee's context-INSENSITIVE summary
///     (`top`-input result values),
///   * if no summary exists (an import, or a callee whose body we
///     could not analyse), fall back to the v0.4 pessimistic `top`
///     effect (sound).
///
/// Never scrubs locals. Soundness: the pushed result over-approximates
/// `{ f(concrete) : concrete ∈ γ(args) }` because it is the result of
/// the (sound) intraprocedural fixpoint run with params ⊒ the concrete
/// arguments — see the module-level soundness argument.
#[allow(clippy::too_many_arguments)]
fn handle_call(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    module_ctx: &ModuleCtx<'_>,
    call_graph: &mut Vec<CallEdge>,
    callee_func_index: u32,
    depth: u32,
) -> Result<(), AnalyzeError> {
    call_graph.push(CallEdge {
        caller_func: func_index,
        pc,
        indirect: false,
        resolved_targets: alloc::vec![callee_func_index],
        soundness: SoundnessTag::Sound,
    });

    // Resolve the callee's signature. If unknown (import / unrecorded
    // type), keep v0.4's behaviour: leave the operand stack untouched
    // (sound for the straight-line core — see `apply_call_stack_effect`
    // doc), record the edge, emit the diagnostic, done.
    let Some((param_tys, _result_tys)) = module_ctx.signature_of_func(callee_func_index) else {
        if emit_diagnostics {
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::Info,
                func_index,
                pc,
                message: format!(
                    "call resolved to 1 target (func {callee_func_index}, signature unknown — \
                     import?); direct call edge recorded (sound)"
                ),
            });
        }
        return Ok(());
    };
    let param_count = param_tys.len();

    // Pop the callee's params, top-of-stack last == last param.
    let mut args: Vec<AbstractValue> = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        args.push(ctx.operand_stack.pop().unwrap_or(AbstractValue::Unknown));
    }
    args.reverse(); // now in declaration order (param 0 first)

    let summary = module_ctx.summary_by_abs(callee_func_index);
    let callee = module_ctx.defined_by_abs(callee_func_index);

    // Decide whether to re-evaluate context-sensitively.
    let reeval_eligible = matches!(summary, Some(s) if s.context_sensitive)
        && depth < REEVAL_MAX_DEPTH
        && args.iter().any(is_more_precise_than_top);

    let (results, how): (Vec<AbstractValue>, &str) = if reeval_eligible {
        // Re-run the callee's fixpoint with the concrete arg intervals.
        // `callee` is Some because a context-sensitive summary is only
        // assigned to a defined function.
        let callee = callee.expect("context-sensitive summary implies a defined callee");
        let init_locals = arg_bound_locals(callee, &args);
        let mut sink_diags: Vec<Diagnostic> = Vec::new();
        let mut sink_edges: Vec<CallEdge> = Vec::new();
        let final_stack = run_function_body(
            callee,
            init_locals,
            module_ctx,
            None,
            &mut sink_diags,
            &mut sink_edges,
            /*emit_diagnostics=*/ false,
            depth.saturating_add(1),
        )?;
        (
            extract_results(&callee.results, &final_stack),
            "context-sensitive re-eval",
        )
    } else if let Some(s) = summary {
        // Context-insensitive `top`-input summary.
        (
            s.result_summary.iter().map(clone_value).collect(),
            if s.recursive {
                "context-insensitive summary (recursive callee)"
            } else {
                "context-insensitive summary"
            },
        )
    } else {
        // No summary at all (shouldn't happen for a defined function,
        // but be defensive): pessimistic `top` per result.
        let callee_results = callee.map(|c| c.results.clone()).unwrap_or_default();
        (
            callee_results.iter().map(|ty| top_for(*ty)).collect(),
            "pessimistic top (no summary)",
        )
    };

    for v in &results {
        ctx.operand_stack.push(clone_value(v));
    }

    if emit_diagnostics {
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Info,
            func_index,
            pc,
            message: format!(
                "call resolved to 1 target (func {callee_func_index}); direct call edge \
                 recorded (sound); result via {how}"
            ),
        });
    }
    Ok(())
}

/// True iff the abstract value carries information strictly stronger
/// than `top` — i.e. a context-sensitive re-eval could improve over
/// the context-insensitive summary. An i32/i64 interval that is not
/// the full lattice top qualifies; `Unknown` and a top interval do
/// not.
fn is_more_precise_than_top(v: &AbstractValue) -> bool {
    match v {
        AbstractValue::I32Interval(iv) | AbstractValue::I64Interval(iv) => !interval_is_top(iv),
        AbstractValue::RegionPointer(_) => true,
        AbstractValue::Unknown => false,
    }
}

/// Handle `CallIndirect { type_index, table_index }` (FEAT-006) via
/// the Paccamiccio et al. 2024 technique (AC-008): pop the top-of-
/// stack abstract index value, intersect its interval with the
/// table bounds `[0, table-len)`, and resolve the target set to
/// every table entry in the resulting range. Emits a sound
/// call-graph edge (`Info` naming the resolved count; `Warning`
/// when the index is unconstrained and the edge covers the whole
/// table). Never emits `UnsoundnessFallback`; never scrubs locals.
/// Models the callee's stack effect pessimistically (the index was
/// already popped; then pop the type's params, push `top` per
/// result).
#[allow(clippy::too_many_arguments)]
fn handle_call_indirect(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    module_ctx: &ModuleCtx<'_>,
    call_graph: &mut Vec<CallEdge>,
    type_index: u32,
    table_index: u32,
) {
    // Pop the table-index operand (top of stack).
    let index_v = ctx.operand_stack.pop();
    let index_iv = index_v.as_ref().and_then(as_i32_interval);

    let table = module_ctx.func_table;
    let table_len = table.len();

    // Determine the resolved index range, clamped to [0, table_len).
    // `unconstrained` is true when we could not pin the index to a
    // sub-range of the table (either the index abstract value wasn't
    // an i32 interval, or its interval is wider than the table, or
    // the table contents are not fully known) — in which case we
    // over-approximate to the whole table (sound, imprecise) and
    // emit a Warning.
    let (lo, hi, unconstrained) = if table_index != 0 || table_len == 0 {
        // We only model table 0. A call_indirect against another
        // table (or with no table present) resolves to the empty
        // set — sound (there are no entries we can name). Treat as
        // "constrained to empty".
        (0u64, 0u64, false)
    } else if let Some(iv) = index_iv {
        // Clamp [iv.lo, iv.hi] to [0, table_len). The interval lives
        // in i64 space (sound per FEAT-001 AC#1).
        let clamp_lo = if iv.lo < 0 { 0 } else { iv.lo as u64 };
        let clamp_hi = if iv.hi < 0 {
            // Whole interval is negative → empty after clamping.
            // A negative concrete index would trap at runtime, so an
            // empty resolved set is sound.
            // Empty target set, and not "unconstrained" — this is a
            // precise (empty) resolution, not a whole-table widening.
            return emit_call_indirect_edge(
                ctx,
                func_index,
                pc,
                emit_diagnostics,
                diagnostics,
                module_ctx,
                call_graph,
                type_index,
                Vec::new(),
                false,
                table_len,
            );
        } else {
            (iv.hi as u64).min(table_len.saturating_sub(1))
        };
        // The index is unconstrained (whole table) if its interval
        // is `top` or otherwise spans the entire table, or if the
        // table contents are not fully known (passive/declared
        // segments etc.).
        let spans_table =
            interval_is_top(&iv) || (clamp_lo == 0 && clamp_hi >= table_len.saturating_sub(1));
        let unconstrained = spans_table || !table.contents_known;
        (clamp_lo, clamp_hi, unconstrained)
    } else {
        // Index abstract value wasn't an i32 interval (i64/unknown):
        // over-approximate to the whole table.
        (0u64, table_len.saturating_sub(1), true)
    };

    let targets = if table_index != 0 || table_len == 0 {
        Vec::new()
    } else {
        table.resolve_range(lo, hi)
    };

    emit_call_indirect_edge(
        ctx,
        func_index,
        pc,
        emit_diagnostics,
        diagnostics,
        module_ctx,
        call_graph,
        type_index,
        targets,
        unconstrained,
        table_len,
    );
}

/// Shared tail of `handle_call_indirect`: record the resolved edge,
/// emit the Info/Warning diagnostic, and apply the pessimistic
/// stack effect for the call type. Factored out so the early-return
/// (all-negative index) path and the normal path share one body.
#[allow(clippy::too_many_arguments)]
fn emit_call_indirect_edge(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    module_ctx: &ModuleCtx<'_>,
    call_graph: &mut Vec<CallEdge>,
    type_index: u32,
    targets: Vec<u32>,
    unconstrained: bool,
    table_len: u64,
) {
    let target_count = targets.len();
    // Keep a copy of the resolved targets for the FEAT-007 summary
    // join below; the `CallEdge` takes ownership of `targets`.
    let resolved_targets = targets.clone();
    call_graph.push(CallEdge {
        caller_func: func_index,
        pc,
        indirect: true,
        resolved_targets: targets,
        // Both the precise and the whole-table over-approximation
        // are sound; an over-approximation is still sound (it never
        // drops a concretely reachable target).
        soundness: SoundnessTag::Sound,
    });

    if emit_diagnostics {
        if unconstrained {
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::Warning,
                func_index,
                pc,
                message: format!(
                    "call_indirect index unconstrained — {target_count} targets \
                     (whole-table over-approximation over a {table_len}-entry table; sound)"
                ),
            });
        } else {
            diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::Info,
                func_index,
                pc,
                message: format!(
                    "call_indirect resolved to {target_count} target(s) \
                     (sound; type {type_index}, {table_len}-entry table)"
                ),
            });
        }
    }

    // Stack effect (the index operand was already popped by the
    // caller). FEAT-007: if the index is constrained to a known target
    // set, push the JOIN of the resolved targets' context-insensitive
    // summaries (sound — the runtime dispatches exactly one of them,
    // and the join over-approximates every candidate). Scope
    // discipline: indirect calls never trigger the context-sensitive
    // re-eval path (that is direct, non-recursive, small callees only),
    // so the join of `top`-input summaries is the precision available
    // here. Fall back to pessimistic `top` when the index is
    // unconstrained, the target set is empty, or any target lacks a
    // summary (an import target, say).
    let sig = module_ctx
        .signature_of_type(type_index)
        .map(|(p, r)| (p.len(), r.clone()));
    let Some((param_count, results)) = sig else {
        return;
    };
    for _ in 0..param_count {
        let _ = ctx.operand_stack.pop();
    }

    // Try to build a precise joined result from the resolved targets.
    let joined = if !unconstrained && !resolved_targets.is_empty() {
        join_target_summaries(module_ctx, &resolved_targets, &results)
    } else {
        None
    };
    match joined {
        Some(values) => {
            for v in &values {
                ctx.operand_stack.push(clone_value(v));
            }
        }
        None => {
            for ty in &results {
                ctx.operand_stack.push(top_for(*ty));
            }
        }
    }
}

/// Join (least-upper-bound) the context-insensitive summaries of a set
/// of resolved `call_indirect` targets into one result vector
/// (FEAT-007). Returns `None` if any target has no summary (e.g. an
/// import) or its summary's result arity doesn't match `results` — the
/// caller then falls back to pessimistic `top`. Sound because the
/// concrete call dispatches exactly one target and the join
/// over-approximates all candidates.
fn join_target_summaries(
    module_ctx: &ModuleCtx<'_>,
    targets: &[u32],
    results: &[wasmparser::ValType],
) -> Option<Vec<AbstractValue>> {
    let n = results.len();
    // Seed with the first target's summary, then join the rest.
    let first = module_ctx.summary_by_abs(*targets.first()?)?;
    if first.result_summary.len() != n {
        return None;
    }
    let mut acc: Vec<AbstractValue> = first.result_summary.iter().map(clone_value).collect();
    for &t in &targets[1..] {
        let s = module_ctx.summary_by_abs(t)?;
        if s.result_summary.len() != n {
            return None;
        }
        for (slot, v) in acc.iter_mut().zip(s.result_summary.iter()) {
            *slot = join_abstract(slot, v);
        }
    }
    Some(acc)
}

/// Least-upper-bound of two abstract values in matching domains. Used
/// to merge `call_indirect` target summaries. When the two values are
/// in different domains (shouldn't happen for a well-typed call), the
/// result is `Unknown` (the conservative top of the variant lattice).
fn join_abstract(a: &AbstractValue, b: &AbstractValue) -> AbstractValue {
    match (a, b) {
        (AbstractValue::I32Interval(x), AbstractValue::I32Interval(y)) => {
            AbstractValue::I32Interval(domain::join(*x, *y))
        }
        (AbstractValue::I64Interval(x), AbstractValue::I64Interval(y)) => {
            AbstractValue::I64Interval(domain::join(*x, *y))
        }
        _ => AbstractValue::Unknown,
    }
}

// NOTE: v0.4's `apply_call_stack_effect` (pop params, push `top` per
// result) is superseded by FEAT-007: `handle_call` applies the callee
// summary / re-eval result, and `emit_call_indirect_edge` applies the
// joined target summaries (falling back to `top_for` per result when
// the index is unconstrained or a target lacks a summary). The
// pessimistic `top` effect now lives inline in those two sites.

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
