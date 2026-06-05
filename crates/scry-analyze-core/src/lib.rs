//! scry-analyze-core — pure, bindgen-free analyzer core (FEAT-014 / DD-012).
//!
//! ## Why this crate exists
//!
//! Through v1.1 the analyzer's decision logic (wasmparser parse, the
//! fixpoint, and the transfer functions) lived in
//! `crates/scry-analyzer/src/lib.rs`, welded
//! to the wit-bindgen-generated types and the `Guest` trait. That made two
//! things impossible: instrumenting the *real* decisions for witness MC/DC
//! (witness wants a core module, but the analyzer is a wasip2 component),
//! and reusing the analyzer outside the component ABI.
//!
//! DD-012 extracts that logic into this pure crate. Its result types are
//! plain Rust mirrors of the analyzer's WIT (`crates/scry-analyzer/wit/
//! scry.wit`); the component (`scry-analyzer`) is a thin wrapper that
//! converts between the wit-bindgen types and these. Same pure-crate
//! dual-compile pattern as [`scry_interval`] / `scry-taint`: it is
//! `#![no_std]` with `extern crate alloc`, no bindgen, so it builds
//! natively (host tests and the MC/DC harness), to
//! `wasm32-unknown-unknown` (witness instruments it), and into the shipped
//! `wasm32-wasip2` component.
//!
//! ## The analyzer
//!
//! The full v0.2–v1.1 abstract-interpretation pipeline now lives here as
//! the free function [`analyze`]: parse the Wasm module via `wasmparser`,
//! run the interval-domain fixpoint with the region-memory domain, resolve
//! the call graph (direct + `call_indirect`), compute compositional
//! function summaries over the SCC condensation, and run the taint
//! (noninterference) analysis. The transfer functions delegate to the pure
//! [`scry_interval`] / `scry_taint` crates via the local `domain` module.
//! Because the core operates on [`scry_interval::Interval`] directly (not
//! the WIT `interval`), the per-op marshalling the component used to do
//! is gone — the soundness-critical decisions run on pure types, which is
//! exactly what lets witness instrument them under MC/DC.
//!
//! ## Type correspondence (this crate ⇄ scry.wit)
//!
//! `interval` and `region-pointer-payload` are field-identical to
//! [`scry_interval::Interval`] / [`scry_interval::Region`], so they are
//! re-used directly rather than re-declared. Every other WIT type has a
//! plain-Rust mirror below with the same fields (snake_case, as wit-bindgen
//! generates them) so the component wrapper's conversion is a field-by-field
//! copy.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use wasmparser::{Operator, Parser, Payload};

// The pure meld<->scry boundary crate (DD-002 / FEAT-002): the binary
// format of the `component-provenance` custom section plus the projection
// lookup. Aliased to avoid colliding with the mirror `ComponentOrigin`
// type below; conversion between the two is a trivial field copy where the
// `provenance` field is built.
use scry_provenance::ComponentOrigin as ProvOrigin;

pub use scry_interval::{Interval, Region};
/// Mirror of WIT `abstract-value`. The abstract value of one Wasm
/// value-stack entry or local at a program point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AbstractValue {
    /// i32 value abstracted as an integer interval.
    I32Interval(Interval),
    /// i64 value abstracted as an integer interval.
    I64Interval(Interval),
    /// i32 value carrying a region tag (region-id + offset interval).
    RegionPointer(Region),
    /// Anything outside the modelled scope.
    Unknown,
}

/// Mirror of WIT `local-invariant`. Per-local abstract value at a pc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalInvariant {
    pub local_index: u32,
    pub value: AbstractValue,
}

/// Mirror of WIT `program-point`. All locals at one pc in one function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramPoint {
    pub func_index: u32,
    pub pc: u32,
    pub locals: Vec<LocalInvariant>,
}

/// Mirror of WIT `invariant-bundle`. The full per-module invariant bundle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvariantBundle {
    /// JSON schema URL the consumer should validate against.
    pub schema: String,
    /// SHA-256 of the input Wasm module, hex-encoded lowercase.
    pub module_sha256: String,
    /// Per-instruction abstract state for each visited program point.
    pub points: Vec<ProgramPoint>,
}

/// Mirror of WIT `diagnostic-severity`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    Info,
    Warning,
    UnsoundnessFallback,
}

/// Mirror of WIT `diagnostic`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub func_index: u32,
    pub pc: u32,
    pub message: String,
}

/// Mirror of WIT `security-label` (FEAT-009). The two-point lattice
/// `low ⊑ high`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SecurityLabel {
    /// Provably public.
    Low,
    /// May depend on a declared secret source (sound top).
    High,
}

/// Mirror of WIT `taint-policy` (FEAT-009). The declared information-flow
/// policy for an analyze call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaintPolicy {
    /// Parameter indices treated as High sources on every analyzed
    /// function's entry.
    pub high_params: Vec<u32>,
    /// Result indices required to remain Low at function exit.
    pub low_results: Vec<u32>,
}

/// Mirror of WIT `analysis-config`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnalysisConfig {
    /// Max fixpoint iterations per loop header before widening. Default 3.
    pub widening_threshold: Option<u32>,
    /// Whether to emit diagnostics for unsupported instructions.
    pub emit_diagnostics: bool,
    /// Optional information-flow policy (FEAT-009). `None` disables taint.
    pub taint_policy: Option<TaintPolicy>,
}

/// Mirror of WIT `soundness-tag` (FEAT-006). Classification of a call-graph
/// edge's resolved target set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SoundnessTag {
    Sound,
    UnsoundFallback,
}

/// Mirror of WIT `call-edge` (FEAT-006). One resolved call-site edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallEdge {
    pub caller_func: u32,
    pub pc: u32,
    /// `true` for `call_indirect`, `false` for a direct `call`.
    pub indirect: bool,
    pub resolved_targets: Vec<u32>,
    pub soundness: SoundnessTag,
}

/// Mirror of WIT `function-summary` (FEAT-007). Per-function abstract
/// summary computed bottom-up over the call graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionSummary {
    pub func_index: u32,
    pub param_count: u32,
    pub result_summary: Vec<AbstractValue>,
    pub context_sensitive: bool,
    pub recursive: bool,
}

/// Mirror of WIT `component-origin` (FEAT-002 / DD-002). One fused-module
/// function's origin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ComponentOrigin {
    pub fused_func_index: u32,
    pub component_id: u32,
    pub orig_func_index: u32,
}

/// Mirror of WIT `component-provenance` (FEAT-002). Decoded
/// `component-provenance` custom section.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentProvenance {
    pub origins: Vec<ComponentOrigin>,
}

/// Mirror of WIT `taint-finding-kind` (FEAT-009).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TaintFindingKind {
    /// High value reached a Low sink via an explicit data flow.
    HighResultExplicit,
    /// High value reached a Low sink via an implicit (control) flow.
    HighResultImplicit,
}

/// Mirror of WIT `taint-finding` (FEAT-009). One noninterference finding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaintFinding {
    pub func_index: u32,
    pub pc: u32,
    pub kind: TaintFindingKind,
    pub source_label: SecurityLabel,
    pub sink_label: SecurityLabel,
    pub message: String,
}

/// Mirror of WIT `analysis-result`. Full analyzer output for one call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnalysisResult {
    pub invariants: InvariantBundle,
    pub diagnostics: Vec<Diagnostic>,
    pub call_graph: Vec<CallEdge>,
    pub function_summaries: Vec<FunctionSummary>,
    pub provenance: Option<ComponentProvenance>,
    pub taint_findings: Vec<TaintFinding>,
}

/// Mirror of WIT `analyze-error`. Reasons an analyze call fails without a
/// partial bundle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnalyzeError {
    /// Input bytes did not decode as a valid Wasm module.
    InvalidModule(String),
    /// Configuration was inconsistent (e.g. widening-threshold = 0).
    InvalidConfig(String),
    /// Internal analyzer invariant broken — a scry bug, not an input bug.
    Internal(String),
}

/// The abstract-domain interface every transfer function dispatches
/// through. Through v1.0 this was the WIT-generated bindings for the
/// imported `pulseengine:wasm-lattice/domain` interface; v1.1 (FEAT-013)
/// made it a thin local module over the pure domain crates so the analyzer
/// is self-contained. In this crate (DD-012) it operates on
/// [`scry_interval::Interval`] directly — there is no WIT `interval` to
/// convert to/from — so each function is a direct delegation. The surface
/// (types + free fns) is unchanged, so the `domain::*` call sites compile
/// as before.
mod domain {
    pub use scry_interval::{Interval, Region};
    pub use scry_taint::Label;

    // ── Interval lattice + transfer functions ──────────────────────
    pub fn top() -> Interval {
        scry_interval::top()
    }
    pub fn constant_i32(c: i32) -> Interval {
        scry_interval::constant_i32(c)
    }
    pub fn constant_i64(c: i64) -> Interval {
        scry_interval::constant_i64(c)
    }
    pub fn join(a: Interval, b: Interval) -> Interval {
        scry_interval::join(a, b)
    }
    pub fn i32_add(a: Interval, b: Interval) -> Interval {
        scry_interval::i32_add(a, b)
    }
    pub fn i32_sub(a: Interval, b: Interval) -> Interval {
        scry_interval::i32_sub(a, b)
    }
    pub fn i32_mul(a: Interval, b: Interval) -> Interval {
        scry_interval::i32_mul(a, b)
    }

    // ── Region-memory domain ───────────────────────────────────────
    pub fn region_create(region_id: u32) -> Region {
        scry_interval::region_create(region_id)
    }
    pub fn region_offset(r: Region, delta: Interval) -> Region {
        scry_interval::region_offset(r, delta)
    }

    // ── Security-label (taint) domain ──────────────────────────────
    pub fn label_bottom() -> Label {
        scry_taint::bottom()
    }
    pub fn label_top() -> Label {
        scry_taint::top()
    }
    pub fn label_leq(a: Label, b: Label) -> bool {
        scry_taint::leq(a, b)
    }
    pub fn label_join(a: Label, b: Label) -> Label {
        scry_taint::join(a, b)
    }
}
const SCRY_VERSION: &str = "1.6.0";
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
            if let Some(Some(f)) = self.entries.get(i as usize)
                && !targets.contains(f)
            {
                targets.push(*f);
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

pub fn analyze(
    module_bytes: Vec<u8>,
    config: AnalysisConfig,
) -> Result<AnalysisResult, AnalyzeError> {
    if module_bytes.is_empty() {
        return Err(AnalyzeError::InvalidModule(
            "module bytes are empty".to_string(),
        ));
    }
    if let Some(threshold) = config.widening_threshold
        && threshold == 0
    {
        return Err(AnalyzeError::InvalidConfig(
            "widening-threshold must be >= 1".to_string(),
        ));
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

    // ── FEAT-002 component-provenance (DD-002) ───────────────────
    // Decoded function-origin map from meld's `component-provenance`
    // custom section, if the fused module carried one. `None` means
    // either no section (a single un-fused component, or any plain
    // Core Wasm input) or a section that failed to decode (reported
    // via a Warning diagnostic — never a partial parse).
    let mut provenance_origins: Option<Vec<ProvOrigin>> = None;

    for payload in Parser::new(0).parse_all(&module_bytes) {
        let payload = payload.map_err(|e| {
            AnalyzeError::InvalidModule(format!("wasm parse failed (pre-pass): {e}"))
        })?;
        match payload {
            Payload::TypeSection(reader) => {
                for rec_group in reader {
                    let rec_group = rec_group
                        .map_err(|e| AnalyzeError::InvalidModule(format!("type section: {e}")))?;
                    for subtype in rec_group.into_types() {
                        if let wasmparser::CompositeInnerType::Func(ft) =
                            &subtype.composite_type.inner
                        {
                            let params: Vec<_> = ft.params().to_vec();
                            let results: Vec<_> = ft.results().to_vec();
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
                    let imp = imp
                        .map_err(|e| AnalyzeError::InvalidModule(format!("import section: {e}")))?;
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
                    let mem = entry
                        .map_err(|e| AnalyzeError::InvalidModule(format!("memory section: {e}")))?;
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
                    let table = entry
                        .map_err(|e| AnalyzeError::InvalidModule(format!("table section: {e}")))?;
                    if first {
                        table_section_seen = true;
                        // `initial` / `maximum` are `u64` in the
                        // table64-aware wasmparser; `u64::from`
                        // also accepts a `u32` width so this stays
                        // correct across the API's integer-width
                        // history.
                        table0_len = table.ty.initial;
                        table0_max = table.ty.maximum;
                        table0_is_funcref = table.ty.element_type == wasmparser::RefType::FUNCREF;
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
                        wasmparser::ElementKind::Passive | wasmparser::ElementKind::Declared => {
                            // Passive / declared segments are
                            // installed at runtime via `table.init`
                            // (which v0.4 doesn't model) — treat
                            // the table contents as unknown.
                            table_contents_unknown = true;
                        }
                    }
                }
            }
            Payload::CustomSection(reader)
                // FEAT-002 / DD-002: meld emits the function-origin
                // map as a `component-provenance` custom section.
                // Decode it strictly here — a malformed section is a
                // Warning + `none`, never a partial parse — so
                // phase 2 can project invariants onto component
                // origins. Other custom sections (name, producers,
                // dwarf, …) are ignored.
                if reader.name() == scry_provenance::SECTION_NAME => {
                    match scry_provenance::decode(reader.data()) {
                        Ok(origins) => provenance_origins = Some(origins),
                        Err(e) => {
                            if config.emit_diagnostics {
                                diagnostics.push(Diagnostic {
                                    severity: DiagnosticSeverity::Warning,
                                    func_index: 0,
                                    pc: 0,
                                    message: format!(
                                        "component-provenance section present but malformed: \
                                             {e}; FEAT-002 projection disabled for this module"
                                    ),
                                });
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
                    AnalyzeError::InvalidModule(format!("function {abs_index} local entry: {e}"))
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
    let static_callees = build_static_call_graph(&defined_funcs, &func_table, import_func_count);
    let sccs = tarjan_sccs(&static_callees);
    let recursive_flags = recursive_flags_from_sccs(&sccs, &static_callees, defined_funcs.len());

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
    let mut summaries: Vec<Option<SummaryEntry>> = (0..defined_funcs.len()).map(|_| None).collect();
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
        let context_sensitive = !recursive && defined_funcs[defined].ops.len() <= REEVAL_MAX_OPS;
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

    // ───────────────────────────────────────────────────────────
    // FEAT-002 (DD-002): project Component-Model results onto fused-
    // module locations. With the decoded `component-provenance` map,
    // every analyzed (fused) function index resolves to the
    // component + function it was lowered from — the association that
    // lets loom / witness / sigil attribute a fused-module invariant
    // back to its component source. v0.7 emits the projection as
    // per-function diagnostics and carries the decoded map on
    // `analysis-result.provenance`; the richer handle-state /
    // capability-flow analysis is a later FEAT-002 slice.
    // ───────────────────────────────────────────────────────────
    let provenance = provenance_origins.as_ref().map(|origins| {
        if config.emit_diagnostics {
            for func in &defined_funcs {
                match scry_provenance::project(origins, func.abs_index) {
                    Some(origin) => diagnostics.push(Diagnostic {
                        severity: DiagnosticSeverity::Info,
                        func_index: func.abs_index,
                        pc: 0,
                        message: format!(
                            "FEAT-002 projection: fused func {} originates from component {} \
                                 function {}",
                            func.abs_index, origin.component_id, origin.orig_func_index
                        ),
                    }),
                    None => diagnostics.push(Diagnostic {
                        severity: DiagnosticSeverity::Warning,
                        func_index: func.abs_index,
                        pc: 0,
                        message: format!(
                            "FEAT-002 projection: fused func {} has no component-provenance \
                                 entry — invariant left unattributed",
                            func.abs_index
                        ),
                    }),
                }
            }
        }
        ComponentProvenance {
            origins: origins
                .iter()
                .map(|o| ComponentOrigin {
                    fused_func_index: o.fused_func_index,
                    component_id: o.component_id,
                    orig_func_index: o.orig_func_index,
                })
                .collect(),
        }
    });

    // ───────────────────────────────────────────────────────────
    // FEAT-009 (AC-007): taint / noninterference domain. Opt-in via
    // `config.taint-policy`. For each defined function we run a
    // dedicated label-propagation walk (a "shadow" taint state over
    // operand stack + locals, plus a control-context label for
    // implicit flows) seeded from the declared High sources, and
    // report a finding when a declared Low result carries the High
    // label at exit. The label lattice operations are dogfooded
    // across the wasm-lattice WIT boundary (DD-008) just like the
    // interval ops — `domain::label_*`. When no policy is supplied
    // the field is empty and behaviour is exactly as before.
    // ───────────────────────────────────────────────────────────
    let mut taint_findings: Vec<TaintFinding> = Vec::new();
    if let Some(policy) = config.taint_policy.as_ref() {
        for func in &defined_funcs {
            run_taint_analysis(
                func,
                policy,
                config.emit_diagnostics,
                &mut diagnostics,
                &mut taint_findings,
            );
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
        provenance,
        taint_findings,
    })
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
/// FEAT-016 slice-1: pair each structured-control opener (`block` / `loop`
/// / `if`) with its matching `end`. `end_at[pc] = Some(end_pc)` when the op
/// at `pc` opens a region closing at `end_pc`; `None` otherwise. The
/// trailing function-level `end` has no open region on the stack, so it maps
/// to nothing (it is interpreted normally as a no-op).
fn build_end_map(ops: &[Operator<'_>]) -> Vec<Option<usize>> {
    let mut end_at: Vec<Option<usize>> = alloc::vec![None; ops.len()];
    let mut open: Vec<usize> = Vec::new();
    for (pc, op) in ops.iter().enumerate() {
        match op {
            Operator::Block { .. } | Operator::Loop { .. } | Operator::If { .. } => {
                open.push(pc);
            }
            Operator::End => {
                if let Some(opener) = open.pop() {
                    end_at[opener] = Some(pc);
                }
            }
            _ => {}
        }
    }
    end_at
}

/// The set of local indices written (`local.set` / `local.tee`) anywhere in
/// `ops[start..end]`, nested regions included. FEAT-016 slice-1 "write-set
/// havoc": `local.set` / `local.tee` are the ONLY operators that write a
/// Wasm local, so this scan is complete — a structured region can change
/// exactly these locals and no others. Widening just them to ⊤ on region
/// exit is therefore sound, while every local outside the set keeps its
/// precise pre-region value (the FEAT-016 precision win over the v0.2
/// scrub-everything fallback).
fn region_write_set(ops: &[Operator<'_>], start: usize, end: usize) -> Vec<u32> {
    let mut written: Vec<u32> = Vec::new();
    for op in &ops[start..end] {
        if let Operator::LocalSet { local_index } | Operator::LocalTee { local_index } = op
            && !written.contains(local_index)
        {
            written.push(*local_index);
        }
    }
    written
}

/// FEAT-016 slice-2a: max fixpoint iterations at a loop header before we
/// widen (then a hard cap before widening straight to ⊤ for termination).
/// Matches the analysis-config `widening-threshold` default (3).
const LOOP_WIDEN_THRESHOLD: u32 = 3;
const LOOP_ITER_CAP: u32 = 64;

/// Per-local widening (FEAT-016 slice-2a). `widen(a, b)` over the interval
/// domain (scry-interval, terminating ascending-chain); region/unknown keep
/// their value only if unchanged, else degrade to ⊤ (`Unknown`).
fn widen_abstract(a: &AbstractValue, b: &AbstractValue) -> AbstractValue {
    match (a, b) {
        (AbstractValue::I32Interval(x), AbstractValue::I32Interval(y)) => {
            AbstractValue::I32Interval(scry_interval::widen(*x, *y))
        }
        (AbstractValue::I64Interval(x), AbstractValue::I64Interval(y)) => {
            AbstractValue::I64Interval(scry_interval::widen(*x, *y))
        }
        _ if a == b => clone_value(a),
        _ => AbstractValue::Unknown,
    }
}

/// `a ⊑ b` in the abstract-value lattice (FEAT-016 slice-2a).
fn leq_abstract(a: &AbstractValue, b: &AbstractValue) -> bool {
    match (a, b) {
        (AbstractValue::I32Interval(x), AbstractValue::I32Interval(y)) => {
            scry_interval::leq(*x, *y)
        }
        (AbstractValue::I64Interval(x), AbstractValue::I64Interval(y)) => {
            scry_interval::leq(*x, *y)
        }
        // `Unknown` is the variant-lattice top: everything is below it.
        (_, AbstractValue::Unknown) => true,
        _ => a == b,
    }
}

fn join_locals(a: &[AbstractValue], b: &[AbstractValue]) -> Vec<AbstractValue> {
    a.iter().zip(b).map(|(x, y)| join_abstract(x, y)).collect()
}

fn widen_locals(a: &[AbstractValue], b: &[AbstractValue]) -> Vec<AbstractValue> {
    a.iter().zip(b).map(|(x, y)| widen_abstract(x, y)).collect()
}

/// Interval NARROWING (FEAT-016 slice-2b-i): replace each INFINITE bound of
/// the widened value `a` with the corresponding bound of the re-applied
/// transfer `b` (`b ⊑ a`), recovering a finite bound widening overshot to ⊤.
/// Finite bounds of `a` are kept (narrowing never loosens). Terminating: the
/// number of infinite bounds only decreases.
fn narrow_abstract(a: &AbstractValue, b: &AbstractValue) -> AbstractValue {
    fn narrow_iv(a: Interval, b: Interval) -> Interval {
        Interval {
            lo: if a.lo == i64::MIN { b.lo } else { a.lo },
            hi: if a.hi == i64::MAX { b.hi } else { a.hi },
        }
    }
    match (a, b) {
        (AbstractValue::I32Interval(x), AbstractValue::I32Interval(y)) => {
            AbstractValue::I32Interval(narrow_iv(*x, *y))
        }
        (AbstractValue::I64Interval(x), AbstractValue::I64Interval(y)) => {
            AbstractValue::I64Interval(narrow_iv(*x, *y))
        }
        _ => clone_value(a),
    }
}

fn narrow_locals(a: &[AbstractValue], b: &[AbstractValue]) -> Vec<AbstractValue> {
    a.iter()
        .zip(b)
        .map(|(x, y)| narrow_abstract(x, y))
        .collect()
}

/// `a ⊑ b` pointwise over the locals vector.
fn locals_leq(a: &[AbstractValue], b: &[AbstractValue]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| leq_abstract(x, y))
}

/// A signed i32 comparison guard `local OP const` (FEAT-016 slice-2b-i).
#[derive(Clone, Copy)]
enum GuardOp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

/// Map a wasmparser comparison operator (with a `local` first operand and a
/// `const` second operand) to a [`GuardOp`]. Only SIGNED i32 comparisons are
/// refined — unsigned comparisons wrap, so refining their bounds with a
/// signed constant is not sound; they return `None` (no refinement).
fn guard_op(op: &Operator<'_>) -> Option<GuardOp> {
    Some(match op {
        Operator::I32Eq => GuardOp::Eq,
        Operator::I32Ne => GuardOp::Ne,
        Operator::I32LtS => GuardOp::Lt,
        Operator::I32GtS => GuardOp::Gt,
        Operator::I32LeS => GuardOp::Le,
        Operator::I32GeS => GuardOp::Ge,
        _ => return None,
    })
}

/// Refine the interval of a local known to satisfy (`taken = true`) or
/// violate (`taken = false`) the guard `local OP c`. Sound: it `meet`s the
/// current interval with the half-space the guard implies; predicates that
/// don't carve an interval (`== ` on the false edge, `!=` on the true edge)
/// leave it unchanged. FEAT-016 slice-2b-i.
fn refine_interval(iv: Interval, op: GuardOp, c: i64, taken: bool) -> Interval {
    let imin = i64::MIN;
    let imax = i64::MAX;
    // The half-space the (possibly negated) guard implies, as [lo, hi].
    let (lo, hi) = match (op, taken) {
        (GuardOp::Eq, true) | (GuardOp::Ne, false) => (c, c),
        (GuardOp::Eq, false) | (GuardOp::Ne, true) => return iv, // ≠ c: no interval
        (GuardOp::Lt, true) | (GuardOp::Ge, false) => (imin, c.saturating_sub(1)), // < c
        (GuardOp::Ge, true) | (GuardOp::Lt, false) => (c, imax), // ≥ c
        (GuardOp::Gt, true) | (GuardOp::Le, false) => (c.saturating_add(1), imax), // > c
        (GuardOp::Le, true) | (GuardOp::Gt, false) => (imin, c), // ≤ c
    };
    scry_interval::meet(iv, Interval { lo, hi })
}

/// Did a straight-line sequence fall through to its end, or did control
/// leave it (a `br`/`return`)? FEAT-016 slice-2a structured dataflow.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Flow {
    Fall,
    Diverged,
}

/// A structured label (an enclosing `block` or `loop`) and the joined locals
/// of every branch that targets it. For a `block` the branch target is the
/// state AFTER the block; for a `loop` it is the loop header (the back-edge).
struct Label {
    breaks: Option<Vec<AbstractValue>>,
}

impl Label {
    fn record(&mut self, locals: &[AbstractValue]) {
        self.breaks = Some(match self.breaks.take() {
            Some(acc) => join_locals(&acc, locals),
            None => locals.to_vec(),
        });
    }
}

/// FEAT-016 slice-2a: a structured-CFG abstract interpreter over the interval
/// (+ region/taint via interpret_op) domain. Replaces slice-1's write-set
/// havoc with a real iterate-then-widen fixpoint, so loop-carried locals keep
/// the precise value they converge to instead of being widened to ⊤. Carries
/// the per-pass mutable analysis outputs + the structured `block`/`loop`
/// dataflow.
struct Interp<'a, 'b> {
    ops: &'a [Operator<'b>],
    end_at: &'a [Option<usize>],
    func_index: u32,
    module_ctx: &'a ModuleCtx<'b>,
    emit_diagnostics: bool,
    depth: u32,
    diagnostics: &'a mut Vec<Diagnostic>,
    call_graph: &'a mut Vec<CallEdge>,
    points: Vec<ProgramPoint>,
}

impl Interp<'_, '_> {
    /// Interpret `ops[start..end)` over `ctx`, mutating its locals/stack and
    /// recording branches into `labels` (innermost last). `emit` gates
    /// program-point emission — suppressed during a loop's pre-convergence
    /// fixpoint passes, enabled on the final pass. Returns whether control
    /// fell through or diverged.
    fn seq(
        &mut self,
        start: usize,
        end: usize,
        ctx: &mut FuncCtx,
        labels: &mut Vec<Label>,
        emit: bool,
    ) -> Result<Flow, AnalyzeError> {
        let mut pc = start;
        while pc < end {
            // ── Structured region: block / loop (precise) ───────────
            if let Some(rend) = self.end_at[pc] {
                let empty = matches!(
                    self.ops[pc],
                    Operator::Block {
                        blockty: wasmparser::BlockType::Empty
                    } | Operator::Loop {
                        blockty: wasmparser::BlockType::Empty
                    }
                );
                if empty && !ctx.degraded && matches!(self.ops[pc], Operator::Block { .. }) {
                    let flow = self.block(pc + 1, rend, ctx, labels, emit)?;
                    if flow == Flow::Diverged && ctx.degraded {
                        // unreachable fall-through; keep going (dead code).
                    }
                    pc = rend + 1;
                    continue;
                } else if empty && !ctx.degraded && matches!(self.ops[pc], Operator::Loop { .. }) {
                    self.loop_region(pc + 1, rend, ctx, labels, emit)?;
                    pc = rend + 1;
                    continue;
                } else {
                    // `if`, non-empty block type, or already degraded: the
                    // sound v0.2 fallback (write-set havoc of the region).
                    self.havoc_region(pc, rend, ctx, emit);
                    pc = rend + 1;
                    continue;
                }
            }

            // ── Guard refinement (FEAT-016 slice-2b-i) ──────────────
            // A comparison-guarded branch `local.get L; i32.const C; <cmp>;
            // br_if D` (or `local.get L; i32.eqz; br_if D`) refines L's
            // interval by the comparison on each edge: the taken edge (the
            // guard holds) reaches label D; the not-taken edge (the guard is
            // false) falls through. This is what bounds a counted loop's
            // counter (e.g. `i >= 10` → exit ⇒ inside the loop `i <= 9`),
            // where the plain interval fixpoint would widen it to ⊤. A
            // peephole on the canonical idiom — anything else falls through to
            // the unrefined br_if below (sound, just no tightening).
            if let Some(next) = self.try_guard_brif(pc, ctx, labels) {
                if emit && !ctx.degraded {
                    self.points.push(ProgramPoint {
                        func_index: self.func_index,
                        pc: pc as u32,
                        locals: snapshot_locals(&ctx.locals),
                    });
                }
                pc = next;
                continue;
            }

            // ── Branches: contribute to the targeted label ──────────
            match &self.ops[pc] {
                Operator::Br { relative_depth } => {
                    self.target(labels, *relative_depth).record(&ctx.locals);
                    return Ok(Flow::Diverged);
                }
                Operator::BrIf { relative_depth } => {
                    // br_if pops its i32 condition; on the taken edge the
                    // locals reach the target, on the not-taken edge we fall
                    // through (both modelled — sound).
                    let _ = ctx.operand_stack.pop();
                    self.target(labels, *relative_depth).record(&ctx.locals);
                    pc += 1;
                    continue;
                }
                Operator::Return => {
                    return Ok(Flow::Diverged);
                }
                Operator::BrTable { .. } => {
                    // Unmodelled multi-target branch: sound fallback.
                    ctx.scrub_to_top();
                    return Ok(Flow::Diverged);
                }
                _ => {}
            }

            // ── Straight-line operator (interpret_op) ───────────────
            let stop = matches!(
                interpret_op(
                    &self.ops[pc],
                    ctx,
                    self.func_index,
                    pc as u32,
                    self.emit_diagnostics,
                    self.diagnostics,
                    self.module_ctx,
                    self.call_graph,
                    self.depth,
                )?,
                StepOutcome::Stop
            );
            if emit && !ctx.degraded {
                self.points.push(ProgramPoint {
                    func_index: self.func_index,
                    pc: pc as u32,
                    locals: snapshot_locals(&ctx.locals),
                });
            }
            if stop {
                return Ok(Flow::Diverged);
            }
            pc += 1;
        }
        Ok(Flow::Fall)
    }

    /// The label a `br relative_depth` targets (innermost = depth 0).
    fn target<'l>(&self, labels: &'l mut [Label], relative_depth: u32) -> &'l mut Label {
        let n = labels.len();
        let idx = n.saturating_sub(1 + relative_depth as usize);
        &mut labels[idx]
    }

    /// FEAT-016 slice-2b-i guard refinement. If the ops at `pc` are the
    /// canonical comparison-guarded branch `local.get L; i32.const C; <signed
    /// cmp>; br_if D` (4 ops) or `local.get L; i32.eqz; br_if D` (3 ops),
    /// refine `L`'s interval by the guard on both edges — record the
    /// taken-edge locals (guard true) into label `D`, set `ctx.locals` to the
    /// not-taken-edge locals (guard false) — and return the pc just past the
    /// idiom. Returns `None` (caller handles `pc` normally) for anything else.
    /// The idiom's net operand-stack effect is zero (push L, push C, cmp pops
    /// 2 / pushes 1, br_if pops 1), so the stack is left untouched.
    fn try_guard_brif(&self, pc: usize, ctx: &mut FuncCtx, labels: &mut [Label]) -> Option<usize> {
        if ctx.degraded {
            return None;
        }
        let ops = self.ops;
        // Recognise `local.get L; i32.const C; <cmp>; br_if D`.
        let (local, c, op, depth, next) = match ops.get(pc)? {
            Operator::LocalGet { local_index } => {
                let l = *local_index;
                match (ops.get(pc + 1)?, ops.get(pc + 2)?, ops.get(pc + 3)) {
                    // 4-op: local.get L; const C; cmp; br_if D
                    (
                        Operator::I32Const { value },
                        cmp,
                        Some(Operator::BrIf { relative_depth }),
                    ) => {
                        let gop = guard_op(cmp)?;
                        (l, *value as i64, gop, *relative_depth, pc + 4)
                    }
                    // 3-op: local.get L; i32.eqz; br_if D  (L == 0)
                    (Operator::I32Eqz, Operator::BrIf { relative_depth }, _) => {
                        (l, 0, GuardOp::Eq, *relative_depth, pc + 3)
                    }
                    _ => return None,
                }
            }
            _ => return None,
        };

        // The local must be a tightenable i32 interval; otherwise no refine.
        let iv = match ctx.locals.get(local as usize) {
            Some(AbstractValue::I32Interval(iv)) => *iv,
            _ => return None,
        };
        let taken_iv = refine_interval(iv, op, c, true);
        let not_taken_iv = refine_interval(iv, op, c, false);

        // Taken edge (guard true) → label D.
        let mut taken_locals = ctx.locals.clone();
        taken_locals[local as usize] = AbstractValue::I32Interval(taken_iv);
        self.target(labels, depth).record(&taken_locals);

        // Not-taken edge (guard false) → fall through.
        ctx.locals[local as usize] = AbstractValue::I32Interval(not_taken_iv);
        Some(next)
    }

    /// `block`: branches to it land AFTER the block, so the post-block state
    /// is the fall-through (if reachable) joined with the break states.
    fn block(
        &mut self,
        start: usize,
        end: usize,
        ctx: &mut FuncCtx,
        labels: &mut Vec<Label>,
        emit: bool,
    ) -> Result<Flow, AnalyzeError> {
        let saved_stack = ctx.operand_stack.clone();
        labels.push(Label { breaks: None });
        let body_flow = self.seq(start, end, ctx, labels, emit)?;
        let label = labels.pop().expect("pushed above");
        // []→[] region: the operand stack is balanced back to pre-region.
        ctx.operand_stack = saved_stack;
        match (body_flow, label.breaks) {
            (Flow::Fall, Some(b)) => ctx.locals = join_locals(&ctx.locals, &b),
            (Flow::Fall, None) => {}
            (Flow::Diverged, Some(b)) => ctx.locals = b,
            (Flow::Diverged, None) => {
                // Post-block unreachable (body always branched elsewhere).
                // Dead code follows; leave locals as a sound over-approx.
            }
        }
        Ok(Flow::Fall)
    }

    /// `loop`: branches to it return to the header (back-edge). Iterate
    /// `header_{k+1} = entry ⊔ back-edges`, widening after the threshold,
    /// until the header is stable (a post-fixpoint). The post-loop state is
    /// the join of the body's fall-through-to-loop-end states (the loop is
    /// usually exited via a `br` to an outer block, handled by that block's
    /// accumulator).
    fn loop_region(
        &mut self,
        start: usize,
        end: usize,
        ctx: &mut FuncCtx,
        labels: &mut Vec<Label>,
        emit: bool,
    ) -> Result<(), AnalyzeError> {
        let entry = ctx.locals.clone();
        let saved_stack = ctx.operand_stack.clone();
        // Snapshot the ENCLOSING labels' break-state. The widening/narrowing
        // passes below re-run the body many times with intermediate (often ⊤)
        // headers; each `br` to an outer label would otherwise accumulate those
        // throwaway states into the enclosing label and poison its exit join.
        // Only the final converged pass should contribute outer breaks, so we
        // restore this snapshot just before it.
        let saved_outer: Vec<Option<Vec<AbstractValue>>> =
            labels.iter().map(|l| l.breaks.clone()).collect();
        let mut header = entry.clone();
        let mut exit: Option<Vec<AbstractValue>> = None;
        let mut iter = 0u32;
        loop {
            ctx.locals = header.clone();
            ctx.operand_stack = saved_stack.clone();
            labels.push(Label { breaks: None });
            // Suppress point emission until the header has converged; the
            // final pass below emits the fixpoint state.
            let body_flow = self.seq(start, end, ctx, labels, false)?;
            let label = labels.pop().expect("pushed above");
            if body_flow == Flow::Fall {
                exit = Some(match exit.take() {
                    Some(e) => join_locals(&e, &ctx.locals),
                    None => ctx.locals.clone(),
                });
            }
            let mut next = match &label.breaks {
                Some(b) => join_locals(&entry, b),
                None => entry.clone(),
            };
            if iter >= LOOP_WIDEN_THRESHOLD {
                next = widen_locals(&header, &next);
            }
            if locals_leq(&next, &header) {
                break;
            }
            header = next;
            iter += 1;
            if iter > LOOP_ITER_CAP {
                // Termination safety net: widen every local to ⊤.
                header = header
                    .iter()
                    .map(|_| AbstractValue::I32Interval(domain::top()))
                    .collect();
                break;
            }
        }
        // ── Narrowing (FEAT-016 slice-2b-i) ──────────────────────────
        // Widening may have overshot a bound to ⊤ (e.g. a guard-bounded loop
        // counter widens up before the `i < C` refinement is seen). Re-apply
        // the body and replace the header's infinite bounds with the
        // recomputed finite ones, descending to a tighter sound post-fixpoint.
        let mut narrow_iter = 0u32;
        loop {
            ctx.locals = header.clone();
            ctx.operand_stack = saved_stack.clone();
            labels.push(Label { breaks: None });
            let _ = self.seq(start, end, ctx, labels, false)?;
            let label = labels.pop().expect("pushed above");
            let candidate = match &label.breaks {
                Some(b) => join_locals(&entry, b),
                None => entry.clone(),
            };
            let narrowed = narrow_locals(&header, &candidate);
            if narrowed == header {
                break;
            }
            header = narrowed;
            narrow_iter += 1;
            if narrow_iter > LOOP_ITER_CAP {
                break;
            }
        }
        // Restore the enclosing labels' break-state, discarding everything the
        // intermediate widening/narrowing passes recorded into them.
        for (label, saved) in labels.iter_mut().zip(saved_outer) {
            label.breaks = saved;
        }
        // Final pass over the converged header WITH emission, to record the
        // fixpoint program points inside the loop body.
        ctx.locals = header.clone();
        ctx.operand_stack = saved_stack.clone();
        labels.push(Label { breaks: None });
        let final_flow = self.seq(start, end, ctx, labels, emit)?;
        let final_label = labels.pop().expect("pushed above");
        if final_flow == Flow::Fall {
            exit = Some(match exit.take() {
                Some(e) => join_locals(&e, &ctx.locals),
                None => ctx.locals.clone(),
            });
        }
        // Drop this loop's own back-edge breaks — they targeted this loop only
        // and already shaped `header`. Breaks to OUTER labels were recorded by
        // the final pass above (the intermediate passes' contributions were
        // wiped by the snapshot restore).
        let _ = final_label;
        // Post-loop state: fall-through-exit if any, else the fixpoint header
        // (sound: covers the otherwise-unreachable fall-through).
        ctx.locals = exit.unwrap_or(header);
        ctx.operand_stack = saved_stack;
        Ok(())
    }

    /// Sound fallback for a region we do not model precisely (`if`, non-empty
    /// block type, `br_table`-heavy bodies): slice-1 write-set havoc — widen
    /// exactly the written locals to ⊤, preserve the rest.
    fn havoc_region(&mut self, opener: usize, end: usize, ctx: &mut FuncCtx, emit: bool) {
        if matches!(self.ops[opener], Operator::If { .. }) {
            let _ = ctx.operand_stack.pop();
        }
        let written = region_write_set(self.ops, opener + 1, end);
        for idx in &written {
            if let Some(slot) = ctx.locals.get_mut(*idx as usize) {
                *slot = AbstractValue::I32Interval(domain::top());
            }
        }
        if self.emit_diagnostics {
            self.diagnostics.push(Diagnostic {
                severity: DiagnosticSeverity::Info,
                func_index: self.func_index,
                pc: opener as u32,
                message: format!(
                    "{} modelled by write-set havoc (FEAT-016 fallback): {} local(s) widened \
                     to top, rest preserved",
                    op_name(&self.ops[opener]),
                    written.len()
                ),
            });
        }
        if emit {
            self.points.push(ProgramPoint {
                func_index: self.func_index,
                pc: end as u32,
                locals: snapshot_locals(&ctx.locals),
            });
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn run_function_body(
    func: &DefinedFunc<'_>,
    init_locals: Vec<AbstractValue>,
    module_ctx: &ModuleCtx<'_>,
    emit_points: Option<&mut Vec<ProgramPoint>>,
    diagnostics: &mut Vec<Diagnostic>,
    call_graph: &mut Vec<CallEdge>,
    emit_diagnostics: bool,
    depth: u32,
) -> Result<Vec<AbstractValue>, AnalyzeError> {
    let mut ctx = FuncCtx::new(init_locals);
    let ops = &func.ops;
    let end_at = build_end_map(ops);
    let want_points = emit_points.is_some();
    let mut interp = Interp {
        ops,
        end_at: &end_at,
        func_index: func.abs_index,
        module_ctx,
        emit_diagnostics,
        depth,
        diagnostics,
        call_graph,
        points: Vec::new(),
    };
    let mut labels: Vec<Label> = Vec::new();
    interp.seq(0, ops.len(), &mut ctx, &mut labels, want_points)?;
    if let Some(out) = emit_points {
        out.extend(interp.points);
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
        if let Some(abs) = slot
            && *abs >= import_func_count
        {
            let d = (*abs - import_func_count) as usize;
            if d < defined_funcs.len() && !table_targets.contains(&d) {
                table_targets.push(d);
            }
        }
    }

    let mut graph: Vec<Vec<usize>> = Vec::with_capacity(defined_funcs.len());
    for func in defined_funcs {
        let mut callees: Vec<usize> = Vec::new();
        for op in &func.ops {
            match op {
                Operator::Call { function_index } if *function_index >= import_func_count => {
                    let d = (*function_index - import_func_count) as usize;
                    if d < defined_funcs.len() && !callees.contains(&d) {
                        callees.push(d);
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
                if let Some(&(parent, _)) = work.last()
                    && lowlink[v] < lowlink[parent]
                {
                    lowlink[parent] = lowlink[v];
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
        // ── i32 comparison family (FEAT-016 slice-2a) ────────────────
        // A comparison/test pushes a boolean i32 in {0, 1}; soundly the
        // bounded interval [0, 1]. Crucially these do NOT write locals, so
        // (unlike the v0.2 catch-all) they must NOT scrub — loop exit tests
        // (`local.get i; i32.eqz; br_if`) need to interpret without
        // degrading, or the loop fixpoint never runs.
        Operator::I32Eqz => {
            let _ = ctx.operand_stack.pop();
            ctx.operand_stack
                .push(AbstractValue::I32Interval(Interval { lo: 0, hi: 1 }));
        }
        Operator::I32Eq
        | Operator::I32Ne
        | Operator::I32LtS
        | Operator::I32LtU
        | Operator::I32GtS
        | Operator::I32GtU
        | Operator::I32LeS
        | Operator::I32LeU
        | Operator::I32GeS
        | Operator::I32GeU => {
            let _ = ctx.operand_stack.pop();
            let _ = ctx.operand_stack.pop();
            ctx.operand_stack
                .push(AbstractValue::I32Interval(Interval { lo: 0, hi: 1 }));
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

// ════════════════════════════════════════════════════════════════════
// FEAT-009 (AC-007): taint / noninterference domain.
//
// A dedicated label-propagation walk over one function body. The
// interval pass scrubs to top on control flow; the taint pass instead
// interprets *structured* control (empty-typed `block` / `if` / `else`
// / `end`) so it can raise a control-context label and capture the
// IMPLICIT flows that make the result a sound termination-insensitive
// noninterference analysis rather than mere explicit-flow taint. Every
// lattice operation is dogfooded across the wasm-lattice WIT boundary
// (DD-008): the propagation calls `domain::label_join` / `label_bottom`
// / `label_top` / `label_leq`, never a local lattice op.
//
// Scope (sound for everything; precise for a bounded set, mirroring the
// interval pass): handled precisely are constants, `local.get/set/tee`,
// `drop`, `select`, the pure i32/i64 arithmetic + bitwise + comparison
// + conversion operators, and empty-typed structured `block`/`if`/
// `else`/`end`. ANY other operator — `loop` (needs a taint fixpoint),
// `br*`, value-typed blocks, `call*`, memory and global ops — degrades
// the function's taint state to High (the sound top) and stops precise
// tracking. Degrading can only ADD taint, so it never misses a flow
// (REQ-001): the absence of a finding still implies noninterference.
// ════════════════════════════════════════════════════════════════════

/// A shadow taint value: a security label plus, when the label is High,
/// whether the High-ness arrived (at least partly) through an implicit
/// (control-context) flow. The label is the WIT-imported `domain::Label`
/// so every combination goes through the lattice component.
#[derive(Clone, Copy)]
struct Taint {
    label: domain::Label,
    implicit: bool,
}

impl Taint {
    fn low() -> Self {
        Taint {
            label: domain::label_bottom(),
            implicit: false,
        }
    }
}

/// `true` iff the label is High — expressed via the dogfooded
/// `label-leq`: High is exactly the elements not below ⊥ (`low`).
fn taint_is_high(l: domain::Label) -> bool {
    !domain::label_leq(l, domain::label_bottom())
}

/// Join two shadow values (explicit data flow): `label = a ⊔ b`, and
/// the result is implicit-High only if its High-ness is owed to an
/// implicit-High operand.
fn taint_join(a: Taint, b: Taint) -> Taint {
    let label = domain::label_join(a.label, b.label);
    let implicit = (taint_is_high(a.label) && a.implicit) || (taint_is_high(b.label) && b.implicit);
    Taint {
        label,
        implicit: taint_is_high(label) && implicit,
    }
}

/// Store a value under a control context: `label = v ⊔ ctx`. If the
/// High-ness comes from `ctx` (the value itself was Low) the flow is
/// implicit; otherwise the value's own implicit-ness is inherited.
fn taint_store(v: Taint, ctx: domain::Label) -> Taint {
    let label = domain::label_join(v.label, ctx);
    let from_ctx = taint_is_high(ctx) && !taint_is_high(v.label);
    let implicit = from_ctx || (taint_is_high(v.label) && v.implicit);
    Taint {
        label,
        implicit: taint_is_high(label) && implicit,
    }
}

/// The taint stack-effect of one operator (see the module banner for
/// the scope rationale). `Scrub` is the sound catch-all.
enum TaintEff {
    /// Push a provably-Low value (a constant).
    PushLow,
    /// Push the shadow label of a local.
    PushLocal(u32),
    /// Pop a value and store it (joined with the control context) into a
    /// local; `keep` (for `local.tee`) leaves the value's data taint on
    /// the stack.
    StoreLocal { idx: u32, keep: bool },
    /// Pop `n` operands, push their join (pure data flow). `n >= 1`.
    Reduce(u8),
    /// Pop one operand, discard it.
    Drop,
    /// No stack effect.
    Nop,
    /// Open an empty-typed `block` (control context unchanged).
    OpenBlock,
    /// Open an empty-typed `if`: pop the condition, raise the context.
    OpenIf,
    /// `else` — the alternate arm stays under the raised context.
    Else,
    /// `end` — close the innermost control frame, restoring its context.
    End,
    /// `return` / `unreachable` — stop the walk.
    Stop,
    /// Anything unmodelled: conservatively raise the whole taint state
    /// to High (sound) and stop precise tracking.
    Scrub,
}

fn taint_effect(op: &Operator<'_>) -> TaintEff {
    match op {
        Operator::I32Const { .. }
        | Operator::I64Const { .. }
        | Operator::F32Const { .. }
        | Operator::F64Const { .. } => TaintEff::PushLow,

        Operator::LocalGet { local_index } => TaintEff::PushLocal(*local_index),
        Operator::LocalSet { local_index } => TaintEff::StoreLocal {
            idx: *local_index,
            keep: false,
        },
        Operator::LocalTee { local_index } => TaintEff::StoreLocal {
            idx: *local_index,
            keep: true,
        },

        Operator::Drop => TaintEff::Drop,
        Operator::Nop => TaintEff::Nop,

        // `select` pops two values + a condition and pushes one. Joining
        // all three folds the (implicit) dependence on the condition into
        // the result's data taint — sound and precise here.
        Operator::Select | Operator::TypedSelect { .. } => TaintEff::Reduce(3),

        // Binary numeric / bitwise / comparison operators: pop 2, push 1.
        Operator::I32Add
        | Operator::I32Sub
        | Operator::I32Mul
        | Operator::I32DivS
        | Operator::I32DivU
        | Operator::I32RemS
        | Operator::I32RemU
        | Operator::I32And
        | Operator::I32Or
        | Operator::I32Xor
        | Operator::I32Shl
        | Operator::I32ShrS
        | Operator::I32ShrU
        | Operator::I32Rotl
        | Operator::I32Rotr
        | Operator::I32Eq
        | Operator::I32Ne
        | Operator::I32LtS
        | Operator::I32LtU
        | Operator::I32GtS
        | Operator::I32GtU
        | Operator::I32LeS
        | Operator::I32LeU
        | Operator::I32GeS
        | Operator::I32GeU
        | Operator::I64Add
        | Operator::I64Sub
        | Operator::I64Mul
        | Operator::I64DivS
        | Operator::I64DivU
        | Operator::I64RemS
        | Operator::I64RemU
        | Operator::I64And
        | Operator::I64Or
        | Operator::I64Xor
        | Operator::I64Shl
        | Operator::I64ShrS
        | Operator::I64ShrU
        | Operator::I64Rotl
        | Operator::I64Rotr
        | Operator::I64Eq
        | Operator::I64Ne
        | Operator::I64LtS
        | Operator::I64LtU
        | Operator::I64GtS
        | Operator::I64GtU
        | Operator::I64LeS
        | Operator::I64LeU
        | Operator::I64GeS
        | Operator::I64GeU => TaintEff::Reduce(2),

        // Unary numeric / test / conversion operators: pop 1, push 1.
        Operator::I32Eqz
        | Operator::I64Eqz
        | Operator::I32Clz
        | Operator::I32Ctz
        | Operator::I32Popcnt
        | Operator::I64Clz
        | Operator::I64Ctz
        | Operator::I64Popcnt
        | Operator::I32WrapI64
        | Operator::I64ExtendI32S
        | Operator::I64ExtendI32U
        | Operator::I32Extend8S
        | Operator::I32Extend16S
        | Operator::I64Extend8S
        | Operator::I64Extend16S
        | Operator::I64Extend32S => TaintEff::Reduce(1),

        // Structured control — only the empty (no value) block type is
        // modelled precisely; a value-producing block/if would perturb
        // the stack-depth model, so it degrades (sound).
        Operator::Block {
            blockty: wasmparser::BlockType::Empty,
        } => TaintEff::OpenBlock,
        Operator::If {
            blockty: wasmparser::BlockType::Empty,
        } => TaintEff::OpenIf,
        Operator::Else => TaintEff::Else,
        Operator::End => TaintEff::End,
        Operator::Return | Operator::Unreachable => TaintEff::Stop,

        _ => TaintEff::Scrub,
    }
}

/// Run the taint / noninterference walk over one function body
/// (FEAT-009). Seeds the parameter labels from the policy, propagates
/// labels (and the implicit-flow control context) through the body, and
/// pushes a `TaintFinding` for every declared Low result that carries
/// the High label at exit.
fn run_taint_analysis(
    func: &DefinedFunc<'_>,
    policy: &TaintPolicy,
    emit_diagnostics: bool,
    diagnostics: &mut Vec<Diagnostic>,
    findings: &mut Vec<TaintFinding>,
) {
    // Seed local labels: declared High params → High (explicit source);
    // every other param and all declared locals → Low.
    let mut t_locals: Vec<Taint> =
        Vec::with_capacity(func.params.len() + func.declared_locals.len());
    for i in 0..func.params.len() {
        if policy.high_params.contains(&(i as u32)) {
            t_locals.push(Taint {
                label: domain::label_top(),
                implicit: false,
            });
        } else {
            t_locals.push(Taint::low());
        }
    }
    for _ in &func.declared_locals {
        t_locals.push(Taint::low());
    }

    let mut t_stack: Vec<Taint> = Vec::new();
    let mut ctx: domain::Label = domain::label_bottom();
    let mut frames: Vec<domain::Label> = Vec::new();
    let mut degraded = false;

    let mut pc: u32 = 0;
    for op in &func.ops {
        if degraded {
            pc = pc.saturating_add(1);
            continue;
        }
        match taint_effect(op) {
            TaintEff::PushLow => t_stack.push(Taint::low()),
            TaintEff::PushLocal(idx) => {
                let v = t_locals.get(idx as usize).copied().unwrap_or(Taint {
                    label: domain::label_top(),
                    implicit: false,
                });
                t_stack.push(v);
            }
            TaintEff::StoreLocal { idx, keep } => {
                let v = t_stack.pop().unwrap_or(Taint {
                    label: domain::label_top(),
                    implicit: false,
                });
                let stored = taint_store(v, ctx);
                if let Some(slot) = t_locals.get_mut(idx as usize) {
                    *slot = stored;
                }
                if keep {
                    t_stack.push(v);
                }
            }
            TaintEff::Reduce(n) => {
                let mut acc = Taint::low();
                for _ in 0..n {
                    let x = t_stack.pop().unwrap_or(Taint {
                        label: domain::label_top(),
                        implicit: false,
                    });
                    acc = taint_join(acc, x);
                }
                t_stack.push(acc);
            }
            TaintEff::Drop => {
                let _ = t_stack.pop();
            }
            TaintEff::Nop => {}
            TaintEff::OpenBlock => frames.push(ctx),
            TaintEff::OpenIf => {
                let cond = t_stack.pop().unwrap_or(Taint {
                    label: domain::label_top(),
                    implicit: false,
                });
                frames.push(ctx);
                ctx = domain::label_join(ctx, cond.label);
            }
            TaintEff::Else => {}
            TaintEff::End => {
                if let Some(saved) = frames.pop() {
                    ctx = saved;
                }
            }
            TaintEff::Stop => break,
            TaintEff::Scrub => {
                if emit_diagnostics {
                    diagnostics.push(Diagnostic {
                        severity: DiagnosticSeverity::Info,
                        func_index: func.abs_index,
                        pc,
                        message: format!(
                            "taint: operator {} not modelled — taint state conservatively \
                             raised to High (sound, FEAT-009)",
                            op_name(op)
                        ),
                    });
                }
                for slot in t_locals.iter_mut() {
                    *slot = Taint {
                        label: domain::label_top(),
                        implicit: false,
                    };
                }
                t_stack.clear();
                ctx = domain::label_top();
                degraded = true;
            }
        }
        pc = pc.saturating_add(1);
    }

    // Exit: the function results are the top `n_results` of the value
    // stack (in order). If the body degraded or left an under-full stack
    // (e.g. an early `return` / `unreachable`), every result is High —
    // sound.
    let n_results = func.results.len();
    let mut result_taints: Vec<Taint> = Vec::with_capacity(n_results);
    if !degraded && t_stack.len() >= n_results {
        let start = t_stack.len() - n_results;
        for t in &t_stack[start..] {
            result_taints.push(*t);
        }
    } else {
        for _ in 0..n_results {
            result_taints.push(Taint {
                label: domain::label_top(),
                implicit: false,
            });
        }
    }

    // The exit pc is the function body's terminating `end`.
    let exit_pc = func.ops.len().saturating_sub(1) as u32;
    for &res_idx in &policy.low_results {
        if let Some(t) = result_taints.get(res_idx as usize)
            && taint_is_high(t.label)
        {
            let kind = if t.implicit {
                TaintFindingKind::HighResultImplicit
            } else {
                TaintFindingKind::HighResultExplicit
            };
            let flow = if t.implicit { "implicit" } else { "explicit" };
            findings.push(TaintFinding {
                func_index: func.abs_index,
                pc: exit_pc,
                kind,
                source_label: SecurityLabel::High,
                sink_label: SecurityLabel::Low,
                message: format!(
                    "noninterference violation: result {res_idx} of function \
                         {} is declared Low but carries High via an {flow} flow",
                    func.abs_index
                ),
            });
            if emit_diagnostics {
                diagnostics.push(Diagnostic {
                    severity: DiagnosticSeverity::Warning,
                    func_index: func.abs_index,
                    pc: exit_pc,
                    message: format!(
                        "taint: High→Low {flow} flow — result {res_idx} of function {} \
                             leaks a declared High source (FEAT-009 / AC-007)",
                        func.abs_index
                    ),
                });
            }
        }
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The mirror surface is constructible and the reused pure types line
    /// up with the analyzer's expectations (Interval/Region field-identical
    /// to the WIT interval / region-pointer-payload).
    #[test]
    fn surface_is_constructible() {
        let av = AbstractValue::I32Interval(Interval { lo: 0, hi: 7 });
        let rp = AbstractValue::RegionPointer(Region {
            region_id: 3,
            offset: Interval { lo: 0, hi: 0 },
        });
        let bundle = InvariantBundle {
            schema: String::from("https://pulseengine.eu/schemas/scry-invariants/v1"),
            module_sha256: String::from("00"),
            points: alloc::vec![ProgramPoint {
                func_index: 0,
                pc: 0,
                locals: alloc::vec![LocalInvariant {
                    local_index: 0,
                    value: av.clone(),
                }],
            }],
        };
        let res = AnalysisResult {
            invariants: bundle,
            diagnostics: alloc::vec![Diagnostic {
                severity: DiagnosticSeverity::Info,
                func_index: 0,
                pc: 0,
                message: String::from("ok"),
            }],
            call_graph: alloc::vec![],
            function_summaries: alloc::vec![],
            provenance: None,
            taint_findings: alloc::vec![],
        };
        assert_eq!(res.invariants.points.len(), 1);
        assert!(matches!(rp, AbstractValue::RegionPointer(_)));
        assert_eq!(
            AnalyzeError::InvalidConfig(String::from("x")),
            AnalyzeError::InvalidConfig(String::from("x"))
        );
    }

    /// FEAT-016 slice-1 oracle (write-set havoc). fixture-08 is a counted
    /// loop whose local 1 (`k`) is set to 42 *before* the loop and never
    /// written inside it; local 0 (`i`) is decremented inside the loop.
    /// Before FEAT-016 the `block`/`loop` scrubbed *every* local to ⊤ and
    /// stopped emitting points. With write-set havoc the loop is modelled:
    /// `i` (in the write-set) widens to ⊤, but `k` (not in the write-set)
    /// keeps its precise `[42, 42]` across the region — and analysis
    /// continues past the loop. Driven natively against `analyze()` (no
    /// component / Bazel needed).
    #[test]
    fn feat016_loop_invariant_local_survives() {
        let wat_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../scry-analyzer/test-fixtures/fixture-08-counted-loop.wat"
        );
        let bytes = wat::parse_file(wat_path).expect("assemble fixture-08");
        let config = AnalysisConfig {
            widening_threshold: Some(3),
            emit_diagnostics: true,
            taint_policy: None,
        };
        let result = analyze(bytes, config).expect("analyze fixture-08 must succeed");

        // SOUNDNESS + the FEAT-016 win: `k` (local 1) is never scrubbed to ⊤
        // anywhere — pre-FEAT-016 the loop would have degraded it.
        for p in &result.invariants.points {
            for l in &p.locals {
                if l.local_index == 1
                    && let AbstractValue::I32Interval(iv) = &l.value
                {
                    assert!(
                        !(iv.lo == i64::MIN && iv.hi == i64::MAX),
                        "loop-invariant local k scrubbed to top at pc {} — write-set havoc \
                         failed",
                        p.pc
                    );
                }
            }
        }

        // Analysis continued PAST the loop (pre-FEAT-016 it degraded and
        // stopped emitting). The final program point must show `k = [42,42]`
        // (survived precisely) and `i = ⊤` (written in the loop → havocked).
        let last = result
            .invariants
            .points
            .last()
            .expect("fixture-08 must emit program points past the loop");
        let find = |idx: u32| -> Interval {
            for l in &last.locals {
                if l.local_index == idx
                    && let AbstractValue::I32Interval(iv) = &l.value
                {
                    return *iv;
                }
            }
            panic!("local {idx} missing / not an i32 interval at the final point");
        };
        let k = find(1);
        assert_eq!(
            (k.lo, k.hi),
            (42, 42),
            "loop-invariant k must be [42,42] after the loop, got [{}, {}]",
            k.lo,
            k.hi
        );
        let i = find(0);
        assert!(
            i.lo == i64::MIN && i.hi == i64::MAX,
            "loop-written i must widen to top, got [{}, {}]",
            i.lo,
            i.hi
        );
    }

    /// FEAT-016 slice-2a oracle (real loop fixpoint vs slice-1 havoc).
    /// fixture-09 writes local 1 (`m`) to the constant 7 on every loop
    /// iteration. Slice-1 havoc would widen `m` to ⊤; the iterate-then-widen
    /// fixpoint converges it to the BOUNDED `[0, 7]` (zero-init `[0,0]` ⊔
    /// body `[7,7]`). Asserts `m` is bounded (not ⊤) and contains the
    /// concrete results {0, 7} — the precision win, soundly.
    #[test]
    fn feat016_loop_written_local_converges() {
        let wat_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../scry-analyzer/test-fixtures/fixture-09-loop-converge.wat"
        );
        let bytes = wat::parse_file(wat_path).expect("assemble fixture-09");
        let config = AnalysisConfig {
            widening_threshold: Some(3),
            emit_diagnostics: true,
            taint_policy: None,
        };
        let result = analyze(bytes, config).expect("analyze fixture-09 must succeed");
        let last = result
            .invariants
            .points
            .last()
            .expect("fixture-09 must emit points past the loop");
        let m = last
            .locals
            .iter()
            .find(|l| l.local_index == 1)
            .and_then(|l| match l.value {
                AbstractValue::I32Interval(iv) => Some(iv),
                _ => None,
            })
            .expect("local m (index 1) i32-interval at final point");
        // The slice-2a win: m is BOUNDED (not ⊤), where slice-1 havoc gave ⊤.
        assert!(
            !(m.lo == i64::MIN && m.hi == i64::MAX),
            "loop-written m widened to ⊤ — the loop fixpoint did not converge it (slice-1 \
             havoc behaviour); got [{}, {}]",
            m.lo,
            m.hi
        );
        // Soundness: m's concrete values {0 (loop skipped), 7 (loop ran)} lie
        // in the abstract interval.
        assert!(
            m.lo <= 0 && m.hi >= 7,
            "m must contain the concrete results {{0, 7}}, got [{}, {}]",
            m.lo,
            m.hi
        );
    }

    /// FEAT-016 slice-2b-i oracle (guard refinement). fixture-10 increments
    /// local 0 (`i`) while `i < 10` (exit guard `i >= 10`). slice-2a widens
    /// the loop-written `i` to ⊤; guard refinement bounds it: on the
    /// not-taken edge `i <= 9` ⇒ after `i+1`, `i <= 10`, so the header
    /// converges to `[0,10]` and the post-loop (exit) value is `[10,10]`.
    /// Asserts `i` has an UPPER BOUND ≤ 10 (not ⊤) and contains the concrete
    /// result 10 — the precision win, soundly.
    #[test]
    fn feat016_guard_bounds_counter() {
        let wat_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../scry-analyzer/test-fixtures/fixture-10-guard-bound.wat"
        );
        let bytes = wat::parse_file(wat_path).expect("assemble fixture-10");
        let config = AnalysisConfig {
            widening_threshold: Some(3),
            emit_diagnostics: true,
            taint_policy: None,
        };
        let result = analyze(bytes, config).expect("analyze fixture-10 must succeed");
        let last = result
            .invariants
            .points
            .last()
            .expect("fixture-10 must emit points past the loop");
        let i = last
            .locals
            .iter()
            .find(|l| l.local_index == 0)
            .and_then(|l| match l.value {
                AbstractValue::I32Interval(iv) => Some(iv),
                _ => None,
            })
            .expect("local i (index 0) i32-interval at final point");
        // The slice-2b-i win: i has a finite UPPER BOUND ≤ 10 (slice-2a gave
        // ⊤ / i64::MAX). The guard `i >= 10` taught the fixpoint i is bounded.
        assert!(
            i.hi <= 10,
            "guard refinement failed: loop counter i has no tight upper bound (got hi={}, \
             expected ≤ 10 — slice-2a widens to ⊤ here)",
            i.hi
        );
        // Soundness: the concrete result (10) lies in i's interval.
        assert!(
            i.lo <= 10 && i.hi >= 10,
            "i must contain the concrete result 10, got [{}, {}]",
            i.lo,
            i.hi
        );
    }
}
