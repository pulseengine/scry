//! scry-analyze-core — pure, bindgen-free analyzer core (FEAT-014 / DD-012).
//!
//! ## Normal API
//!
//! Call [`analyze`] with a Core Wasm module's bytes and an [`AnalysisConfig`];
//! it returns an [`AnalysisResult`] of plain Rust types — no WIT, no component,
//! no `wasmtime`. This is the library a Rust tool (e.g. synth's footprint
//! analysis) consumes directly from crates.io:
//!
//! ```ignore
//! use scry_analyze_core::{analyze, AnalysisConfig};
//!
//! let r = analyze(wasm_bytes, AnalysisConfig::default())?;
//!
//! for e in &r.call_graph {
//!     // e.indirect, e.resolved_targets: Vec<u32> (over-approximated for
//!     // call_indirect), e.soundness — fold edges into a longest-path, etc.
//! }
//! let has_cycle = r.function_summaries.iter().any(|s| s.recursive);
//! let reachable = &r.reachable_from_exports; // sound superset; prune the rest
//! let stack = r.stack_usage.max_stack_bytes;  // Bytes(n) | Unbounded | Unknown
//! ```
//!
//! Every result type ([`AnalysisResult`], [`CallEdge`], [`FunctionSummary`],
//! [`StackUsage`]/[`StackBound`], …) is `pub` and `#[derive(Clone, Debug, Eq)]`.
//! The crate is `#![no_std]` (over `alloc`), which is a fine dependency for a
//! `std` tool.
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

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use wasmparser::{Operator, Parser, Payload};

// The pure meld<->scry boundary crate (DD-002 / FEAT-002 / FEAT-032): the
// binary format of the `component-provenance` v3 custom section plus the
// projection lookup. `decode()` returns a `ProvenanceSection` (premises +
// sha + origins); the `provenance` field below maps it into the mirror types.
use scry_bits::{BitsCong, Cong};
use scry_octagon::Octagon;
use scry_poly::Poly;
use scry_segment::Segmentation;

pub use scry_interval::{Interval, Region};
// FEAT-032 (scry#63): the fusion premises + code-range types travel with the
// `component-provenance` v3 section; re-exported so a library consumer reads
// them off `AnalysisResult.provenance` without depending on scry-provenance.
pub use scry_provenance::{CodeRange, FusionPremises};
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

/// Mirror of WIT `program-point`. The abstract state at one pc in one function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramPoint {
    pub func_index: u32,
    pub pc: u32,
    pub locals: Vec<LocalInvariant>,
    /// FEAT-023: the abstract operand-stack at this pc, in stack order
    /// (bottom → top). The transient value-stack state a backend maps onto
    /// SSA temps / selected instructions. Core-only for now (the WIT
    /// `program-point` mirror still carries only `locals`; a later slice
    /// surfaces it for non-Rust consumers). Sound over the same interval
    /// domain as `locals`.
    pub operand_stack: Vec<AbstractValue>,
    /// FEAT-041 (REQ-016): the GENUINELY-relational octagon constraints holding
    /// between distinct locals at this pc (`x_a - x_b ≤ c` / `x_a + x_b ≤ c`),
    /// filtered to those NOT implied by the unary interval bounds. This makes
    /// the octagon's relational precision OBSERVABLE — the v1.9 finding was that
    /// strong closure tightened these but the output only ever projected the
    /// octagon to unary intervals, so the relational facts were invisible.
    /// Library-only (the WIT mirror carries only `locals`); sound (each is a
    /// constraint the octagon maintains).
    pub relational: Vec<RelationalConstraint>,
    /// FEAT-062 (FEAT-058 observability): the tracked linear-memory CONTENT at
    /// this pc — the segmentation's `[lo, hi) → interval` cells, in ascending
    /// offset order. Makes the content-sensitive memory (FEAT-058) OBSERVABLE
    /// (scry-viz renders it; before this it only affected loaded-value
    /// intervals). Empty = ⊤ (no content tracked). Library-only (WIT mirror
    /// carries only `locals`); sound (each cell is a constraint the analysis
    /// maintains — every concrete run's memory respects it).
    pub memory: Vec<MemSegment>,
    /// FEAT-057 slice 2a (REQ-016): general linear constraints `Σ aᵢ·xᵢ ≤ c`
    /// over the locals holding at this pc — the convex-polyhedra domain's
    /// output, strictly above the octagon's `±xᵢ ± xⱼ ≤ c` form. Filtered to
    /// constraints over ≥ 2 distinct locals (a unary poly bound duplicates the
    /// interval domain, mirroring FEAT-041's not-implied-by-unary filter).
    /// ADDITIVE next to `relational` — that struct is in the FEAT-041 output
    /// contract (viz + guidance feed) and is not reshaped. Library-only (the
    /// WIT mirror carries only `locals`). Sound: every constraint is
    /// maintained by the wrap-gated poly transfers through the fixpoint —
    /// an assignment equality (`z = x + y`) enters ONLY when the interval
    /// domain proves the arithmetic cannot wrap on any run reaching this pc.
    pub linear: Vec<LinearConstraint>,
}

/// FEAT-057 slice 2a: one surfaced polyhedra constraint `Σ terms ≤ bound` at
/// a program point. `terms` lists only the non-zero coefficients, each pairing
/// a local index with its integer coefficient.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearConstraint {
    /// The non-zero coefficient terms, in ascending `local_index` order.
    pub terms: Vec<LinearTerm>,
    /// Upper bound: `Σ coeff·local ≤ bound`.
    pub bound: i64,
}

/// FEAT-057 slice 2a: one `coeff · local` term of a [`LinearConstraint`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LinearTerm {
    /// The local's index.
    pub local_index: u32,
    /// Its (non-zero) integer coefficient.
    pub coeff: i64,
}

/// FEAT-062: a surfaced linear-memory content cell at a program point — every
/// offset in `[lo, hi)` is constrained to `value`. Mirrors the internal
/// `scry_segment::Seg`; offsets outside all cells are unconstrained (⊤).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemSegment {
    /// Inclusive low byte offset.
    pub lo: i64,
    /// Exclusive high byte offset (`lo < hi`).
    pub hi: i64,
    /// Interval every offset in `[lo, hi)` is constrained to.
    pub value: Interval,
}

/// FEAT-041: a surfaced relational octagon constraint between two distinct
/// locals at a program point. `a != b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationalConstraint {
    /// Local index `a`.
    pub a: u32,
    /// Local index `b`.
    pub b: u32,
    /// Constraint form (`Diff`: `x_a - x_b ≤ bound`; `Sum`: `x_a + x_b ≤ bound`).
    pub kind: RelKind,
    /// The upper bound.
    pub bound: i64,
}

/// FEAT-041: the form of a [`RelationalConstraint`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelKind {
    /// `x_a - x_b ≤ bound`.
    Diff,
    /// `x_a + x_b ≤ bound`.
    Sum,
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
///
/// [`AnalysisConfig::default()`] is the normal entry-point config for a library
/// consumer: default widening, no diagnostics, no taint policy — i.e. just the
/// intervals / call-graph / stack / reachability results.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
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
    /// FEAT-036: the abstract argument values at this call site, in parameter
    /// declaration order (param 0 first) — the operand-stack slots the call
    /// consumes. Populated for direct calls (empty for `call_indirect` and for
    /// calls to a signature-unknown import). A library-only field — the WIT
    /// `call-edge` mirror does not carry it.
    pub arg_ranges: Vec<AbstractValue>,
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
    /// FEAT-036: interprocedural parameter ranges — the join, per parameter, of
    /// the argument values observed at every call site reaching this function.
    /// SOUND only when scry has accounted for ALL callers, so it is `Unknown`
    /// (⊤) for every parameter of a function that is exported, the start
    /// function, or — conservatively — defined in any module that bears a
    /// funcref container: one that declares/imports ANY table OR uses any
    /// `ref.func`. (A funcref to a defined function can only originate from a
    /// table or a `ref.func`; with neither present, no indirect or host
    /// dispatch is possible, so the recorded direct calls are the complete
    /// caller set.) Otherwise each entry is the join over all direct call
    /// sites — an over-approximation of the parameter's incoming value across
    /// every reachable call (never narrower than some reachable call permits).
    /// Library-only.
    pub param_ranges: Vec<AbstractValue>,
}

/// Mirror of WIT `component-origin` (FEAT-002 / DD-002). One fused-module
/// function's origin.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentOrigin {
    pub fused_func_index: u32,
    /// meld's string id for the originating component (FEAT-032 / v3).
    pub component_id: String,
    pub orig_func_index: u32,
    /// Byte span of the function body in the fused module, if meld recorded it.
    pub code_range: Option<CodeRange>,
}

/// Mirror of WIT `component-provenance` (FEAT-002 / FEAT-032). Decoded
/// `component-provenance` v3 custom section: the fusion premises, the
/// module-binding hash, and the function-origin table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentProvenance {
    /// Fusion premises meld asserts by construction (scry#63). A consumer may
    /// use these as sound analysis assumptions; absent ⇒ stay conservative.
    pub premises: FusionPremises,
    /// SHA-256 of the fused module the section was emitted for.
    pub fused_module_sha256: [u8; 32],
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

/// A worst-case shadow-stack bound (FEAT-021 slice-1). `Bytes(n)` is a sound
/// finite over-approximation; `Unbounded` marks a recursion SCC (no finite
/// bound provable without a ranking function); `Unknown` marks a frame we
/// could not recognise (dynamic `alloca`, an unrecognised prologue, an
/// unresolved `call_indirect` / host edge, or an ambiguous stack-pointer
/// global). For a SOUND bound both `Unbounded` and `Unknown` mean "no finite
/// bound proven" — neither is ever treated as zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StackBound {
    Bytes(u64),
    Unbounded,
    Unknown,
}

/// Per-function shadow-stack facts (FEAT-021 slice-1): the function's own frame
/// and its whole-subtree worst case (this frame plus the deepest reachable
/// callee chain).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FunctionStack {
    pub func_index: u32,
    pub frame: StackBound,
    pub max_stack: StackBound,
}

/// Worst-case shadow-stack usage of the module (FEAT-021 slice-1). The
/// AbsInt-StackAnalyzer analogue for the Wasm linear-memory shadow stack:
/// `max_stack_bytes` is the deepest weighted path through the call graph,
/// each function weighted by the frame its prologue subtracts from the
/// `__stack_pointer` global. Host/WASI frames run on a separate stack and are
/// out of scope (the bound is "guest shadow-stack only").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StackUsage {
    /// The identified `__stack_pointer` global, or `None` if the module has no
    /// shadow stack (no mutable i32 global) or it could not be identified.
    pub sp_global: Option<u32>,
    pub functions: Vec<FunctionStack>,
    pub max_stack_bytes: StackBound,
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
    /// FEAT-021 slice-1: worst-case shadow-stack bound. Core-only (not yet in
    /// the WIT mirror — slice-2 surfaces it); the component wrapper ignores it.
    pub stack_usage: StackUsage,
    /// FEAT-022 slice-1: absolute indices of functions reachable (via direct +
    /// over-approximated `call_indirect` edges) from an exported or start
    /// function — a sound SUPERSET of concretely-reachable functions, so a
    /// downstream consumer can soundly prune what is absent (REQ-011/SCRY-001).
    /// Sorted ascending. Core-only for now (slice-1b surfaces it in WIT).
    pub reachable_from_exports: Vec<u32>,
    /// FEAT-027: human-readable metadata for every function index (imports +
    /// defined), sorted by `func_index`. Names come from the custom `name`
    /// section, else an export name, else an import `module.field`; `None`
    /// when the module carries none (consumers fall back to the index). Lets a
    /// consumer (synth's footprint report, scry-viz) show `$compute_stack` in
    /// place of `func 42`. Library-only addition (not in the WIT mirror).
    pub function_meta: Vec<FunctionMeta>,
    /// FEAT-034: fusion premises scry determined for ITSELF by inspecting the
    /// module (verify-not-trust) — `bounded_memory` = no `memory.grow` anywhere
    /// (linear memory is fixed), `closed_world` = no functional imports (no
    /// external caller scry cannot see). These are scry's OWN sound facts,
    /// independent of any meld-provided premise in `provenance.premises`; a
    /// consumer can rely on them because scry proved them. When a meld v3
    /// premise contradicts scry's verification (e.g. claims bounded_memory on a
    /// module containing `memory.grow`), scry emits a diagnostic and keeps its
    /// own (conservative) determination here.
    pub verified_premises: FusionPremises,
    /// FEAT-037 (DD-017): known-bits / congruence facts for locals, produced by
    /// an additive straight-line-sound pass over each function body using the
    /// known-bits × interval-guarded congruence reduced product
    /// ([`scry_bits`]). Each entry records, at the program point of a
    /// `local.set`/`local.tee`, the abstract bit/alignment/stride fact the
    /// written local then carries — for alignment-driven bounds-check elision
    /// and bit-level specialization in codegen consumers (synth#54). Sorted by
    /// `(func_index, pc, local_index)`. Library-only (not in the WIT mirror or
    /// the frozen v1 JSON contract), like [`AnalysisResult::function_meta`].
    /// Only non-⊤ facts are emitted (a ⊤ fact carries no information).
    pub bit_facts: Vec<BitFact>,
    /// FEAT-040 (REQ-017): explicit, machine-readable records of the places the
    /// interval/region interpreter was CONSERVATIVE — every site where it either
    /// degraded a whole function to ⊤ (an unsupported op, a `br_table`, or a
    /// non-i32-shaped memory address — the [`FuncCtx::scrub_to_top`] sites,
    /// enforced complete by that method's signature) OR fell back to write-set
    /// havoc of an unmodelled control-flow region (a typed `if` / non-empty
    /// block-type — a partial give-up). Where the rest of the result emits ⊤ as
    /// *silence* (an unanalyzed point produces no record), this enumerates the
    /// "scry was conservative here" sites so an assessor (the qualification
    /// scope/limitation statement) or an AI agent can see them directly. Sorted
    /// by `(func_index, pc)`. Library-only, emitted regardless of
    /// `emit_diagnostics`.
    ///
    /// SCOPE (honest bounds): this covers the interval/region INTERPRETER. It
    /// does NOT enumerate (a) ordinary loop widening to ⊤ — that is normal sound
    /// abstraction, not a give-up; (b) the separate `bit_facts` / taint passes'
    /// own conservative stops; (c) imported functions (never analyzed). Those
    /// are sound but out of this report's scope.
    pub gaps: Vec<Gap>,
    /// FEAT-044 (REQ-014, AC-014): proven strict-less-than relations between a
    /// local and another local / a constant, recorded by an additive
    /// guard-detection pass using the Pentagons domain ([`scry_pentagon`]).
    /// Each entry is a guard `x < y` (or `x < c`) that scry proved holds inside
    /// the then-region of an `if` — the cheap relational fact out-of-bounds
    /// trap detection (FEAT-046) consumes as `index < length`. Sorted by
    /// `(func_index, pc)`. Library-only (not in the WIT mirror or the frozen v1
    /// JSON contract), like [`AnalysisResult::bit_facts`].
    pub pentagon_facts: Vec<PentagonFact>,
    /// FEAT-045 (REQ-014, MF-006): division/remainder trap classifications —
    /// scry's first runtime-error verdict. Every `i32/i64.div_s/div_u/rem_s/
    /// rem_u` the interval interpreter reaches gets a `DivByZero` verdict (and
    /// every `div_s` additionally a `SignedOverflow` verdict); `ProvenSafe` is
    /// emitted only when the divisor (resp. dividend) interval excludes the
    /// trapping value, else `PotentialTrap`. No reached div/rem is silently
    /// dropped. Sorted by `(func_index, pc, kind)`. Library-only (not in the
    /// WIT mirror or the frozen v1 JSON contract), like [`Self::bit_facts`].
    pub trap_checks: Vec<TrapCheck>,
    /// FEAT-047 (REQ-015, AC-022): sound float-interval facts for f32/f64
    /// locals, produced by an additive straight-line pass over each function
    /// body using the IEEE-754 float-interval domain ([`scry_float`]). Each
    /// entry records, at a `local.set`/`local.tee`, the sound over-approximation
    /// (interval + NaN possibility) the written float local then carries —
    /// removing the scope hole where float arithmetic was un-analyzed. Sorted by
    /// `(func_index, pc, local_index)`. Library-only (not in the WIT mirror or
    /// the frozen v1 JSON contract), like [`Self::bit_facts`]. Only non-⊤ facts
    /// are emitted.
    pub float_facts: Vec<FloatFact>,
    /// FEAT-049 (REQ-003, MF-007): Component-Model handle-lifetime faults
    /// (use-after-drop / double-drop) found by the affine handle-state pass over
    /// the canonical-ABI `[resource-drop]` / `[method]` call sites. Sound
    /// definite faults only (no false report on correctly owned/borrowed
    /// handles). Sorted by `(func_index, pc)`. Library-only (not in the WIT
    /// mirror or the frozen v1 JSON contract), like [`Self::bit_facts`].
    pub handle_findings: Vec<HandleFinding>,
    /// FEAT-059 (REQ-018): ranked, actionable remediation guidance synthesised
    /// from the sound findings above — turning "what scry found" into "what to
    /// do about it", for a human or an AI agent. Each carries an actionability
    /// class (fault / unproven / precision-gap / leverageable), a suggested
    /// action, and a verification oracle. Sorted by `(class rank, func_index,
    /// pc)`. Library-only (not in the WIT mirror or the frozen v1 JSON
    /// contract), like [`Self::bit_facts`].
    pub advisories: Vec<Advisory>,
    /// FEAT-065 (REQ-021): per-function identity records — the same two-tier
    /// identity `stamp_obligation_ids` derives (DD-020/FEAT-077/FEAT-087),
    /// surfaced per FUNCTION so [`verify_against`] can (a) pair functions
    /// across two runs and (b) tell whether a function's body changed between
    /// them via [`FuncIdentity::body_shape_hash`] (the AC-mandated
    /// discriminator between `still-open-untouched` and
    /// `still-open-after-edit`). One entry per DEFINED function, sorted by
    /// `func_index`. Library-only (not in the WIT mirror or the frozen v1 JSON
    /// contract), like [`Self::bit_facts`].
    pub func_identities: Vec<FuncIdentity>,
}

/// FEAT-065 (REQ-021): the identity record of one defined function, as used by
/// [`verify_against`]. `ident` / `id_build_local` / `ident_survives_own_edit`
/// are exactly the values `stamp_obligation_ids` folds into every advisory in
/// the function (single source of truth — both come out of the same tier
/// decision); `body_shape_hash` is ALWAYS the operator-shape hash of the body,
/// regardless of which identity tier won.
///
/// GRANULARITY (honest scope): `body_shape_hash` hashes operator NAMES, not
/// immediates (it is the hash the unnamed-identity tier already used). An edit
/// that changes only immediates — `i32.const 0` → `i32.const 7` — therefore
/// reads as "body unchanged". That granularity is what makes `discharged`
/// sound: a shape-preserving edit cannot delete or insert an operator, so the
/// k-th same-kind operator in a region is still the k-th — site correspondence
/// is EXACT. The flip side: `still-open-untouched` means "no operator was
/// added, removed or reordered", not "no byte changed".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncIdentity {
    /// Absolute function index in THIS run (positional; not stable across runs).
    pub func_index: u32,
    /// The tier identity: unique stripped name / raw name / plain name / body
    /// shape hash (DD-020). What `site_key`/`group_key` hashes embed.
    pub ident: String,
    /// See [`Advisory::id_build_local`].
    pub id_build_local: bool,
    /// See [`Advisory::ident_survives_own_edit`].
    pub ident_survives_own_edit: bool,
    /// The operator-shape hash of the body (always computed, every tier).
    pub body_shape_hash: String,
}

/// FEAT-040: one analysis-gap record — a site where scry was conservative.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gap {
    /// Absolute function index where the gap occurred.
    pub func_index: u32,
    /// Operator index (pc) of the conservative site.
    pub pc: u32,
    /// The operator name that triggered the gap (e.g. `f64.add`, `select`).
    pub op: String,
    /// What kind of conservative step this is.
    pub kind: GapKind,
}

/// FEAT-040: the category of an analysis [`Gap`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GapKind {
    /// An operator outside scry's modelled set: the function's abstract state
    /// is scrubbed to ⊤ (sound, but no further facts are learned in it).
    UnsupportedOp,
    /// An unmodelled multi-target branch (`br_table`): control flow scrubbed.
    UnmodeledBranch,
    /// A memory access on a non-i32-shaped address operand: region state
    /// scrubbed to ⊤ (the address could alias anywhere — sound fallback).
    UnmodeledMemoryAddress,
    /// An unmodelled control-flow region (a typed `if`, or a non-empty
    /// block-type `block`) handled by write-set havoc: the locals the region
    /// writes are widened to ⊤ (the rest stay precise — a PARTIAL give-up,
    /// unlike the full-function scrubs above). FEAT-016 fallback.
    UnmodeledControlFlow,
}

/// FEAT-037: a known-bits / congruence fact about one local at one program
/// point. Sound over-approximation: the local's concrete value at this pc is
/// always in the concretization of these fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitFact {
    /// Absolute function index.
    pub func_index: u32,
    /// Operator index (pc) of the `local.set`/`local.tee` that established it.
    pub pc: u32,
    /// The local written.
    pub local_index: u32,
    /// Value width in bits (32 or 64).
    pub width: u32,
    /// Bits known to be 0 (`value & known_zeros == 0`).
    pub known_zeros: u64,
    /// Bits known to be 1 (`value & known_ones == known_ones`).
    pub known_ones: u64,
    /// Congruence modulus: `0` = exact singleton (`value == cong_residue`),
    /// `1` = no congruence fact, `m ≥ 2` = `value ≡ cong_residue (mod m)`.
    pub cong_modulus: u64,
    /// Congruence residue (see `cong_modulus`).
    pub cong_residue: u64,
}

/// FEAT-044: a proven strict-less-than relation `x < bound`, holding on ENTRY
/// to the then-region of the `if` it guards. Sound: the then-branch is taken
/// only when the comparison evaluated true, so `x < bound` holds the instant
/// control enters it. (A consumer that reads the fact deeper in the region must
/// confirm `lhs_local` was not reassigned since the guard — the fact is a
/// guard-entry condition, not a region-wide invariant.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PentagonFact {
    /// Absolute function index.
    pub func_index: u32,
    /// Operator index (pc) of the `if` whose then-region the relation guards.
    pub pc: u32,
    /// The local on the left of the strict comparison (`x` in `x < bound`).
    pub lhs_local: u32,
    /// The right-hand side of the strict relation.
    pub bound: PentagonBound,
    /// `true` when the guard was an unsigned comparison (`lt_u`) — then both
    /// operands are also known `≥ 0`, the form bounds-checking wants.
    pub unsigned: bool,
}

/// FEAT-044: the right-hand side of a [`PentagonFact`] strict relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PentagonBound {
    /// `x < x_other` — a strict relation between two locals.
    Local(u32),
    /// `x < c` — a strict relation against a constant.
    Const(i64),
}

/// FEAT-047 (REQ-015, AC-022): a sound float-interval fact about one local at
/// one program point, from the additive straight-line float pass over
/// [`scry_float`]. The local's concrete f32/f64 value at this pc is always in
/// the concretization of these bounds. Bounds are stored as IEEE bit patterns
/// (so the struct is `Eq` and the JSON stays exact); use [`Self::lo`] /
/// [`Self::hi`] for the `f64` values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FloatFact {
    /// Absolute function index.
    pub func_index: u32,
    /// Operator index (pc) of the `local.set`/`local.tee` that established it.
    pub pc: u32,
    /// The local written.
    pub local_index: u32,
    /// Value width in bits (32 or 64).
    pub width: u32,
    /// Lower bound as `f64::to_bits` (may be `-inf`).
    pub lo_bits: u64,
    /// Upper bound as `f64::to_bits` (may be `+inf`).
    pub hi_bits: u64,
    /// The value may be NaN.
    pub nan: bool,
}

impl FloatFact {
    /// The lower bound as an `f64`.
    pub fn lo(&self) -> f64 {
        f64::from_bits(self.lo_bits)
    }
    /// The upper bound as an `f64`.
    pub fn hi(&self) -> f64 {
        f64::from_bits(self.hi_bits)
    }
}

/// FEAT-049 (REQ-003, MF-007): a Component-Model handle-lifetime fault found by
/// the affine handle-state pass over [`scry_handle`] — a resource handle used or
/// dropped after it was already dropped. Sound (a DEFINITE fault): reported only
/// on a straight-line path where the handle is provably `Dropped` at the site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandleFinding {
    /// Absolute function index.
    pub func_index: u32,
    /// Operator index (pc) of the offending `call` (drop/use of a dropped handle).
    pub pc: u32,
    /// The local holding the handle.
    pub local_index: u32,
    /// The `module.field` name of the canonical-ABI import involved.
    pub via: String,
    /// Which fault.
    pub kind: HandleFindingKind,
}

/// FEAT-049: the category of a [`HandleFinding`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HandleFindingKind {
    /// A resource method / representation call on an already-dropped handle.
    UseAfterDrop,
    /// A second `resource.drop` on an already-dropped handle.
    DoubleDrop,
}

/// FEAT-059 (REQ-018): one piece of actionable remediation guidance synthesised
/// from scry's sound findings — "here is what to do about it", for a human or an
/// AI agent. The [`AdvisoryClass`] is load-bearing: it separates a proven bug
/// from a merely-unproven obligation from an analyzer blind spot, so guidance
/// from a SOUND tool never overclaims a fix. Each advisory names a
/// [`Self::verification`] oracle — what re-running scry should show once the fix
/// lands — closing an AI agent's edit→verify loop against a sound checker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Advisory {
    /// Absolute function index the advisory concerns.
    pub func_index: u32,
    /// Operator index (pc) of the site (`0` for a function-level advisory).
    pub pc: u32,
    /// Actionability class (governs ranking and how to read the advice).
    pub class: AdvisoryClass,
    /// Short machine-stable category code (e.g. `use-after-drop`,
    /// `div-by-zero`, `unsupported-op`, `unbounded-stack`).
    pub code: String,
    /// Human rationale: what the analysis found and why it matters.
    pub detail: String,
    /// The concrete action to improve the code.
    pub suggested_action: String,
    /// The oracle that confirms the fix — what re-running scry should show.
    pub verification: String,
    /// FEAT-055: for an `UnprovenObligation`, a candidate counterexample — the
    /// operand assignment that would trigger the trap, derived from the abstract
    /// state. `None` for other classes. A ready seed for a repro / regression
    /// test; see [`Counterexample`] for the reachability caveat.
    pub counterexample: Option<Counterexample>,
    /// FEAT-064 (REQ-020, DD-020): a STABLE, content-addressed identity for this
    /// site — invariant under instruction insertion elsewhere in the module and
    /// elsewhere in the same function, unlike `(func_index, pc)` which renumbers
    /// on any edit. It is what a fix-verify loop keys on: without it a consumer
    /// comparing two runs cannot distinguish DISCHARGED from MOVED.
    ///
    /// Empty when no identity could be derived. Opaque by construction — the
    /// layout is not a contract; do not parse it.
    pub obligation_id: String,
    /// FEAT-072 (DD-021): identity of the SITE, excluding the advisory code —
    /// so it is STABLE when an obligation changes state. A `div-by-zero`
    /// becoming `proven-safe` changes `obligation_id` but NOT this, which is
    /// what lets a delta view report "this site changed state" instead of
    /// "one identity vanished and an unrelated one appeared".
    ///
    /// Derived here as DATA. It is deliberately NOT paired with an adjudicator
    /// in this release: matching on this key alone was refuted in review
    /// (scry#122), because a positional ordinal can be inherited by a
    /// surviving sibling. Consumers may group and diff by it; nothing in this
    /// release may conclude "discharged" from it.
    pub site_key: String,
    /// FEAT-072 (DD-021): the ORDINAL DOMAIN this site's ordinal is counted
    /// within (function + region path + operator kind), WITHOUT the ordinal.
    ///
    /// This is the aliasing signal made observable: `ObligationId.v` proves a
    /// surviving site can inherit a deleted sibling's ordinal
    /// (survivor_inherits_deleted_identity), and that can only happen inside
    /// one group. Comparing a group's membership across two runs therefore
    /// bounds where identity may have shifted. Necessary but NOT sufficient to
    /// rule aliasing out — the pairing of a deletion with a same-kind insertion
    /// leaves the group unchanged, which is precisely what falsified DD-021.
    pub group_key: String,
    /// FEAT-077 (scry#123, DD-020): TRUE when this advisory's identity keys
    /// (`obligation_id` / `site_key` / `group_key`) are BUILD-LOCAL — unique
    /// within THIS analysis but NOT comparable across builds of the same
    /// source. Set when the function's name-section name carries a Rust legacy
    /// symbol disambiguator (`17h<16 hex>E`) whose stripped form is shared by
    /// another function in the module (dependency generics, measured at 37.8%
    /// of functions on scry's own binary): the disambiguator cannot be dropped
    /// without merging distinct monomorphizations onto one identity, so the
    /// raw name — which churns with crate metadata — is kept, and this flag
    /// says so INSTEAD of letting a consumer diff the id across builds and
    /// read the churn as discharged/new obligations.
    ///
    /// FALSE for every other identity tier (unique stripped name, a name with
    /// no disambiguator, export names, the body-shape hash, module-scoped
    /// advisories): those behave exactly as before this flag existed.
    pub id_build_local: bool,
    /// FEAT-087 (scry#122 item 2): TRUE when this advisory's identity keys
    /// survive an edit to the function's OWN body — the property an
    /// adjudicator needs, and a DIFFERENT question from [`Advisory::id_build_local`].
    ///
    /// The two bits are INDEPENDENT, not a ranking:
    ///
    /// | tier                         | `id_build_local` | `ident_survives_own_edit` |
    /// |------------------------------|------------------|---------------------------|
    /// | unique stripped name         | false            | **true**                  |
    /// | shared stripped -> raw name  | **true**         | **true**                  |
    /// | name, no disambiguator       | false            | **true**                  |
    /// | unnamed -> `body_shape_hash` | false            | **false**                 |
    ///
    /// FALSE only for the body-shape-hash tier, whose ident is by construction
    /// a hash of the very bytes an edit changes. That tier is NOT build-local —
    /// the hash is deterministic, so it IS comparable across builds — which is
    /// exactly why one bit could not express both facts. Measured on a stripped
    /// build of scry's own binary, that tier is 766 of 766 obligation-carrying
    /// functions and all 10,520 obligations; stripping is standard in release
    /// builds.
    ///
    /// CONSUMER RULE: treat a missing key in a later build as evidence the site
    /// is gone ONLY when `!id_build_local && ident_survives_own_edit`. Otherwise
    /// the honest verdict is `uncertain` — never `discharged` (REQ-021).
    pub ident_survives_own_edit: bool,
}

/// FEAT-055 (REQ-018): a candidate counterexample for an `UnprovenObligation`
/// advisory — the operand value(s) that would make the site trap.
///
/// SOUNDNESS CAVEAT (why "candidate"): the values are read off scry's abstract
/// state, which OVER-approximates. That the divisor's interval *contains* 0 does
/// not prove 0 is *reachable* on a concrete run. So this is a starting point for
/// a repro / regression test, NOT a proof the trap fires — consistent with the
/// `UnprovenObligation` class. Confirming reachability (a genuine
/// symbolic/SMT-checked input) is the deferred full-counterexample tier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {
    /// Human/agent-readable trapping condition.
    pub trigger: String,
    /// Concrete candidate operand assignments (empty when none is derivable).
    pub witness: Vec<CxAssign>,
}

/// FEAT-055: one operand assignment in a [`Counterexample`] witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CxAssign {
    /// The operand role (e.g. `divisor`, `dividend`, `address`).
    pub operand: String,
    /// The candidate trapping value.
    pub value: i64,
}

/// FEAT-059 (REQ-018): the actionability class of an [`Advisory`]. Ranked
/// (lower discriminant = higher priority). The split is the honesty guarantee:
/// a POTENTIAL-TRAP is an `UnprovenObligation` ("prove/guard it"), never a
/// `DefiniteFault` ("it's a bug").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdvisoryClass {
    /// A real bug scry PROVED (use-after-drop, double-drop). Fix it.
    DefiniteFault,
    /// A trap scry could not discharge (a POTENTIAL-TRAP). Prove / guard / bound
    /// it — this is NOT a claim that it is a bug.
    UnprovenObligation,
    /// A site where scry lost precision (degraded to ⊤). Restructure for
    /// analyzability, or accept the limitation.
    PrecisionGap,
    /// A property scry PROVED (PROVEN-SAFE / a proven bound). A defensive
    /// runtime check here may be soundly relied on or elided.
    LeverageableFact,
}

impl AdvisoryClass {
    /// Ranking key (0 = highest priority).
    pub fn rank(self) -> u8 {
        match self {
            AdvisoryClass::DefiniteFault => 0,
            AdvisoryClass::UnprovenObligation => 1,
            AdvisoryClass::PrecisionGap => 2,
            AdvisoryClass::LeverageableFact => 3,
        }
    }

    /// FEAT-065 (REQ-021): is this class an OPEN obligation — something an
    /// edit could aim to resolve (a proven fault, an unproven obligation, or a
    /// precision gap) — as opposed to a proven fact
    /// ([`Self::LeverageableFact`], which [`verify_against`] treats as the
    /// PROVEN-SAFE state rather than as an obligation)?
    pub fn is_open_obligation(self) -> bool {
        !matches!(self, AdvisoryClass::LeverageableFact)
    }
}

/// FEAT-067 (REQ-017, REQ-020): a filter surface so a consumer ASKS instead of
/// scraping. The bounded slice of the FEAT-056 queryable-CPG idea — filtering
/// over the existing result, with no new graph substrate and no query language.
///
/// Every field is an independent constraint and they are ANDed. `None` means
/// "unconstrained", so `Query::default()` selects everything — the identity of
/// a conjunction, not a special case.
///
/// `op` and `gap_kind` are NOT fields of [`Advisory`]; they are joined from the
/// gap and trap-check records at the same `(func_index, pc)`. That join is why
/// this is a query surface rather than a filter over one vector.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Query {
    /// Advisory class (`DefiniteFault` / `UnprovenObligation` / ...).
    pub class: Option<AdvisoryClass>,
    /// Advisory code, e.g. `div-by-zero`.
    pub code: Option<String>,
    /// Absolute function index.
    pub func_index: Option<u32>,
    /// Operator name in wasm text format, e.g. `i32.load`. FEAT-092 made these
    /// consistent; before it, 2,800 of 10,520 were Rust enum identifiers.
    pub op: Option<String>,
    /// Gap kind, joined from the gap record at the same site.
    pub gap_kind: Option<GapKind>,
}

impl AnalysisResult {
    /// FEAT-067: the advisories matching EVERY constraint set on `q`, in result
    /// order, each carrying its stable obligation identity (REQ-020).
    pub fn query(&self, q: &Query) -> Vec<&Advisory> {
        self.advisories
            .iter()
            .filter(|a| {
                // Each `Some` is a constraint; `None` imposes none. `all` over
                // an empty constraint set is TRUE, which is why
                // `Query::default()` selects everything without a special case.
                q.class.is_none_or(|c| a.class == c)
                    && q.code.as_deref().is_none_or(|c| a.code == c)
                    && q.func_index.is_none_or(|f| a.func_index == f)
                    // `op` and `gap_kind` are joined from the records that DO
                    // carry them, at the same site. An advisory with no such
                    // record cannot satisfy the constraint, so it is excluded
                    // rather than admitted — a filter must never widen.
                    && q.op.as_deref().is_none_or(|want| {
                        self.gaps
                            .iter()
                            .any(|g| g.func_index == a.func_index && g.pc == a.pc && g.op == want)
                            || self.trap_checks.iter().any(|t| {
                                t.func_index == a.func_index && t.pc == a.pc && t.op == want
                            })
                    })
                    && q.gap_kind.is_none_or(|want| {
                        self.gaps.iter().any(|g| {
                            g.func_index == a.func_index && g.pc == a.pc && g.kind == want
                        })
                    })
            })
            .collect()
    }
}

/// FEAT-045 (REQ-014, MF-006): a runtime-trap classification for one
/// division/remainder operator. scry's first runtime-error verdict — the
/// Astrée/Polyspace-style "PROVEN-SAFE vs POTENTIAL-TRAP" judgement, derived
/// from the interval domain at the operator's program point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TrapCheck {
    /// Absolute function index.
    pub func_index: u32,
    /// Operator index (pc) of the div/rem.
    pub pc: u32,
    /// The operator name (e.g. `i32.div_s`).
    pub op: String,
    /// Which trap condition this verdict concerns.
    pub kind: TrapKind,
    /// The verdict.
    pub verdict: TrapVerdict,
}

/// FEAT-045: the trap condition a [`TrapCheck`] classifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrapKind {
    /// The divisor may be zero (`div`/`rem` by zero traps in Wasm).
    DivByZero,
    /// Signed `div` overflow: `INT_MIN / -1` traps (only `i32/i64.div_s`;
    /// `rem_s` does NOT trap on this case, so it is never classified for rem).
    SignedOverflow,
    /// FEAT-046: an out-of-bounds linear-memory access (the effective address
    /// plus the access width may exceed the memory's guaranteed size).
    OutOfBounds,
}

/// FEAT-045: the verdict of a [`TrapCheck`]. SOUND direction: `ProvenSafe` is
/// emitted only when the interval domain proves the trap CANNOT occur on any
/// concrete run; every residual possibility (including ⊤/unknown operands) is
/// `PotentialTrap`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrapVerdict {
    /// The trap provably cannot occur (the operand interval excludes the
    /// trapping value).
    ProvenSafe,
    /// The trap may occur (the operand interval includes the trapping value,
    /// or the operand is unknown). The sound default.
    PotentialTrap,
}

/// FEAT-027: human-readable metadata for one function index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionMeta {
    /// Absolute function index (imports occupy the low indices, then defined).
    pub func_index: u32,
    /// Best human-readable name, in priority order: custom `name` section →
    /// first export name → import `module.field`. `None` when the module
    /// carries no name for this index (fall back to the index).
    pub name: Option<String>,
    /// True when this index is an imported function.
    pub imported: bool,
    /// Export names for this function (empty when not exported). A function may
    /// be exported under several names.
    pub exports: Vec<String>,
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
/// scry#133: DERIVED, never hand-maintained. This was a literal, the v3.2.5
/// bump missed it, and the shipped 3.2.5 component reported itself as 3.2.4 in
/// its own diagnostics. Consumers identify the producing analyzer from this
/// string, so a stale value misattributes bug reports to the wrong build.
/// `env!` resolves at compile time from the crate's version, which the
/// workspace sets — so it cannot drift from the published version again.
const SCRY_VERSION: &str = env!("CARGO_PKG_VERSION");
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
    /// FEAT-038: the memory is provably fixed at `memory_initial_pages` — it is
    /// module-private (not imported/exported/shared) and no defined function
    /// grows it — so `memory.size` returns that exact constant. When false,
    /// `memory.size` is the sound interval `[memory_initial_pages,
    /// memory_max_pages-or-65536]` (memory may have been grown by this module,
    /// the host, or another thread).
    memory_size_constant: bool,
    /// FEAT-038: first memory's declared initial / maximum page counts.
    memory_initial_pages: u64,
    memory_max_pages: Option<u64>,
    /// FEAT-038: total memory count (precise `memory.size`/`grow` only when 1)
    /// and whether memory index 0 is 64-bit (2^48-page ceiling + i64 result).
    memory_count: u64,
    memory_is_64: bool,
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
    /// Relational octagon over the locals (FEAT-016 slice-2b-ii), carried in
    /// lockstep with `locals` through the structured-CFG fixpoint. Dimension
    /// equals `locals.len()`; variable `k` is local `k`. `top` means "no
    /// relation known" (so projecting it back is the identity — existing
    /// interval-only behaviour is preserved until a transfer/guard populates
    /// it). Soundness rule: any write to a local that the octagon transfer
    /// does not model must `forget` that variable.
    octagon: Octagon,
    /// FEAT-058: content-sensitive linear-memory abstraction (scry-sai-segment),
    /// carried in lockstep with `locals`/`octagon` through the structured-CFG
    /// fixpoint — joined at every merge and widened at every loop header, or the
    /// fixpoint would be unsound. Maps byte offsets to interval content for i32
    /// (4-byte) accesses; `top` means "no memory content known" (every load ⊤,
    /// the pre-FEAT-058 behaviour). Soundness rule: any store scry cannot pin to
    /// a single in-bounds i32 cell must invalidate (⊤) the possibly-touched byte
    /// window, never record content; any degrade resets it to `top`.
    mem: Segmentation,
    /// FEAT-057 slice 2a: convex-polyhedra domain over the locals
    /// (scry-sai-poly), carried in lockstep with `locals`/`octagon`/`mem`
    /// through the structured-CFG fixpoint — joined at every merge and widened
    /// at every loop header, or the fixpoint would be unsound. Dimension
    /// equals `locals.len()`; variable `k` is local `k`; `top` means "no
    /// linear fact known". Soundness rules: (1) any write to a local that
    /// [`Interp::poly_transfer`] does not model must `project` (FM-forget)
    /// that variable — a constraint surviving a reassignment is a false
    /// proof; (2) over Wasm's WRAPPING i32 arithmetic an assignment equality
    /// (`z = x + y`) is added ONLY when the interval domain proves no-wrap
    /// (`scry_interval::i32_add`/`i32_sub` returns ⊤ exactly when wrap is
    /// possible) — never an unguarded equality; (3) any degrade resets it to
    /// `top`.
    poly: Poly,
    /// Once we see an unsupported construct in a function, we stop
    /// emitting fresh program-points for it — the abstract state has
    /// become uninformative (all-top) and further records would just
    /// be noise.
    degraded: bool,
    /// FEAT-040: analysis-gap records collected during this function's walk
    /// (every unsupported-op fallback), drained by the caller in phase 2.
    /// Independent of `emit_diagnostics` so the gap report is always available.
    gaps: Vec<Gap>,
    /// FEAT-045: division/remainder trap-classification records collected during
    /// this function's walk, drained by the caller in the authoritative pass
    /// (same as `gaps`). One entry per applicable trap condition per div/rem.
    trap_checks: Vec<TrapCheck>,
    /// FEAT-089: locals known NON-ZERO on the current path — the narrow
    /// predicate fact an interval cannot hold (`!= 0` is a hole in the middle
    /// of a range). Established ONLY on the fall-through edge of a
    /// [`Interp::try_guard_brif`] guard whose taken edge pins the local to
    /// `== 0` (the canonical `local.get L; i32.eqz; br_if D` div-by-zero
    /// repair), and consulted ONLY by the div/rem trap check
    /// ([`classify_div_trap`]) — a targeted fact feeding one decision, not a
    /// general domain (same shape as FEAT-084's known-bits reduction).
    ///
    /// SOUNDNESS — a fact that survives a write is a FALSE PROOF, so the
    /// invalidation is over-approximated. A fact dies on:
    ///   * `local.set` / `local.tee` to its local (the only wasm writes to a
    ///     local), including the tee the guard peephole applies itself;
    ///   * ANY call (`call` / `call_indirect`): all facts are cleared. Wasm
    ///     locals are callee-inaccessible, so this is conservative rather
    ///     than semantically forced — but cheap and safe;
    ///   * every region boundary: cleared on leaving a `block`, at the start
    ///     of EVERY `loop` fixpoint pass (a back-edge must never carry a
    ///     fact) and on leaving the loop, and on entering a `havoc_region`
    ///     (`if` / unmodelled shapes — the body is not interpreted);
    ///   * any degrade ([`Self::scrub_to_top`]).
    ///
    /// [`Label`]/`BreakState` deliberately carry NO facts, so a state merged
    /// in from a branch edge can never contribute one; combined with the
    /// region-boundary clearing, a join can only ever MEET facts (drop them),
    /// never union them. A fact therefore survives only straight-line
    /// interpret_op-processed ops (none of which write locals except the two
    /// killers above) and a plain `br_if` FALL-THROUGH (path narrowing —
    /// br_if writes nothing, and its taken edge goes through a fact-free
    /// label).
    nonzero_locals: BTreeSet<u32>,
}

impl FuncCtx {
    fn new(locals: Vec<AbstractValue>) -> Self {
        let octagon = scry_octagon::top(locals.len() as u32);
        let poly = scry_poly::top(locals.len() as u32);
        Self {
            locals,
            operand_stack: Vec::new(),
            octagon,
            mem: scry_segment::top(),
            poly,
            degraded: false,
            gaps: Vec::new(),
            trap_checks: Vec::new(),
            nonzero_locals: BTreeSet::new(),
        }
    }

    /// Drop the operand stack and widen every local to top. Used when
    /// we hit any operator outside the v0.2 AC#1 supported set —
    /// soundness over precision (REQ-001 / DD-005). The octagon is reset to
    /// `top` too (all relations forgotten — sound).
    ///
    /// FEAT-040: every degradation MUST record a [`Gap`] (passed in), so no
    /// function can silently degrade to ⊤ — the gap report is complete. The
    /// `degraded` early-return elsewhere means only the FIRST scrub records a
    /// gap (subsequent ops are skipped), which is the give-up point we want.
    fn scrub_to_top(&mut self, gap: Gap) {
        if !self.degraded {
            self.gaps.push(gap);
        }
        for slot in self.locals.iter_mut() {
            *slot = AbstractValue::I32Interval(domain::top());
        }
        self.operand_stack.clear();
        self.octagon = scry_octagon::top(self.locals.len() as u32);
        // FEAT-058: a degrade means we can no longer track control flow, so any
        // subsequent store could land anywhere — forget all memory content.
        self.mem = scry_segment::top();
        // FEAT-057: linear facts degrade with everything else (rule 3).
        self.poly = scry_poly::top(self.locals.len() as u32);
        // FEAT-089: predicate facts degrade with everything else.
        self.nonzero_locals.clear();
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

/// FEAT-041: extract the surfaced relational constraints from an octagon, as
/// the core's `RelationalConstraint` (converting `scry_octagon::Relation`).
fn snapshot_relational(octagon: &Octagon) -> Vec<RelationalConstraint> {
    scry_octagon::relations(octagon)
        .into_iter()
        .map(|r| RelationalConstraint {
            a: r.a,
            b: r.b,
            kind: match r.kind {
                scry_octagon::RelKind::Diff => RelKind::Diff,
                scry_octagon::RelKind::Sum => RelKind::Sum,
            },
            bound: r.bound,
        })
        .collect()
}

/// FEAT-062: snapshot the tracked linear-memory content (the segmentation's
/// cells) as a list of `MemSegment` records, in ascending offset order.
fn snapshot_memory(mem: &Segmentation) -> Vec<MemSegment> {
    mem.segments()
        .iter()
        .map(|s| MemSegment {
            lo: s.lo,
            hi: s.hi,
            value: s.val,
        })
        .collect()
}

/// FEAT-057 slice 2a: snapshot the polyhedron's general linear constraints as
/// output records. Filtered to constraints over ≥ 2 distinct locals — a unary
/// poly bound duplicates what the interval domain already publishes (the
/// FEAT-041 not-implied-by-unary spirit); the unary constraint stays INSIDE
/// the domain, where it still feeds entailment across joins. ⊥ (an
/// unreachable point) snapshots as empty — claiming nothing is sound.
fn snapshot_linear(poly: &Poly) -> Vec<LinearConstraint> {
    if poly.is_bottom() {
        return Vec::new();
    }
    poly.constraints()
        .iter()
        .filter(|c| c.coeffs.iter().filter(|&&a| a != 0).count() >= 2)
        .map(|c| LinearConstraint {
            terms: c
                .coeffs
                .iter()
                .enumerate()
                .filter(|&(_, &a)| a != 0)
                .map(|(i, &a)| LinearTerm {
                    local_index: i as u32,
                    coeff: a,
                })
                .collect(),
            bound: c.bound,
        })
        .collect()
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

/// FEAT-023: snapshot the abstract operand-stack (bottom → top) for a
/// `ProgramPoint`. The values are the same sound abstract values as the
/// locals; no octagon reduction (the octagon is over locals, not stack slots).
fn snapshot_stack(stack: &[AbstractValue]) -> Vec<AbstractValue> {
    stack.iter().map(clone_value).collect()
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
    // FEAT-038: the first memory's declared page limits, for `memory.size` /
    // `memory.grow` modelling. `memory_initial_pages` is the page count
    // `memory.size` returns when memory is fixed (bounded_memory); the maximum
    // (when declared) caps the size interval otherwise.
    let mut memory_initial_pages: u64 = 0;
    let mut memory_max_pages: Option<u64> = None;
    // FEAT-038 soundness (clean-room): the constant-`memory.size` collapse is
    // valid ONLY for a module-PRIVATE memory — not imported (host supplies and
    // may grow it), not exported (host can grow it via the API), not shared
    // (another thread may grow it). For any of those, `memory.size` is the
    // sound interval `[initial, max]`, never a constant.
    let mut memory_is_imported: bool = false;
    let mut memory_is_exported: bool = false;
    let mut memory_is_shared: bool = false;
    // FEAT-038 soundness (clean-room): total memory count (imports + defined)
    // and whether memory index 0 is 64-bit. `memory.size`/`memory.grow` are
    // modelled precisely ONLY for the single-memory, memidx-0 case; >1 memory
    // or a non-zero memidx ⇒ ⊤ (only index 0 is captured). A 64-bit memory
    // grows to 2^48 pages, so its ceiling is 2^48, not the memory32 65536.
    let mut memory_count: u64 = 0;
    let mut memory_is_64: bool = false;

    // ── FEAT-021 shadow-stack state ──────────────────────────────
    // Indices of mutable i32 globals — the candidates for the C-style
    // `__stack_pointer` the shadow-stack analysis weighs frames against.
    let mut mutable_i32_globals: Vec<u32> = Vec::new();

    // ── FEAT-022 reachability roots ──────────────────────────────
    // Exported functions + the optional start function are the entry
    // points the `reachable-from-exports` set (FEAT-022) is computed
    // from (absolute function indices).
    let mut exported_funcs: Vec<u32> = Vec::new();
    let mut start_func: Option<u32> = None;

    // ── FEAT-027 human-readable function metadata ────────────────
    // Names from three sources, resolved later in priority order:
    // the custom `name` section (canonical debug names), else an
    // export name, else an import "module.field". `import_func_meta`
    // is indexed by import order (absolute index == position, since
    // imports occupy the low indices); `export_names`/`name_section`
    // are (abs-index, name) pairs.
    let mut import_func_meta: Vec<String> = Vec::new();
    let mut export_names: Vec<(u32, String)> = Vec::new();
    let mut name_section: Vec<(u32, String)> = Vec::new();

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
    // FEAT-036 soundness: true if the module declares OR imports ANY table
    // (of any element type). A table is the only funcref container besides a
    // `ref.func` instruction, so its mere presence means a defined function's
    // address may be reachable indirectly (or by the host, via an exported or
    // imported table) — which the param-range gate cannot otherwise bound.
    let mut module_has_table: bool = false;
    // FEAT-043 soundness (clean-room #5): true if table 0 is host-writable —
    // imported (the host supplies, and may overwrite, its slots) or exported
    // (the host holds the export and may write through it). scry sees no
    // `table.*` opcode for a host write, so an active-segment-resolved slot
    // cannot be trusted: the host may install a callee of arbitrary frame
    // depth. Forces `contents_known = false` so indirect dispatch is Unknown.
    let mut table0_host_writable: bool = false;
    // FEAT-036 soundness: true if a `ref.func` appears OUTSIDE a function body —
    // in a global's init expression or an element segment's items. Such a
    // funcref to a defined function can escape (e.g. via an exported global) to
    // a `call_ref`/host call the param-range gate cannot bound, and the
    // body-only operator scan would miss it. (Third clean-room finding.)
    let mut func_ref_taken_in_const: bool = false;
    // FEAT-039: every function whose address is taken anywhere (a `ref.func` in
    // a body / global init / element item, or a bare element-segment func index)
    // — absolute indices. When funcrefs can escape (open world, NOT
    // `callers_fully_known`), these are added as reachability roots so
    // `reachable_from_exports` stays a sound SUPERSET (the host / an import may
    // dispatch any escaped funcref). May contain duplicates / imports; filtered
    // when seeded.
    let mut address_taken_funcs: Vec<u32> = Vec::new();
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
    let mut provenance_section: Option<scry_provenance::ProvenanceSection> = None;

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
                        // FEAT-027: imported funcs occupy the low indices in
                        // import order; record "module.field" as a fallback name.
                        import_func_meta.push(alloc::format!("{}.{}", imp.module, imp.name));
                    }
                    // FEAT-036 soundness: an imported table is host-controlled —
                    // the host can dispatch through it with arbitrary arguments.
                    if matches!(imp.ty, wasmparser::TypeRef::Table(_)) {
                        module_has_table = true;
                        // Imported tables occupy the low table-index space, so
                        // the first one is table 0: it is host-supplied and
                        // host-writable (clean-room #5).
                        table0_host_writable = true;
                    }
                    // FEAT-038 soundness: an imported memory is host-supplied —
                    // its true size is ≥ the declared minimum and the host may
                    // grow it. Capture its declared limits (the minimum is the
                    // sound lower bound `memory.size` must use) and mark it
                    // host-controlled / possibly-shared.
                    if let wasmparser::TypeRef::Memory(memty) = imp.ty {
                        // Imported memories occupy the low memory-index space, so
                        // the first one is memory index 0. Capture index 0 only.
                        if memory_count == 0 {
                            memory_is_imported = true;
                            memory_initial_pages = memty.initial;
                            memory_max_pages = memty.maximum;
                            memory_is_shared |= memty.shared;
                            memory_is_64 = memty.memory64;
                        }
                        memory_count += 1;
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
            Payload::ExportSection(reader) => {
                // FEAT-022: exported FUNCTIONS are reachability roots.
                for entry in reader {
                    let ex = entry.map_err(|e| {
                        AnalyzeError::InvalidModule(format!("export section: {e}"))
                    })?;
                    if matches!(ex.kind, wasmparser::ExternalKind::Func) {
                        exported_funcs.push(ex.index);
                        // FEAT-027: keep the export name for readable metadata.
                        export_names.push((ex.index, alloc::string::String::from(ex.name)));
                    }
                    // FEAT-038 soundness: an exported memory can be grown by the
                    // host through the embedder API, so `memory.size` is not a
                    // constant even with no in-module `memory.grow`.
                    if matches!(ex.kind, wasmparser::ExternalKind::Memory) {
                        memory_is_exported = true;
                    }
                    // FEAT-043 soundness (clean-room #5): an exported table 0 is
                    // held by the host, which can overwrite its slots through the
                    // embedder API with a callee of arbitrary frame depth.
                    if matches!(ex.kind, wasmparser::ExternalKind::Table) && ex.index == 0 {
                        table0_host_writable = true;
                    }
                }
            }
            Payload::StartSection { func, .. } => {
                // FEAT-022: the start function is a reachability root.
                start_func = Some(func);
            }
            Payload::MemorySection(reader) => {
                // v0.3 region domain (FEAT-005): the first
                // declared memory's minimum-pages count
                // becomes the lower bound on the single
                // "default" region's size. Multi-memory
                // (post-MVP) is not yet supported — we use
                // the first entry only.
                let mut first_defined = true;
                for entry in reader {
                    let mem = entry
                        .map_err(|e| AnalyzeError::InvalidModule(format!("memory section: {e}")))?;
                    // The first DEFINED memory anchors the v0.3 region floor.
                    if first_defined {
                        memory_min_bytes = mem.initial.saturating_mul(WASM_PAGE_SIZE);
                        first_defined = false;
                    }
                    // FEAT-038: capture memory INDEX 0's limits. Imports precede
                    // defined memories in the index space, so a defined memory is
                    // index 0 only when no memory was imported (memory_count == 0).
                    if memory_count == 0 {
                        memory_initial_pages = mem.initial;
                        memory_max_pages = mem.maximum;
                        memory_is_shared |= mem.shared;
                        memory_is_64 = mem.memory64;
                    }
                    memory_count += 1;
                }
            }
            Payload::GlobalSection(reader) => {
                // FEAT-021: record which globals are MUTABLE i32 — the
                // candidates for the linear-memory shadow-stack pointer
                // (Rust/LLVM's `__stack_pointer`, conventionally global 0).
                // Their index here is the global index (no global imports are
                // modelled — a sound limitation: an imported SP would leave
                // `mutable_i32_globals` not naming it, and frame detection
                // would then report Unknown rather than mis-count).
                let mut gidx: u32 = 0;
                for entry in reader {
                    let g = entry.map_err(|e| {
                        AnalyzeError::InvalidModule(format!("global section: {e}"))
                    })?;
                    if g.ty.mutable && matches!(g.ty.content_type, wasmparser::ValType::I32) {
                        mutable_i32_globals.push(gidx);
                    }
                    // FEAT-036 soundness: a `ref.func` in the init expr takes a
                    // defined function's address (the global can be exported /
                    // read by the host) — outside any function body.
                    if const_expr_takes_func_ref(&g.init_expr) {
                        func_ref_taken_in_const = true;
                    }
                    // FEAT-039: collect the addressed function(s) as escape roots.
                    const_expr_ref_func_targets(&g.init_expr, &mut address_taken_funcs);
                    gidx = gidx.saturating_add(1);
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
                    // FEAT-036 soundness: any declared table (any element type)
                    // is a potential funcref container / indirect-dispatch root.
                    module_has_table = true;
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
                    // FEAT-036 soundness: any element segment that names defined
                    // functions takes their addresses. Active segments imply a
                    // table (already caught), but passive/declared segments need
                    // no table, so flag the escape uniformly here. (Third
                    // clean-room finding.)
                    if element_items_take_func_ref(&element.items)? {
                        func_ref_taken_in_const = true;
                    }
                    // FEAT-039: collect the named functions as escape roots (any
                    // table / segment kind — host or `call_indirect` may reach
                    // them once funcrefs escape).
                    element_items_ref_func_targets(&element.items, &mut address_taken_funcs);
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
                        Ok(section) => provenance_section = Some(section),
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
            // FEAT-027: the standard `name` custom section maps function
            // indices to human-readable names. Best-effort — a malformed
            // entry is skipped, never an error (debug info is advisory).
            Payload::CustomSection(reader) if reader.name() == "name" => {
                let names = wasmparser::NameSectionReader::new(wasmparser::BinaryReader::new(
                    reader.data(),
                    reader.data_offset(),
                ));
                for subsection in names {
                    let Ok(subsection) = subsection else { break };
                    if let wasmparser::Name::Function(map) = subsection {
                        for naming in map {
                            let Ok(naming) = naming else { break };
                            name_section
                                .push((naming.index, alloc::string::String::from(naming.name)));
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
    let mut func_table = if !table_section_seen || !table0_is_funcref {
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

    // FEAT-043 soundness (clean-room #4): the static element-segment shape
    // tells us the table's *initial* contents, but a Wasm table is mutable
    // module-global state. If ANY defined function can write table 0
    // (`table.set` / `table.fill` / `table.grow` on it, or it is the
    // destination of a `table.copy` / `table.init`), a slot resolved from
    // the active segments may be overwritten at runtime with a deeper-framed
    // callee — so the resolved `call_indirect` target (and its stack frame)
    // is no longer a sound enumeration. Clear `contents_known` so every
    // downstream consumer (resolved stack weighting, interpret-time
    // resolution, and the `compute_stack_usage` Unknown guard) falls back to
    // the conservative whole-table over-approximation / Unknown.
    let table0_mutated = defined_funcs.iter().any(|f| {
        f.ops.iter().any(|op| match op {
            Operator::TableSet { table }
            | Operator::TableFill { table }
            | Operator::TableGrow { table }
            | Operator::TableInit { table, .. } => *table == 0,
            Operator::TableCopy { dst_table, .. } => *dst_table == 0,
            _ => false,
        })
    });
    if table0_mutated || table0_host_writable {
        func_table.contents_known = false;
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

    // FEAT-038: scry's OWN bounded-memory determination — no `memory.grow` in
    // any defined function ⇒ linear memory is fixed at its declared initial
    // size (verify-not-trust; computed here, before the fixpoint, so the
    // `memory.size` transfer can return the exact page count). Reused for
    // `verified_premises` below.
    let saw_memory_grow = defined_funcs.iter().any(|f| {
        f.ops
            .iter()
            .any(|op| matches!(op, Operator::MemoryGrow { .. }))
    });
    let bounded_memory = !saw_memory_grow;
    // FEAT-038 soundness (clean-room): `memory.size` is the EXACT initial-page
    // constant only for a module-PRIVATE memory grown by no one — not imported,
    // not exported, not shared, and with no in-module `memory.grow`. Then only
    // this module's defined code could grow it, which `bounded_memory` rules
    // out. Otherwise `memory.size` is the sound interval `[initial, max]`.
    let memory_size_constant =
        bounded_memory && !memory_is_imported && !memory_is_exported && !memory_is_shared;

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
                memory_size_constant,
                memory_initial_pages,
                memory_max_pages,
                memory_count,
                memory_is_64,
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
                /*emit_gaps=*/ None,
                /*emit_trap_checks=*/ None,
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
        memory_size_constant,
        memory_initial_pages,
        memory_max_pages,
        memory_count,
        memory_is_64,
        defined_funcs: &defined_funcs,
        summaries: &summaries,
    };

    let mut points: Vec<ProgramPoint> = Vec::new();
    let mut call_graph: Vec<CallEdge> = Vec::new();
    let mut gaps: Vec<Gap> = Vec::new();
    let mut trap_checks: Vec<TrapCheck> = Vec::new();
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
            /*emit_gaps=*/ Some(&mut gaps),
            /*emit_trap_checks=*/ Some(&mut trap_checks),
        )?;
    }
    gaps.sort_by_key(|g| (g.func_index, g.pc));
    // FEAT-045 soundness: `classify_div_trap` runs on EVERY fixpoint pass, so a
    // div/rem in a loop body can collect a stale `ProvenSafe` from an early
    // (pre-widening) iterate alongside the `PotentialTrap` of the converged
    // iterate. Reconcile per `(func, pc, kind)` with `PotentialTrap` dominating
    // `ProvenSafe`: the converged interval is the widest in a widening chain, so
    // if it excludes the trap value every iterate did (all `ProvenSafe`), and if
    // it includes it the converged pass contributes the `PotentialTrap` that
    // dominates. Either way the surviving verdict is the sound (converged) one.
    trap_checks.sort_by_key(|t| (t.func_index, t.pc, t.kind as u8));
    trap_checks.dedup_by(|next, kept| {
        if kept.func_index == next.func_index && kept.pc == next.pc && kept.kind == next.kind {
            if next.verdict == TrapVerdict::PotentialTrap {
                kept.verdict = TrapVerdict::PotentialTrap;
            }
            true
        } else {
            false
        }
    });

    // ───────────────────────────────────────────────────────────
    // Assemble the per-function-summary output records (FEAT-007).
    // ───────────────────────────────────────────────────────────
    // FEAT-036: interprocedural parameter ranges. A function's params are sound
    // to narrow ONLY when scry has accounted for EVERY caller. The join over the
    // recorded DIRECT call sites is the complete caller set iff there is NO
    // other way to reach the function with an argument scry did not capture.
    //
    // The external / unseen entry points are:
    //   * exports and the start function — invoked by the host with unknown
    //     args (gated per-function below); and
    //   * ANY indirect dispatch. scry cannot soundly enumerate indirect
    //     targets: its static table model under-reports them (passive/declared
    //     element segments, runtime `table.init`/`set`, non-constant indices),
    //     and several dispatch ops (`return_call_indirect`, `call_ref`) are
    //     unsupported — they scrub to ⊤ and record NO call-graph edge, so an
    //     edge-based test misses them entirely. A host holding an exported (or
    //     imported) table can likewise `call_indirect` with arbitrary args.
    //
    // Root-cause-sound rule: a non-null funcref to a defined function can ONLY
    // come from a `ref.func` instruction or a table (element segments). If the
    // module has NEITHER a table (declared or imported) NOR any `ref.func`
    // ANYWHERE — function bodies (`any_funcref_escape`) AND the const positions
    // a body scan misses: global init exprs and element-segment items
    // (`func_ref_taken_in_const`) — then no funcref to any defined function can
    // exist anywhere (code, table, global, or returned/handed to the host), so
    // NO indirect or host dispatch is possible and the recorded direct calls
    // are provably the complete caller set. Only then may we narrow. (A future
    // slice can recover precision with whole-table / escape analysis.)
    // Defense-in-depth: besides the funcref-origin signals above, also bail on
    // the *presence* of any indirect-dispatch operator. In valid Wasm these
    // imply a table (so `module_has_table` already fires), but matching the ops
    // directly makes the gate robust to malformed input and to dispatch ops the
    // value interpreter does not model (`return_call_indirect`, `call_ref` fall
    // through to the scrub-to-⊤ arm and record no call-graph edge) — exactly the
    // class of "an op slipped through" the clean-room kept surfacing.
    let any_funcref_escape = defined_funcs.iter().any(|f| {
        f.ops.iter().any(|op| {
            matches!(
                op,
                Operator::RefFunc { .. }
                    | Operator::CallIndirect { .. }
                    | Operator::ReturnCallIndirect { .. }
                    | Operator::CallRef { .. }
            )
        })
    });
    let callers_fully_known = !module_has_table && !any_funcref_escape && !func_ref_taken_in_const;

    let mut function_summaries: Vec<FunctionSummary> = Vec::with_capacity(defined_funcs.len());
    for (defined, func) in defined_funcs.iter().enumerate() {
        if let Some(entry) = summaries.get(defined).and_then(|s| s.as_ref()) {
            let abs = func.abs_index;
            let n = func.params.len();
            let top_params = || (0..n).map(|_| AbstractValue::Unknown).collect::<Vec<_>>();
            let param_ranges = if n == 0
                || !callers_fully_known
                || exported_funcs.contains(&abs)
                || start_func == Some(abs)
            {
                top_params()
            } else {
                // Join arguments over every direct call site reaching `abs`.
                let mut acc: Option<Vec<AbstractValue>> = None;
                for e in &call_graph {
                    if !e.indirect && e.resolved_targets.contains(&abs) && e.arg_ranges.len() == n {
                        acc = Some(match acc {
                            Some(a) => join_locals(&a, &e.arg_ranges),
                            None => e.arg_ranges.iter().map(clone_value).collect(),
                        });
                    }
                }
                // No direct caller found (dead / unreached): nothing constrains
                // the params, so ⊤ — never invent a tighter range.
                acc.unwrap_or_else(top_params)
            };
            function_summaries.push(FunctionSummary {
                func_index: abs,
                param_count: n as u32,
                result_summary: entry.result_summary.iter().map(clone_value).collect(),
                context_sensitive: entry.context_sensitive,
                recursive: entry.recursive,
                param_ranges,
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
    let provenance = provenance_section.as_ref().map(|section| {
        let origins = &section.origins;
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
            premises: section.premises,
            fused_module_sha256: section.fused_module_sha256,
            origins: origins
                .iter()
                .map(|o| ComponentOrigin {
                    fused_func_index: o.fused_func_index,
                    component_id: o.component_id.clone(),
                    orig_func_index: o.orig_func_index,
                    code_range: o.code_range,
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

    // FEAT-021 slice-1: worst-case shadow-stack bound, reusing the FEAT-006/007
    // call graph + Tarjan SCCs computed above for the summary pass.
    // FEAT-043: weight the stack longest-path by the resolved call_indirect
    // targets (not the whole table) for functions interpreted without a gap;
    // recursion + topo stay on the conservative `static_callees`.
    let stack_callees = resolved_stack_callees(
        defined_funcs.len(),
        &static_callees,
        &call_graph,
        &gaps,
        import_func_count,
    );
    let stack_usage = compute_stack_usage(
        &defined_funcs,
        &stack_callees,
        &sccs_reverse_topo_order(&sccs),
        &recursive_flags,
        resolve_sp_global(&mutable_i32_globals),
        func_table.contents_known,
    );
    if config.emit_diagnostics {
        let msg = match stack_usage.max_stack_bytes {
            StackBound::Bytes(n) => {
                alloc::format!("FEAT-021: worst-case shadow-stack bound = {n} bytes (sound)")
            }
            StackBound::Unbounded => {
                "FEAT-021: shadow-stack usage UNBOUNDED (recursion — no finite bound \
                 without a ranking function)"
                    .to_string()
            }
            StackBound::Unknown => {
                "FEAT-021: shadow-stack usage UNKNOWN (unrecognised frame / dynamic alloca / \
                 unresolved call or ambiguous stack-pointer global)"
                    .to_string()
            }
        };
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Info,
            func_index: 0,
            pc: 0,
            message: msg,
        });
    }

    // FEAT-039: complete the address-taken set with `ref.func` operands in
    // function BODIES (the const-position ones were collected during parsing).
    for f in &defined_funcs {
        for op in &f.ops {
            if let Operator::RefFunc { function_index } = op {
                address_taken_funcs.push(*function_index);
            }
        }
    }

    // FEAT-022 slice-1 + FEAT-039: reachability from the module's entry points
    // over the over-approximated static call graph. SOUNDNESS (FEAT-039): when
    // funcrefs can escape to a caller scry cannot see (open world — NOT
    // `callers_fully_known`, the FEAT-036 escape predicate), the host or an
    // import may dispatch ANY address-taken function, so those are added as
    // reachability roots to keep the result a sound SUPERSET (SCRY-001). When
    // the module is provably closed-and-escape-free, the tight exports+start
    // seed is correct — the precision the premise licenses.
    let reachable_from_exports = compute_reachable_from_exports(
        &static_callees,
        import_func_count,
        &exported_funcs,
        start_func,
        callers_fully_known,
        &address_taken_funcs,
    );

    let function_meta = build_function_meta(
        import_func_count,
        function_type_indices.len() as u32,
        &import_func_meta,
        &export_names,
        &name_section,
    );

    // FEAT-034: scry's OWN fusion premises (verify-not-trust). A syntactic
    // scan — `memory.grow` anywhere ⇒ memory is not provably fixed; any
    // functional import ⇒ scry cannot prove a closed world at the core level.
    // These are sound because scry derived them, independent of meld's claim.
    // `bounded_memory` (= `!saw_memory_grow`) is computed once before the
    // fixpoint (FEAT-038, so `memory.size` can use it) and reused here.
    let saw_memory_grow = !bounded_memory;
    let verified_premises = FusionPremises {
        bounded_memory,
        closed_world: import_func_count == 0,
    };
    // Cross-check meld's asserted premise against scry's observation: a v3
    // section claiming `bounded_memory` on a module that contains `memory.grow`
    // is a producer↔consumer disagreement — flag it; scry keeps its own
    // conservative determination (meld stays out of scry's TCB).
    if config.emit_diagnostics
        && let Some(section) = &provenance_section
        && section.premises.bounded_memory
        && saw_memory_grow
    {
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::UnsoundnessFallback,
            func_index: 0,
            pc: 0,
            message: "FEAT-034: meld component-provenance asserts bounded_memory but the fused \
                 module contains memory.grow — premise rejected; scry uses its own \
                 (unbounded) determination"
                .to_string(),
        });
    }

    // FEAT-037 (DD-017): additive known-bits × congruence pass over each
    // function body. Does not touch the interval/region/octagon/taint state
    // computed above — it is a separate straight-line-sound walk (the FEAT-021
    // "additive pass" precedent).
    let bit_facts = compute_bit_facts(&defined_funcs);
    let pentagon_facts = compute_pentagon_facts(&defined_funcs);
    let float_facts = compute_float_facts(&defined_funcs);
    let handle_findings =
        compute_handle_findings(&defined_funcs, &import_func_meta, import_func_count);
    // FEAT-059: synthesise the sound findings into ranked remediation guidance
    // (pure synthesis over the results above; borrows before they are moved).
    let (mut advisories, advisory_id_codes) = compute_advisories(
        &gaps,
        &trap_checks,
        &handle_findings,
        &stack_usage,
        memory_min_bytes,
    );
    // FEAT-064: give every advisory an identity that survives the next edit, so
    // a consumer comparing two runs can tell DISCHARGED from MOVED.
    let func_identities = stamp_obligation_ids(
        &mut advisories,
        &advisory_id_codes,
        &defined_funcs,
        &function_meta,
    );

    Ok(AnalysisResult {
        invariants,
        diagnostics,
        call_graph,
        function_summaries,
        provenance,
        taint_findings,
        stack_usage,
        reachable_from_exports,
        function_meta,
        verified_premises,
        bit_facts,
        gaps,
        pentagon_facts,
        trap_checks,
        float_facts,
        handle_findings,
        advisories,
        func_identities,
    })
}

// ───────────────────────── FEAT-037 (DD-017) ─────────────────────────

/// FEAT-038: the page ceiling for memory index 0 — the declared maximum if any,
/// else the architectural cap (2^48 for memory64, 65536 for memory32).
#[inline]
fn mem_page_ceiling(m: &ModuleCtx<'_>) -> i64 {
    let arch_cap: u64 = if m.memory_is_64 { 1u64 << 48 } else { 65536 };
    m.memory_max_pages.unwrap_or(arch_cap) as i64
}

/// FEAT-038: the abstract `memory.size` result for `memidx`. Precise only for
/// memory index 0 of a single-memory module (the only memory scry captures);
/// any other memidx or a multi-memory module is ⊤ (sound). The exact constant
/// `initial` applies only to a provably-fixed module-private memory; otherwise
/// the sound interval `[initial, ceiling]`. 64-bit memory returns an i64.
#[inline]
fn mem_size_value(m: &ModuleCtx<'_>, memidx: u32) -> AbstractValue {
    if memidx != 0 || m.memory_count != 1 {
        return AbstractValue::Unknown;
    }
    let lo = m.memory_initial_pages as i64;
    let hi = if m.memory_size_constant {
        lo
    } else {
        mem_page_ceiling(m)
    };
    let iv = Interval { lo, hi };
    if m.memory_is_64 {
        AbstractValue::I64Interval(iv)
    } else {
        AbstractValue::I32Interval(iv)
    }
}

/// Integer bit width of a Wasm value type, or `None` for types the bits domain
/// does not model (floats, v128, references).
#[inline]
fn bits_width_of(ty: wasmparser::ValType) -> Option<u32> {
    match ty {
        wasmparser::ValType::I32 => Some(32),
        wasmparser::ValType::I64 => Some(64),
        _ => None,
    }
}

/// If a companion value is an exact constant (a congruence singleton), return
/// it — used to read a constant shift amount.
#[inline]
fn bits_as_const(slot: &Option<(BitsCong, u32)>) -> Option<u64> {
    match slot {
        Some((bc, _)) => match bc.cong {
            Cong::Mod { m: 0, r } => Some(r),
            _ => None,
        },
        None => None,
    }
}

/// True when a companion value carries no information (both components ⊤).
#[inline]
fn bits_is_top(bc: &BitsCong) -> bool {
    matches!(bc.kb, scry_bits::KnownBits::Bits { zeros: 0, ones: 0 })
        && matches!(bc.cong, Cong::Mod { m: 1, r: 0 })
}

/// FEAT-037 (DD-017): the additive known-bits × congruence pass. For each
/// defined function it runs a STRAIGHT-LINE-sound abstract interpretation over
/// the body using [`scry_bits`], emitting a [`BitFact`] at each
/// `local.set`/`local.tee` whose written value carries a non-⊤ fact.
///
/// Soundness discipline (this pass never perturbs the interval/region/octagon/
/// taint analysis — it is a separate walk):
///   * Declared (non-parameter) locals are Wasm-zero-initialized, so they start
///     as the exact constant 0; parameters start as ⊤ (unknown caller args).
///   * Only a curated all-list of integer ops is modelled; on the FIRST
///     control-flow op (`block`/`loop`/`if`/`br*`/`call*`/`return`/`end`/…) or
///     any unmodelled op the walk STOPS for that function — every fact emitted
///     was therefore established on the straight-line prefix before any merge,
///     which is sound. (A future slice can add a join-at-merge fixpoint.)
///   * The no-wrap guard for add/sub/mul is derived from the operands' known
///     value range (`umax`/`umin`), a sound source: full modulus retained only
///     when no wrap is provable, else weakened to `gcd(m, 2^w)` per DD-017.
fn compute_bit_facts(defined_funcs: &[DefinedFunc<'_>]) -> Vec<BitFact> {
    let mut facts: Vec<BitFact> = Vec::new();

    for func in defined_funcs {
        // Local slots: params (⊤) then declared locals (zero-initialized).
        // `None` = a local the bits domain does not model (non-integer).
        let mut locals: Vec<Option<(BitsCong, u32)>> = Vec::new();
        for &ty in &func.params {
            locals.push(bits_width_of(ty).map(|w| (BitsCong::top(), w)));
        }
        for &ty in &func.declared_locals {
            locals.push(bits_width_of(ty).map(|w| (BitsCong::constant(0, w), w)));
        }

        let mut stack: Vec<Option<(BitsCong, u32)>> = Vec::new();

        'body: for (pc, op) in func.ops.iter().enumerate() {
            let pc = pc as u32;
            match op {
                Operator::I32Const { value } => {
                    stack.push(Some((BitsCong::constant(*value as u32 as u64, 32), 32)));
                }
                Operator::I64Const { value } => {
                    stack.push(Some((BitsCong::constant(*value as u64, 64), 64)));
                }
                Operator::LocalGet { local_index } => {
                    let Some(slot) = locals.get(*local_index as usize) else {
                        break 'body;
                    };
                    stack.push(*slot);
                }
                Operator::LocalSet { local_index } | Operator::LocalTee { local_index } => {
                    let is_tee = matches!(op, Operator::LocalTee { .. });
                    let Some(top) = stack.pop() else { break 'body };
                    let idx = *local_index as usize;
                    if idx >= locals.len() {
                        break 'body;
                    }
                    // The written value must match the local's modelled width.
                    let written = match (top, locals[idx]) {
                        (Some((bc, wv)), Some((_, wl))) if wv == wl => Some((bc, wl)),
                        // type/width mismatch or opaque source: local becomes ⊤
                        // if it is an integer local, else stays unmodelled.
                        (_, Some((_, wl))) => Some((BitsCong::top(), wl)),
                        (_, None) => None,
                    };
                    locals[idx] = written;
                    if let Some((bc, w)) = written
                        && !bits_is_top(&bc)
                    {
                        facts.push(make_bit_fact(func.abs_index, pc, *local_index, w, &bc));
                    }
                    if is_tee {
                        stack.push(written);
                    }
                }
                Operator::Drop => {
                    if stack.pop().is_none() {
                        break 'body;
                    }
                }
                // ── binary integer transfers ──
                Operator::I32And | Operator::I64And => {
                    bits_binop(&mut stack, |a, b, w| a.and(b, w))
                }
                Operator::I32Or | Operator::I64Or => bits_binop(&mut stack, |a, b, w| a.or(b, w)),
                Operator::I32Xor | Operator::I64Xor => {
                    bits_binop(&mut stack, |a, b, w| a.xor(b, w))
                }
                Operator::I32Add | Operator::I64Add => {
                    bits_binop(&mut stack, |a, b, w| a.add(b, w, a.add_wrap_free(b, w)))
                }
                Operator::I32Sub | Operator::I64Sub => {
                    bits_binop(&mut stack, |a, b, w| a.sub(b, w, a.sub_wrap_free(b, w)))
                }
                Operator::I32Mul | Operator::I64Mul => {
                    bits_binop(&mut stack, |a, b, w| a.mul(b, w, a.mul_wrap_free(b, w)))
                }
                // ── shifts: the count is a runtime operand; model it only when
                // it is a known constant (taken mod width, per Wasm). ──
                Operator::I32Shl | Operator::I64Shl => {
                    bits_shift(&mut stack, |a, s, w| a.shl(s, w))
                }
                Operator::I32ShrU | Operator::I64ShrU => {
                    bits_shift(&mut stack, |a, s, w| a.shr_u(s, w))
                }
                Operator::I32ShrS | Operator::I64ShrS => {
                    bits_shift(&mut stack, |a, s, w| a.shr_s(s, w))
                }
                // First control-flow / unmodelled op: stop — the straight-line
                // prefix's facts are sound; beyond a merge we make no claim.
                _ => break 'body,
            }
        }
    }

    facts.sort_by_key(|f| (f.func_index, f.pc, f.local_index));
    facts
}

/// FEAT-044 (AC-014): an additive guard-detection pass that records the strict
/// `x < bound` relations the Pentagons domain ([`scry_pentagon`]) can prove from
/// a comparison that guards an `if`. It scans each body for the shape
///
/// ```text
///   local.get i ;  (local.get j | i32.const c | i64.const c) ;  <lt> ;  if
/// ```
///
/// where `<lt>` is `i32/i64.lt_u` or `i32/i64.lt_s`. The then-branch is taken
/// only when the comparison was true, so `x_i < bound` holds on ENTRY to the
/// then-region — exactly the `index < length` fact FEAT-046 consumes. The
/// fact is emitted only when a freshly-built Pentagon, told `assume_lt`,
/// actually *proves* it via [`Pentagon::implies_lt`] — so the domain is
/// load-bearing, not decorative. Straight-line, no fixpoint, library-only.
fn compute_pentagon_facts(defined_funcs: &[DefinedFunc<'_>]) -> Vec<PentagonFact> {
    use scry_pentagon::Pentagon;
    let mut facts: Vec<PentagonFact> = Vec::new();

    for func in defined_funcs {
        let ops = &func.ops;
        for pc in 0..ops.len() {
            // Window: cmp-lhs, cmp-rhs, lt-op, if.
            if pc + 3 >= ops.len() {
                break;
            }
            let Operator::LocalGet { local_index: i } = ops[pc] else {
                continue;
            };
            let bound = match ops[pc + 1] {
                Operator::LocalGet { local_index: j } => PentagonBound::Local(j),
                Operator::I32Const { value } => PentagonBound::Const(value as i64),
                Operator::I64Const { value } => PentagonBound::Const(value),
                _ => continue,
            };
            let unsigned = match ops[pc + 2] {
                Operator::I32LtU | Operator::I64LtU => true,
                Operator::I32LtS | Operator::I64LtS => false,
                _ => continue,
            };
            if !matches!(ops[pc + 3], Operator::If { .. }) {
                continue;
            }
            // Validate the relation through the domain: x_0 = lhs, x_1 = rhs.
            let mut p = Pentagon::top(2);
            match bound {
                PentagonBound::Local(_) => p.assume_lt(0, 1),
                PentagonBound::Const(c) => {
                    // model the constant rhs as a singleton interval on x_1
                    p.set_interval(1, c, c);
                    p.assume_lt(0, 1);
                }
            }
            if !p.implies_lt(0, 1) {
                continue;
            }
            facts.push(PentagonFact {
                func_index: func.abs_index,
                pc: (pc + 3) as u32,
                lhs_local: i,
                bound,
                unsigned,
            });
        }
    }

    facts.sort_by_key(|f| (f.func_index, f.pc));
    facts
}

/// The float width a value type carries, or `None` if not a float.
fn float_width_of(ty: wasmparser::ValType) -> Option<u32> {
    match ty {
        wasmparser::ValType::F32 => Some(32),
        wasmparser::ValType::F64 => Some(64),
        _ => None,
    }
}

fn float_is_top(fa: &scry_float::FloatAbstract) -> bool {
    *fa == scry_float::FloatAbstract::top()
}

fn make_float_fact(
    func_index: u32,
    pc: u32,
    local_index: u32,
    width: u32,
    fa: &scry_float::FloatAbstract,
) -> FloatFact {
    FloatFact {
        func_index,
        pc,
        local_index,
        width,
        lo_bits: fa.lo.to_bits(),
        hi_bits: fa.hi.to_bits(),
        nan: fa.nan,
    }
}

/// FEAT-047 (AC-022): an additive straight-line-sound pass over each function
/// body that tracks f32/f64 locals + operand stack through the IEEE-754
/// float-interval domain ([`scry_float`]), recording a sound [`FloatFact`] at
/// each float `local.set`/`local.tee`. Removes the scope hole where any float
/// arithmetic left the value un-analyzed. Mirrors [`compute_bit_facts`]:
/// straight-line (stops at the first control-flow / unmodelled op), library-only,
/// only non-⊤ facts emitted.
fn compute_float_facts(defined_funcs: &[DefinedFunc<'_>]) -> Vec<FloatFact> {
    use scry_float::{FWidth, FloatAbstract};
    let mut facts: Vec<FloatFact> = Vec::new();

    let fw = |w: u32| if w == 32 { FWidth::W32 } else { FWidth::W64 };

    for func in defined_funcs {
        let mut locals: Vec<Option<(FloatAbstract, u32)>> = Vec::new();
        for &ty in &func.params {
            locals.push(float_width_of(ty).map(|w| (FloatAbstract::top(), w)));
        }
        for &ty in &func.declared_locals {
            locals.push(float_width_of(ty).map(|w| (FloatAbstract::constant(0.0), w)));
        }
        let mut stack: Vec<Option<(FloatAbstract, u32)>> = Vec::new();

        'body: for (pc, op) in func.ops.iter().enumerate() {
            let pc = pc as u32;
            match op {
                Operator::F32Const { value } => {
                    let f = f32::from_bits(value.bits()) as f64;
                    stack.push(Some((FloatAbstract::constant(f), 32)));
                }
                Operator::F64Const { value } => {
                    let f = f64::from_bits(value.bits());
                    stack.push(Some((FloatAbstract::constant(f), 64)));
                }
                Operator::LocalGet { local_index } => match locals.get(*local_index as usize) {
                    Some(slot) => stack.push(*slot),
                    None => break 'body,
                },
                Operator::LocalSet { local_index } | Operator::LocalTee { local_index } => {
                    let is_tee = matches!(op, Operator::LocalTee { .. });
                    let Some(top) = stack.pop() else { break 'body };
                    let idx = *local_index as usize;
                    if idx >= locals.len() {
                        break 'body;
                    }
                    let written = match (top, locals[idx]) {
                        (Some((fa, wv)), Some((_, wl))) if wv == wl => Some((fa, wl)),
                        (_, Some((_, wl))) => Some((FloatAbstract::top(), wl)),
                        (_, None) => None,
                    };
                    locals[idx] = written;
                    if let Some((fa, w)) = written
                        && !float_is_top(&fa)
                    {
                        facts.push(make_float_fact(func.abs_index, pc, *local_index, w, &fa));
                    }
                    if is_tee {
                        stack.push(written);
                    }
                }
                Operator::Drop => {
                    if stack.pop().is_none() {
                        break 'body;
                    }
                }
                Operator::F32Add | Operator::F64Add => {
                    float_binop(&mut stack, &fw, |a, b, w| a.add(&b, w))
                }
                Operator::F32Sub | Operator::F64Sub => {
                    float_binop(&mut stack, &fw, |a, b, w| a.sub(&b, w))
                }
                Operator::F32Mul | Operator::F64Mul => {
                    float_binop(&mut stack, &fw, |a, b, w| a.mul(&b, w))
                }
                Operator::F32Neg | Operator::F64Neg => float_unop(&mut stack, |a| a.neg()),
                Operator::F32Abs | Operator::F64Abs => float_unop(&mut stack, |a| a.abs()),
                // First control-flow / unmodelled op: the straight-line prefix's
                // facts are sound; beyond a merge we make no claim.
                _ => break 'body,
            }
        }
    }

    facts.sort_by_key(|f| (f.func_index, f.pc, f.local_index));
    facts
}

/// Pop two float companions, apply a binary transfer when both are modelled and
/// same-width, push the result (opaque otherwise).
#[inline]
fn float_binop(
    stack: &mut Vec<Option<(scry_float::FloatAbstract, u32)>>,
    fw: &dyn Fn(u32) -> scry_float::FWidth,
    f: impl Fn(
        scry_float::FloatAbstract,
        scry_float::FloatAbstract,
        scry_float::FWidth,
    ) -> scry_float::FloatAbstract,
) {
    let b = stack.pop().flatten();
    let a = stack.pop().flatten();
    let out = match (a, b) {
        (Some((fa, wa)), Some((fb, wb))) if wa == wb => Some((f(fa, fb, fw(wa)), wa)),
        _ => None,
    };
    stack.push(out);
}

/// Pop one float companion, apply a unary transfer, push the result.
#[inline]
fn float_unop(
    stack: &mut Vec<Option<(scry_float::FloatAbstract, u32)>>,
    f: impl Fn(scry_float::FloatAbstract) -> scry_float::FloatAbstract,
) {
    let a = stack.pop().flatten();
    stack.push(a.map(|(fa, w)| (f(fa), w)));
}

/// FEAT-049: how a canonical-ABI import touches a resource handle passed to it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum HandleOp {
    /// `[resource-drop]T` — drops the handle.
    Drop,
    /// `[method]T.m` / `[resource-rep]T` — uses (reads) the handle.
    Use,
}

/// FEAT-049: classify an import by its Component-Model canonical-ABI name.
/// The bracketed tags are the ABI's own convention; a value passed to such an
/// import is a resource handle being dropped or used.
fn classify_handle_import(name: &str) -> Option<HandleOp> {
    if name.contains("[resource-drop]") {
        Some(HandleOp::Drop)
    } else if name.contains("[method]") || name.contains("[resource-rep]") {
        Some(HandleOp::Use)
    } else {
        None
    }
}

/// FEAT-049 (MF-007): the affine handle-state pass. Tracks each local's handle
/// state ([`scry_handle::HandleState`]) across the canonical-ABI
/// `local.get L; call [resource-drop|method|resource-rep] …` sites and reports
/// DEFINITE use-after-drop / double-drop faults. Straight-line and conservative
/// at control flow (all locals widen to `Top` — "maybe dropped" — at any
/// branch/merge, so a definite fault is never reported across paths): sound in
/// the "no false report" direction the AC requires. `import_func_meta[i]` is the
/// `module.field` of imported function `i` (`i < import_func_count`).
fn compute_handle_findings(
    defined_funcs: &[DefinedFunc<'_>],
    import_func_meta: &[String],
    import_func_count: u32,
) -> Vec<HandleFinding> {
    use scry_handle::HandleState;
    let mut findings: Vec<HandleFinding> = Vec::new();

    for func in defined_funcs {
        let nlocals = func.params.len() + func.declared_locals.len();
        let mut states: Vec<HandleState> = alloc::vec![HandleState::Alive; nlocals];
        let ops = &func.ops;

        for i in 0..ops.len() {
            match &ops[i] {
                Operator::LocalSet { local_index } | Operator::LocalTee { local_index } => {
                    // A fresh value is written — reset to Alive (a newly-bound
                    // handle is live; conservative for no-false-report).
                    if let Some(s) = states.get_mut(*local_index as usize) {
                        *s = HandleState::Alive;
                    }
                }
                Operator::LocalGet { local_index } => {
                    // Canonical shape: `local.get L` immediately consumed by a
                    // resource `call`.
                    let Some(Operator::Call { function_index }) = ops.get(i + 1) else {
                        continue;
                    };
                    if *function_index >= import_func_count {
                        continue;
                    }
                    let Some(name) = import_func_meta.get(*function_index as usize) else {
                        continue;
                    };
                    let Some(op) = classify_handle_import(name) else {
                        continue;
                    };
                    let l = *local_index as usize;
                    let Some(&st) = states.get(l) else { continue };
                    match op {
                        HandleOp::Drop => {
                            // DEFINITE double-drop only when provably Dropped.
                            if st == HandleState::Dropped {
                                findings.push(HandleFinding {
                                    func_index: func.abs_index,
                                    pc: (i + 1) as u32,
                                    local_index: *local_index,
                                    via: name.clone(),
                                    kind: HandleFindingKind::DoubleDrop,
                                });
                            }
                            states[l] = st.after_drop().0; // → Dropped
                        }
                        HandleOp::Use => {
                            if st.use_is_after_drop() {
                                findings.push(HandleFinding {
                                    func_index: func.abs_index,
                                    pc: (i + 1) as u32,
                                    local_index: *local_index,
                                    via: name.clone(),
                                    kind: HandleFindingKind::UseAfterDrop,
                                });
                            }
                        }
                    }
                }
                // Control flow: widen every local to Top (maybe-dropped) so no
                // DEFINITE fault is reported across a branch/merge — the sound
                // "no false report" treatment.
                Operator::Block { .. }
                | Operator::Loop { .. }
                | Operator::If { .. }
                | Operator::Else
                | Operator::End
                | Operator::Br { .. }
                | Operator::BrIf { .. }
                | Operator::BrTable { .. }
                | Operator::Return => {
                    for s in states.iter_mut() {
                        *s = HandleState::Top;
                    }
                }
                _ => {}
            }
        }
    }

    findings.sort_by_key(|f| (f.func_index, f.pc));
    findings
}

/// FEAT-055 (REQ-018): a candidate counterexample for a POTENTIAL-TRAP, derived
/// from the trap kind (and, for OOB, the memory size). CANDIDATE, not proven
/// reachable — the abstract state over-approximates (see [`Counterexample`]).
fn trap_counterexample(kind: TrapKind, op: &str, memory_size_bytes: u64) -> Counterexample {
    match kind {
        TrapKind::DivByZero => Counterexample {
            trigger: "the divisor is 0".into(),
            witness: alloc::vec![CxAssign {
                operand: "divisor".into(),
                value: 0
            }],
        },
        TrapKind::SignedOverflow => {
            let int_min = if op.starts_with("i64") {
                i64::MIN
            } else {
                i32::MIN as i64
            };
            Counterexample {
                trigger: "the dividend is INT_MIN and the divisor is -1".into(),
                witness: alloc::vec![
                    CxAssign {
                        operand: "dividend".into(),
                        value: int_min,
                    },
                    CxAssign {
                        operand: "divisor".into(),
                        value: -1,
                    },
                ],
            }
        }
        TrapKind::OutOfBounds => {
            let addr = memory_size_bytes.min(i64::MAX as u64) as i64;
            Counterexample {
                trigger: alloc::format!(
                    "an effective address at or beyond the memory's current size ({memory_size_bytes} bytes)"
                ),
                witness: alloc::vec![CxAssign {
                    operand: "address".into(),
                    value: addr,
                }],
            }
        }
    }
}

/// FEAT-059 (REQ-018): synthesise the sound findings into ranked, actionable
/// remediation advisories. Pure synthesis over already-computed results — it
/// introduces NO new unsoundness, and each advisory is only as strong as the
/// finding it derives from (a POTENTIAL-TRAP becomes an `UnprovenObligation`,
/// never a `DefiniteFault`). Ranked DefiniteFault > UnprovenObligation >
/// PrecisionGap > LeverageableFact.
/// FEAT-064 (REQ-020, DD-020): the STRUCTURAL KEY of every operator in a body —
/// the part of an obligation identity that survives an edit.
///
/// For each pc returns `(path, ordinal)`:
///   * `path` — the chain of enclosing `block`/`loop`/`if` SIBLING ordinals from
///     the function root, e.g. `"b0.l1"` = the 2nd region (a loop) inside the
///     1st region (a block). Raw pcs never appear, which is exactly why
///     inserting instructions earlier in the function does not disturb it.
///   * `ordinal` — the operator's index among SAME-KIND operators within its own
///     enclosing region, so two `i32.load`s in one block stay distinguishable
///     without reintroducing a global counter.
///
/// Pure function of the operator list: it perturbs no analysis state and is
/// independently testable.
fn structural_keys(ops: &[Operator<'_>]) -> Vec<(String, u32)> {
    let mut out: Vec<(String, u32)> = Vec::with_capacity(ops.len());
    // Enclosing regions as (kind marker, sibling ordinal at that depth).
    let mut path: Vec<(char, u32)> = Vec::new();
    // How many regions have been opened so far at each depth.
    let mut opened: Vec<u32> = alloc::vec![0];
    // Per-region same-kind operator counters.
    let mut kinds: Vec<alloc::collections::BTreeMap<String, u32>> =
        alloc::vec![alloc::collections::BTreeMap::new()];

    for op in ops {
        let path_str = path
            .iter()
            .map(|(c, n)| format!("{c}{n}"))
            .collect::<Vec<_>>()
            .join(".");
        let kind = op_report_name(op);
        let slot = kinds
            .last_mut()
            .expect("kind stack non-empty")
            .entry(kind)
            .or_insert(0);
        let ordinal = *slot;
        *slot += 1;
        out.push((path_str, ordinal));

        let marker = match op {
            Operator::Block { .. } => Some('b'),
            Operator::Loop { .. } => Some('l'),
            Operator::If { .. } => Some('i'),
            _ => None,
        };
        if let Some(m) = marker {
            let depth = path.len();
            let n = opened[depth];
            opened[depth] += 1;
            path.push((m, n));
            opened.push(0);
            kinds.push(alloc::collections::BTreeMap::new());
        } else if matches!(op, Operator::End) {
            // The body's final `End` closes no region — guard the pops.
            if !path.is_empty() {
                path.pop();
                opened.pop();
                kinds.pop();
            }
        }
    }
    out
}

/// FEAT-064: hash of a body's structural SHAPE (opcode sequence, immediates
/// elided). The last-resort function identity, used only when a module carries
/// neither a name section nor an export for the function — see DD-020 for why
/// it is deliberately the weakest of the three.
fn body_shape_hash(ops: &[Operator<'_>]) -> String {
    let mut h = Sha256::new();
    for op in ops {
        h.update(op_report_name(op).as_bytes());
        h.update(b";");
    }
    let d = h.finalize();
    let mut out = String::with_capacity(16);
    for b in d.iter().take(8) {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// FEAT-077 (scry#123): strip Rust's LEGACY-mangling symbol disambiguator — a
/// trailing `17h` + exactly 16 LOWERCASE hex digits + `E` — from a
/// name-section name. Returns `None` for any other shape; nothing broader is
/// attempted (an over-matching heuristic would rename functions that were
/// never Rust symbols). The disambiguator is derived from crate metadata and
/// the instantiation, NOT the function body — measured on real builds
/// (scry#123) it re-rolls on ANY upstream edit, destroying every obligation
/// identity in 45% of identified functions per commit, while the stripped
/// prefix was 100% stable across both an unrelated edit and an edit to the
/// function's own body.
fn strip_rust_disambiguator(name: &str) -> Option<alloc::string::String> {
    // ── LEGACY mangling: a trailing `17h<16 lowercase hex>E`. ──────────────
    if let Some(no_e) = name.strip_suffix('E')
        && no_e.len() >= 16
    {
        let (head, hex) = no_e.split_at(no_e.len() - 16);
        if hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
            && let Some(base) = head.strip_suffix("17h")
            && !base.is_empty()
        {
            return Some(base.into());
        }
    }
    // ── v0 mangling (scry#144): the disambiguator is a CRATE-level ─────────
    // `Cs<base62>_` near the FRONT, not a trailing hash. gale's dissolved OS
    // object is mangled this way, so the legacy path above gave it no
    // stability at all — every function fell back to the raw name and was
    // marked build-local. Measured: identity churned across a crate-
    // disambiguator change (`217a5de8…` vs `d32b8646…`).
    //
    // `_RNvCs942N1ctoMYm_18gust_exec_provider5admit`
    //      ^^ ^----------^ the segment removed
    //
    // Conservative by construction, matching the house posture: this strips
    // ONLY the exact shape `C` `s` <base62+> `_`, and only on a `_R` name.
    // Anything else returns None and falls back to the raw name plus the
    // build-local marker, which is honest rather than clever.
    let rest = name.strip_prefix("_R")?;
    let at = rest.find("Cs")?;
    let after = &rest[at + 2..];
    let run: &str = after.split('_').next()?;
    if run.is_empty() || !run.bytes().all(|b| b.is_ascii_alphanumeric()) {
        return None;
    }
    // The `_` terminator must actually be present, not merely implied by the
    // end of the string.
    if after.len() <= run.len() {
        return None;
    }
    let mut out = alloc::string::String::with_capacity(name.len());
    out.push_str("_R");
    out.push_str(&rest[..at + 1]); // through the `C`
    out.push_str(&after[run.len() + 1..]); // past the `_`
    if out == "_RC" { None } else { Some(out) }
}

/// FEAT-064: the content address itself. Opaque, fixed-width; consumers must not
/// parse it (DD-020).
fn obligation_id_of(func_ident: &str, path: &str, kind: &str, ordinal: u32, code: &str) -> String {
    let mut h = Sha256::new();
    h.update(func_ident.as_bytes());
    h.update(b"|");
    h.update(path.as_bytes());
    h.update(b"|");
    h.update(kind.as_bytes());
    h.update(b"|");
    h.update(ordinal.to_le_bytes());
    // Clean-room: one operator can raise SEVERAL obligations (an `i32.div_s`
    // raises both div-by-zero and signed-overflow), so the site alone does not
    // discriminate. The advisory's code is the fifth component.
    h.update(b"|");
    h.update(code.as_bytes());
    let d = h.finalize();
    let mut out = String::with_capacity(16);
    for b in d.iter().take(8) {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// FEAT-072 (DD-021): the SITE key — everything the obligation id has EXCEPT
/// the advisory code, so it survives an obligation changing state.
fn site_key_of(func_ident: &str, path: &str, kind: &str, ordinal: u32) -> String {
    let mut h = Sha256::new();
    h.update(b"site|");
    h.update(func_ident.as_bytes());
    h.update(b"|");
    h.update(path.as_bytes());
    h.update(b"|");
    h.update(kind.as_bytes());
    h.update(b"|");
    h.update(ordinal.to_le_bytes());
    let d = h.finalize();
    let mut out = String::with_capacity(16);
    for b in d.iter().take(8) {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// FEAT-072 (DD-021): the ORDINAL DOMAIN key — function + region path + kind,
/// WITHOUT the ordinal. Aliasing can only occur WITHIN one such domain, so a
/// change in a group's membership bounds where identity may have shifted.
fn group_key_of(func_ident: &str, path: &str, kind: &str) -> String {
    let mut h = Sha256::new();
    h.update(b"group|");
    h.update(func_ident.as_bytes());
    h.update(b"|");
    h.update(path.as_bytes());
    h.update(b"|");
    h.update(kind.as_bytes());
    let d = h.finalize();
    let mut out = String::with_capacity(16);
    for b in d.iter().take(8) {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

/// FEAT-064: does this advisory describe the MODULE rather than a code site?
/// Such advisories carry `(func 0, pc 0)` as a SENTINEL, so giving them a site
/// identity would collide with a genuine advisory there, drift whenever func 0's
/// first instruction changes, and yield nothing when index 0 is an import
/// (clean-room finding).
fn is_module_scoped(code: &str) -> bool {
    code == "unbounded-stack"
}

/// FEAT-064 + FEAT-077: stamp every advisory with its obligation identity.
///
/// Function identity is TWO-TIER (scry#123, DD-020). The raw name-section name
/// inherits Rust's legacy symbol disambiguator (`17h<16 hex>E`), which is
/// derived from crate metadata rather than the body — measured, it re-rolls on
/// any upstream edit and destroyed every obligation identity in 45% of
/// identified functions per commit, including the very function a fix edits.
/// So:
///   1. named, disambiguated, and the STRIPPED name is unique in the module →
///      the stripped name (stable: measured 100% survival across both an
///      unrelated edit and an own-body edit);
///   2. named, disambiguated, stripped name SHARED (dependency generics —
///      measured 37.8% of functions, all of them dependencies, none scry's
///      own) → the raw name, and the advisory is MARKED
///      [`Advisory::id_build_local`]: unique within this build, not comparable
///      across builds;
///   3. named, no disambiguator → the raw name (unchanged from v3.2.5);
///   4. unnamed → the body-shape hash (unchanged from v3.2.5).
///
/// FEAT-087 (scry#122 item 2) adds a SECOND, INDEPENDENT bit,
/// [`Advisory::ident_survives_own_edit`]. Tier 4 is the only one that answers
/// NO: its ident is a hash of the very bytes an edit changes. It is emphatically
/// NOT build-local — the hash is deterministic across builds — which is why one
/// bit could not carry both facts, and why tier 4 must NOT simply be marked
/// build-local (that would suppress cross-build citation for 100% of every
/// stripped module to fix a different property). Tier 2 is the mirror case:
/// build-local, yet body-independent, so it DOES survive its own edit.
fn stamp_obligation_ids(
    advisories: &mut [Advisory],
    id_codes: &[Option<&'static str>],
    defined_funcs: &[DefinedFunc<'_>],
    function_meta: &[FunctionMeta],
) -> Vec<FuncIdentity> {
    // FEAT-089: `id_codes` is index-parallel to `advisories` (built together
    // in `compute_advisories`); `Some(code)` overrides `Advisory::code` as the
    // obligation-identity input, so a `proven-safe` advisory keeps the id of
    // the obligation it discharges. A `None`/missing entry falls back to the
    // advisory's own code — the pre-FEAT-089 behaviour.
    debug_assert_eq!(advisories.len(), id_codes.len());
    for a in advisories.iter_mut().filter(|a| is_module_scoped(&a.code)) {
        a.obligation_id = obligation_id_of("<module>", "", "<module>", 0, &a.code);
        a.site_key = site_key_of("<module>", "", "<module>", 0);
        a.group_key = group_key_of("<module>", "", "<module>");
        // FEAT-087: set DELIBERATELY, not left to the construction-site
        // default. A module-scoped advisory's ident is the literal `<module>`,
        // which is body-independent, so it survives an edit to any function.
        a.ident_survives_own_edit = true;
    }
    // FEAT-077: a stripped name may serve as the identity ONLY when unique in
    // the module. Count every named function's CANDIDATE — stripped when the
    // exact disambiguator shape is present, else the raw name — so a stripped
    // name that lands on another function's candidate (a sibling
    // monomorphization OR a plain name that never had a disambiguator) is
    // rejected. Known residual (clean-room, accepted): the count does NOT
    // cover UNNAMED functions' body-shape hashes, so a stripped name that is
    // itself exactly 16 lowercase hex characters could in principle collide
    // with a shape hash. A real Rust legacy symbol starts `_ZN…`, so its
    // stripped form is never pure hex; reaching this needs a hand-crafted
    // name plus a SHA-256-prefix coincidence.
    let mut candidates: alloc::collections::BTreeMap<alloc::string::String, u32> =
        alloc::collections::BTreeMap::new();
    for m in function_meta {
        if let Some(n) = m.name.as_deref() {
            let key = strip_rust_disambiguator(n).unwrap_or_else(|| n.into());
            *candidates.entry(key).or_insert(0) += 1;
        }
    }
    let mut func_identities: Vec<FuncIdentity> = Vec::with_capacity(defined_funcs.len());
    for f in defined_funcs {
        let name = function_meta
            .iter()
            .find(|m| m.func_index == f.abs_index)
            .and_then(|m| m.name.as_deref());
        // FEAT-065 (REQ-021): the shape hash is computed for EVERY function
        // (not only the unnamed tier) — it is the adjudicator's discriminator
        // between `still-open-untouched` and `still-open-after-edit`.
        let body_hash = body_shape_hash(&f.ops);
        // FEAT-087 (scry#122 item 2): the third element is a SECOND,
        // INDEPENDENT bit — "does this ident survive an edit to its own body?"
        // Only the body-shape-hash tier answers no; it is nonetheless NOT
        // build-local, because the hash is deterministic across builds.
        let (ident, build_local, survives_own_edit) = match name {
            None => (body_hash.clone(), false, false),
            Some(raw) => match strip_rust_disambiguator(raw) {
                Some(stripped) if candidates.get(&stripped) == Some(&1) => (stripped, false, true),
                Some(_) => (String::from(raw), true, true),
                None => (String::from(raw), false, true),
            },
        };
        func_identities.push(FuncIdentity {
            func_index: f.abs_index,
            ident: ident.clone(),
            id_build_local: build_local,
            ident_survives_own_edit: survives_own_edit,
            body_shape_hash: body_hash,
        });
        let keys = structural_keys(&f.ops);
        for (i, a) in advisories
            .iter_mut()
            .enumerate()
            .filter(|(_, a)| a.func_index == f.abs_index && !is_module_scoped(&a.code))
        {
            if let Some((path, ordinal)) = keys.get(a.pc as usize) {
                let kind = f
                    .ops
                    .get(a.pc as usize)
                    .map(op_report_name)
                    .unwrap_or_else(|| a.code.clone());
                let id_code = id_codes.get(i).copied().flatten();
                a.obligation_id =
                    obligation_id_of(&ident, path, &kind, *ordinal, id_code.unwrap_or(&a.code));
                a.site_key = site_key_of(&ident, path, &kind, *ordinal);
                a.group_key = group_key_of(&ident, path, &kind);
                a.id_build_local = build_local;
                a.ident_survives_own_edit = survives_own_edit;
            }
        }
    }
    func_identities
}

// ───────────────────────── FEAT-065 (REQ-021) ─────────────────────────

/// FEAT-065 (REQ-021): the verdict [`verify_against`] assigns to ONE obligation
/// when a fresh analysis is compared against a prior one.
///
/// `Discharged` is a CERTAINTY claim and is guarded the way the analyzer guards
/// PROVEN-SAFE: it is claimed only when every precondition holds (see
/// [`verify_against`]); everything short of that degrades to `Uncertain`, never
/// up to `Discharged`.
///
/// HONEST CONSEQUENCE, stated up front (FEAT-087 measured 10,520 of 10,520 on a
/// stripped build): on a STRIPPED module every obligation-carrying function
/// falls to the body-shape-hash identity tier, whose ident does not survive an
/// edit to its own body — so `ident_survives_own_edit` is false for EVERY
/// obligation and `Discharged` is UNREACHABLE. Stripping is standard in release
/// builds: on that common production shape a fix-verify loop cannot converge on
/// a `Discharged` verdict, and the honest answer it gets is `Uncertain`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyVerdict {
    /// A CERTAINTY claim: the obligation was open, the same site now carries a
    /// proof of safety, and every identity precondition held (four-term
    /// conjunction + shape-unchanged corroboration). The fix worked.
    Discharged,
    /// The site survives, the obligation persists, and the function body's
    /// operator shape did NOT change: genuinely not addressed.
    StillOpenUntouched,
    /// The site survives, the obligation persists, and the body DID change.
    /// scry cannot distinguish an ineffective fix from one it cannot see
    /// (FEAT-089) — explicitly NOT a failure signal to an agent.
    StillOpenAfterEdit,
    /// A previously PROVEN-SAFE site is no longer proven safe. Fails the gate.
    Regressed,
    /// The identity survived but its position (function index) changed — the
    /// module was edited around it. Informational; NOT progress.
    Moved,
    /// The site is gone because the code is gone (function deleted, or a
    /// same-kind operator removed from the region). NEVER a discharge:
    /// deleting the code that carried an unproven obligation proves nothing.
    RemovedWithCode,
    /// Some precondition of a certainty claim is unmet: identity not
    /// comparable across builds, identity destroyed by its own edit, group
    /// membership changed, body shape changed under a would-be discharge,
    /// ambiguous identity, or no prior state to compare against.
    Uncertain,
}

impl VerifyVerdict {
    /// Stable machine-readable name (what a JSON surface emits).
    pub fn as_str(self) -> &'static str {
        match self {
            VerifyVerdict::Discharged => "discharged",
            VerifyVerdict::StillOpenUntouched => "still-open-untouched",
            VerifyVerdict::StillOpenAfterEdit => "still-open-after-edit",
            VerifyVerdict::Regressed => "regressed",
            VerifyVerdict::Moved => "moved",
            VerifyVerdict::RemovedWithCode => "removed-with-code",
            VerifyVerdict::Uncertain => "uncertain",
        }
    }
}

/// FEAT-065 (REQ-021): the adjudication of one obligation across two runs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObligationVerdict {
    /// The verdict.
    pub verdict: VerifyVerdict,
    /// The obligation's site identity ([`Advisory::site_key`]) — the matching
    /// key. Matching is by `site_key`, NEVER by `obligation_id`: the id embeds
    /// the advisory code, which changes on the very transition being detected.
    pub site_key: String,
    /// The obligation's ordinal domain ([`Advisory::group_key`]).
    pub group_key: String,
    /// The advisory code of the obligation being adjudicated
    /// (e.g. `div-by-zero`).
    pub code: String,
    /// Function index in the BEFORE run (`None` for an obligation that has no
    /// before-state, i.e. `introduced`).
    pub before_func_index: Option<u32>,
    /// Function index in the AFTER run (`None` when the site is gone).
    pub after_func_index: Option<u32>,
    /// TRUE for an obligation in the AFTER run at a site that had NO advisory
    /// at all in the BEFORE run: introduced by the edit (or surfaced by
    /// identity churn — indistinguishable, and both fail the gate). An agent
    /// that fixed A while breaking B must not pass clean.
    pub introduced: bool,
    /// Human/agent rationale — for `Uncertain`, names the failed precondition.
    pub reason: String,
}

/// FEAT-065 (REQ-021): the full adjudication of an AFTER run against a BEFORE
/// run. See [`verify_against`].
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct VerifyReport {
    /// One entry per adjudicated obligation: every open obligation of the
    /// BEFORE run, every regression, and every introduced obligation of the
    /// AFTER run.
    pub verdicts: Vec<ObligationVerdict>,
}

impl VerifyReport {
    /// Count of verdicts of one kind.
    pub fn count(&self, v: VerifyVerdict) -> usize {
        self.verdicts.iter().filter(|o| o.verdict == v).count()
    }

    /// The machine-usable gate: FALSE when the edit regressed a proven-safe
    /// site or introduced a new obligation. `Uncertain` and `still-open-*` do
    /// NOT fail the gate — an agent is failed on positive evidence of harm,
    /// never on scry's inability to see its fix.
    pub fn gate_pass(&self) -> bool {
        !self
            .verdicts
            .iter()
            .any(|o| o.verdict == VerifyVerdict::Regressed || o.introduced)
    }

    /// Process-exit-code mapping of [`Self::gate_pass`] (0 = pass, 1 = fail).
    pub fn exit_code(&self) -> i32 {
        i32::from(!self.gate_pass())
    }
}

/// FEAT-065 (REQ-021): adjudicate a fresh analysis (`after`) against a prior
/// one (`before`) — scry judging its own oracle, conservative by construction.
///
/// Emits one [`ObligationVerdict`] for (a) every OPEN obligation of the
/// `before` run, (b) every regression of a previously PROVEN-SAFE site, and
/// (c) every obligation of the `after` run at a site with no prior advisory
/// (`introduced`). Matching is by [`Advisory::site_key`], NEVER by
/// `obligation_id` — several obligations share a site, and while FEAT-089
/// made a trap obligation's id survive its own open→proven flip (a
/// `proven-safe` advisory is keyed by the obligation code it discharges),
/// every OTHER advisory's id still embeds its surfaced code, so the site is
/// the one join key that is stable across every transition.
///
/// `Discharged` is a certainty claim, guarded like the analyzer guards
/// PROVEN-SAFE. It requires ALL of:
///   1. the site was matched by `site_key` and the after-run carries a proof
///      of safety there ([`AdvisoryClass::LeverageableFact`]) with no
///      persisting open advisory of the same code;
///   2. `!id_build_local` on both sides (FEAT-077 — build-local keys are not
///      comparable across builds at all);
///   3. `ident_survives_own_edit` on both sides (FEAT-087 — a body-derived
///      identity is destroyed by the very edit being adjudicated; on a
///      STRIPPED module this term is false for EVERY obligation, so
///      `Discharged` is UNREACHABLE there — the honest production-shape
///      consequence, stated rather than discovered);
///   4. the ordinal domain's membership (`group_key` population) is unchanged
///      (DD-021 — `survivor_inherits_deleted_identity` admits a false
///      discharge otherwise);
///   5. the containing function's OPERATOR SHAPE is unchanged
///      ([`FuncIdentity::body_shape_hash`]). This is the content
///      corroboration REQ-021's review made mandatory: a cardinality-
///      preserving delete+insert leaves the group membership byte-identical
///      (the case that falsified DD-021's rationale), so terms 1–4 alone
///      still admit a false discharge. A shape-preserving edit cannot delete
///      or insert an operator, so under term 5 site correspondence is exact —
///      which is also why term 5 subsumes term 4 (same shape ⇒ same groups);
///      term 4 is kept as an explicit, independently-checked conjunct.
///
/// Consequently a discharge is claimable on exactly two edit shapes: a fix in
/// ANOTHER function (the obligation's own body untouched), and an
/// immediates-only fix in the same function (`i32.const 0` → `i32.const 7`).
/// Everything else that looks like open→safe degrades to `Uncertain` — a
/// sound checker that over-claims a discharge is the same error as an unsound
/// analysis, one layer up.
pub fn verify_against(before: &AnalysisResult, after: &AnalysisResult) -> VerifyReport {
    use alloc::collections::{BTreeMap, BTreeSet};

    let module_site = site_key_of("<module>", "", "<module>", 0);

    // Per-function identity lookups (by index within a run, by ident across).
    let by_index = |r: &AnalysisResult| -> BTreeMap<u32, FuncIdentity> {
        r.func_identities
            .iter()
            .map(|f| (f.func_index, f.clone()))
            .collect()
    };
    let b_funcs = by_index(before);
    let a_funcs = by_index(after);
    let by_ident = |r: &AnalysisResult| -> BTreeMap<String, Vec<u32>> {
        let mut m: BTreeMap<String, Vec<u32>> = BTreeMap::new();
        for f in &r.func_identities {
            m.entry(f.ident.clone()).or_default().push(f.func_index);
        }
        m
    };
    let b_idents = by_ident(before);
    let a_idents = by_ident(after);

    // Site → advisories (non-empty keys only; module-scoped handled apart).
    fn site_map(r: &AnalysisResult) -> BTreeMap<String, Vec<&Advisory>> {
        let mut m: BTreeMap<String, Vec<&Advisory>> = BTreeMap::new();
        for adv in r.advisories.iter().filter(|x| !x.site_key.is_empty()) {
            m.entry(adv.site_key.clone()).or_default().push(adv);
        }
        m
    }
    let b_sites = site_map(before);
    let a_sites = site_map(after);

    // A site key claimed by advisories of MORE THAN ONE function in one run
    // (two byte-identical unnamed bodies, a duplicated name) cannot be matched
    // — every conclusion over it degrades to Uncertain.
    let ambiguous = |list: &[&Advisory]| -> bool {
        list.iter()
            .map(|x| x.func_index)
            .collect::<BTreeSet<_>>()
            .len()
            > 1
    };

    // Ordinal-domain population: group_key → its distinct site keys.
    let group_pop =
        |sites: &BTreeMap<String, Vec<&Advisory>>| -> BTreeMap<String, BTreeSet<String>> {
            let mut m: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
            for list in sites.values() {
                for adv in list {
                    m.entry(adv.group_key.clone())
                        .or_default()
                        .insert(adv.site_key.clone());
                }
            }
            m
        };
    let b_groups = group_pop(&b_sites);
    let a_groups = group_pop(&a_sites);
    let group_count = |m: &BTreeMap<String, BTreeSet<String>>, k: &str| -> usize {
        m.get(k).map(|s| s.len()).unwrap_or(0)
    };

    // Module-scope edit signal: the multiset of body shapes across the module.
    fn body_multiset(r: &AnalysisResult) -> Vec<&str> {
        let mut v: Vec<&str> = r
            .func_identities
            .iter()
            .map(|f| f.body_shape_hash.as_str())
            .collect();
        v.sort_unstable();
        v
    }
    let module_bodies_changed = body_multiset(before) != body_multiset(after);

    // An AMBIGUOUS site (claimed by several byte-identical unnamed bodies, or
    // by duplicated names) cannot be attributed function-by-function — but the
    // POPULATION argument still holds: when the site's full advisory multiset
    // (code + class) and the claiming functions' body-shape multiset are both
    // unchanged across the runs, every one of its obligations persists
    // wholesale in an unchanged body, and each is honestly
    // `still-open-untouched`. Measured need: 30 of 10,558 self-comparison
    // verdicts on scry's own module sit on 15 such duplicate-body sites.
    // Anything short of both equalities stays `Uncertain` — attribution of a
    // CHANGE inside an ambiguous group is exactly what cannot be done.
    let population_stable = |site: &str| -> bool {
        let (Some(bl), Some(al)) = (b_sites.get(site), a_sites.get(site)) else {
            return false;
        };
        let sig = |list: &[&Advisory], funcs: &BTreeMap<u32, FuncIdentity>| {
            let mut codes: Vec<(String, u8)> = list
                .iter()
                .map(|x| (x.code.clone(), x.class.rank()))
                .collect();
            codes.sort_unstable();
            let mut hashes: Vec<String> = list
                .iter()
                .map(|x| x.func_index)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .filter_map(|fi| funcs.get(&fi).map(|f| f.body_shape_hash.clone()))
                .collect();
            hashes.sort_unstable();
            (codes, hashes)
        };
        sig(bl, &b_funcs) == sig(al, &a_funcs)
    };

    let mut verdicts: Vec<ObligationVerdict> = Vec::new();
    let mut push = |verdict: VerifyVerdict,
                    site_key: &str,
                    group_key: &str,
                    code: &str,
                    bfi: Option<u32>,
                    afi: Option<u32>,
                    introduced: bool,
                    reason: &str| {
        verdicts.push(ObligationVerdict {
            verdict,
            site_key: site_key.into(),
            group_key: group_key.into(),
            code: code.into(),
            before_func_index: bfi,
            after_func_index: afi,
            introduced,
            reason: reason.into(),
        });
    };

    // ── pass 1: every OPEN obligation of the before run ─────────────────────
    for b in before
        .advisories
        .iter()
        .filter(|x| x.class.is_open_obligation())
    {
        if b.site_key.is_empty() {
            push(
                VerifyVerdict::Uncertain,
                "",
                &b.group_key,
                &b.code,
                Some(b.func_index),
                None,
                false,
                "no identity was stamped on this obligation; nothing can be matched",
            );
            continue;
        }
        // Module-scoped obligation (`unbounded-stack`): the `<module>` ident
        // cannot alias, but scry does not adjudicate a module-scoped
        // discharge — a vanished module obligation stays Uncertain.
        if b.site_key == module_site {
            let persists = after.advisories.iter().any(|x| {
                x.site_key == module_site && x.code == b.code && x.class.is_open_obligation()
            });
            if persists {
                let (v, why) = if module_bodies_changed {
                    (
                        VerifyVerdict::StillOpenAfterEdit,
                        "the module-scoped obligation persists and the module was edited",
                    )
                } else {
                    (
                        VerifyVerdict::StillOpenUntouched,
                        "the module-scoped obligation persists and no function body changed",
                    )
                };
                push(
                    v,
                    &b.site_key,
                    &b.group_key,
                    &b.code,
                    Some(b.func_index),
                    Some(b.func_index),
                    false,
                    why,
                );
            } else {
                push(
                    VerifyVerdict::Uncertain,
                    &b.site_key,
                    &b.group_key,
                    &b.code,
                    Some(b.func_index),
                    None,
                    false,
                    "the module-scoped obligation is no longer reported; scry does not adjudicate module-scoped discharge",
                );
            }
            continue;
        }

        let b_list = b_sites
            .get(&b.site_key)
            .map(|v| v.as_slice())
            .unwrap_or(&[]);
        if ambiguous(b_list) {
            if population_stable(&b.site_key) {
                push(
                    VerifyVerdict::StillOpenUntouched,
                    &b.site_key,
                    &b.group_key,
                    &b.code,
                    Some(b.func_index),
                    None,
                    false,
                    "the site is claimed by several identical functions, but its advisory population and every claiming body are unchanged wholesale; each obligation persists untouched",
                );
            } else {
                push(
                    VerifyVerdict::Uncertain,
                    &b.site_key,
                    &b.group_key,
                    &b.code,
                    Some(b.func_index),
                    None,
                    false,
                    "this site key is claimed by more than one function in the before run and its population changed; matching is ambiguous",
                );
            }
            continue;
        }

        match a_sites.get(&b.site_key) {
            Some(a_list) => {
                if ambiguous(a_list) {
                    if population_stable(&b.site_key) {
                        push(
                            VerifyVerdict::StillOpenUntouched,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            None,
                            false,
                            "the site is claimed by several identical functions, but its advisory population and every claiming body are unchanged wholesale; each obligation persists untouched",
                        );
                    } else {
                        push(
                            VerifyVerdict::Uncertain,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            None,
                            false,
                            "this site key is claimed by more than one function in the after run and its population changed; matching is ambiguous",
                        );
                    }
                    continue;
                }
                let afi = a_list[0].func_index;
                let shape_unchanged = match (b_funcs.get(&b.func_index), a_funcs.get(&afi)) {
                    (Some(x), Some(y)) => Some(x.body_shape_hash == y.body_shape_hash),
                    _ => None,
                };
                let same_code_open = a_list
                    .iter()
                    .any(|x| x.code == b.code && x.class.is_open_obligation());
                let proven_safe = a_list
                    .iter()
                    .find(|x| x.class == AdvisoryClass::LeverageableFact);

                if same_code_open {
                    match shape_unchanged {
                        Some(false) => push(
                            VerifyVerdict::StillOpenAfterEdit,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            Some(afi),
                            false,
                            "the obligation persists and the function body changed; scry cannot distinguish an ineffective fix from one it cannot see — not a failure signal",
                        ),
                        Some(true) if b.func_index != afi => push(
                            VerifyVerdict::Moved,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            Some(afi),
                            false,
                            "identity and body are unchanged but the function index shifted; informational, not progress",
                        ),
                        Some(true) => push(
                            VerifyVerdict::StillOpenUntouched,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            Some(afi),
                            false,
                            "the obligation persists and the function body's operator shape is unchanged; genuinely not addressed",
                        ),
                        None => push(
                            VerifyVerdict::Uncertain,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            Some(afi),
                            false,
                            "no function identity record on one side; the edit state cannot be corroborated",
                        ),
                    }
                } else if proven_safe.is_some() {
                    // Candidate discharge. Every conjunct must hold; the first
                    // failure names itself (a certainty claim degrades, never
                    // rounds up).
                    let safe = proven_safe.unwrap();
                    let reason_failed = if b.id_build_local || safe.id_build_local {
                        Some(
                            "id_build_local: this identity is not comparable across builds (FEAT-077)",
                        )
                    } else if !b.ident_survives_own_edit || !safe.ident_survives_own_edit {
                        Some(
                            "ident_survives_own_edit is false: a body-derived identity cannot corroborate a discharge (FEAT-087); on a stripped module this holds for every obligation, so discharged is unreachable there",
                        )
                    } else if group_count(&b_groups, &b.group_key)
                        != group_count(&a_groups, &b.group_key)
                    {
                        Some(
                            "the ordinal domain's membership changed; a surviving site may have inherited a deleted sibling's identity (DD-021)",
                        )
                    } else if shape_unchanged != Some(true) {
                        Some(
                            "the function's operator shape changed: a same-kind delete+insert is indistinguishable from a fix at this site (the case that falsified DD-021), so the open→safe transition cannot be attributed",
                        )
                    } else {
                        None
                    };
                    match reason_failed {
                        None => push(
                            VerifyVerdict::Discharged,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            Some(afi),
                            false,
                            "the obligation is now proven safe at the same site, the identity is comparable and edit-stable, the ordinal domain is unchanged, and the operator shape is unchanged (site correspondence exact)",
                        ),
                        Some(why) => push(
                            VerifyVerdict::Uncertain,
                            &b.site_key,
                            &b.group_key,
                            &b.code,
                            Some(b.func_index),
                            Some(afi),
                            false,
                            why,
                        ),
                    }
                } else {
                    push(
                        VerifyVerdict::Uncertain,
                        &b.site_key,
                        &b.group_key,
                        &b.code,
                        Some(b.func_index),
                        Some(afi),
                        false,
                        "the site survives but carries neither the obligation nor a proof of safety",
                    );
                }
            }
            None => {
                // The site key is gone. A missing key is evidence the code is
                // gone ONLY under the comparability conjunction (FEAT-087).
                if b.id_build_local || !b.ident_survives_own_edit {
                    push(
                        VerifyVerdict::Uncertain,
                        &b.site_key,
                        &b.group_key,
                        &b.code,
                        Some(b.func_index),
                        None,
                        false,
                        "the site key is absent but this identity tier cannot distinguish deletion from identity churn; a missing key is not evidence the code is gone",
                    );
                    continue;
                }
                let ident = b_funcs.get(&b.func_index).map(|f| f.ident.clone());
                let unique_before = ident
                    .as_deref()
                    .map(|i| b_idents.get(i).map(|v| v.len()) == Some(1))
                    .unwrap_or(false);
                let in_after = ident.as_deref().and_then(|i| a_idents.get(i));
                match (unique_before, in_after) {
                    (true, None) => push(
                        VerifyVerdict::RemovedWithCode,
                        &b.site_key,
                        &b.group_key,
                        &b.code,
                        Some(b.func_index),
                        None,
                        false,
                        "the containing function was deleted (its identity is absent from the after run); removal is not a discharge",
                    ),
                    (true, Some(v)) if v.len() == 1 => {
                        if group_count(&a_groups, &b.group_key)
                            < group_count(&b_groups, &b.group_key)
                        {
                            push(
                                VerifyVerdict::RemovedWithCode,
                                &b.site_key,
                                &b.group_key,
                                &b.code,
                                Some(b.func_index),
                                Some(v[0]),
                                false,
                                "a same-kind operator was removed from this region (the ordinal domain shrank); attribution within the group is positional (DD-020), but the removed code is certainly not a discharge",
                            );
                        } else {
                            push(
                                VerifyVerdict::Uncertain,
                                &b.site_key,
                                &b.group_key,
                                &b.code,
                                Some(b.func_index),
                                Some(v[0]),
                                false,
                                "the site key is absent while the function survives and the ordinal domain did not shrink; the site's fate cannot be attributed",
                            );
                        }
                    }
                    _ => push(
                        VerifyVerdict::Uncertain,
                        &b.site_key,
                        &b.group_key,
                        &b.code,
                        Some(b.func_index),
                        None,
                        false,
                        "the containing function's identity is not unique enough to pair across the runs",
                    ),
                }
            }
        }
    }

    // ── pass 2: regressions of previously PROVEN-SAFE sites ────────────────
    // Alarming is the safe direction: a false regression blocks a merge, a
    // missed one ships an unproven trap behind a stale green. COUNT-aware so a
    // duplicated (ambiguous) site cannot hide one copy regressing behind a
    // sibling that was open all along.
    let open_code_count = |list: &[&Advisory], code: &str| -> usize {
        list.iter()
            .filter(|x| x.code == code && x.class.is_open_obligation())
            .count()
    };
    for (site, a_list) in &a_sites {
        let Some(b_list) = b_sites.get(site) else {
            continue;
        };
        if !b_list
            .iter()
            .any(|x| x.class == AdvisoryClass::LeverageableFact)
        {
            continue;
        }
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        for a in a_list.iter().filter(|x| x.class.is_open_obligation()) {
            if !seen.insert(a.code.as_str()) {
                continue;
            }
            let n_after = open_code_count(a_list, &a.code);
            let n_before = open_code_count(b_list, &a.code);
            if n_after > n_before {
                push(
                    VerifyVerdict::Regressed,
                    site,
                    &a.group_key,
                    &a.code,
                    Some(b_list[0].func_index),
                    Some(a.func_index),
                    false,
                    "this site was PROVEN-SAFE in the before run and now carries an open obligation; the edit broke it",
                );
            }
        }
    }

    // ── pass 3: obligations introduced at sites with NO prior advisory ─────
    // An agent that fixed A while breaking B must not pass clean (AC12).
    for a in after
        .advisories
        .iter()
        .filter(|x| x.class.is_open_obligation())
    {
        if a.site_key.is_empty() || a.site_key == module_site {
            continue;
        }
        if b_sites.contains_key(&a.site_key) {
            continue;
        }
        push(
            VerifyVerdict::Uncertain,
            &a.site_key,
            &a.group_key,
            &a.code,
            None,
            Some(a.func_index),
            true,
            "an open obligation exists at a site with no prior advisory: introduced by the edit, or surfaced by identity churn — indistinguishable, and neither passes the gate",
        );
    }

    VerifyReport { verdicts }
}

/// Returns the advisories PLUS a parallel per-advisory IDENTITY code
/// (FEAT-089): `Some(code)` where the advisory's identity must be keyed by an
/// obligation code that differs from its surfaced `code`, `None` to key by
/// `Advisory::code` itself. Today only the `proven-safe` advisories need this:
/// their identity is the OBLIGATION they discharge (`div-by-zero` /
/// `signed-overflow` / `out-of-bounds`), not the verdict — so the obligation's
/// `obligation_id` is STABLE across the open→proven flip, which is what lets
/// an adjudicator address "the div-by-zero obligation at this site" before AND
/// after a fix. The vectors are index-parallel by construction; every `push`
/// to one pushes to the other.
fn compute_advisories(
    gaps: &[Gap],
    trap_checks: &[TrapCheck],
    handle_findings: &[HandleFinding],
    stack_usage: &StackUsage,
    memory_size_bytes: u64,
) -> (Vec<Advisory>, Vec<Option<&'static str>>) {
    let mut out: Vec<Advisory> = Vec::new();
    let mut id_codes: Vec<Option<&'static str>> = Vec::new();

    // (a) DefiniteFault — handle-lifetime bugs scry PROVED.
    for h in handle_findings {
        let (code, what, action) = match h.kind {
            HandleFindingKind::UseAfterDrop => (
                "use-after-drop",
                "used after it was already dropped",
                "remove the post-drop use, or drop the handle only after its last use — an `own` handle is affine (usable many times, dropped exactly once)",
            ),
            HandleFindingKind::DoubleDrop => (
                "double-drop",
                "dropped a second time after it was already dropped",
                "remove the redundant `resource.drop`; a handle must be dropped exactly once",
            ),
        };
        out.push(Advisory {
            func_index: h.func_index,
            pc: h.pc,
            class: AdvisoryClass::DefiniteFault,
            code: code.into(),
            detail: alloc::format!(
                "The resource handle in local {} is {} (via `{}`).",
                h.local_index,
                what,
                h.via
            ),
            suggested_action: action.into(),
            verification: "re-run scry: this handle_findings entry disappears".into(),
            counterexample: None,
            obligation_id: String::new(),
            site_key: String::new(),
            group_key: String::new(),
            id_build_local: false,
            ident_survives_own_edit: true,
        });
        id_codes.push(None);
    }

    // (b) UnprovenObligation / (d) LeverageableFact — from trap verdicts.
    for t in trap_checks {
        match t.verdict {
            TrapVerdict::PotentialTrap => {
                let (code, trap, action) = match t.kind {
                    TrapKind::DivByZero => (
                        "div-by-zero",
                        "divide-by-zero",
                        "guard the divisor to be non-zero (or constrain its interval to exclude 0) before this operation",
                    ),
                    TrapKind::SignedOverflow => (
                        "signed-overflow",
                        "INT_MIN / -1 overflow",
                        "guard against dividend == INT_MIN && divisor == -1, or constrain the operands",
                    ),
                    TrapKind::OutOfBounds => (
                        "out-of-bounds",
                        "out-of-bounds access",
                        "bound the effective address (base + offset + width) below the memory size before the access — e.g. a checked index or an `i < len` guard scry can see",
                    ),
                };
                out.push(Advisory {
                    func_index: t.func_index,
                    pc: t.pc,
                    class: AdvisoryClass::UnprovenObligation,
                    code: code.into(),
                    detail: alloc::format!(
                        "scry could not prove `{}` cannot {} on some run (POTENTIAL-TRAP). This is not a proof that it DOES trap — only that safety is not established.",
                        t.op, trap
                    ),
                    suggested_action: action.into(),
                    verification: alloc::format!(
                        "re-run scry: the `{}` {} trap_check at this pc becomes ProvenSafe",
                        t.op, code
                    ),
                    counterexample: Some(trap_counterexample(t.kind, &t.op, memory_size_bytes)),
                obligation_id: String::new(),
                site_key: String::new(),
                group_key: String::new(),
            id_build_local: false,
            ident_survives_own_edit: true,
                });
                // The surfaced code IS the obligation code here.
                id_codes.push(None);
            }
            TrapVerdict::ProvenSafe => {
                let trap = match t.kind {
                    TrapKind::DivByZero => "divide-by-zero",
                    TrapKind::SignedOverflow => "INT_MIN/-1 overflow",
                    TrapKind::OutOfBounds => "out-of-bounds access",
                };
                out.push(Advisory {
                    func_index: t.func_index,
                    pc: t.pc,
                    class: AdvisoryClass::LeverageableFact,
                    code: "proven-safe".into(),
                    detail: alloc::format!(
                        "scry PROVED `{}` cannot {} on any run.",
                        t.op, trap
                    ),
                    suggested_action: alloc::format!(
                        "you may rely on this: a defensive runtime check for {} here is redundant and can be soundly elided",
                        trap
                    ),
                    verification: alloc::format!(
                        "the `{}` trap_check stays ProvenSafe after the change",
                        t.op
                    ),
                    counterexample: None,
                obligation_id: String::new(),
                site_key: String::new(),
                group_key: String::new(),
            id_build_local: false,
            ident_survives_own_edit: true,
                });
                // FEAT-089: the identity of a proven-safe fact is the
                // OBLIGATION it discharges, so the id survives the verdict
                // flip ("changes the verdict, never the identity").
                id_codes.push(Some(match t.kind {
                    TrapKind::DivByZero => "div-by-zero",
                    TrapKind::SignedOverflow => "signed-overflow",
                    TrapKind::OutOfBounds => "out-of-bounds",
                }));
            }
        }
    }

    // (c) PrecisionGap — where the interpreter degraded to ⊤.
    for g in gaps {
        let (code, action) = match g.kind {
            GapKind::UnsupportedOp => (
                "unsupported-op",
                "this operator is outside scry's modelled set, so the function degrades to ⊤ from here; extract the surrounding analyzable logic into its own function, or accept the precision loss",
            ),
            GapKind::UnmodeledBranch => (
                "unmodeled-branch",
                "a multi-target branch (`br_table`) is not modelled; refactor to modelled control flow if precision here matters, or accept it",
            ),
            GapKind::UnmodeledMemoryAddress => (
                "unmodeled-memory-address",
                "the memory address is not an i32-shaped value scry can track, so the region state is scrubbed; compute the address as a tracked i32 if precision here matters",
            ),
            GapKind::UnmodeledControlFlow => (
                "unmodeled-control-flow",
                "a typed `if`/`block` region is handled by write-set havoc (its written locals widen to ⊤); simplify the region or accept the local precision loss",
            ),
        };
        out.push(Advisory {
            func_index: g.func_index,
            pc: g.pc,
            class: AdvisoryClass::PrecisionGap,
            code: code.into(),
            detail: alloc::format!(
                "scry lost precision (degraded to ⊤) at `{}` — downstream facts in this function are weaker.",
                g.op
            ),
            suggested_action: action.into(),
            verification: alloc::format!(
                "re-run scry: the gap at fn{}:{} is gone (or no longer reached)",
                g.func_index, g.pc
            ),
            counterexample: None,
                obligation_id: String::new(),
                site_key: String::new(),
                group_key: String::new(),
            id_build_local: false,
            ident_survives_own_edit: true,
        });
        id_codes.push(None);
    }

    // (b′) UnprovenObligation — an unbounded worst-case shadow stack.
    if stack_usage.max_stack_bytes == StackBound::Unbounded {
        out.push(Advisory {
            func_index: 0,
            pc: 0,
            class: AdvisoryClass::UnprovenObligation,
            code: "unbounded-stack".into(),
            detail:
                "the module's worst-case shadow-stack usage could not be bounded (recursion, or an unresolvable / growable / host-writable indirect-call table)."
                    .into(),
            suggested_action:
                "break the recursion, or make the dispatch table non-growable and fully enumerable (so call_indirect targets resolve), to obtain a finite bound"
                    .into(),
            verification: "re-run scry: stack_usage.max_stack_bytes becomes Bytes(n)".into(),
            counterexample: None,
                obligation_id: String::new(),
                site_key: String::new(),
                group_key: String::new(),
            id_build_local: false,
            ident_survives_own_edit: true,
        });
        id_codes.push(None);
    }

    // Sort advisories and identity codes TOGETHER — the two vectors are
    // index-parallel and a lone `out.sort` would silently re-key identities.
    let mut pairs: Vec<(Advisory, Option<&'static str>)> = out.into_iter().zip(id_codes).collect();
    pairs.sort_by_key(|(a, _)| (a.class.rank(), a.func_index, a.pc));
    pairs.into_iter().unzip()
}

/// Pop two companion operands, apply a binary transfer when both are modelled
/// and same-width, push the result (⊤/opaque otherwise).
#[inline]
fn bits_binop(
    stack: &mut Vec<Option<(BitsCong, u32)>>,
    f: impl Fn(&BitsCong, &BitsCong, u32) -> BitsCong,
) {
    let b = stack.pop().flatten();
    let a = stack.pop().flatten();
    let out = match (a, b) {
        (Some((ba, wa)), Some((bb, wb))) if wa == wb => Some((f(&ba, &bb, wa), wa)),
        _ => None,
    };
    stack.push(out);
}

/// Pop a (count, value) pair; apply the shift only when the count is a known
/// constant (taken mod width); push ⊤/opaque otherwise.
#[inline]
fn bits_shift(
    stack: &mut Vec<Option<(BitsCong, u32)>>,
    f: impl Fn(&BitsCong, u32, u32) -> BitsCong,
) {
    let count = stack.pop().flatten();
    let value = stack.pop().flatten();
    let out = match value {
        Some((bv, w)) => bits_as_const(&count).map(|c| (f(&bv, (c % w as u64) as u32, w), w)),
        None => None,
    };
    stack.push(out);
}

/// Build a [`BitFact`] from a companion value.
#[inline]
fn make_bit_fact(func_index: u32, pc: u32, local_index: u32, width: u32, bc: &BitsCong) -> BitFact {
    let (known_zeros, known_ones) = match bc.kb {
        scry_bits::KnownBits::Bits { zeros, ones } => (zeros, ones),
        scry_bits::KnownBits::Bottom => (0, 0),
    };
    let (cong_modulus, cong_residue) = match bc.cong {
        Cong::Mod { m, r } => (m, r),
        Cong::Bottom => (1, 0),
    };
    BitFact {
        func_index,
        pc,
        local_index,
        width,
        known_zeros,
        known_ones,
        cong_modulus,
        cong_residue,
    }
}

/// FEAT-027: assemble per-function human-readable metadata for every index
/// (imports + defined). Name priority: custom `name` section → first export
/// name → import `module.field` → `None`.
fn build_function_meta(
    import_func_count: u32,
    defined_func_count: u32,
    import_func_meta: &[String],
    export_names: &[(u32, String)],
    name_section: &[(u32, String)],
) -> Vec<FunctionMeta> {
    let total = import_func_count.saturating_add(defined_func_count);
    let mut out = Vec::with_capacity(total as usize);
    for idx in 0..total {
        let imported = idx < import_func_count;
        let exports: Vec<String> = export_names
            .iter()
            .filter(|(i, _)| *i == idx)
            .map(|(_, n)| n.clone())
            .collect();
        // Priority: name section → export name → import "module.field".
        let name = name_section
            .iter()
            .find(|(i, _)| *i == idx)
            .map(|(_, n)| n.clone())
            .or_else(|| exports.first().cloned())
            .or_else(|| {
                if imported {
                    import_func_meta.get(idx as usize).cloned()
                } else {
                    None
                }
            });
        out.push(FunctionMeta {
            func_index: idx,
            name,
            imported,
            exports,
        });
    }
    out
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
fn widen_abstract(a: &AbstractValue, b: &AbstractValue, thresholds: &[i64]) -> AbstractValue {
    match (a, b) {
        (AbstractValue::I32Interval(x), AbstractValue::I32Interval(y)) => {
            AbstractValue::I32Interval(scry_interval::widen_with_thresholds(*x, *y, thresholds))
        }
        (AbstractValue::I64Interval(x), AbstractValue::I64Interval(y)) => {
            AbstractValue::I64Interval(scry_interval::widen_with_thresholds(*x, *y, thresholds))
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

fn widen_locals(
    a: &[AbstractValue],
    b: &[AbstractValue],
    thresholds: &[i64],
) -> Vec<AbstractValue> {
    a.iter()
        .zip(b)
        .map(|(x, y)| widen_abstract(x, y, thresholds))
        .collect()
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

/// What a `local.set`/`local.tee` stores, recovered by a look-behind over the
/// producer ops (FEAT-016 slice-2b-ii octagon transfer). `Other` (anything not
/// one of these canonical idioms) is handled by forgetting the variable.
enum StoreSrc {
    /// `x := c`
    Const(i64),
    /// `x := y`
    Copy(u32),
    /// `x := y + c` (a `local.get y; i32.const c; i32.add|sub; local.set x`
    /// idiom — `sub` is recorded as `+(-c)`). Covers the self-increment `x :=
    /// x + c` when `y == x`.
    AddConst(u32, i64),
    Other,
}

/// Classify the value a `local.set`/`local.tee` at `pc` stores, by matching
/// the producer ops immediately before it. Sound: the producers are
/// consecutive (structured Wasm has no mid-straight-line branch targets), so
/// the value on top of the stack is exactly what they computed. Anything not
/// matched is `Other` (⇒ forget). Only `i32.const` literals and `local.get`
/// of an unmodified local are tracked relationally.
fn classify_store(ops: &[Operator<'_>], pc: usize) -> StoreSrc {
    // `x := y ± c` : local.get y; i32.const c; i32.add|sub; local.set x
    if pc >= 3
        && let (Operator::LocalGet { local_index: y }, Operator::I32Const { value: c }, op3) =
            (&ops[pc - 3], &ops[pc - 2], &ops[pc - 1])
    {
        match op3 {
            Operator::I32Add => return StoreSrc::AddConst(*y, *c as i64),
            Operator::I32Sub => return StoreSrc::AddConst(*y, (*c as i64).saturating_neg()),
            _ => {}
        }
    }
    if pc >= 1 {
        match &ops[pc - 1] {
            Operator::I32Const { value } => return StoreSrc::Const(*value as i64),
            Operator::LocalGet { local_index } => return StoreSrc::Copy(*local_index),
            _ => {}
        }
    }
    StoreSrc::Other
}

/// Add to the octagon the difference constraint implied by the signed
/// comparison `A OP B` being true (`taken`) or false (FEAT-016 slice-2b-ii).
/// `==`/`!=` add an equality (both directions) when they pin `A = B`, and add
/// nothing on the `≠` edge (not octagon-expressible). All bounds are coherent
/// ([`scry_octagon::add_diff`]).
fn refine_octagon_rel(oct: &Octagon, a: u32, b: u32, op: GuardOp, taken: bool) -> Octagon {
    use scry_octagon::add_diff;
    match (op, taken) {
        // A < B (true) / A ≥ B (false→A<B is the negation of ≥): A − B ≤ −1
        (GuardOp::Lt, true) | (GuardOp::Ge, false) => add_diff(oct, a, b, -1),
        // A ≥ B / ¬(A < B): B − A ≤ 0
        (GuardOp::Ge, true) | (GuardOp::Lt, false) => add_diff(oct, b, a, 0),
        // A ≤ B: A − B ≤ 0
        (GuardOp::Le, true) | (GuardOp::Gt, false) => add_diff(oct, a, b, 0),
        // A > B: B − A ≤ −1
        (GuardOp::Gt, true) | (GuardOp::Le, false) => add_diff(oct, b, a, -1),
        // A == B: A − B ≤ 0 ∧ B − A ≤ 0
        (GuardOp::Eq, true) | (GuardOp::Ne, false) => {
            let o = add_diff(oct, a, b, 0);
            add_diff(&o, b, a, 0)
        }
        // A ≠ B: not an octagon constraint.
        (GuardOp::Eq, false) | (GuardOp::Ne, true) => oct.clone(),
    }
}

/// FEAT-057 slice 2a: what a `local.set`/`local.tee` stores, for the
/// polyhedra transfer. Extends [`StoreSrc`] with the two-LOCAL arithmetic
/// shapes (`z := x + y` / `z := x − y`) — the general-coefficient facts that
/// are the polyhedra's reason to exist (a 3-variable equality is outside the
/// octagon's `±xᵢ ± xⱼ ≤ c` form). The patterns are disjoint from
/// [`classify_store`]'s (`local.get; local.get; add` vs `local.get;
/// i32.const; add`), so this delegates for everything else.
enum PolyStoreSrc {
    /// `x := c`
    Const(i64),
    /// `x := y`
    Copy(u32),
    /// `x := y + c`
    AddConst(u32, i64),
    /// `x := a + b` (a `local.get a; local.get b; i32.add; local.set x` idiom)
    AddLocals(u32, u32),
    /// `x := a − b`
    SubLocals(u32, u32),
    Other,
}

/// Classify the value a `local.set`/`local.tee` at `pc` stores, for the
/// polyhedra transfer. Sound for the same reason [`classify_store`] is: the
/// producer ops are consecutive (structured Wasm has no mid-straight-line
/// branch targets), so the stack top is exactly what they computed.
fn classify_poly_store(ops: &[Operator<'_>], pc: usize) -> PolyStoreSrc {
    // `x := a ± b` : local.get a; local.get b; i32.add|sub; local.set x
    if pc >= 3
        && let (Operator::LocalGet { local_index: a }, Operator::LocalGet { local_index: b }, op3) =
            (&ops[pc - 3], &ops[pc - 2], &ops[pc - 1])
    {
        match op3 {
            Operator::I32Add => return PolyStoreSrc::AddLocals(*a, *b),
            Operator::I32Sub => return PolyStoreSrc::SubLocals(*a, *b),
            _ => {}
        }
    }
    match classify_store(ops, pc) {
        StoreSrc::Const(c) => PolyStoreSrc::Const(c),
        StoreSrc::Copy(src) => PolyStoreSrc::Copy(src),
        StoreSrc::AddConst(src, c) => PolyStoreSrc::AddConst(src, c),
        StoreSrc::Other => PolyStoreSrc::Other,
    }
}

/// FEAT-057 slice 2a: add the equality `Σ coeff·local = rhs` to the poly as
/// its two half-spaces (`≤ rhs` and `≥ rhs`). `terms` accumulate additively,
/// so a repeated local (e.g. `z := x + x`) folds into one coefficient.
fn poly_with_equality(mut p: Poly, dim: u32, terms: &[(u32, i64)], rhs: i64) -> Poly {
    let mut coeffs = alloc::vec![0i64; dim as usize];
    for &(v, a) in terms {
        coeffs[v as usize] += a;
    }
    p.add_constraint(scry_poly::Constraint {
        coeffs: coeffs.clone(),
        bound: rhs,
    });
    p.add_constraint(scry_poly::Constraint {
        coeffs: coeffs.iter().map(|&a| -a).collect(),
        bound: -rhs,
    });
    p
}

/// FEAT-057 slice 2a: add to the polyhedra the difference constraint implied
/// by the signed comparison `A OP B` being true (`taken`) or false — the
/// poly-side mirror of [`refine_octagon_rel`], adding the SAME facts. Sound
/// for the same reason: `guard_op` admits only SIGNED comparisons, which are
/// facts about the locals' signed values (no wrap consideration applies — no
/// arithmetic is performed). The `≠` edge adds nothing (not convex).
fn refine_poly_rel(poly: &Poly, dim: u32, a: u32, b: u32, op: GuardOp, taken: bool) -> Poly {
    let diff = |x: u32, y: u32, c: i64| {
        let mut p = poly.clone();
        let mut coeffs = alloc::vec![0i64; dim as usize];
        coeffs[x as usize] = 1;
        coeffs[y as usize] = -1;
        p.add_constraint(scry_poly::Constraint { coeffs, bound: c });
        p
    };
    match (op, taken) {
        // A < B: A − B ≤ −1
        (GuardOp::Lt, true) | (GuardOp::Ge, false) => diff(a, b, -1),
        // A ≥ B: B − A ≤ 0
        (GuardOp::Ge, true) | (GuardOp::Lt, false) => diff(b, a, 0),
        // A ≤ B: A − B ≤ 0
        (GuardOp::Le, true) | (GuardOp::Gt, false) => diff(a, b, 0),
        // A > B: B − A ≤ −1
        (GuardOp::Gt, true) | (GuardOp::Le, false) => diff(b, a, -1),
        // A == B: both directions.
        (GuardOp::Eq, true) | (GuardOp::Ne, false) => {
            let p = diff(a, b, 0);
            let mut coeffs = alloc::vec![0i64; dim as usize];
            coeffs[b as usize] = 1;
            coeffs[a as usize] = -1;
            let mut p2 = p;
            p2.add_constraint(scry_poly::Constraint { coeffs, bound: 0 });
            p2
        }
        // A ≠ B: not convex — nothing to add.
        (GuardOp::Eq, false) | (GuardOp::Ne, true) => poly.clone(),
    }
}

/// The reduced product (FEAT-016 slice-2b-ii observability, DD-015 2c): tighten
/// each local's interval using the octagon, with NO WIT change. Inject the
/// current interval bounds into a working octagon (sound — they hold for every
/// concrete value), then project each variable back out and `meet` it with its
/// interval. This is where a relational bound becomes a numeric one:
/// `i ≤ n ∧ n ≤ 10 ⟹ i ≤ 10`. The octagon's `bound_of` closes internally, so
/// the injected unary bounds propagate through the difference constraints.
/// Inject each local's interval bounds into the octagon as coherent unary
/// constraints. Sound: the interval bounds hold for every concrete value of
/// the local at this point, so adding them only tightens. This is the
/// interval→octagon half of the reduced product; it is what lets a difference
/// relation (`i − n`) combine with a unary bound (`n ≤ 10`) — and what seeds
/// the loop entry so the relation survives the `entry ⊔ back-edge` join.
fn inject_intervals(octagon: &Octagon, locals: &[AbstractValue]) -> Octagon {
    let mut oct = octagon.clone();
    for (k, v) in locals.iter().enumerate() {
        if let AbstractValue::I32Interval(iv) = v {
            if iv.lo != i64::MIN {
                oct = scry_octagon::set_lower(&oct, k as u32, iv.lo);
            }
            if iv.hi != i64::MAX {
                oct = scry_octagon::set_upper(&oct, k as u32, iv.hi);
            }
        }
    }
    oct
}

fn reduce_locals(locals: &[AbstractValue], octagon: &Octagon) -> Vec<AbstractValue> {
    // Fast path: a top octagon carries no relations, so projection is the
    // identity — preserve the exact interval-only behaviour (and the cost).
    if octagon.m.iter().all(|&b| b == scry_octagon::INF || b == 0) {
        return locals.iter().map(clone_value).collect();
    }
    let oct = inject_intervals(octagon, locals);
    locals
        .iter()
        .enumerate()
        .map(|(k, v)| match v {
            AbstractValue::I32Interval(iv) => match scry_octagon::bound_of(&oct, k as u32) {
                Some((lo, hi)) => {
                    AbstractValue::I32Interval(scry_interval::meet(*iv, Interval { lo, hi }))
                }
                // Infeasible (⊥): the program point is unreachable; keep the
                // interval as a sound over-approximation rather than fabricate.
                None => clone_value(v),
            },
            _ => clone_value(v),
        })
        .collect()
}

/// Did a straight-line sequence fall through to its end, or did control
/// leave it (a `br`/`return`)? FEAT-016 slice-2a structured dataflow.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Flow {
    Fall,
    Diverged,
}

/// The abstract state a branch carries to its target: the locals AND the
/// relational octagon (FEAT-016 slice-2b-ii), joined across all branches that
/// target the same label.
#[derive(Clone)]
struct BreakState {
    locals: Vec<AbstractValue>,
    octagon: Octagon,
    /// FEAT-058: memory content carried to the branch target, joined across all
    /// branches to the same label (in lockstep with `locals`/`octagon`).
    mem: Segmentation,
    /// FEAT-057: polyhedra state carried to the branch target, joined across
    /// all branches to the same label (in lockstep with `locals`/`octagon`).
    poly: Poly,
}

/// A structured label (an enclosing `block` or `loop`) and the joined state
/// of every branch that targets it. For a `block` the branch target is the
/// state AFTER the block; for a `loop` it is the loop header (the back-edge).
struct Label {
    breaks: Option<BreakState>,
}

impl Label {
    fn record(
        &mut self,
        locals: &[AbstractValue],
        octagon: &Octagon,
        mem: &Segmentation,
        poly: &Poly,
    ) {
        self.breaks = Some(match self.breaks.take() {
            Some(acc) => BreakState {
                locals: join_locals(&acc.locals, locals),
                octagon: scry_octagon::join(&acc.octagon, octagon),
                mem: acc.mem.join(mem),
                poly: acc.poly.join(poly),
            },
            None => BreakState {
                locals: locals.to_vec(),
                octagon: octagon.clone(),
                mem: mem.clone(),
                poly: poly.clone(),
            },
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
    /// FEAT-042: syntactic widening thresholds for this function (its constant
    /// operands, plus 0), used by the loop-header widening to snap a runaway
    /// bound to the nearest enclosing constant instead of ±∞.
    widen_thresholds: Vec<i64>,
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
                        locals: snapshot_locals(&reduce_locals(&ctx.locals, &ctx.octagon)),
                        operand_stack: snapshot_stack(&ctx.operand_stack),
                        relational: snapshot_relational(&ctx.octagon),
                        memory: snapshot_memory(&ctx.mem),
                        linear: snapshot_linear(&ctx.poly),
                    });
                }
                pc = next;
                continue;
            }

            // ── Relational guard refinement (FEAT-016 slice-2b-ii) ──
            // A comparison-guarded branch on TWO locals `local.get A;
            // local.get B; <cmp>; br_if D` adds the octagon difference
            // constraint the comparison implies on each edge (taken → label D,
            // not-taken → fall through). This is what bounds a counter by a
            // VARIABLE relation (`i < n`, n not constant) — the case the
            // constant peephole above cannot reach.
            if let Some(next) = self.try_guard_brif_rel(pc, ctx, labels) {
                if emit && !ctx.degraded {
                    self.points.push(ProgramPoint {
                        func_index: self.func_index,
                        pc: pc as u32,
                        locals: snapshot_locals(&reduce_locals(&ctx.locals, &ctx.octagon)),
                        operand_stack: snapshot_stack(&ctx.operand_stack),
                        relational: snapshot_relational(&ctx.octagon),
                        memory: snapshot_memory(&ctx.mem),
                        linear: snapshot_linear(&ctx.poly),
                    });
                }
                pc = next;
                continue;
            }

            // ── Branches: contribute to the targeted label ──────────
            match &self.ops[pc] {
                Operator::Br { relative_depth } => {
                    // `None` = the branch exits the function; nothing to record.
                    if let Some(l) = self.target(labels, *relative_depth) {
                        l.record(&ctx.locals, &ctx.octagon, &ctx.mem, &ctx.poly);
                    }
                    return Ok(Flow::Diverged);
                }
                Operator::BrIf { relative_depth } => {
                    // br_if pops its i32 condition; on the taken edge the
                    // locals reach the target, on the not-taken edge we fall
                    // through (both modelled — sound).
                    let _ = ctx.operand_stack.pop();
                    // `None` = the taken edge exits the function; the
                    // fall-through below is still modelled.
                    if let Some(l) = self.target(labels, *relative_depth) {
                        l.record(&ctx.locals, &ctx.octagon, &ctx.mem, &ctx.poly);
                    }
                    pc += 1;
                    continue;
                }
                Operator::Return => {
                    return Ok(Flow::Diverged);
                }
                Operator::BrTable { .. } => {
                    // Unmodelled multi-target branch: sound fallback.
                    ctx.scrub_to_top(Gap {
                        func_index: self.func_index,
                        pc: pc as u32,
                        op: "br_table".to_string(),
                        kind: GapKind::UnmodeledBranch,
                    });
                    return Ok(Flow::Diverged);
                }
                _ => {}
            }

            // ── Straight-line operator (interpret_op) ───────────────
            // FEAT-089 look-behind: is the top of stack the freshly-read value
            // of a local known non-zero on this path? Sound because whenever
            // `ops[pc-1]` is a `local.get`, control reached `pc` ONLY by
            // executing it straight-line (`pc += 1`): every jump into `pc`
            // lands after a `block`/`loop`/`end`/`br_if` — never after a
            // `local.get` — and `local.get` writes nothing, so the fact that
            // held at `pc-1` still holds at `pc`. Consulted only by the
            // div/rem trap check; recomputed fresh for every op (no staleness).
            let divisor_from_nonzero_local = pc > 0
                && matches!(&self.ops[pc - 1], Operator::LocalGet { local_index }
                    if ctx.nonzero_locals.contains(local_index));
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
                    divisor_from_nonzero_local,
                )?,
                StepOutcome::Stop
            );
            // Octagon relational transfer for this op (FEAT-016 slice-2b-ii):
            // local.set/tee update or forget the written variable's relations.
            self.octagon_transfer(pc, ctx);
            // FEAT-057 slice 2a: polyhedra transfer — wrap-gated assignment
            // equalities, projection (FM-forget) for everything else.
            self.poly_transfer(pc, ctx);
            if emit && !ctx.degraded {
                self.points.push(ProgramPoint {
                    func_index: self.func_index,
                    pc: pc as u32,
                    locals: snapshot_locals(&reduce_locals(&ctx.locals, &ctx.octagon)),
                    operand_stack: snapshot_stack(&ctx.operand_stack),
                    relational: snapshot_relational(&ctx.octagon),
                    memory: snapshot_memory(&ctx.mem),
                    linear: snapshot_linear(&ctx.poly),
                });
            }
            if stop {
                return Ok(Flow::Diverged);
            }
            pc += 1;
        }
        Ok(Flow::Fall)
    }

    /// The label a `br relative_depth` targets (innermost = depth 0), or `None`
    /// when the branch leaves the FUNCTION rather than an enclosing region.
    ///
    /// scry#125: `labels` is pushed only on ENTERING a block/loop/if, so the
    /// function body's own implicit label is never on it. A branch whose depth
    /// reaches past every enclosing region therefore targets that label — which
    /// is a RETURN, with no in-function successor to carry state to. `n == 0`
    /// (a branch at function top level) is the degenerate case of the same
    /// thing, and it used to index an empty slice and PANIC, trapping the guest
    /// so the host got neither arm of `result<analysis-result, analyze-error>`.
    ///
    /// `checked_sub` rather than `saturating_sub` is deliberate and fixes a
    /// second defect: clamping sent a branch that exits the function into the
    /// OUTERMOST region's label, so `(block br 1)` recorded the function-exit
    /// state as if it reached that block. Over-approximate, hence sound, but
    /// attributed to a label the state never arrives at.
    ///
    /// Returning `None` records nothing, which is sound: the branch genuinely
    /// leaves the function, so no in-function path is being dropped. It is not
    /// a gap either — a return is fully modelled, and emitting one would
    /// inflate the gap report with an ordinary construct.
    fn target<'l>(&self, labels: &'l mut [Label], relative_depth: u32) -> Option<&'l mut Label> {
        let idx = labels.len().checked_sub(1 + relative_depth as usize)?;
        labels.get_mut(idx)
    }

    /// FEAT-016 slice-2b-i guard refinement, extended by FEAT-070 (REQ-020).
    /// If the ops at `pc` are a guarded branch on a single local, refine `L`'s
    /// interval by the guard on both edges — record the taken-edge locals
    /// (guard true) into label `D`, set `ctx.locals` to the not-taken-edge
    /// locals (guard false) — and return the pc just past the idiom. Returns
    /// `None` (caller handles `pc` normally) for anything else.
    ///
    /// Recognised shapes, where the leading op is `local.get L` **or**
    /// `local.tee L` (FEAT-070 — LLVM emits the tee form constantly, for
    /// increment-and-test and count-to-zero loops):
    ///
    /// ```text
    ///   <get|tee> L; i32.const C; <signed cmp>; br_if D   (4 ops)
    ///   <get|tee> L; i32.eqz; br_if D                     (3 ops)  taken ⇔ L == 0
    ///   <get|tee> L; br_if D                              (2 ops)  taken ⇔ L ≠ 0
    /// ```
    ///
    /// The 2-op form is the bare-truthiness branch: `br_if` takes the edge when
    /// the popped value is non-zero, so the FALL-THROUGH pins `L` to exactly 0.
    /// That is the dual of the `i32.eqz` shape and the reason a count-to-zero
    /// loop's exit value is knowable at all.
    ///
    /// Operand stack: with a leading `local.get` the idiom's net effect is zero
    /// (push L, push C, cmp pops 2 / pushes 1, br_if pops 1). With a leading
    /// `local.tee` it is **−1** — the tee'd value arrives on the stack and is
    /// ultimately consumed by the `br_if` — so the tee form pops once. A
    /// shape-blind skip would leak or underflow the modelled stack.
    ///
    /// Soundness note for the tee form: `local.tee L` **assigns** `L`, and this
    /// peephole bypasses the normal `LocalTee` transfer (including
    /// [`Self::octagon_transfer`]). The assignment is therefore applied here and
    /// `L`'s octagon relations are FORGOTTEN — retaining a relation for a local
    /// that was just overwritten would be unsound. All bail-out checks run
    /// before any mutation, so a `None` return leaves `ctx` untouched and the
    /// caller can re-process the ops normally.
    fn try_guard_brif(&self, pc: usize, ctx: &mut FuncCtx, labels: &mut [Label]) -> Option<usize> {
        if ctx.degraded {
            return None;
        }
        let ops = self.ops;
        // Leading op: a read (`local.get`) or a read-modify (`local.tee`).
        let (local, is_tee) = match ops.get(pc)? {
            Operator::LocalGet { local_index } => (*local_index, false),
            Operator::LocalTee { local_index } => (*local_index, true),
            _ => return None,
        };
        // Guard shape, longest match first.
        let (c, op, depth, next) = match (ops.get(pc + 1)?, ops.get(pc + 2), ops.get(pc + 3)) {
            (Operator::I32Const { value }, Some(cmp), Some(Operator::BrIf { relative_depth })) => {
                (*value as i64, guard_op(cmp)?, *relative_depth, pc + 4)
            }
            (Operator::I32Eqz, Some(Operator::BrIf { relative_depth }), _) => {
                (0, GuardOp::Eq, *relative_depth, pc + 3)
            }
            // FEAT-070: bare truthiness — taken ⇔ L ≠ 0, fall-through ⇔ L == 0.
            (Operator::BrIf { relative_depth }, _, _) => (0, GuardOp::Ne, *relative_depth, pc + 2),
            _ => return None,
        };

        // ── all bail-out checks BEFORE any mutation ──────────────────────
        if local as usize >= ctx.locals.len() {
            return None;
        }
        // The interval to refine: for the tee form it is the value being
        // assigned (the stack top), not the local's stale pre-assignment value.
        let iv = if is_tee {
            match ctx.operand_stack.last() {
                Some(AbstractValue::I32Interval(iv)) => *iv,
                _ => return None,
            }
        } else {
            match ctx.locals.get(local as usize) {
                Some(AbstractValue::I32Interval(iv)) => *iv,
                _ => return None,
            }
        };

        // ── mutation from here on ────────────────────────────────────────
        if is_tee {
            // Consume the tee'd value and apply the assignment this peephole
            // is skipping; forget the local's relations (see the doc comment).
            // FEAT-089: the tee is a WRITE — the local's non-zero fact dies
            // here (the qualifying fall-through below may re-establish it,
            // and then it speaks about the freshly-assigned value).
            ctx.nonzero_locals.remove(&local);
            let _ = ctx.operand_stack.pop();
            ctx.locals[local as usize] = AbstractValue::I32Interval(iv);
            // Apply the octagon side of the assignment this peephole skips.
            // `octagon_transfer` models the recognised producer shapes (const /
            // copy / add-const) and FORGETS `local` otherwise — at least as
            // sound as a blanket forget, and strictly more precise on the
            // increment/decrement-and-test idiom FEAT-070 exists to handle
            // (clean-room finding: the blanket forget was a precision
            // regression on this feature's own motivating shape).
            self.octagon_transfer(pc, ctx);
            // FEAT-057: the tee is a write the poly must see too — same
            // wrap-gated transfer as the straight-line path (projects the
            // assigned variable unless a no-wrap equality is provable).
            self.poly_transfer(pc, ctx);
        }
        let taken_iv = refine_interval(iv, op, c, true);
        let not_taken_iv = refine_interval(iv, op, c, false);

        // Taken edge (guard true) → label D. The octagon rides along
        // unchanged (the constant bound is already captured in the interval;
        // injecting it into the octagon would be redundant for projection).
        let mut taken_locals = ctx.locals.clone();
        taken_locals[local as usize] = AbstractValue::I32Interval(taken_iv);
        if let Some(l) = self.target(labels, depth) {
            l.record(&taken_locals, &ctx.octagon, &ctx.mem, &ctx.poly);
        }

        // Not-taken edge (guard false) → fall through.
        ctx.locals[local as usize] = AbstractValue::I32Interval(not_taken_iv);
        // FEAT-089: a guard whose TAKEN edge pins the local to `== 0`
        // (`i32.eqz; br_if` or `i32.const 0; i32.eq; br_if`) licenses
        // `local != 0` on this fall-through edge — the disequality the
        // interval lattice cannot hold (`refine_interval` returns `iv`
        // untouched for exactly this case). Carry it as a narrow predicate
        // fact for the div/rem trap check. The dual `Ne` shape needs no fact:
        // its fall-through pins the interval to `[0,0]` above.
        if matches!(op, GuardOp::Eq) && c == 0 {
            ctx.nonzero_locals.insert(local);
        }
        Some(next)
    }

    /// FEAT-016 slice-2b-ii relational guard refinement. If the ops at `pc`
    /// are `local.get A; local.get B; <signed cmp>; br_if D`, add the octagon
    /// difference constraint the comparison implies on each edge: the taken
    /// edge (guard true) reaches label `D`, the not-taken edge (guard false)
    /// falls through. Locals are NOT refined (neither operand is a constant —
    /// that is the constant peephole's job); only the relational octagon
    /// learns `A − B ≤ c`. Returns the pc just past the 4-op idiom, or `None`.
    /// Net operand-stack effect is zero (push A, push B, cmp pops 2/pushes 1,
    /// br_if pops 1), so the stack is left untouched.
    fn try_guard_brif_rel(
        &self,
        pc: usize,
        ctx: &mut FuncCtx,
        labels: &mut [Label],
    ) -> Option<usize> {
        if ctx.degraded {
            return None;
        }
        let ops = self.ops;
        let (a, b, op, depth, next) = match (ops.get(pc)?, ops.get(pc + 1)?, ops.get(pc + 2)?) {
            (Operator::LocalGet { local_index: a }, Operator::LocalGet { local_index: b }, cmp) => {
                match ops.get(pc + 3) {
                    Some(Operator::BrIf { relative_depth }) => {
                        (*a, *b, guard_op(cmp)?, *relative_depth, pc + 4)
                    }
                    _ => return None,
                }
            }
            _ => return None,
        };
        let dim = ctx.locals.len() as u32;
        if a == b || a >= dim || b >= dim {
            return None; // self-compare or out-of-range: nothing relational to learn
        }
        let taken_oct = refine_octagon_rel(&ctx.octagon, a, b, op, true);
        let not_taken_oct = refine_octagon_rel(&ctx.octagon, a, b, op, false);
        // FEAT-057: the polyhedra learn the same difference constraint on each
        // edge (guard refinement mirroring the octagon's — sound for the same
        // reason: the signed comparison is a fact about the locals' VALUES).
        let taken_poly = refine_poly_rel(&ctx.poly, dim, a, b, op, true);
        let not_taken_poly = refine_poly_rel(&ctx.poly, dim, a, b, op, false);
        // Taken edge (guard true) → label D (locals unchanged). `None` when
        // that edge exits the function; the not-taken refinement still applies.
        if let Some(l) = self.target(labels, depth) {
            l.record(&ctx.locals, &taken_oct, &ctx.mem, &taken_poly);
        }
        // Not-taken edge (guard false) → fall through.
        ctx.octagon = not_taken_oct;
        ctx.poly = not_taken_poly;
        Some(next)
    }

    /// Octagon relational transfer for the op at `pc` (FEAT-016 slice-2b-ii).
    /// Only `local.set` / `local.tee` change the relational state: they write
    /// a local, so the octagon must drop or re-derive that variable's
    /// constraints. The value stored is classified by a look-behind over the
    /// producer ops ([`classify_store`]); anything not recognised forgets the
    /// variable (the sound default — never retain a stale relation).
    fn octagon_transfer(&self, pc: usize, ctx: &mut FuncCtx) {
        if ctx.degraded {
            return;
        }
        let l = match &self.ops[pc] {
            Operator::LocalSet { local_index } | Operator::LocalTee { local_index } => *local_index,
            _ => return,
        };
        let dim = ctx.locals.len() as u32;
        if l >= dim {
            return;
        }
        let oct = &ctx.octagon;
        ctx.octagon = match classify_store(self.ops, pc) {
            StoreSrc::Const(c) => scry_octagon::assign_const(oct, l, c),
            StoreSrc::Copy(src) if src < dim => scry_octagon::assign_copy(oct, l, src),
            StoreSrc::AddConst(src, c) if src < dim => {
                scry_octagon::assign_add_const(oct, l, src, c)
            }
            _ => scry_octagon::forget(oct, l),
        };
    }

    /// FEAT-057 slice 2a: polyhedra transfer for the op at `pc`, run at the
    /// same sites as [`Self::octagon_transfer`]. Only `local.set`/`local.tee`
    /// change the linear state: the assigned variable is ALWAYS `project`ed
    /// (FM-forgotten) first — every branch below starts from a state with no
    /// stale constraint on it — and an assignment EQUALITY is then added only
    /// when it is sound.
    ///
    /// THE WRAP GATE — the soundness core of this slice. Over Wasm's WRAPPING
    /// i32 arithmetic, `z := x + y` justifies the linear fact `z = x + y` only
    /// on runs where the addition does not wrap. The no-wrap proof comes from
    /// the interval domain: [`scry_interval::i32_add`] / [`i32_sub`] return ⊤
    /// exactly when the result may leave i32 range, so a non-⊤ result over the
    /// operands' current intervals proves NO run reaching this pc wraps here.
    /// When no-wrap is NOT proven the projection above is the whole transfer —
    /// never an unguarded equality. Constants and copies involve no arithmetic
    /// and need no gate.
    ///
    /// Self-referencing assignments (`x := x + c`, or `z := x + y` with `z`
    /// aliasing an operand) only project: this method runs AFTER
    /// `interpret_op` has overwritten `ctx.locals[l]`, so the operand's
    /// PRE-assignment interval — which the wrap gate needs — is gone. A
    /// precision loss (the octagon still models `x := x + c`), never a
    /// soundness one. Operand intervals are read from `ctx.locals`, which the
    /// assignment left untouched for every non-aliased operand.
    fn poly_transfer(&self, pc: usize, ctx: &mut FuncCtx) {
        if ctx.degraded {
            return;
        }
        let l = match &self.ops[pc] {
            Operator::LocalSet { local_index } | Operator::LocalTee { local_index } => *local_index,
            _ => return,
        };
        let dim = ctx.locals.len() as u32;
        if l >= dim {
            return;
        }
        // Only a genuine I32Interval participates in the wrap gate: a
        // RegionPointer's offset interval is NOT the value's range, and using
        // it to prove no-wrap would be unsound.
        let iv = |v: u32| match ctx.locals.get(v as usize) {
            Some(AbstractValue::I32Interval(iv)) => Some(*iv),
            _ => None,
        };
        let forgotten = ctx.poly.project(l);
        ctx.poly = match classify_poly_store(self.ops, pc) {
            // `l := c` — no arithmetic, the equality is exact.
            PolyStoreSrc::Const(c) => poly_with_equality(forgotten, dim, &[(l, 1)], c),
            // `l := src` — a copy cannot wrap.
            PolyStoreSrc::Copy(src) if src < dim && src != l => {
                poly_with_equality(forgotten, dim, &[(l, 1), (src, -1)], 0)
            }
            // `l := src + c` — equality only under the interval no-wrap proof.
            PolyStoreSrc::AddConst(src, c) if src < dim && src != l => {
                let no_wrap = iv(src).is_some_and(|s| {
                    !interval_is_top(&scry_interval::i32_add(s, scry_interval::constant_i64(c)))
                });
                if no_wrap {
                    poly_with_equality(forgotten, dim, &[(l, 1), (src, -1)], c)
                } else {
                    forgotten
                }
            }
            // `l := a + b` — THE polyhedra case (a 3-variable equality no
            // octagon can express), equality only under the no-wrap proof.
            PolyStoreSrc::AddLocals(a, b) if a < dim && b < dim && a != l && b != l => {
                let no_wrap = match (iv(a), iv(b)) {
                    (Some(x), Some(y)) => !interval_is_top(&scry_interval::i32_add(x, y)),
                    _ => false,
                };
                if no_wrap {
                    poly_with_equality(forgotten, dim, &[(l, 1), (a, -1), (b, -1)], 0)
                } else {
                    forgotten
                }
            }
            // `l := a − b` — same gate through i32_sub.
            PolyStoreSrc::SubLocals(a, b) if a < dim && b < dim && a != l && b != l => {
                let no_wrap = match (iv(a), iv(b)) {
                    (Some(x), Some(y)) => !interval_is_top(&scry_interval::i32_sub(x, y)),
                    _ => false,
                };
                if no_wrap {
                    poly_with_equality(forgotten, dim, &[(l, 1), (a, -1), (b, 1)], 0)
                } else {
                    forgotten
                }
            }
            // Anything else (including self-referencing shapes): the
            // projection is the whole transfer — the sound default.
            _ => forgotten,
        };
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
            (Flow::Fall, Some(b)) => {
                ctx.locals = join_locals(&ctx.locals, &b.locals);
                ctx.octagon = scry_octagon::join(&ctx.octagon, &b.octagon);
                ctx.mem = ctx.mem.join(&b.mem);
                ctx.poly = ctx.poly.join(&b.poly);
            }
            (Flow::Fall, None) => {}
            (Flow::Diverged, Some(b)) => {
                ctx.locals = b.locals;
                ctx.octagon = b.octagon;
                ctx.mem = b.mem;
                ctx.poly = b.poly;
            }
            (Flow::Diverged, None) => {
                // Post-block unreachable (body always branched elsewhere).
                // Dead code follows; leave locals as a sound over-approx.
            }
        }
        // FEAT-089: non-zero facts never cross a region boundary outward. The
        // post-block state may be a JOIN with break edges whose paths did not
        // establish the fact (labels carry no facts), so the only sound merge
        // is to drop them all. Conservative for the pure fall-through case
        // too — a deliberate simplicity-over-precision trade: the invariant
        // "no fact survives an `end`" is auditable at a glance.
        ctx.nonzero_locals.clear();
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
        // FEAT-058: memory content rides the fixpoint in lockstep too — joined
        // at back-edges, widened at the header (segment-count cap ⇒ termination).
        let entry_mem = ctx.mem.clone();
        // FEAT-057: the polyhedra ride the fixpoint in lockstep as well —
        // joined at back-edges, widened at the header (the constraint set only
        // shrinks under scry_poly::widen, so the chain stabilises).
        let entry_poly = ctx.poly.clone();
        // Seed the entry octagon with the entry interval bounds (FEAT-016
        // slice-2b-ii): without this the octagon does not relate the loop
        // counter to its bound at entry (e.g. `i = 0`, `n = 10` ⇒ `i − n ≤
        // −10`), and the very first `entry ⊔ back-edge` join would discard the
        // body's `i − n ≤ 0` (join keeps the looser bound). Sound — injecting
        // true entry bounds only tightens.
        let entry_oct = inject_intervals(&ctx.octagon, &entry);
        let saved_stack = ctx.operand_stack.clone();
        // Snapshot the ENCLOSING labels' break-state. The widening/narrowing
        // passes below re-run the body many times with intermediate (often ⊤)
        // headers; each `br` to an outer label would otherwise accumulate those
        // throwaway states into the enclosing label and poison its exit join.
        // Only the final converged pass should contribute outer breaks, so we
        // restore this snapshot just before it.
        let saved_outer: Vec<Option<BreakState>> =
            labels.iter().map(|l| l.breaks.clone()).collect();
        let mut header = entry.clone();
        // FEAT-016 slice-2b-ii: the relational octagon rides the fixpoint in
        // LOCKSTEP with the interval locals — joined and widened at the same
        // points, and (crucially) NARROWED in the same phase, because octagon
        // widening drops a slowly-growing difference bound (e.g. `i − n`) to ⊤
        // exactly as interval widening drops a counter, and narrowing is what
        // re-derives it from the guard.
        let mut header_oct = entry_oct.clone();
        let mut header_mem = entry_mem.clone();
        let mut header_poly = entry_poly.clone();
        let mut exit: Option<(Vec<AbstractValue>, Octagon, Segmentation, Poly)> = None;
        let mut iter = 0u32;
        loop {
            ctx.locals = header.clone();
            ctx.octagon = header_oct.clone();
            ctx.mem = header_mem.clone();
            ctx.poly = header_poly.clone();
            ctx.operand_stack = saved_stack.clone();
            // FEAT-089: a loop pass starts from `entry ⊔ back-edges`, and a
            // back-edge must NEVER carry a non-zero fact into the next
            // iteration — nor may a pre-loop fact leak into the body (the
            // header covers back-edge states too). Cleared at EVERY pass
            // start (widening, narrowing, and final emission pass alike).
            ctx.nonzero_locals.clear();
            labels.push(Label { breaks: None });
            // Suppress point emission until the header has converged; the
            // final pass below emits the fixpoint state.
            let body_flow = self.seq(start, end, ctx, labels, false)?;
            let label = labels.pop().expect("pushed above");
            if body_flow == Flow::Fall {
                exit = Some(match exit.take() {
                    Some((el, eo, em, ep)) => (
                        join_locals(&el, &ctx.locals),
                        scry_octagon::join(&eo, &ctx.octagon),
                        em.join(&ctx.mem),
                        ep.join(&ctx.poly),
                    ),
                    None => (
                        ctx.locals.clone(),
                        ctx.octagon.clone(),
                        ctx.mem.clone(),
                        ctx.poly.clone(),
                    ),
                });
            }
            let (mut next, mut next_oct, mut next_mem, mut next_poly) = match &label.breaks {
                Some(b) => (
                    join_locals(&entry, &b.locals),
                    scry_octagon::join(&entry_oct, &b.octagon),
                    entry_mem.join(&b.mem),
                    entry_poly.join(&b.poly),
                ),
                None => (
                    entry.clone(),
                    entry_oct.clone(),
                    entry_mem.clone(),
                    entry_poly.clone(),
                ),
            };
            if iter >= LOOP_WIDEN_THRESHOLD {
                next = widen_locals(&header, &next, &self.widen_thresholds);
                next_oct = scry_octagon::widen(&header_oct, &next_oct);
                next_mem = header_mem.widen(&next_mem);
                next_poly = header_poly.widen(&next_poly);
            }
            if locals_leq(&next, &header)
                && scry_octagon::leq(&next_oct, &header_oct)
                && next_mem.leq(&header_mem)
                && next_poly.leq(&header_poly)
            {
                break;
            }
            header = next;
            header_oct = next_oct;
            header_mem = next_mem;
            header_poly = next_poly;
            iter += 1;
            if iter > LOOP_ITER_CAP {
                // Termination safety net: widen every local + relation to ⊤.
                header = header
                    .iter()
                    .map(|_| AbstractValue::I32Interval(domain::top()))
                    .collect();
                header_oct = scry_octagon::top(header.len() as u32);
                header_mem = scry_segment::top();
                header_poly = scry_poly::top(header.len() as u32);
                break;
            }
        }
        // ── Narrowing (FEAT-016 slice-2b-i + 2b-ii) ──────────────────
        // Widening may have overshot a bound to ⊤ (an interval counter, or a
        // relational difference bound). Re-apply the body and replace the
        // header's infinite bounds — interval AND octagon — with the recomputed
        // finite ones, descending to a tighter sound post-fixpoint.
        let mut narrow_iter = 0u32;
        loop {
            ctx.locals = header.clone();
            ctx.octagon = header_oct.clone();
            ctx.mem = header_mem.clone();
            ctx.poly = header_poly.clone();
            ctx.operand_stack = saved_stack.clone();
            // FEAT-089: a loop pass starts from `entry ⊔ back-edges`, and a
            // back-edge must NEVER carry a non-zero fact into the next
            // iteration — nor may a pre-loop fact leak into the body (the
            // header covers back-edge states too). Cleared at EVERY pass
            // start (widening, narrowing, and final emission pass alike).
            ctx.nonzero_locals.clear();
            labels.push(Label { breaks: None });
            let _ = self.seq(start, end, ctx, labels, false)?;
            let label = labels.pop().expect("pushed above");
            let (candidate, candidate_oct) = match &label.breaks {
                Some(b) => (
                    join_locals(&entry, &b.locals),
                    scry_octagon::join(&entry_oct, &b.octagon),
                ),
                None => (entry.clone(), entry_oct.clone()),
            };
            let narrowed = narrow_locals(&header, &candidate);
            let narrowed_oct = scry_octagon::narrow(&header_oct, &candidate_oct);
            if narrowed == header && narrowed_oct == header_oct {
                break;
            }
            header = narrowed;
            header_oct = narrowed_oct;
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
        ctx.octagon = header_oct.clone();
        ctx.mem = header_mem.clone();
        ctx.poly = header_poly.clone();
        ctx.operand_stack = saved_stack.clone();
        // FEAT-089: same clear as every other pass start (see above).
        ctx.nonzero_locals.clear();
        labels.push(Label { breaks: None });
        let final_flow = self.seq(start, end, ctx, labels, emit)?;
        let final_label = labels.pop().expect("pushed above");
        if final_flow == Flow::Fall {
            exit = Some(match exit.take() {
                Some((el, eo, em, ep)) => (
                    join_locals(&el, &ctx.locals),
                    scry_octagon::join(&eo, &ctx.octagon),
                    em.join(&ctx.mem),
                    ep.join(&ctx.poly),
                ),
                None => (
                    ctx.locals.clone(),
                    ctx.octagon.clone(),
                    ctx.mem.clone(),
                    ctx.poly.clone(),
                ),
            });
        }
        // Drop this loop's own back-edge breaks — they targeted this loop only
        // and already shaped `header`. Breaks to OUTER labels were recorded by
        // the final pass above (the intermediate passes' contributions were
        // wiped by the snapshot restore).
        let _ = final_label;
        // Post-loop state: fall-through-exit if any, else the fixpoint header
        // (sound: covers the otherwise-unreachable fall-through).
        let (post_locals, post_oct, post_mem, post_poly) =
            exit.unwrap_or((header, header_oct, header_mem, header_poly));
        ctx.locals = post_locals;
        ctx.octagon = post_oct;
        ctx.mem = post_mem;
        ctx.poly = post_poly;
        ctx.operand_stack = saved_stack;
        // FEAT-089: the post-loop state may join several exit paths; no
        // non-zero fact crosses the region boundary outward.
        ctx.nonzero_locals.clear();
        Ok(())
    }

    /// Sound fallback for a region we do not model precisely (`if`, non-empty
    /// block type, `br_table`-heavy bodies): slice-1 write-set havoc — widen
    /// exactly the written locals to ⊤, preserve the rest.
    fn havoc_region(&mut self, opener: usize, end: usize, ctx: &mut FuncCtx, emit: bool) {
        if matches!(self.ops[opener], Operator::If { .. }) {
            let _ = ctx.operand_stack.pop();
        }
        // FEAT-089: the region body is not interpreted, so any write inside it
        // is invisible to the per-op fact killers — drop EVERY non-zero fact,
        // not just the write-set's (over-approximate the invalidation).
        ctx.nonzero_locals.clear();
        let written = region_write_set(self.ops, opener + 1, end);
        // FEAT-040 / FEAT-043 / scry#121: an unmodelled control-flow region is
        // ALWAYS worth a gap. `havoc_region` does not interpret the body at all,
        // so the reason to record is that the region WAS NOT ANALYSED — not that
        // it happened to write a local.
        //
        // This used to be gated on `!written.is_empty() || region_has_call`. The
        // call half was added correctly (FEAT-043: a void call inside an `if`
        // must still record, or `resolved_stack_callees` silently under-counts),
        // but the gate as a whole let a typed region with an empty write set and
        // no call vanish with NO record of any kind. That is:
        //   * a hole in REQ-017's invariant — maximally conservative, and silent;
        //   * a one-line laundering vector, since wrapping a flagged expression
        //     in a typed block removed it from the report entirely;
        //   * a source of WRONG adjudicator verdicts, which read the resulting
        //     absence as `removed-with-code` while the code was still there.
        //
        // An empty write set makes a region CHEAPER TO HAVOC, not more analysed.
        ctx.gaps.push(Gap {
            func_index: self.func_index,
            pc: opener as u32,
            op: op_report_name(&self.ops[opener]),
            kind: GapKind::UnmodeledControlFlow,
        });
        for idx in &written {
            if let Some(slot) = ctx.locals.get_mut(*idx as usize) {
                *slot = AbstractValue::I32Interval(domain::top());
            }
            // The unmodelled region may assign these locals arbitrarily — drop
            // their octagon relations too (sound havoc), FEAT-016 slice-2b-ii.
            if (*idx as usize) < ctx.locals.len() {
                ctx.octagon = scry_octagon::forget(&ctx.octagon, *idx);
                // FEAT-057: project (FM-forget) the written local out of the
                // polyhedra — a linear fact about a value the unmodelled
                // region may have replaced is a false proof. Facts over
                // UNwritten locals soundly survive (calls cannot write Wasm
                // locals, and region_write_set catches every local.set/tee).
                ctx.poly = ctx.poly.project(*idx);
            }
        }
        // FEAT-058: havoc does NOT interpret the region body, so any store (or
        // call that writes shared linear memory) inside it is unmodelled — forget
        // all tracked memory content (sound: every later load falls back to ⊤).
        ctx.mem = scry_segment::top();
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
                // FEAT-023: havoc does NOT model the region's operand-stack
                // effect (a non-empty block type leaves result values our model
                // never simulated). `ctx.operand_stack` is therefore stale here,
                // so we emit an EMPTY stack — a vacuous, trivially-sound claim
                // ("no operand-stack info at this pc") rather than a
                // precise-looking-but-unsound one. Locals stay meaningful: they
                // were soundly widened to ⊤ above.
                operand_stack: Vec::new(),
                relational: snapshot_relational(&ctx.octagon),
                // havoc reset ctx.mem to ⊤ above, so this is empty (accurate).
                memory: snapshot_memory(&ctx.mem),
                linear: snapshot_linear(&ctx.poly),
            });
        }
    }
}

/// FEAT-042: the widening thresholds for a function — its integer constant
/// operands (the `i32.const` / `i64.const` immediates, where loop bounds and
/// array sizes live) plus `0`, deduped and sorted. The loop-header widening
/// snaps a runaway bound to the nearest enclosing threshold instead of ±∞.
fn collect_widen_thresholds(ops: &[Operator<'_>]) -> Vec<i64> {
    let mut ts: Vec<i64> = alloc::vec![0];
    for op in ops {
        match op {
            Operator::I32Const { value } => ts.push(*value as i64),
            Operator::I64Const { value } => ts.push(*value),
            _ => {}
        }
    }
    ts.sort_unstable();
    ts.dedup();
    ts
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
    emit_gaps: Option<&mut Vec<Gap>>,
    emit_trap_checks: Option<&mut Vec<TrapCheck>>,
) -> Result<Vec<AbstractValue>, AnalyzeError> {
    let mut ctx = FuncCtx::new(init_locals);
    let ops = &func.ops;
    let end_at = build_end_map(ops);
    let want_points = emit_points.is_some();
    let widen_thresholds = collect_widen_thresholds(ops);
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
        widen_thresholds,
    };
    let mut labels: Vec<Label> = Vec::new();
    interp.seq(0, ops.len(), &mut ctx, &mut labels, want_points)?;
    if let Some(out) = emit_points {
        out.extend(interp.points);
    }
    if let Some(g) = emit_gaps {
        g.append(&mut ctx.gaps);
    }
    if let Some(t) = emit_trap_checks {
        t.append(&mut ctx.trap_checks);
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
                // Direct call AND direct TAIL call (`return_call`): both transfer
                // to the target; a tail call does NOT tear down the caller's
                // shadow frame first, so the callee's frame is live on top of the
                // caller's — a regular call edge for the longest-path. (FEAT-043
                // clean-room: omitting return_call here under-counted the stack
                // AND missed tail-recursive cycles.)
                Operator::Call { function_index } | Operator::ReturnCall { function_index }
                    if *function_index >= import_func_count =>
                {
                    let d = (*function_index - import_func_count) as usize;
                    if d < defined_funcs.len() && !callees.contains(&d) {
                        callees.push(d);
                    }
                }
                Operator::CallIndirect { .. } | Operator::ReturnCallIndirect { .. } => {
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

/// FEAT-022 slice-1: the set of functions reachable from the module's entry
/// points, as sorted ABSOLUTE function indices. Roots are the exported
/// functions + the optional start function; the search follows the static
/// call graph (`build_static_call_graph` — direct calls plus every
/// over-approximated `call_indirect` target), so the result is a sound
/// SUPERSET of the concretely-reachable functions (REQ-011/SCRY-001): an edge
/// the analyzer over-approximates only ever ADDS a function, never drops a
/// reachable one. A consumer may soundly prune any function NOT in this set.
///
/// FEAT-039: `callers_fully_known` (the FEAT-036 funcref-escape predicate) is
/// true exactly when no funcref to a defined function can exist outside the
/// recorded call edges. When it is FALSE — an open world where a funcref may
/// have escaped to the host or an import — every address-taken function
/// (`address_taken_funcs`, absolute indices) is added as a reachability root,
/// because such a caller can dispatch any escaped funcref. This keeps the set a
/// sound superset; without it a function reachable only via, e.g., an exported
/// funcref table (with no in-module `call_indirect`) would be wrongly omitted.
fn compute_reachable_from_exports(
    static_callees: &[Vec<usize>],
    import_func_count: u32,
    exported_funcs: &[u32],
    start_func: Option<u32>,
    callers_fully_known: bool,
    address_taken_funcs: &[u32],
) -> Vec<u32> {
    let n = static_callees.len();
    let mut reachable_defined = alloc::vec![false; n];
    let mut work: Vec<usize> = Vec::new();
    let mut out: Vec<u32> = Vec::new();

    let seed = |abs: u32, work: &mut Vec<usize>, out: &mut Vec<u32>, vis: &mut [bool]| {
        if abs >= import_func_count {
            let d = (abs - import_func_count) as usize;
            if d < n && !vis[d] {
                vis[d] = true;
                work.push(d);
            }
        } else {
            // An exported/start IMPORT: reachable itself, reaches nothing in
            // the defined call graph. Record its absolute index directly.
            out.push(abs);
        }
    };
    for &abs in exported_funcs {
        seed(abs, &mut work, &mut out, &mut reachable_defined);
    }
    if let Some(s) = start_func {
        seed(s, &mut work, &mut out, &mut reachable_defined);
    }
    // FEAT-039: in an open world, any escaped funcref is host/import-dispatchable.
    if !callers_fully_known {
        for &abs in address_taken_funcs {
            seed(abs, &mut work, &mut out, &mut reachable_defined);
        }
    }
    // BFS/DFS over the over-approximated static call graph.
    while let Some(d) = work.pop() {
        for &c in &static_callees[d] {
            if c < n && !reachable_defined[c] {
                reachable_defined[c] = true;
                work.push(c);
            }
        }
    }
    for (d, &r) in reachable_defined.iter().enumerate() {
        if r {
            out.push(import_func_count + d as u32);
        }
    }
    out.sort_unstable();
    out.dedup();
    out
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

// ─────────────────────────────────────────────────────────────────────
// FEAT-021 slice-1: worst-case shadow-stack bound (DD-016).
//
// The shadow stack is the C-style stack Rust/LLVM keep in linear memory via
// a mutable i32 global (`__stack_pointer`). Each function's prologue subtracts
// a constant frame from it; the worst-case usage is the deepest weighted path
// through the call graph. We reuse the FEAT-006/007 call graph + Tarjan SCCs +
// reverse-topological order: per-function frames are summed callees-first, a
// recursion SCC is `Unbounded`, and any unrecognised frame / unresolved edge
// is `Unknown` — never zero (the soundness rule, DD-016 guardrail 1 & 2).
// ─────────────────────────────────────────────────────────────────────

/// Which global, if any, is the shadow-stack pointer.
#[derive(Clone, Copy)]
enum SpGlobal {
    /// The identified `__stack_pointer` (mutable i32; global 0 by LLVM
    /// convention, or the unique mutable i32 global).
    Index(u32),
    /// No mutable i32 global ⇒ the module has no linear-memory shadow stack ⇒
    /// every frame is genuinely 0 bytes (sound).
    NoShadowStack,
    /// Several mutable i32 globals and none is index 0 ⇒ we cannot reliably
    /// say which is the SP ⇒ every frame is `Unknown` (sound, imprecise).
    Ambiguous,
}

/// Pick the shadow-stack pointer global from the mutable i32 globals.
fn resolve_sp_global(mutable_i32_globals: &[u32]) -> SpGlobal {
    if mutable_i32_globals.is_empty() {
        SpGlobal::NoShadowStack
    } else if mutable_i32_globals.contains(&0) {
        SpGlobal::Index(0)
    } else if mutable_i32_globals.len() == 1 {
        SpGlobal::Index(mutable_i32_globals[0])
    } else {
        SpGlobal::Ambiguous
    }
}

/// Worst-case stack `+` (a frame plus its callees): any non-finite operand
/// makes the sum non-finite (`Unbounded` dominates `Unknown`).
fn sb_add(a: StackBound, b: StackBound) -> StackBound {
    match (a, b) {
        (StackBound::Unbounded, _) | (_, StackBound::Unbounded) => StackBound::Unbounded,
        (StackBound::Unknown, _) | (_, StackBound::Unknown) => StackBound::Unknown,
        (StackBound::Bytes(x), StackBound::Bytes(y)) => StackBound::Bytes(x.saturating_add(y)),
    }
}

/// Worst-case stack `max` (the deepest of several callee subtrees): same
/// non-finite domination as [`sb_add`].
fn sb_max(a: StackBound, b: StackBound) -> StackBound {
    match (a, b) {
        (StackBound::Unbounded, _) | (_, StackBound::Unbounded) => StackBound::Unbounded,
        (StackBound::Unknown, _) | (_, StackBound::Unknown) => StackBound::Unknown,
        (StackBound::Bytes(x), StackBound::Bytes(y)) => StackBound::Bytes(x.max(y)),
    }
}

/// Detect one function's shadow-stack frame by recognising the standard
/// prologue `global.get SP; i32.const F; i32.sub`. Returns `Bytes(F)` only for
/// a function whose SOLE stack-growing operation is that single constant
/// decrement; `Bytes(0)` for a leaf that never touches SP; and `Unknown` for
/// everything else — a non-constant / negative frame, MORE THAN ONE decrement
/// (stacked frames), ANY DYNAMIC decrement (`alloca`, even alongside a
/// recognised constant frame), or SP written with no recognised decrement.
///
/// Per DD-016 guardrail 1 this is conservatively the function's MAX live frame:
/// every SP decrement (constant OR dynamic) is counted, and any unrecognised /
/// extra one forces `Unknown` — so a frame is NEVER under-counted (the
/// soundness premise the Rocq `sb_postfixpoint` / `sframe` upper-bound relies
/// on). A `global.get SP` that is NOT followed by a subtract (e.g. the `add`
/// epilogue, or a read for comparison) does not grow the stack and is ignored.
fn detect_frame(ops: &[Operator<'_>], sp: SpGlobal) -> StackBound {
    let g = match sp {
        SpGlobal::NoShadowStack => return StackBound::Bytes(0),
        SpGlobal::Ambiguous => return StackBound::Unknown,
        SpGlobal::Index(g) => g,
    };
    // FEAT-043 soundness (clean-room #6): `detect_frame` is otherwise
    // control-flow-INSENSITIVE — it counts each prologue shape once. A
    // constant SP decrement that lives INSIDE a `loop` body and is NOT
    // restored within the same iteration leaks `frame` bytes on every
    // back-edge, so the live frame is `frame × trip_count` — unbounded from a
    // bound that cannot prove the trip count. Detect any loop whose body has a
    // NET-NEGATIVE constant SP delta (more subtracted than added within the
    // loop) and report `Unbounded`, never the single-iteration `frame`.
    if loop_leaks_stack(ops, g) {
        return StackBound::Unbounded;
    }
    let mut const_decr: u32 = 0;
    let mut dyn_decr: u32 = 0;
    let mut frame: u64 = 0;
    let mut bad = false;
    let mut sp_written = false;
    for (i, op) in ops.iter().enumerate() {
        if let Operator::GlobalSet { global_index } = op
            && *global_index == g
        {
            sp_written = true;
        }
        // A stack-GROWING op is `global.get SP` whose value flows into an
        // `i32.sub` (SP := SP - x). Recognise the constant-frame shape and,
        // crucially, ALSO any dynamic shape — an unrecognised subtrahend must
        // not be silently skipped.
        if let Operator::GlobalGet { global_index } = op
            && *global_index == g
        {
            match (ops.get(i + 1), ops.get(i + 2)) {
                // global.get SP; i32.const F; i32.sub  — the recognised frame.
                (Some(Operator::I32Const { value }), Some(Operator::I32Sub)) => {
                    const_decr = const_decr.saturating_add(1);
                    if *value >= 0 {
                        frame = *value as u64;
                    } else {
                        bad = true;
                    }
                }
                // global.get SP; i32.sub  — SP minus a stack value (dynamic).
                (Some(Operator::I32Sub), _) => dyn_decr = dyn_decr.saturating_add(1),
                // global.get SP; <non-const>; i32.sub  — dynamic alloca.
                (_, Some(Operator::I32Sub)) => dyn_decr = dyn_decr.saturating_add(1),
                _ => {}
            }
        }
    }
    if bad || const_decr > 1 || dyn_decr > 0 {
        StackBound::Unknown
    } else if const_decr == 1 {
        StackBound::Bytes(frame)
    } else if sp_written {
        StackBound::Unknown
    } else {
        StackBound::Bytes(0)
    }
}

/// FEAT-043 soundness (clean-room #6): true if ANY `loop` body has a
/// net-negative CONSTANT shadow-stack-pointer delta — i.e. one iteration
/// subtracts more from SP (`global.get g; i32.const F; i32.sub`) than it adds
/// back (`global.get g; i32.const F; i32.add`). Such a loop drives SP down on
/// every back-edge, so the worst-case live frame grows with the (statically
/// unknown) trip count and is unbounded. Nested loops are covered because an
/// inner decrement also falls inside the outer loop's range, and an inner leak
/// is itself flagged at the inner loop. Dynamic (non-constant) SP writes are
/// handled by the caller's `dyn_decr`/`bad` paths; here we only need the
/// constant arithmetic, since only that path can otherwise yield a finite
/// `Bytes(frame)`.
fn loop_leaks_stack(ops: &[Operator<'_>], g: u32) -> bool {
    let end_map = build_end_map(ops);
    for (opener, op) in ops.iter().enumerate() {
        if !matches!(op, Operator::Loop { .. }) {
            continue;
        }
        let Some(end) = end_map[opener] else { continue };
        let mut delta: i64 = 0;
        for k in (opener + 1)..end {
            if !matches!(ops.get(k), Some(Operator::GlobalGet { global_index }) if *global_index == g)
            {
                continue;
            }
            if let (Some(Operator::I32Const { value }), Some(kind)) =
                (ops.get(k + 1), ops.get(k + 2))
                && *value >= 0
            {
                match kind {
                    Operator::I32Sub => delta -= *value as i64,
                    Operator::I32Add => delta += *value as i64,
                    _ => {}
                }
            }
        }
        if delta < 0 {
            return true;
        }
    }
    false
}

/// Compute the module's worst-case shadow-stack usage (FEAT-021 slice-1):
/// per-function frame, then `max_stack(f) = frame(f) + max over callees`,
/// folded callees-first over the call-graph reverse-topological order;
/// recursion SCCs are `Unbounded`. The overall bound is the max over all
/// functions (any may be an entry point — sound).
/// FEAT-043 (DD-016 slice-3): the per-defined-function callee set used to WEIGHT
/// the worst-case shadow-stack longest-path — tightened to the RESOLVED
/// `call_indirect` target set (FEAT-006's index-interval resolution) instead of
/// the whole table, for functions scry interpreted COMPLETELY (no FEAT-040 gap).
///
/// Soundness: a gap-free function was fully interpreted, so every call it makes
/// is in `call_graph` (havoc_region records a gap whenever it skips a region
/// containing a call — FEAT-040, so the no-gap ⟹ complete-call_graph invariant
/// holds), and each edge's `resolved_targets` is a sound superset of the
/// MATERIALIZED-table targets — equal to the whole-table set when the index is
/// unconstrained. A function WITH a gap (it degraded, or a control region with a
/// call/write was havocked) falls back to the conservative whole-table
/// `static_callees`. Recursion detection + the topo order stay on
/// `static_callees` (conservative) — this only tightens the WEIGHTING.
///
/// KNOWN LIMITATION (pre-existing, shared with `static_callees`/reachability,
/// NOT introduced here): scry's static table model (`FuncTable.entries`) holds
/// only ACTIVE-segment functions, so a `call_indirect` against a table populated
/// by a passive/declared element segment under-reports its targets in BOTH
/// graphs — a FEAT-036-class gap tracked separately. FEAT-043 is no less sound
/// than the prior whole-table weighting on that case.
fn resolved_stack_callees(
    n: usize,
    static_callees: &[Vec<usize>],
    call_graph: &[CallEdge],
    gaps: &[Gap],
    import_func_count: u32,
) -> Vec<Vec<usize>> {
    let to_defined = |abs: u32| -> Option<usize> {
        if abs >= import_func_count {
            let d = (abs - import_func_count) as usize;
            (d < n).then_some(d)
        } else {
            None // imports are out of the (guest) shadow-stack graph
        }
    };
    let mut gapped = alloc::vec![false; n];
    for g in gaps {
        if let Some(d) = to_defined(g.func_index) {
            gapped[d] = true;
        }
    }
    let mut resolved: Vec<alloc::collections::BTreeSet<usize>> =
        alloc::vec![alloc::collections::BTreeSet::new(); n];
    for e in call_graph {
        let Some(f) = to_defined(e.caller_func) else {
            continue;
        };
        if gapped[f] {
            continue;
        }
        for &t in &e.resolved_targets {
            if let Some(d) = to_defined(t) {
                resolved[f].insert(d);
            }
        }
    }
    (0..n)
        .map(|f| {
            if gapped[f] {
                static_callees.get(f).cloned().unwrap_or_default()
            } else {
                resolved[f].iter().copied().collect()
            }
        })
        .collect()
}

fn compute_stack_usage(
    defined_funcs: &[DefinedFunc<'_>],
    stack_callees: &[Vec<usize>],
    reverse_topo: &[usize],
    recursive_flags: &[bool],
    sp: SpGlobal,
    table0_contents_known: bool,
) -> StackUsage {
    let n = defined_funcs.len();
    let frames: Vec<StackBound> = defined_funcs
        .iter()
        .map(|f| detect_frame(&f.ops, sp))
        .collect();
    // FEAT-043 soundness: a function whose indirect dispatch scry CANNOT
    // ENUMERATE calls a target neither the resolved nor the whole-table graph
    // covers, so its stack contribution is UNKNOWN — not a false finite bound:
    //   * `call_ref` / `return_call_ref` — an arbitrary funcref;
    //   * `call_indirect` / `return_call_indirect` against a table scry does not
    //     model (`table_index != 0`), or against table 0 whose contents are not
    //     fully known (passive/declared elem, non-constant offsets) — then
    //     `resolve_range` under-reports and the whole-table fallback is empty.
    // A `call_indirect` against a FULLY-KNOWN table 0 is enumerable (resolved /
    // whole-table) and stays finite. (Clean-room: multi-table + passive-elem.)
    let has_unresolvable_call: Vec<bool> = defined_funcs
        .iter()
        .map(|f| {
            f.ops.iter().any(|op| match op {
                Operator::CallRef { .. } | Operator::ReturnCallRef { .. } => true,
                Operator::CallIndirect { table_index, .. }
                | Operator::ReturnCallIndirect { table_index, .. } => {
                    *table_index != 0 || !table0_contents_known
                }
                _ => false,
            })
        })
        .collect();
    let mut max_stack: Vec<StackBound> = alloc::vec![StackBound::Bytes(0); n];
    for &f in reverse_topo {
        if f >= n {
            continue;
        }
        if recursive_flags[f] {
            max_stack[f] = StackBound::Unbounded;
            continue;
        }
        if has_unresolvable_call[f] {
            max_stack[f] = StackBound::Unknown;
            continue;
        }
        let mut callee = StackBound::Bytes(0);
        for &c in &stack_callees[f] {
            if c < n {
                callee = sb_max(callee, max_stack[c]);
            }
        }
        max_stack[f] = sb_add(frames[f], callee);
    }
    let functions: Vec<FunctionStack> = (0..n)
        .map(|i| FunctionStack {
            func_index: defined_funcs[i].abs_index,
            frame: frames[i],
            max_stack: max_stack[i],
        })
        .collect();
    let overall = max_stack
        .iter()
        .fold(StackBound::Bytes(0), |acc, &b| sb_max(acc, b));
    let sp_global = match sp {
        SpGlobal::Index(g) => Some(g),
        _ => None,
    };
    StackUsage {
        sp_global,
        functions,
        max_stack_bytes: overall,
    }
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
    divisor_from_nonzero_local: bool,
) -> Result<StepOutcome, AnalyzeError> {
    let default_region = module_ctx.default_region;
    if ctx.degraded {
        // Once degraded, we still need to scan through to keep the
        // operator iterator advancing — but we don't update state.
        // FEAT-045 (AC: "never silently dropped"): a div/rem reached in a
        // degraded state still gets a verdict — necessarily PotentialTrap,
        // since the operand intervals are no longer tracked (we cannot prove
        // safety). This keeps every reached div/rem classified even after an
        // unsupported op upstream scrubbed the function.
        if let Some((name, _w, is_div_s)) = div_op_info(op) {
            ctx.trap_checks.push(TrapCheck {
                func_index,
                pc,
                op: name.into(),
                kind: TrapKind::DivByZero,
                verdict: TrapVerdict::PotentialTrap,
            });
            if is_div_s {
                ctx.trap_checks.push(TrapCheck {
                    func_index,
                    pc,
                    op: name.into(),
                    kind: TrapKind::SignedOverflow,
                    verdict: TrapVerdict::PotentialTrap,
                });
            }
        } else if is_memory_access(op) {
            // FEAT-046: a memory access reached in a degraded state cannot be
            // proven in-bounds — classify PotentialTrap, never omit it.
            ctx.trap_checks.push(TrapCheck {
                func_index,
                pc,
                op: op_report_name(op),
                kind: TrapKind::OutOfBounds,
                verdict: TrapVerdict::PotentialTrap,
            });
        }
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
            // FEAT-089: a write kills the local's non-zero fact — a fact that
            // survives a write is a false proof.
            ctx.nonzero_locals.remove(local_index);
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
            // FEAT-089: a tee is a write exactly like a set.
            ctx.nonzero_locals.remove(local_index);
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
            // FEAT-089: clear ALL non-zero facts across a call. Wasm locals
            // are callee-inaccessible, so this is conservative rather than
            // semantically forced — but over-approximating invalidation is
            // sound and under-approximating it is a false proof (AC3).
            ctx.nonzero_locals.clear();
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
            // FEAT-089: same conservative clear as for `call` above.
            ctx.nonzero_locals.clear();
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
        Operator::MemorySize { mem, .. } => {
            // FEAT-038: `memory.size` returns the current size in PAGES. Memory
            // never shrinks, so size ∈ [initial, max]; the exact constant
            // `initial` only for a provably-fixed module-private memory. We
            // model precisely ONLY memory index 0 of a single-memory module
            // (scry captures only index 0); any other memidx, or a multi-memory
            // module, is ⊤ (sound). 64-bit memory caps at 2^48 pages and
            // returns an i64. Modelled WITHOUT degrading the function.
            let value = mem_size_value(module_ctx, *mem);
            ctx.operand_stack.push(value);
        }
        Operator::MemoryGrow { mem, .. } => {
            // FEAT-038: `memory.grow(delta)` pops the requested page delta and
            // pushes the PREVIOUS size on success or -1 on failure — so the
            // result is in `[-1, max]`. Does NOT degrade locals (a grow mutates
            // linear memory, not locals). ⊤ for an unmodelled memidx/memory.
            let _ = ctx.operand_stack.pop();
            let value = if *mem == 0 && module_ctx.memory_count == 1 {
                let hi = mem_page_ceiling(module_ctx);
                if module_ctx.memory_is_64 {
                    AbstractValue::I64Interval(Interval { lo: -1, hi })
                } else {
                    AbstractValue::I32Interval(Interval { lo: -1, hi })
                }
            } else {
                AbstractValue::Unknown
            };
            ctx.operand_stack.push(value);
        }
        Operator::GlobalGet { .. } => {
            // FEAT-043: globals are not tracked in the interval domain, so a
            // read yields ⊤ (sound). Crucially this does NOT degrade the
            // function — previously `global.get` fell to the `other` fallback
            // and scrubbed every local to ⊤, so any function with a stack
            // prologue (which reads the SP global) lost all its analysis AND its
            // `call_indirect` index resolution. Modelling it as a ⊤-push keeps
            // the rest of the function analyzed.
            ctx.operand_stack.push(AbstractValue::Unknown);
        }
        Operator::GlobalSet { .. } => {
            // Writing a global consumes one operand and changes only that
            // (untracked) global — locals/stack are unaffected (sound).
            let _ = ctx.operand_stack.pop();
        }
        // FEAT-084 (scry#126): i32 bitwise family, interpreted through the
        // PROVEN known-bits × congruence domain (scry-sai-bits, FEAT-037,
        // BitsCongruence.v) — interval → bits → transfer → interval. The
        // headline: `x & M` with `M` a non-negative constant bounds a masked
        // address to `[0, M]`, making the bounds-check idiom provable. This
        // ALSO stops `i32.and` (433 fallbacks in avrabe's 468-module corpus)
        // from scrubbing the whole function to ⊤. A sign-bit mask, a variable
        // shift count, or any shape outside the two sound interval→bits
        // conversions falls back to ⊤ for the RESULT only — never a false
        // bound, never a function-wide degrade.
        // NOT modelled here (still the unsupported-op fallback): the i64
        // bitwise family, `i32.shr_s`, and `rotl`/`rotr`.
        Operator::I32And => {
            i32_bitop(ctx, func_index, pc, |a, b| a.and(b, 32))?;
        }
        Operator::I32Or => {
            i32_bitop(ctx, func_index, pc, |a, b| a.or(b, 32))?;
        }
        Operator::I32Xor => {
            i32_bitop(ctx, func_index, pc, |a, b| a.xor(b, 32))?;
        }
        Operator::I32Shl => {
            i32_shiftop(ctx, func_index, pc, |a, s| a.shl(s, 32))?;
        }
        Operator::I32ShrU => {
            i32_shiftop(ctx, func_index, pc, |a, s| a.shr_u(s, 32))?;
        }
        // FEAT-045: division / remainder — classify the runtime trap from the
        // operand intervals, then push ⊤ for the result. Modelling them here
        // (instead of the `other` fallback) ALSO stops a div/rem from degrading
        // the whole function to ⊤.
        Operator::I32DivS
        | Operator::I32DivU
        | Operator::I32RemS
        | Operator::I32RemU
        | Operator::I64DivS
        | Operator::I64DivU
        | Operator::I64RemS
        | Operator::I64RemU => {
            let (name, width, is_div_s) = div_op_info(op).expect("div op");
            classify_div_trap(
                ctx,
                func_index,
                pc,
                name,
                width,
                is_div_s,
                divisor_from_nonzero_local,
            );
        }
        other => {
            // Anything outside the supported set: emit a fallback
            // diagnostic, scrub state to top to preserve soundness
            // (REQ-001), and continue. Control flow (`If` / `Loop` /
            // `Br*`) still land here; FEAT-005 lifted the canonical
            // memory ops, FEAT-006 lifted `call` / `call_indirect`,
            // FEAT-038 lifted `memory.size` / `memory.grow`.
            if emit_diagnostics {
                diagnostics.push(Diagnostic {
                    severity: DiagnosticSeverity::UnsoundnessFallback,
                    func_index,
                    pc,
                    message: format!(
                        // scry#126: `op_report_name`, NOT `op_name`. The latter
                        // returns the literal "<unsupported>" for anything
                        // outside its small hardcoded list, which made the
                        // LARGEST bucket of fallbacks in a real-world corpus
                        // (579 of them) name nothing at all. The operator is
                        // known here, the Debug-variant fallback already
                        // existed, and the GAP record was already using it —
                        // so the two surfaces disagreed about the same event.
                        "unsupported operator at v0.2 AC#1: {} — locals degraded to top",
                        op_report_name(other)
                    ),
                });
            }
            // FEAT-046: an unmodelled memory access (narrow/float width) still
            // gets a trap verdict — it cannot be proven in-bounds here, so it is
            // PotentialTrap. Recorded before the scrub so it is never dropped.
            if is_memory_access(other) {
                ctx.trap_checks.push(TrapCheck {
                    func_index,
                    pc,
                    op: op_report_name(other),
                    kind: TrapKind::OutOfBounds,
                    verdict: TrapVerdict::PotentialTrap,
                });
            }
            // FEAT-040: scrub_to_top records the gap (the function degrades to
            // ⊤ here). The `degraded` early-return means this fires once per
            // function — at the first unsupported op, the give-up point.
            ctx.scrub_to_top(Gap {
                func_index,
                pc,
                op: op_report_name(other),
                kind: GapKind::UnsupportedOp,
            });
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

/// FEAT-084 (scry#126): sound [`BitsCong`] approximation of an i32 interval
/// (signed i64 reading, the encoding `Interval` uses for i32 values).
///
/// Only two shapes yield information; everything else is ⊤ (sound):
/// * a singleton in i32 range → the exact constant (bit pattern of the i32);
/// * a non-negative interval `[lo, hi]` with `hi ≤ i32::MAX` → every value's
///   bits at or above `bit_len(hi)` are known-0 (`0 ≤ x ≤ hi` unsigned).
///
/// An interval containing negatives is ⊤: its members' unsigned readings
/// straddle the 2^31 boundary, so no bit is common. This is the
/// interval→known-bits half of the FEAT-037 reduced product, applied at the
/// operand level (BitsCongruence.v mechanizes the domain's own transfers).
fn bits_from_i32_interval(iv: Interval) -> BitsCong {
    if scry_interval::is_bot(iv) {
        return BitsCong::bottom();
    }
    if iv.lo == iv.hi && iv.lo >= i32::MIN as i64 && iv.hi <= i32::MAX as i64 {
        return BitsCong::constant(iv.lo as i32 as u32 as u64, 32);
    }
    if iv.lo >= 0 && iv.hi <= i32::MAX as i64 {
        // hi > 0 here (hi == 0 with lo ≥ 0 is the singleton case above).
        let bit_len = 64 - (iv.hi as u64).leading_zeros();
        let zeros = scry_bits::width_mask(32) & !((1u64 << bit_len) - 1);
        return BitsCong {
            kb: scry_bits::KnownBits::new(zeros, 0, 32),
            cong: Cong::top(),
        }
        .reduce(32);
    }
    BitsCong::top()
}

/// FEAT-084: sound i32 interval (signed reading) from a [`BitsCong`]'s
/// unsigned range `[umin, umax]` at width 32.
///
/// * `umax ≤ i32::MAX` — every member is non-negative in the signed reading
///   and the unsigned order agrees with the signed one: `[umin, umax]`.
/// * `umin ≥ 2^31` — every member is negative; `u ↦ u − 2^32` is monotone on
///   the range, so `[umin − 2^32, umax − 2^32]`.
/// * straddling 2^31 — the signed reading is not an interval of the unsigned
///   one; give up (⊤). A sign-bit mask (e.g. `x & 0x8000_0FFF`) lands here,
///   which is exactly the "negative mask must not bound" soundness case.
fn i32_interval_from_bits(bc: &BitsCong) -> Interval {
    if bc.is_bottom() {
        // Unreachable state: mirror the interval transfers, which propagate ⊥.
        return scry_interval::bottom();
    }
    let umin = bc.umin(32);
    let umax = bc.umax(32);
    if umax <= i32::MAX as u64 {
        Interval {
            lo: umin as i64,
            hi: umax as i64,
        }
    } else if umin > i32::MAX as u64 {
        Interval {
            lo: (umin as u32 as i32) as i64,
            hi: (umax as u32 as i32) as i64,
        }
    } else {
        domain::top()
    }
}

/// FEAT-084: interpret an i32 bitwise binop (`and`/`or`/`xor`) by round-trip
/// through the PROVEN known-bits × congruence domain (scry-sai-bits,
/// BitsCongruence.v): interval → BitsCong (sound approximation), the domain's
/// own transfer, BitsCong → interval (sound projection). The headline case —
/// `x & M` with `M` a non-negative constant — comes out as `[0, M]`, tight
/// enough for the in-bounds decision on a masked address.
///
/// These operators write no locals and no memory, so the octagon and the
/// FEAT-058 memory domain are untouched (the octagon's `classify_store`
/// treats a bitwise producer as `Other` ⇒ `forget`, its sound default).
/// A non-interval operand pushes ⊤ WITHOUT degrading the function — pop 2 /
/// push ⊤ is a complete model of a pure binop.
fn i32_bitop(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    f: fn(&BitsCong, &BitsCong) -> BitsCong,
) -> Result<(), AnalyzeError> {
    let b = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: i32 bitop with empty stack"
        ))
    })?;
    let a = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: i32 bitop with single operand"
        ))
    })?;
    let result = match (as_i32_interval(&a), as_i32_interval(&b)) {
        (Some(ai), Some(bi)) => {
            i32_interval_from_bits(&f(&bits_from_i32_interval(ai), &bits_from_i32_interval(bi)))
        }
        _ => domain::top(),
    };
    ctx.operand_stack.push(AbstractValue::I32Interval(result));
    Ok(())
}

/// FEAT-084: interpret an i32 shift (`shl`/`shr_u`) with a CONSTANT count via
/// the bits domain. Wasm takes the count mod 32. A non-constant count (or a
/// non-interval operand) pushes ⊤ without degrading — count 0 makes the
/// result equal the unbounded input, so nothing tighter is sound.
fn i32_shiftop(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    f: fn(&BitsCong, u32) -> BitsCong,
) -> Result<(), AnalyzeError> {
    let count = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: i32 shift with empty stack"
        ))
    })?;
    let value = ctx.operand_stack.pop().ok_or_else(|| {
        AnalyzeError::Internal(format!(
            "func {func_index} pc {pc}: i32 shift with single operand"
        ))
    })?;
    let result = match (as_i32_interval(&value), as_i32_interval(&count)) {
        (Some(vi), Some(ci))
            if ci.lo == ci.hi && ci.lo >= i32::MIN as i64 && ci.hi <= i32::MAX as i64 =>
        {
            let s = (ci.lo as i32 as u32) % 32;
            i32_interval_from_bits(&f(&bits_from_i32_interval(vi), s))
        }
        _ => domain::top(),
    };
    ctx.operand_stack.push(AbstractValue::I32Interval(result));
    Ok(())
}

/// FEAT-045: `(op-name, width, is-signed-division)` for the eight trapping
/// div/rem operators, else `None`. `is_div_s` is true only for `div_s` (the
/// ops that trap on `INT_MIN/-1`); `rem_s` is false (it does not trap there).
fn div_op_info(op: &Operator<'_>) -> Option<(&'static str, u32, bool)> {
    Some(match op {
        Operator::I32DivS => ("i32.div_s", 32, true),
        Operator::I32DivU => ("i32.div_u", 32, false),
        Operator::I32RemS => ("i32.rem_s", 32, false),
        Operator::I32RemU => ("i32.rem_u", 32, false),
        Operator::I64DivS => ("i64.div_s", 64, true),
        Operator::I64DivU => ("i64.div_u", 64, false),
        Operator::I64RemS => ("i64.rem_s", 64, false),
        Operator::I64RemU => ("i64.rem_u", 64, false),
        _ => return None,
    })
}

/// FEAT-046: true if `op` is a linear-memory load or store (any width). Used to
/// give a trap verdict to memory ops the interval interpreter does NOT model
/// precisely (narrow/float widths, or any access reached while the function is
/// already degraded) — they cannot be proven in-bounds, so they are classified
/// `OutOfBounds`/`PotentialTrap`, never silently dropped.
fn is_memory_access(op: &Operator<'_>) -> bool {
    matches!(
        op,
        Operator::I32Load { .. }
            | Operator::I64Load { .. }
            | Operator::F32Load { .. }
            | Operator::F64Load { .. }
            | Operator::I32Load8S { .. }
            | Operator::I32Load8U { .. }
            | Operator::I32Load16S { .. }
            | Operator::I32Load16U { .. }
            | Operator::I64Load8S { .. }
            | Operator::I64Load8U { .. }
            | Operator::I64Load16S { .. }
            | Operator::I64Load16U { .. }
            | Operator::I64Load32S { .. }
            | Operator::I64Load32U { .. }
            | Operator::I32Store { .. }
            | Operator::I64Store { .. }
            | Operator::F32Store { .. }
            | Operator::F64Store { .. }
            | Operator::I32Store8 { .. }
            | Operator::I32Store16 { .. }
            | Operator::I64Store8 { .. }
            | Operator::I64Store16 { .. }
            | Operator::I64Store32 { .. }
    )
}

/// FEAT-045: classify the runtime trap(s) of a division/remainder operator
/// from the operand intervals, record the verdict(s) on `ctx.trap_checks`, and
/// push a ⊤ result. Wasm operand order: the divisor is on top of the stack, the
/// dividend below it.
///
/// SOUNDNESS: `ProvenSafe` is emitted only when the interval domain proves the
/// trap cannot happen — div-by-zero is safe iff the divisor interval excludes
/// `0`; signed-division overflow (`INT_MIN / -1`, only `div_s`) is safe iff the
/// dividend excludes `INT_MIN` OR the divisor excludes `-1`. An unknown (⊤)
/// operand excludes nothing, so it falls to `PotentialTrap` — the sound
/// default. Remainder ops never trap on overflow, so `is_div_s` is false for
/// them and no `SignedOverflow` verdict is produced.
///
/// FEAT-089: `divisor_from_nonzero_local` is the caller's (i.e. [`Interp::seq`]'s)
/// look-behind — true iff the op immediately before this div is `local.get L`
/// with `L ∈ ctx.nonzero_locals`, in which case the value on top of the stack
/// IS local `L`'s current value and is known non-zero even though its interval
/// carries no hole. It clears ONLY the div-by-zero obligation, and only for
/// the 32-bit ops (the fact is established by an i32 guard; a valid module
/// cannot feed an i32 local to an i64 div, but the width gate makes the claim
/// independent of validation). It is deliberately NOT consulted for the
/// signed-overflow obligation: `!= 0` excludes neither `INT_MIN` nor `-1`.
fn classify_div_trap(
    ctx: &mut FuncCtx,
    func_index: u32,
    pc: u32,
    op_name: &str,
    width: u32,
    is_div_s: bool,
    divisor_from_nonzero_local: bool,
) {
    // Pop divisor (top) then dividend (below). Defensive on a short stack:
    // a missing operand is treated as ⊤ (→ PotentialTrap).
    let divisor = ctx.operand_stack.pop();
    let dividend = ctx.operand_stack.pop();
    let div_iv = div_operand_interval(divisor.as_ref(), width);
    let dvd_iv = div_operand_interval(dividend.as_ref(), width);

    let dbz = if interval_excludes(div_iv, 0) || (divisor_from_nonzero_local && width == 32) {
        TrapVerdict::ProvenSafe
    } else {
        TrapVerdict::PotentialTrap
    };
    ctx.trap_checks.push(TrapCheck {
        func_index,
        pc,
        op: op_name.into(),
        kind: TrapKind::DivByZero,
        verdict: dbz,
    });

    if is_div_s {
        let int_min = if width == 32 {
            i32::MIN as i64
        } else {
            i64::MIN
        };
        let safe = interval_excludes(dvd_iv, int_min) || interval_excludes(div_iv, -1);
        ctx.trap_checks.push(TrapCheck {
            func_index,
            pc,
            op: op_name.into(),
            kind: TrapKind::SignedOverflow,
            verdict: if safe {
                TrapVerdict::ProvenSafe
            } else {
                TrapVerdict::PotentialTrap
            },
        });
    }

    // The quotient/remainder value is not interval-tracked: push ⊤ of the
    // op's width. Crucially this does NOT degrade the function.
    let result = if width == 32 {
        AbstractValue::I32Interval(domain::top())
    } else {
        AbstractValue::I64Interval(domain::top())
    };
    ctx.operand_stack.push(result);
}

/// The interval of a div/rem operand of the given width, or ⊤ when the operand
/// is absent or not an interval of that width (so it excludes no value).
fn div_operand_interval(v: Option<&AbstractValue>, width: u32) -> Interval {
    match v {
        Some(AbstractValue::I32Interval(iv)) if width == 32 => *iv,
        Some(AbstractValue::I64Interval(iv)) if width == 64 => *iv,
        _ => domain::top(),
    }
}

/// True iff the interval provably does not contain `val` (`lo > val ∨ hi < val`).
/// A ⊤ interval excludes nothing; a bottom (empty/dead) interval excludes
/// everything — both sound for the trap verdict.
#[inline]
fn interval_excludes(iv: Interval, val: i64) -> bool {
    iv.lo > val || iv.hi < val
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
        // FEAT-046: a non-i32-shaped address cannot be proven in-bounds.
        ctx.trap_checks.push(TrapCheck {
            func_index,
            pc,
            op: op_label.to_string(),
            kind: TrapKind::OutOfBounds,
            verdict: TrapVerdict::PotentialTrap,
        });
        ctx.scrub_to_top(Gap {
            func_index,
            pc,
            op: op_label.to_string(),
            kind: GapKind::UnmodeledMemoryAddress,
        });
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

    // FEAT-046: surface the OOB verdict. `region_in_bounds` is sound — true only
    // when `addr ≥ 0` and `addr_hi + width ≤ size_bytes`, where `size_bytes` is
    // the memory's GUARANTEED size (initial pages; memory only grows), so a
    // proven-in-bounds access can never trap on any run.
    ctx.trap_checks.push(TrapCheck {
        func_index,
        pc,
        op: op_label.to_string(),
        kind: TrapKind::OutOfBounds,
        verdict: if in_bounds {
            TrapVerdict::ProvenSafe
        } else {
            TrapVerdict::PotentialTrap
        },
    });

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

    // FEAT-058: for a SINGLETON, in-bounds i32 (4-byte) address, return the
    // tracked segment content — the store→load round-trip that lifts the ⊤
    // cliff. Any other case (non-singleton address, i64/wider width, or an
    // out-of-bounds address that may not have been written) stays ⊤, exactly as
    // before (the i32-content scope; type-punning stays sound because every
    // store invalidates the overlapping byte window — see handle_memory_store).
    let loaded = match pushed_kind {
        MemValKind::I32 if in_bounds && width == 4 && effective.lo == effective.hi => {
            AbstractValue::I32Interval(ctx.mem.load(effective.lo))
        }
        MemValKind::I32 => AbstractValue::I32Interval(domain::top()),
        MemValKind::I64 => AbstractValue::I64Interval(domain::top()),
    };
    ctx.operand_stack.push(loaded);
    Ok(())
}

/// FEAT-058: the widest linear-memory access scry models (i64/f64 = 8 bytes).
/// A store at base `a` width `w` invalidates the byte window
/// `[a − (MEM_MAX_ACCESS_WIDTH − 1), a + w)` so that no tracked cell of ANY
/// width whose bytes overlap the store can survive it — the invariant that
/// keeps the address-keyed content model sound under type-punning.
const MEM_MAX_ACCESS_WIDTH: i64 = 8;

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
    let value_v = ctx.operand_stack.pop().ok_or_else(|| {
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
        // FEAT-046: a non-i32-shaped address cannot be proven in-bounds.
        ctx.trap_checks.push(TrapCheck {
            func_index,
            pc,
            op: op_label.to_string(),
            kind: TrapKind::OutOfBounds,
            verdict: TrapVerdict::PotentialTrap,
        });
        ctx.scrub_to_top(Gap {
            func_index,
            pc,
            op: op_label.to_string(),
            kind: GapKind::UnmodeledMemoryAddress,
        });
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

    // FEAT-046: surface the OOB verdict. `region_in_bounds` is sound — true only
    // when `addr ≥ 0` and `addr_hi + width ≤ size_bytes`, where `size_bytes` is
    // the memory's GUARANTEED size (initial pages; memory only grows), so a
    // proven-in-bounds access can never trap on any run.
    ctx.trap_checks.push(TrapCheck {
        func_index,
        pc,
        op: op_label.to_string(),
        kind: TrapKind::OutOfBounds,
        verdict: if in_bounds {
            TrapVerdict::ProvenSafe
        } else {
            TrapVerdict::PotentialTrap
        },
    });

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
    // FEAT-058: update tracked memory content.
    //
    // First INVALIDATE (⊤) every offset whose byte range could overlap this
    // store — the window `[effective.lo − (MAX_ACCESS − 1), effective.hi + width)`
    // — so no stale cell of any width survives an overlapping write (the
    // type-punning soundness keystone). Invalidation is unconditional on the
    // in-bounds verdict: if the store executes it wrote here; if it traps, the
    // following code is unreachable — either way, forgetting content is sound.
    let inval_lo = effective.lo.saturating_sub(MEM_MAX_ACCESS_WIDTH - 1);
    let inval_hi = effective.hi.saturating_add(width as i64);
    ctx.mem = ctx.mem.weak_store(inval_lo, inval_hi, domain::top());

    // Then RECORD precise content only for a singleton, in-bounds i32 (4-byte)
    // store of a plain i32 value (a region-pointer's projected offset interval
    // is NOT the stored bit pattern, so it must not be recorded — unsound).
    if in_bounds
        && width == 4
        && effective.lo == effective.hi
        && let AbstractValue::I32Interval(v_iv) = value_v
    {
        ctx.mem = ctx.mem.strong_store(effective.lo, v_iv);
    }
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

/// FEAT-036 soundness: does a constant expression (a global init or an
/// element-segment offset/item) contain a `ref.func`? Such an expression takes
/// a defined function's address OUTSIDE any function body — the body-only
/// operator scan misses it, so the param-range gate must account for it here.
fn const_expr_takes_func_ref(expr: &wasmparser::ConstExpr<'_>) -> bool {
    expr.get_operators_reader()
        .into_iter()
        .any(|op| matches!(op, Ok(Operator::RefFunc { .. })))
}

/// FEAT-036 soundness: does an element segment name any defined function (and
/// thereby take its address)? `Functions` items are bare func indices;
/// `Expressions` items may carry `ref.func`. A malformed segment is treated as
/// taking a reference (conservative — never under-reports an escape).
fn element_items_take_func_ref(items: &wasmparser::ElementItems<'_>) -> Result<bool, AnalyzeError> {
    match items {
        wasmparser::ElementItems::Functions(funcs) => {
            Ok(funcs.clone().into_iter().next().is_some())
        }
        wasmparser::ElementItems::Expressions(_, exprs) => {
            for expr in exprs.clone() {
                let expr = expr.map_err(|e| {
                    AnalyzeError::InvalidModule(format!("element expression item: {e}"))
                })?;
                if const_expr_takes_func_ref(&expr) {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

/// FEAT-039: collect the function indices a constant expression takes the
/// address of via `ref.func` (global init / element item). Used to seed
/// reachability roots when funcrefs can escape (the open-world case).
fn const_expr_ref_func_targets(expr: &wasmparser::ConstExpr<'_>, out: &mut Vec<u32>) {
    for op in expr.get_operators_reader() {
        if let Ok(Operator::RefFunc { function_index }) = op {
            out.push(function_index);
        }
    }
}

/// FEAT-039: collect the function indices an element segment names (bare
/// `Functions` items and `ref.func` `Expressions` items). A malformed segment
/// is ignored for collection (the boolean escape flag already forces the
/// conservative path; this set only ADDS roots, so a miss here cannot make the
/// reachable set under-approximate beyond what the boolean already guards).
fn element_items_ref_func_targets(items: &wasmparser::ElementItems<'_>, out: &mut Vec<u32>) {
    match items {
        wasmparser::ElementItems::Functions(funcs) => {
            for idx in funcs.clone().into_iter().flatten() {
                out.push(idx);
            }
        }
        wasmparser::ElementItems::Expressions(_, exprs) => {
            for expr in exprs.clone().into_iter().flatten() {
                const_expr_ref_func_targets(&expr, out);
            }
        }
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
    // FEAT-058: a callee may write shared linear memory, and scry does not track
    // callee memory effects — so forget all tracked memory content across any
    // call (sound: subsequent loads fall back to ⊤). Interprocedural memory
    // summaries are future work. Applies on every path below.
    ctx.mem = scry_segment::top();
    // The call edge is recorded in each branch below, once the argument
    // values are known (FEAT-036: `arg_ranges`). For a signature-unknown
    // import the args can't be popped, so the edge carries empty `arg_ranges`.
    //
    // Resolve the callee's signature. If unknown (import / unrecorded
    // type), keep v0.4's behaviour: leave the operand stack untouched
    // (sound for the straight-line core — see `apply_call_stack_effect`
    // doc), record the edge, emit the diagnostic, done.
    let Some((param_tys, _result_tys)) = module_ctx.signature_of_func(callee_func_index) else {
        call_graph.push(CallEdge {
            caller_func: func_index,
            pc,
            indirect: false,
            resolved_targets: alloc::vec![callee_func_index],
            soundness: SoundnessTag::Sound,
            arg_ranges: Vec::new(),
        });
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

    // FEAT-036: record the edge carrying the abstract arguments at this site.
    call_graph.push(CallEdge {
        caller_func: func_index,
        pc,
        indirect: false,
        resolved_targets: alloc::vec![callee_func_index],
        soundness: SoundnessTag::Sound,
        arg_ranges: args.clone(),
    });

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
            /*emit_gaps=*/ None,
            /*emit_trap_checks=*/ None,
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
    // FEAT-058: an indirect callee may write shared linear memory — forget all
    // tracked memory content (sound; see handle_call).
    ctx.mem = scry_segment::top();
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
        // FEAT-036: indirect-call arguments are not harvested (and any
        // indirectly-reachable callee is forced to ⊤ params anyway), so leave
        // empty.
        arg_ranges: Vec::new(),
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
                            // scry#126: `op_report_name`, NOT `op_name` — this
                            // diagnostic's TRIGGER is an unmodelled operator, so
                            // `op_name`'s `<unsupported>` fallback fired for
                            // exactly the population it exists to describe.
                            "taint: operator {} not modelled — taint state conservatively \
                             raised to High (sound, FEAT-009)",
                            op_report_name(op)
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
/// FEAT-040: a human-readable name for ANY operator, for gap records. Uses the
/// curated [`op_name`] when known, else falls back to the operator's Debug
/// variant name (e.g. `F64Add`, `V128Const`) so an unsupported op is still
/// identified in the gap report rather than shown as a generic placeholder.
fn op_report_name(op: &Operator<'_>) -> String {
    let n = op_name(op);
    if n != "<unsupported>" {
        return n.to_string();
    }
    let dbg = alloc::format!("{op:?}");
    dbg.split([' ', '(', '{'])
        .next()
        .unwrap_or("<op>")
        .to_string()
}

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
        // FEAT-092 (scry#126): `op_name` covered only i32.load/i32.store among
        // memory ops, so `op_report_name` fell through to the `{:?}` Debug
        // fallback for every other one and leaked a RUST ENUM IDENTIFIER into
        // consumer-facing text — measured 2,800 of 10,520 advisories on
        // scry_mcdc.wasm. The same operator then carried TWO names (the
        // non-degraded path said `i64.store`, the degraded path `I64Store`),
        // splitting one operator into two rows in an operator ranking.
        Operator::I64Load { .. } => "i64.load",
        Operator::I64Store { .. } => "i64.store",
        Operator::F32Load { .. } => "f32.load",
        Operator::F32Store { .. } => "f32.store",
        Operator::F64Load { .. } => "f64.load",
        Operator::F64Store { .. } => "f64.store",
        Operator::I32Load8S { .. } => "i32.load8_s",
        Operator::I32Load8U { .. } => "i32.load8_u",
        Operator::I32Load16S { .. } => "i32.load16_s",
        Operator::I32Load16U { .. } => "i32.load16_u",
        Operator::I32Store8 { .. } => "i32.store8",
        Operator::I32Store16 { .. } => "i32.store16",
        Operator::I64Load8S { .. } => "i64.load8_s",
        Operator::I64Load8U { .. } => "i64.load8_u",
        Operator::I64Load16S { .. } => "i64.load16_s",
        Operator::I64Load16U { .. } => "i64.load16_u",
        Operator::I64Load32S { .. } => "i64.load32_s",
        Operator::I64Load32U { .. } => "i64.load32_u",
        Operator::I64Store8 { .. } => "i64.store8",
        Operator::I64Store16 { .. } => "i64.store16",
        Operator::I64Store32 { .. } => "i64.store32",
        Operator::MemoryCopy { .. } => "memory.copy",
        Operator::MemoryFill { .. } => "memory.fill",
        Operator::MemoryInit { .. } => "memory.init",
        Operator::DataDrop { .. } => "data.drop",
        Operator::I32WrapI64 => "i32.wrap_i64",
        Operator::I64ExtendI32S => "i64.extend_i32_s",
        Operator::I64ExtendI32U => "i64.extend_i32_u",
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
                operand_stack: alloc::vec![av.clone()],
                relational: alloc::vec![],
                memory: alloc::vec![],
                linear: alloc::vec![],
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
            stack_usage: StackUsage {
                sp_global: None,
                functions: alloc::vec![],
                max_stack_bytes: StackBound::Bytes(0),
            },
            reachable_from_exports: alloc::vec![],
            function_meta: alloc::vec![],
            verified_premises: FusionPremises::default(),
            bit_facts: alloc::vec![],
            gaps: alloc::vec![],
            pentagon_facts: alloc::vec![],
            trap_checks: alloc::vec![],
            float_facts: alloc::vec![],
            handle_findings: alloc::vec![],
            advisories: alloc::vec![],
            func_identities: alloc::vec![],
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

    /// FEAT-016 slice-2b-ii (octagon product): a loop counter bounded by a
    /// VARIABLE relation (`i < n`, with `n` in a local, not an immediate) stays
    /// bounded. The exit guard compares two locals, so slice-2b-i's constant
    /// peephole cannot fire and the interval fixpoint alone widens `i` to ⊤;
    /// the relational octagon carries `i ≤ n` across iterations and projects
    /// `i ≤ n ≤ 10` — bounded, where interval-alone gives ⊤.
    #[test]
    fn feat016_octagon_var_bounds_counter() {
        let wat_path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../scry-analyzer/test-fixtures/fixture-11-var-bound.wat"
        );
        let bytes = wat::parse_file(wat_path).expect("assemble fixture-11");
        let config = AnalysisConfig {
            widening_threshold: Some(3),
            emit_diagnostics: true,
            taint_policy: None,
        };
        let result = analyze(bytes, config).expect("analyze fixture-11 must succeed");
        let last = result
            .invariants
            .points
            .last()
            .expect("fixture-11 must emit points past the loop");
        let i = last
            .locals
            .iter()
            .find(|l| l.local_index == 0)
            .and_then(|l| match l.value {
                AbstractValue::I32Interval(iv) => Some(iv),
                _ => None,
            })
            .expect("local i (index 0) i32-interval at final point");
        // The slice-2b-ii win: i has a finite UPPER BOUND ≤ 10 via the
        // RELATION i ≤ n ∧ n = 10 (interval-alone + constant guards give ⊤,
        // since the guard compares two locals, not local-vs-const).
        assert!(
            i.hi <= 10,
            "octagon product failed: variable-bounded counter i has no tight upper bound \
             (got hi={}, expected ≤ 10 — interval/const-guard alone widen to ⊤ here)",
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

    fn analyze_fixture(name: &str) -> AnalysisResult {
        let wat_path = alloc::format!(
            "{}/../scry-analyzer/test-fixtures/{}",
            env!("CARGO_MANIFEST_DIR"),
            name
        );
        let bytes = wat::parse_file(&wat_path).expect("assemble fixture");
        let config = AnalysisConfig {
            widening_threshold: Some(3),
            emit_diagnostics: true,
            taint_policy: None,
        };
        analyze(bytes, config).expect("analyze must succeed")
    }

    /// FEAT-041: the octagon's relational constraint between i and n in
    /// fixture-11 (the variable-bounded loop) is now SURFACED on the program
    /// points — the v1.9 non-observability finding closed. A relation between
    /// locals 0 (i) and 1 (n) must appear, and every surfaced constraint must be
    /// sound (consistent with the unary intervals at that point).
    #[test]
    fn feat041_relational_invariants_surfaced() {
        let r = analyze_fixture("fixture-11-var-bound.wat");
        let has_rel = r.invariants.points.iter().any(|p| {
            p.relational
                .iter()
                .any(|c| (c.a == 0 && c.b == 1) || (c.a == 1 && c.b == 0))
        });
        assert!(
            has_rel,
            "fixture-11 must surface a relational constraint between i (0) and n (1); \
             points' relational: {:?}",
            r.invariants
                .points
                .iter()
                .map(|p| (p.pc, &p.relational))
                .collect::<alloc::vec::Vec<_>>()
        );
    }

    /// FEAT-041: a purely non-relational function surfaces NO relational
    /// constraints (no noise).
    #[test]
    fn feat041_no_relations_when_non_relational() {
        let r = analyze_default(
            "(module (func (param i32) (result i32) local.get 0 i32.const 1 i32.add))",
        );
        assert!(
            r.invariants.points.iter().all(|p| p.relational.is_empty()),
            "a non-relational function must surface no relational constraints"
        );
    }

    /// FEAT-043 (DD-016 slice-3): the stack longest-path weights a
    /// `call_indirect` by its RESOLVED target (a constant index → one table
    /// entry), not the whole table. The entry (frame 8) calls table[0]=$small
    /// (frame 16), so its bound is 8+16=24 — NOT 8+max(16,64)=72 that the
    /// whole-table over-approximation would give.
    #[test]
    fn feat043_indirect_stack_weighted_by_resolved_target() {
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 65536)) \
               (table 2 2 funcref) (elem (i32.const 0) 0 1) \
               (type $t (func)) \
               (func \
                 global.get $sp i32.const 16 i32.sub global.set $sp \
                 global.get $sp i32.const 16 i32.add global.set $sp) \
               (func \
                 global.get $sp i32.const 64 i32.sub global.set $sp \
                 global.get $sp i32.const 64 i32.add global.set $sp) \
               (func (export \"entry\") \
                 global.get $sp i32.const 8 i32.sub global.set $sp \
                 i32.const 0 call_indirect (type $t) \
                 global.get $sp i32.const 8 i32.add global.set $sp))",
        );
        let entry = r
            .stack_usage
            .functions
            .iter()
            .find(|f| f.func_index == 2)
            .expect("entry function stack record");
        assert_eq!(
            entry.max_stack,
            StackBound::Bytes(24),
            "entry must be weighted by the RESOLVED target $small (8+16=24), not the \
             whole-table max (8+64=72); got {:?}",
            entry.max_stack
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room): a call inside an `if` region
    /// (write-set EMPTY — a void call) is havocked, so its edge is never in
    /// call_graph. Without recording a gap for the call-bearing region, the
    /// function looks gap-free and resolved_stack_callees would drop $big from
    /// the weighting → under-count (256 instead of 264). The havoc-region gap
    /// must force the conservative fallback, restoring the sound 264.
    #[test]
    fn feat043_call_in_havocked_if_not_dropped() {
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 65536)) \
               (func \
                 global.get $sp i32.const 256 i32.sub global.set $sp \
                 global.get $sp i32.const 256 i32.add global.set $sp) \
               (func (export \"entry\") (param i32) \
                 global.get $sp i32.const 8 i32.sub global.set $sp \
                 local.get 0 (if (then call 0)) \
                 global.get $sp i32.const 8 i32.add global.set $sp))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Bytes(264),
            "a void call inside an if must still contribute its callee's frame \
             (8 + 256 = 264, not 256); got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room #6): a constant SP decrement
    /// inside a `loop` body with no per-iteration restore leaks `frame` bytes on
    /// FEAT-044 (AC-014): a guard `local.get i; local.get n; i32.lt_u; if`
    /// makes scry record the strict relation `i < n` for the then-region — the
    /// `index < length` fact OOB-trap detection (FEAT-046) consumes.
    #[test]
    fn feat044_lt_u_guard_records_index_below_length() {
        let r = analyze_default(
            "(module \
               (func (export \"f\") (param i32 i32) (result i32) \
                 local.get 0 local.get 1 i32.lt_u \
                 (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        assert_eq!(r.pentagon_facts.len(), 1, "expected one recorded guard");
        let f = &r.pentagon_facts[0];
        assert_eq!(f.lhs_local, 0);
        assert_eq!(f.bound, PentagonBound::Local(1));
        assert!(f.unsigned, "lt_u guard is unsigned");
    }

    /// FEAT-044: a guard against a constant (`i < 16`) is recorded with a
    /// `Const` bound; the signed comparison is flagged `unsigned == false`.
    #[test]
    fn feat044_lt_s_guard_against_const_recorded() {
        let r = analyze_default(
            "(module \
               (func (export \"f\") (param i32) (result i32) \
                 local.get 0 i32.const 16 i32.lt_s \
                 (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        assert_eq!(r.pentagon_facts.len(), 1);
        let f = &r.pentagon_facts[0];
        assert_eq!(f.lhs_local, 0);
        assert_eq!(f.bound, PentagonBound::Const(16));
        assert!(!f.unsigned);
    }

    /// FEAT-044: a comparison NOT feeding an `if` records nothing — the strict
    /// fact is only sound when it guards the region.
    #[test]
    fn feat044_unguarded_comparison_records_nothing() {
        let r = analyze_default(
            "(module \
               (func (export \"f\") (param i32 i32) (result i32) \
                 local.get 0 local.get 1 i32.lt_u))",
        );
        assert!(r.pentagon_facts.is_empty());
    }

    fn trap_verdict(r: &AnalysisResult, op: &str, kind: TrapKind) -> Option<TrapVerdict> {
        r.trap_checks
            .iter()
            .find(|t| t.op == op && t.kind == kind)
            .map(|t| t.verdict)
    }

    /// FEAT-045: a constant non-zero divisor and a constant dividend prove BOTH
    /// the div-by-zero and the signed-overflow cases safe.
    #[test]
    fn feat045_const_divisor_proven_safe() {
        let r = analyze_default(
            "(module (func (export \"f\") (result i32) \
               i32.const 100 i32.const 4 i32.div_s))",
        );
        assert_eq!(
            trap_verdict(&r, "i32.div_s", TrapKind::DivByZero),
            Some(TrapVerdict::ProvenSafe)
        );
        assert_eq!(
            trap_verdict(&r, "i32.div_s", TrapKind::SignedOverflow),
            Some(TrapVerdict::ProvenSafe)
        );
    }

    /// FEAT-045: a literal zero divisor is a div-by-zero POTENTIAL-TRAP (it in
    /// fact always traps; scry soundly flags it).
    #[test]
    fn feat045_zero_divisor_potential_trap() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) \
               local.get 0 i32.const 0 i32.div_u))",
        );
        assert_eq!(
            trap_verdict(&r, "i32.div_u", TrapKind::DivByZero),
            Some(TrapVerdict::PotentialTrap)
        );
    }

    /// FEAT-045: an unknown (parameter) divisor cannot be proven non-zero — the
    /// sound default is POTENTIAL-TRAP, and the signed-overflow case (unknown
    /// dividend AND unknown divisor) is also POTENTIAL-TRAP.
    #[test]
    fn feat045_unknown_divisor_potential_trap() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) \
               local.get 0 local.get 1 i32.div_s))",
        );
        assert_eq!(
            trap_verdict(&r, "i32.div_s", TrapKind::DivByZero),
            Some(TrapVerdict::PotentialTrap)
        );
        assert_eq!(
            trap_verdict(&r, "i32.div_s", TrapKind::SignedOverflow),
            Some(TrapVerdict::PotentialTrap)
        );
    }

    /// FEAT-045: `div_u` and `rem_s`/`rem_u` never trap on INT_MIN/-1, so they
    /// get a DivByZero verdict but NO SignedOverflow verdict.
    #[test]
    fn feat045_only_div_s_has_overflow_verdict() {
        let r = analyze_default(
            "(module \
               (func (export \"u\") (param i32) (result i32) local.get 0 i32.const 3 i32.div_u) \
               (func (export \"r\") (param i32) (result i32) local.get 0 i32.const 3 i32.rem_s))",
        );
        assert!(trap_verdict(&r, "i32.div_u", TrapKind::DivByZero).is_some());
        assert!(trap_verdict(&r, "i32.div_u", TrapKind::SignedOverflow).is_none());
        assert!(trap_verdict(&r, "i32.rem_s", TrapKind::DivByZero).is_some());
        assert!(trap_verdict(&r, "i32.rem_s", TrapKind::SignedOverflow).is_none());
    }

    /// FEAT-045: a div_s whose dividend is bounded away from INT_MIN is overflow-
    /// safe even with an unknown divisor (the INT_MIN/-1 case needs BOTH).
    #[test]
    fn feat045_bounded_dividend_makes_overflow_safe() {
        // dividend = 0+0 = const 0 (excludes INT_MIN); divisor = param (unknown).
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) \
               i32.const 0 local.get 0 i32.div_s))",
        );
        assert_eq!(
            trap_verdict(&r, "i32.div_s", TrapKind::SignedOverflow),
            Some(TrapVerdict::ProvenSafe),
            "dividend const 0 excludes INT_MIN ⇒ overflow impossible"
        );
        // but div-by-zero is still possible (divisor unknown)
        assert_eq!(
            trap_verdict(&r, "i32.div_s", TrapKind::DivByZero),
            Some(TrapVerdict::PotentialTrap)
        );
    }

    /// FEAT-045: a div/rem no longer degrades the whole function (it used to hit
    /// the unsupported-op fallback and scrub everything to ⊤). A const-divisor
    /// `div_u` AFTER an earlier `div_s` is still reached and proven safe — only
    /// possible if the first division left the interpreter live.
    #[test]
    fn feat045_div_does_not_degrade_function() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) \
               local.get 0 i32.const 2 i32.div_s \
               local.get 0 i32.const 5 i32.div_u \
               i32.add))",
        );
        assert!(trap_verdict(&r, "i32.div_s", TrapKind::DivByZero).is_some());
        assert_eq!(
            trap_verdict(&r, "i32.div_u", TrapKind::DivByZero),
            Some(TrapVerdict::ProvenSafe),
            "the later const-divisor div_u stays live (div_s did not scrub it)"
        );
    }

    fn oob_verdict(r: &AnalysisResult, op: &str) -> Option<TrapVerdict> {
        r.trap_checks
            .iter()
            .find(|t| t.op == op && t.kind == TrapKind::OutOfBounds)
            .map(|t| t.verdict)
    }

    /// FEAT-046: a constant in-bounds address proves the access safe (memory of
    /// 1 page = 65536 bytes; `i32.load` at address 0 accesses [0,4) ⊂ memory).
    #[test]
    fn feat046_const_in_bounds_proven_safe() {
        let r = analyze_default(
            "(module (memory 1) (func (export \"f\") (result i32) \
               i32.const 0 i32.load))",
        );
        assert_eq!(
            oob_verdict(&r, "i32.load"),
            Some(TrapVerdict::ProvenSafe),
            "addr 0 + 4 bytes fits in 65536-byte memory"
        );
    }

    /// FEAT-046: a constant address past the memory is a POTENTIAL-TRAP.
    #[test]
    fn feat046_const_out_of_bounds_potential_trap() {
        let r = analyze_default(
            "(module (memory 1) (func (export \"f\") (result i32) \
               i32.const 100000 i32.load))",
        );
        assert_eq!(
            oob_verdict(&r, "i32.load"),
            Some(TrapVerdict::PotentialTrap),
            "addr 100000 exceeds the 65536-byte memory"
        );
    }

    /// FEAT-046: an unknown (parameter) address cannot be proven in-bounds.
    #[test]
    fn feat046_unknown_address_potential_trap() {
        let r = analyze_default(
            "(module (memory 1) (func (export \"f\") (param i32) (result i32) \
               local.get 0 i32.load))",
        );
        assert_eq!(
            oob_verdict(&r, "i32.load"),
            Some(TrapVerdict::PotentialTrap)
        );
    }

    /// FEAT-046: a store is classified too (here an in-bounds const address).
    #[test]
    fn feat046_store_in_bounds_proven_safe() {
        let r = analyze_default(
            "(module (memory 1) (func (export \"f\") \
               i32.const 8 i32.const 42 i32.store))",
        );
        assert_eq!(oob_verdict(&r, "i32.store"), Some(TrapVerdict::ProvenSafe));
    }

    /// FEAT-046: the access width matters — a const address at the very end of
    /// memory where the access would spill past the boundary is POTENTIAL-TRAP.
    #[test]
    fn feat046_access_width_spills_past_boundary() {
        // addr 65534 + 4-byte load = bytes [65534, 65538) but memory is [0,65536).
        let r = analyze_default(
            "(module (memory 1) (func (export \"f\") (result i32) \
               i32.const 65534 i32.load))",
        );
        assert_eq!(
            oob_verdict(&r, "i32.load"),
            Some(TrapVerdict::PotentialTrap),
            "a 4-byte load at 65534 spills past the 65536 boundary"
        );
    }

    /// FEAT-046 (never silently dropped): an unmodelled narrow load (`i32.load8_u`)
    /// still gets a verdict — conservatively PotentialTrap (the interval
    /// interpreter does not model the narrow width precisely).
    #[test]
    fn feat046_narrow_load_classified_potential_trap() {
        let r = analyze_default(
            "(module (memory 1) (func (export \"f\") (result i32) \
               i32.const 0 i32.load8_u))",
        );
        // The function's only memory op is the narrow load; it must be
        // classified (regardless of the op-name spelling) and PotentialTrap.
        let oob: alloc::vec::Vec<_> = r
            .trap_checks
            .iter()
            .filter(|t| t.kind == TrapKind::OutOfBounds)
            .collect();
        assert_eq!(oob.len(), 1, "the narrow load is classified, not omitted");
        assert_eq!(
            oob[0].verdict,
            TrapVerdict::PotentialTrap,
            "an unmodelled narrow load cannot be proven in-bounds"
        );
    }

    /// FEAT-084 helper: the OutOfBounds verdict for the (single) memory access
    /// in function `func_index`. `None` if the function has no such trap check
    /// — callers assert `Some(..)` so a test can never pass because the access
    /// silently produced no obligation at all.
    fn oob_verdict_in_func(r: &AnalysisResult, func_index: u32) -> Option<TrapVerdict> {
        let checks: alloc::vec::Vec<_> = r
            .trap_checks
            .iter()
            .filter(|t| t.func_index == func_index && t.kind == TrapKind::OutOfBounds)
            .collect();
        assert!(
            checks.len() <= 1,
            "test fixtures here have at most one memory access per function; got {checks:?}"
        );
        checks.first().map(|t| t.verdict)
    }

    /// FEAT-084 helper: true iff `func_index` recorded an `unsupported-op` gap.
    fn has_unsupported_gap(r: &AnalysisResult, func_index: u32) -> bool {
        r.gaps
            .iter()
            .any(|g| g.func_index == func_index && g.kind == GapKind::UnsupportedOp)
    }

    /// FEAT-084 (scry#126) AC#1: `x & 0xFFF` bounds the address to [0, 4095],
    /// an order of magnitude inside the 65536-byte memory, so the load is
    /// PROVEN-SAFE. Red-first baseline on main: POTENTIAL-TRAP with an
    /// `unsupported-op` gap, while the constant-address load beside it proves.
    #[test]
    fn feat084_masked_address_proven_safe() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"masked\") (param i32) (result i32) \
                 local.get 0 i32.const 0xFFF i32.and i32.load) \
               (func (export \"constant\") (result i32) \
                 i32.const 16 i32.load))",
        );
        // Precondition (anti-vacuity): both loads produced an OOB obligation.
        let masked = oob_verdict_in_func(&r, 0).expect("masked load must be classified");
        let constant = oob_verdict_in_func(&r, 1).expect("constant load must be classified");
        assert_eq!(
            constant,
            TrapVerdict::ProvenSafe,
            "baseline sanity: the constant-address load proves"
        );
        assert_eq!(
            masked,
            TrapVerdict::ProvenSafe,
            "x & 0xFFF ≤ 4095 < 65536-4: the masked load must be PROVEN-SAFE"
        );
        assert!(
            !has_unsupported_gap(&r, 0),
            "i32.and is modelled — no unsupported-op gap; gaps={:?}",
            r.gaps
        );
    }

    /// FEAT-084 AC#2 (NEGATIVE — the test that keeps the reduction honest): a
    /// mask that does NOT bound the address below the memory size must stay
    /// POTENTIAL-TRAP. `x & 0x1FFFF` can reach 131071 ≥ 65536.
    #[test]
    fn feat084_unbounding_mask_stays_potential_trap() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"f\") (param i32) (result i32) \
                 local.get 0 i32.const 0x1FFFF i32.and i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("the load must still be classified");
        assert_eq!(
            v,
            TrapVerdict::PotentialTrap,
            "x & 0x1FFFF reaches 131071 ≥ memory size 65536 — must NOT prove"
        );
    }

    /// FEAT-084 AC#2 (NEGATIVE, sign-agnostic i32): a mask with the sign bit
    /// set does not bound the value — `x & 0x80000FFF` admits addresses like
    /// 0x80000000 (or, signed, negative values). Must stay POTENTIAL-TRAP.
    #[test]
    fn feat084_negative_mask_stays_potential_trap() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"f\") (param i32) (result i32) \
                 local.get 0 i32.const 0x80000FFF i32.and i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("the load must still be classified");
        assert_eq!(
            v,
            TrapVerdict::PotentialTrap,
            "a sign-bit mask does not bound the address — must NOT prove"
        );
    }

    /// FEAT-084 AC#3: `i32.and` no longer scrubs the function — a DOWNSTREAM
    /// constant-address load (after the mask result is stored to a local)
    /// retains its proof. Red-first baseline on main: the and degrades the
    /// whole function first, so the later load is POTENTIAL-TRAP.
    #[test]
    fn feat084_downstream_facts_survive_the_mask() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"g\") (param i32) (result i32) (local i32) \
                 local.get 0 i32.const 0xFFF i32.and local.set 1 \
                 i32.const 16 i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("the downstream load must be classified");
        assert_eq!(
            v,
            TrapVerdict::ProvenSafe,
            "the const-address load AFTER the mask must stay proven (no scrub)"
        );
        assert!(
            !has_unsupported_gap(&r, 0),
            "no unsupported-op gap for a function whose only exotic op is i32.and; gaps={:?}",
            r.gaps
        );
    }

    /// FEAT-084: `i32.or` — OR can only set bits, so `(x & 0xF00) | 0xFF` is
    /// bounded by 0xFFF and the load proves.
    #[test]
    fn feat084_or_bounded_proven_safe() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"f\") (param i32) (result i32) \
                 local.get 0 i32.const 0xF00 i32.and i32.const 0xFF i32.or i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("load classified");
        assert_eq!(v, TrapVerdict::ProvenSafe, "(x & 0xF00) | 0xFF ≤ 0xFFF");
    }

    /// FEAT-084: `i32.xor` of a bounded value with a constant inside the same
    /// bit budget stays bounded: `(x & 0xFFF) ^ 0xFF ≤ 0xFFF`.
    #[test]
    fn feat084_xor_bounded_proven_safe() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"f\") (param i32) (result i32) \
                 local.get 0 i32.const 0xFFF i32.and i32.const 0xFF i32.xor i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("load classified");
        assert_eq!(v, TrapVerdict::ProvenSafe, "(x & 0xFFF) ^ 0xFF ≤ 0xFFF");
    }

    /// FEAT-084: `i32.shl` by a constant count keeps the known high zeros:
    /// `(x & 0xFF) << 4 ≤ 0xFF0`.
    #[test]
    fn feat084_shl_bounded_proven_safe() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"f\") (param i32) (result i32) \
                 local.get 0 i32.const 0xFF i32.and i32.const 4 i32.shl i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("load classified");
        assert_eq!(v, TrapVerdict::ProvenSafe, "(x & 0xFF) << 4 ≤ 0xFF0");
    }

    /// FEAT-084: `i32.shr_u` by a constant count bounds any x: `x >> 20 ≤ 0xFFF`.
    #[test]
    fn feat084_shr_u_bounded_proven_safe() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"f\") (param i32) (result i32) \
                 local.get 0 i32.const 20 i32.shr_u i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("load classified");
        assert_eq!(v, TrapVerdict::ProvenSafe, "x >> 20 ≤ 0xFFF < 65536-4");
    }

    /// FEAT-084 (NEGATIVE for shifts): a variable shift count proves nothing —
    /// `x >> y` must stay POTENTIAL-TRAP (count 0 leaves x unbounded).
    #[test]
    fn feat084_variable_shift_count_stays_potential_trap() {
        let r = analyze_default(
            "(module (memory 1) \
               (func (export \"f\") (param i32 i32) (result i32) \
                 local.get 0 local.get 1 i32.shr_u i32.load))",
        );
        let v = oob_verdict_in_func(&r, 0).expect("the load must still be classified");
        assert_eq!(
            v,
            TrapVerdict::PotentialTrap,
            "a variable shift count bounds nothing — must NOT prove"
        );
    }

    /// FEAT-049: a resource handle dropped and then USED (a method call) is a
    /// use-after-drop, reported soundly.
    #[test]
    fn feat049_use_after_drop_reported() {
        let r = analyze_default(
            "(module \
               (import \"p/i\" \"[resource-drop]t\" (func $drop (param i32))) \
               (import \"p/i\" \"[method]t.go\" (func $use (param i32))) \
               (func (export \"f\") (param i32) \
                 local.get 0 call $drop \
                 local.get 0 call $use))",
        );
        let uad: alloc::vec::Vec<_> = r
            .handle_findings
            .iter()
            .filter(|h| h.kind == HandleFindingKind::UseAfterDrop)
            .collect();
        assert_eq!(
            uad.len(),
            1,
            "one use-after-drop expected: {:?}",
            r.handle_findings
        );
        assert_eq!(uad[0].local_index, 0);
    }

    /// FEAT-049: dropping the same handle twice is a double-drop.
    #[test]
    fn feat049_double_drop_reported() {
        let r = analyze_default(
            "(module \
               (import \"p/i\" \"[resource-drop]t\" (func $drop (param i32))) \
               (func (export \"f\") (param i32) \
                 local.get 0 call $drop \
                 local.get 0 call $drop))",
        );
        assert_eq!(
            r.handle_findings
                .iter()
                .filter(|h| h.kind == HandleFindingKind::DoubleDrop)
                .count(),
            1,
            "one double-drop expected: {:?}",
            r.handle_findings
        );
    }

    /// FEAT-049: a handle used BEFORE it is dropped (correct affine lifetime)
    /// raises NO finding — no false report.
    #[test]
    fn feat049_correct_lifetime_no_finding() {
        let r = analyze_default(
            "(module \
               (import \"p/i\" \"[resource-drop]t\" (func $drop (param i32))) \
               (import \"p/i\" \"[method]t.go\" (func $use (param i32))) \
               (func (export \"f\") (param i32) \
                 local.get 0 call $use \
                 local.get 0 call $use \
                 local.get 0 call $drop))",
        );
        assert!(
            r.handle_findings.is_empty(),
            "correct use-then-drop must not report: {:?}",
            r.handle_findings
        );
    }

    /// FEAT-059: the advisory engine synthesises all four actionability classes
    /// from the sound findings, ranked with DefiniteFault first.
    #[test]
    fn feat059_synthesizes_ranked_classes() {
        let r = analyze_default(
            "(module \
               (import \"p/i\" \"[resource-drop]t\" (func $drop (param i32))) \
               (import \"p/i\" \"[method]t.go\" (func $use (param i32))) \
               (func (export \"bug\") (param i32) \
                 local.get 0 call $drop local.get 0 call $use) \
               (func (export \"unproven\") (param i32 i32) (result i32) \
                 local.get 0 local.get 1 i32.div_s) \
               (func (export \"safe\") (result i32) i32.const 10 i32.const 2 i32.div_u) \
               (func (export \"gap\") (param i32) (result i32) local.get 0 i32.popcnt))",
        );
        use AdvisoryClass::*;
        let has = |c: AdvisoryClass| r.advisories.iter().any(|a| a.class == c);
        assert!(has(DefiniteFault), "use-after-drop → DefiniteFault");
        assert!(
            has(UnprovenObligation),
            "unknown divisor → UnprovenObligation"
        );
        assert!(has(PrecisionGap), "unsupported popcnt → PrecisionGap");
        assert!(
            has(LeverageableFact),
            "const-divisor div_u → LeverageableFact"
        );
        // ranked: the first advisory is the proven bug.
        assert_eq!(r.advisories[0].class, DefiniteFault, "faults rank first");
        // every advisory carries a verification oracle.
        assert!(
            r.advisories.iter().all(|a| !a.verification.is_empty()),
            "every advisory names a verification oracle"
        );
    }

    /// FEAT-059 HONESTY INVARIANT: a POTENTIAL-TRAP is only ever an
    /// UnprovenObligation, NEVER a DefiniteFault — a sound tool must not label an
    /// unproven obligation a bug. DefiniteFault advisories come only from proven
    /// faults (handle findings), whose codes are the handle-fault codes.
    #[test]
    fn feat059_potential_trap_is_never_a_definite_fault() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) \
               local.get 0 local.get 1 i32.div_s))",
        );
        // there IS a POTENTIAL-TRAP here (unknown divisor)
        assert!(
            r.advisories
                .iter()
                .any(|a| a.class == AdvisoryClass::UnprovenObligation),
            "unknown divisor yields an UnprovenObligation"
        );
        // and NO advisory calls it a definite fault
        for a in &r.advisories {
            if a.class == AdvisoryClass::DefiniteFault {
                assert!(
                    a.code == "use-after-drop" || a.code == "double-drop",
                    "DefiniteFault must be a proven handle fault, not `{}`",
                    a.code
                );
            }
        }
    }

    /// FEAT-059: a clean module (no faults, no unproven traps, no gaps) yields no
    /// fault/obligation advisories — guidance is finding-driven, not noise.
    #[test]
    fn feat059_clean_module_no_fault_advisories() {
        let r = analyze_default(
            "(module (func (export \"f\") (result i32) i32.const 1 i32.const 2 i32.add))",
        );
        assert!(
            !r.advisories
                .iter()
                .any(|a| a.class == AdvisoryClass::DefiniteFault
                    || a.class == AdvisoryClass::UnprovenObligation),
            "a clean add-only function raises no fault/obligation advisories: {:?}",
            r.advisories
        );
    }

    /// FEAT-055: a POTENTIAL-TRAP obligation carries a candidate counterexample —
    /// the operand value that would trigger the trap (a repro/regression seed).
    #[test]
    fn feat055_div_by_zero_counterexample_is_divisor_0() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) \
               local.get 0 local.get 1 i32.div_s))",
        );
        let dbz = r
            .advisories
            .iter()
            .find(|a| a.code == "div-by-zero" && a.class == AdvisoryClass::UnprovenObligation)
            .expect("a div-by-zero obligation");
        let cx = dbz.counterexample.as_ref().expect("has a counterexample");
        assert!(
            cx.witness
                .iter()
                .any(|w| w.operand == "divisor" && w.value == 0),
            "divisor=0 witness expected: {:?}",
            cx.witness
        );
    }

    /// FEAT-055: an OOB obligation's counterexample address is the memory size
    /// (1 page = 65536 bytes) — the smallest definitely-out-of-bounds address.
    #[test]
    fn feat055_oob_counterexample_is_memory_size() {
        let r = analyze_default(
            "(module (memory 1) (func (export \"f\") (param i32) (result i32) \
               local.get 0 i32.load))",
        );
        let oob = r
            .advisories
            .iter()
            .find(|a| a.code == "out-of-bounds")
            .expect("an out-of-bounds obligation");
        let cx = oob.counterexample.as_ref().expect("has a counterexample");
        assert!(
            cx.witness
                .iter()
                .any(|w| w.operand == "address" && w.value == 65536),
            "address=65536 (1 page) witness expected: {:?}",
            cx.witness
        );
    }

    /// FEAT-055: only UnprovenObligation advisories carry a counterexample —
    /// a proven-safe / precision / fault advisory has none.
    #[test]
    fn feat055_non_obligations_have_no_counterexample() {
        let r = analyze_default(
            "(module (func (export \"f\") (result i32) i32.const 10 i32.const 2 i32.div_u))",
        );
        assert!(
            r.advisories
                .iter()
                .filter(|a| a.class != AdvisoryClass::UnprovenObligation)
                .all(|a| a.counterexample.is_none()),
            "non-obligation advisories must not carry a counterexample: {:?}",
            r.advisories
        );
    }

    /// FEAT-047: float arithmetic is no longer an opaque scope hole — a
    /// `local := c1 + c2` on f64 constants yields a sound float interval fact.
    #[test]
    fn feat047_float_add_yields_interval() {
        let r = analyze_default(
            "(module (func (export \"f\") (result f64) (local f64) \
               f64.const 1.5 f64.const 2.25 f64.add local.tee 0))",
        );
        let f = r
            .float_facts
            .iter()
            .find(|f| f.local_index == 0)
            .expect("a float fact for local 0");
        assert_eq!(f.width, 64);
        assert!(!f.nan);
        // 1.5 + 2.25 = 3.75 exactly; sound interval must contain it.
        assert!(
            f.lo() <= 3.75 && 3.75 <= f.hi(),
            "3.75 ∉ [{}, {}]",
            f.lo(),
            f.hi()
        );
    }

    /// FEAT-047: `x / 0.0`-style NaN sources — here `0.0 * inf` via a const —
    /// track the NaN possibility. (Uses f64 mul of 0 and a huge value squared to
    /// reach inf is overkill; instead verify a plain finite mul stays finite.)
    #[test]
    fn feat047_float_mul_finite_no_nan() {
        let r = analyze_default(
            "(module (func (export \"f\") (result f32) (local f32) \
               f32.const 3.0 f32.const 4.0 f32.mul local.tee 0))",
        );
        let f = r
            .float_facts
            .iter()
            .find(|f| f.local_index == 0)
            .expect("float fact");
        assert_eq!(f.width, 32);
        assert!(!f.nan, "3.0 * 4.0 is finite, not NaN");
        assert!(f.lo() <= 12.0 && 12.0 <= f.hi());
    }

    /// FEAT-047: a float local written from an unknown (parameter) value carries
    /// ⊤ and is NOT emitted (only informative, non-⊤ facts surface).
    #[test]
    fn feat047_unknown_float_param_not_emitted() {
        let r = analyze_default(
            "(module (func (export \"f\") (param f64) (result f64) \
               local.get 0 local.get 0 f64.add))",
        );
        // param is ⊤; ⊤+⊤ is ⊤ — no informative fact for a written local
        // (there is no local.set here anyway). Just assert no spurious fact.
        assert!(r.float_facts.iter().all(|f| f.width == 64 || f.width == 32));
    }

    /// FEAT-045 SOUNDNESS REGRESSION (clean-room): a div in a LOOP body must not
    /// keep a stale `ProvenSafe` from an early (pre-widening) iterate. Here the
    /// counter `i` runs 3→2→1→0 and `100 / i` traps at i=0; the converged
    /// divisor interval includes 0, so the verdict must be PotentialTrap — and
    /// there must be exactly ONE DivByZero entry for that op (reconciled).
    #[test]
    fn feat045_loop_divisor_reaching_zero_is_potential_trap() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) (local i32) \
               i32.const 3 local.set 1 \
               (loop \
                 local.get 1 i32.const 1 i32.sub local.set 1 \
                 i32.const 100 local.get 1 i32.div_s drop \
                 local.get 1 i32.const 0 i32.gt_s br_if 0) \
               i32.const 0))",
        );
        let dbz: alloc::vec::Vec<_> = r
            .trap_checks
            .iter()
            .filter(|t| t.op == "i32.div_s" && t.kind == TrapKind::DivByZero)
            .collect();
        assert_eq!(
            dbz.len(),
            1,
            "exactly one reconciled DivByZero verdict per op"
        );
        assert_eq!(
            dbz[0].verdict,
            TrapVerdict::PotentialTrap,
            "a loop divisor that reaches 0 must NOT be ProvenSafe (stale pre-widen iterate)"
        );
    }

    /// FEAT-045 (AC: "never silently dropped"): even when an unsupported op
    /// degrades the function, a div/rem reached afterwards still gets a verdict —
    /// necessarily PotentialTrap (operands no longer tracked). Here a `drop`
    /// (unmodelled in the interval interpreter) degrades, yet the div_u after it
    /// is still classified.
    #[test]
    fn feat045_degraded_div_still_classified() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) \
               local.get 0 i32.const 2 i32.div_s drop \
               i32.const 50 i32.const 5 i32.div_u))",
        );
        // div_u after the degrading `drop` is not silently dropped: it is
        // classified, conservatively as PotentialTrap.
        assert_eq!(
            trap_verdict(&r, "i32.div_u", TrapKind::DivByZero),
            Some(TrapVerdict::PotentialTrap),
            "reached-while-degraded div/rem is classified PotentialTrap, never omitted"
        );
    }

    // ════════════ ADVERSARIAL THROWAWAY (clean-room FEAT-044 pass) ════════════

    /// Probe B(1): operand order. `local.get 0; local.get 1; lt; if` must record
    /// lhs=0, bound=Local(1) (i.e. x0 < x1), NOT the reverse.
    #[test]
    fn adv_operand_order() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) \
               local.get 0 local.get 1 i32.lt_u \
               (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        assert_eq!(r.pentagon_facts.len(), 1);
        let f = &r.pentagon_facts[0];
        assert_eq!(f.lhs_local, 0, "lhs must be the FIRST local.get");
        assert_eq!(f.bound, PentagonBound::Local(1), "bound must be the SECOND");
    }

    /// Probe B(4): br_if must emit NOTHING. br_if branches when TRUE; the
    /// fall-through is where !(a<b) holds, so recording a<b would be UNSOUND.
    #[test]
    fn adv_br_if_emits_nothing() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) \
               (block \
                 local.get 0 local.get 1 i32.lt_u \
                 br_if 0)))",
        );
        assert!(
            r.pentagon_facts.is_empty(),
            "br_if must not emit a fact: {:?}",
            r.pentagon_facts
        );
    }

    /// Probe B(6a): comparison result STORED to a local then later used by `if`.
    /// The `if` does not consume the lt directly -> no fact may be emitted.
    /// `local.get 0; local.get 1; lt; local.set 2; ...; local.get 2; if`
    #[test]
    fn adv_result_stored_not_directly_consumed() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local i32) \
               local.get 0 local.get 1 i32.lt_u local.set 2 \
               local.get 2 \
               (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        // The window cmp,cmp,lt,if never lines up (local.set 2 sits between lt and if),
        // so nothing should be emitted.
        assert!(
            r.pentagon_facts.is_empty(),
            "stored bool not directly guarding if -> no fact: {:?}",
            r.pentagon_facts
        );
    }

    /// Probe B(6b): an op intervenes between lt and if, but ALSO try the case
    /// where another value is pushed after lt so the `if` tests something else.
    /// `local.get 0; local.get 1; lt; drop; i32.const 1; if` — the if tests the
    /// const, not the comparison. Must emit nothing.
    #[test]
    fn adv_intervening_op_before_if() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) \
               local.get 0 local.get 1 i32.lt_u drop \
               i32.const 1 \
               (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        assert!(
            r.pentagon_facts.is_empty(),
            "intervening op -> no fact: {:?}",
            r.pentagon_facts
        );
    }

    /// Probe B(3): the `if` carries a non-empty block type (params). Does the
    /// stack-param shift mean the compared values aren't the locals named?
    /// Here the if takes one i32 param: stack is [extra, cmp_bool] but the if
    /// pops only the bool as its condition. The folded form `(if (param i32) ...)`
    /// — verify whatever is emitted is still sound (lhs<bound on entry).
    #[test]
    fn adv_if_with_block_params() {
        // push an extra value (local 0), do the guard, if-with-param consumes it.
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) \
               local.get 0 \
               local.get 0 local.get 1 i32.lt_u \
               (if (param i32) (result i32) (then drop i32.const 1) (else drop i32.const 0))))",
        );
        // Pattern: ops are LocalGet0, LocalGet0, LocalGet1, LtU, If. The window
        // starting at the SECOND LocalGet0 matches: lhs=0,bound=Local(1). The
        // guard genuinely holds on entry (the if's condition IS local0<local1),
        // so the fact is sound. Just ensure if a fact exists it is x0<x1.
        for f in &r.pentagon_facts {
            assert_eq!(f.lhs_local, 0);
            assert_eq!(f.bound, PentagonBound::Local(1));
        }
    }

    /// Probe B(5): negative i32 const. `local.get 0; i32.const -1; lt_s; if`
    /// records x0 < -1 (signed). The i32 value -1 must be sign-extended to i64,
    /// NOT recorded as 0xFFFFFFFF.
    #[test]
    fn adv_negative_i32_const() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) \
               local.get 0 i32.const -1 i32.lt_s \
               (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        assert_eq!(r.pentagon_facts.len(), 1);
        assert_eq!(
            r.pentagon_facts[0].bound,
            PentagonBound::Const(-1),
            "i32 -1 must sign-extend to i64 -1, not 4294967295"
        );
        assert!(!r.pentagon_facts[0].unsigned);
    }

    /// Probe B(5b): i64 negative const path.
    #[test]
    fn adv_negative_i64_const() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i64) (result i32) \
               local.get 0 i64.const -5 i64.lt_s \
               (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        assert_eq!(r.pentagon_facts.len(), 1);
        assert_eq!(r.pentagon_facts[0].bound, PentagonBound::Const(-5));
    }

    /// Probe B(2): SEMANTIC soundness of the unsigned guard recorded as a strict
    /// fact. `lt_u` with a NEGATIVE i32 const: local.get 0; i32.const -1; i32.lt_u.
    /// Unsigned, -1 is 0xFFFFFFFF (4294967295). The pass records Const(-1) and
    /// unsigned=true. Is `x0 < -1` (the literal i64 fact) actually true on entry?
    /// CONCRETE: x0 = 0. Unsigned 0 <_u 0xFFFFFFFF is TRUE -> guard taken.
    /// But signed/i64 reading of the fact "x0 < -1" with x0=0 is FALSE.
    /// A consumer reading bound=Const(-1) as a signed i64 bound is MISLED.
    #[test]
    fn adv_unsigned_const_semantic_trap() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) \
               local.get 0 i32.const -1 i32.lt_u \
               (if (result i32) (then i32.const 1) (else i32.const 0))))",
        );
        // Document what is recorded.
        if let Some(f) = r.pentagon_facts.first() {
            std::eprintln!(
                "RECORDED: lhs_local={} bound={:?} unsigned={}",
                f.lhs_local,
                f.bound,
                f.unsigned
            );
            // The literal i64 fact x0 < -1 is FALSE for the entering value x0=0
            // (0 <_u 0xFFFFFFFF holds). So treating Const as a signed i64 bound
            // is unsound. It is only sound under the unsigned reading.
            assert!(
                f.unsigned,
                "MUST flag unsigned so consumer knows the reading"
            );
        }
    }

    /// every back-edge — the live frame is `frame × trip_count`, unbounded.
    /// detect_frame was control-flow-insensitive and reported the single-
    /// iteration frame (16) instead of Unbounded.
    #[test]
    fn feat043_sp_decrement_in_loop_is_unbounded() {
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 65536)) \
               (func (export \"entry\") (local i32) \
                 i32.const 10 local.set 0 \
                 (loop \
                   global.get $sp i32.const 16 i32.sub global.set $sp \
                   local.get 0 i32.const 1 i32.sub local.tee 0 br_if 0) \
                 global.get $sp i32.const 160 i32.add global.set $sp))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Unbounded,
            "an unrestored SP decrement in a loop body must be Unbounded, not a \
             single-iteration frame; got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 (clean-room #6 control): a loop that allocates AND restores the
    /// frame within the SAME iteration (net-zero SP delta) does NOT leak — the
    /// peak live frame is one iteration's worth, so the finite `Bytes(frame)`
    /// bound stays correct. Guards the leak detector against over-flagging.
    #[test]
    fn feat043_balanced_loop_frame_stays_bytes() {
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 65536)) \
               (func (export \"entry\") (local i32) \
                 i32.const 10 local.set 0 \
                 (loop \
                   global.get $sp i32.const 32 i32.sub global.set $sp \
                   global.get $sp i32.const 32 i32.add global.set $sp \
                   local.get 0 i32.const 1 i32.sub local.tee 0 br_if 0)))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Bytes(32),
            "a per-iteration balanced alloc/free must keep the finite single-frame \
             bound; got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room #5): table 0 is HOST-WRITABLE
    /// when imported — the host supplies its slots and scry sees no `table.*`
    /// op, so a `call_indirect 0` may dispatch a host-installed callee of any
    /// frame depth. Must be Unknown, not the function's own frame only.
    #[test]
    fn feat043_imported_table_indirect_is_unknown() {
        let r = analyze_default(
            "(module \
               (import \"env\" \"t\" (table 1 1 funcref)) \
               (global $sp (mut i32) (i32.const 1048576)) \
               (type $ft (func)) \
               (func (export \"entry\") \
                 global.get $sp i32.const 4096 i32.sub global.set $sp \
                 i32.const 0 call_indirect 0 (type $ft) \
                 global.get $sp i32.const 4096 i32.add global.set $sp))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Unknown,
            "an imported (host-writable) table-0 call_indirect must be Unknown; \
             got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room #5): an EXPORTED defined table 0
    /// is held by the host, which can overwrite a slot via the embedder API with
    /// a deeper-framed callee. The declared active-segment target is no longer a
    /// sound enumeration — must be Unknown.
    #[test]
    fn feat043_exported_table_indirect_is_unknown() {
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 1048576)) \
               (table (export \"t\") 1 1 funcref) (elem (i32.const 0) func 0) \
               (type $ft (func)) \
               (func $small (type $ft) \
                 global.get $sp i32.const 16 i32.sub global.set $sp \
                 global.get $sp i32.const 16 i32.add global.set $sp) \
               (func (export \"entry\") \
                 global.get $sp i32.const 4096 i32.sub global.set $sp \
                 i32.const 0 call_indirect (type $ft) \
                 global.get $sp i32.const 4096 i32.add global.set $sp))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Unknown,
            "an exported (host-writable) table-0 call_indirect must be Unknown; \
             got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room #4): a non-growable, active-
    /// elem table-0 looks contents-known from its declaration, but a runtime
    /// `table.set` (or table.copy/fill/init/grow) can overwrite a slot with a
    /// deeper-framed callee. Resolving the call_indirect to the *declared*
    /// target then under-counts the stack. Any table-0 mutation must demote the
    /// table to contents-unknown so the dispatch becomes Unknown.
    #[test]
    fn feat043_runtime_table_mutation_is_unknown() {
        // table 0 is (table 1 1 funcref) — non-growable, active elem slot0=$small —
        // but `entry` overwrites slot0 with $big (frame 4096) via table.set before
        // dispatching. The true peak is entry(4096)+$big(4096); the declared
        // resolution would see only $small(16).
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 1048576)) \
               (table 1 1 funcref) (elem (i32.const 0) func 0) \
               (type $ft (func)) \
               (func $small (type $ft) \
                 global.get $sp i32.const 16 i32.sub global.set $sp \
                 global.get $sp i32.const 16 i32.add global.set $sp) \
               (func $big (export \"big\") (type $ft) \
                 global.get $sp i32.const 4096 i32.sub global.set $sp \
                 global.get $sp i32.const 4096 i32.add global.set $sp) \
               (func (export \"entry\") \
                 global.get $sp i32.const 4096 i32.sub global.set $sp \
                 i32.const 0 ref.func $big table.set 0 \
                 i32.const 0 call_indirect (type $ft) \
                 global.get $sp i32.const 4096 i32.add global.set $sp))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Unknown,
            "a runtime table.set demotes table-0 to contents-unknown; the dispatch \
             must be Unknown, not a finite under-count; got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room #3): a `call_indirect` against
    /// a table scry cannot enumerate — a non-zero table index, or a GROWABLE /
    /// passive-populated table-0 (contents not fully known) — must yield Unknown,
    /// not a false finite bound that drops the dispatched callee's frame.
    #[test]
    fn feat043_unenumerable_indirect_is_unknown() {
        // call_indirect against table 1 (scry models only table 0).
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 65536)) \
               (table $t0 1 1 funcref) (table $t1 1 1 funcref) \
               (elem (table $t1) (i32.const 0) func 0) \
               (type $ft (func)) \
               (func \
                 global.get $sp i32.const 256 i32.sub global.set $sp \
                 global.get $sp i32.const 256 i32.add global.set $sp) \
               (func (export \"entry\") \
                 global.get $sp i32.const 512 i32.sub global.set $sp \
                 i32.const 0 call_indirect $t1 (type $ft) \
                 global.get $sp i32.const 512 i32.add global.set $sp))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Unknown,
            "an unenumerable (table 1) call_indirect must be Unknown, not a finite \
             under-count; got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room #2): a `return_call` (tail
    /// call) was never matched by build_static_call_graph, so its callee was
    /// dropped from the stack weighting (and from recursion/reachability). A
    /// tail call keeps the caller's shadow frame live, so entry(8) → mid(16)
    /// →return_call→ big(256) peaks at 280 — not 256.
    #[test]
    fn feat043_tail_call_counted_in_stack() {
        let r = analyze_default(
            "(module \
               (global $sp (mut i32) (i32.const 65536)) \
               (func \
                 global.get $sp i32.const 256 i32.sub global.set $sp \
                 global.get $sp i32.const 256 i32.add global.set $sp) \
               (func \
                 global.get $sp i32.const 16 i32.sub global.set $sp \
                 return_call 0) \
               (func (export \"entry\") \
                 global.get $sp i32.const 8 i32.sub global.set $sp \
                 call 1 \
                 global.get $sp i32.const 8 i32.add global.set $sp))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Bytes(280),
            "tail call must contribute its callee's frame (8+16+256=280, not 256); got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-043 SOUNDNESS REGRESSION (clean-room #2b): a self `return_call`
    /// (tail recursion) must be flagged recursive ⇒ Unbounded, not a finite
    /// bound (recursion detection rides static_callees, which now sees the
    /// return_call self-edge).
    #[test]
    fn feat043_tail_recursion_is_unbounded() {
        let r = analyze_default(
            "(module (global $sp (mut i32) (i32.const 65536)) \
               (func (export \"loop_tail\") \
                 global.get $sp i32.const 16 i32.sub global.set $sp \
                 return_call 0))",
        );
        assert_eq!(
            r.stack_usage.max_stack_bytes,
            StackBound::Unbounded,
            "tail recursion must be Unbounded, got {:?}",
            r.stack_usage.max_stack_bytes
        );
    }

    /// FEAT-021 slice-1: a 3-deep direct call chain with constant frames sums
    /// along the deepest path (16 + 32 + 8 = 56). The reported bound must equal
    /// the concrete peak (sound + exact here), and per-function frames recorded.
    #[test]
    fn feat021_stack_chain_sums_frames() {
        let res = analyze_fixture("fixture-12-stack-chain.wat");
        assert_eq!(res.stack_usage.sp_global, Some(0), "global 0 is the SP");
        assert_eq!(
            res.stack_usage.max_stack_bytes,
            StackBound::Bytes(56),
            "outer(16) -> mid(32) -> inner(8) = 56"
        );
        // Per-function frames: inner=8, mid=32, outer=16 (func indices 0,1,2).
        let frame = |idx: u32| {
            res.stack_usage
                .functions
                .iter()
                .find(|f| f.func_index == idx)
                .map(|f| f.frame)
        };
        assert_eq!(frame(0), Some(StackBound::Bytes(8)), "inner frame");
        assert_eq!(frame(1), Some(StackBound::Bytes(32)), "mid frame");
        assert_eq!(frame(2), Some(StackBound::Bytes(16)), "outer frame");
        // Soundness: the bound is >= the true peak (56) on the deepest path.
        assert!(matches!(res.stack_usage.max_stack_bytes, StackBound::Bytes(n) if n >= 56));
    }

    /// FEAT-021 slice-1: a self-recursive function (call-graph SCC) has no
    /// finite shadow-stack bound — must report Unbounded, never a finite
    /// under-count.
    #[test]
    fn feat021_stack_recursion_is_unbounded() {
        let res = analyze_fixture("fixture-13-stack-recursion.wat");
        assert_eq!(
            res.stack_usage.max_stack_bytes,
            StackBound::Unbounded,
            "recursion through the shadow stack is unbounded"
        );
    }

    /// FEAT-021 slice-1: a dynamic (variable) frame is not statically known —
    /// must report Unknown (a sound admission), never zero.
    #[test]
    fn feat021_stack_dynamic_frame_is_unknown() {
        let res = analyze_fixture("fixture-14-stack-dynamic.wat");
        let dyn_frame = res
            .stack_usage
            .functions
            .iter()
            .find(|f| f.func_index == 0)
            .map(|f| f.frame);
        assert_eq!(dyn_frame, Some(StackBound::Unknown), "dynamic alloca frame");
        assert_eq!(res.stack_usage.max_stack_bytes, StackBound::Unknown);
    }

    /// FEAT-021 slice-1: a module with no mutable i32 global has no shadow
    /// stack, so the bound is soundly 0 bytes (fixture-01 has no globals).
    #[test]
    fn feat021_no_shadow_stack_is_zero() {
        let res = analyze_fixture("fixture-01-constant-fold.wat");
        assert_eq!(res.stack_usage.sp_global, None);
        assert_eq!(res.stack_usage.max_stack_bytes, StackBound::Bytes(0));
    }

    /// FEAT-022 slice-1: reachable-from-exports is a sound superset — it
    /// INCLUDES an exported function and its (transitive) callees, and EXCLUDES
    /// a function that is neither exported/start nor reachable (so a consumer
    /// may soundly prune the absent one).
    #[test]
    fn feat022_reachable_from_exports() {
        let res = analyze_fixture("fixture-17-reachability.wat");
        // func 0 = $exported (root), func 1 = $helper (called), func 2 = $dead.
        assert!(
            res.reachable_from_exports.contains(&0),
            "exported root must be reachable"
        );
        assert!(
            res.reachable_from_exports.contains(&1),
            "callee of the export must be reachable"
        );
        assert!(
            !res.reachable_from_exports.contains(&2),
            "uncalled non-exported function must NOT be in the reachable set"
        );
        // Sorted, no dups.
        let mut sorted = res.reachable_from_exports.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted, res.reachable_from_exports,
            "set is sorted + deduped"
        );
    }

    /// FEAT-039 SOUNDNESS REGRESSION (clean-room): in an OPEN world a function
    /// reachable only via an escaped funcref (exported table / exported global /
    /// passed to an import) was wrongly OMITTED from reachable_from_exports —
    /// making the SCRY-001 "prune the complement" contract unsound. It must now
    /// be INCLUDED. And in a closed-and-escape-free module, a genuinely dead
    /// function must still be EXCLUDED (the precision the escape gate licenses).
    #[test]
    fn feat039_exported_table_func_is_reachable() {
        // func 0 = main (export); func 1 = F, only in an EXPORTED funcref table,
        // no in-module call_indirect. Host can call_indirect it ⇒ reachable.
        let r = analyze_default(
            "(module (table (export \"t\") 1 funcref) (elem (i32.const 0) 1) \
               (func (export \"main\")) (func (result i32) i32.const 7))",
        );
        assert!(
            r.reachable_from_exports.contains(&1),
            "F in an exported funcref table is host-dispatchable ⇒ reachable; got {:?}",
            r.reachable_from_exports
        );
    }

    #[test]
    fn feat039_exported_global_funcref_is_reachable() {
        // func 1 (F) addressed by ref.func in an exported global's init expr.
        let r = analyze_default(
            "(module (func (export \"main\")) (func (result i32) i32.const 7) \
               (global (export \"g\") funcref (ref.func 1)))",
        );
        assert!(
            r.reachable_from_exports.contains(&1),
            "F held in an exported funcref global is host-callable ⇒ reachable; got {:?}",
            r.reachable_from_exports
        );
    }

    #[test]
    fn feat039_reffunc_to_import_is_reachable() {
        // import cb=0; main=1 (export) passes ref.func 2 to the import; F=2.
        let r = analyze_default(
            "(module (import \"e\" \"cb\" (func (param funcref))) \
               (func (export \"main\") ref.func 2 call 0) \
               (func (result i32) i32.const 7))",
        );
        assert!(
            r.reachable_from_exports.contains(&2),
            "F passed as a funcref to an import can be called back ⇒ reachable; got {:?}",
            r.reachable_from_exports
        );
    }

    #[test]
    fn feat039_closed_world_dead_func_still_excluded() {
        // No table, no ref.func ⇒ callers_fully_known ⇒ tight seed; func 1 dead.
        let r =
            analyze_default("(module (func (export \"main\")) (func (result i32) i32.const 7))");
        assert!(
            !r.reachable_from_exports.contains(&1),
            "a genuinely dead func in a closed/escape-free module must stay pruned; got {:?}",
            r.reachable_from_exports
        );
    }

    /// FEAT-023: the abstract operand-stack is surfaced on each `ProgramPoint`
    /// and is sound over the same interval domain as the locals. In
    /// fixture-18, `i32.const 42; i32.const 7; i32.add` produces program points
    /// whose stack top is the singleton 42 (after the first const) and 49
    /// (after the add) — so a consumer can read a known constant off the stack
    /// top, the operand-stack analogue of a constant local.
    #[test]
    fn feat023_operand_stack_constants() {
        let res = analyze_fixture("fixture-18-operand-stack.wat");
        let points = &res.invariants.points;
        assert!(!points.is_empty(), "fixture-18 must emit program points");

        // The singleton constant on top of the stack after `i32.const 42`.
        let saw_42 = points.iter().any(|p| {
            matches!(
                p.operand_stack.last(),
                Some(AbstractValue::I32Interval(iv)) if iv.lo == 42 && iv.hi == 42
            )
        });
        assert!(
            saw_42,
            "a program point's operand-stack top must be the constant 42"
        );

        // The add result 42 + 7 = 49, again a singleton, on the stack top.
        let saw_49 = points.iter().any(|p| {
            matches!(
                p.operand_stack.last(),
                Some(AbstractValue::I32Interval(iv)) if iv.lo == 49 && iv.hi == 49
            )
        });
        assert!(
            saw_49,
            "the i32.add result 49 must appear as a singleton on the operand-stack top"
        );

        // Soundness/shape: at the point holding [42,7] the stack has depth 2
        // (bottom → top), confirming bottom-to-top ordering is preserved.
        let saw_depth2 = points.iter().any(|p| {
            p.operand_stack.len() == 2
                && matches!(
                    p.operand_stack.first(),
                    Some(AbstractValue::I32Interval(iv)) if iv.lo == 42 && iv.hi == 42
                )
                && matches!(
                    p.operand_stack.last(),
                    Some(AbstractValue::I32Interval(iv)) if iv.lo == 7 && iv.hi == 7
                )
        });
        assert!(
            saw_depth2,
            "after the second const the stack is [42, 7] bottom → top"
        );
    }

    /// FEAT-027: every function index resolves to human-readable metadata —
    /// name (custom `name` section → export → import), imported flag, and
    /// export names — so a consumer can show `$compute` for `func 1`.
    #[test]
    fn feat027_function_meta_names() {
        let res = analyze_fixture("fixture-19-named-functions.wat");
        let meta = &res.function_meta;
        assert_eq!(
            meta.len(),
            3,
            "one entry per function index (1 import + 2 defined)"
        );

        // func 0: imported $log. The name section name wins over the
        // "env.log" import fallback.
        assert_eq!(meta[0].func_index, 0);
        assert!(meta[0].imported, "func 0 is imported");
        assert_eq!(meta[0].name.as_deref(), Some("log"));
        assert!(meta[0].exports.is_empty());

        // func 1: defined $compute, exported "run".
        assert!(!meta[1].imported, "func 1 is defined");
        assert_eq!(meta[1].name.as_deref(), Some("compute"));
        assert!(
            meta[1].exports.iter().any(|e| e == "run"),
            "func 1 is exported as \"run\""
        );

        // func 2: defined $helper, not exported.
        assert!(!meta[2].imported);
        assert_eq!(meta[2].name.as_deref(), Some("helper"));
        assert!(meta[2].exports.is_empty());

        // Sorted by func_index, one entry per index, no gaps.
        for (i, m) in meta.iter().enumerate() {
            assert_eq!(
                m.func_index as usize, i,
                "function_meta is index-ordered, gapless"
            );
        }
    }

    /// FEAT-027: a module with no name section, no exports, and no imports
    /// yields metadata with `None` names — consumers fall back to the index.
    #[test]
    fn feat027_no_names_is_none() {
        // wat emits a name section from `$id`s, so use a numerically-indexed
        // module with no symbolic names / exports / imports.
        let bytes = wat::parse_str("(module (func nop))").expect("assemble");
        let res = analyze(
            bytes,
            AnalysisConfig {
                widening_threshold: Some(3),
                emit_diagnostics: true,
                taint_policy: None,
            },
        )
        .expect("analyze");
        assert_eq!(res.function_meta.len(), 1);
        assert_eq!(res.function_meta[0].name, None, "no name source → None");
        assert!(!res.function_meta[0].imported);
    }

    /// scry#125 (avrabe): `analyze` PANICKED with "index out of bounds: the len
    /// is 0 but the index is 0" on two valid spec-suite modules. A panic inside
    /// the component TRAPS the guest, so a host gets neither arm of
    /// `result<analysis-result, analyze-error>` — the interface's own channel
    /// for "I could not analyse this" is bypassed entirely.
    ///
    /// Root cause: `target()` clamps `relative_depth` with `saturating_sub`, but
    /// nothing guards `labels.len() == 0`. The label stack is pushed only when
    /// ENTERING a block/loop/if, so the function body's own implicit label is
    /// never on it — and a branch at function top level targets exactly that.
    /// `unwind.wast`, one of the two reported modules, is the spec suite's test
    /// for unwinding out of blocks, which is why it found this.
    #[test]
    fn issue125_branch_to_the_function_label_does_not_panic() {
        // `br 0` with no enclosing region targets the function label = return.
        let r = analyze_default("(module (func (export \"f\") br 0))");
        assert_eq!(
            r.function_meta.len(),
            1,
            "the function must still be analysed"
        );

        // The same shape for every branch form that resolves a label, since
        // they share `target()` and a fix that guards only `br` would leave the
        // others live.
        let _ = analyze_default("(module (func (export \"f\") (param i32) local.get 0 br_if 0))");
        let _ =
            analyze_default("(module (func (export \"f\") (param i32) local.get 0 br_table 0 0))");
        // And a branch nested one level deep that targets PAST its own region
        // out to the function label — depth 1 with a single pushed label.
        let _ = analyze_default("(module (func (export \"f\") (block br 1)))");
    }

    /// scry#126 (avrabe): 579 of the fallback diagnostics in a real-world
    /// corpus — the LARGEST bucket, larger than any named operator — said only
    /// `<unsupported>`. A consumer was told THAT analysis degraded but not WHAT
    /// caused it, which makes the diagnostic non-actionable in exactly the case
    /// it exists for.
    ///
    /// The operator is known at the point the fallback is raised, and the
    /// naming helper already existed: `op_report_name` falls back to the Debug
    /// variant name. It was wired into the GAP records but not into this
    /// diagnostic, so the two surfaces disagreed about the same event.
    #[test]
    fn issue126_fallback_diagnostic_names_the_operator() {
        // f64.add is outside the modelled set, so it takes the fallback path.
        // `emit_diagnostics` is OFF in the default config, so the fallback
        // diagnostic is never pushed — using analyze_default here made the test
        // pass its own precondition vacuously the first time.
        let r = analyze(
            wat::parse_str(
                "(module (func (param f64) (result f64) local.get 0 local.get 0 f64.add))",
            )
            .expect("assemble"),
            AnalysisConfig {
                emit_diagnostics: true,
                ..Default::default()
            },
        )
        .expect("analyze");
        let fallbacks: Vec<&Diagnostic> = r
            .diagnostics
            .iter()
            .filter(|d| d.severity == DiagnosticSeverity::UnsoundnessFallback)
            .collect();
        assert!(
            !fallbacks.is_empty(),
            "f64 ops must raise unsoundness fallbacks"
        );
        // The property that matters: NO fallback names a placeholder.
        for d in &fallbacks {
            assert!(
                !d.message.contains("<unsupported>"),
                "every fallback must name its operator: {:?}",
                d.message
            );
        }
        // Non-vacuity: it must name the operators actually present. `f64.const`
        // is itself unmodelled and raises the FIRST fallback — asserting only
        // on `F64Add` made this test fail against a working fix.
        let all = fallbacks
            .iter()
            .map(|d| d.message.as_str())
            .collect::<Vec<_>>()
            .join(" | ");
        // Non-vacuity: it must name the operator actually present. Only ONE
        // fallback fires per function (the scrub degrades the locals once), so
        // the fixture makes f64.add the only unmodelled op — `local.get` is
        // modelled; `f64.const` takes the fallback first and the test would
        // otherwise assert on the wrong operator.
        assert!(all.contains("F64Add"), "must name f64.add: {all}");
        let d = fallbacks[0];
        // The gap record already named it; the two surfaces must now agree, so
        // a consumer correlating them does not see two different events.
        let g = r
            .gaps
            .iter()
            .find(|g| g.pc == d.pc && g.func_index == d.func_index)
            .expect("the same site must carry a gap record");
        assert!(
            d.message.contains(&g.op),
            "diagnostic {:?} must name the same operator as its gap {:?}",
            d.message,
            g.op
        );
    }

    /// scry#126, second site. The taint pass has its OWN "operator not
    /// modelled" diagnostic, and it formatted `op_name` too — so it printed
    /// `<unsupported>` for exactly the population it exists to describe.
    ///
    /// Found by grepping every `op_name` call site after fixing the first one,
    /// rather than assuming the first was the only one. A third site (the
    /// write-set-havoc Info at the `block`/`loop`/`if` opener) is safe, because
    /// `op_name` does cover those three.
    #[test]
    fn issue126_taint_fallback_diagnostic_also_names_the_operator() {
        let r = analyze(
            wat::parse_str(
                "(module (func (param f64) (result f64) local.get 0 local.get 0 f64.add))",
            )
            .expect("assemble"),
            AnalysisConfig {
                emit_diagnostics: true,
                taint_policy: Some(TaintPolicy {
                    high_params: alloc::vec![0],
                    low_results: alloc::vec![0],
                }),
                ..Default::default()
            },
        )
        .expect("analyze");
        let taint: Vec<&Diagnostic> = r
            .diagnostics
            .iter()
            .filter(|d| d.message.starts_with("taint: operator"))
            .collect();
        assert!(
            !taint.is_empty(),
            "the taint pass must report the unmodelled f64.add"
        );
        for d in &taint {
            assert!(
                !d.message.contains("<unsupported>"),
                "the taint fallback must name its operator: {:?}",
                d.message
            );
        }
    }

    /// scry#133: `SCRY_VERSION` was a hand-maintained literal and the v3.2.5
    /// bump missed it, so the SHIPPED 3.2.5 component emitted
    /// `"scry 3.2.4 — wasm-lattice cross-component import alive"`. Consumers
    /// use that string to identify which analyzer produced a result, and both
    /// #125 and #126 were reported against a specific released version — a
    /// component that misreports itself sends a bug report to the wrong build.
    ///
    /// This is the same drift class `claims.yaml` gates in the docs (#97), but
    /// the claim-check gate cannot see a Rust string literal. Deriving the
    /// value is what actually closes it; this test only proves it stays derived.
    #[test]
    fn issue133_scry_version_is_derived_from_the_package_version() {
        // scry#152: the assertion that USED to be here was
        //     assert_eq!(SCRY_VERSION, env!("CARGO_PKG_VERSION"))
        // which is TAUTOLOGICAL, because SCRY_VERSION *is* that expression. It
        // compared a value to itself and could not fail under any build.
        //
        // It was not vacuous when written — red-first it failed honestly with
        // left "3.2.4" / right "3.2.5", because SCRY_VERSION was still a
        // literal. It became vacuous the MOMENT the fix landed, since the fix
        // makes the asserted identity true by construction. A test can be
        // meaningful before a change and worthless after it, and mutation-
        // checking the implementation does not reveal that: reverting to a
        // literal makes it fail, which looks like a healthy oracle.
        //
        // What it failed to catch: rules_rust populates CARGO_PKG_VERSION from
        // the Bazel target's `version` attribute and defaults it to "0.0.0".
        // Bazel builds the SHIPPED component, so v3.2.6 went out announcing
        // "scry 0.0.0" with this test green.
        assert_ne!(
            SCRY_VERSION, "0.0.0",
            "SCRY_VERSION is the rules_rust default — the Bazel target is \
             missing its `version` attribute, and the shipped component will \
             announce 0.0.0 (scry#152)"
        );
        // Non-vacuity: a bare `assert_eq!(X, X)` would pass on any value, so
        // pin the shape too — the released artifact showed this string verbatim.
        assert!(
            SCRY_VERSION.split('.').count() == 3
                && SCRY_VERSION.split('.').all(|p| p.parse::<u32>().is_ok()),
            "expected a three-part numeric version, got {SCRY_VERSION:?}"
        );
    }

    /// scry#121: `havoc_region` never interprets the region body, but recorded a
    /// gap ONLY when the write set was non-empty or the region held a call. So a
    /// typed region that writes no local and calls nothing vanished with no
    /// record of any kind — no trap check, no gap, no advisory.
    ///
    /// That breaks the invariant REQ-017 exists for: every place the analysis is
    /// conservative is recorded as DATA, never as silence. Here scry is
    /// maximally conservative — it interprets nothing — and says nothing.
    ///
    /// It is also a one-line laundering vector: wrapping a flagged expression in
    /// a typed block removed it from the report entirely, no understanding of
    /// any internal scheme required. And it promotes to a WRONG VERDICT in the
    /// adjudicator, which reads "absent from the after-run" as
    /// `removed-with-code` — "the site no longer exists" — while the code is
    /// still there and the obligation still live (DD-021 finding 3).
    #[test]
    fn issue121_havocked_region_always_records_a_gap() {
        // CONTROL FIRST: unwrapped, the obligation is reported. If this ever
        // stops holding, the test below proves nothing about laundering.
        let bare = analyze_default(
            "(module (func (export \"b\") (param i32) (result i32) \
             i32.const 10 local.get 0 i32.div_s))",
        );
        assert!(
            !bare.trap_checks.is_empty(),
            "control: the unwrapped div must raise a trap check"
        );

        // The laundering case: same expression inside a typed block. The block
        // writes NO local and contains NO call, so it took the silent path.
        let wrapped = analyze_default(
            "(module (func (export \"b\") (param i32) (result i32) \
             (block (result i32) i32.const 10 local.get 0 i32.div_s)))",
        );
        assert!(
            !wrapped.gaps.is_empty(),
            "a region that was NEVER INTERPRETED must record a gap — it is \
             maximally conservative, so silence is the one thing it must not be"
        );
        let g = wrapped
            .gaps
            .iter()
            .find(|g| g.kind == GapKind::UnmodeledControlFlow)
            .expect("the havoc must be recorded as unmodelled control flow");
        assert_eq!(g.func_index, 0);

        // Same for a typed `if`, which took the identical path.
        let iffed = analyze_default(
            "(module (func (export \"b\") (param i32) (result i32) \
             local.get 0 (if (result i32) (then i32.const 10 local.get 0 i32.div_s) \
             (else i32.const 1))))",
        );
        assert!(
            iffed
                .gaps
                .iter()
                .any(|g| g.kind == GapKind::UnmodeledControlFlow),
            "a typed `if` havoc must record a gap too"
        );
    }

    fn analyze_default(src: &str) -> AnalysisResult {
        analyze(
            wat::parse_str(src).expect("assemble"),
            AnalysisConfig::default(),
        )
        .expect("analyze")
    }

    /// FEAT-037: masking a value to clear its low bits surfaces a known-bits /
    /// alignment fact on the destination local. `local 1 := (local 0) & 0xFFF8`
    /// ⇒ local 1 has its low 3 bits known-0 (8-aligned) and ≡ 0 (mod 8).
    #[test]
    fn feat037_mask_surfaces_alignment() {
        // func: (param i32) (local i32); local.set 1 (local.get 0 & 0xFFFFFFF8)
        let r = analyze_default(
            "(module (func (param i32) (local i32) \
               local.get 0 i32.const 0xFFFFFFF8 i32.and local.set 1))",
        );
        let f = r
            .bit_facts
            .iter()
            .find(|f| f.local_index == 1)
            .expect("a bit fact for local 1");
        assert_eq!(f.width, 32);
        // low 3 bits known zero.
        assert_eq!(f.known_zeros & 0b111, 0b111, "low 3 bits must be known-0");
        // and the reduced congruence sees ≡ 0 (mod 8).
        assert_eq!(f.cong_modulus, 8, "alignment ⇒ mod 8");
        assert_eq!(f.cong_residue, 0);
    }

    /// FEAT-037: a zero-initialized local OR'd with a constant carries exact
    /// bits. `local 0 := 0 | 5` ⇒ local 0 is the constant 5 (singleton).
    #[test]
    fn feat037_zero_init_local_is_known() {
        // declared local starts at 0; `local.set 0 (local.get 0 | 5)` ⇒ 5.
        let r = analyze_default(
            "(module (func (local i32) \
               local.get 0 i32.const 5 i32.or local.set 0))",
        );
        let f = r
            .bit_facts
            .iter()
            .find(|f| f.local_index == 0)
            .expect("a bit fact for local 0");
        // 0 | 5 = 5 exactly: every bit is known and the value is pinned to 5.
        assert_eq!(f.known_ones, 5, "bits known-1 must be exactly 5");
        assert_eq!(
            f.known_zeros,
            !5u64 & scry_bits::width_mask(32),
            "all other 32 bits must be known-0 (fully pinned to 5)"
        );
        // congruence is exact too: ≡ 5 (mod 0 singleton OR mod 2^32 — both pin
        // a unique 32-bit value).
        assert!(
            f.cong_residue == 5 && (f.cong_modulus == 0 || f.cong_modulus == (1u64 << 32)),
            "congruence must pin the value to 5, got mod {} res {}",
            f.cong_modulus,
            f.cong_residue
        );
    }

    /// FEAT-037 soundness: every emitted bit fact must be a sound
    /// over-approximation — it never fixes a bit both ways, and the congruence
    /// is well-formed. (A deeper concrete-execution cross-check lives in the
    /// scry-bits γ-sweep; here we assert the surfaced facts are well-formed and
    /// the pass is purely additive — produced without touching other output.)
    #[test]
    fn feat037_emitted_facts_are_wellformed() {
        let r = analyze_default(
            "(module (func (param i32) (local i32) \
               local.get 0 i32.const 0xFF00 i32.and i32.const 8 i32.shl local.set 1))",
        );
        for f in &r.bit_facts {
            assert_eq!(
                f.known_zeros & f.known_ones,
                0,
                "a bit cannot be known both 0 and 1: {f:?}"
            );
            if f.cong_modulus >= 2 {
                assert!(
                    f.cong_residue < f.cong_modulus,
                    "residue out of range: {f:?}"
                );
            }
        }
    }

    /// FEAT-037 NON-TERMINATION REGRESSION (clean-room): a zero-init i64 local
    /// OR'd with a wide (40-bit) constant drives `reduce` to meet ⊤ with a
    /// 2^40-modulus congruence. A prior linear residue search in `Cong::meet`
    /// made this O(2^40) — `analyze()` hung. The closed-form CRT combine must
    /// make it return promptly (and soundly).
    #[test]
    fn feat037_wide_or_does_not_hang() {
        let r = analyze_default(
            "(module (func (local i64) \
               local.get 0 i64.const 0xFFFFFFFFFF i64.or local.set 0))",
        );
        // 0 | 0xFFFFFFFFFF = 0xFFFFFFFFFF exactly: low 40 bits known-1.
        let f = r
            .bit_facts
            .iter()
            .find(|f| f.local_index == 0)
            .expect("bit fact for local 0");
        assert_eq!(f.width, 64);
        assert_eq!(f.known_ones, 0xFF_FFFF_FFFF, "low 40 bits known-1");
    }

    /// FEAT-038: under verified `bounded_memory` (no `memory.grow` anywhere),
    /// `memory.size` is the exact constant initial page count — and modelling it
    /// no longer degrades the function (the pre-FEAT-038 fallback scrubbed every
    /// local to ⊤).
    #[test]
    fn feat038_memory_size_constant_when_bounded() {
        // (memory 3), no grow ⇒ memory.size == 3 pages, stored into local 0.
        let r = analyze_default(
            "(module (memory 3) (func (result i32) (local i32) \
               memory.size local.set 0 local.get 0))",
        );
        assert!(r.verified_premises.bounded_memory, "no grow ⇒ bounded");
        let found = r.invariants.points.iter().any(|p| {
            p.locals.iter().any(|l| {
                l.local_index == 0
                    && matches!(&l.value, AbstractValue::I32Interval(iv) if iv.lo == 3 && iv.hi == 3)
            })
        });
        assert!(
            found,
            "memory.size under bounded_memory must make local 0 = [3,3] (not degraded); points={:?}",
            r.invariants.points
        );
    }

    /// FEAT-038: `memory.grow` is modelled (result ∈ [-1, max]) WITHOUT degrading
    /// the function — its bounded result lands in a local instead of ⊤.
    #[test]
    fn feat038_memory_grow_does_not_degrade() {
        // (memory 2 10): grow result ∈ [-1, 10], stored into local 0 (no drop —
        // `drop` is itself unsupported and would degrade).
        let r = analyze_default(
            "(module (memory 2 10) (func (result i32) (local i32) \
               i32.const 1 memory.grow local.set 0 local.get 0))",
        );
        assert!(!r.verified_premises.bounded_memory, "grow ⇒ not bounded");
        let found = r.invariants.points.iter().any(|p| {
            p.locals.iter().any(|l| {
                l.local_index == 0
                    && matches!(&l.value, AbstractValue::I32Interval(iv) if iv.lo == -1 && iv.hi == 10)
            })
        });
        assert!(
            found,
            "memory.grow result must be the bounded [-1,10] (modelled, not degraded); points={:?}",
            r.invariants.points
        );
    }

    /// Does any emitted point bind local 0 to exactly `[v, v]`?
    fn local0_is_const(r: &AnalysisResult, v: i64) -> bool {
        r.invariants.points.iter().any(|p| {
            p.locals.iter().any(|l| {
                l.local_index == 0
                    && matches!(&l.value, AbstractValue::I32Interval(iv) if iv.lo == v && iv.hi == v)
            })
        })
    }

    /// FEAT-058 (slice 2) — the headline capability: store a constant to a
    /// singleton in-bounds i32 address, load it back, and the loaded value is
    /// the tracked interval `[42,42]` instead of the pre-FEAT-058 ⊤.
    #[test]
    fn feat058_store_then_load_round_trips() {
        let r = analyze_default(
            "(module (memory 1) (func (result i32) (local i32) \
               i32.const 16 i32.const 42 i32.store \
               i32.const 16 i32.load local.set 0 local.get 0))",
        );
        assert!(
            local0_is_const(&r, 42),
            "store 42 @16 then load @16 must yield local0=[42,42]; points={:?}",
            r.invariants.points
        );
    }

    /// FEAT-058 soundness — type-punning: an overlapping WIDER store (i64 at 14
    /// covers bytes [14,22) ⊇ 16) must INVALIDATE the tracked i32 cell at 16, so
    /// the later i32 load returns ⊤ — never the stale [42,42].
    #[test]
    fn feat058_overlapping_wider_store_invalidates() {
        let r = analyze_default(
            "(module (memory 1) (func (result i32) (local i32) \
               i32.const 16 i32.const 42 i32.store \
               i32.const 14 i64.const 0 i64.store \
               i32.const 16 i32.load local.set 0 local.get 0))",
        );
        assert!(
            !local0_is_const(&r, 42),
            "overlapping i64 store must invalidate mem[16]; stale [42,42] is UNSOUND; points={:?}",
            r.invariants.points
        );
    }

    /// FEAT-058 soundness — a call between store and load forgets memory content
    /// (a callee may write shared linear memory), so the load returns ⊤.
    #[test]
    fn feat058_call_forgets_memory() {
        let r = analyze_default(
            "(module (memory 1) (func $f) (func (result i32) (local i32) \
               i32.const 16 i32.const 42 i32.store \
               call $f \
               i32.const 16 i32.load local.set 0 local.get 0))",
        );
        assert!(
            !local0_is_const(&r, 42),
            "a call must forget memory content; stale [42,42] is UNSOUND; points={:?}",
            r.invariants.points
        );
    }

    // ── FEAT-057 slice 2a: polyhedra in the fixpoint ────────────────────

    /// Rebuild a `scry_poly::Poly` from a point's surfaced `linear` facts, so
    /// entailment over the OUTPUT (not the internal state) can be checked.
    fn poly_of_linear(linear: &[LinearConstraint], dim: u32) -> scry_poly::Poly {
        let mut p = scry_poly::top(dim);
        for c in linear {
            let mut coeffs = alloc::vec![0i64; dim as usize];
            for t in &c.terms {
                coeffs[t.local_index as usize] = t.coeff;
            }
            p.add_constraint(scry_poly::Constraint {
                coeffs,
                bound: c.bound,
            });
        }
        p
    }

    /// Does the concrete valuation satisfy every surfaced linear constraint
    /// at this point? (The γ-soundness check for the poly OUTPUT.)
    fn linear_holds(linear: &[LinearConstraint], vals: &[i64]) -> bool {
        linear.iter().all(|c| {
            c.terms
                .iter()
                .map(|t| t.coeff as i128 * vals[t.local_index as usize] as i128)
                .sum::<i128>()
                <= c.bound as i128
        })
    }

    /// x, y guard-refined into [0,100] (so no-wrap is provable), then
    /// `z := x + y`. Ops 0..=16 are the block + four constant-guard idioms;
    /// pc 20 is the `local.set 2`.
    const FEAT057_GUARDED_ADD_PREFIX: &str = "block \
           local.get 0 i32.const 0 i32.lt_s br_if 0 \
           local.get 0 i32.const 100 i32.gt_s br_if 0 \
           local.get 1 i32.const 0 i32.lt_s br_if 0 \
           local.get 1 i32.const 100 i32.gt_s br_if 0 \
           local.get 0 local.get 1 i32.add local.set 2 ";

    /// THE ORACLE, both directions (FEAT-057 AC#1): a THREE-variable relation
    /// the octagon provably cannot express. After guard-bounding x,y∈[0,100]
    /// and `z := x + y`, the invariant `x + y − z ≤ 0` holds. The witness
    /// valuation (100, 100, 0) satisfies EVERY fact the octagon side
    /// publishes at that point (all surfaced relational constraints and all
    /// unary interval bounds) yet violates the invariant — so the octagon
    /// output does NOT imply it. The poly output must both ENTAIL the
    /// invariant and EXCLUDE the witness. A test that only checked
    /// `linear` non-empty would pass on a domain emitting garbage; this one
    /// cannot.
    #[test]
    fn feat057_linear_beats_octagon_on_three_var_relation() {
        let r = analyze_default(&alloc::format!(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local i32) \
               {FEAT057_GUARDED_ADD_PREFIX} \
             end \
             local.get 2))"
        ));
        // pc 20 = the `local.set 2` (see the prefix doc comment).
        let p = r
            .invariants
            .points
            .iter()
            .find(|p| p.pc == 20)
            .expect("point at the z := x + y assignment");
        // Direction 1: the poly output entails the invariant (both halves of
        // the equality, so this is not satisfied by an accidental one-sided
        // constraint).
        let poly = poly_of_linear(&p.linear, 3);
        let inv = scry_poly::Constraint {
            coeffs: alloc::vec![1, 1, -1],
            bound: 0,
        };
        let inv_rev = scry_poly::Constraint {
            coeffs: alloc::vec![-1, -1, 1],
            bound: 0,
        };
        assert!(
            poly.entails(&inv) && poly.entails(&inv_rev),
            "linear output must entail z = x + y; got {:?}",
            p.linear
        );
        // Direction 2: the octagon side CANNOT rule out the witness — it
        // satisfies every surfaced relational constraint and every unary
        // interval bound at this point...
        let witness: [i64; 3] = [100, 100, 0];
        for c in &p.relational {
            let (a, b) = (witness[c.a as usize], witness[c.b as usize]);
            let v = match c.kind {
                RelKind::Diff => a - b,
                RelKind::Sum => a + b,
            };
            assert!(
                v <= c.bound,
                "witness must satisfy every octagon constraint (else the \
                 octagon-cannot-express claim is untested); violated {c:?}"
            );
        }
        for l in &p.locals {
            if let AbstractValue::I32Interval(iv) = &l.value {
                let v = witness[l.local_index as usize];
                assert!(
                    iv.lo <= v && v <= iv.hi,
                    "witness must satisfy every interval bound; local {} = {v} \
                     outside [{}, {}]",
                    l.local_index,
                    iv.lo,
                    iv.hi
                );
            }
        }
        // ...while the poly output excludes it.
        assert!(
            !linear_holds(&p.linear, &witness),
            "the linear output must EXCLUDE (100, 100, 0) — x + y − z = 200 > 0"
        );
    }

    /// THE WRAP GATE (FEAT-057 soundness core). `z := x + y` with
    /// x = i32::MAX, y = 1 WRAPS to i32::MIN at run time, so the linear
    /// equality `z = x + y` (over ℤ) is FALSE — the transfer must project z
    /// instead. γ-check: the concrete run's valuation at every pc satisfies
    /// every surfaced linear constraint. Forcing the equality in
    /// unconditionally (ignoring the no-wrap result) makes pc ≥ 7 carry
    /// `x + y − z ≤ 0`, violated by 2147483647 + 1 − (−2147483648) = 2^32.
    /// The no-wrap twin (5 + 7) pins the gate's other side: a gate that
    /// never admits an equality would be inert, not sound.
    #[test]
    fn feat057_wrap_gate_never_admits_unproven_equality() {
        let r = analyze_default(
            "(module (func (export \"f\") (result i32) (local i32 i32 i32) \
               i32.const 2147483647 local.set 0 \
               i32.const 1 local.set 1 \
               local.get 0 local.get 1 i32.add local.set 2 \
               local.get 2))",
        );
        // Concrete valuation after each pc (locals start at 0).
        let vals_at = |pc: u32| -> [i64; 3] {
            match pc {
                0 => [0, 0, 0],
                1 | 2 => [2147483647, 0, 0],
                3..=6 => [2147483647, 1, 0],
                _ => [2147483647, 1, -2147483648],
            }
        };
        assert!(!r.invariants.points.is_empty(), "fixture must emit points");
        for p in &r.invariants.points {
            assert!(
                linear_holds(&p.linear, &vals_at(p.pc)),
                "UNSOUND linear fact at pc {} (the run wraps): {:?}",
                p.pc,
                p.linear
            );
        }
        // No-wrap twin: 5 + 7 cannot wrap, so the equality MUST be admitted
        // (otherwise the gate is inert and the whole domain is dead weight).
        let r2 = analyze_default(
            "(module (func (export \"f\") (result i32) (local i32 i32 i32) \
               i32.const 5 local.set 0 \
               i32.const 7 local.set 1 \
               local.get 0 local.get 1 i32.add local.set 2 \
               local.get 2))",
        );
        let p7 = r2
            .invariants
            .points
            .iter()
            .find(|p| p.pc == 7)
            .expect("point at the no-wrap z := x + y");
        let poly = poly_of_linear(&p7.linear, 3);
        assert!(
            poly.entails(&scry_poly::Constraint {
                coeffs: alloc::vec![1, 1, -1],
                bound: 0,
            }),
            "no-wrap equality must be admitted; got {:?}",
            p7.linear
        );
        // And it must hold on the concrete run (5, 7, 12) — the positive γ.
        assert!(linear_holds(&p7.linear, &[5, 7, 12]));
    }

    /// Relational-guard refinement into the poly (mirroring
    /// `refine_octagon_rel`): the fall-through of `br_if (x < y)` licenses
    /// `y − x ≤ 0`. Direction matters — the classic refinement bug adds the
    /// TAKEN edge's constraint to the fall-through. Checked both ways: the
    /// fall-through point must entail `y − x ≤ 0` (non-vacuity: the
    /// refinement actually fired) AND satisfy the concrete fall-through
    /// valuation (5, 3, 5), which violates the taken edge's `x − y ≤ −1`.
    /// The post-merge point must satisfy BOTH paths' valuations.
    #[test]
    fn feat057_guard_refinement_direction() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local i32) \
               block \
                 local.get 0 local.get 1 i32.lt_s br_if 0 \
                 local.get 0 local.set 2 \
               end \
               local.get 2))",
        );
        // pc 6 = `local.set 2` on the fall-through (x ≥ y) path.
        let p6 = r
            .invariants
            .points
            .iter()
            .find(|p| p.pc == 6)
            .expect("fall-through point at z := x");
        assert!(
            poly_of_linear(&p6.linear, 3).entails(&scry_poly::Constraint {
                coeffs: alloc::vec![-1, 1, 0],
                bound: 0,
            }),
            "fall-through of br_if (x < y) must carry y − x ≤ 0; got {:?}",
            p6.linear
        );
        assert!(
            linear_holds(&p6.linear, &[5, 3, 5]),
            "fall-through run (x, y, z) = (5, 3, 5) violated: {:?}",
            p6.linear
        );
        // pc 8 = post-merge `local.get 2`: both paths' runs must satisfy it
        // (taken: x < y, z still 0).
        let p8 = r
            .invariants
            .points
            .iter()
            .find(|p| p.pc == 8)
            .expect("post-merge point");
        for vals in [[5i64, 3, 5], [3i64, 5, 0]] {
            assert!(
                linear_holds(&p8.linear, &vals),
                "post-merge point keeps a one-sided guard fact, violated by \
                 {vals:?}: {:?}",
                p8.linear
            );
        }
    }

    /// Merge-join soundness at a `block` exit: one path keeps `z = x + y`,
    /// the other reassigns `z := x + 1`. NEITHER fact may survive the merge
    /// alone — a real execution exists against each. γ-check with one
    /// valuation per path at every post-merge pc; drop either merge arm
    /// (keeping the fall-through poly, or replacing with the break state)
    /// and one of the two valuations goes red. Local 3 is a scratch the
    /// post-merge `local.get 2; local.set 3` copy writes — it exists because
    /// `drop` is outside the modelled op set (it would scrub the function)
    /// and a point is only emitted at an interpreted op.
    ///
    /// Non-vacuity is asserted per pc: every checked pc must actually carry a
    /// point (the first draft of the LOOP twin of this test silently checked
    /// zero points — the fixture had degraded upstream).
    #[test]
    fn feat057_merge_join_drops_one_sided_facts() {
        let r = analyze_default(&alloc::format!(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local i32 i32) \
               {FEAT057_GUARDED_ADD_PREFIX} \
               block \
                 local.get 1 br_if 0 \
                 local.get 0 i32.const 1 i32.add local.set 2 \
               end \
               local.get 2 local.set 3 \
             end \
             local.get 2))"
        ));
        // Non-vacuity: the fall-through path's `z := x + 1` (pc 27) must
        // itself carry a 2-variable fact, or this fixture exercises nothing.
        let p27 = r
            .invariants
            .points
            .iter()
            .find(|p| p.pc == 27)
            .expect("point at z := x + 1");
        assert!(
            poly_of_linear(&p27.linear, 4).entails(&scry_poly::Constraint {
                coeffs: alloc::vec![-1, 0, 1, 0],
                bound: 1,
            }),
            "z := x + 1 must yield z − x ≤ 1 pre-merge; got {:?}",
            p27.linear
        );
        // Post-merge pcs, with the concrete per-path valuation at each:
        // path 1 (y = 2 ≠ 0, branch taken): z = x + y = 7;
        // path 2 (y = 0, fall through):     z = x + 1 = 6.
        // The scratch (local 3) is 0 until the pc-30 copy executes.
        let checks: [(u32, [i64; 4], [i64; 4]); 3] = [
            (29, [5, 2, 7, 0], [5, 0, 6, 0]), // local.get 2
            (30, [5, 2, 7, 7], [5, 0, 6, 6]), // local.set 3
            (32, [5, 2, 7, 7], [5, 0, 6, 6]), // final local.get 2
        ];
        for (pc, v1, v2) in checks {
            let p = r
                .invariants
                .points
                .iter()
                .find(|p| p.pc == pc)
                .unwrap_or_else(|| panic!("post-merge point at pc {pc} must exist"));
            for vals in [v1, v2] {
                assert!(
                    linear_holds(&p.linear, &vals),
                    "post-merge pc {pc} keeps a one-sided fact, violated by {vals:?}: {:?}",
                    p.linear
                );
            }
        }
    }

    /// Loop-header join soundness: `z = x + y` holds at loop ENTRY but the
    /// body reassigns `z := x + 1`, so from iteration 2 on the entry fact is
    /// FALSE at the header. The header state must be entry ⊔ back-edge;
    /// seeding each pass from the entry poly alone keeps the stale equality
    /// and the iteration-2 valuation refutes it. γ-check at the header point
    /// (pc 24, the first body op — a `local.get 2; local.set 4` copy into a
    /// scratch, because `drop` is outside the modelled op set) with the
    /// concrete iteration-1 AND iteration-2 states.
    #[test]
    fn feat057_loop_backedge_kills_stale_equality() {
        let r = analyze_default(&alloc::format!(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local i32 i32 i32) \
               {FEAT057_GUARDED_ADD_PREFIX} \
               i32.const 0 local.set 3 \
               loop \
                 local.get 2 local.set 4 \
                 local.get 0 i32.const 1 i32.add local.set 2 \
                 local.get 3 i32.const 1 i32.add local.set 3 \
                 local.get 3 i32.const 2 i32.lt_s br_if 0 \
               end \
             end \
             local.get 2))"
        ));
        // Run x = 5, y = 3 (locals: 2 = z, 3 = i, 4 = scratch):
        //   iteration 1 reaches pc 24 with (5, 3, 8, 0, 0);
        //   iteration 2 reaches it with z = x + 1 = 6, i = 1, scratch = 8.
        let p = r
            .invariants
            .points
            .iter()
            .find(|p| p.pc == 24)
            .expect("loop header point must be emitted");
        for vals in [[5i64, 3, 8, 0, 0], [5i64, 3, 6, 1, 8]] {
            assert!(
                linear_holds(&p.linear, &vals),
                "stale fact at the loop header, violated by {vals:?}: {:?}",
                p.linear
            );
        }
    }

    /// First non-empty obligation id recorded for `func`.
    fn adv_id(r: &AnalysisResult, func: u32) -> String {
        r.advisories
            .iter()
            .find(|a| a.func_index == func && !a.obligation_id.is_empty())
            .unwrap_or_else(|| {
                panic!(
                    "an advisory with an id for func {func}; got {:?}",
                    r.advisories
                )
            })
            .obligation_id
            .clone()
    }

    /// FEAT-064 AC#1 (REQ-020) — an edit in an UNRELATED function must not
    /// disturb this function's obligation identity.
    #[test]
    fn feat064_id_survives_edit_in_unrelated_function() {
        let base = analyze_default(
            "(module \
               (func (export \"a\") (param i32) (result i32) i32.const 10 local.get 0 i32.div_s) \
               (func (export \"b\") (param i32) (result i32) i32.const 20 local.get 0 i32.div_s))",
        );
        // Function "a" grows two instructions; "b" is untouched.
        let edited = analyze_default(
            "(module \
               (func (export \"a\") (param i32) (result i32) \
                 i32.const 7 local.set 0 i32.const 10 local.get 0 i32.div_s) \
               (func (export \"b\") (param i32) (result i32) i32.const 20 local.get 0 i32.div_s))",
        );
        assert_eq!(
            adv_id(&base, 1),
            adv_id(&edited, 1),
            "an edit in another function must not change func 1's obligation id"
        );
    }

    /// FEAT-064 AC#2 — pc-shift immunity: inserting instructions EARLIER in the
    /// SAME function must not change the identity of a later site. This is the
    /// property `(func_index, pc)` cannot provide, and the one the fix-verify
    /// loop depends on.
    #[test]
    fn feat064_id_survives_pc_shift_in_same_function() {
        let base = analyze_default(
            "(module (func (export \"b\") (param i32) (result i32) (local i32) \
               i32.const 20 local.get 0 i32.div_s))",
        );
        // The inserted code writes a DIFFERENT local, so the observed div keeps
        // the same class and code — an insertion that changed the divisor would
        // legitimately change the identity and prove nothing about pc-shift.
        let shifted = analyze_default(
            "(module (func (export \"b\") (param i32) (result i32) (local i32) \
               i32.const 99 local.set 1 i32.const 20 local.get 0 i32.div_s))",
        );
        // The div moved from pc 2 to pc 4 …
        let base_pc = base
            .advisories
            .iter()
            .find(|a| a.func_index == 0)
            .map(|a| a.pc);
        let shifted_pc = shifted
            .advisories
            .iter()
            .find(|a| a.func_index == 0)
            .map(|a| a.pc);
        assert_ne!(base_pc, shifted_pc, "fixture must actually shift the pc");
        // … but its identity did not.
        assert_eq!(
            adv_id(&base, 0),
            adv_id(&shifted, 0),
            "a pc shift within the same function must not change the obligation id"
        );
    }

    /// FEAT-064 (clean-room finding) — ONE operator can raise SEVERAL
    /// obligations: an `i32.div_s` with an unknown divisor raises both
    /// div-by-zero and signed-overflow at the same pc. The site alone therefore
    /// does not discriminate, and two obligations sharing an id would make the
    /// FEAT-065 adjudicator conflate them.
    #[test]
    fn feat064_two_obligations_at_one_pc_get_distinct_ids() {
        let r = analyze_default(
            "(module (func (export \"b\") (param i32) (result i32) \
               local.get 0 local.get 0 i32.div_s))",
        );
        let at_pc: Vec<(&str, &str)> = r
            .advisories
            .iter()
            .filter(|a| !a.obligation_id.is_empty())
            .map(|a| (a.code.as_str(), a.obligation_id.as_str()))
            .collect();
        assert!(
            at_pc.len() >= 2,
            "fixture must raise several obligations; got {at_pc:?}"
        );
        let mut ids: Vec<&str> = at_pc.iter().map(|(_, i)| *i).collect();
        ids.sort_unstable();
        let before = ids.len();
        ids.dedup();
        assert_eq!(
            ids.len(),
            before,
            "distinct obligations must not share an id; got {at_pc:?}"
        );
    }

    /// FEAT-064 anti-vacuity — the id must actually DISCRIMINATE. Two distinct
    /// div sites in one function must not collapse to the same identity, or the
    /// "survives the edit" tests above would pass on a constant.
    #[test]
    fn feat064_distinct_sites_get_distinct_ids() {
        let r = analyze_default(
            "(module (func (export \"b\") (param i32) (result i32) \
               i32.const 10 local.get 0 i32.div_s \
               i32.const 20 local.get 0 i32.div_s i32.add))",
        );
        let ids: Vec<&String> = r
            .advisories
            .iter()
            .filter(|a| a.func_index == 0 && !a.obligation_id.is_empty())
            .map(|a| &a.obligation_id)
            .collect();
        assert!(
            ids.len() >= 2,
            "fixture must yield two advisories; got {ids:?}"
        );
        assert_ne!(ids[0], ids[1], "distinct sites must get distinct ids");
    }

    /// FEAT-070 (REQ-020) — guard refinement for `br_if` on a BARE value.
    /// `local.tee $i; br_if` is the count-to-zero loop LLVM emits: it branches
    /// while the value is non-zero, so the FALL-THROUGH edge pins the local to
    /// exactly 0. Before FEAT-070 scry matched only comparison-guarded idioms
    /// (`local.get L; const C; cmp; br_if` / `local.get L; i32.eqz; br_if`),
    /// so this shape left the counter unrefined.
    ///
    /// The assertion is deliberately position-specific: `(local i32)` is
    /// zero-initialised, so an "any point has [0,0]" predicate passes VACUOUSLY
    /// on the entry point and tests nothing (caught by running this oracle red
    /// before implementing).
    #[test]
    fn feat070_brif_on_bare_tee_pins_fallthrough_to_zero() {
        let r = analyze_default(
            "(module (func (export \"run\") (result i32) (local i32) \
               i32.const 5 local.set 0 \
               block loop \
                 local.get 0 i32.const 1 i32.sub local.tee 0 \
                 br_if 0 \
               end end \
               local.get 0))",
        );
        // The LAST emitted point is after the loop; the only way out of the
        // loop is br_if falling through, i.e. the counter is exactly 0 there.
        let last = r
            .invariants
            .points
            .iter()
            .max_by_key(|p| p.pc)
            .expect("at least one program point");
        let l0 = last
            .locals
            .iter()
            .find(|l| l.local_index == 0)
            .expect("local 0 present");
        assert!(
            matches!(&l0.value, AbstractValue::I32Interval(iv) if iv.lo == 0 && iv.hi == 0),
            "post-loop local 0 must be pinned to [0,0] by the br_if fall-through; \
             got {:?} at pc={}",
            l0.value,
            last.pc
        );
    }

    /// FEAT-070 — the peephole must keep the modelled operand stack balanced.
    /// `local.tee` consumes an incoming stack value that `local.get` does not,
    /// so a shape-blind skip of the idiom leaks (or underflows) the stack.
    #[test]
    fn feat070_tee_guard_keeps_operand_stack_balanced() {
        let r = analyze_default(
            "(module (func (export \"run\") (result i32) (local i32) \
               i32.const 3 local.set 0 \
               block loop \
                 local.get 0 i32.const 1 i32.sub local.tee 0 \
                 br_if 0 \
               end end \
               i32.const 7))",
        );
        let last = r
            .invariants
            .points
            .iter()
            .max_by_key(|p| p.pc)
            .expect("at least one program point");
        // Exactly the `i32.const 7` is live at the end. A leaked tee value
        // would leave 2; an underflow would have degraded the function.
        assert_eq!(
            last.operand_stack.len(),
            1,
            "operand stack must carry exactly the final const; got {:?} at pc={}",
            last.operand_stack,
            last.pc
        );
    }

    /// FEAT-062 — the tracked memory content is SURFACED on the program points
    /// (so scry-viz can render it). A `i32.store 42 @16` records the cell
    /// [16,17) → [42,42]; it must appear in `point.memory`.
    #[test]
    fn feat062_memory_content_surfaced_in_points() {
        let r = analyze_default(
            "(module (memory 1) (func (result i32) (local i32) \
               i32.const 16 i32.const 42 i32.store \
               i32.const 16 i32.load local.set 0 local.get 0))",
        );
        let found = r.invariants.points.iter().any(|p| {
            p.memory
                .iter()
                .any(|m| m.lo == 16 && m.hi == 17 && m.value.lo == 42 && m.value.hi == 42)
        });
        assert!(
            found,
            "the [16,17)→[42,42] memory cell must be surfaced on a point; points={:?}",
            r.invariants.points
        );
    }

    /// The abstract `memory.size` value via a one-function `(func (result i32)
    /// memory.size)` — read off the function summary, unambiguous (no pre-set
    /// program-point to confuse with the result).
    #[cfg(test)]
    fn memory_size_value(module_src: &str) -> AbstractValue {
        let r = analyze_default(module_src);
        // The defined function returning memory.size is the last summary.
        r.function_summaries
            .last()
            .and_then(|s| s.result_summary.first().cloned())
            .expect("a result summary with the memory.size value")
    }

    /// FEAT-038 SOUNDNESS REGRESSION (clean-room #A): an IMPORTED memory is
    /// host-supplied — true size ≥ declared minimum and the host may grow it.
    /// `memory.size` must be `[initial, max]`, never the constant (and never the
    /// `[0,0]` an un-captured import default would give).
    #[test]
    fn feat038_imported_memory_size_not_constant() {
        let v = memory_size_value(
            "(module (import \"env\" \"mem\" (memory 1)) \
               (func (result i32) memory.size))",
        );
        match v {
            AbstractValue::I32Interval(iv) => {
                assert_eq!(iv.lo, 1, "imported (memory 1) ⇒ size ≥ 1, never 0: {iv:?}");
                assert!(iv.hi > 1, "host may grow ⇒ not a constant: {iv:?}");
            }
            other => panic!("expected a sound bounded interval, got {other:?}"),
        }
    }

    /// FEAT-038 soundness reasoning (clean-room #B, resolved): a functional
    /// import canNOT grow this module's PRIVATE memory — in core Wasm an
    /// imported `(func)` has no handle to a non-imported/exported/shared memory
    /// (memory is not a first-class value that can be passed). Only this
    /// module's defined code can grow a private memory, which `bounded_memory`
    /// already rules out. So the constant `[1,1]` here is SOUND despite the
    /// functional import — the gate does not (and need not) require closed_world.
    #[test]
    fn feat038_private_memory_constant_despite_import() {
        let v = memory_size_value(
            "(module (import \"env\" \"f\" (func)) (memory 1) \
               (func (result i32) call 0 memory.size))",
        );
        match v {
            AbstractValue::I32Interval(iv) => assert!(
                iv.lo == 1 && iv.hi == 1,
                "private memory + grow-free module ⇒ size is the constant 1 \
                 (an import cannot reach a private memory): {iv:?}"
            ),
            other => panic!("expected [1,1], got {other:?}"),
        }
    }

    /// FEAT-038: an EXPORTED memory is host-growable via the embedder API, so
    /// even with no in-module grow `memory.size` is not a constant.
    #[test]
    fn feat038_exported_memory_size_not_constant() {
        let v = memory_size_value(
            "(module (memory 1) (export \"mem\" (memory 0)) \
               (func (result i32) memory.size))",
        );
        if let AbstractValue::I32Interval(iv) = v {
            assert!(
                !(iv.lo == 1 && iv.hi == 1),
                "exported memory is host-growable ⇒ not the constant 1: {iv:?}"
            );
        }
    }

    /// FEAT-038 SOUNDNESS REGRESSION (clean-room #1): a 64-bit memory grows to
    /// 2^48 pages, not the memory32 cap of 65536. An exported memory64 (host-
    /// growable, so not a constant) must report `memory.size ∈ [1, 2^48]` as an
    /// i64 — the prior `unwrap_or(65536)` under-approximated.
    #[test]
    fn feat038_memory64_ceiling() {
        let v = memory_size_value(
            "(module (memory i64 1) (export \"m\" (memory 0)) \
               (func (result i64) memory.size))",
        );
        match v {
            AbstractValue::I64Interval(iv) => {
                assert_eq!(iv.lo, 1);
                assert_eq!(
                    iv.hi,
                    1i64 << 48,
                    "memory64 ceiling is 2^48 pages, not 65536"
                );
            }
            other => {
                panic!("memory64 memory.size must be an i64 interval [1, 2^48], got {other:?}")
            }
        }
    }

    /// FEAT-038 SOUNDNESS REGRESSION (clean-room #2/#3): scry captures only
    /// memory index 0 and does not model multi-memory, so `memory.size` in a
    /// module with >1 memory is ⊤ (never memory 0's bounds reused for another
    /// memidx, and never an imported memory 0's min clobbered by a defined one).
    #[test]
    fn feat038_multimemory_is_top() {
        // memidx 1 read against a 2-memory module ⇒ ⊤ (Unknown), not [1,..].
        let v = memory_size_value(
            "(module (memory 1 5) (memory 3 9) (func (result i32) memory.size 1))",
        );
        assert!(
            matches!(v, AbstractValue::Unknown),
            "multi-memory memory.size must be ⊤ (only index 0 of a single-memory \
             module is modelled), got {v:?}"
        );
    }

    /// FEAT-040: an unsupported operator that degrades the function to ⊤ is
    /// recorded as an explicit Gap — not emitted as silence — so an assessor /
    /// AI agent can enumerate where scry gave up.
    #[test]
    fn feat040_unsupported_op_recorded_as_gap() {
        // f64.add is outside scry's modelled set ⇒ the function degrades to ⊤.
        let r = analyze_default(
            "(module (func (param f64 f64) (result f64) \
               local.get 0 local.get 1 f64.add))",
        );
        let g = r
            .gaps
            .iter()
            .find(|g| g.func_index == 0)
            .expect("a gap for the unsupported f64.add");
        assert_eq!(g.kind, GapKind::UnsupportedOp);
        assert!(
            g.op != "<unsupported>" && g.op.to_lowercase().contains("f64"),
            "gap should name the unsupported op (f64.*), got {:?}",
            g.op
        );
    }

    /// FEAT-040 completeness: a non-unsupported-op degradation (an unmodelled
    /// `br_table`) is ALSO recorded — degradation can't be silent (scrub_to_top
    /// requires a Gap by signature).
    #[test]
    fn feat040_br_table_recorded_as_gap() {
        let r = analyze_default(
            "(module (func (param i32) (block (block \
               local.get 0 br_table 0 1 0))))",
        );
        let g = r.gaps.iter().find(|g| g.func_index == 0);
        if let Some(g) = g {
            assert_eq!(
                g.kind,
                GapKind::UnmodeledBranch,
                "br_table ⇒ UnmodeledBranch gap, got {g:?}"
            );
        } else {
            panic!("br_table must record a gap; gaps={:?}", r.gaps);
        }
    }

    /// FEAT-040 completeness (clean-room finding): write-set havoc of an
    /// unmodelled control-flow region (a typed `if`) is now recorded — it is a
    /// partial give-up that previously left no gap.
    #[test]
    fn feat040_control_flow_havoc_recorded_as_gap() {
        let r = analyze_default(
            "(module (func (param i32) (local i32) \
               i32.const 5 local.set 1 \
               local.get 0 (if (then i32.const 9 local.set 1))))",
        );
        assert!(
            r.gaps
                .iter()
                .any(|g| g.kind == GapKind::UnmodeledControlFlow),
            "write-set havoc of the if-region must record an UnmodeledControlFlow gap; got {:?}",
            r.gaps
        );
    }

    /// FEAT-040: a fully-modelled function produces NO gaps (no false "gave up").
    #[test]
    fn feat040_modelled_function_has_no_gaps() {
        let r = analyze_default(
            "(module (func (param i32) (result i32) local.get 0 i32.const 1 i32.add))",
        );
        assert!(
            r.gaps.is_empty(),
            "a fully-modelled i32 function must report no gaps, got {:?}",
            r.gaps
        );
    }

    /// FEAT-040: gaps are emitted even with the default config
    /// (emit_diagnostics = false) — the gap report is independent of verbose
    /// diagnostics.
    #[test]
    fn feat040_gaps_independent_of_emit_diagnostics() {
        let r = analyze(
            wat::parse_str("(module (func (result f64) f64.const 1 f64.const 2 f64.add))")
                .expect("assemble"),
            AnalysisConfig::default(), // emit_diagnostics = false
        )
        .expect("analyze");
        assert!(
            !r.gaps.is_empty(),
            "gaps must populate even with default (no-diagnostics) config"
        );
        assert!(
            r.diagnostics.is_empty(),
            "default config emits no diagnostics"
        );
    }

    /// FEAT-034: scry determines its OWN fusion premises (verify-not-trust):
    /// bounded_memory = no `memory.grow`; closed_world = no functional imports.
    #[test]
    fn feat034_verified_premises() {
        // memory.grow present → not bounded.
        let g = analyze_default(
            "(module (memory 1) (func (export \"g\") (result i32) i32.const 1 memory.grow))",
        );
        assert!(
            !g.verified_premises.bounded_memory,
            "memory.grow ⇒ not bounded"
        );

        // memory, no grow, no imports → bounded + closed.
        let b = analyze_default("(module (memory 1) (func (export \"f\") nop))");
        assert!(b.verified_premises.bounded_memory, "no grow ⇒ bounded");
        assert!(
            b.verified_premises.closed_world,
            "no imports ⇒ closed world"
        );

        // a functional import → scry cannot prove closed world.
        let i = analyze_default("(module (import \"env\" \"h\" (func)) (func (export \"f\") nop))");
        assert!(
            !i.verified_premises.closed_world,
            "functional import ⇒ not provably closed"
        );
        assert!(
            i.verified_premises.bounded_memory,
            "no memory/grow ⇒ vacuously bounded"
        );
    }

    /// FEAT-034: a meld v3 premise asserting bounded_memory on a module that
    /// contains memory.grow is rejected with a disagreement diagnostic, and
    /// scry keeps its own (unbounded) determination.
    #[test]
    fn feat034_rejects_false_bounded_memory_premise() {
        // Module with memory.grow.
        let mut module = wat::parse_str(
            "(module (memory 1) (func (export \"g\") (result i32) i32.const 1 memory.grow))",
        )
        .expect("assemble");
        // Append a component-provenance v3 section asserting bounded_memory=true.
        let section = scry_provenance::ProvenanceSection {
            premises: scry_provenance::FusionPremises {
                bounded_memory: true,
                closed_world: false,
            },
            fused_module_sha256: [0u8; 32],
            origins: alloc::vec![],
        };
        let payload = scry_provenance::encode(&section);
        let name = scry_provenance::SECTION_NAME.as_bytes();
        let mut body = alloc::vec![];
        write_uleb128(&mut body, name.len() as u64);
        body.extend_from_slice(name);
        body.extend_from_slice(&payload);
        module.push(0x00); // custom section id
        write_uleb128(&mut module, body.len() as u64);
        module.extend_from_slice(&body);

        let res = analyze(
            module,
            AnalysisConfig {
                widening_threshold: Some(3),
                emit_diagnostics: true,
                taint_policy: None,
            },
        )
        .expect("analyze");
        // scry kept its own determination (not bounded), despite the premise.
        assert!(!res.verified_premises.bounded_memory);
        // and flagged the disagreement.
        assert!(
            res.diagnostics
                .iter()
                .any(|d| d.message.contains("premise rejected")),
            "expected a bounded_memory disagreement diagnostic"
        );
    }

    fn write_uleb128(out: &mut Vec<u8>, mut value: u64) {
        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            out.push(byte);
            if value == 0 {
                break;
            }
        }
    }

    /// FEAT-036: a non-exported, only-directly-called function's parameter
    /// ranges are the JOIN of the arguments at every call site.
    #[test]
    fn feat036_interproc_param_ranges() {
        // $callee (func 0) is called with 5 and with 10; not exported / not
        // indirect → params bounded by the join 5 ⊔ 10 = [5, 10].
        let r = analyze_default(
            "(module \
             (func (param i32) (result i32) local.get 0) \
             (func (export \"a\") (result i32) i32.const 5 call 0) \
             (func (export \"b\") (result i32) i32.const 10 call 0))",
        );
        let callee = r
            .function_summaries
            .iter()
            .find(|f| f.func_index == 0)
            .expect("callee summary");
        assert_eq!(callee.param_count, 1);
        assert!(
            matches!(
                callee.param_ranges.first(),
                Some(AbstractValue::I32Interval(iv)) if iv.lo == 5 && iv.hi == 10
            ),
            "param range must be the join of call-site args [5,10], got {:?}",
            callee.param_ranges
        );
    }

    /// FEAT-036 soundness: an EXPORTED function has unknown external arguments,
    /// so its parameter ranges must be ⊤ — never narrowed.
    #[test]
    fn feat036_exported_params_are_top() {
        let r =
            analyze_default("(module (func (export \"f\") (param i32) (result i32) local.get 0))");
        let f = r
            .function_summaries
            .iter()
            .find(|f| f.func_index == 0)
            .unwrap();
        assert!(
            matches!(f.param_ranges.first(), Some(AbstractValue::Unknown)),
            "exported function params must be ⊤ (unknown external args), got {:?}",
            f.param_ranges
        );
    }

    /// FEAT-036 SOUNDNESS REGRESSION (clean-room finding): a function called
    /// directly with a constant, in a module that ALSO contains a
    /// `call_indirect` (and therefore a table), must keep ⊤ params. scry's
    /// static table model under-reports indirect targets, so the directly-
    /// called function could ALSO be reached indirectly with an unbounded
    /// argument. The gate forces every param to ⊤ as soon as the module bears
    /// a funcref container. Without this, `param_ranges` would narrow $callee
    /// to the single direct-call constant [7,7] — an UNSOUND under-approx.
    #[test]
    fn feat036_indirect_call_forces_top() {
        // func 0 ($callee): called directly with 7 below.
        // func 2 (exported "ind"): contains a `call_indirect` — and the module
        // declares a table — so callers are not fully known → no narrowing.
        let r = analyze_default(
            "(module \
             (type $t (func (param i32) (result i32))) \
             (table 1 funcref) \
             (func (param i32) (result i32) local.get 0) \
             (func (export \"direct\") (result i32) i32.const 7 call 0) \
             (func (export \"ind\") (param i32) (result i32) \
               local.get 0 \
               local.get 0 \
               call_indirect (type $t)))",
        );
        // sanity: the module really did produce an indirect edge.
        assert!(
            r.call_graph.iter().any(|e| e.indirect),
            "fixture must contain a call_indirect edge"
        );
        let callee = r
            .function_summaries
            .iter()
            .find(|f| f.func_index == 0)
            .expect("callee summary");
        assert_eq!(callee.param_count, 1);
        assert!(
            matches!(callee.param_ranges.first(), Some(AbstractValue::Unknown)),
            "a module bearing a funcref table must leave ALL param ranges ⊤ \
             (the directly-called func could be an unseen indirect target), \
             got {:?}",
            callee.param_ranges
        );
    }

    /// FEAT-036 SOUNDNESS REGRESSION (clean-room counterexample #1): an EXPORTED
    /// funcref table lets the HOST `call_indirect` a defined function with
    /// arbitrary arguments, even though the module itself has NO `call_indirect`
    /// (so an edge-based gate sees nothing). The table's mere presence must
    /// force ⊤. Without the fix, func 0 narrows to the single direct call [42].
    #[test]
    fn feat036_exported_table_forces_top() {
        let r = analyze_default(
            "(module \
             (table (export \"t\") 1 funcref) \
             (elem (i32.const 0) 0) \
             (func (param i32) (result i32) local.get 0) \
             (func (export \"run\") (result i32) i32.const 42 call 0))",
        );
        let callee = r
            .function_summaries
            .iter()
            .find(|f| f.func_index == 0)
            .expect("callee summary");
        assert!(
            matches!(callee.param_ranges.first(), Some(AbstractValue::Unknown)),
            "a function in an exported funcref table is host-reachable with \
             unknown args ⇒ params must be ⊤, got {:?}",
            callee.param_ranges
        );
    }

    /// FEAT-036 SOUNDNESS REGRESSION (clean-room counterexample #2 generalized):
    /// a `ref.func` materializes a callable reference to a defined function that
    /// can escape (to a table, a global, the host, or a `call_ref`) beyond the
    /// direct call sites scry recorded. Its presence must force ⊤ even with no
    /// table-section table. Here func 0 is called directly with 7 and also has
    /// its address taken via `ref.func`.
    #[test]
    fn feat036_ref_func_forces_top() {
        let r = analyze_default(
            "(module \
             (func (param i32) (result i32) local.get 0) \
             (func (export \"take\") (result funcref) ref.func 0) \
             (func (export \"direct\") (result i32) i32.const 7 call 0))",
        );
        let callee = r
            .function_summaries
            .iter()
            .find(|f| f.func_index == 0)
            .expect("callee summary");
        assert!(
            matches!(callee.param_ranges.first(), Some(AbstractValue::Unknown)),
            "a function whose address is taken via ref.func can be called \
             indirectly with unknown args ⇒ params must be ⊤, got {:?}",
            callee.param_ranges
        );
    }

    /// FEAT-036 SOUNDNESS REGRESSION (clean-room counterexample #3): a `ref.func`
    /// in a GLOBAL init expression takes a defined function's address with NO
    /// table and NO `ref.func` in any function BODY — so a body-only scan misses
    /// it. The exported global hands func 0's reference to the host, which can
    /// `call_ref` it with arbitrary args. Must force ⊤; without the fix func 0
    /// narrows to the single direct call [7,7].
    #[test]
    fn feat036_global_init_ref_func_forces_top() {
        let r = analyze_default(
            "(module \
             (func (param i32) (result i32) local.get 0) \
             (global (export \"g\") funcref (ref.func 0)) \
             (func (export \"direct\") (result i32) i32.const 7 call 0))",
        );
        let callee = r
            .function_summaries
            .iter()
            .find(|f| f.func_index == 0)
            .expect("callee summary");
        assert!(
            matches!(callee.param_ranges.first(), Some(AbstractValue::Unknown)),
            "a function whose address is taken in a global init expr escapes to \
             the host ⇒ params must be ⊤, got {:?}",
            callee.param_ranges
        );
    }

    /// FEAT-021 slice-2b: the self-measuring fixture (two mutable i32 globals:
    /// SP=0 + min_sp=1) must still resolve SP to global 0 and report the chain
    /// bound 32+16 = 48 — the min-recording `global.get SP` reads (not followed
    /// by `i32.sub`) do not perturb frame detection.
    #[test]
    fn feat021_measured_chain_bound() {
        let res = analyze_fixture("fixture-16-stack-measured.wat");
        assert_eq!(
            res.stack_usage.sp_global,
            Some(0),
            "SP is global 0 despite min_sp"
        );
        assert_eq!(
            res.stack_usage.max_stack_bytes,
            StackBound::Bytes(48),
            "entry(32) -> deep(16) = 48"
        );
    }

    /// FEAT-021 slice-1 SOUNDNESS REGRESSION (clean-room finding): a constant
    /// prologue frame PLUS a later dynamic `alloca` decrement must be Unknown —
    /// reporting the constant 16 would under-count the true `16 + param` peak.
    #[test]
    fn feat021_const_frame_plus_dynamic_is_unknown() {
        let res = analyze_fixture("fixture-15-stack-alloca.wat");
        let f = res
            .stack_usage
            .functions
            .iter()
            .find(|f| f.func_index == 0)
            .map(|f| f.frame);
        assert_eq!(
            f,
            Some(StackBound::Unknown),
            "const frame + dynamic alloca must be Unknown, never the under-counted constant"
        );
        assert_eq!(res.stack_usage.max_stack_bytes, StackBound::Unknown);
    }

    // ── FEAT-077 (scry#123): two-tier function identity ─────────────────────

    /// All identity-stamped advisories for `func`, asserted non-empty —
    /// anti-vacuity: a fixture that never produces a stamped advisory would
    /// let every assertion below pass without touching the code path.
    fn stamped(r: &AnalysisResult, func: u32) -> Vec<&Advisory> {
        let v: Vec<&Advisory> = r
            .advisories
            .iter()
            .filter(|a| a.func_index == func && !a.obligation_id.is_empty())
            .collect();
        assert!(
            !v.is_empty(),
            "fixture must produce an identity-stamped advisory for func {func}; got {:?}",
            r.advisories
        );
        v
    }

    /// scry#144 (gale): FEAT-077 strips only LEGACY Rust mangling
    /// (`…17h<16 hex>E`). gale's dissolved OS object uses **v0** mangling —
    /// `_RNvCs942N1ctoMYm_18gust_exec_provider5admit` — whose disambiguator is
    /// a crate-level `Cs<base62>_` near the FRONT, not a trailing hash.
    ///
    /// So on the module that most needs stable identity, FEAT-077 provides
    /// none: every function falls back to the raw name and is marked
    /// `id_build_local`. That degrades honestly, which is the design working —
    /// but it means the consumer who asked for a stable join key gets nothing
    /// usable, and they measured that 7 of their 13 target functions have no
    /// usable name at all.
    #[test]
    fn issue144_v0_mangled_identity_survives_crate_disambiguator_churn() {
        let base = analyze_default(
            "(module \
               (func $\"_RNvCs942N1ctoMYm_18gust_exec_provider5admit\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_RNvCs942N1ctoMYm_18gust_time_provider8deadline\" (param i32) (result i32) \
                 i32.const 20 local.get 0 i32.div_s))",
        );
        // Same source, rebuilt: the CRATE disambiguator re-rolls, bodies identical.
        let rebuilt = analyze_default(
            "(module \
               (func $\"_RNvCs4dFUS4ljfv3_18gust_exec_provider5admit\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_RNvCs4dFUS4ljfv3_18gust_time_provider8deadline\" (param i32) (result i32) \
                 i32.const 20 local.get 0 i32.div_s))",
        );
        // Non-vacuity: both fixtures must actually raise identified advisories,
        // or the equality below would compare two empty sets.
        for (tag, r) in [("base", &base), ("rebuilt", &rebuilt)] {
            assert!(
                !stamped(r, 0).is_empty(),
                "{tag}: fixture must raise an identified advisory in func 0"
            );
        }
        for f in [0, 1] {
            assert_eq!(
                adv_id(&base, f),
                adv_id(&rebuilt, f),
                "a v0-mangled name must survive a crate-disambiguator change (func {f})"
            );
            for a in stamped(&base, f) {
                assert!(
                    !a.id_build_local,
                    "a v0 name unique after stripping is stable — not build-local"
                );
            }
        }
    }

    /// FEAT-077 tier 1 — a UNIQUE stripped name survives the disambiguator
    /// re-rolling. Rust legacy mangling ends in `17h<16 hex>E`, a symbol
    /// disambiguator derived from crate metadata and instantiation, NOT the
    /// body — so an unrelated edit renames the function and (before this fix)
    /// destroyed every obligation identity in it (measured: 45% of identified
    /// functions churn per commit, scry#123).
    #[test]
    fn feat077_unique_stripped_ident_survives_disambiguator_churn() {
        let base = analyze_default(
            "(module \
               (func $\"_ZN4demo3foo17h0123456789abcdefE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_ZN4demo3bar17h00aabbccddeeff11E\" (param i32) (result i32) \
                 i32.const 20 local.get 0 i32.div_s))",
        );
        // The SAME source rebuilt after an unrelated edit: both disambiguators
        // re-rolled, both bodies identical.
        let rebuilt = analyze_default(
            "(module \
               (func $\"_ZN4demo3foo17hfedcba9876543210E\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_ZN4demo3bar17h22aabbccddeeff33E\" (param i32) (result i32) \
                 i32.const 20 local.get 0 i32.div_s))",
        );
        for f in [0, 1] {
            assert_eq!(
                adv_id(&base, f),
                adv_id(&rebuilt, f),
                "a unique stripped name must survive a disambiguator change (func {f})"
            );
            for a in stamped(&base, f) {
                assert!(
                    !a.id_build_local,
                    "a unique stripped name is stable — it must NOT be marked build-local"
                );
            }
        }
    }

    /// FEAT-077 tier 2 — two functions sharing a stripped name (two
    /// monomorphizations of one dependency generic; measured 37.8% of
    /// functions, max multiplicity 39) must NOT collapse onto one identity.
    /// The raw name keeps them apart WITHIN the build, and the advisory is
    /// marked build-local because that raw name churns ACROSS builds.
    #[test]
    fn feat077_shared_stripped_name_does_not_collide_and_is_marked_build_local() {
        let r = analyze_default(
            "(module \
               (func $\"_ZN3dep7generic17haaaaaaaaaaaaaaaaE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_ZN3dep7generic17hbbbbbbbbbbbbbbbbE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s))",
        );
        // Identical bodies + identical stripped names: naive stripping would
        // merge these onto ONE identity (wrong attribution, the scry#122
        // class). They must stay distinct …
        assert_ne!(
            adv_id(&r, 0),
            adv_id(&r, 1),
            "two functions sharing a stripped name must NOT collapse onto one identity"
        );
        // … and be HONEST about the price: the id is unique only in this build.
        for f in [0, 1] {
            for a in stamped(&r, f) {
                assert!(
                    a.id_build_local,
                    "an ambiguous stripped name means the id is not comparable \
                     across builds — it must be marked build-local (func {f})"
                );
            }
        }
    }

    /// FEAT-077 — the uniqueness check must count PLAIN names too: `foo17h…E`
    /// strips to `foo`, which another function already IS. Using the stripped
    /// form would collide with a name that never had a disambiguator.
    #[test]
    fn feat077_stripped_name_colliding_with_plain_name_falls_back() {
        let r = analyze_default(
            "(module \
               (func $foo (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"foo17h0123456789abcdefE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s))",
        );
        assert_ne!(
            adv_id(&r, 0),
            adv_id(&r, 1),
            "a stripped name must not collide with an existing plain name"
        );
        for a in stamped(&r, 0) {
            assert!(
                !a.id_build_local,
                "the plain name keeps today's stable identity"
            );
        }
        for a in stamped(&r, 1) {
            assert!(a.id_build_local, "ambiguous after stripping → build-local");
        }
    }

    /// FEAT-077 — only the EXACT shape `17h` + 16 LOWERCASE hex + `E` is a
    /// Rust disambiguator. Near misses (uppercase hex, 15 digits) are ordinary
    /// names: the id tracks the raw name exactly as today, unmarked.
    #[test]
    fn feat077_only_the_exact_disambiguator_shape_is_stripped() {
        let base = analyze_default(
            "(module \
               (func $\"upper17h0123456789ABCDEFE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"short17h012345678abcdefE\" (param i32) (result i32) \
                 i32.const 20 local.get 0 i32.div_s))",
        );
        let renamed = analyze_default(
            "(module \
               (func $\"upper17h0123456799ABCDEFE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"short17h012345679abcdefE\" (param i32) (result i32) \
                 i32.const 20 local.get 0 i32.div_s))",
        );
        for f in [0, 1] {
            assert_ne!(
                adv_id(&base, f),
                adv_id(&renamed, f),
                "a near-miss suffix is part of the name; renaming it changes the \
                 id — today's behaviour must not be widened (func {f})"
            );
            for a in stamped(&base, f) {
                assert!(!a.id_build_local, "a near-miss name is not build-local");
            }
        }
    }

    /// FEAT-077 regression pin — for a name with NO disambiguator the identity
    /// derivation is byte-identical to v3.2.5. The constant was captured from
    /// the UNMODIFIED code (main, 5cd2a89) on this exact fixture.
    #[test]
    fn feat077_plain_name_id_is_byte_identical_to_v325() {
        let r = analyze_default(
            "(module (func $compute (param i32) (result i32) \
               i32.const 10 local.get 0 i32.div_s))",
        );
        let a = r
            .advisories
            .iter()
            .find(|a| a.code == "div-by-zero" && !a.obligation_id.is_empty())
            .expect("fixture must raise an identity-stamped div-by-zero advisory");
        assert_eq!(
            a.obligation_id, "dd7c4231ce161f87",
            "a plain name's obligation id must not change across FEAT-077"
        );
        assert!(!a.id_build_local, "a plain name is not build-local");
    }

    /// FEAT-077 regression pin — the body-shape-hash fallback (no name section,
    /// no export) is byte-identical to v3.2.5 and unmarked. Constant captured
    /// from the UNMODIFIED code (main, 5cd2a89) on this exact fixture.
    #[test]
    fn feat077_shape_hash_fallback_id_is_byte_identical_to_v325() {
        let r = analyze_default(
            "(module (func (param i32) (result i32) \
               i32.const 10 local.get 0 i32.div_s))",
        );
        let a = r
            .advisories
            .iter()
            .find(|a| a.code == "div-by-zero" && !a.obligation_id.is_empty())
            .expect("fixture must raise an identity-stamped div-by-zero advisory");
        assert_eq!(
            a.obligation_id, "4f61c85b63648dc7",
            "the shape-hash fallback id must not change across FEAT-077"
        );
        assert!(
            !a.id_build_local,
            "the shape-hash fallback is not build-local"
        );
    }

    /// FEAT-087 (scry#122 item 2) — THE DISCRIMINATING ORACLE for the new bit.
    ///
    /// A test in which both tiers AGREE on `ident_survives_own_edit` is not a
    /// gate: it would stay green if the field were a constant. So this fixture
    /// puts a NAMED function (identity = its name, which an edit to its body
    /// does not touch) and an UNNAMED one (identity = `body_shape_hash`, which
    /// an edit to its body destroys by construction) in ONE module and requires
    /// them to DISAGREE.
    ///
    /// It also pins the INDEPENDENCE of the two bits: the unnamed tier stays
    /// `id_build_local: false`, because a body-shape hash IS deterministic
    /// across builds. Flipping that instead would suppress cross-build citation
    /// for 100% of every stripped module (measured: 10,520 of 10,520
    /// obligations) to fix a different property.
    #[test]
    fn feat087_named_and_unnamed_tiers_disagree_on_surviving_their_own_edit() {
        let r = analyze_default(
            "(module \
               (func $compute (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func (param i32) (result i32) \
                 i32.const 20 local.get 0 i32.div_s))",
        );
        let pick = |idx: u32| {
            r.advisories
                .iter()
                .find(|a| {
                    a.func_index == idx && a.code == "div-by-zero" && !a.obligation_id.is_empty()
                })
                .unwrap_or_else(|| panic!("func {idx} must raise a stamped div-by-zero advisory"))
        };
        let named = pick(0);
        let unnamed = pick(1);

        assert!(
            named.ident_survives_own_edit,
            "a name-derived ident is body-independent, so it survives its own edit"
        );
        assert!(
            !unnamed.ident_survives_own_edit,
            "a body-shape-hash ident is a hash of the very bytes an edit changes"
        );
        assert_ne!(
            named.ident_survives_own_edit, unnamed.ident_survives_own_edit,
            "the field must DISCRIMINATE between identity tiers; if both agree \
             it is a constant, not a bit"
        );

        assert!(!named.id_build_local, "a plain name is not build-local");
        assert!(
            !unnamed.id_build_local,
            "the shape-hash tier stays cross-build comparable — the new bit is \
             NOT a rename of the old one"
        );
    }

    /// FEAT-087 — the two bits are INDEPENDENT, pinned on the tier that
    /// separates them. Two monomorphizations sharing a stripped name fall back
    /// to the raw, disambiguated name: that name CHURNS across builds
    /// (`id_build_local: true`) but is still body-INDEPENDENT, so an edit to
    /// the function's own body does not move it. Were the new field merely a
    /// rename of the old one, this test would demand `false` and fail.
    #[test]
    fn feat087_a_build_local_ident_still_survives_its_own_edit() {
        let r = analyze_default(
            "(module \
               (func $\"_ZN3dep7generic17haaaaaaaaaaaaaaaaE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_ZN3dep7generic17hbbbbbbbbbbbbbbbbE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s))",
        );
        let a = r
            .advisories
            .iter()
            .find(|a| a.func_index == 0 && a.code == "div-by-zero" && !a.obligation_id.is_empty())
            .expect("fixture must raise a stamped div-by-zero advisory");
        assert!(a.id_build_local, "a shared stripped name is build-local");
        assert!(
            a.ident_survives_own_edit,
            "the raw name is body-independent: build-local and \
             survives-own-edit are INDEPENDENT bits, not a ranking"
        );
    }

    /// FEAT-087: a module-scoped advisory (`unbounded-stack`) is identified by
    /// the literal `<module>`, which no function body feeds — so it survives an
    /// edit to its own module. Pinned as a GATE rather than left to the
    /// construction-site default, so the value is a decision and not a seed.
    #[test]
    fn feat087_a_module_scoped_ident_survives_any_edit() {
        let r = analyze_default("(module (func $recurse (result i32) call $recurse))");
        let a = r
            .advisories
            .iter()
            .find(|a| a.code == "unbounded-stack")
            .expect("a recursive module must raise unbounded-stack");
        assert!(
            a.ident_survives_own_edit,
            "the `<module>` ident is body-independent"
        );
    }

    /// FEAT-064 AC3 (scry#122, scry#123): does a GENUINE fix present as a
    /// changed obligation at a SURVIVING site? AC3 was left explicitly OPEN
    /// because the only evidence was a sample of scry's own history, which
    /// recompiles into different monomorphizations. This is the isolating
    /// fixture AC3 asked for.
    ///
    /// The fix is REAL and semantics-preserving — not a deletion of the risky
    /// functionality. `$r` defaults to 0, so branching out of the ALREADY
    /// PRESENT block when the divisor is zero returns 0 instead of trapping.
    /// It opens no new region and adds no second `i32.div_s`, so the division
    /// site's region path and intra-region ordinal are untouched.
    ///
    /// MEASURED RESULT, and it splits cleanly in two:
    ///   * identity survives PERFECTLY — same `site_key`, byte-identical
    ///     `obligation_id`s. So identity is NOT what blocks adjudication here.
    ///   * the obligation set is UNCHANGED — `div-by-zero` still fires after
    ///     the fix. `br_if` on `i32.eqz` licenses `divisor != 0` on the
    ///     FALL-THROUGH path, and `refine_interval` documents that a
    ///     disequality carves no interval (`(GuardOp::Eq, false) => return
    ///     iv`), so the divisor is never refined.
    ///
    /// This test pins the IDENTITY half, which is the AC3 evidence. It
    /// deliberately does NOT pin `div-by-zero` still firing: that is a defect
    /// (FEAT-089), and a test asserting a defect becomes a barrier to fixing
    /// it. When FEAT-089 lands, this test must still pass unchanged.
    #[test]
    fn feat064_ac3_a_genuine_fix_preserves_obligation_identity() {
        const BEFORE: &str = "(module (func $d (export \"d\") (param i32) (result i32) (local $r i32) \
             block i32.const 10 local.get 0 i32.div_s local.set $r end \
             local.get $r))";
        const AFTER: &str = "(module (func $d (export \"d\") (param i32) (result i32) (local $r i32) \
             block local.get 0 i32.eqz br_if 0 \
             i32.const 10 local.get 0 i32.div_s local.set $r end \
             local.get $r))";
        let pick = |wat: &str| {
            let r = analyze_default(wat);
            let v: alloc::vec::Vec<_> = r
                .advisories
                .iter()
                .filter(|a| !a.obligation_id.is_empty() && a.code != "unbounded-stack")
                .map(|a| (a.obligation_id.clone(), a.site_key.clone(), a.code.clone()))
                .collect();
            v
        };
        let before = pick(BEFORE);
        let after = pick(AFTER);

        // Non-vacuity: the fixture must actually raise the obligation whose
        // identity is the subject, or "identity survived" is a claim about an
        // empty set.
        assert!(
            before.iter().any(|(_, _, c)| c == "div-by-zero"),
            "precondition: the pre-fix fixture must raise div-by-zero; got {before:?}"
        );

        let sites_before: alloc::collections::BTreeSet<_> =
            before.iter().map(|(_, s, _)| s.clone()).collect();
        let sites_after: alloc::collections::BTreeSet<_> =
            after.iter().map(|(_, s, _)| s.clone()).collect();
        assert_eq!(
            sites_before, sites_after,
            "a genuine fix that opens no region must leave the site identity intact"
        );

        let ids_before: alloc::collections::BTreeSet<_> =
            before.iter().map(|(i, _, _)| i.clone()).collect();
        let ids_after: alloc::collections::BTreeSet<_> =
            after.iter().map(|(i, _, _)| i.clone()).collect();
        assert!(
            !ids_before.is_empty() && ids_before.is_subset(&ids_after),
            "every pre-fix obligation id must still be addressable after the fix \
             (before={ids_before:?} after={ids_after:?})"
        );
    }

    // ─────────────── FEAT-089 (REQ-021): non-zero facts ───────────────

    /// FEAT-089 helper: the single `DivByZero` trap check of a one-div
    /// fixture, with non-vacuity built in — panics if the fixture never
    /// reached a div (a claim about an empty set is not a claim).
    fn the_div_by_zero_check(r: &AnalysisResult) -> &TrapCheck {
        let v: alloc::vec::Vec<&TrapCheck> = r
            .trap_checks
            .iter()
            .filter(|t| t.kind == TrapKind::DivByZero)
            .collect();
        assert_eq!(
            v.len(),
            1,
            "fixture must reach exactly one classified div/rem; got {v:?}"
        );
        v[0]
    }

    /// FEAT-089 AC1 + AC2 (primary): the canonical div-by-zero repair —
    /// `br_if` on `i32.eqz` — establishes `divisor != 0` on the FALL-THROUGH
    /// edge, and the div/rem trap check must consult that fact and report
    /// PROVEN-SAFE for the divisor-zero obligation. Differential against the
    /// unguarded twin (the FEAT-064 AC3 BEFORE fixture) so the test cannot
    /// pass vacuously: the guard, and nothing else, is what flips the verdict.
    #[test]
    fn feat089_a_eqz_guard_fallthrough_proves_div_by_zero_safe() {
        const UNGUARDED: &str = "(module (func $d (export \"d\") (param i32) (result i32) (local $r i32) \
             block i32.const 10 local.get 0 i32.div_s local.set $r end \
             local.get $r))";
        const GUARDED: &str = "(module (func $d (export \"d\") (param i32) (result i32) (local $r i32) \
             block local.get 0 i32.eqz br_if 0 \
             i32.const 10 local.get 0 i32.div_s local.set $r end \
             local.get $r))";

        // Control / non-vacuity: without the guard the obligation stands.
        let before = analyze_default(UNGUARDED);
        assert_eq!(
            the_div_by_zero_check(&before).verdict,
            TrapVerdict::PotentialTrap,
            "precondition: the unguarded twin must raise the obligation"
        );
        assert!(
            before.advisories.iter().any(|a| a.code == "div-by-zero"),
            "precondition: the unguarded twin must raise a div-by-zero advisory"
        );

        // The fix: the fall-through of `local.get 0; i32.eqz; br_if 0`
        // licenses `local 0 != 0`, so the div is proven safe.
        let after = analyze_default(GUARDED);
        assert_eq!(
            the_div_by_zero_check(&after).verdict,
            TrapVerdict::ProvenSafe,
            "the eqz-guard fall-through licenses divisor != 0; the trap check \
             must consult the non-zero fact"
        );
        assert!(
            !after.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the guarded site must no longer raise div-by-zero; got {:?}",
            after
                .advisories
                .iter()
                .map(|a| &a.code)
                .collect::<alloc::vec::Vec<_>>()
        );
        assert!(
            after
                .advisories
                .iter()
                .any(|a| a.code == "proven-safe" && a.detail.contains("divide-by-zero")),
            "the proof must surface as a LeverageableFact advisory"
        );
    }

    /// FEAT-089 AC2 names all four i32 div/rem ops. The primary test covers
    /// `i32.div_s`; this one runs `div_u` / `rem_s` / `rem_u` under ONE guard
    /// (straight-line, no intervening write/call, so the fact survives across
    /// all three sites) — each must be PROVEN-SAFE for divisor-zero.
    #[test]
    fn feat089_a_div_u_rem_s_rem_u_consult_the_fact_too() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) (local $r i32) \
               block local.get 0 i32.eqz br_if 0 \
               i32.const 10 local.get 0 i32.div_u local.set $r \
               i32.const 10 local.get 0 i32.rem_s local.set $r \
               i32.const 10 local.get 0 i32.rem_u local.set $r end \
               local.get $r))",
        );
        let dbz: alloc::vec::Vec<&TrapCheck> = r
            .trap_checks
            .iter()
            .filter(|t| t.kind == TrapKind::DivByZero)
            .collect();
        assert_eq!(
            dbz.len(),
            3,
            "fixture must classify all three ops; got {dbz:?}"
        );
        for t in &dbz {
            assert_eq!(
                t.verdict,
                TrapVerdict::ProvenSafe,
                "`{}` must consult the non-zero fact",
                t.op
            );
        }
        assert!(
            !r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "no divisor-zero obligation may stand under the guard"
        );
    }

    /// FEAT-089 AC4: `!= 0` says nothing about `INT_MIN / -1`. At a site where
    /// BOTH obligations stand (⊤ dividend, ⊤ divisor), the non-zero fact must
    /// clear the divisor-zero obligation ONLY — the signed-overflow obligation
    /// at the same pc must be UNAFFECTED. Clearing both is over-claiming.
    #[test]
    fn feat089_a_signed_overflow_is_unaffected_by_the_nonzero_fact() {
        let r = analyze_default(
            "(module (func $q (export \"q\") (param i32 i32) (result i32) (local $r i32) \
               block local.get 1 i32.eqz br_if 0 \
               local.get 0 local.get 1 i32.div_s local.set $r end \
               local.get $r))",
        );
        // Non-vacuity: both obligations must exist at the SAME div site.
        let dbz = the_div_by_zero_check(&r);
        let so = r
            .trap_checks
            .iter()
            .find(|t| t.kind == TrapKind::SignedOverflow)
            .expect("i32.div_s must also be classified for signed overflow");
        assert_eq!(
            (dbz.func_index, dbz.pc),
            (so.func_index, so.pc),
            "the two obligations under test must be at one site"
        );
        assert_eq!(
            dbz.verdict,
            TrapVerdict::ProvenSafe,
            "divisor-zero: cleared by the guard's non-zero fact"
        );
        assert_eq!(
            so.verdict,
            TrapVerdict::PotentialTrap,
            "signed overflow: `!= 0` excludes neither INT_MIN nor -1 — this \
             obligation must STAND"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "signed-overflow"),
            "the standing obligation must still surface as an advisory"
        );
        assert!(
            !r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the cleared obligation must not"
        );
    }

    /// FEAT-089 AC3 (soundness, adversarial): a `local.set` to the guarded
    /// local between the guard and the div must KILL the fact. The written
    /// value is a ⊤ param, so nothing else proves safety — a ProvenSafe here
    /// would be a FALSE PROOF (call with param1 = 0).
    #[test]
    fn feat089_s_local_set_after_the_guard_kills_the_fact() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local $r i32) \
               block local.get 0 i32.eqz br_if 0 \
               local.get 1 local.set 0 \
               i32.const 10 local.get 0 i32.div_s local.set $r end \
               local.get $r))",
        );
        assert_eq!(
            the_div_by_zero_check(&r).verdict,
            TrapVerdict::PotentialTrap,
            "a non-zero fact must not survive a write to its local"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the obligation must stand as an advisory"
        );
    }

    /// FEAT-089 AC3 (soundness, adversarial): same for `local.tee` — it is a
    /// write exactly like `local.set` (runtime counterexample: param1 = 0).
    #[test]
    fn feat089_s_local_tee_after_the_guard_kills_the_fact() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local $r i32) \
               block local.get 0 i32.eqz br_if 0 \
               local.get 1 local.tee 0 local.set $r \
               i32.const 10 local.get 0 i32.div_s local.set $r end \
               local.get $r))",
        );
        assert_eq!(
            the_div_by_zero_check(&r).verdict,
            TrapVerdict::PotentialTrap,
            "a non-zero fact must not survive a `local.tee` write to its local"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the obligation must stand as an advisory"
        );
    }

    /// FEAT-089 AC3 (soundness, adversarial): only a guard whose taken edge
    /// pins the local to `== 0` establishes the fact — `!= c` for any other
    /// constant is a different hole and licenses nothing about zero.
    #[test]
    fn feat089_s_a_guard_against_a_nonzero_constant_licenses_nothing() {
        // Fall-through of `local.get 0; i32.const 5; i32.eq; br_if` licenses
        // `x != 5` — which says NOTHING about zero (runtime counterexample:
        // param = 0 falls through straight into 10/0). Pins the `c == 0`
        // condition on fact establishment.
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) (local $r i32) \
               block local.get 0 i32.const 5 i32.eq br_if 0 \
               i32.const 10 local.get 0 i32.div_s local.set $r end \
               local.get $r))",
        );
        assert_eq!(
            the_div_by_zero_check(&r).verdict,
            TrapVerdict::PotentialTrap,
            "a disequality against 5 must not become a non-zero fact"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the obligation must stand as an advisory"
        );
    }

    /// FEAT-089 AC3 (soundness, adversarial): a call between the guard and the
    /// div kills the fact. Wasm locals are callee-inaccessible, so this is
    /// deliberately CONSERVATIVE rather than forced by the semantics — but the
    /// AC names it, over-approximating invalidation is sound, and the cheap
    /// direction is the safe one. This test PINS the conservative choice.
    #[test]
    fn feat089_s_a_call_after_the_guard_kills_the_fact() {
        let r = analyze_default(
            "(module (func $noop) (func (export \"f\") (param i32) (result i32) (local $r i32) \
               block local.get 0 i32.eqz br_if 0 \
               call $noop \
               i32.const 10 local.get 0 i32.div_s local.set $r end \
               local.get $r))",
        );
        assert_eq!(
            the_div_by_zero_check(&r).verdict,
            TrapVerdict::PotentialTrap,
            "the non-zero fact must be dropped (conservatively) across a call"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the obligation must stand as an advisory"
        );
    }

    /// FEAT-089 AC3 (soundness, adversarial): a fact established OUTSIDE a
    /// loop must not reach a div INSIDE it — the back-edge re-enters the
    /// region after a write. Runtime counterexample with param = 2:
    /// iteration 1 divides 10/2 and decrements local 0 to 1 ($r=5, loop),
    /// iteration 2 divides 10/1 and decrements to 0 ($r=10, loop),
    /// iteration 3 divides 10/0 — TRAP. Any ProvenSafe here is a false proof.
    #[test]
    fn feat089_s_a_loop_back_edge_kills_the_fact() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32) (result i32) (local $r i32) \
               block local.get 0 i32.eqz br_if 0 \
               loop \
                 i32.const 10 local.get 0 i32.div_s local.set $r \
                 local.get 0 i32.const 1 i32.sub local.set 0 \
                 local.get $r br_if 0 \
               end end \
               local.get $r))",
        );
        assert_eq!(
            the_div_by_zero_check(&r).verdict,
            TrapVerdict::PotentialTrap,
            "a pre-loop non-zero fact must not survive into the loop body"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the obligation must stand as an advisory"
        );
    }

    /// FEAT-089 AC3 (soundness, adversarial): a join where one predecessor
    /// LACKS the fact must lose it — facts meet (intersect) at merges, never
    /// union. Path A (`local.get 1 br_if 0`) skips the guard and reaches the
    /// div with local 0 unconstrained; path B falls through the guard with the
    /// fact. Runtime counterexample: param0 = 0, param1 = 1 takes path A
    /// straight into 10/0 — TRAP.
    #[test]
    fn feat089_s_a_join_with_an_unguarded_predecessor_kills_the_fact() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local $r i32) \
               block \
                 block \
                   local.get 1 br_if 0 \
                   local.get 0 i32.eqz br_if 1 \
                 end \
                 i32.const 10 local.get 0 i32.div_s local.set $r \
               end \
               local.get $r))",
        );
        assert_eq!(
            the_div_by_zero_check(&r).verdict,
            TrapVerdict::PotentialTrap,
            "a fact held on only ONE join predecessor must not survive the merge"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the obligation must stand as an advisory"
        );
    }

    /// FEAT-089 AC3 (soundness, adversarial): a function that degrades to ⊤
    /// (unsupported op — `i32.rotl` — after the guard) must lose every fact
    /// with the rest of its state; the degraded-path div verdict stays
    /// PotentialTrap.
    #[test]
    fn feat089_s_a_degrade_after_the_guard_kills_the_fact() {
        let r = analyze_default(
            "(module (func (export \"f\") (param i32 i32) (result i32) (local $r i32) \
               block local.get 0 i32.eqz br_if 0 \
               local.get 1 i32.const 1 i32.rotl local.set $r \
               i32.const 10 local.get 0 i32.div_s local.set $r end \
               local.get $r))",
        );
        // Non-vacuity: the fixture must actually have degraded.
        assert!(
            r.gaps
                .iter()
                .any(|g| g.op.to_ascii_lowercase().contains("rotl")),
            "precondition: the fixture must degrade on i32.rotl; gaps: {:?}",
            r.gaps
        );
        assert_eq!(
            the_div_by_zero_check(&r).verdict,
            TrapVerdict::PotentialTrap,
            "a degraded function retains no facts"
        );
        assert!(
            r.advisories.iter().any(|a| a.code == "div-by-zero"),
            "the obligation must stand as an advisory"
        );
    }

    /// FEAT-092 (scry#126): `TrapCheck::op` is documented as "the operator name
    /// (e.g. `i32.div_s`)" — wasm text format. MEASURED on a real module
    /// (scry's own scry_mcdc.wasm, identical stripped and unstripped): 2,800 of
    /// 10,520 advisories instead carried a RUST ENUM IDENTIFIER — `I64Store`,
    /// `I32Load8U`, `I32Store8`, `MemoryCopy`, … — because `op_report_name`
    /// falls back to `{:?}` for any operator `op_name` has no arm for, and
    /// among memory ops `op_name` covered only `I32Load` and `I32Store`.
    ///
    /// Worse than uniformly wrong: the SAME operator got BOTH names. The
    /// non-degraded path labels it `i64.store` (287 sites) while the degraded
    /// path produced `I64Store` (1,008). A consumer ranking operators by
    /// frequency (scry#126) sees one operator as two and under-counts the top
    /// entry by ~4.5x.
    ///
    /// This is a NAMING fix only — the verdict multiset is pinned below so a
    /// future edit cannot change what scry proves while claiming to rename.
    #[test]
    fn feat092_a_memory_operator_is_never_reported_by_its_rust_identifier() {
        let r = analyze_default(
            "(module (memory 1) (func $f (export \"f\") (param i32) \
               local.get 0 i64.const 7 i64.store \
               local.get 0 i32.load8_u drop \
               local.get 0 i32.const 3 i32.store8))",
        );
        // Non-vacuity: the fixture must actually reach the operators in
        // question, or "no Rust identifiers" is a claim about an empty set.
        assert!(
            r.trap_checks.len() >= 3,
            "fixture must raise trap checks for the three memory ops; got {:?}",
            r.trap_checks
                .iter()
                .map(|t| &t.op)
                .collect::<alloc::vec::Vec<_>>()
        );
        let leaked: alloc::vec::Vec<&str> = r
            .trap_checks
            .iter()
            .map(|t| t.op.as_str())
            .filter(|n| n.starts_with(|c: char| c.is_ascii_uppercase()))
            .collect();
        assert!(
            leaked.is_empty(),
            "TrapCheck::op must be the wasm text-format name, never a Rust \
             enum identifier; leaked: {leaked:?}"
        );
        for t in &r.trap_checks {
            assert!(
                t.op.contains('.') && t.op.chars().all(|c| !c.is_ascii_uppercase()),
                "not a wasm text-format operator name: {:?}",
                t.op
            );
        }
        // NAMING ONLY: pin the verdicts so a rename cannot quietly move what
        // scry proves. All three accesses are unproven here.
        let potential = r
            .trap_checks
            .iter()
            .filter(|t| t.verdict == TrapVerdict::PotentialTrap)
            .count();
        assert_eq!(
            potential,
            r.trap_checks.len(),
            "this fixture proves nothing safe; a naming change must not alter that"
        );
    }

    // ─────────────── FEAT-065 (REQ-021): verify_against ───────────────

    /// Shared driver: analyze both texts, adjudicate `after` against `before`.
    fn adjudicate(before: &str, after: &str) -> (AnalysisResult, AnalysisResult, VerifyReport) {
        let b = analyze_default(before);
        let a = analyze_default(after);
        let rep = verify_against(&b, &a);
        (b, a, rep)
    }

    fn open_advisories(r: &AnalysisResult) -> alloc::vec::Vec<&Advisory> {
        r.advisories
            .iter()
            .filter(|a| a.class.is_open_obligation())
            .collect()
    }

    /// The stamped `site_key` of the `code` advisory in function `fi` — with a
    /// panic (not a silent None) when the fixture failed to raise it, so no
    /// test downstream of this helper can be vacuous about its fixture.
    fn site_of(r: &AnalysisResult, fi: u32, code: &str) -> String {
        r.advisories
            .iter()
            .find(|a| a.func_index == fi && a.code == code && !a.site_key.is_empty())
            .unwrap_or_else(|| panic!("fixture must raise a stamped `{code}` in func {fi}"))
            .site_key
            .clone()
    }

    /// FEAT-065: `func_identities` is the adjudicator's function-level surface:
    /// one entry per defined function, `ident` from the same tier decision the
    /// advisories carry, and `body_shape_hash` ALWAYS populated. The shape hash
    /// is immediate-blind BY DESIGN (that is what makes a shape-preserving fix
    /// adjudicable): two bodies differing only in immediates hash identically,
    /// two bodies differing in operator shape do not.
    #[test]
    fn feat065_func_identities_cover_every_defined_function() {
        let r = analyze_default(
            "(module \
               (func $named (result i32) i32.const 10 i32.const 0 i32.div_s) \
               (func (result i32) i32.const 12 i32.const 7 i32.div_s) \
               (func (result i32) i32.const 1))",
        );
        assert_eq!(
            r.func_identities.len(),
            3,
            "one identity record per defined function; got {:?}",
            r.func_identities
        );
        let named = &r.func_identities[0];
        let unnamed_div = &r.func_identities[1];
        let unnamed_const = &r.func_identities[2];
        assert_eq!(named.ident, "named", "tier 1-3: ident is the name");
        assert!(named.ident_survives_own_edit && !named.id_build_local);
        assert_eq!(
            unnamed_div.ident, unnamed_div.body_shape_hash,
            "tier 4: ident IS the body shape hash"
        );
        assert!(!unnamed_div.ident_survives_own_edit);
        // Immediate-blindness, the property `discharged` soundness rests on:
        // same operator shape (const const div) despite different immediates.
        assert_eq!(
            named.body_shape_hash, unnamed_div.body_shape_hash,
            "shape hash must be immediate-blind (op names only)"
        );
        assert_ne!(
            named.body_shape_hash, unnamed_const.body_shape_hash,
            "a different operator shape must hash differently"
        );
    }

    /// FEAT-065 AC9 (ADVERSARIAL — the original test passed vacuously): a
    /// module compared with ITSELF yields one verdict per open obligation and
    /// EVERY one of them is `still-open-untouched`. No regressed, no moved,
    /// no discharged, no removed, no uncertain, nothing introduced. The AC
    /// text predates the AC2 still-open split; self-comparison means unchanged
    /// bodies, so the correct expectation is the `-untouched` arm.
    #[test]
    fn feat065_ac9_self_comparison_yields_only_still_open_untouched() {
        // The last two functions are BYTE-IDENTICAL unnamed bodies: they share
        // one body-shape-hash identity, so their sites are AMBIGUOUS (claimed
        // by two functions). Self-comparison must still adjudicate them
        // still-open-untouched — the population is unchanged wholesale, and 30
        // of 10,558 verdicts on scry's own module sit on exactly this shape.
        let src = "(module \
             (func $rec (result i32) call $rec) \
             (func $open (param i32) (result i32) local.get 0 local.get 0 i32.div_s) \
             (func $safe (result i32) i32.const 10 i32.const 7 i32.div_s) \
             (func (param i32) (result i32) i32.const 9 local.get 0 i32.div_s) \
             (func (param i32) (result i32) i32.const 9 local.get 0 i32.div_s))";
        let r = analyze_default(src);
        // Non-vacuity of the ambiguity: one site key must be claimed by BOTH
        // duplicate functions.
        {
            let mut funcs_per_site: alloc::collections::BTreeMap<
                &str,
                alloc::collections::BTreeSet<u32>,
            > = alloc::collections::BTreeMap::new();
            for adv in r.advisories.iter().filter(|x| !x.site_key.is_empty()) {
                funcs_per_site
                    .entry(adv.site_key.as_str())
                    .or_default()
                    .insert(adv.func_index);
            }
            assert!(
                funcs_per_site.values().any(|f| f.len() > 1),
                "fixture must contain an AMBIGUOUS site (duplicate unnamed bodies)"
            );
        }
        // Non-vacuity: the fixture must carry open obligations ACROSS SCOPES
        // (module-scoped unbounded-stack + site-scoped div-by-zero) AND at
        // least one proven-safe fact (so the regression path has material to
        // stay silent about).
        let open = open_advisories(&r);
        assert!(
            open.len() >= 3 && open.iter().any(|a| a.code == "unbounded-stack"),
            "fixture must raise >=3 open obligations incl. unbounded-stack; got {:?}",
            r.advisories
                .iter()
                .map(|a| &a.code)
                .collect::<alloc::vec::Vec<_>>()
        );
        assert!(
            r.advisories
                .iter()
                .any(|a| a.class == AdvisoryClass::LeverageableFact),
            "fixture must carry a proven-safe fact"
        );

        let rep = verify_against(&r, &r);
        assert_eq!(
            rep.verdicts.len(),
            open.len(),
            "self-comparison must adjudicate EVERY open obligation (no silent drop); got {:?}",
            rep.verdicts
        );
        for v in &rep.verdicts {
            assert_eq!(
                v.verdict,
                VerifyVerdict::StillOpenUntouched,
                "self-comparison: every verdict is still-open-untouched, got {v:?}"
            );
            assert!(!v.introduced, "nothing is introduced by a no-op: {v:?}");
        }
        assert!(rep.gate_pass(), "a no-op edit must pass the gate");
        assert_eq!(rep.exit_code(), 0);
    }

    /// FEAT-065 AC2/AC3/AC6: the fix-invisible case must come back
    /// `still-open-after-edit`, while an obligation in a function the edit did
    /// NOT touch stays `still-open-untouched`. The discriminator is the body
    /// shape hash (AC3): a body that did not change cannot contain a fix.
    ///
    /// FIXTURE NOTE (FEAT-089): this test originally used the canonical
    /// `local.get L; i32.eqz; br_if` repair — which FEAT-089 made VISIBLE, so
    /// it no longer exercises the invisible path. The fix here is the
    /// operand-REVERSED guard `(i32.eq (i32.const 0) (local.get L))` —
    /// semantically the identical repair, but the guard recogniser matches
    /// only the `local.get`-first idiom, so the obligation genuinely persists.
    /// If a later feature recognises this shape too, this fixture must move to
    /// a still-invisible one again.
    #[test]
    fn feat065_ac6_fix_invisible_is_still_open_after_edit_not_untouched() {
        const BEFORE: &str = "(module \
             (func $d (export \"d\") (param i32) (result i32) (local $r i32) \
               block i32.const 10 local.get 0 i32.div_s local.set $r end \
               local.get $r) \
             (func $u (param i32) (result i32) i32.const 20 local.get 0 i32.div_s))";
        const AFTER: &str = "(module \
             (func $d (export \"d\") (param i32) (result i32) (local $r i32) \
               block i32.const 0 local.get 0 i32.eq br_if 0 \
               i32.const 10 local.get 0 i32.div_s local.set $r end \
               local.get $r) \
             (func $u (param i32) (result i32) i32.const 20 local.get 0 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        // Non-vacuity: div-by-zero must be open in BOTH functions in BOTH runs
        // (FEAT-089: the genuine fix does not close the obligation).
        let s_d = site_of(&b, 0, "div-by-zero");
        let s_u = site_of(&b, 1, "div-by-zero");
        assert_eq!(
            s_d,
            site_of(&a, 0, "div-by-zero"),
            "identity must survive the fix"
        );
        assert_eq!(s_u, site_of(&a, 1, "div-by-zero"));

        let verdict_at = |s: &str| {
            rep.verdicts
                .iter()
                .find(|v| v.site_key == *s && v.code == "div-by-zero")
                .unwrap_or_else(|| {
                    panic!("a verdict must exist for site {s}; got {:?}", rep.verdicts)
                })
        };
        assert_eq!(
            verdict_at(&s_d).verdict,
            VerifyVerdict::StillOpenAfterEdit,
            "the edited function's persisting obligation is fix-invisible, NOT untouched"
        );
        assert_eq!(
            verdict_at(&s_u).verdict,
            VerifyVerdict::StillOpenUntouched,
            "an untouched function's obligation must not inherit the edit signal"
        );
        assert!(rep.gate_pass(), "still-open is not a failure signal");
    }

    /// FEAT-065 AC1/AC4: `discharged` IS reachable — on the shape it is sound
    /// for: a shape-preserving fix (immediates only: `i32.const 0` divisor →
    /// `i32.const 7`) in a named function. Every conjunct holds: matched by
    /// site_key, !id_build_local, ident_survives_own_edit, group membership
    /// unchanged — and the operator shape is unchanged, so site
    /// correspondence is exact and the discharge is a certainty claim.
    #[test]
    fn feat065_ac4_discharged_on_a_shape_preserving_fix() {
        const BEFORE: &str = "(module (func $f (result i32) i32.const 10 i32.const 0 i32.div_s))";
        const AFTER: &str = "(module (func $f (result i32) i32.const 10 i32.const 7 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        // Non-vacuity: the obligation must be open before and the SAME site
        // must carry a proof of safety after.
        let s = site_of(&b, 0, "div-by-zero");
        assert!(
            a.advisories
                .iter()
                .any(|x| x.site_key == s && x.class == AdvisoryClass::LeverageableFact),
            "after-fixture must prove the same site safe; got {:?}",
            a.advisories
        );
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s && v.code == "div-by-zero")
            .unwrap_or_else(|| {
                panic!(
                    "a verdict must exist for the fixed site; got {:?}",
                    rep.verdicts
                )
            });
        assert_eq!(
            v.verdict,
            VerifyVerdict::Discharged,
            "a sound, shape-preserving, identity-corroborated fix is a discharge: {v:?}"
        );
        assert_eq!(rep.count(VerifyVerdict::Uncertain), 0, "{:?}", rep.verdicts);
        assert!(rep.gate_pass());
        assert_eq!(rep.exit_code(), 0);
    }

    /// FEAT-065 AC7: deleting the function that contained an open obligation
    /// is `removed-with-code` — NEVER `discharged`. Deleting the code that
    /// carried an unproven obligation proves nothing, and an agent optimising
    /// against a conflated verdict would learn to delete rather than to fix.
    #[test]
    fn feat065_ac7_deleted_function_is_removed_with_code_never_discharged() {
        const BEFORE: &str = "(module \
             (func $keep (param i32) (result i32) i32.const 10 local.get 0 i32.div_s) \
             (func $gone (param i32) (result i32) i32.const 30 local.get 0 i32.div_s))";
        const AFTER: &str = "(module \
             (func $keep (param i32) (result i32) i32.const 10 local.get 0 i32.div_s))";
        let (b, _a, rep) = adjudicate(BEFORE, AFTER);
        let s_gone = site_of(&b, 1, "div-by-zero");
        let s_keep = site_of(&b, 0, "div-by-zero");
        let v_gone = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s_gone && v.code == "div-by-zero")
            .unwrap_or_else(|| {
                panic!("deleted obligation needs a verdict; got {:?}", rep.verdicts)
            });
        assert_eq!(
            v_gone.verdict,
            VerifyVerdict::RemovedWithCode,
            "gone-with-the-function is removal, not progress: {v_gone:?}"
        );
        assert_eq!(
            rep.count(VerifyVerdict::Discharged),
            0,
            "deletion must NEVER read as discharged; got {:?}",
            rep.verdicts
        );
        let v_keep = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s_keep && v.code == "div-by-zero")
            .expect("kept obligation needs a verdict");
        assert_eq!(v_keep.verdict, VerifyVerdict::StillOpenUntouched);
    }

    /// FEAT-065 AC8: an edit that turns a PROVEN-SAFE site back into an
    /// obligation is `regressed`, and the exit code signals failure.
    #[test]
    fn feat065_ac8_regression_is_reported_and_fails_the_gate() {
        const BEFORE: &str = "(module (func $f (result i32) i32.const 10 i32.const 7 i32.div_s))";
        const AFTER: &str = "(module (func $f (result i32) i32.const 10 i32.const 0 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        // Non-vacuity: proven-safe before (and NOT open), open after.
        let s = site_of(&b, 0, "proven-safe");
        assert!(
            !b.advisories
                .iter()
                .any(|x| x.site_key == s && x.class.is_open_obligation()),
            "before-fixture must carry no open obligation at the safe site"
        );
        assert_eq!(
            s,
            site_of(&a, 0, "div-by-zero"),
            "the regression must hit the SAME site"
        );
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s && v.code == "div-by-zero")
            .unwrap_or_else(|| panic!("regression needs a verdict; got {:?}", rep.verdicts));
        assert_eq!(v.verdict, VerifyVerdict::Regressed, "{v:?}");
        assert!(!rep.gate_pass(), "a regression must fail the gate");
        assert_eq!(rep.exit_code(), 1);
    }

    /// FEAT-065 AC10 (ADVERSARIAL — the case that falsified DD-021's
    /// rationale): one same-kind operator deleted and another inserted in the
    /// same region, leaving the group multiset byte-identical. The after-run
    /// PROVES the surviving site safe — the exact bait the withdrawn
    /// adjudicator took as `discharged`. The honest verdict is `uncertain`:
    /// the operator shape changed, so positional identity cannot say whether
    /// this is a fixed operator or a deleted one plus a safe stranger.
    #[test]
    fn feat065_ac10_cardinality_preserving_delete_insert_is_uncertain() {
        const BEFORE: &str = "(module (func $g (result i32) \
             i32.const 1 drop i32.const 10 i32.const 0 i32.div_s))";
        const AFTER: &str = "(module (func $g (result i32) \
             i32.const 10 i32.const 7 i32.div_s i32.const 1 drop))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        let s = site_of(&b, 0, "div-by-zero");
        // Non-vacuity 1: the site survives BYTE-IDENTICALLY (same func ident,
        // same region path, same kind, same ordinal) …
        assert_eq!(
            s,
            site_of(&a, 0, "proven-safe"),
            "the inserted same-kind operator must inherit the deleted one's site key"
        );
        // Non-vacuity 2: … and the group multiset is byte-identical across
        // the runs — this IS the falsifying configuration.
        let groups = |r: &AnalysisResult| {
            let mut m: alloc::collections::BTreeMap<String, alloc::collections::BTreeSet<String>> =
                alloc::collections::BTreeMap::new();
            for adv in r.advisories.iter().filter(|x| !x.site_key.is_empty()) {
                m.entry(adv.group_key.clone())
                    .or_default()
                    .insert(adv.site_key.clone());
            }
            m
        };
        assert_eq!(groups(&b), groups(&a), "group membership must be unchanged");
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s && v.code == "div-by-zero")
            .unwrap_or_else(|| panic!("the obligation needs a verdict; got {:?}", rep.verdicts));
        assert_eq!(
            v.verdict,
            VerifyVerdict::Uncertain,
            "a shape-changing open→safe transition is UNCERTAIN, never discharged: {v:?}"
        );
        assert_eq!(
            rep.count(VerifyVerdict::Discharged),
            0,
            "{:?}",
            rep.verdicts
        );
    }

    /// FEAT-065 AC5/AC11: an obligation whose function identity came from the
    /// body-shape hash (`ident_survives_own_edit: false` — every function of a
    /// STRIPPED module, FEAT-087: 10,520 of 10,520) is NEVER `discharged`,
    /// even on the one shape where matching would technically work (a
    /// shape-preserving immediate fix keeps the hash ident equal). The
    /// fallback identity cannot corroborate a discharge; the AC makes the
    /// production-shape consequence explicit rather than discovered.
    #[test]
    fn feat065_ac11_body_hash_identity_never_discharges() {
        const BEFORE: &str = "(module (func (result i32) i32.const 10 i32.const 0 i32.div_s))";
        const AFTER: &str = "(module (func (result i32) i32.const 10 i32.const 7 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        let s = site_of(&b, 0, "div-by-zero");
        // Non-vacuity: tier-4 identity, open before, SAME site proven after —
        // every other discharge precondition is deliberately satisfied.
        let adv = b.advisories.iter().find(|x| x.site_key == s).unwrap();
        assert!(
            !adv.ident_survives_own_edit && !adv.id_build_local,
            "fixture must sit on the body-shape-hash tier"
        );
        assert!(
            a.advisories
                .iter()
                .any(|x| x.site_key == s && x.class == AdvisoryClass::LeverageableFact),
            "after-fixture must prove the same site safe (the bait must be real)"
        );
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s && v.code == "div-by-zero")
            .unwrap_or_else(|| panic!("the obligation needs a verdict; got {:?}", rep.verdicts));
        assert_eq!(v.verdict, VerifyVerdict::Uncertain, "{v:?}");
        assert_eq!(
            rep.count(VerifyVerdict::Discharged),
            0,
            "discharged must be UNREACHABLE on the stripped/unnamed shape"
        );
    }

    /// FEAT-065 AC4 term (2): a BUILD-LOCAL identity (shared stripped name →
    /// raw disambiguated name, FEAT-077) is not comparable across builds, so
    /// even a perfect-looking open→safe transition at a matching key degrades
    /// to `uncertain`.
    #[test]
    fn feat065_ac4_build_local_identity_never_discharges() {
        const BEFORE: &str = "(module \
             (func $\"_ZN3dep7generic17haaaaaaaaaaaaaaaaE\" (result i32) \
               i32.const 10 i32.const 0 i32.div_s) \
             (func $\"_ZN3dep7generic17hbbbbbbbbbbbbbbbbE\" (result i32) \
               i32.const 12 i32.const 6 i32.div_s))";
        const AFTER: &str = "(module \
             (func $\"_ZN3dep7generic17haaaaaaaaaaaaaaaaE\" (result i32) \
               i32.const 10 i32.const 7 i32.div_s) \
             (func $\"_ZN3dep7generic17hbbbbbbbbbbbbbbbbE\" (result i32) \
               i32.const 12 i32.const 6 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        let s = site_of(&b, 0, "div-by-zero");
        let adv = b.advisories.iter().find(|x| x.site_key == s).unwrap();
        assert!(
            adv.id_build_local && adv.ident_survives_own_edit,
            "fixture must sit on the build-local raw-name tier; got {adv:?}"
        );
        assert!(
            a.advisories
                .iter()
                .any(|x| x.site_key == s && x.class == AdvisoryClass::LeverageableFact),
            "after-fixture must prove the same site safe (the bait must be real)"
        );
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s && v.code == "div-by-zero")
            .unwrap_or_else(|| panic!("the obligation needs a verdict; got {:?}", rep.verdicts));
        assert_eq!(v.verdict, VerifyVerdict::Uncertain, "{v:?}");
        assert_eq!(rep.count(VerifyVerdict::Discharged), 0);
    }

    /// FEAT-065 AC12 (ADVERSARIAL — pre-rework this produced ZERO verdicts):
    /// an edit that INTRODUCES a new obligation at a site with no prior
    /// advisory gets a verdict, and the gate fails — an agent that fixed A
    /// while breaking B must not pass clean.
    #[test]
    fn feat065_ac12_introduced_obligation_gets_a_verdict_and_fails_the_gate() {
        const BEFORE: &str = "(module (func $f (param i32) (result i32) \
             i32.const 10 i32.const 7 i32.div_s))";
        const AFTER: &str = "(module (func $f (param i32) (result i32) \
             i32.const 10 i32.const 7 i32.div_s \
             i32.const 20 local.get 0 i32.div_s i32.add))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        // Non-vacuity: the after-run must actually carry a NEW open obligation
        // at a site the before-run has no advisory for.
        let new_site = site_of(&a, 0, "div-by-zero");
        assert!(
            !b.advisories.iter().any(|x| x.site_key == new_site),
            "the new obligation's site must have no prior advisory"
        );
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == new_site && v.code == "div-by-zero")
            .unwrap_or_else(|| {
                panic!(
                    "an introduced obligation MUST get a verdict; got {:?}",
                    rep.verdicts
                )
            });
        assert!(v.introduced, "{v:?}");
        assert!(v.before_func_index.is_none());
        assert!(
            !rep.gate_pass(),
            "introducing an obligation must not pass clean"
        );
        assert_eq!(rep.exit_code(), 1);
        assert_eq!(
            rep.count(VerifyVerdict::Regressed),
            0,
            "the untouched safe site did not regress; got {:?}",
            rep.verdicts
        );
    }

    /// FEAT-065: an identity whose position moved while its body shape did NOT
    /// change (a function inserted ahead of it shifts `func_index`) is
    /// `moved` — informational, not progress, and not an edit signal.
    #[test]
    fn feat065_moved_position_shift_with_unchanged_body_is_moved() {
        const BEFORE: &str = "(module \
             (func $t (param i32) (result i32) i32.const 10 local.get 0 i32.div_s))";
        const AFTER: &str = "(module \
             (func $pad (result i32) i32.const 1) \
             (func $t (param i32) (result i32) i32.const 10 local.get 0 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        let s = site_of(&b, 0, "div-by-zero");
        assert_eq!(
            s,
            site_of(&a, 1, "div-by-zero"),
            "identity must survive the shift"
        );
        assert!(
            !a.advisories.iter().any(|x| x.func_index == 0),
            "the inserted pad function must itself be advisory-free"
        );
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s && v.code == "div-by-zero")
            .unwrap_or_else(|| panic!("the obligation needs a verdict; got {:?}", rep.verdicts));
        assert_eq!(v.verdict, VerifyVerdict::Moved, "{v:?}");
        assert_eq!(v.before_func_index, Some(0));
        assert_eq!(v.after_func_index, Some(1));
        assert!(rep.gate_pass(), "moved is informational");
    }

    /// FEAT-065 / FEAT-087 consumer rule: on the body-shape-hash tier an edit
    /// DESTROYS the identity, so the vanished before-site is `uncertain` —
    /// NEVER `removed-with-code` (a missing key is not evidence the code is
    /// gone). The churned after-sites surface as `introduced` and fail the
    /// gate: on a stripped module the loop honestly cannot converge (AC5),
    /// which must show up as a failed gate plus uncertainty, not as invented
    /// removals.
    #[test]
    fn feat065_identity_churn_on_the_hash_tier_is_not_removal() {
        const BEFORE: &str = "(module (func (result i32) i32.const 10 i32.const 0 i32.div_s))";
        const AFTER: &str = "(module (func (result i32) nop i32.const 10 i32.const 0 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        let s = site_of(&b, 0, "div-by-zero");
        // Non-vacuity: the shape edit must actually churn the identity — the
        // before-site must be ABSENT from the after run.
        assert!(
            !a.advisories.iter().any(|x| x.site_key == s),
            "fixture must churn the tier-4 identity (site absent after)"
        );
        let v = rep
            .verdicts
            .iter()
            .find(|v| v.site_key == s && v.code == "div-by-zero")
            .unwrap_or_else(|| panic!("the obligation needs a verdict; got {:?}", rep.verdicts));
        assert_eq!(
            v.verdict,
            VerifyVerdict::Uncertain,
            "a missing tier-4 key is churn, not evidence of removal: {v:?}"
        );
        assert_eq!(
            rep.count(VerifyVerdict::RemovedWithCode),
            0,
            "no removal may be invented from identity churn; got {:?}",
            rep.verdicts
        );
        assert!(
            rep.verdicts.iter().any(|v| v.introduced),
            "the churned after-sites must surface as introduced"
        );
        assert!(
            !rep.gate_pass(),
            "on the stripped shape the loop honestly cannot converge (AC5)"
        );
    }

    /// FEAT-065: an AMBIGUOUS site (two byte-identical unnamed bodies share
    /// one identity) whose population CHANGED — one copy's divisor fixed
    /// `0 → 7`, an immediate edit the shape hash cannot see — must stay
    /// `uncertain`: attribution of a change inside an ambiguous group is
    /// exactly what cannot be done, and `still-open-untouched` here would tell
    /// the agent its (real) fix touched nothing. Only an ambiguous group whose
    /// population is unchanged WHOLESALE adjudicates to still-open (AC9 on
    /// scry's own module: 30 verdicts sit on such sites).
    #[test]
    fn feat065_ambiguous_site_with_changed_population_stays_uncertain() {
        const BEFORE: &str = "(module \
             (func (result i32) i32.const 8 i32.const 0 i32.div_s) \
             (func (result i32) i32.const 8 i32.const 0 i32.div_s))";
        const AFTER: &str = "(module \
             (func (result i32) i32.const 8 i32.const 0 i32.div_s) \
             (func (result i32) i32.const 8 i32.const 7 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        let s = site_of(&b, 0, "div-by-zero");
        // Non-vacuity: the site must be ambiguous in BOTH runs (the immediate
        // edit does not change the shape hash) and the after run must carry
        // the proven-safe bait.
        for (r, name) in [(&b, "before"), (&a, "after")] {
            let claimants: alloc::collections::BTreeSet<u32> = r
                .advisories
                .iter()
                .filter(|x| x.site_key == s)
                .map(|x| x.func_index)
                .collect();
            assert!(
                claimants.len() > 1,
                "the {name} run must keep the site ambiguous; got {claimants:?}"
            );
        }
        assert!(
            a.advisories
                .iter()
                .any(|x| x.site_key == s && x.class == AdvisoryClass::LeverageableFact),
            "the fixed copy must be proven safe (the bait must be real)"
        );
        let open_verdicts: alloc::vec::Vec<_> = rep
            .verdicts
            .iter()
            .filter(|v| v.site_key == s && v.code == "div-by-zero")
            .collect();
        assert!(
            !open_verdicts.is_empty(),
            "the duplicated obligations need verdicts; got {:?}",
            rep.verdicts
        );
        for v in open_verdicts {
            assert_eq!(
                v.verdict,
                VerifyVerdict::Uncertain,
                "a changed ambiguous population cannot be attributed: {v:?}"
            );
        }
        assert_eq!(rep.count(VerifyVerdict::Discharged), 0);
        assert_eq!(
            rep.count(VerifyVerdict::StillOpenUntouched),
            0,
            "{:?}",
            rep.verdicts
        );
    }

    /// FEAT-065: the count-aware regression check — one copy of a duplicated
    /// (ambiguous) site regressing from proven-safe to open must alarm even
    /// though a sibling copy was open all along (a presence-only check would
    /// see `div-by-zero` already open and stay silent).
    #[test]
    fn feat065_regression_inside_a_duplicated_site_still_alarms() {
        const BEFORE: &str = "(module \
             (func (result i32) i32.const 8 i32.const 0 i32.div_s) \
             (func (result i32) i32.const 8 i32.const 7 i32.div_s))";
        const AFTER: &str = "(module \
             (func (result i32) i32.const 8 i32.const 0 i32.div_s) \
             (func (result i32) i32.const 8 i32.const 0 i32.div_s))";
        let (b, a, rep) = adjudicate(BEFORE, AFTER);
        let s = site_of(&b, 0, "div-by-zero");
        // Non-vacuity: before has one open + one safe copy at the SAME key;
        // after has two open copies.
        let count = |r: &AnalysisResult, open: bool| {
            r.advisories
                .iter()
                .filter(|x| x.site_key == s && x.class.is_open_obligation() == open)
                .count()
        };
        assert!(
            count(&b, true) >= 1 && count(&b, false) >= 1,
            "before must mix open and safe copies at one key"
        );
        assert!(
            count(&a, true) > count(&b, true),
            "after must have MORE open copies"
        );
        assert!(
            rep.count(VerifyVerdict::Regressed) >= 1,
            "a regressed duplicate must alarm despite an open sibling; got {:?}",
            rep.verdicts
        );
        assert!(!rep.gate_pass());
    }
    /// FEAT-064 AC5, the half that was never tested. AC5 states a GENERAL
    /// property — "one operator raising several obligations gets DISTINCT ids;
    /// the site alone is not a discriminator" — and
    /// `feat064_two_obligations_at_one_pc_get_distinct_ids` verified it for
    /// OPEN obligations only. Measured 2026-08-27: NONE of the five FEAT-064
    /// tests referenced `proven-safe` or `LeverageableFact`, and the identical
    /// property was BROKEN for them through the whole FEAT-064/077/087 identity
    /// arc — two facts at one pc (`i32.div_s` proving both divide-by-zero-safe
    /// AND INT_MIN/-1-overflow-safe) shared a single `obligation_id`.
    ///
    /// FEAT-089 repaired the mechanism (`id_codes` keys a proven-safe advisory
    /// by the obligation code it discharges) but left no oracle. This is it: a
    /// change to that keying must not silently restore the collision.
    #[test]
    fn feat064_ac5_two_proven_safe_facts_at_one_pc_get_distinct_ids() {
        // Both operands constant: div-by-zero AND signed-overflow are both
        // provable, so one pc yields two LeverageableFact advisories.
        let r = analyze_default(
            "(module (func $d (export \"d\") (result i32) \
               i32.const 10 i32.const 2 i32.div_s))",
        );
        let ps: alloc::vec::Vec<&Advisory> = r
            .advisories
            .iter()
            .filter(|a| a.code == "proven-safe" && !a.obligation_id.is_empty())
            .collect();
        // Non-vacuity: without two facts at one pc there is nothing to collide.
        assert_eq!(
            ps.len(),
            2,
            "fixture must yield TWO proven-safe facts at one pc; got {:?}",
            ps.iter().map(|a| &a.detail).collect::<alloc::vec::Vec<_>>()
        );
        assert_eq!(ps[0].pc, ps[1].pc, "precondition: both facts share a pc");
        assert_ne!(
            ps[0].obligation_id, ps[1].obligation_id,
            "two DISTINCT proven-safe facts at one pc must have distinct ids; \
             the site alone is not a discriminator (FEAT-064 AC5), and this \
             held for open obligations while silently failing here"
        );
        // The site key SHOULD match — it deliberately excludes the code.
        assert_eq!(
            ps[0].site_key, ps[1].site_key,
            "site_key excludes the code, so both facts share a site"
        );
    }
    /// FEAT-067 AC1: a consumer filters by class / code / function / operator /
    /// gap kind and receives ONLY the matching records, each carrying its stable
    /// obligation identity (REQ-020).
    #[test]
    fn feat067_ac1_filters_select_only_matching_records_with_their_ids() {
        // Two functions: one divides (div-by-zero + signed-overflow + a
        // proven-safe), one uses an unmodelled op (a gap).
        let r = analyze_default(
            "(module (memory 1) \
               (func $a (export \"a\") (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $b (export \"b\") (param i32) \
                 local.get 0 i32.const 3 i32.store8))",
        );
        assert!(
            r.advisories.len() >= 3,
            "non-vacuity: fixture must raise several advisories; got {}",
            r.advisories.len()
        );

        // everything
        let all = r.query(&Query::default());
        assert_eq!(
            all.len(),
            r.advisories.len(),
            "an unconstrained query is the identity of a conjunction: it selects all"
        );

        // by code
        let dbz = r.query(&Query {
            code: Some("div-by-zero".into()),
            ..Query::default()
        });
        assert!(!dbz.is_empty(), "fixture must contain a div-by-zero");
        assert!(
            dbz.iter().all(|a| a.code == "div-by-zero"),
            "a code filter must return ONLY that code"
        );
        assert!(
            dbz.iter().all(|a| !a.obligation_id.is_empty()),
            "every returned record carries its stable obligation id (REQ-020)"
        );

        // by class
        let unproven = r.query(&Query {
            class: Some(AdvisoryClass::UnprovenObligation),
            ..Query::default()
        });
        assert!(
            !unproven.is_empty(),
            "fixture must contain an UnprovenObligation"
        );
        assert!(
            unproven
                .iter()
                .all(|a| a.class == AdvisoryClass::UnprovenObligation)
        );

        // by function — and it must EXCLUDE the other function
        let f0 = r.query(&Query {
            func_index: Some(0),
            ..Query::default()
        });
        assert!(!f0.is_empty(), "function 0 must have advisories");
        assert!(
            f0.iter().all(|a| a.func_index == 0),
            "func filter must exclude func 1"
        );
        assert!(
            r.advisories.iter().any(|a| a.func_index != 0),
            "non-vacuity: the fixture must have advisories OUTSIDE function 0, \
             else 'excludes the other function' is untested"
        );

        // CONJUNCTIVE: both constraints must hold
        let both = r.query(&Query {
            code: Some("div-by-zero".into()),
            func_index: Some(0),
            ..Query::default()
        });
        assert!(
            both.iter()
                .all(|a| a.code == "div-by-zero" && a.func_index == 0)
        );
        let impossible = r.query(&Query {
            code: Some("div-by-zero".into()),
            func_index: Some(9999),
            ..Query::default()
        });
        assert!(
            impossible.is_empty(),
            "constraints are ANDed: an unsatisfiable pair selects nothing"
        );
    }

    /// FEAT-067: `op` and `gap_kind` are not Advisory fields — they are joined
    /// from the gap/trap-check record at the same `(func_index, pc)`. That join
    /// is the part that can be wrong, so it is tested separately.
    #[test]
    fn feat067_op_and_gap_kind_are_joined_from_the_site() {
        let r = analyze_default(
            "(module (memory 1) (func $b (export \"b\") (param i32) \
               local.get 0 i32.const 3 i32.store8))",
        );
        let ops: alloc::collections::BTreeSet<&str> =
            r.gaps.iter().map(|g| g.op.as_str()).collect();
        assert!(
            !ops.is_empty(),
            "non-vacuity: the fixture must produce gaps to join against"
        );
        let some_op = ops.iter().next().unwrap().to_string();
        let by_op = r.query(&Query {
            op: Some(some_op.clone()),
            ..Query::default()
        });
        assert!(
            !by_op.is_empty(),
            "an operator present in the gap records must select its advisories: {some_op:?} \
             among {ops:?}"
        );
        // a wasm-format name that is NOT in this module selects nothing
        let none = r.query(&Query {
            op: Some("f64.sqrt".into()),
            ..Query::default()
        });
        assert!(none.is_empty(), "an absent operator selects nothing");
    }
}
