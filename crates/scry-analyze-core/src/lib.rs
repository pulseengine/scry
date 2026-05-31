//! scry-analyze-core — pure, bindgen-free analyzer core (FEAT-014 / DD-012).
//!
//! ## Why this crate exists
//!
//! Through v1.1 the analyzer's decision logic (wasmparser parse + fixpoint
//! + transfer functions) lived in `crates/scry-analyzer/src/lib.rs`, welded
//! to the wit-bindgen-generated types and the `Guest` trait. That made it
//! impossible to (a) instrument the *real* decisions for witness MC/DC
//! (witness wants a core module; the analyzer is a wasip2 component) and
//! (b) reuse the analyzer outside the component ABI.
//!
//! DD-012 extracts that logic into this pure crate. Its result types are
//! plain Rust mirrors of the analyzer's WIT (`crates/scry-analyzer/wit/
//! scry.wit`); the component (`scry-analyzer`) becomes a thin wrapper that
//! converts between the wit-bindgen types and these. Same pure-crate
//! dual-compile pattern as [`scry_interval`] / `scry-taint` / `scry-octagon`
//! / `scry-provenance`: `#![no_std]` + `extern crate alloc`, no bindgen, so
//! it builds natively (host tests + the MC/DC harness), to
//! `wasm32-unknown-unknown` (witness instruments it), and into the shipped
//! `wasm32-wasip2` component.
//!
//! ## Status
//!
//! Step 1 (this commit): the result-type surface only. The analyze body and
//! its ~40 helpers move here in a following step; until then `scry-analyzer`
//! is unchanged and still owns the live logic.
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

use alloc::string::String;
use alloc::vec::Vec;

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
}
