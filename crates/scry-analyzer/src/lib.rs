//! scry-analyzer — the scry analyzer as a Wasm component (thin wrapper).
//!
//! Implements the `analyzer.analyze` function defined in `wit/scry.wit`
//! (derived from `spar/scry.aadl` per DD-010).
//!
//! ## DD-012: this crate is now a thin canonical-ABI wrapper
//!
//! Through v1.1 the entire abstract-interpretation pipeline lived in this
//! file, welded to the wit-bindgen-generated types and the `Guest` trait.
//! That made the analyzer's real decisions impossible to instrument for
//! witness MC/DC (witness wants a core module; the analyzer is a wasip2
//! component) and impossible to reuse outside the component ABI.
//!
//! DD-012 (FEAT-014) extracts the logic into the pure, bindgen-free
//! [`scry_analyze_core`] crate — the wasmparser parse, the interval +
//! region-memory fixpoint, the call-graph / SCC / summary machinery, and
//! the taint (noninterference) walk all live there now, operating on plain
//! Rust types. This crate keeps only:
//!
//!   * `struct Component` and the `Guest` impl (the export surface);
//!   * the field-by-field conversions between the wit-bindgen types and the
//!     core's plain-Rust mirrors — pure boilerplate, no analysis;
//!   * the `export!` macro.
//!
//! The conversions are a straight copy because every core mirror type has
//! the same fields/variants as its WIT counterpart (the core was authored
//! that way). The only nominal difference is the region payload: WIT calls
//! it `region-pointer-payload`, the core reuses [`scry_interval::Region`] —
//! same `{region_id, offset}` shape.
//!
//! For the analysis itself — scope discipline, soundness arguments,
//! per-version history (v0.2 interval fixpoint, v0.3 region memory, v0.4
//! call graph, v0.5 summaries, FEAT-009 taint) — see the module docs in
//! [`scry_analyze_core`].

#![no_std]
extern crate alloc;

use alloc::vec::Vec;

use scry_analyze_core as ac;
use scry_analyzer_component_bindings::exports::pulseengine::scry::analyzer as wit;
use scry_analyzer_component_bindings::exports::pulseengine::scry::analyzer::Guest;

struct Component;

impl Guest for Component {
    fn analyze(
        module_bytes: Vec<u8>,
        config: wit::AnalysisConfig,
    ) -> Result<wit::AnalysisResult, wit::AnalyzeError> {
        match ac::analyze(module_bytes, config_to_core(config)) {
            Ok(result) => Ok(result_to_wit(result)),
            Err(err) => Err(error_to_wit(err)),
        }
    }
}

// ───────────────────────── WIT → core (inputs) ─────────────────────────

fn config_to_core(c: wit::AnalysisConfig) -> ac::AnalysisConfig {
    ac::AnalysisConfig {
        widening_threshold: c.widening_threshold,
        emit_diagnostics: c.emit_diagnostics,
        taint_policy: c.taint_policy.map(taint_policy_to_core),
    }
}

fn taint_policy_to_core(p: wit::TaintPolicy) -> ac::TaintPolicy {
    ac::TaintPolicy {
        high_params: p.high_params,
        low_results: p.low_results,
    }
}

// ───────────────────────── core → WIT (outputs) ────────────────────────

fn stack_bound_to_wit(b: ac::StackBound) -> wit::StackBound {
    match b {
        ac::StackBound::Bytes(n) => wit::StackBound::Bytes(n),
        ac::StackBound::Unbounded => wit::StackBound::Unbounded,
        ac::StackBound::Unknown => wit::StackBound::Unknown,
    }
}

fn function_stack_to_wit(f: ac::FunctionStack) -> wit::FunctionStack {
    wit::FunctionStack {
        func_index: f.func_index,
        frame: stack_bound_to_wit(f.frame),
        max_stack: stack_bound_to_wit(f.max_stack),
    }
}

fn stack_usage_to_wit(s: ac::StackUsage) -> wit::StackUsage {
    wit::StackUsage {
        sp_global: s.sp_global,
        functions: s.functions.into_iter().map(function_stack_to_wit).collect(),
        max_stack_bytes: stack_bound_to_wit(s.max_stack_bytes),
    }
}

fn result_to_wit(r: ac::AnalysisResult) -> wit::AnalysisResult {
    wit::AnalysisResult {
        invariants: bundle_to_wit(r.invariants),
        diagnostics: r.diagnostics.into_iter().map(diagnostic_to_wit).collect(),
        call_graph: r.call_graph.into_iter().map(call_edge_to_wit).collect(),
        function_summaries: r
            .function_summaries
            .into_iter()
            .map(summary_to_wit)
            .collect(),
        provenance: r.provenance.map(provenance_to_wit),
        taint_findings: r
            .taint_findings
            .into_iter()
            .map(taint_finding_to_wit)
            .collect(),
        stack_usage: stack_usage_to_wit(r.stack_usage),
    }
}

fn bundle_to_wit(b: ac::InvariantBundle) -> wit::InvariantBundle {
    wit::InvariantBundle {
        schema: b.schema,
        module_sha256: b.module_sha256,
        points: b.points.into_iter().map(point_to_wit).collect(),
    }
}

fn point_to_wit(p: ac::ProgramPoint) -> wit::ProgramPoint {
    wit::ProgramPoint {
        func_index: p.func_index,
        pc: p.pc,
        locals: p.locals.into_iter().map(local_to_wit).collect(),
    }
}

fn local_to_wit(l: ac::LocalInvariant) -> wit::LocalInvariant {
    wit::LocalInvariant {
        local_index: l.local_index,
        value: value_to_wit(l.value),
    }
}

fn value_to_wit(v: ac::AbstractValue) -> wit::AbstractValue {
    match v {
        ac::AbstractValue::I32Interval(iv) => wit::AbstractValue::I32Interval(interval_to_wit(iv)),
        ac::AbstractValue::I64Interval(iv) => wit::AbstractValue::I64Interval(interval_to_wit(iv)),
        ac::AbstractValue::RegionPointer(r) => wit::AbstractValue::RegionPointer(region_to_wit(r)),
        ac::AbstractValue::Unknown => wit::AbstractValue::Unknown,
    }
}

fn interval_to_wit(iv: ac::Interval) -> wit::Interval {
    wit::Interval {
        lo: iv.lo,
        hi: iv.hi,
    }
}

fn region_to_wit(r: ac::Region) -> wit::RegionPointerPayload {
    wit::RegionPointerPayload {
        region_id: r.region_id,
        offset: interval_to_wit(r.offset),
    }
}

fn diagnostic_to_wit(d: ac::Diagnostic) -> wit::Diagnostic {
    wit::Diagnostic {
        severity: severity_to_wit(d.severity),
        func_index: d.func_index,
        pc: d.pc,
        message: d.message,
    }
}

fn severity_to_wit(s: ac::DiagnosticSeverity) -> wit::DiagnosticSeverity {
    match s {
        ac::DiagnosticSeverity::Info => wit::DiagnosticSeverity::Info,
        ac::DiagnosticSeverity::Warning => wit::DiagnosticSeverity::Warning,
        ac::DiagnosticSeverity::UnsoundnessFallback => wit::DiagnosticSeverity::UnsoundnessFallback,
    }
}

fn call_edge_to_wit(e: ac::CallEdge) -> wit::CallEdge {
    wit::CallEdge {
        caller_func: e.caller_func,
        pc: e.pc,
        indirect: e.indirect,
        resolved_targets: e.resolved_targets,
        soundness: soundness_to_wit(e.soundness),
    }
}

fn soundness_to_wit(s: ac::SoundnessTag) -> wit::SoundnessTag {
    match s {
        ac::SoundnessTag::Sound => wit::SoundnessTag::Sound,
        ac::SoundnessTag::UnsoundFallback => wit::SoundnessTag::UnsoundFallback,
    }
}

fn summary_to_wit(s: ac::FunctionSummary) -> wit::FunctionSummary {
    wit::FunctionSummary {
        func_index: s.func_index,
        param_count: s.param_count,
        result_summary: s.result_summary.into_iter().map(value_to_wit).collect(),
        context_sensitive: s.context_sensitive,
        recursive: s.recursive,
    }
}

fn provenance_to_wit(p: ac::ComponentProvenance) -> wit::ComponentProvenance {
    wit::ComponentProvenance {
        premises: wit::FusionPremises {
            bounded_memory: p.premises.bounded_memory,
            closed_world: p.premises.closed_world,
        },
        fused_module_sha256: p.fused_module_sha256.to_vec(),
        origins: p.origins.into_iter().map(origin_to_wit).collect(),
    }
}

fn origin_to_wit(o: ac::ComponentOrigin) -> wit::ComponentOrigin {
    wit::ComponentOrigin {
        fused_func_index: o.fused_func_index,
        component_id: o.component_id,
        orig_func_index: o.orig_func_index,
        code_range: o.code_range.map(|c| wit::CodeRange {
            start: c.start,
            end: c.end,
        }),
    }
}

fn taint_finding_to_wit(f: ac::TaintFinding) -> wit::TaintFinding {
    wit::TaintFinding {
        func_index: f.func_index,
        pc: f.pc,
        kind: finding_kind_to_wit(f.kind),
        source_label: label_to_wit(f.source_label),
        sink_label: label_to_wit(f.sink_label),
        message: f.message,
    }
}

fn finding_kind_to_wit(k: ac::TaintFindingKind) -> wit::TaintFindingKind {
    match k {
        ac::TaintFindingKind::HighResultExplicit => wit::TaintFindingKind::HighResultExplicit,
        ac::TaintFindingKind::HighResultImplicit => wit::TaintFindingKind::HighResultImplicit,
    }
}

fn label_to_wit(l: ac::SecurityLabel) -> wit::SecurityLabel {
    match l {
        ac::SecurityLabel::Low => wit::SecurityLabel::Low,
        ac::SecurityLabel::High => wit::SecurityLabel::High,
    }
}

fn error_to_wit(e: ac::AnalyzeError) -> wit::AnalyzeError {
    match e {
        ac::AnalyzeError::InvalidModule(m) => wit::AnalyzeError::InvalidModule(m),
        ac::AnalyzeError::InvalidConfig(m) => wit::AnalyzeError::InvalidConfig(m),
        ac::AnalyzeError::Internal(m) => wit::AnalyzeError::Internal(m),
    }
}

scry_analyzer_component_bindings::export!(Component with_types_in scry_analyzer_component_bindings);
