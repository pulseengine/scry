//! scry-mcdc — witness MC/DC harness over the real analyzer core.
//!
//! FEAT-014 / DD-012. This crate exists for one purpose: let `witness`
//! reconstruct an MC/DC truth table over the analyzer's *real* decisions —
//! the same [`scry_analyze_core::analyze`] body the shipped component runs —
//! measured over the in-repo corpus fixtures (`crates/scry-analyzer/
//! test-fixtures/`), not a synthetic re-implementation.
//!
//! ## Why drive the corpus instead of synthetic inputs
//!
//! witness proves a condition under MC/DC only when it finds an independent-
//! effect pair: two executions where that condition flips, the other shared
//! conditions agree (masking), and the decision's outcome differs. A single
//! no-arg export is one fixed execution → one truth-table row → no pair
//! possible. (This is exactly why the v1.2 spike that swept synthetic domain
//! inputs proved zero conditions.)
//!
//! So each `run_*` export below drives the *same* `analyze` entry over a
//! different (fixture, config) pair. Five structurally different fixtures —
//! constant-fold, a bounded param, region/bounds, `call_indirect`, and
//! interprocedural summaries — crossed with config variants (taint on/off,
//! diagnostics on/off, widening threshold 1 vs 3) hit the branchy decisions
//! inside `analyze` / `interpret_op` / `run_taint_analysis` /
//! `handle_call*` with genuinely varied operands. `witness run
//! --invoke-all` calls every export, accumulating the per-branch counters
//! across all of them, so flipping pairs exist for the decisions the corpus
//! actually exercises.
//!
//! The fixtures are baked in as pre-assembled core-Wasm bytes (the `.wat`
//! sources assembled with `wasm-tools parse`); the harness owns no analysis
//! logic of its own.

// The harness shell uses `std` (wasm32-wasip1 provides it): std supplies the
// global allocator + panic handler, so the harness needs no `#[no_std]`
// allocator wiring of its own. This does not affect the MC/DC measurement —
// witness attributes reconstructed Decisions to their DWARF source file, and
// the decisions we measure live in the `#![no_std]` scry-analyze-core
// (`lib.rs`), not in the harness shell.

use scry_analyze_core::{AbstractValue, AnalysisConfig, AnalysisResult, TaintPolicy, analyze};

// ── The corpus, baked in as assembled core-Wasm bytes ───────────────────
const FIXTURE_CONST_FOLD: &[u8] = include_bytes!("../fixtures/fixture-01-constant-fold.wasm");
const FIXTURE_WITH_PARAM: &[u8] = include_bytes!("../fixtures/fixture-02-with-param.wasm");
const FIXTURE_REGION: &[u8] = include_bytes!("../fixtures/fixture-03-region-bounds.wasm");
const FIXTURE_CALL_INDIRECT: &[u8] = include_bytes!("../fixtures/fixture-04-call-indirect.wasm");
const FIXTURE_INTERPROC: &[u8] = include_bytes!("../fixtures/fixture-05-interproc.wasm");
/// Overflow/underflow inputs that flip the transfer functions' straddle→TOP
/// guard to TRUE (the small-constant corpus only ever gives the FALSE
/// polarity), so witness can form the MC/DC independence pair.
const FIXTURE_OVERFLOW: &[u8] = include_bytes!("../fixtures/fixture-06-overflow.wasm");
/// Counted loop (block + loop + br_if, empty block type) with a loop-invariant
/// local — drives the FEAT-016 structured-control / write-set-havoc path in
/// run_function_body so those decisions are MC/DC-covered by the live gate.
const FIXTURE_COUNTED_LOOP: &[u8] = include_bytes!("../fixtures/fixture-08-counted-loop.wasm");
/// Loop writing a local to a constant each iteration — drives the FEAT-016
/// slice-2a iterate-then-widen loop fixpoint (the converging-local path).
const FIXTURE_LOOP_CONVERGE: &[u8] = include_bytes!("../fixtures/fixture-09-loop-converge.wasm");
/// Guard-bounded counted loop (`br_if (i >= 10)`) — drives the FEAT-016
/// slice-2b-i guard-refinement + narrowing decisions (`try_guard_brif`,
/// `refine_interval`, the loop_region narrowing phase) so they are covered.
const FIXTURE_GUARD_BOUND: &[u8] = include_bytes!("../fixtures/fixture-10-guard-bound.wasm");
/// Variable-bounded counted loop (`i < n`, n in a local) — drives the FEAT-016
/// slice-2b-ii octagon-product decisions (`try_guard_brif_rel`,
/// `octagon_transfer`/`classify_store`, `refine_octagon_rel`, `reduce_locals`,
/// the lockstep octagon join/widen/narrow in loop_region) so they are covered.
const FIXTURE_VAR_BOUND: &[u8] = include_bytes!("../fixtures/fixture-11-var-bound.wasm");

// ── Config variants — each flips a different family of analyze decisions ─

/// Baseline: widening threshold 3, diagnostics on, no taint policy.
fn cfg_default() -> AnalysisConfig {
    AnalysisConfig {
        widening_threshold: Some(3),
        emit_diagnostics: true,
        taint_policy: None,
    }
}

/// Widening threshold 1 — exercises the early-widen decision branches.
fn cfg_widen1() -> AnalysisConfig {
    AnalysisConfig {
        widening_threshold: Some(1),
        emit_diagnostics: true,
        taint_policy: None,
    }
}

/// Diagnostics off — flips every `if emit_diagnostics` guard.
fn cfg_no_diag() -> AnalysisConfig {
    AnalysisConfig {
        widening_threshold: Some(3),
        emit_diagnostics: false,
        taint_policy: None,
    }
}

/// Taint policy: param 0 is a High source, result 0 must stay Low — drives
/// `run_taint_analysis` and its High→Low finding decisions.
fn cfg_taint() -> AnalysisConfig {
    AnalysisConfig {
        widening_threshold: Some(3),
        emit_diagnostics: true,
        taint_policy: Some(TaintPolicy {
            high_params: vec![0],
            low_results: vec![0],
        }),
    }
}

/// Taint policy with diagnostics off — taint findings without the diagnostic
/// arm.
fn cfg_taint_no_diag() -> AnalysisConfig {
    AnalysisConfig {
        widening_threshold: Some(3),
        emit_diagnostics: false,
        taint_policy: Some(TaintPolicy {
            high_params: vec![0],
            low_results: vec![0],
        }),
    }
}

/// Fold a full result into one `i32` so the optimizer cannot drop the
/// analysis as dead. Touches every output vector and every abstract-value
/// variant so the whole `analyze` data path stays live.
fn observe(r: &AnalysisResult) -> i32 {
    let mut acc: i64 = 0;
    acc = acc
        .wrapping_add(r.diagnostics.len() as i64)
        .wrapping_mul(31)
        .wrapping_add(r.call_graph.len() as i64)
        .wrapping_mul(31)
        .wrapping_add(r.function_summaries.len() as i64)
        .wrapping_mul(31)
        .wrapping_add(r.taint_findings.len() as i64)
        .wrapping_mul(31)
        .wrapping_add(r.invariants.points.len() as i64);
    for p in &r.invariants.points {
        acc = acc
            .wrapping_add(p.func_index as i64)
            .wrapping_add(p.pc as i64);
        for l in &p.locals {
            acc = acc.wrapping_add(l.local_index as i64);
            fold_value(&l.value, &mut acc);
        }
    }
    for e in &r.call_graph {
        acc = acc
            .wrapping_add(e.caller_func as i64)
            .wrapping_add(e.resolved_targets.len() as i64)
            .wrapping_add(e.indirect as i64);
    }
    for s in &r.function_summaries {
        acc = acc
            .wrapping_add(s.func_index as i64)
            .wrapping_add(s.param_count as i64)
            .wrapping_add(s.recursive as i64)
            .wrapping_add(s.context_sensitive as i64);
        for v in &s.result_summary {
            fold_value(v, &mut acc);
        }
    }
    acc as i32
}

fn fold_value(v: &AbstractValue, acc: &mut i64) {
    match v {
        AbstractValue::I32Interval(iv) | AbstractValue::I64Interval(iv) => {
            *acc = acc.wrapping_mul(31).wrapping_add(iv.lo).wrapping_add(iv.hi);
        }
        AbstractValue::RegionPointer(r) => {
            *acc = acc
                .wrapping_mul(31)
                .wrapping_add(r.region_id as i64)
                .wrapping_add(r.offset.lo)
                .wrapping_add(r.offset.hi);
        }
        AbstractValue::Unknown => {
            *acc = acc.wrapping_mul(31).wrapping_add(7);
        }
    }
}

/// Drive `analyze` once over `(bytes, config)` and fold the outcome live.
/// The input bytes go through `black_box` so the optimizer cannot fold the
/// fixed fixture into a constant analysis result.
#[inline(never)]
fn drive(bytes: &[u8], config: AnalysisConfig) -> i32 {
    let bytes = std::hint::black_box(bytes);
    match analyze(bytes.to_vec(), config) {
        Ok(r) => observe(&r),
        Err(_) => i32::MIN,
    }
}

// ── No-arg exports: every (fixture, config) pair witness --invoke-all runs ─

macro_rules! run_export {
    ($name:ident, $bytes:expr, $cfg:expr) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name() -> i32 {
            drive($bytes, $cfg)
        }
    };
}

run_export!(run_const_fold_default, FIXTURE_CONST_FOLD, cfg_default());
run_export!(run_const_fold_widen1, FIXTURE_CONST_FOLD, cfg_widen1());
run_export!(run_const_fold_no_diag, FIXTURE_CONST_FOLD, cfg_no_diag());

run_export!(run_with_param_default, FIXTURE_WITH_PARAM, cfg_default());
run_export!(run_with_param_taint, FIXTURE_WITH_PARAM, cfg_taint());
run_export!(
    run_with_param_taint_no_diag,
    FIXTURE_WITH_PARAM,
    cfg_taint_no_diag()
);

run_export!(run_region_default, FIXTURE_REGION, cfg_default());
run_export!(run_region_no_diag, FIXTURE_REGION, cfg_no_diag());
run_export!(run_region_widen1, FIXTURE_REGION, cfg_widen1());

run_export!(
    run_call_indirect_default,
    FIXTURE_CALL_INDIRECT,
    cfg_default()
);
run_export!(
    run_call_indirect_no_diag,
    FIXTURE_CALL_INDIRECT,
    cfg_no_diag()
);
run_export!(run_call_indirect_taint, FIXTURE_CALL_INDIRECT, cfg_taint());

run_export!(run_interproc_default, FIXTURE_INTERPROC, cfg_default());
run_export!(run_interproc_widen1, FIXTURE_INTERPROC, cfg_widen1());
run_export!(run_interproc_taint, FIXTURE_INTERPROC, cfg_taint());
run_export!(
    run_interproc_taint_no_diag,
    FIXTURE_INTERPROC,
    cfg_taint_no_diag()
);

// Straddle→TOP closure: these flip the transfer-fn overflow conditions TRUE.
run_export!(run_overflow_default, FIXTURE_OVERFLOW, cfg_default());
run_export!(run_overflow_widen1, FIXTURE_OVERFLOW, cfg_widen1());

// FEAT-016: exercise the structured-control / write-set-havoc decisions.
run_export!(
    run_counted_loop_default,
    FIXTURE_COUNTED_LOOP,
    cfg_default()
);
run_export!(
    run_counted_loop_no_diag,
    FIXTURE_COUNTED_LOOP,
    cfg_no_diag()
);
run_export!(
    run_loop_converge_default,
    FIXTURE_LOOP_CONVERGE,
    cfg_default()
);
run_export!(
    run_loop_converge_widen1,
    FIXTURE_LOOP_CONVERGE,
    cfg_widen1()
);
// FEAT-016 slice-2b-i: exercise the guard-refinement + narrowing decisions.
run_export!(run_guard_bound_default, FIXTURE_GUARD_BOUND, cfg_default());
run_export!(run_guard_bound_widen1, FIXTURE_GUARD_BOUND, cfg_widen1());
// FEAT-016 slice-2b-ii: exercise the octagon-product decisions.
run_export!(run_var_bound_default, FIXTURE_VAR_BOUND, cfg_default());
run_export!(run_var_bound_widen1, FIXTURE_VAR_BOUND, cfg_widen1());

#[cfg(test)]
mod tests {
    use super::*;

    /// On the host (native), every (fixture, config) pair analyzes without
    /// panicking and the folded observation is well-defined. This is the
    /// cheap native gate; the wasm build + witness pipeline is the MC/DC
    /// measurement proper.
    #[test]
    fn every_pair_analyzes() {
        let pairs: &[(&[u8], AnalysisConfig)] = &[
            (FIXTURE_CONST_FOLD, cfg_default()),
            (FIXTURE_WITH_PARAM, cfg_taint()),
            (FIXTURE_REGION, cfg_default()),
            (FIXTURE_CALL_INDIRECT, cfg_default()),
            (FIXTURE_INTERPROC, cfg_taint()),
            (FIXTURE_OVERFLOW, cfg_default()),
            (FIXTURE_COUNTED_LOOP, cfg_default()),
            (FIXTURE_LOOP_CONVERGE, cfg_default()),
            (FIXTURE_GUARD_BOUND, cfg_default()),
            (FIXTURE_VAR_BOUND, cfg_default()),
        ];
        for (bytes, cfg) in pairs {
            let _ = drive(bytes, cfg.clone());
        }
    }
}
