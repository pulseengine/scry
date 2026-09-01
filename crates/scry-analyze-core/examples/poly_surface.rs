//! FEAT-057 slice-2 sizing: how much surface would a polyhedra domain actually
//! have on a real module?
//!
//! WHY THIS IS COMMITTED, and it is a narrow reason. The numbers it prints are
//! cited on FEAT-057 to justify a scheduling decision. A bare number in an
//! artifact is exactly the drift hazard that left "the dev REQ-* carry no
//! verifies link by construction" checked in and false for months. RE-RUN THIS
//! after FEAT-095 (region-havoc coverage) lands, and after any change to the
//! octagon or the fixpoint, and check whether the answer moved.
//!
//!   cargo run --release -p scry-sai-core --example poly_surface -- <module.wasm>
//!
//! FEAT-069 taught the lesson — measure the ceiling before building. The
//! octagon already emits `ProgramPoint.relational`, filtered to constraints
//! NOT implied by the unary intervals. Those points are where a relational
//! domain is carrying real information, and they bound what polyhedra can
//! improve: a point where the octagon is degraded to top is degraded for
//! polyhedra too, because both ride the same fixpoint and the same havoc.
use scry_analyze_core::{AnalysisConfig, GapKind, analyze};
use std::collections::{BTreeMap, BTreeSet};

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: poly_surface <module.wasm>");
    let bytes = std::fs::read(&path).expect("read module");
    let r = analyze(
        bytes,
        AnalysisConfig {
            emit_diagnostics: true,
            ..Default::default()
        },
    )
    .expect("analysis");

    let pts = &r.invariants.points;
    let total_pts = pts.len();
    let funcs_with_pts: BTreeSet<u32> = pts.iter().map(|p| p.func_index).collect();

    // Points carrying >=1 genuinely-relational octagon constraint.
    let rel_pts: Vec<_> = pts.iter().filter(|p| !p.relational.is_empty()).collect();
    let rel_funcs: BTreeSet<u32> = rel_pts.iter().map(|p| p.func_index).collect();
    let total_rel: usize = pts.iter().map(|p| p.relational.len()).sum();

    // Functions degraded by region havoc / full scrub.
    let mut gap_funcs: BTreeMap<&'static str, BTreeSet<u32>> = BTreeMap::new();
    for g in &r.gaps {
        let k = match g.kind {
            GapKind::UnsupportedOp => "unsupported-op",
            GapKind::UnmodeledBranch => "unmodeled-branch",
            GapKind::UnmodeledMemoryAddress => "unmodeled-mem-addr",
            GapKind::UnmodeledControlFlow => "unmodeled-control-flow",
        };
        gap_funcs.entry(k).or_default().insert(g.func_index);
    }
    let havoc: BTreeSet<u32> = gap_funcs
        .get("unmodeled-control-flow")
        .cloned()
        .unwrap_or_default();
    let scrub: BTreeSet<u32> = gap_funcs.get("unsupported-op").cloned().unwrap_or_default();
    let any_gap: BTreeSet<u32> = gap_funcs.values().flatten().copied().collect();
    let clean: BTreeSet<u32> = funcs_with_pts.difference(&any_gap).copied().collect();

    println!("module            : {path}");
    println!("functions (meta)  : {}", r.function_meta.len());
    println!("functions w/ pts  : {}", funcs_with_pts.len());
    println!("program points    : {total_pts}");
    println!();
    println!("--- gap population, by function ---");
    for (k, s) in &gap_funcs {
        println!(
            "  {k:<24} {:>6} functions, {:>7} gaps",
            s.len(),
            r.gaps
                .iter()
                .filter(|g| match g.kind {
                    GapKind::UnsupportedOp => *k == "unsupported-op",
                    GapKind::UnmodeledBranch => *k == "unmodeled-branch",
                    GapKind::UnmodeledMemoryAddress => *k == "unmodeled-mem-addr",
                    GapKind::UnmodeledControlFlow => *k == "unmodeled-control-flow",
                })
                .count()
        );
    }
    println!("  {:<24} {:>6} functions", "ANY gap", any_gap.len());
    println!(
        "  {:<24} {:>6} functions",
        "NO gap (fully modelled)",
        clean.len()
    );
    println!();
    println!("--- THE POLYHEDRA CEILING: where a relational domain carries info ---");
    println!(
        "  points with >=1 relational constraint : {} / {total_pts}  ({:.2}%)",
        rel_pts.len(),
        100.0 * rel_pts.len() as f64 / total_pts.max(1) as f64
    );
    println!("  total relational constraints          : {total_rel}");
    println!(
        "  functions with >=1 relational point   : {} / {}  ({:.2}%)",
        rel_funcs.len(),
        funcs_with_pts.len(),
        100.0 * rel_funcs.len() as f64 / funcs_with_pts.len().max(1) as f64
    );
    println!();
    println!(
        "  of those functions, ALSO control-flow havoc'd : {}",
        rel_funcs.intersection(&havoc).count()
    );
    println!(
        "  of those functions, ALSO unsupported-op scrub : {}",
        rel_funcs.intersection(&scrub).count()
    );
    println!(
        "  fully-clean functions that emit relational    : {}",
        rel_funcs.intersection(&clean).count()
    );
    println!();
    // How wide are the relations? Octagon is 2-variable by construction; the
    // question for polyhedra is how many DISTINCT locals participate per point.
    let mut width_hist: BTreeMap<usize, usize> = BTreeMap::new();
    for p in &rel_pts {
        let vars: BTreeSet<u32> = p.relational.iter().flat_map(|c| [c.a, c.b]).collect();
        *width_hist.entry(vars.len()).or_default() += 1;
    }
    println!("--- distinct locals participating in relations, per point ---");
    for (w, n) in &width_hist {
        println!("  {w:>3} locals : {n:>6} points");
    }
    println!();
    // SHARPENED: the octagon is exact for 2-variable constraints, so a point
    // can only benefit from polyhedra if >=3 locals are mutually constrained.
    // Of THOSE points, how many sit in a function that is not already degraded?
    let mut wide_clean = 0usize;
    let mut wide_degraded = 0usize;
    let mut wide_funcs: BTreeSet<u32> = BTreeSet::new();
    for p in &rel_pts {
        let vars: BTreeSet<u32> = p.relational.iter().flat_map(|c| [c.a, c.b]).collect();
        if vars.len() >= 3 {
            wide_funcs.insert(p.func_index);
            if clean.contains(&p.func_index) {
                wide_clean += 1
            } else {
                wide_degraded += 1
            }
        }
    }
    println!("--- SHARPENED: points where polyhedra COULD exceed the octagon ---");
    println!(
        "  points with >=3 mutually-constrained locals : {}  ({:.2}% of all points)",
        wide_clean + wide_degraded,
        100.0 * (wide_clean + wide_degraded) as f64 / total_pts.max(1) as f64
    );
    println!("    in a FULLY-CLEAN function                : {wide_clean}");
    println!("    in an already-DEGRADED function          : {wide_degraded}");
    println!(
        "  distinct functions involved                : {}",
        wide_funcs.len()
    );
    println!();

    // Constraint form split. Diff-only would mean the octagon is operating as a
    // difference-bound matrix and its Sum power is unused.
    let mut diff = 0usize;
    let mut sum = 0usize;
    for p in pts {
        for c in &p.relational {
            match c.kind {
                scry_analyze_core::RelKind::Diff => diff += 1,
                scry_analyze_core::RelKind::Sum => sum += 1,
            }
        }
    }
    // "In a degraded function" is NOT "degraded at this point": gaps are
    // per-pc and write-set havoc widens only the locals a region writes, so a
    // wide point can sit nowhere near a gap. Measure the sharper thing --
    // whether ANY gap in the same function occurs at a pc at or before this
    // point, i.e. whether this point's state could have been touched by one.
    let mut first_gap: BTreeMap<u32, u32> = BTreeMap::new();
    for g in &r.gaps {
        first_gap
            .entry(g.func_index)
            .and_modify(|e| *e = (*e).min(g.pc))
            .or_insert(g.pc);
    }
    let (mut upstream_clean, mut downstream_of_gap) = (0usize, 0usize);
    for p in &rel_pts {
        let vars: BTreeSet<u32> = p.relational.iter().flat_map(|c| [c.a, c.b]).collect();
        if vars.len() < 3 {
            continue;
        }
        match first_gap.get(&p.func_index) {
            Some(&gpc) if gpc <= p.pc => downstream_of_gap += 1,
            _ => upstream_clean += 1,
        }
    }
    // ── FEAT-057 slice 2a REALIZATION: what does the wired poly deliver? ──
    // The sections above measured the CEILING before slice 2a was built.
    // This one measures what the wired domain actually carries: points whose
    // `linear` output is non-empty (constraints over >=2 locals — unary poly
    // bounds are filtered as interval-duplicates), and the >=3-variable
    // subset only polyhedra can express at all. Compare against the 2,512
    // wide-point ceiling: the DELTA, not "tests pass", is whether the slice
    // did anything.
    let lin_pts: Vec<_> = pts.iter().filter(|p| !p.linear.is_empty()).collect();
    let total_lin: usize = pts.iter().map(|p| p.linear.len()).sum();
    let lin_funcs: BTreeSet<u32> = lin_pts.iter().map(|p| p.func_index).collect();
    let wide_lin: Vec<_> = lin_pts
        .iter()
        .filter(|p| p.linear.iter().any(|c| c.terms.len() >= 3))
        .collect();
    let wide_set: BTreeSet<(u32, u32)> = rel_pts
        .iter()
        .filter(|p| {
            let vars: BTreeSet<u32> = p.relational.iter().flat_map(|c| [c.a, c.b]).collect();
            vars.len() >= 3
        })
        .map(|p| (p.func_index, p.pc))
        .collect();
    let lin_on_wide = lin_pts
        .iter()
        .filter(|p| wide_set.contains(&(p.func_index, p.pc)))
        .count();
    println!("--- FEAT-057 slice 2a REALIZED: points carrying `linear` facts ---");
    println!(
        "  points with >=1 linear constraint (>=2 locals) : {} / {total_pts}  ({:.2}%)",
        lin_pts.len(),
        100.0 * lin_pts.len() as f64 / total_pts.max(1) as f64
    );
    println!("  total linear constraints                       : {total_lin}");
    println!(
        "  points with a >=3-local linear constraint      : {}",
        wide_lin.len()
    );
    println!(
        "  functions with >=1 linear point                : {}",
        lin_funcs.len()
    );
    println!(
        "  linear points among the >=3-mutually-constrained ceiling set : {lin_on_wide} / {}",
        wide_set.len()
    );
    println!();
    println!("--- SHARPER: is the wide point actually downstream of a gap? ---");
    println!("  wide points with NO gap at or before them : {upstream_clean}");
    println!("  wide points downstream of a gap in-func   : {downstream_of_gap}");
    println!("  CAUTION -- these are bounds in the directions you might not expect.");
    println!("  `no gap at or before` is an UPPER bound on unaffected points, NOT a");
    println!("  lower bound: program order is not dataflow order. A gap at pc 500");
    println!("  inside a LOOP does reach a point at pc 100, because the fixpoint");
    println!("  joins the back edge. So the true reachable set is <= the first");
    println!("  number and >= (total - second). Straight-line code is exact.");
    println!();
    // THE LOOP CAVEAT IS REAL AND UNQUANTIFIED HERE, deliberately.
    //
    // A first attempt sized it by counting functions where the fixpoint
    // revisited a pc -- and the vacuity check built into it reported
    // `(func,pc) pairs seen more than once: 0`. ProgramPoint is one per pc
    // (the FINAL fixpoint state), so the proxy could only ever return zero.
    // Printing "0 functions with loops" would have been a measurement that
    // discriminates nothing, reported as a fact -- this repo's dominant
    // documented failure class. It was removed rather than reported.
    //
    // Sizing it properly needs the operator stream (back edges), which this
    // harness does not have. So: `no gap at or before` is an UPPER bound, the
    // loop-induced shortfall is UNKNOWN, and 13 is the only number here that
    // is provably lost.

    println!("--- constraint form ---");
    println!("  Diff (x_a - x_b <= c) : {diff}");
    println!("  Sum  (x_a + x_b <= c) : {sum}");
    println!();
    println!("CAVEAT, stated because the number invites overreach: >=3 mutually");
    println!("constrained locals is OPPORTUNITY, not realized gain. Polyhedra beats");
    println!("the octagon only where the true invariant is a general linear");
    println!("inequality the pairwise closure cannot express. This bounds the");
    println!("ceiling from ABOVE; it does not show any point would actually improve.");
    println!("(A point where the octagon is TOP is TOP for polyhedra too: both ride");
    println!(" the same fixpoint and the same region havoc.)");
}
