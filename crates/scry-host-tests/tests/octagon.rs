//! FEAT-010 (AC-011) host-side falsifier for the octagon relational
//! domain.
//!
//! The DBM algebra ships inside the `wasm-lattice` Wasm component, whose
//! WIT `octagon-*` exports delegate to the pure `scry-octagon` crate.
//! Because the live `analyze()` round-trip is still gated by the
//! wac_compose / wasmtime-45 root-import limitation (see
//! `tests/soundness.rs`), we falsify the *exact shipped relational code*
//! here on the native cargo path by exercising `scry-octagon` directly —
//! the same crate the component compiles in. This is the octagon
//! analogue of `tests/taint.rs` / `tests/provenance.rs`.
//!
//! Kill-criterion (v0.9): the octagon operations are SOUND w.r.t. the
//! concretization γ — closure preserves γ, join over-approximates the
//! union, meet is exactly the intersection, and `add-bound` encodes the
//! intended difference constraint. If any fails, the relational domain
//! could drop a concrete point (unsound) or admit a spurious relation.
//! γ is recomputed here independently of the crate's own test module so
//! this is a genuine second oracle.

use scry_octagon::{
    INF, Octagon, add_bound, bottom, close, is_bottom, join, leq, meet, top, widen,
};

/// Independent concretization: does the assignment `vals` (length `dim`)
/// satisfy every DBM bound? `v(2k) = x_k`, `v(2k+1) = -x_k`, and
/// `m[i*n + j]` bounds `v(j) - v(i)`.
fn gamma(o: &Octagon, vals: &[i64]) -> bool {
    let dim = o.dim as usize;
    assert_eq!(vals.len(), dim);
    let n = 2 * dim;
    let v = |idx: usize| -> i64 {
        let k = idx / 2;
        if idx.is_multiple_of(2) {
            vals[k]
        } else {
            -vals[k]
        }
    };
    for i in 0..n {
        for j in 0..n {
            let bound = o.m[i * n + j];
            if bound != INF && v(j) - v(i) > bound {
                return false;
            }
        }
    }
    true
}

/// DBM index of variable `x_k`: positive form `2k`, negative form `2k+1`.
fn idx(k: u32, positive: bool) -> u32 {
    2 * k + if positive { 0 } else { 1 }
}

/// Build a single-variable octagon `lo ≤ x_0 ≤ hi`.
fn box1(lo: i64, hi: i64) -> Octagon {
    let o = top(1);
    // x_0 ≤ hi  is  v(0) - v(1) ≤ 2·hi   (v(0)=x_0, v(1)=-x_0)
    let o = add_bound(&o, idx(0, false), idx(0, true), 2 * hi);
    // x_0 ≥ lo  is  v(1) - v(0) ≤ -2·lo
    add_bound(&o, idx(0, true), idx(0, false), -2 * lo)
}

#[test]
fn top_admits_everything_bottom_admits_nothing() {
    let t = top(2);
    assert!(!is_bottom(&t));
    assert!(gamma(&t, &[0, 0]));
    assert!(gamma(&t, &[i32::MAX as i64, i32::MIN as i64]));

    let b = bottom(2);
    assert!(is_bottom(&b));
    assert!(!gamma(&b, &[0, 0]));
    assert!(!gamma(&b, &[3, 4]));
}

#[test]
fn add_bound_encodes_a_difference_constraint() {
    // x_0 - x_1 = 3  ≡  x_0 - x_1 ≤ 3  ∧  x_1 - x_0 ≤ -3.
    let o = top(2);
    let o = add_bound(&o, idx(1, true), idx(0, true), 3);
    let o = add_bound(&o, idx(0, true), idx(1, true), -3);
    assert!(gamma(&o, &[5, 2]), "5-2=3 holds");
    assert!(gamma(&o, &[3, 0]), "3-0=3 holds");
    assert!(!gamma(&o, &[5, 1]), "5-1=4 excluded");
    assert!(!gamma(&o, &[0, 0]), "0-0=0 excluded");
}

/// Closure PRESERVES γ — the soundness-critical property. Checked over a
/// dense sweep of concrete points.
#[test]
fn close_preserves_concretization() {
    // x_0 - x_1 ≤ 2 ∧ x_1 - x_2 ≤ 3  ⇒  x_0 - x_2 ≤ 5 (implied).
    let o = top(3);
    let o = add_bound(&o, idx(1, true), idx(0, true), 2);
    let o = add_bound(&o, idx(2, true), idx(1, true), 3);
    let c = close(&o);
    for a in -6..=6 {
        for b in -6..=6 {
            for d in -6..=6 {
                assert_eq!(
                    gamma(&o, &[a, b, d]),
                    gamma(&c, &[a, b, d]),
                    "closure changed γ at ({a},{b},{d})"
                );
            }
        }
    }
    // The implied bound is now explicit.
    let n = 6;
    assert!(c.m[(2 * 2) * n] <= 5, "closure derives x_0 - x_2 ≤ 5");
}

#[test]
fn close_detects_infeasibility() {
    // x_0 - x_1 ≤ 1 ∧ x_1 - x_0 ≤ -2  ⇒  0 ≤ -1 (⊥).
    let o = top(2);
    let o = add_bound(&o, idx(1, true), idx(0, true), 1);
    let o = add_bound(&o, idx(0, true), idx(1, true), -2);
    assert!(!is_bottom(&o), "raw matrix not yet ⊥");
    assert!(is_bottom(&close(&o)), "closure exposes contradiction");
}

/// Join OVER-approximates the union: every point of `a` or `b` is in
/// `a ⊔ b`. Checked over a sweep.
#[test]
fn join_over_approximates_union() {
    let a = box1(1, 1);
    let b = box1(4, 4);
    let j = join(&a, &b);
    for x in -3..=9 {
        if gamma(&a, &[x]) || gamma(&b, &[x]) {
            assert!(gamma(&j, &[x]), "join dropped a point at x={x}");
        }
    }
    assert!(gamma(&j, &[1]) && gamma(&j, &[4]));
}

/// Meet is EXACTLY the intersection.
#[test]
fn meet_is_intersection() {
    let lo = box1(2, 100);
    let hi = box1(-100, 5);
    let m = meet(&lo, &hi);
    for x in -3..=9 {
        assert_eq!(
            gamma(&m, &[x]),
            gamma(&lo, &[x]) && gamma(&hi, &[x]),
            "meet ≠ intersection at x={x}"
        );
    }
}

/// `leq` matches γ-inclusion on a concrete pair, and every concrete
/// point of the tighter octagon lies in the looser one.
#[test]
fn leq_matches_gamma_inclusion() {
    let tight = box1(2, 5);
    let loose = box1(0, 9);
    assert!(leq(&tight, &loose), "[2,5] ⊑ [0,9]");
    assert!(!leq(&loose, &tight), "[0,9] ⋢ [2,5]");
    for x in -2..=11 {
        if gamma(&tight, &[x]) {
            assert!(gamma(&loose, &[x]), "γ(tight) ⊄ γ(loose) at x={x}");
        }
    }
}

/// Widening discards a growing bound (→ ∞) and keeps a stable one — the
/// fixpoint-termination property.
#[test]
fn widen_discards_growing_keeps_stable() {
    let a = {
        let o = top(2);
        add_bound(&o, idx(1, true), idx(0, true), 3)
    };
    let grew = {
        let o = top(2);
        add_bound(&o, idx(1, true), idx(0, true), 5)
    };
    let w = widen(&a, &grew);
    let n = 4;
    let pos = (idx(1, true) as usize) * n + (idx(0, true) as usize);
    assert_eq!(w.m[pos], INF, "a grown bound must widen to ∞");
    let w2 = widen(&a, &a);
    assert_eq!(w2.m[pos], 3, "a stable bound survives widening");
}

/// Join/meet lattice laws: commutativity, and top as join-absorbing /
/// meet-identity.
#[test]
fn lattice_laws() {
    let a = {
        let o = top(2);
        add_bound(&o, idx(1, true), idx(0, true), 3)
    };
    let b = {
        let o = top(2);
        add_bound(&o, idx(0, true), idx(1, true), 7)
    };
    assert_eq!(join(&a, &b), join(&b, &a), "join commutative");
    assert_eq!(meet(&a, &b), meet(&b, &a), "meet commutative");
    assert_eq!(meet(&a, &top(2)), a, "top is meet-identity");
}
