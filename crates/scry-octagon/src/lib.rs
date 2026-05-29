//! scry-octagon — the pure octagon relational abstract domain for scry
//! (FEAT-010, v0.9; Miné HOSC 2006, AC-011).
//!
//! This crate holds the *algebra* of the octagon domain and nothing
//! else: no Wasm parsing, no WIT bindings, no I/O. It is the relational
//! analogue of [`scry-taint`] / [`scry-provenance`] — a pure,
//! dependency-free crate that compiles to BOTH `wasm32-wasip2` (where
//! `wasm-lattice` delegates its WIT `octagon-*` exports to it, so the
//! *shipped* relational code is exactly this code) AND natively (where
//! `scry-host-tests` falsifies the lattice laws + concretization
//! soundness against it).
//!
//! ## The domain
//!
//! An octagon over `dim` variables `x_0 … x_{dim-1}` is the set of
//! points satisfying constraints of the form `±x_i ± x_j ≤ c`. We use
//! the standard Difference-Bound-Matrix (DBM) encoding (Miné): each
//! variable `x_k` has a *positive* form at index `2k` and a *negative*
//! form at index `2k+1`. Writing `v(2k) = x_k` and `v(2k+1) = -x_k`,
//! the DBM entry `m[i][j]` is an upper bound on `v(j) - v(i)`:
//!
//! ```text
//!   v(j) - v(i) ≤ m[i][j]      for all 0 ≤ i, j < 2·dim
//! ```
//!
//! Every octagonal constraint maps to one (or two) DBM entries; e.g.
//! `x_a - x_b ≤ c` is `v(2a) - v(2b) ≤ c`, i.e. `m[2b][2a] = c`.
//!
//! ## Soundness role (REQ-001, REQ-002)
//!
//! The matrix is stored row-major in a `Vec<i64>` of length `(2·dim)²`,
//! with [`INF`] (= `i64::MAX`) the +∞ sentinel ("no bound"). All
//! arithmetic is saturating and INF-absorbing ([`sadd`]) so a bound can
//! never silently wrap. [`close`] is the standard Floyd–Warshall
//! shortest-path closure: it is **sound** (it never drops a concrete
//! point — it only makes implicit bounds explicit) and detects
//! infeasibility (a negative diagonal ⇒ ⊥). [`join`] is the pointwise
//! max of two *closed* DBMs, which over-approximates the union; [`meet`]
//! is the pointwise min (exact intersection); [`leq`] compares closed
//! DBMs pointwise. These are the operations the analyzer dispatches
//! through the `pulseengine:wasm-lattice/domain` WIT boundary (DD-008).
//!
//! Deferred to a later FEAT-010 slice: Miné's *strong/tight* closure
//! (the extra `m[i][j] ≤ (m[i][ī] + m[j̄][j]) / 2` tightening that buys
//! precision, not soundness), and the analyzer's loop-carried
//! relational fixpoint.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;

/// The +∞ sentinel — "no upper bound on this difference".
pub const INF: i64 = i64::MAX;

/// Saturating, INF-absorbing addition: `INF + x = INF`, otherwise the
/// saturating integer sum. This is the path-relaxation step's combine
/// operator; INF-absorption is what keeps "no bound ∘ anything = no
/// bound" and saturation is what stops a long path from wrapping.
#[inline]
pub fn sadd(a: i64, b: i64) -> i64 {
    if a == INF || b == INF {
        INF
    } else {
        a.saturating_add(b)
    }
}

/// An octagon over `dim` variables, as a `(2·dim) × (2·dim)` DBM stored
/// row-major. `m[i * n + j]` (with `n = 2·dim`) bounds `v(j) - v(i)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Octagon {
    /// Number of tracked variables.
    pub dim: u32,
    /// Row-major `(2·dim)²` DBM. `INF` means "no bound".
    pub m: Vec<i64>,
}

impl Octagon {
    /// Side length of the DBM (`2·dim`).
    #[inline]
    pub fn n(&self) -> usize {
        2 * self.dim as usize
    }

    #[inline]
    fn at(&self, i: usize, j: usize) -> i64 {
        self.m[i * self.n() + j]
    }

    #[inline]
    fn set(&mut self, i: usize, j: usize, v: i64) {
        let n = self.n();
        self.m[i * n + v_guard(j, n)] = v;
    }
}

#[inline]
fn v_guard(j: usize, n: usize) -> usize {
    debug_assert!(j < n);
    j
}

/// The top element for `dim` variables: every off-diagonal bound is
/// `INF` (no constraint), every diagonal bound is `0` (`v(i) - v(i) ≤
/// 0`). `γ(top)` is all of `ℤ^dim`.
pub fn top(dim: u32) -> Octagon {
    let n = 2 * dim as usize;
    let mut m = vec![INF; n * n];
    for i in 0..n {
        m[i * n + i] = 0;
    }
    Octagon { dim, m }
}

/// A canonical bottom element for `dim` variables: an infeasible system
/// (a negative diagonal). `γ(bottom)` is empty. Encoded by setting
/// `m[0][0] = -1` (when `dim ≥ 1`); for `dim == 0` the (empty) octagon
/// is vacuously top, and bottom coincides with it.
pub fn bottom(dim: u32) -> Octagon {
    let mut o = top(dim);
    if o.n() > 0 {
        let n = o.n();
        o.m[0] = -1; // m[0][0] = -1  ⇒  0 = v(0)-v(0) ≤ -1, infeasible
        let _ = n;
    }
    o
}

/// True iff the octagon is infeasible (empty concretization). Detected
/// by a negative diagonal entry after (or before) closure: `v(i) - v(i)
/// = 0 ≤ m[i][i] < 0` is unsatisfiable.
pub fn is_bottom(o: &Octagon) -> bool {
    let n = o.n();
    for i in 0..n {
        if o.at(i, i) < 0 {
            return true;
        }
    }
    false
}

/// Floyd–Warshall shortest-path closure. Makes every implied bound
/// explicit (`m[i][j] := min over paths`). Sound: it never removes a
/// concrete point, it only tightens the matrix to the least DBM with
/// the same concretization (modulo the deferred strong closure). A
/// negative diagonal after closure marks ⊥.
pub fn close(o: &Octagon) -> Octagon {
    let n = o.n();
    let mut r = o.clone();
    for k in 0..n {
        for i in 0..n {
            let ik = r.at(i, k);
            if ik == INF {
                continue;
            }
            for j in 0..n {
                let kj = r.at(k, j);
                if kj == INF {
                    continue;
                }
                let cand = sadd(ik, kj);
                if cand < r.at(i, j) {
                    r.set(i, j, cand);
                }
            }
        }
    }
    r
}

/// `a ⊑ b` — the octagon partial order, i.e. `γ(a) ⊆ γ(b)`. Computed by
/// closing `a` (so all implied bounds are explicit) and checking it is
/// pointwise at least as tight as `b`. A bottom `a` is `⊑` everything.
pub fn leq(a: &Octagon, b: &Octagon) -> bool {
    debug_assert_eq!(a.dim, b.dim);
    let ca = close(a);
    if is_bottom(&ca) {
        return true;
    }
    if is_bottom(b) {
        return false;
    }
    let n = ca.n();
    for i in 0..n {
        for j in 0..n {
            // a ⊑ b  ⇔  every bound of b is implied by a, i.e.
            // closed-a's bound is ≤ b's bound.
            if ca.at(i, j) > b.at(i, j) {
                return false;
            }
        }
    }
    true
}

/// `a ⊔ b` — least upper bound: the pointwise **max** of the two closed
/// DBMs. Over-approximates `γ(a) ∪ γ(b)` (a weaker bound admits more
/// points), which is sound. Operands are closed first so the max is
/// taken over fully-propagated bounds.
pub fn join(a: &Octagon, b: &Octagon) -> Octagon {
    debug_assert_eq!(a.dim, b.dim);
    let ca = close(a);
    let cb = close(b);
    if is_bottom(&ca) {
        return cb;
    }
    if is_bottom(&cb) {
        return ca;
    }
    let n = ca.n();
    let mut m = vec![INF; n * n];
    for idx in 0..n * n {
        m[idx] = ca.m[idx].max(cb.m[idx]);
    }
    Octagon { dim: a.dim, m }
}

/// `a ⊓ b` — greatest lower bound: the pointwise **min** of the two
/// DBMs (exact intersection of the constraint systems). The result may
/// be infeasible (⊥), which a subsequent [`close`] + [`is_bottom`]
/// detects.
pub fn meet(a: &Octagon, b: &Octagon) -> Octagon {
    debug_assert_eq!(a.dim, b.dim);
    let n = a.n();
    let mut m = vec![INF; n * n];
    for idx in 0..n * n {
        m[idx] = a.m[idx].min(b.m[idx]);
    }
    Octagon { dim: a.dim, m }
}

/// Standard DBM widening (Miné): keep every bound that is stable
/// (`b ≤ a`), and discard (→ `INF`) every bound that grew. Guarantees
/// termination of the fixpoint on the non-Noetherian octagon lattice.
/// The left operand is closed first; the right operand is **not**
/// closed (closing the right operand before widening can defeat
/// termination — the classic Miné caveat).
pub fn widen(a: &Octagon, b: &Octagon) -> Octagon {
    debug_assert_eq!(a.dim, b.dim);
    let ca = close(a);
    if is_bottom(&ca) {
        return b.clone();
    }
    let n = ca.n();
    let mut m = vec![INF; n * n];
    for idx in 0..n * n {
        // Keep the bound only if it did not relax; otherwise → INF.
        m[idx] = if b.m[idx] <= ca.m[idx] {
            ca.m[idx]
        } else {
            INF
        };
    }
    Octagon { dim: a.dim, m }
}

/// Add the octagonal bound `v(j) - v(i) ≤ c` (tightening only — the new
/// matrix keeps the stricter of the existing and the new bound). `i`
/// and `j` are DBM indices in `[0, 2·dim)`: variable `x_k` is `2k`
/// (positive form) and `2k+1` (negative form). Out-of-range indices are
/// a no-op (sound: adds no constraint).
pub fn add_bound(o: &Octagon, i: u32, j: u32, c: i64) -> Octagon {
    let n = o.n();
    let mut r = o.clone();
    let (i, j) = (i as usize, j as usize);
    if i < n && j < n {
        let cur = r.at(i, j);
        if c < cur {
            r.set(i, j, c);
        }
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    /// γ(o, vals): does the concrete assignment `vals` (length `dim`)
    /// satisfy every bound of the DBM? This is the test-side
    /// concretization — the spec the algebra is falsified against.
    fn gamma(o: &Octagon, vals: &[i64]) -> bool {
        let dim = o.dim as usize;
        assert_eq!(vals.len(), dim);
        let n = o.n();
        // v(2k) = x_k, v(2k+1) = -x_k.
        let v = |idx: usize| -> i64 {
            let k = idx / 2;
            if idx % 2 == 0 { vals[k] } else { -vals[k] }
        };
        for i in 0..n {
            for j in 0..n {
                let bound = o.at(i, j);
                if bound != INF && v(j) - v(i) > bound {
                    return false;
                }
            }
        }
        true
    }

    fn dbm_index(k: u32, positive: bool) -> u32 {
        2 * k + if positive { 0 } else { 1 }
    }

    #[test]
    fn top_admits_everything() {
        let o = top(2);
        assert!(gamma(&o, &[0, 0]));
        assert!(gamma(&o, &[1_000, -1_000]));
        assert!(gamma(&o, &[i32::MAX as i64, i32::MIN as i64]));
        assert!(!is_bottom(&o));
    }

    #[test]
    fn bottom_admits_nothing() {
        let o = bottom(2);
        assert!(is_bottom(&o));
        assert!(!gamma(&o, &[0, 0]));
        assert!(!gamma(&o, &[5, 7]));
    }

    /// Add `x_0 - x_1 ≤ 3` and `x_1 - x_0 ≤ -3` (i.e. x_0 - x_1 = 3) and
    /// check the concretization is exactly that relational set.
    #[test]
    fn add_bound_encodes_a_difference_constraint() {
        // v(j) - v(i) ≤ c with v(0)=x_0, v(2)=x_1:
        //   x_0 - x_1 ≤ 3   is  v(0) - v(2) ≤ 3  ⇒ m[2][0] = 3
        //   x_1 - x_0 ≤ -3  is  v(2) - v(0) ≤ -3 ⇒ m[0][2] = -3
        let o = top(2);
        let o = add_bound(&o, dbm_index(1, true), dbm_index(0, true), 3);
        let o = add_bound(&o, dbm_index(0, true), dbm_index(1, true), -3);
        assert!(gamma(&o, &[5, 2]), "5 - 2 = 3 holds");
        assert!(gamma(&o, &[3, 0]), "3 - 0 = 3 holds");
        assert!(!gamma(&o, &[5, 1]), "5 - 1 = 4 ≠ 3 must be excluded");
        assert!(!gamma(&o, &[0, 0]), "0 - 0 = 0 ≠ 3 must be excluded");
    }

    /// Closure must PRESERVE the concretization — the soundness-critical
    /// property: closing makes implied bounds explicit but never adds or
    /// drops a concrete point.
    #[test]
    fn close_preserves_concretization() {
        // x_0 - x_1 ≤ 2 and x_1 - x_2 ≤ 3 imply x_0 - x_2 ≤ 5.
        let o = top(3);
        let o = add_bound(&o, dbm_index(1, true), dbm_index(0, true), 2);
        let o = add_bound(&o, dbm_index(2, true), dbm_index(1, true), 3);
        let c = close(&o);
        // The implied bound is now explicit: m[2·2][2·0] ≤ 5.
        let n = c.n();
        assert!(
            c.m[(2 * 2) * n + (2 * 0)] <= 5,
            "closure must derive x_0 - x_2 ≤ 5"
        );
        // Same concretization on a sweep of points.
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
    }

    /// Closure detects infeasibility: x_0 - x_1 ≤ 1 ∧ x_1 - x_0 ≤ -2
    /// implies 0 ≤ -1.
    #[test]
    fn close_detects_infeasibility() {
        let o = top(2);
        let o = add_bound(&o, dbm_index(1, true), dbm_index(0, true), 1);
        let o = add_bound(&o, dbm_index(0, true), dbm_index(1, true), -2);
        assert!(!is_bottom(&o), "raw matrix has no negative diagonal yet");
        let c = close(&o);
        assert!(is_bottom(&c), "closure must expose the contradiction");
    }

    /// Join over-approximates the union — the soundness law for the LUB:
    /// every point of `a` or `b` is a point of `a ⊔ b`.
    #[test]
    fn join_over_approximates_union() {
        // a: x_0 = 1 (1 ≤ x_0 ≤ 1); b: x_0 = 4. join admits both.
        let mk = |val: i64| {
            let o = top(1);
            // x_0 ≤ val:  v(0) - v(1) ... use single-var bounds.
            // x_0 ≤ val is v(0) - v(1) ≤ 2·val  (since v(1) = -x_0):
            //   v(0) - v(1) = x_0 - (-x_0) = 2 x_0 ≤ 2 val
            // x_0 ≥ val is v(1) - v(0) ≤ -2·val.
            let o = add_bound(&o, dbm_index(0, false), dbm_index(0, true), 2 * val);
            add_bound(&o, dbm_index(0, true), dbm_index(0, false), -2 * val)
        };
        let a = mk(1);
        let b = mk(4);
        assert!(gamma(&a, &[1]));
        assert!(gamma(&b, &[4]));
        let j = join(&a, &b);
        assert!(gamma(&j, &[1]), "join must keep a's point");
        assert!(gamma(&j, &[4]), "join must keep b's point");
    }

    /// Meet is the exact intersection: a point is in `a ⊓ b` iff it is in
    /// both `a` and `b`.
    #[test]
    fn meet_is_intersection() {
        let lower = {
            let o = top(1);
            add_bound(&o, dbm_index(0, true), dbm_index(0, false), -2 * 2) // x_0 ≥ 2
        };
        let upper = {
            let o = top(1);
            add_bound(&o, dbm_index(0, false), dbm_index(0, true), 2 * 5) // x_0 ≤ 5
        };
        let m = meet(&lower, &upper);
        for x in -3..=9 {
            let in_both = gamma(&lower, &[x]) && gamma(&upper, &[x]);
            assert_eq!(gamma(&m, &[x]), in_both, "meet ≠ intersection at x={x}");
        }
    }

    /// `leq` is consistent with concretization inclusion on a concrete
    /// pair: a tighter box ⊑ a looser box, but not vice versa.
    #[test]
    fn leq_matches_concretization_inclusion() {
        let tight = {
            let o = top(1);
            let o = add_bound(&o, dbm_index(0, false), dbm_index(0, true), 2 * 5); // ≤5
            add_bound(&o, dbm_index(0, true), dbm_index(0, false), -2 * 2) // ≥2
        };
        let loose = {
            let o = top(1);
            let o = add_bound(&o, dbm_index(0, false), dbm_index(0, true), 2 * 9); // ≤9
            add_bound(&o, dbm_index(0, true), dbm_index(0, false), -2 * 0) // ≥0
        };
        assert!(leq(&tight, &loose), "[2,5] ⊑ [0,9]");
        assert!(!leq(&loose, &tight), "[0,9] ⋢ [2,5]");
        // sanity: every concrete point of tight is in loose.
        for x in -2..=11 {
            if gamma(&tight, &[x]) {
                assert!(gamma(&loose, &[x]));
            }
        }
    }

    /// Join is commutative, idempotent (on closed forms), and `top` is
    /// its absorbing element — the lattice laws over the pointwise-max.
    #[test]
    fn join_lattice_laws() {
        let a = {
            let o = top(2);
            add_bound(&o, dbm_index(1, true), dbm_index(0, true), 3)
        };
        let b = {
            let o = top(2);
            add_bound(&o, dbm_index(0, true), dbm_index(1, true), 7)
        };
        assert_eq!(join(&a, &b), join(&b, &a), "join commutative");
        assert_eq!(join(&a, &a), close(&a), "join idempotent (closed)");
        assert_eq!(join(&a, &top(2)), close(&top(2)), "top absorbs under join");
    }

    /// Meet is commutative and `top` is its identity.
    #[test]
    fn meet_lattice_laws() {
        let a = {
            let o = top(2);
            add_bound(&o, dbm_index(1, true), dbm_index(0, true), 3)
        };
        assert_eq!(meet(&a, &top(2)), a, "top is meet-identity");
        let b = {
            let o = top(2);
            add_bound(&o, dbm_index(0, true), dbm_index(1, true), 7)
        };
        assert_eq!(meet(&a, &b), meet(&b, &a), "meet commutative");
    }

    /// Widening reaches a post-fixpoint: widening a stable system is a
    /// no-op, and widening a growing bound discards it (→ INF), which is
    /// what guarantees termination.
    #[test]
    fn widen_discards_growing_bounds_keeps_stable() {
        let a = {
            let o = top(2);
            add_bound(&o, dbm_index(1, true), dbm_index(0, true), 3)
        };
        // b relaxes the bound to 5 (grew): widen drops it to INF.
        let b = {
            let o = top(2);
            add_bound(&o, dbm_index(1, true), dbm_index(0, true), 5)
        };
        let w = widen(&a, &b);
        let n = w.n();
        let idx = (dbm_index(1, true) as usize) * n + (dbm_index(0, true) as usize);
        assert_eq!(w.m[idx], INF, "a grown bound must be widened away");
        // Widening against itself keeps the bound (stable).
        let w2 = widen(&a, &a);
        assert_eq!(w2.m[idx], 3, "a stable bound survives widening");
    }

    #[test]
    fn sadd_is_inf_absorbing_and_saturating() {
        assert_eq!(sadd(INF, 5), INF);
        assert_eq!(sadd(5, INF), INF);
        assert_eq!(sadd(2, 3), 5);
        assert_eq!(sadd(i64::MAX - 1, 10), INF); // saturates to i64::MAX = INF
        assert_eq!(sadd(i64::MIN, -10), i64::MIN);
    }
}
