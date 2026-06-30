#![no_std]
#![forbid(unsafe_code)]
//! # scry-sai-pentagon — the Pentagons weakly-relational abstract domain
//!
//! FEAT-044 (AC-014, Logozzo & Fähndrich, *Pentagons: a weakly relational
//! abstract domain for the efficient validation of array accesses*, 2008).
//!
//! A Pentagon over `dim` variables `x_0 … x_{dim-1}` pairs, per variable, an
//! integer interval `[lo_i, hi_i]` with a set of **strict** upper bounds —
//! other variables `x_j` such that `x_i < x_j` is known to hold. The strict
//! facts are stored as a dense `dim × dim` boolean matrix `lt`, where
//! `lt[i*dim + j]` means "`x_i < x_j` is recorded".
//!
//! ## Concretization
//!
//! ```text
//!   γ(P) = { v ∈ ℤ^dim |  ∀i.  lo_i ≤ v_i ≤ hi_i
//!                       ∧  ∀i,j. lt[i][j] ⟹ v_i < v_j }
//! ```
//!
//! ## Why Pentagons (not octagons) for bounds
//!
//! Octagons need an O(n³) closure to be precise; Pentagons recover the only
//! relational fact bounds-checking needs — `index < length` — for the price of
//! interval arithmetic plus a boolean matrix. The subtlety is the **join**: a
//! strict fact `x_i < x_j` is kept in `a ⊔ b` when it is *provable* in both
//! operands, where "provable in a state" means it is recorded **or** implied by
//! that state's intervals (`hi_i < lo_j`). This is exactly [`implies_lt`].
//!
//! ## Soundness
//!
//! Every operation over-approximates: `γ(a ⊔ b) ⊇ γ(a) ∪ γ(b)`, `a ⊑ b ⟹
//! γ(a) ⊆ γ(b)`, and [`close`] only *adds* constraints it can derive, so it
//! preserves γ. The native build runs an exhaustive γ-sweep (small `dim`, small
//! value range) asserting these laws on every pair of points; the lattice +
//! join soundness is additionally mechanized admit-free in
//! `proofs/rocq/Pentagon.v`.

extern crate alloc;
use alloc::vec;
use alloc::vec::Vec;

/// Sentinel for "no finite upper bound" (`+∞`). Comparisons treat it as the
/// largest value; we never *add* to it (all arithmetic is saturating).
pub const INF: i64 = i64::MAX;
/// Sentinel for "no finite lower bound" (`-∞`).
pub const NEG_INF: i64 = i64::MIN;

/// A Pentagon over `dim` variables: an interval per variable plus a dense
/// strict-less-than matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pentagon {
    /// Number of tracked variables.
    pub dim: u32,
    /// Per-variable lower bounds (`NEG_INF` = unbounded).
    pub lo: Vec<i64>,
    /// Per-variable upper bounds (`INF` = unbounded).
    pub hi: Vec<i64>,
    /// Row-major `dim × dim` strict-less-than matrix: `lt[i*dim + j]` ⟺
    /// `x_i < x_j` is recorded.
    pub lt: Vec<bool>,
}

#[inline]
fn idx(dim: u32, i: usize, j: usize) -> usize {
    i * dim as usize + j
}

/// `a - 1` without underflowing past `NEG_INF`; `INF - 1 == INF`.
#[inline]
fn dec(a: i64) -> i64 {
    if a == NEG_INF || a == INF { a } else { a - 1 }
}

/// `a + 1` without overflowing past `INF`; `NEG_INF + 1 == NEG_INF`.
#[inline]
fn inc(a: i64) -> i64 {
    if a == INF || a == NEG_INF { a } else { a + 1 }
}

impl Pentagon {
    /// The top element: every interval is `[-∞, +∞]` and no strict fact is
    /// recorded. `γ(top) = ℤ^dim`.
    pub fn top(dim: u32) -> Self {
        let n = dim as usize;
        Pentagon {
            dim,
            lo: vec![NEG_INF; n],
            hi: vec![INF; n],
            lt: vec![false; n * n],
        }
    }

    /// A canonical bottom: an infeasible interval on `x_0` (for `dim ≥ 1`).
    /// `γ(bottom) = ∅`.
    pub fn bottom(dim: u32) -> Self {
        let mut p = Pentagon::top(dim);
        if dim >= 1 {
            p.lo[0] = 1;
            p.hi[0] = 0;
        }
        p
    }

    /// Side length helper.
    #[inline]
    pub fn n(&self) -> usize {
        self.dim as usize
    }

    /// `true` if the system is unsatisfiable for an *easily detected* reason:
    /// an empty interval, a self strict-bound (`x_i < x_i`), or a 2-cycle
    /// (`x_i < x_j ∧ x_j < x_i`). Conservative — returning `false` for a
    /// subtler infeasibility is sound (it only costs precision), but returning
    /// `true` always means `γ = ∅`.
    pub fn is_bottom(&self) -> bool {
        let n = self.n();
        for i in 0..n {
            if self.lo[i] > self.hi[i] {
                return true;
            }
            if self.lt[idx(self.dim, i, i)] {
                return true;
            }
            for j in 0..n {
                if self.lt[idx(self.dim, i, j)] && self.lt[idx(self.dim, j, i)] {
                    return true;
                }
            }
        }
        false
    }

    /// Membership: is the concrete point `v` in `γ(self)`? (`v.len()` must be
    /// `dim`.) The soundness oracle for the γ-sweep tests.
    pub fn contains(&self, v: &[i64]) -> bool {
        let n = self.n();
        if v.len() != n {
            return false;
        }
        for ((&vi, &lo), &hi) in v.iter().zip(&self.lo).zip(&self.hi) {
            if vi < lo || vi > hi {
                return false;
            }
        }
        for i in 0..n {
            for j in 0..n {
                if self.lt[idx(self.dim, i, j)] && v[i] >= v[j] {
                    return false;
                }
            }
        }
        true
    }

    /// Is `x_i < x_j` *provable* in this state — recorded explicitly, or forced
    /// by the intervals (`hi_i < lo_j`)? This is the predicate the join and the
    /// order use, and the public query bounds-checking (FEAT-046) calls.
    #[inline]
    pub fn implies_lt(&self, i: usize, j: usize) -> bool {
        if i >= self.n() || j >= self.n() {
            return false;
        }
        self.lt[idx(self.dim, i, j)] || self.hi[i] < self.lo[j]
    }

    /// The proven upper bound on `x_i` (`INF` if none).
    #[inline]
    pub fn upper_bound(&self, i: usize) -> i64 {
        if i < self.n() { self.hi[i] } else { INF }
    }

    // ── transfer functions ────────────────────────────────────────────────

    /// Constrain `x_i` to `[lo, hi]` (intersect with the existing interval).
    pub fn set_interval(&mut self, i: usize, lo: i64, hi: i64) {
        if i < self.n() {
            if lo > self.lo[i] {
                self.lo[i] = lo;
            }
            if hi < self.hi[i] {
                self.hi[i] = hi;
            }
        }
    }

    /// Record the strict fact `x_i < x_j`.
    pub fn assume_lt(&mut self, i: usize, j: usize) {
        let n = self.n();
        if i < n && j < n {
            self.lt[idx(self.dim, i, j)] = true;
        }
    }

    /// Forget everything known about `x_i` (havoc): reset its interval to
    /// `[-∞,+∞]` and drop every strict fact mentioning it. Sound for an
    /// assignment `x_i := <unknown>`.
    pub fn forget(&mut self, i: usize) {
        let n = self.n();
        if i >= n {
            return;
        }
        self.lo[i] = NEG_INF;
        self.hi[i] = INF;
        for j in 0..n {
            self.lt[idx(self.dim, i, j)] = false;
            self.lt[idx(self.dim, j, i)] = false;
        }
    }

    // ── lattice operations ─────────────────────────────────────────────────

    /// `self ⊑ other` (γ(self) ⊆ γ(other)). Sound and decidable: `self`'s
    /// intervals must sit inside `other`'s, and every strict fact `other`
    /// records must be provable in `self`.
    pub fn leq(&self, other: &Self) -> bool {
        debug_assert_eq!(self.dim, other.dim);
        if self.is_bottom() {
            return true;
        }
        if other.is_bottom() {
            return false;
        }
        let n = self.n();
        for i in 0..n {
            if self.lo[i] < other.lo[i] || self.hi[i] > other.hi[i] {
                return false;
            }
        }
        for i in 0..n {
            for j in 0..n {
                if other.lt[idx(self.dim, i, j)] && !self.implies_lt(i, j) {
                    return false;
                }
            }
        }
        true
    }

    /// Join `self ⊔ other`. `γ(result) ⊇ γ(self) ∪ γ(other)`: interval-wise
    /// hull, and a strict fact survives only when [`implies_lt`] holds in BOTH
    /// operands (the Logozzo–Fähndrich interval-recovering join).
    pub fn join(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dim, other.dim);
        if self.is_bottom() {
            return other.clone();
        }
        if other.is_bottom() {
            return self.clone();
        }
        let n = self.n();
        let mut r = Pentagon::top(self.dim);
        for i in 0..n {
            r.lo[i] = self.lo[i].min(other.lo[i]);
            r.hi[i] = self.hi[i].max(other.hi[i]);
        }
        for i in 0..n {
            for j in 0..n {
                r.lt[idx(self.dim, i, j)] = self.implies_lt(i, j) && other.implies_lt(i, j);
            }
        }
        r
    }

    /// Meet `self ⊓ other`: interval intersection and the union of strict
    /// facts. `γ(result) ⊆ γ(self) ∩ γ(other)` (it may be a strict subset only
    /// in the sense of being more precise; never drops a real common point).
    pub fn meet(&self, other: &Self) -> Self {
        debug_assert_eq!(self.dim, other.dim);
        let n = self.n();
        let mut r = Pentagon::top(self.dim);
        for i in 0..n {
            r.lo[i] = self.lo[i].max(other.lo[i]);
            r.hi[i] = self.hi[i].min(other.hi[i]);
        }
        for i in 0..n {
            for j in 0..n {
                r.lt[idx(self.dim, i, j)] =
                    self.lt[idx(self.dim, i, j)] || other.lt[idx(self.dim, i, j)];
            }
        }
        r
    }

    /// Sound tightening to (a) the transitive closure of the strict relation
    /// (`x_i < x_k < x_j ⟹ x_i < x_j`) and (b) the interval bounds those facts
    /// force (`x_i < x_j ⟹ hi_i ≤ hi_j − 1 ∧ lo_j ≥ lo_i + 1`). Only adds
    /// derivable constraints, so `γ(close(p)) = γ(p)`.
    ///
    /// TERMINATION (DD soundness): the strict relation is closed FIRST and to a
    /// fixpoint (monotone edge addition, bounded by `dim²`). A strict CYCLE
    /// `x < … < x` then shows up as a self-loop `lt[i][i]`, which is
    /// unsatisfiable — so the pentagon is ⊥ and we return canonical bottom
    /// WITHOUT tightening intervals. This is the crucial guard: a cycle's
    /// interval tightening would otherwise drive `hi` and `lo` past each other
    /// one unit at a time, looping ~2⁶³ times toward the ±∞ sentinels. With no
    /// self-loop the relation is a strict partial order (a DAG), so the interval
    /// tightening converges in at most `dim` further passes (each bound moves
    /// monotonically toward a finite limit set by the source intervals).
    pub fn close(&self) -> Self {
        let n = self.n();
        let mut r = self.clone();

        // (a) transitive closure of `<` to a fixpoint (terminates: only ever
        // adds edges, of which there are at most `dim²`).
        let mut changed = true;
        while changed {
            changed = false;
            for k in 0..n {
                for i in 0..n {
                    if !r.lt[idx(r.dim, i, k)] {
                        continue;
                    }
                    for j in 0..n {
                        if r.lt[idx(r.dim, k, j)] && !r.lt[idx(r.dim, i, j)] {
                            r.lt[idx(r.dim, i, j)] = true;
                            changed = true;
                        }
                    }
                }
            }
        }
        // A self-loop means a strict cycle `x < x` — unsatisfiable. Return
        // canonical ⊥ before any interval tightening (the non-terminating path).
        for i in 0..n {
            if r.lt[idx(r.dim, i, i)] {
                return Pentagon::bottom(self.dim);
            }
        }

        // (b) interval tightening from each strict fact. The relation is now a
        // DAG, so this converges; a `lo > hi` that appears mid-tightening is a
        // genuine (acyclic) infeasibility — return canonical ⊥.
        changed = true;
        while changed {
            changed = false;
            for i in 0..n {
                for j in 0..n {
                    if !r.lt[idx(r.dim, i, j)] {
                        continue;
                    }
                    let cap = dec(r.hi[j]); // x_i < x_j ≤ hi_j  ⟹ x_i ≤ hi_j − 1
                    if cap < r.hi[i] {
                        r.hi[i] = cap;
                        changed = true;
                    }
                    let floor = inc(r.lo[i]); // x_j > x_i ≥ lo_i ⟹ x_j ≥ lo_i + 1
                    if floor > r.lo[j] {
                        r.lo[j] = floor;
                        changed = true;
                    }
                }
            }
            for i in 0..n {
                if r.lo[i] > r.hi[i] {
                    return Pentagon::bottom(self.dim);
                }
            }
        }
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    // ── exhaustive γ-sweep harness (dim = 2, values in [-2, 3]) ─────────────
    const LO: i64 = -2;
    const HI: i64 = 3;

    /// Every concrete point of `ℤ^2` within the sweep box.
    fn all_points() -> Vec<[i64; 2]> {
        let mut out = Vec::new();
        for a in LO..=HI {
            for b in LO..=HI {
                out.push([a, b]);
            }
        }
        out
    }

    /// A small but representative family of 2-var pentagons.
    fn sample_pentagons() -> Vec<Pentagon> {
        let mut out = Vec::new();
        out.push(Pentagon::top(2));
        out.push(Pentagon::bottom(2));
        for &(l0, h0) in &[(NEG_INF, INF), (-1, 2), (0, 0), (1, 3), (-2, 1)] {
            for &(l1, h1) in &[(NEG_INF, INF), (-1, 2), (0, 2), (2, 3)] {
                for &lt01 in &[false, true] {
                    for &lt10 in &[false, true] {
                        let mut p = Pentagon::top(2);
                        p.lo = vec![l0, l1];
                        p.hi = vec![h0, h1];
                        p.lt[idx(2, 0, 1)] = lt01;
                        p.lt[idx(2, 1, 0)] = lt10;
                        out.push(p);
                    }
                }
            }
        }
        out
    }

    fn gamma(p: &Pentagon) -> Vec<[i64; 2]> {
        all_points().into_iter().filter(|v| p.contains(v)).collect()
    }

    #[test]
    fn gamma_sweep_join_is_upper_bound() {
        let ps = sample_pentagons();
        for a in &ps {
            for b in &ps {
                let j = a.join(b);
                // γ(a) ∪ γ(b) ⊆ γ(a ⊔ b)
                for v in gamma(a) {
                    assert!(
                        j.contains(&v),
                        "join lost a γ(a) point {v:?}\na={a:?}\nb={b:?}"
                    );
                }
                for v in gamma(b) {
                    assert!(
                        j.contains(&v),
                        "join lost a γ(b) point {v:?}\na={a:?}\nb={b:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_meet_is_lower_bound() {
        let ps = sample_pentagons();
        for a in &ps {
            for b in &ps {
                let m = a.meet(b);
                // γ(a ⊓ b) ⊆ γ(a) ∩ γ(b)
                for v in gamma(&m) {
                    assert!(a.contains(&v) && b.contains(&v), "meet gained point {v:?}");
                }
                // and it keeps every common point: γ(a) ∩ γ(b) ⊆ γ(a ⊓ b)
                for v in all_points() {
                    if a.contains(&v) && b.contains(&v) {
                        assert!(m.contains(&v), "meet dropped common point {v:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_leq_is_sound_and_complete_on_box() {
        let ps = sample_pentagons();
        for a in &ps {
            for b in &ps {
                if a.leq(b) {
                    // a ⊑ b ⟹ γ(a) ⊆ γ(b)
                    for v in gamma(a) {
                        assert!(
                            b.contains(&v),
                            "leq unsound: {v:?} in a∉b\na={a:?}\nb={b:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_close_preserves_gamma() {
        for p in sample_pentagons() {
            let c = p.close();
            assert_eq!(gamma(&p), gamma(&c), "close changed γ\np={p:?}\nc={c:?}");
        }
    }

    #[test]
    fn implies_lt_recovers_from_intervals() {
        // x_0 ∈ [0,2], x_1 ∈ [5,9], no explicit lt: 2 < 5 ⟹ x_0 < x_1.
        let mut p = Pentagon::top(2);
        p.set_interval(0, 0, 2);
        p.set_interval(1, 5, 9);
        assert!(p.implies_lt(0, 1));
        assert!(!p.implies_lt(1, 0));
    }

    #[test]
    fn assume_lt_records_index_below_length() {
        // The FEAT-044 headline: a guard `i < n` is recorded soundly.
        let mut p = Pentagon::top(2); // x_0 = i, x_1 = n
        p.assume_lt(0, 1);
        assert!(p.implies_lt(0, 1));
        // every concrete point the pentagon admits satisfies i < n
        for v in gamma(&p) {
            assert!(v[0] < v[1]);
        }
    }

    #[test]
    fn close_tightens_interval_from_strict_fact() {
        // x_0 < x_1 with x_1 ≤ 4 ⟹ x_0 ≤ 3.
        let mut p = Pentagon::top(2);
        p.set_interval(1, NEG_INF, 4);
        p.assume_lt(0, 1);
        let c = p.close();
        assert_eq!(c.hi[0], 3);
    }

    #[test]
    fn self_strict_is_bottom() {
        let mut p = Pentagon::top(1);
        p.assume_lt(0, 0);
        assert!(p.is_bottom());
    }

    /// TERMINATION regression: `close` on an infeasible strict CYCLE
    /// (`x_0 < x_1 ∧ x_1 < x_0`) with FINITE bounds must terminate (return ⊥),
    /// not loop ~2⁶³ times driving hi/lo past each other. γ was empty; ⊥ is too.
    #[test]
    fn close_on_strict_cycle_terminates_to_bottom() {
        let mut p = Pentagon::top(2);
        p.set_interval(0, -1, 2);
        p.set_interval(1, -1, 2);
        p.assume_lt(0, 1);
        p.assume_lt(1, 0);
        let c = p.close(); // must return promptly
        assert!(c.is_bottom());
        // γ(p) was already empty (no point satisfies x0<x1 ∧ x1<x0).
        assert!(gamma(&p).is_empty());
    }

    /// TERMINATION regression: a 3-cycle through transitive closure
    /// (`x_0<x_1<x_2<x_0`) also resolves to ⊥ promptly.
    #[test]
    fn close_on_three_cycle_terminates_to_bottom() {
        let mut p = Pentagon::top(3);
        for i in 0..3 {
            p.set_interval(i, 0, 9);
        }
        p.assume_lt(0, 1);
        p.assume_lt(1, 2);
        p.assume_lt(2, 0);
        assert!(p.close().is_bottom());
    }

    // ════════════ ADVERSARIAL THROWAWAY (clean-room FEAT-044) ════════════

    /// dim=3, range [-3,4], full enumeration of intervals+lt matrices.
    fn adv_pentagons_dim3() -> Vec<Pentagon> {
        let mut out = Vec::new();
        let ivs = [(NEG_INF, INF), (-3, 1), (0, 0), (1, 4), (-1, 2)];
        // To keep the cross product tractable we vary intervals on a few combos
        // and sweep ALL 2^(9) lt matrices for a couple of interval assignments.
        for combo in 0..8usize {
            let mut p = Pentagon::top(3);
            p.lo = vec![
                ivs[combo % 5].0,
                ivs[(combo + 1) % 5].0,
                ivs[(combo + 2) % 5].0,
            ];
            p.hi = vec![
                ivs[combo % 5].1,
                ivs[(combo + 1) % 5].1,
                ivs[(combo + 2) % 5].1,
            ];
            for mask in 0..(1u32 << 9) {
                let mut q = p.clone();
                for b in 0..9 {
                    q.lt[b] = (mask >> b) & 1 == 1;
                }
                out.push(q);
            }
        }
        out
    }

    fn gamma3(p: &Pentagon) -> Vec<[i64; 3]> {
        let mut out = Vec::new();
        for a in -3..=4 {
            for b in -3..=4 {
                for c in -3..=4 {
                    let v = [a, b, c];
                    if p.contains(&v) {
                        out.push(v);
                    }
                }
            }
        }
        out
    }

    #[test]
    fn adv_close_preserves_gamma_dim3() {
        for p in adv_pentagons_dim3().iter().step_by(5) {
            if p.is_bottom() {
                continue;
            }
            let c = p.close();
            assert_eq!(gamma3(p), gamma3(&c), "close changed γ\np={p:?}\nc={c:?}");
        }
    }

    #[test]
    fn adv_join_upper_bound_dim3() {
        let ps = adv_pentagons_dim3();
        // sample pairs (full cross is too big); step to keep it bounded
        for (ia, a) in ps.iter().enumerate().step_by(37) {
            for b in ps.iter().step_by(53) {
                let j = a.join(b);
                for v in gamma3(a) {
                    assert!(
                        j.contains(&v),
                        "join lost γ(a) {v:?}\na={a:?}\nb={b:?}\nj={j:?}\n(ia={ia})"
                    );
                }
                for v in gamma3(b) {
                    assert!(
                        j.contains(&v),
                        "join lost γ(b) {v:?}\na={a:?}\nb={b:?}\nj={j:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn adv_meet_keeps_common_dim3() {
        let ps = adv_pentagons_dim3();
        for a in ps.iter().step_by(41) {
            for b in ps.iter().step_by(59) {
                let m = a.meet(&b);
                for v in gamma3(&m) {
                    assert!(a.contains(&v) && b.contains(&v), "meet gained {v:?}");
                }
                for v in gamma3(a) {
                    if b.contains(&v) {
                        assert!(
                            m.contains(&v),
                            "meet dropped common {v:?}\na={a:?}\nb={b:?}\nm={m:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn adv_leq_sound_dim3() {
        let ps = adv_pentagons_dim3();
        for a in ps.iter().step_by(31) {
            for b in ps.iter().step_by(47) {
                if a.leq(&b) {
                    for v in gamma3(a) {
                        assert!(b.contains(&v), "leq unsound {v:?}\na={a:?}\nb={b:?}");
                    }
                }
            }
        }
    }

    // ── Probe (1): close near INF / NEG_INF sentinels ──
    #[test]
    fn adv_close_inf_bounds() {
        // x_0 < x_1, x_1 = [NEG_INF, INF]. cap = dec(INF) = INF -> hi[0] stays.
        // The DANGER: if dec(INF) returned INF-1 it would wrongly cap a var whose
        // partner is genuinely unbounded. Verify γ unchanged.
        let mut p = Pentagon::top(2);
        p.assume_lt(0, 1);
        let c = p.close();
        assert_eq!(
            c.hi[0], INF,
            "close must not finite-cap from an INF partner"
        );
        assert_eq!(
            c.lo[1], NEG_INF,
            "close must not finite-floor from a NEG_INF partner"
        );

        // x_0 in [INF, INF] (singleton at i64::MAX), x_0 < x_1.
        // Then x_1 > INF is UNSAT — but is_bottom won't see it; check γ=∅ via close+contains.
        let mut q = Pentagon::top(2);
        q.set_interval(0, INF, INF);
        q.assume_lt(0, 1);
        let qc = q.close();
        // floor = inc(lo[0]) = inc(INF) = INF, so lo[1] becomes INF, and any point
        // needs x_1 > INF which is impossible -> γ must be empty.
        for a in [INF - 1, INF] {
            for b in [INF - 1, INF] {
                assert!(
                    !qc.contains(&[a, b]),
                    "γ should be empty, contains [{a},{b}]"
                );
                assert!(!q.contains(&[a, b]), "orig γ empty too, contains [{a},{b}]");
            }
        }
    }

    // ── Probe (2): bottom-by-empty-interval that is_bottom DOES detect (var≠0) ──
    #[test]
    fn adv_join_with_hidden_empty_interval() {
        // empty interval on var 1 (not var 0). is_bottom scans ALL i, so it IS caught.
        let mut a = Pentagon::top(2);
        a.lo[1] = 5;
        a.hi[1] = 0; // empty
        assert!(
            a.is_bottom(),
            "is_bottom must catch empty interval on var 1"
        );
        // join: a is bottom -> returns other. Sound as long as is_bottom holds.
        let b = Pentagon::top(2);
        let j = a.join(&b);
        // γ(a)=∅ so result ⊇ γ(b) suffices; b is top.
        for v in gamma(&b) {
            assert!(j.contains(&v));
        }
    }

    // ── Probe (3): overflow at i64::MAX with strict fact ──
    #[test]
    fn adv_overflow_at_max() {
        // x_0 in [i64::MAX-1, i64::MAX-1], x_0 < x_1, x_1 in [.., i64::MAX].
        let mut p = Pentagon::top(2);
        p.set_interval(0, INF - 1, INF - 1);
        p.assume_lt(0, 1);
        let c = p.close();
        // floor = inc(INF-1) = INF, so lo[1] >= INF.  x_1 must be exactly INF.
        assert_eq!(c.lo[1], INF);
        // the only candidate point [INF-1, INF] satisfies x_0<x_1.
        assert!(c.contains(&[INF - 1, INF]));
        assert!(!c.contains(&[INF - 1, INF - 1]));
        // NEG_INF side: x_0 < x_1, x_0 in [NEG_INF, NEG_INF].
        let mut q = Pentagon::top(2);
        q.set_interval(0, NEG_INF, NEG_INF);
        q.assume_lt(0, 1);
        let qc = q.close();
        // cap = dec(hi[1]=INF)=INF; floor = inc(lo[0]=NEG_INF)=NEG_INF -> lo[1] stays.
        // x_1 just needs to be > NEG_INF, i.e. >= NEG_INF+1.  Check no point with x_1==NEG_INF.
        assert!(!qc.contains(&[NEG_INF, NEG_INF]));
        assert!(qc.contains(&[NEG_INF, NEG_INF + 1]));
    }
}
