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
    for (slot, (&av, &bv)) in m.iter_mut().zip(ca.m.iter().zip(cb.m.iter())) {
        *slot = av.max(bv);
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
    for (slot, (&av, &bv)) in m.iter_mut().zip(a.m.iter().zip(b.m.iter())) {
        *slot = av.min(bv);
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
    // Keep the bound only if it did not relax; otherwise → INF.
    for (slot, (&cav, &bv)) in m.iter_mut().zip(ca.m.iter().zip(b.m.iter())) {
        *slot = if bv <= cav { cav } else { INF };
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

// ─────────────────────────────────────────────────────────────────────
// Analyzer-facing primitives (FEAT-016 slice-2b-ii).
//
// `add_bound` above is the low-level single-cell tightening. The octagon
// the analyzer carries needs a handful of higher-level, COHERENT operations:
// the transfer functions for the Wasm ops that move/relate locals
// (`local.set` of a const / copy / `x := y + c`), the per-variable
// projection back to an integer interval, a `forget` (havoc on write), and
// `narrow`. These live here (pure algebra) so the analyzer integration in a
// later slice is just dispatch; they are falsified by the γ-sweep tests
// below, exactly like the lattice ops.
//
// ## Coherence
//
// A well-formed octagon DBM is *coherent*: `m[i][j] = m[j̄][ī]` where `ī =
// i^1` swaps a variable's positive (`2k`) and negative (`2k+1`) form (since
// `v(i^1) = -v(i)`, the entry `m[j̄][ī]` bounds the same difference
// `v(j)-v(i)`). `add_bound` sets a single cell; the helpers below set both
// the cell and its coherent twin, which is what lets `close` propagate a
// difference bound + a unary bound into a tighter unary bound (the whole
// point of the relational product: `i ≤ n-1 ∧ n ≤ 10 ⟹ i ≤ 9`).

/// Coherent twin of a DBM index: positive form `2k` ↔ negative form `2k+1`.
#[inline]
fn bar(i: u32) -> u32 {
    i ^ 1
}

/// Saturating `2·c` (the unary-bound scale: `x_k ≤ c` is `2·x_k ≤ 2·c`).
#[inline]
fn two(c: i64) -> i64 {
    c.saturating_mul(2)
}

/// Add the COHERENT octagonal difference constraint `x_a - x_b ≤ c` — sets
/// both the primary cell `m[2b][2a]` and its coherent twin
/// `m[(2a)^1][(2b)^1]`, so the bound survives [`close`].
pub fn add_diff(o: &Octagon, a: u32, b: u32, c: i64) -> Octagon {
    let (pa, pb) = (2 * a, 2 * b);
    let o = add_bound(o, pb, pa, c); // v(2a) - v(2b) ≤ c
    add_bound(&o, bar(pa), bar(pb), c) // twin: v((2b)^1) - v((2a)^1) ≤ c
}

/// Add the coherent unary upper bound `x_k ≤ c`. Encoded `v(2k) - v(2k+1) =
/// 2·x_k ≤ 2·c`, i.e. `m[2k+1][2k] = 2c` (self-coherent: its twin is itself).
pub fn set_upper(o: &Octagon, k: u32, c: i64) -> Octagon {
    add_bound(o, 2 * k + 1, 2 * k, two(c))
}

/// Add the coherent unary lower bound `x_k ≥ c`. Encoded `v(2k+1) - v(2k) =
/// -2·x_k ≤ -2·c`, i.e. `m[2k][2k+1] = -2c`.
pub fn set_lower(o: &Octagon, k: u32, c: i64) -> Octagon {
    add_bound(o, 2 * k, 2 * k + 1, two(c).saturating_neg())
}

/// Forget variable `x_k` (project it out): drop every constraint mentioning
/// `x_k`, keeping all constraints among the other variables. This is the
/// sound transfer for a write of an UNKNOWN value to local `k` (havoc): for
/// any concrete point of `o` and any new value of `x_k`, the modified point
/// is in `γ(forget(o,k))`. We [`close`] first so constraints between other
/// variables that were only implied *through* `x_k` are preserved as
/// explicit bounds before `x_k`'s rows/cols are cleared to `INF`.
pub fn forget(o: &Octagon, k: u32) -> Octagon {
    let mut r = close(o);
    if is_bottom(&r) {
        return r; // havoc of the empty set is empty
    }
    let n = r.n();
    let (p, q) = (2 * k as usize, 2 * k as usize + 1);
    if p >= n {
        return r; // out of range: no variable to forget (sound no-op)
    }
    for t in 0..n {
        if t != p {
            r.set(p, t, INF);
            r.set(t, p, INF);
        }
        if t != q {
            r.set(q, t, INF);
            r.set(t, q, INF);
        }
    }
    r.set(p, p, 0);
    r.set(q, q, 0);
    r
}

/// Transfer for `local.set k` of a constant: `x_k := c`. Forget the old
/// `x_k`, then pin it to `[c, c]`.
pub fn assign_const(o: &Octagon, k: u32, c: i64) -> Octagon {
    let o = forget(o, k);
    let o = set_lower(&o, k, c);
    set_upper(&o, k, c)
}

/// Transfer for a copy `x_k := x_src`. Forget the old `x_k`, then bind
/// `x_k = x_src` relationally (`x_k - x_src ≤ 0 ∧ x_src - x_k ≤ 0`). A
/// self-copy is the identity.
pub fn assign_copy(o: &Octagon, k: u32, src: u32) -> Octagon {
    if k == src {
        return o.clone();
    }
    let o = forget(o, k);
    let o = add_diff(&o, k, src, 0);
    add_diff(&o, src, k, 0)
}

/// Transfer for `x_k := x_src + c`. For `k ≠ src` this forgets `x_k` then
/// binds `x_k = x_src + c` relationally. For `k == src` (the in-place
/// increment `x_k := x_k + c` — the loop-counter case) the old `x_k` MUST
/// NOT be forgotten; instead every bound touching `x_k` is SHIFTED by the
/// change in `v`: `v(2k) = x_k` rises by `c`, `v(2k+1) = -x_k` falls by `c`.
/// This is exactly what carries a relational bound like `x_k - x_n ≤ -1`
/// across the increment (it becomes `x_k - x_n ≤ 0`).
pub fn assign_add_const(o: &Octagon, k: u32, src: u32, c: i64) -> Octagon {
    if k != src {
        let o = forget(o, k);
        let o = add_diff(&o, k, src, c); // x_k - x_src ≤ c
        return add_diff(&o, src, k, c.saturating_neg()); // x_src - x_k ≤ -c
    }
    // In-place increment: shift bounds along the x_k axes.
    let n = o.n();
    let (p, q) = (2 * k as usize, 2 * k as usize + 1);
    if p >= n {
        return o.clone();
    }
    let mut r = o.clone();
    for i in 0..n {
        for j in 0..n {
            let mut d = o.at(i, j);
            // v(p) := v(p) + c  ⇒  any bound with j==p rises by c, i==p falls by c.
            // v(q) := v(q) - c  ⇒  any bound with j==q falls by c, i==q rises by c.
            if j == p {
                d = sadd(d, c);
            } else if j == q {
                d = sadd(d, c.saturating_neg());
            }
            if i == p {
                d = sadd(d, c.saturating_neg());
            } else if i == q {
                d = sadd(d, c);
            }
            r.set(i, j, d);
        }
    }
    r
}

/// Project the octagon onto variable `x_k` as an integer interval
/// `[lo, hi]`, reading the tightest unary bounds out of the CLOSED matrix
/// (so relational + unary constraints have been propagated into `x_k`'s own
/// bounds). `i64::MIN` / `i64::MAX` denote an unbounded side. Returns `None`
/// iff the octagon is infeasible (⊥ — no concrete point, i.e. unreachable).
/// Sound: the returned interval over-approximates `{ x_k : point ∈ γ(o) }`.
pub fn bound_of(o: &Octagon, k: u32) -> Option<(i64, i64)> {
    let c = close(o);
    if is_bottom(&c) {
        return None;
    }
    let n = c.n();
    let (p, q) = (2 * k as usize, 2 * k as usize + 1);
    if p >= n {
        return Some((i64::MIN, i64::MAX));
    }
    // m[2k+1][2k] bounds v(2k) - v(2k+1) = 2·x_k ≤ U  ⇒ x_k ≤ ⌊U/2⌋.
    let upper = c.at(q, p);
    // m[2k][2k+1] bounds v(2k+1) - v(2k) = -2·x_k ≤ L ⇒ x_k ≥ ⌈-L/2⌉ = -⌊L/2⌋.
    let lower = c.at(p, q);
    let hi = if upper == INF {
        i64::MAX
    } else {
        upper.div_euclid(2)
    };
    let lo = if lower == INF {
        i64::MIN
    } else {
        lower.div_euclid(2).saturating_neg()
    };
    Some((lo, hi))
}

/// Octagon narrowing: recover bounds that [`widen`] over-eagerly discarded.
/// Where the widened `a` has `INF` (a bound widening dropped), take `b`'s
/// (re-applied, tighter) bound; elsewhere keep `a`. Descending and sound:
/// the result is `⊑ a` and still over-approximates the loop fixpoint, the
/// dual of the interval narrowing used at loop headers.
pub fn narrow(a: &Octagon, b: &Octagon) -> Octagon {
    debug_assert_eq!(a.dim, b.dim);
    let n = a.n();
    let mut m = vec![INF; n * n];
    for (slot, (&av, &bv)) in m.iter_mut().zip(a.m.iter().zip(b.m.iter())) {
        *slot = if av == INF { bv } else { av };
    }
    Octagon { dim: a.dim, m }
}

#[cfg(test)]
// These tests spell out DBM cell indices in their pedagogical form
// `(2*i)*n + (2*j)` and octagonal bounds as `±2*c`, mirroring the
// octagon variable encoding `v(2k)=x_k, v(2k+1)=-x_k`. For i=0 / c=0
// that yields `*0` / identity terms, which clippy's identity_op and
// erasing_op flag — but collapsing them to bare `0` would erase the
// index/bound formula the assertions are meant to document. Allow both
// in the test module only.
#[allow(clippy::identity_op, clippy::erasing_op)]
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
            if idx.is_multiple_of(2) {
                vals[k]
            } else {
                -vals[k]
            }
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

    // ── FEAT-016 slice-2b-ii primitives ─────────────────────────────────

    /// `set_upper`/`set_lower` encode an integer box, and `bound_of` reads it
    /// back exactly after closure.
    #[test]
    fn unary_bounds_and_projection_roundtrip() {
        let o = top(2);
        let o = set_lower(&o, 0, 2);
        let o = set_upper(&o, 0, 5);
        let o = set_lower(&o, 1, -3);
        let o = set_upper(&o, 1, 1);
        assert_eq!(bound_of(&o, 0), Some((2, 5)));
        assert_eq!(bound_of(&o, 1), Some((-3, 1)));
        // γ agrees: exactly the box [2,5]×[-3,1].
        for x in -1..=8 {
            for y in -6..=4 {
                let in_box = (2..=5).contains(&x) && (-3..=1).contains(&y);
                assert_eq!(gamma(&o, &[x, y]), in_box, "box mismatch at ({x},{y})");
            }
        }
    }

    /// `add_diff` is coherent: a difference bound plus a unary bound on the
    /// other variable closes into a tighter unary bound — the relational win
    /// `x_0 ≤ x_1 - 1 ∧ x_1 ≤ 10 ⟹ x_0 ≤ 9`. This is the exact mechanism the
    /// loop-counter slice relies on.
    #[test]
    fn coherent_diff_plus_unary_projects_to_tighter_unary() {
        let o = top(2);
        let o = add_diff(&o, 0, 1, -1); // x_0 - x_1 ≤ -1  (x_0 ≤ x_1 - 1)
        let o = set_upper(&o, 1, 10); // x_1 ≤ 10
        let o = set_lower(&o, 1, 0); // x_1 ≥ 0
        let o = set_lower(&o, 0, 0); // x_0 ≥ 0
        // Projection must derive x_0 ≤ 9 from the relation + x_1 ≤ 10.
        assert_eq!(bound_of(&o, 0), Some((0, 9)), "x_0 ≤ x_1 - 1 ≤ 9");
        // γ sanity: (9,10) is in, (10,10) violates x_0 ≤ x_1 - 1.
        assert!(gamma(&o, &[9, 10]));
        assert!(!gamma(&o, &[10, 10]));
    }

    /// `forget` is the havoc transfer: for every concrete point of `o` and
    /// every new value of the forgotten variable, the modified point is
    /// admitted (sound over-approximation), while constraints among the other
    /// variables are preserved.
    #[test]
    fn forget_havocs_one_var_preserves_the_rest() {
        // x_0 = x_1 (equality) and x_1 ∈ [2,5].
        let o = top(2);
        let o = add_diff(&o, 0, 1, 0);
        let o = add_diff(&o, 1, 0, 0);
        let o = set_lower(&o, 1, 2);
        let o = set_upper(&o, 1, 5);
        let f = forget(&o, 0);
        // x_1's bound survives; x_0 is now unconstrained.
        assert_eq!(bound_of(&f, 1), Some((2, 5)), "other var preserved");
        assert_eq!(bound_of(&f, 0), Some((i64::MIN, i64::MAX)), "x_0 forgotten");
        // Soundness: every (anything, y) with y ∈ [2,5] is admitted.
        for x0 in [-100, 0, 3, 999] {
            for y in 2..=5 {
                assert!(gamma(&f, &[x0, y]), "forget must admit ({x0},{y})");
            }
        }
        // And it still admits all of o's original points.
        for x in 2..=5 {
            assert!(gamma(&o, &[x, x]) && gamma(&f, &[x, x]));
        }
    }

    /// `assign_const` pins a variable and discards its old relations.
    #[test]
    fn assign_const_pins_and_forgets() {
        let o = top(2);
        let o = add_diff(&o, 0, 1, 0); // x_0 = x_1 ...
        let o = add_diff(&o, 1, 0, 0);
        let o = assign_const(&o, 0, 7); // ... then x_0 := 7
        assert_eq!(bound_of(&o, 0), Some((7, 7)));
        // The old x_0 = x_1 relation is gone: x_1 is free.
        assert_eq!(bound_of(&o, 1), Some((i64::MIN, i64::MAX)));
        assert!(gamma(&o, &[7, 42]));
        assert!(!gamma(&o, &[8, 42]));
    }

    /// `assign_copy` binds `x_k = x_src`.
    #[test]
    fn assign_copy_binds_equality() {
        let o = top(2);
        let o = set_lower(&o, 1, 3);
        let o = set_upper(&o, 1, 3); // x_1 = 3
        let o = assign_copy(&o, 0, 1); // x_0 := x_1
        assert_eq!(bound_of(&o, 0), Some((3, 3)));
        assert!(gamma(&o, &[3, 3]));
        assert!(!gamma(&o, &[4, 3]));
    }

    /// `assign_add_const` for distinct vars binds `x_k = x_src + c`.
    #[test]
    fn assign_add_const_distinct_binds_offset() {
        let o = top(2);
        let o = set_lower(&o, 1, 10);
        let o = set_upper(&o, 1, 10); // x_1 = 10
        let o = assign_add_const(&o, 0, 1, 5); // x_0 := x_1 + 5
        assert_eq!(bound_of(&o, 0), Some((15, 15)));
        assert!(gamma(&o, &[15, 10]));
        assert!(!gamma(&o, &[14, 10]));
    }

    /// The critical loop-counter case: `x_k := x_k + c` SHIFTS bounds rather
    /// than forgetting, so a relational bound is carried across the
    /// increment. `x_0 - x_1 ≤ -1` (i.e. x_0 < x_1) becomes `x_0 - x_1 ≤ 0`
    /// (x_0 ≤ x_1) after `x_0 := x_0 + 1`, and the unary bound shifts too.
    #[test]
    fn increment_shifts_relations_not_forgets() {
        let o = top(2);
        let o = add_diff(&o, 0, 1, -1); // x_0 ≤ x_1 - 1
        let o = set_lower(&o, 0, 0); // x_0 ≥ 0
        let o = set_upper(&o, 0, 4); // x_0 ≤ 4
        let inc = assign_add_const(&o, 0, 0, 1); // x_0 := x_0 + 1
        // Unary bound shifted [0,4] → [1,5].
        assert_eq!(bound_of(&inc, 0), Some((1, 5)));
        // Relation shifted x_0 ≤ x_1 - 1 → x_0 ≤ x_1: (5,5) now allowed.
        assert!(gamma(&inc, &[5, 5]), "x_0 ≤ x_1 after increment");
        assert!(!gamma(&inc, &[6, 5]), "x_0 ≤ x_1 still excludes x_0 > x_1");
        // Soundness vs concrete: any point (x+1, y) where (x,y) ∈ γ(o).
        for x in 0..=4 {
            for y in (x + 1)..=10 {
                if gamma(&o, &[x, y]) {
                    assert!(gamma(&inc, &[x + 1, y]), "shift must admit ({},{y})", x + 1);
                }
            }
        }
    }

    /// `bound_of` reports `None` exactly on the infeasible octagon.
    #[test]
    fn bound_of_detects_bottom() {
        let o = top(1);
        let o = set_lower(&o, 0, 5);
        let o = set_upper(&o, 0, 2); // 5 ≤ x_0 ≤ 2 : infeasible
        assert_eq!(bound_of(&o, 0), None);
    }

    /// `narrow` recovers an `INF` bound (that widening discarded) from the
    /// re-applied candidate, while keeping already-finite bounds.
    #[test]
    fn narrow_recovers_widened_bound() {
        // a: x_0 ≥ 0 only (upper widened to INF). b: re-applied [0,5].
        let a = set_lower(&top(1), 0, 0);
        let b = {
            let o = set_lower(&top(1), 0, 0);
            set_upper(&o, 0, 5)
        };
        let nb = narrow(&a, &b);
        assert_eq!(bound_of(&nb, 0), Some((0, 5)), "narrow recovers the upper");
        // narrow ⊑ a (descended) and still admits b's points.
        assert!(leq(&nb, &a));
        for x in 0..=5 {
            assert!(gamma(&nb, &[x]));
        }
        assert!(!gamma(&nb, &[6]), "recovered upper bound excludes 6");
    }
}
