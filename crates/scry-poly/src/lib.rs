#![no_std]
#![forbid(unsafe_code)]
//! # scry-sai-poly — convex-polyhedra abstract domain (Fourier–Motzkin)
//!
//! FEAT-057 (AC-012; Cousot & Halbwachs, *Automatic discovery of linear
//! restraints among variables of a program*, POPL 1978; DD-019). Convex
//! polyhedra express **arbitrary-coefficient** linear inequalities
//! `Σ aⱼ·xⱼ ≤ b` over the program variables — strictly above the octagon
//! (which is limited to `±xᵢ ± xⱼ ≤ c`). This crate is the pure, Wasm-agnostic
//! core (REQ-016 relational surfacing).
//!
//! ## Representation
//!
//! A [`Poly`] over `dim` variables is a conjunction of [`Constraint`]s (each
//! `Σ coeffs[j]·xⱼ ≤ bound`, integer coefficients), plus an `empty` flag for ⊥.
//!
//! ## Concretization
//!
//! ```text
//!   γ(P) = { x ∈ ℤ^dim | ∀ c ∈ P.  Σ c.coeffs[j]·xⱼ ≤ c.bound }   (∅ if empty)
//! ```
//!
//! ## Operations & soundness
//!
//! - **meet** = union of the constraint sets — EXACT (`γ(a⊓b) = γ(a) ∩ γ(b)`).
//! - **entailment** `P ⊨ (a·x ≤ b)` is decided by [`fm_feasible`]: it holds iff
//!   `P ∧ (a·x ≥ b+1)` is **infeasible** over ℚ (the `+1` integer trick avoids
//!   strict inequalities — sound for integer variables: a ℚ-infeasible negation
//!   means no integer point violates the constraint). Fourier–Motzkin
//!   elimination decides ℚ-feasibility; on any coefficient overflow it returns
//!   `true` (feasible) — the SOUND direction, since that only makes entailment
//!   *under*-report (less precise, never unsound).
//! - **join** = the constraints entailed by BOTH operands (drawn from their
//!   combined constraint pool). This is a sound **over-approximation** of the
//!   convex hull — `γ(a) ∪ γ(b) ⊆ γ(a⊔b)` — NOT the exact hull (DD-019: the
//!   exact double-description hull is deferred; this is enough to beat the
//!   octagon on general-coefficient facts).
//! - **leq** `a ⊑ b` iff every constraint of `b` is entailed by `a` ⟹
//!   `γ(a) ⊆ γ(b)` (sound; conservative — may report `false` when unsure, which
//!   only costs fixpoint iterations, never soundness).
//! - **widen** keeps the constraints of `a` that `b` still entails — the
//!   constraint set can only shrink, so ascending chains stabilise.
//! - **project** (FEAT-057 slice 2a) eliminates ONE variable by
//!   Fourier–Motzkin — the "forget on reassignment" transfer. Every bail
//!   (overflow, combination cap) DROPS constraints, which only enlarges the
//!   result: sound for a projection. See [`Poly::project`].
//!
//! The lattice laws (order reflexive/transitive, join an upper bound, meet a
//! lower bound) are mechanized admit-free in `proofs/rocq/Poly.v`; the FM
//! transfer functions above are γ-swept natively (below), NOT mechanized — the
//! honest DD-019 scope (no "mechanized" claim for the hull/entailment).

extern crate alloc;
use alloc::vec::Vec;

/// A single linear constraint `Σ coeffs[j]·xⱼ ≤ bound` (integer coefficients).
/// `coeffs.len()` equals the enclosing [`Poly`]'s `dim`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constraint {
    /// Per-variable integer coefficients.
    pub coeffs: Vec<i64>,
    /// Upper bound.
    pub bound: i64,
}

/// A convex polyhedron: a conjunction of [`Constraint`]s over `dim` variables,
/// or ⊥ (`empty`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Poly {
    dim: u32,
    cons: Vec<Constraint>,
    empty: bool,
}

/// Magnitude guard for the i128 Fourier–Motzkin arithmetic: if any combined
/// coefficient/bound would exceed this, [`fm_feasible`] bails to `true`
/// (feasible) — the sound direction (entailment then under-reports).
const FM_LIMIT: i128 = 1 << 100;

/// Cap on the number of pos×neg row combinations [`Poly::project`] will form.
/// Above it the combinations are SKIPPED entirely (only zero-coefficient rows
/// survive) — the sound direction for a projection (larger result, no false
/// fact), trading precision for a hard cost bound.
const PROJECT_COMBINE_LIMIT: usize = 64;

/// ⊤ over `dim` variables — no constraints; admits every point.
pub fn top(dim: u32) -> Poly {
    Poly {
        dim,
        cons: Vec::new(),
        empty: false,
    }
}

/// ⊥ over `dim` variables — the empty polyhedron; admits nothing.
pub fn bottom(dim: u32) -> Poly {
    Poly {
        dim,
        cons: Vec::new(),
        empty: true,
    }
}

impl Poly {
    /// Number of tracked variables.
    pub fn dim(&self) -> u32 {
        self.dim
    }

    /// Is this ⊥?
    pub fn is_bottom(&self) -> bool {
        self.empty
    }

    /// The current constraint set (empty for ⊤ **and** for ⊥ — use
    /// [`is_bottom`](Self::is_bottom) to distinguish).
    pub fn constraints(&self) -> &[Constraint] {
        &self.cons
    }

    /// Does the concrete integer point `x` (length `dim`) lie in `γ(self)`?
    pub fn contains(&self, x: &[i64]) -> bool {
        if self.empty {
            return false;
        }
        self.cons
            .iter()
            .all(|c| dot(&c.coeffs, x) <= c.bound as i128)
    }

    /// Add a constraint in place (⊓ with a single half-space). Detects the
    /// obvious `0 ≤ negative` contradiction and collapses to ⊥.
    pub fn add_constraint(&mut self, c: Constraint) {
        if self.empty {
            return;
        }
        if c.coeffs.iter().all(|&a| a == 0) {
            if c.bound < 0 {
                self.empty = true;
                self.cons.clear();
            }
            return; // 0 ≤ nonneg : redundant
        }
        self.cons.push(c);
    }

    /// Meet (⊓): the conjunction of both constraint sets — EXACT intersection.
    pub fn meet(&self, other: &Poly) -> Poly {
        if self.empty || other.empty {
            return bottom(self.dim);
        }
        let mut cons = self.cons.clone();
        for c in &other.cons {
            cons.push(c.clone());
        }
        Poly {
            dim: self.dim,
            cons,
            empty: false,
        }
    }

    /// Does `self` entail the constraint `c` (i.e. `γ(self) ⊆ γ(c)`)? Decided by
    /// Fourier–Motzkin: `self ∧ ¬c` (over integers, `c.coeffs·x ≥ c.bound+1`)
    /// is infeasible. `⊥` entails everything.
    pub fn entails(&self, c: &Constraint) -> bool {
        if self.empty {
            return true;
        }
        // Negation over ℤ: ¬(a·x ≤ b) ⟺ a·x ≥ b+1 ⟺ (−a)·x ≤ −(b+1).
        let neg = Constraint {
            coeffs: c.coeffs.iter().map(|&a| -a).collect(),
            bound: -(c.bound.saturating_add(1)),
        };
        let mut sys = self.cons.clone();
        sys.push(neg);
        !fm_feasible(self.dim, &sys)
    }

    /// Order: `self ⊑ other` iff every constraint of `other` is entailed by
    /// `self` ⟹ `γ(self) ⊆ γ(other)`. Sound; conservative.
    pub fn leq(&self, other: &Poly) -> bool {
        if self.empty {
            return true;
        }
        if other.empty {
            return false; // non-⊥ ⊑ ⊥ only if self is ⊥
        }
        other.cons.iter().all(|c| self.entails(c))
    }

    /// Join (⊔): a sound over-approximation of the convex hull — the
    /// constraints (from the combined pool of both operands) entailed by BOTH.
    /// `γ(a) ∪ γ(b) ⊆ γ(a⊔b)`.
    pub fn join(&self, other: &Poly) -> Poly {
        if self.empty {
            return other.clone();
        }
        if other.empty {
            return self.clone();
        }
        let mut cons: Vec<Constraint> = Vec::new();
        for c in self.cons.iter().chain(other.cons.iter()) {
            if cons.contains(c) {
                continue;
            }
            if self.entails(c) && other.entails(c) {
                cons.push(c.clone());
            }
        }
        Poly {
            dim: self.dim,
            cons,
            empty: false,
        }
    }

    /// Fourier–Motzkin elimination of ONE variable: a sound over-approximation
    /// of the projection `∃x_k. γ(self)`, expressed in the SAME `dim`-space
    /// with `x_k` left unconstrained. This is the "forget on reassignment"
    /// transfer (FEAT-057 slice 2a): when a local is overwritten, every
    /// constraint mentioning its OLD value must go, but the consequences that
    /// do not mention it (the pos/neg combinations) may soundly stay.
    ///
    /// Soundness spec: if `x[k := v] ∈ γ(self)` for SOME `v`, then
    /// `x[k := w] ∈ γ(project(self, k))` for EVERY `w` (γ-swept below).
    ///
    /// Bail directions — each stated explicitly, mirroring [`fm_feasible`]:
    /// - a combined row whose coefficients/bound OVERFLOW (i128 check, then
    ///   the i64 narrowing, `FM_LIMIT` cap) is DROPPED — dropping a constraint
    ///   only ENLARGES the result, which for a forget/projection is the sound
    ///   direction (precision loss, never a false fact);
    /// - when `pos·neg` exceeds [`PROJECT_COMBINE_LIMIT`] ALL combinations are
    ///   skipped (only the rows with coefficient 0 on `x_k` are kept) — same
    ///   sound direction;
    /// - what would be UNSOUND is keeping any row that still mentions `x_k`,
    ///   or keeping a wrongly-combined row: neither happens — every kept row
    ///   has coefficient 0 on `x_k` by construction, and combination
    ///   arithmetic is exact-or-dropped.
    ///
    /// A combination that degenerates to `0 ≤ negative` proves `self` was
    /// infeasible (γ = ∅), so ⊥ is returned — exact, not an approximation.
    pub fn project(&self, var: u32) -> Poly {
        if self.empty {
            return bottom(self.dim);
        }
        let k = var as usize;
        if var >= self.dim {
            return self.clone();
        }
        let mut keep: Vec<Constraint> = Vec::new();
        let mut pos: Vec<&Constraint> = Vec::new();
        let mut neg: Vec<&Constraint> = Vec::new();
        for c in &self.cons {
            match c.coeffs.get(k).copied().unwrap_or(0) {
                0 => keep.push(c.clone()),
                a if a > 0 => pos.push(c),
                _ => neg.push(c),
            }
        }
        if pos
            .len()
            .checked_mul(neg.len())
            .is_some_and(|n| n <= PROJECT_COMBINE_LIMIT)
        {
            for p in &pos {
                for n in &neg {
                    // Cancel x_k: a·p + b·n with a = −n_k > 0, b = p_k > 0.
                    let a = -(n.coeffs[k] as i128);
                    let b = p.coeffs[k] as i128;
                    let mut nc = alloc::vec![0i128; self.dim as usize];
                    let mut overflow = false;
                    for (j, slot) in nc.iter_mut().enumerate() {
                        match a.checked_mul(p.coeffs[j] as i128).and_then(|ap| {
                            b.checked_mul(n.coeffs[j] as i128)
                                .and_then(|bn| ap.checked_add(bn))
                        }) {
                            Some(v) if v.abs() <= FM_LIMIT => *slot = v,
                            _ => {
                                overflow = true;
                                break;
                            }
                        }
                    }
                    let nb = match a.checked_mul(p.bound as i128).and_then(|ap| {
                        b.checked_mul(n.bound as i128)
                            .and_then(|bn| ap.checked_add(bn))
                    }) {
                        Some(v) if v.abs() <= FM_LIMIT => v,
                        _ => {
                            overflow = true;
                            0
                        }
                    };
                    if overflow {
                        continue; // sound bail: DROP the combination
                    }
                    let (rc, rb) = reduce(nc, nb);
                    if rc.iter().all(|&c| c == 0) {
                        if rb < 0 {
                            return bottom(self.dim); // 0 ≤ negative: infeasible
                        }
                        continue; // 0 ≤ nonneg: trivially true
                    }
                    // Narrow back to i64; a row that does not fit is DROPPED
                    // (sound — see the bail-direction note above).
                    let coeffs: Option<Vec<i64>> =
                        rc.iter().map(|&c| i64::try_from(c).ok()).collect();
                    match (coeffs, i64::try_from(rb).ok()) {
                        (Some(coeffs), Some(bound)) => keep.push(Constraint { coeffs, bound }),
                        _ => continue,
                    }
                }
            }
        }
        Poly {
            dim: self.dim,
            cons: keep,
            empty: false,
        }
    }

    /// Widening: keep the constraints of `self` still entailed by `other`. The
    /// constraint set only shrinks across iterations, so ascending chains
    /// stabilise (standard polyhedra widening). `γ(self) ∪ γ(other) ⊆ result`.
    pub fn widen(&self, other: &Poly) -> Poly {
        if self.empty {
            return other.clone();
        }
        if other.empty {
            return self.clone();
        }
        let cons: Vec<Constraint> = self
            .cons
            .iter()
            .filter(|c| other.entails(c))
            .cloned()
            .collect();
        Poly {
            dim: self.dim,
            cons,
            empty: false,
        }
    }
}

/// Integer dot product in i128 (coefficients are small; the point values in a
/// γ-check are small — no overflow in practice, and i128 gives wide headroom).
fn dot(coeffs: &[i64], x: &[i64]) -> i128 {
    coeffs
        .iter()
        .zip(x.iter())
        .map(|(&a, &v)| a as i128 * v as i128)
        .sum()
}

/// gcd of two non-negative i128.
fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Decide whether the constraint system is FEASIBLE over ℚ by Fourier–Motzkin
/// elimination of every variable. Returns `true` (feasible) on any coefficient
/// overflow — the sound default for the entailment use (see module docs).
pub fn fm_feasible(dim: u32, cons: &[Constraint]) -> bool {
    // Rows: (coeffs over ℚ as i128, bound) meaning Σ coeffs·x ≤ bound.
    let mut rows: Vec<(Vec<i128>, i128)> = cons
        .iter()
        .map(|c| {
            (
                c.coeffs.iter().map(|&a| a as i128).collect(),
                c.bound as i128,
            )
        })
        .collect();

    for k in 0..dim as usize {
        let mut pos: Vec<&(Vec<i128>, i128)> = Vec::new();
        let mut neg: Vec<&(Vec<i128>, i128)> = Vec::new();
        let mut next: Vec<(Vec<i128>, i128)> = Vec::new();
        for r in &rows {
            let ck = r.0.get(k).copied().unwrap_or(0);
            if ck > 0 {
                pos.push(r);
            } else if ck < 0 {
                neg.push(r);
            } else {
                next.push(r.clone());
            }
        }
        for p in &pos {
            for n in &neg {
                // Combine a·p + b·n with a=-n_k>0, b=p_k>0 to cancel x_k.
                let a = -n.0[k];
                let b = p.0[k];
                let mut nc = alloc::vec![0i128; dim as usize];
                let mut overflow = false;
                // Indexes three parallel rows (nc write, p/n read) with a
                // checked-overflow early break — clearer as an index loop.
                #[allow(clippy::needless_range_loop)]
                for j in 0..dim as usize {
                    match a
                        .checked_mul(p.0[j])
                        .and_then(|ap| b.checked_mul(n.0[j]).and_then(|bn| ap.checked_add(bn)))
                    {
                        Some(v) if v.abs() <= FM_LIMIT => nc[j] = v,
                        _ => {
                            overflow = true;
                            break;
                        }
                    }
                }
                let nb = match a
                    .checked_mul(p.1)
                    .and_then(|ap| b.checked_mul(n.1).and_then(|bn| ap.checked_add(bn)))
                {
                    Some(v) if v.abs() <= FM_LIMIT => v,
                    _ => {
                        overflow = true;
                        0
                    }
                };
                if overflow {
                    return true; // sound bail: treat as feasible
                }
                let (rc, rb) = reduce(nc, nb);
                next.push((rc, rb));
            }
        }
        rows = next;
    }

    // All variables eliminated: rows are `0 ≤ bound`. Infeasible iff some bound
    // is negative (a `0 ≤ negative` contradiction).
    !rows.iter().any(|(_, bnd)| *bnd < 0)
}

/// gcd-reduce a constraint (`coeffs`, `bound`) when the gcd of ALL of them
/// divides evenly — shrinks magnitudes without changing the ℚ half-space.
fn reduce(coeffs: Vec<i128>, bound: i128) -> (Vec<i128>, i128) {
    let mut g: i128 = 0;
    for &c in &coeffs {
        g = gcd(g, c);
    }
    g = gcd(g, bound);
    if g > 1 {
        (coeffs.iter().map(|&c| c / g).collect(), bound / g)
    } else {
        (coeffs, bound)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn con(coeffs: &[i64], bound: i64) -> Constraint {
        Constraint {
            coeffs: coeffs.to_vec(),
            bound,
        }
    }

    fn poly(dim: u32, cs: &[Constraint]) -> Poly {
        let mut p = top(dim);
        for c in cs {
            p.add_constraint(c.clone());
        }
        p
    }

    // ── γ-sweep scaffolding (dim=2, values -3..=3) ─────────────────────────
    const D: usize = 2;
    const LO: i64 = -3;
    const HI: i64 = 3;

    fn all_points() -> Vec<[i64; D]> {
        let mut out = Vec::new();
        for a in LO..=HI {
            for b in LO..=HI {
                out.push([a, b]);
            }
        }
        out
    }

    fn samples() -> Vec<Poly> {
        vec![
            top(2),
            bottom(2),
            poly(2, &[con(&[1, 0], 2)]),                    // x ≤ 2
            poly(2, &[con(&[1, 0], 2), con(&[-1, 0], 1)]),  // -1 ≤ x ≤ 2
            poly(2, &[con(&[1, 1], 3)]),                    // x + y ≤ 3   (octagon-expressible)
            poly(2, &[con(&[2, 3], 6)]),                    // 2x + 3y ≤ 6 (NOT octagon-expressible)
            poly(2, &[con(&[1, -1], 0), con(&[-1, 1], 0)]), // x = y
            poly(2, &[con(&[1, 0], 1), con(&[0, 1], 1)]),   // x ≤ 1 ∧ y ≤ 1
        ]
    }

    #[test]
    fn contains_matches_constraints() {
        let p = poly(2, &[con(&[2, 3], 6)]);
        assert!(p.contains(&[0, 0]));
        assert!(p.contains(&[3, 0])); // 6 ≤ 6
        assert!(!p.contains(&[3, 1])); // 9 > 6
        assert!(!bottom(2).contains(&[0, 0]));
        assert!(top(2).contains(&[100, -100]));
    }

    #[test]
    fn meet_is_exact_intersection() {
        let pts = all_points();
        for a in &samples() {
            for b in &samples() {
                let m = a.meet(b);
                for x in &pts {
                    assert_eq!(
                        m.contains(x),
                        a.contains(x) && b.contains(x),
                        "meet must be exact intersection at {x:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn leq_is_gamma_sound_and_reflexive() {
        let pts = all_points();
        for a in &samples() {
            assert!(a.leq(a), "leq reflexive");
            for b in &samples() {
                if a.leq(b) {
                    for x in &pts {
                        assert!(
                            !a.contains(x) || b.contains(x),
                            "leq(a,b) but γ(a) ⊄ γ(b) at {x:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn join_over_approximates_union_and_is_upper_bound() {
        let pts = all_points();
        for a in &samples() {
            for b in &samples() {
                let j = a.join(b);
                for x in &pts {
                    if a.contains(x) || b.contains(x) {
                        assert!(j.contains(x), "γ(a)∪γ(b) ⊄ γ(a⊔b) at {x:?}");
                    }
                }
                assert!(a.leq(&j), "a ⊑ a⊔b");
                assert!(b.leq(&j), "b ⊑ a⊔b");
            }
        }
    }

    #[test]
    fn widen_is_an_upper_bound() {
        let pts = all_points();
        for a in &samples() {
            for b in &samples() {
                let w = a.widen(b);
                // γ(a) ∪ γ(b) ⊆ γ(a▽b)
                for x in &pts {
                    if a.contains(x) || b.contains(x) {
                        assert!(w.contains(x), "widen must cover both operands at {x:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn entailment_is_sound() {
        // If P entails c, then every point of P satisfies c.
        let pts = all_points();
        let cands = [
            con(&[1, 0], 2),
            con(&[2, 3], 6),
            con(&[1, 1], 3),
            con(&[-1, 0], 0),
            con(&[0, 1], 1),
        ];
        for p in &samples() {
            for c in &cands {
                if p.entails(c) {
                    for x in &pts {
                        if p.contains(x) {
                            assert!(
                                dot(&c.coeffs, x) <= c.bound as i128,
                                "entailed {c:?} violated at {x:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn polyhedra_beats_octagon_on_general_coeffs() {
        // The headline: `2x + 3y ≤ 6` is representable + entailed here — a fact
        // the octagon (±x ± y ≤ c) cannot express. Straight-line meet keeps it.
        let p = poly(2, &[con(&[2, 3], 6)]);
        assert!(p.entails(&con(&[2, 3], 6)));
        assert!(p.entails(&con(&[2, 3], 7)), "weaker bound also entailed");
        assert!(!p.entails(&con(&[2, 3], 5)), "tighter bound NOT entailed");
    }

    #[test]
    fn fm_detects_infeasibility() {
        // x ≤ 1 ∧ x ≥ 3  (i.e. -x ≤ -3) is infeasible.
        assert!(!fm_feasible(2, &[con(&[1, 0], 1), con(&[-1, 0], -3)]));
        // x ≤ 3 ∧ x ≥ 1 is feasible.
        assert!(fm_feasible(2, &[con(&[1, 0], 3), con(&[-1, 0], -1)]));
    }

    /// γ-sweep for [`Poly::project`] (FEAT-057 slice 2a): if some value of
    /// x_k puts the point inside γ(P), then EVERY value of x_k puts it inside
    /// γ(project(P, k)). The witness range for `v` is wider than the sample
    /// polyhedra's own bounds so non-trivial slices are exercised. Also the
    /// structural half: no surviving constraint may mention x_k at all —
    /// keeping one would be the unsound direction (a stale fact about a
    /// reassigned variable).
    #[test]
    fn project_is_gamma_sound_and_forgets_the_variable() {
        let pts = all_points();
        for p in &samples() {
            for k in 0..D as u32 {
                let q = p.project(k);
                for c in q.constraints() {
                    assert_eq!(
                        c.coeffs[k as usize], 0,
                        "project({k}) kept a constraint mentioning x_{k}: {c:?}"
                    );
                }
                for x in &pts {
                    for v in -10..=10i64 {
                        let mut y = *x;
                        y[k as usize] = v;
                        if p.contains(&y) {
                            for w in -10..=10i64 {
                                y[k as usize] = w;
                                assert!(
                                    q.contains(&y),
                                    "γ-unsound project: {y:?} outside project({p:?}, {k})"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// `project` keeps the sound CONSEQUENCES that do not mention the
    /// eliminated variable: from `x ≤ 2 ∧ y − x ≤ 0`, eliminating x still
    /// knows `y ≤ 2`. This is the precision half — a blanket "drop everything
    /// mentioning x" would lose it (and would still be sound, which is why
    /// the γ-sweep alone cannot catch a lazy implementation).
    #[test]
    fn project_keeps_transitive_consequences() {
        let p = poly(2, &[con(&[1, 0], 2), con(&[-1, 1], 0)]);
        let q = p.project(0);
        assert!(
            q.entails(&con(&[0, 1], 2)),
            "projecting x from x ≤ 2 ∧ y ≤ x must retain y ≤ 2; got {q:?}"
        );
        assert!(!q.entails(&con(&[0, 1], 1)), "y ≤ 1 must NOT appear");
    }

    /// Projecting a variable from an infeasible-by-combination system detects
    /// the contradiction (`0 ≤ negative`) and returns ⊥ — exact, not sound-by-
    /// enlargement.
    #[test]
    fn project_detects_infeasibility() {
        // x ≤ 1 ∧ x ≥ 3.
        let p = poly(2, &[con(&[1, 0], 1), con(&[-1, 0], -3)]);
        assert!(p.project(0).is_bottom());
        // ⊥ projects to ⊥.
        assert!(bottom(2).project(0).is_bottom());
        // ⊤ projects to ⊤.
        assert!(top(2).project(1).constraints().is_empty());
    }

    #[test]
    fn empty_and_top_edges() {
        assert!(bottom(2).leq(&top(2)));
        assert!(!top(2).leq(&bottom(2)));
        assert!(bottom(2).leq(&bottom(2)));
        // join with ⊥ is identity; meet with ⊥ is ⊥.
        let p = poly(2, &[con(&[1, 0], 2)]);
        assert_eq!(p.join(&bottom(2)), p);
        assert!(p.meet(&bottom(2)).is_bottom());
    }
}
