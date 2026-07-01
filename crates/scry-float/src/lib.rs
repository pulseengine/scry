#![no_std]
#![forbid(unsafe_code)]
//! # scry-sai-float — the IEEE-754 float-interval abstract domain
//!
//! FEAT-047 (REQ-015, AC-022). A sound abstraction of an `f32`/`f64` value: a
//! real interval `[lo, hi]` (bounds may be `±∞`) plus a `nan` flag, since NaN is
//! unordered and cannot live inside an interval.
//!
//! ## Concretization
//!
//! ```text
//!   γ(a) = { x : f64 |  (x is NaN  ∧ a.nan)
//!                    ∨  (x not NaN ∧ a.lo ≤ x ≤ a.hi) }
//! ```
//!
//! ## Soundness of the arithmetic transfers (round-to-nearest)
//!
//! IEEE round-to-nearest is MONOTONE, and for `f64` the interval endpoints are
//! themselves `f64` values, so `a.lo + b.lo` computed in `f64` is exactly the
//! IEEE `f64.add` of the endpoints and — by monotonicity — bounds `f64.add` over
//! the whole box. Hence `f64` transfers need NO widening.
//!
//! For `f32`, the IEEE result rounds to the `f32` grid (`RN₃₂`), which differs
//! from the `f64` value we compute (`RN₆₄`) by up to half an `f32` ULP. So every
//! `f32` result bound is snapped OUTWARD onto the `f32` grid and stepped one
//! `f32` ULP further (`round_out`), soundly covering `RN₃₂`.
//!
//! `±∞` bounds propagate through the `f64` corner arithmetic natively; whenever
//! a relevant corner is NaN (e.g. `∞ + (−∞)`, `0 · ∞`) the `nan` flag is set and
//! that corner is dropped from the interval hull.
//!
//! ## Evidence
//!
//! The native build runs an exhaustive γ-sweep over a concrete float grid
//! (incl. `±0`, subnormals, `±∞`, NaN) asserting the lattice laws AND the
//! transfer soundness on every pair of points. The lattice soundness (join
//! over-approximates, order sound) is additionally mechanized admit-free in
//! `proofs/rocq/Float.v`; the rounding-transfer soundness is falsified by the
//! γ-sweep (mechanising IEEE rounding in Rocq — Flocq — is named future work,
//! as the octagon DBM / known-bits transfers were).

/// A sound abstraction of an IEEE-754 float value: a real interval plus a NaN
/// possibility flag.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FloatAbstract {
    /// Lower bound of the non-NaN part (may be `f64::NEG_INFINITY`).
    pub lo: f64,
    /// Upper bound of the non-NaN part (may be `f64::INFINITY`).
    pub hi: f64,
    /// The value may be NaN.
    pub nan: bool,
}

/// The IEEE width an operation rounds to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FWidth {
    /// `f32`.
    W32,
    /// `f64`.
    W64,
}

// ── directed stepping over the float grids (no_std, no unsafe) ──────────────

// f64 needs no `next_up`/`next_down`: round-to-nearest is monotone and the
// interval endpoints are exact f64 values, so the f64-computed bounds are
// already tight+sound (see `round_out`). Only f32 stepping is needed.

fn f32_next_up(x: f32) -> f32 {
    if x.is_nan() || x == f32::INFINITY {
        return x;
    }
    if x == 0.0 {
        return f32::from_bits(1);
    }
    let b = x.to_bits();
    f32::from_bits(if x > 0.0 { b + 1 } else { b - 1 })
}

fn f32_next_down(x: f32) -> f32 {
    if x.is_nan() || x == f32::NEG_INFINITY {
        return x;
    }
    if x == 0.0 {
        return -f32::from_bits(1);
    }
    let b = x.to_bits();
    f32::from_bits(if x > 0.0 { b - 1 } else { b + 1 })
}

/// Round a real bound `r` (held as `f64`) OUTWARD to a sound width-`w` bound.
/// For `f64` this is the identity (RN₆₄ endpoints are exact + monotone); for
/// `f32` it snaps onto the `f32` grid bounding `r` on the correct side, then
/// steps one further `f32` ULP to cover the `RN₃₂` half-ULP.
fn round_out(r: f64, w: FWidth, up: bool) -> f64 {
    if r.is_nan() {
        return r;
    }
    match w {
        FWidth::W64 => r,
        FWidth::W32 => {
            if r.is_infinite() {
                return r;
            }
            let f = r as f32; // RN₆₄→₃₂
            let ff = f as f64;
            // snap so the f32 value bounds r on the requested side
            let bounding = if up {
                if ff >= r { f } else { f32_next_up(f) }
            } else if ff <= r {
                f
            } else {
                f32_next_down(f)
            };
            // one extra f32 ULP for the RN₃₂ half-ULP margin
            let stepped = if up {
                f32_next_up(bounding)
            } else {
                f32_next_down(bounding)
            };
            stepped as f64
        }
    }
}

impl FloatAbstract {
    /// `⊤`: any float, including NaN.
    pub fn top() -> Self {
        FloatAbstract {
            lo: f64::NEG_INFINITY,
            hi: f64::INFINITY,
            nan: true,
        }
    }

    /// A canonical `⊥` (empty): no finite value, no NaN.
    pub fn bottom() -> Self {
        FloatAbstract {
            lo: f64::INFINITY,
            hi: f64::NEG_INFINITY,
            nan: false,
        }
    }

    /// The singleton abstraction of a concrete float constant.
    pub fn constant(c: f64) -> Self {
        if c.is_nan() {
            FloatAbstract {
                lo: f64::INFINITY,
                hi: f64::NEG_INFINITY,
                nan: true,
            }
        } else {
            FloatAbstract {
                lo: c,
                hi: c,
                nan: false,
            }
        }
    }

    /// `true` if `γ = ∅`.
    pub fn is_bottom(&self) -> bool {
        !self.nan && self.lo > self.hi
    }

    /// Membership — the γ-sweep oracle.
    pub fn contains(&self, x: f64) -> bool {
        if x.is_nan() {
            self.nan
        } else {
            self.lo <= x && x <= self.hi
        }
    }

    /// `self ⊑ other` (γ(self) ⊆ γ(other)).
    pub fn leq(&self, other: &Self) -> bool {
        if self.is_bottom() {
            return true;
        }
        (!self.nan || other.nan) && other.lo <= self.lo && self.hi <= other.hi
    }

    /// Join `self ⊔ other` — `γ ⊇ γ(self) ∪ γ(other)`.
    pub fn join(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return *other;
        }
        if other.is_bottom() {
            return *self;
        }
        FloatAbstract {
            lo: self.lo.min(other.lo),
            hi: self.hi.max(other.hi),
            nan: self.nan || other.nan,
        }
    }

    /// Meet `self ⊓ other` — `γ ⊆ γ(self) ∩ γ(other)`.
    pub fn meet(&self, other: &Self) -> Self {
        FloatAbstract {
            lo: self.lo.max(other.lo),
            hi: self.hi.min(other.hi),
            nan: self.nan && other.nan,
        }
    }

    /// Negation (`f*.neg`): exact, no rounding. NaN stays possible.
    pub fn neg(&self) -> Self {
        FloatAbstract {
            lo: -self.hi,
            hi: -self.lo,
            nan: self.nan,
        }
    }

    /// Absolute value (`f*.abs`): exact.
    pub fn abs(&self) -> Self {
        let (lo, hi) = if self.lo >= 0.0 {
            (self.lo, self.hi)
        } else if self.hi <= 0.0 {
            (-self.hi, -self.lo)
        } else {
            (0.0, self.hi.max(-self.lo))
        };
        FloatAbstract {
            lo,
            hi,
            nan: self.nan,
        }
    }

    /// Coerce the bounds to the operation width's grid (outward). At `W32` a
    /// large finite `f64` bound overflows to `±∞` — modelling that an `f32`
    /// operation's operands are `f32` values, so a bound beyond `f32::MAX`
    /// really denotes `±∞` at runtime. Identity at `W64`.
    pub fn coerce(&self, w: FWidth) -> Self {
        if self.is_bottom() || w == FWidth::W64 {
            return *self;
        }
        FloatAbstract {
            lo: round_out(self.lo, w, false),
            hi: round_out(self.hi, w, true),
            nan: self.nan,
        }
    }

    /// Addition. The result's extrema are among the four corner sums; an
    /// `∞ + (−∞)` corner yields NaN (flagged + dropped from the hull), but the
    /// surviving corners still capture the reachable finite/`∞` results.
    /// Operands are coerced to the op width first (an `f32` add rounds its
    /// `f32` operands, where a `>f32::MAX` bound already means `±∞`).
    pub fn add(&self, other: &Self, w: FWidth) -> Self {
        let a = self.coerce(w);
        let b = other.coerce(w);
        let corners = [a.lo + b.lo, a.lo + b.hi, a.hi + b.lo, a.hi + b.hi];
        hull_corners(&corners, a.nan || b.nan, false, w)
    }

    /// Subtraction (`a − b == a + (−b)`).
    pub fn sub(&self, other: &Self, w: FWidth) -> Self {
        self.add(&other.neg(), w)
    }

    /// Multiplication — the extrema are among the four corner products (interval
    /// multiplication). A `0 · ∞` corner yields NaN; besides flagging NaN and
    /// dropping that corner, `0` itself is a reachable product (`0 · finite`),
    /// so it is folded into the hull (`include_zero_on_nan`).
    pub fn mul(&self, other: &Self, w: FWidth) -> Self {
        let a = self.coerce(w);
        let b = other.coerce(w);
        let corners = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi];
        // `0 · ∞` is NaN, and it is reachable whenever one operand's interval
        // contains 0 and the other reaches ±∞ — even when 0 is INTERIOR (so no
        // corner product is NaN). Detect it explicitly; `include_zero_on_nan`
        // then also folds the reachable finite `0` into the hull.
        let a_zero = a.lo <= 0.0 && 0.0 <= a.hi;
        let b_zero = b.lo <= 0.0 && 0.0 <= b.hi;
        let a_inf = a.lo == f64::NEG_INFINITY || a.hi == f64::INFINITY;
        let b_inf = b.lo == f64::NEG_INFINITY || b.hi == f64::INFINITY;
        let zero_times_inf = (a_zero && b_inf) || (b_zero && a_inf);
        hull_corners(&corners, a.nan || b.nan || zero_times_inf, true, w)
    }
}

/// Hull the non-NaN corner results into a sound `FloatAbstract`, applying
/// outward width-rounding. `seed_nan` seeds the NaN flag from the operands; a
/// NaN corner additionally sets it. `include_zero_on_nan` folds `0.0` into the
/// hull when a NaN corner appeared — for multiplication, where a `0 · ∞`
/// indeterminate hides the reachable finite product `0 · finite = 0`.
fn hull_corners(
    corners: &[f64],
    seed_nan: bool,
    include_zero_on_nan: bool,
    w: FWidth,
) -> FloatAbstract {
    let mut nan = seed_nan;
    let mut saw_nan_corner = false;
    let mut lo = f64::INFINITY;
    let mut hi = f64::NEG_INFINITY;
    for &c in corners {
        if c.is_nan() {
            nan = true;
            saw_nan_corner = true;
        } else {
            if c < lo {
                lo = c;
            }
            if c > hi {
                hi = c;
            }
        }
    }
    if include_zero_on_nan && saw_nan_corner {
        if 0.0 < lo {
            lo = 0.0;
        }
        if 0.0 > hi {
            hi = 0.0;
        }
    }
    if lo > hi {
        // every corner was NaN and no zero folded in — only NaN remains.
        return FloatAbstract {
            lo: f64::INFINITY,
            hi: f64::NEG_INFINITY,
            nan,
        };
    }
    FloatAbstract {
        lo: round_out(lo, w, false),
        hi: round_out(hi, w, true),
        nan,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    use alloc::vec::Vec;

    /// A representative concrete float grid: ±0, subnormals, small/large finite,
    /// ±∞, NaN.
    fn grid() -> Vec<f64> {
        alloc::vec![
            f64::NAN,
            f64::NEG_INFINITY,
            -1.0e300,
            -3.5,
            -1.0,
            -0.5,
            -f64::from_bits(1), // tiny negative subnormal
            -0.0,
            0.0,
            f64::from_bits(1),
            0.5,
            1.0,
            3.5,
            1.0e300,
            f64::INFINITY,
        ]
    }

    /// A family of abstract values covering the grid.
    fn samples() -> Vec<FloatAbstract> {
        let mut out = Vec::new();
        out.push(FloatAbstract::top());
        out.push(FloatAbstract::bottom());
        let pts = grid();
        for &c in &pts {
            out.push(FloatAbstract::constant(c));
        }
        // some finite intervals + a couple with NaN
        for &(lo, hi) in &[(-1.0, 1.0), (0.5, 3.5), (-3.5, -0.5), (0.0, f64::INFINITY)] {
            out.push(FloatAbstract { lo, hi, nan: false });
            out.push(FloatAbstract { lo, hi, nan: true });
        }
        out
    }

    fn gamma(a: &FloatAbstract) -> Vec<f64> {
        grid().into_iter().filter(|&x| a.contains(x)).collect()
    }

    /// Both f32 and f64 rounding must be covered by the sweep.
    const WIDTHS: [FWidth; 2] = [FWidth::W32, FWidth::W64];

    fn as_width(x: f64, w: FWidth) -> f64 {
        match w {
            FWidth::W64 => x,
            FWidth::W32 => x as f32 as f64,
        }
    }

    #[test]
    fn gamma_sweep_join_is_upper_bound() {
        for a in &samples() {
            for b in &samples() {
                let j = a.join(b);
                for x in gamma(a) {
                    assert!(j.contains(x), "join lost γ(a) {x}\n{a:?} ⊔ {b:?}");
                }
                for x in gamma(b) {
                    assert!(j.contains(x), "join lost γ(b) {x}");
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_leq_sound() {
        for a in &samples() {
            for b in &samples() {
                if a.leq(b) {
                    for x in gamma(a) {
                        assert!(b.contains(x), "leq unsound: {x} in a∉b\n{a:?} ⊑ {b:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_add_sound() {
        for w in WIDTHS {
            for a in &samples() {
                for b in &samples() {
                    let r = a.add(b, w);
                    for x in gamma(a) {
                        for y in gamma(b) {
                            // the concrete IEEE result at this width
                            let concrete = as_width(as_width(x, w) + as_width(y, w), w);
                            assert!(
                                r.contains(concrete),
                                "add unsound @ {w:?}: {x}+{y}={concrete} ∉ {r:?}\na={a:?} b={b:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_sub_sound() {
        for w in WIDTHS {
            for a in &samples() {
                for b in &samples() {
                    let r = a.sub(b, w);
                    for x in gamma(a) {
                        for y in gamma(b) {
                            let concrete = as_width(as_width(x, w) - as_width(y, w), w);
                            assert!(r.contains(concrete), "sub unsound @ {w:?}: {x}-{y}");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_mul_sound() {
        for w in WIDTHS {
            for a in &samples() {
                for b in &samples() {
                    let r = a.mul(b, w);
                    for x in gamma(a) {
                        for y in gamma(b) {
                            let concrete = as_width(as_width(x, w) * as_width(y, w), w);
                            assert!(
                                r.contains(concrete),
                                "mul unsound @ {w:?}: {x}*{y}={concrete} ∉ {r:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn gamma_sweep_neg_abs_sound() {
        for a in &samples() {
            let n = a.neg();
            let ab = a.abs();
            for x in gamma(a) {
                assert!(n.contains(-x), "neg unsound: -{x}");
                assert!(ab.contains(x.abs()), "abs unsound: |{x}|");
            }
        }
    }

    #[test]
    fn nan_is_tracked() {
        // 0.0 * inf = NaN must set the flag.
        let zero = FloatAbstract::constant(0.0);
        let inf = FloatAbstract::constant(f64::INFINITY);
        let r = zero.mul(&inf, FWidth::W64);
        assert!(r.nan, "0 * ∞ must be flagged NaN-possible");
        assert!(r.contains(f64::NAN));
    }

    #[test]
    fn inf_minus_inf_is_nan() {
        let pinf = FloatAbstract::constant(f64::INFINITY);
        let r = pinf.sub(&pinf, FWidth::W64);
        assert!(r.nan, "∞ − ∞ must be flagged NaN-possible");
    }

    #[test]
    fn f32_rounding_widens() {
        // A value not exactly representable in f32, added in f32, must stay in
        // the abstract result (the outward snap covers RN₃₂).
        let a = FloatAbstract::constant(0.1);
        let b = FloatAbstract::constant(0.2);
        let r = a.add(&b, FWidth::W32);
        let concrete = (0.1f32 + 0.2f32) as f64;
        assert!(r.contains(concrete), "f32 0.1+0.2 = {concrete} ∉ {r:?}");
    }
}
