//! FEAT-012 / FEAT-010 — Verus proof that the interval-domain `join`
//! operator is commutative **up to concretization** (semantic equality),
//! and that join with bottom is the semantic identity.
//!
//! ## Why semantic (γ) equality, not structural `==`
//!
//! `join` short-circuits on bottom: `join(a, b) = if is_bot(a) { b } else
//! if is_bot(b) { a } else { min/max }`. When BOTH `a` and `b` are bottom
//! with *different* encodings (any `lo > hi` is bottom — e.g. `{1,0}` and
//! `{5,0}`), `join(a, b) = b` but `join(b, a) = a`, which are NOT
//! structurally equal. So `join(a,b) == join(b,a)` is FALSE as a structural
//! theorem. (The earlier empty-bodied structural version asserted exactly
//! that and was never actually checked — the Verus toolchain was broken; it
//! does not verify.)
//!
//! The correct, true theorem is over the CONCRETIZATION: both results denote
//! the SAME set of integers. Two bottoms both denote ∅, and the non-bottom
//! cases are structurally equal (min/max commute). We model the
//! concretization `γ : Interval → set of int` as the membership predicate
//! `gamma(x, z)` and prove the join results are γ-equal pointwise. This is
//! the Cousot-sense statement that matches `Soundness.v`'s γ-style and is
//! what a sound analysis actually relies on (the abstract value denotes a
//! set; the encoding of ∅ is irrelevant).
//!
//! Theorems (mechanically, no admits):
//!   * `join_commutative` : ∀ z. z ∈ γ(join(a,b)) ⇔ z ∈ γ(join(b,a))
//!   * `join_bot_identity`: is_bot(b) ⇒ ∀ z. z ∈ γ(join(a,b)) ⇔ z ∈ γ(a)

use vstd::prelude::*;

verus! {

/// Minimal mirror of the interval type from `crates/scry-interval/src/lib.rs`.
/// An interval with `lo > hi` is bottom (denotes ∅); the specific witnessing
/// pair does not matter — only the `lo > hi` predicate.
pub struct Interval {
    pub lo: i64,
    pub hi: i64,
}

/// `true` iff the interval is bottom (empty / denotes ∅).
pub open spec fn is_bot(x: Interval) -> bool {
    x.lo > x.hi
}

/// Concretization membership: `z ∈ γ(x)`. Bottom denotes ∅ (no member);
/// otherwise the closed integer range `[lo, hi]`. `z` is a mathematical
/// integer (`int`) so the SMT backend reasons without i64 overflow.
pub open spec fn gamma(x: Interval, z: int) -> bool {
    !is_bot(x) && x.lo as int <= z && z <= x.hi as int
}

/// Spec-level `join`. Mirrors `join` in the production crate.
pub open spec fn join(a: Interval, b: Interval) -> Interval {
    if is_bot(a) {
        b
    } else if is_bot(b) {
        a
    } else {
        Interval {
            lo: if a.lo <= b.lo { a.lo } else { b.lo },
            hi: if a.hi >= b.hi { a.hi } else { b.hi },
        }
    }
}

/// **Main theorem (FEAT-012 AC#1, corrected):** `join` is commutative up to
/// concretization — `join(a,b)` and `join(b,a)` denote the same integer set.
/// True in all four bottom-combinations: both-bottom ⇒ both denote ∅; one
/// bottom ⇒ both results equal the other operand; neither bottom ⇒ min/max
/// commute, so the results are structurally equal. No admits, no axioms.
pub proof fn join_commutative(a: Interval, b: Interval)
    ensures
        forall|z: int| gamma(join(a, b), z) <==> gamma(join(b, a), z),
{
    assert forall|z: int| gamma(join(a, b), z) <==> gamma(join(b, a), z) by {
        // `is_bot` / `join` / `gamma` are `open` and unfold; the proof is a
        // case split on is_bot(a), is_bot(b). In every case join(a,b) and
        // join(b,a) are either the same interval or both bottom (γ = ∅), and
        // min/max commute in the non-bottom case.
        if is_bot(a) {
        } else if is_bot(b) {
        } else {
        }
    }
}

/// Companion lemma: join with bottom is the semantic identity. When `b` is
/// bottom, `join(a,b)` denotes the same set as `a` — whether or not `a` is
/// itself bottom (if `a` is bottom too, `join(a,b) = b` which is also ∅).
pub proof fn join_bot_identity(a: Interval, b: Interval)
    requires
        is_bot(b),
    ensures
        forall|z: int| gamma(join(a, b), z) <==> gamma(a, z),
{
    assert forall|z: int| gamma(join(a, b), z) <==> gamma(a, z) by {
        if is_bot(a) {
        } else {
        }
    }
}

} // verus!
