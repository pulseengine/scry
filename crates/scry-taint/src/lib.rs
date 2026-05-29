//! scry-taint — the pure security-label lattice for scry's taint /
//! noninterference domain (FEAT-009, v0.8).
//!
//! This crate holds the *algebra* of the two-point confidentiality
//! lattice `low ⊑ high` and nothing else: no Wasm parsing, no WIT
//! bindings, no I/O. It is the taint analogue of [`scry-provenance`]:
//! a pure, dependency-free crate that compiles to BOTH `wasm32-wasip2`
//! (where `wasm-lattice` delegates its WIT `label-*` exports to it, so
//! the *shipped* lattice code is exactly this code) AND natively (where
//! `scry-host-tests` falsifies the lattice laws against it).
//!
//! The lattice is the classic information-flow ordering:
//!
//! ```text
//!        high   (⊤ — secret; "may depend on a declared High source")
//!         |
//!        low    (⊥ — public; "provably carries no secret")
//! ```
//!
//! Forward taint propagation uses [`join`]: a value derived from two
//! operands is secret iff either operand was. [`meet`] is provided for
//! lattice completeness and the reduced-product combinator. The lattice
//! has height 1, so its algebra is *exhaustively* falsifiable — every
//! law below is checked over all 2ⁿ input tuples in the unit tests.
//!
//! Soundness role (REQ-001, AC-007): `high` is the sound top. When the
//! analyzer cannot prove a value is public it must label it `high`;
//! `join` never moves *down* the lattice, so taint can only ever
//! over-approximate the true secret-dependence — the property that
//! makes "absence of a finding implies noninterference" sound.

#![cfg_attr(not(test), no_std)]

/// A confidentiality label from the two-point lattice `low ⊑ high`.
///
/// `Low` is the bottom element (provably public); `High` is the top
/// element (the sound over-approximation for any value that may depend
/// on a declared secret source).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Label {
    /// Bottom (⊥): provably public.
    Low,
    /// Top (⊤): may carry secret data.
    High,
}

/// The bottom element of the lattice (`Low`; ⊥).
#[inline]
pub const fn bottom() -> Label {
    Label::Low
}

/// The top element of the lattice (`High`; ⊤).
#[inline]
pub const fn top() -> Label {
    Label::High
}

/// `a ⊑ b` — the chain order `low ⊑ high`.
///
/// True for every pair except `high ⊑ low`. Equivalent to
/// `join(a, b) == b` (checked exhaustively in the tests), the standard
/// consistency law between a lattice's order and its join.
#[inline]
pub const fn leq(a: Label, b: Label) -> bool {
    // The only non-related pair (the only place the chain fails) is
    // a = High, b = Low.
    !matches!((a, b), (Label::High, Label::Low))
}

/// `a ⊔ b` — least upper bound. `High` iff either operand is `High`.
///
/// This is the forward taint-propagation rule: the abstract value
/// produced from two operands is secret iff either input was.
#[inline]
pub const fn join(a: Label, b: Label) -> Label {
    match (a, b) {
        (Label::Low, Label::Low) => Label::Low,
        _ => Label::High,
    }
}

/// `a ⊓ b` — greatest lower bound. `Low` iff either operand is `Low`.
#[inline]
pub const fn meet(a: Label, b: Label) -> Label {
    match (a, b) {
        (Label::High, Label::High) => Label::High,
        _ => Label::Low,
    }
}

/// `true` iff `x` is the bottom element (`Low`). Mirrors the
/// `is-bottom` query the interval domain exposes, for symmetry.
#[inline]
pub const fn is_bottom(x: Label) -> bool {
    matches!(x, Label::Low)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// All elements of the (tiny) lattice — the basis for exhaustive
    /// law checking.
    const ALL: [Label; 2] = [Label::Low, Label::High];

    #[test]
    fn extrema_are_low_and_high() {
        assert_eq!(bottom(), Label::Low);
        assert_eq!(top(), Label::High);
        assert!(is_bottom(bottom()));
        assert!(!is_bottom(top()));
    }

    #[test]
    fn join_truth_table() {
        assert_eq!(join(Label::Low, Label::Low), Label::Low);
        assert_eq!(join(Label::Low, Label::High), Label::High);
        assert_eq!(join(Label::High, Label::Low), Label::High);
        assert_eq!(join(Label::High, Label::High), Label::High);
    }

    #[test]
    fn meet_truth_table() {
        assert_eq!(meet(Label::Low, Label::Low), Label::Low);
        assert_eq!(meet(Label::Low, Label::High), Label::Low);
        assert_eq!(meet(Label::High, Label::Low), Label::Low);
        assert_eq!(meet(Label::High, Label::High), Label::High);
    }

    #[test]
    fn leq_truth_table() {
        assert!(leq(Label::Low, Label::Low));
        assert!(leq(Label::Low, Label::High));
        assert!(!leq(Label::High, Label::Low)); // the only false case
        assert!(leq(Label::High, Label::High));
    }

    // ── Lattice axioms, checked exhaustively over ALL × ALL(× ALL) ──

    #[test]
    fn join_and_meet_are_commutative() {
        for a in ALL {
            for b in ALL {
                assert_eq!(join(a, b), join(b, a), "join commutativity {a:?} {b:?}");
                assert_eq!(meet(a, b), meet(b, a), "meet commutativity {a:?} {b:?}");
            }
        }
    }

    #[test]
    fn join_and_meet_are_associative() {
        for a in ALL {
            for b in ALL {
                for c in ALL {
                    assert_eq!(join(join(a, b), c), join(a, join(b, c)));
                    assert_eq!(meet(meet(a, b), c), meet(a, meet(b, c)));
                }
            }
        }
    }

    #[test]
    fn join_and_meet_are_idempotent() {
        for a in ALL {
            assert_eq!(join(a, a), a);
            assert_eq!(meet(a, a), a);
        }
    }

    #[test]
    fn absorption_laws_hold() {
        for a in ALL {
            for b in ALL {
                assert_eq!(join(a, meet(a, b)), a, "a ⊔ (a ⊓ b) = a");
                assert_eq!(meet(a, join(a, b)), a, "a ⊓ (a ⊔ b) = a");
            }
        }
    }

    #[test]
    fn bottom_and_top_are_identities() {
        for a in ALL {
            assert_eq!(join(bottom(), a), a, "⊥ ⊔ a = a");
            assert_eq!(meet(top(), a), a, "⊤ ⊓ a = a");
            assert_eq!(join(top(), a), top(), "⊤ ⊔ a = ⊤");
            assert_eq!(meet(bottom(), a), bottom(), "⊥ ⊓ a = ⊥");
        }
    }

    /// The defining consistency law between the order and the join:
    /// `a ⊑ b  ⟺  a ⊔ b = b` (equivalently `a ⊓ b = a`). This is the
    /// property the analyzer relies on when it compares labels at
    /// fixpoint merge points.
    #[test]
    fn leq_is_consistent_with_join_and_meet() {
        for a in ALL {
            for b in ALL {
                assert_eq!(leq(a, b), join(a, b) == b, "leq⟺join {a:?} {b:?}");
                assert_eq!(leq(a, b), meet(a, b) == a, "leq⟺meet {a:?} {b:?}");
            }
        }
    }

    /// `leq` is a partial order: reflexive, antisymmetric, transitive.
    #[test]
    fn leq_is_a_partial_order() {
        for a in ALL {
            assert!(leq(a, a), "reflexive");
        }
        for a in ALL {
            for b in ALL {
                if leq(a, b) && leq(b, a) {
                    assert_eq!(a, b, "antisymmetric");
                }
                for c in ALL {
                    if leq(a, b) && leq(b, c) {
                        assert!(leq(a, c), "transitive");
                    }
                }
            }
        }
    }

    /// Forward propagation never moves *down* the lattice — the
    /// soundness-critical monotonicity that makes taint an
    /// over-approximation: `a ⊑ join(a, b)` and `b ⊑ join(a, b)`.
    #[test]
    fn join_is_an_upper_bound() {
        for a in ALL {
            for b in ALL {
                assert!(leq(a, join(a, b)));
                assert!(leq(b, join(a, b)));
            }
        }
    }
}
