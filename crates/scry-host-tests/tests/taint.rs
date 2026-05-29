//! FEAT-009 (AC-007) host-side falsifier for the security-label (taint)
//! lattice.
//!
//! The lattice algebra ships inside the `wasm-lattice` Wasm component,
//! whose WIT `label-*` exports delegate to the pure `scry-taint` crate.
//! Because the live `analyze()` round-trip is still gated by the
//! wac_compose / wasmtime-45 root-import limitation (see
//! `tests/soundness.rs`), we falsify the *exact shipped lattice code*
//! here on the native cargo path by exercising `scry-taint` directly —
//! the same crate the component compiles in. This is the taint analogue
//! of `tests/provenance.rs`.
//!
//! Kill-criterion (v0.8): the label lattice obeys its algebraic laws AND
//! forward propagation never moves *down* the lattice — i.e. `join` is an
//! upper bound and `high` (⊤) is absorbing. If either fails, taint could
//! under-approximate secret dependence and "absence of a finding implies
//! noninterference" would be unsound. All laws are checked EXHAUSTIVELY:
//! the lattice has height 1, so 2ⁿ input tuples cover it completely.

use scry_taint::{Label, bottom, is_bottom, join, leq, meet, top};

const ALL: [Label; 2] = [Label::Low, Label::High];

#[test]
fn extrema_are_low_and_high() {
    assert_eq!(bottom(), Label::Low, "⊥ is low (public)");
    assert_eq!(top(), Label::High, "⊤ is high (secret)");
    assert!(is_bottom(bottom()));
    assert!(!is_bottom(top()));
}

#[test]
fn join_is_logical_or_meet_is_logical_and() {
    // join: high iff either operand high (the forward-taint rule).
    assert_eq!(join(Label::Low, Label::Low), Label::Low);
    assert_eq!(join(Label::Low, Label::High), Label::High);
    assert_eq!(join(Label::High, Label::Low), Label::High);
    assert_eq!(join(Label::High, Label::High), Label::High);
    // meet: low iff either operand low.
    assert_eq!(meet(Label::Low, Label::Low), Label::Low);
    assert_eq!(meet(Label::Low, Label::High), Label::Low);
    assert_eq!(meet(Label::High, Label::Low), Label::Low);
    assert_eq!(meet(Label::High, Label::High), Label::High);
}

#[test]
fn order_is_the_chain_low_below_high() {
    assert!(leq(Label::Low, Label::Low));
    assert!(leq(Label::Low, Label::High));
    assert!(leq(Label::High, Label::High));
    // The single dropped pair — the whole point of the lattice.
    assert!(!leq(Label::High, Label::Low), "high must NOT be ⊑ low");
}

#[test]
fn lattice_axioms_hold_exhaustively() {
    for a in ALL {
        // idempotence
        assert_eq!(join(a, a), a);
        assert_eq!(meet(a, a), a);
        // identities
        assert_eq!(join(bottom(), a), a, "⊥ ⊔ a = a");
        assert_eq!(meet(top(), a), a, "⊤ ⊓ a = a");
        for b in ALL {
            // commutativity
            assert_eq!(join(a, b), join(b, a));
            assert_eq!(meet(a, b), meet(b, a));
            // absorption
            assert_eq!(join(a, meet(a, b)), a);
            assert_eq!(meet(a, join(a, b)), a);
            // order ⟺ join/meet consistency
            assert_eq!(leq(a, b), join(a, b) == b);
            assert_eq!(leq(a, b), meet(a, b) == a);
            for c in ALL {
                // associativity
                assert_eq!(join(join(a, b), c), join(a, join(b, c)));
                assert_eq!(meet(meet(a, b), c), meet(a, meet(b, c)));
            }
        }
    }
}

/// The soundness-critical property for taint over-approximation: a value
/// derived from operands is at least as secret as each operand, and
/// `high` is absorbing. This is exactly what guarantees the analyzer's
/// forward propagation can only ADD taint — so a Low result is provably
/// independent of every High source (REQ-001 / AC-007).
#[test]
fn join_is_an_upper_bound_and_high_is_absorbing() {
    for a in ALL {
        for b in ALL {
            assert!(leq(a, join(a, b)), "a ⊑ a⊔b");
            assert!(leq(b, join(a, b)), "b ⊑ a⊔b");
        }
        // High absorbs: once secret, always secret under join.
        assert_eq!(join(Label::High, a), Label::High);
    }
}

/// `leq` is a genuine partial order (reflexive, antisymmetric,
/// transitive) — the property the analyzer relies on when comparing
/// labels at structured-control merge points.
#[test]
fn leq_is_a_partial_order() {
    for a in ALL {
        assert!(leq(a, a), "reflexive");
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
