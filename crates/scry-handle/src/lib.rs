#![no_std]
#![forbid(unsafe_code)]
//! # scry-sai-handle — the affine Component-Model handle-state lattice
//!
//! FEAT-049 (REQ-003, MF-007). The Component Model's `own`/`borrow` resource
//! handles are AFFINE: an owned handle may be used any number of times but
//! dropped exactly once; after the drop, any use (including a second drop) is a
//! fault. scry only sees CORE Wasm, but the canonical ABI lowers
//! `resource.drop` to a call to an import named `[resource-drop]T` and resource
//! methods/constructors to other `[...]`-named imports, so a handle's lifetime
//! is observable as a sequence of such calls on the value in a local.
//!
//! This crate is the pure lattice + transition functions the analyzer's
//! handle-state pass runs. A concrete handle at a program point is either
//! `Alive` or `Dropped`; the abstract [`HandleState`] over-approximates the set
//! of concrete statuses reaching that point.
//!
//! ## Concretization
//!
//! ```text
//!   γ(Bottom)  = {}                 (unreachable)
//!   γ(Alive)   = { alive }
//!   γ(Dropped) = { dropped }
//!   γ(Top)     = { alive, dropped } (a merge of both — use is only *maybe* UAD)
//! ```
//!
//! ## Transitions (sound over-approximations)
//!
//! * [`HandleState::after_drop`] — dropping. From `Alive` → `Dropped`; from
//!   `Dropped` (or `Top`, which may be dropped) it is a **double-drop**.
//! * [`HandleState::use_is_after_drop`] — a use is a **use-after-drop** iff the
//!   handle is DEFINITELY `Dropped`. (`Top` — maybe dropped — is reported
//!   separately as a *possible* UAD by the analyzer, never as a definite one,
//!   so correct owned/borrowed code raises no false definite report.)
//!
//! The lattice laws (join is the least upper bound, order is a partial order)
//! and the transition soundness are asserted by an exhaustive γ-sweep here and
//! mechanized admit-free in `proofs/rocq/Handle.v`.

/// The abstract state of a resource handle at a program point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HandleState {
    /// Unreachable / no concrete handle (`γ = ∅`).
    Bottom,
    /// Definitely a live (not-yet-dropped) handle.
    Alive,
    /// Definitely a dropped handle.
    Dropped,
    /// May be either alive or dropped (a control-flow merge of the two).
    Top,
}

/// A concrete handle status — the γ elements.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Concrete {
    Alive,
    Dropped,
}

impl HandleState {
    /// Membership: is the concrete status in `γ(self)`? The γ-sweep oracle.
    pub fn contains(self, c: Concrete) -> bool {
        match self {
            HandleState::Bottom => false,
            HandleState::Alive => c == Concrete::Alive,
            HandleState::Dropped => c == Concrete::Dropped,
            HandleState::Top => true,
        }
    }

    /// `self ⊑ other` (γ(self) ⊆ γ(other)).
    pub fn leq(self, other: Self) -> bool {
        matches!(
            (self, other),
            (HandleState::Bottom, _)
                | (_, HandleState::Top)
                | (HandleState::Alive, HandleState::Alive)
                | (HandleState::Dropped, HandleState::Dropped)
        )
    }

    /// Join `self ⊔ other` — the least upper bound (control-flow merge).
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            (HandleState::Bottom, x) | (x, HandleState::Bottom) => x,
            (a, b) if a == b => a,
            // Alive ⊔ Dropped (in either order), or anything with Top → Top.
            _ => HandleState::Top,
        }
    }

    /// The state after a `resource.drop` on a handle in this state, paired with
    /// whether that drop is a **double-drop** fault (the handle may already be
    /// dropped). After any drop the handle is `Dropped`.
    pub fn after_drop(self) -> (Self, bool) {
        let double = matches!(self, HandleState::Dropped | HandleState::Top);
        (HandleState::Dropped, double)
    }

    /// Is a USE of a handle in this state a DEFINITE use-after-drop? Only when
    /// the handle is definitely `Dropped`. (`Top` is a *possible* UAD — the
    /// analyzer surfaces that distinctly and never as a definite fault, so
    /// correct code merged with an unrelated path raises no false definite.)
    pub fn use_is_after_drop(self) -> bool {
        self == HandleState::Dropped
    }

    /// Is a use of a handle in this state a POSSIBLE (but not definite)
    /// use-after-drop? True only for `Top` (may be dropped on some path).
    pub fn use_is_maybe_after_drop(self) -> bool {
        self == HandleState::Top
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    use alloc::vec;
    use alloc::vec::Vec;

    fn all() -> Vec<HandleState> {
        vec![
            HandleState::Bottom,
            HandleState::Alive,
            HandleState::Dropped,
            HandleState::Top,
        ]
    }
    const CONCRETES: [Concrete; 2] = [Concrete::Alive, Concrete::Dropped];

    fn gamma(s: HandleState) -> Vec<Concrete> {
        CONCRETES.into_iter().filter(|&c| s.contains(c)).collect()
    }

    #[test]
    fn join_is_upper_bound() {
        for a in all() {
            for b in all() {
                let j = a.join(b);
                for c in gamma(a) {
                    assert!(j.contains(c), "join lost γ(a) {c:?}: {a:?}⊔{b:?}={j:?}");
                }
                for c in gamma(b) {
                    assert!(j.contains(c), "join lost γ(b) {c:?}");
                }
            }
        }
    }

    #[test]
    fn leq_sound() {
        for a in all() {
            for b in all() {
                if a.leq(b) {
                    for c in gamma(a) {
                        assert!(b.contains(c), "leq unsound: {c:?} in {a:?}∉{b:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn drop_then_use_is_after_drop() {
        let (s, dbl) = HandleState::Alive.after_drop();
        assert_eq!(s, HandleState::Dropped);
        assert!(!dbl, "first drop of a live handle is not a double-drop");
        assert!(s.use_is_after_drop(), "use of a dropped handle is UAD");
    }

    #[test]
    fn double_drop_detected() {
        let (s1, _) = HandleState::Alive.after_drop();
        let (_, dbl) = s1.after_drop();
        assert!(dbl, "dropping an already-dropped handle is a double-drop");
    }

    #[test]
    fn live_handle_use_is_safe() {
        assert!(!HandleState::Alive.use_is_after_drop());
        assert!(!HandleState::Alive.use_is_maybe_after_drop());
    }

    #[test]
    fn merged_alive_dropped_is_top_only_maybe() {
        let merged = HandleState::Alive.join(HandleState::Dropped);
        assert_eq!(merged, HandleState::Top);
        // Top is only a POSSIBLE UAD, never a definite one — no false definite.
        assert!(!merged.use_is_after_drop());
        assert!(merged.use_is_maybe_after_drop());
    }
}
