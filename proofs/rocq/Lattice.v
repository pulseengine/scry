(** * FEAT-012 — Interval-lattice partial-order reflexivity (Rocq).

    This file mechanically proves [forall x : interval, sqsubseteq x x],
    the reflexivity of the interval-domain partial order [⊑] used by
    scry's wasm-lattice (crates/wasm-lattice/src/lib.rs).

    The full mechanized soundness theorem of the interval domain
    against WasmCert-Coq lands at v0.9 (FEAT-010). The v0.2 ship just
    lights up the Rocq toolchain end-to-end with one provable theorem.

    Build:
      bazel build //proofs/rocq:lattice
    Test:
      bazel test  //proofs/rocq:lattice_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** ** Interval representation

    An interval is a pair [(lo, hi) : Z * Z]. Bottom is encoded by
    [lo > hi] — the same convention used by the production crate
    ({1, 0} canonical). The proofs below quantify over arbitrary
    integer pairs; bottom-handling is the subject of a future
    extension (FEAT-010).
*)

Record interval := mk_interval { lo : Z; hi : Z }.

(** ** Partial order [⊑]

    The interval lattice order: [a ⊑ b] iff [b] contains [a] as a set
    of concrete values. For non-bottom intervals this is

      [lo_a, hi_a] ⊑ [lo_b, hi_b]  iff  lo_b ≤ lo_a  /\  hi_a ≤ hi_b.

    We use this concrete-extension reading directly, omitting the
    bottom case at v0.2 — it'll be added when the full mechanization
    lands at v0.9 (FEAT-010).
*)
Definition sqsubseteq (a b : interval) : Prop :=
  lo b <= lo a /\ hi a <= hi b.

(** ** Main theorem (FEAT-012 AC#2): [⊑] is reflexive.

    Mechanically discharged by [lia] (no admits, no axioms).
*)
Theorem sqsubseteq_refl : forall x : interval, sqsubseteq x x.
Proof.
  intros x. unfold sqsubseteq. split; lia.
Qed.

(** ** Companion lemma: [⊑] is transitive.

    Not strictly required by FEAT-012 AC#2, but the proof is
    one-liner and we'll lean on it when the v0.9 mechanization
    expands to a full lattice proof.
*)
Theorem sqsubseteq_trans :
  forall x y z : interval,
    sqsubseteq x y -> sqsubseteq y z -> sqsubseteq x z.
Proof.
  intros x y z [Hxy_lo Hxy_hi] [Hyz_lo Hyz_hi].
  unfold sqsubseteq. split; lia.
Qed.

Close Scope Z_scope.
