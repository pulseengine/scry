(** * FEAT-011 — Soundness of scry's reachability lattice (Rocq).

    The reachability domain is the two-point lattice
    [Unreachable ⊑ Reachable] (whether a program point can be reached
    by some concrete execution). It was bundled in the initial domain
    set (DD-005) but the powerset/dead-code ANALYSIS consuming it was
    deferred at FEAT-006 — so this file proves the soundness of the
    reachability *lattice algebra* (the abstract foundation), and the
    dossier (docs/credit-dossier-v1.md) is explicit that no analyzer
    transfer function consumes it yet (paper/lattice-only, not
    code-consumed). Proving the algebra here keeps the v1.0 stack claim
    honest: the lattice is mechanized; its analyzer integration is named
    future work, not silently claimed.

    The soundness reading: [Reachable] is the sound top — when the
    analysis cannot prove a point dead it must mark it [Reachable], and
    [join] never moves down the lattice, so reachability can only
    over-approximate the truly-reachable set.

    No admits, no axioms.

    Build:  bazel build //proofs/rocq:reachability
    Test:   bazel test  //proofs/rocq:reachability_test
*)

(** ** The two-point reachability lattice. *)
Inductive reach := Unreachable | Reachable.

(** Order: [Unreachable ⊑ Reachable], reflexive. *)
Definition rleq (a b : reach) : Prop :=
  match a, b with
  | Unreachable, _ => True
  | Reachable, Reachable => True
  | Reachable, Unreachable => False
  end.

(** Join: [Reachable] iff either operand is [Reachable] (the merge at a
    control-flow join point). *)
Definition rjoin (a b : reach) : reach :=
  match a, b with
  | Unreachable, Unreachable => Unreachable
  | _, _ => Reachable
  end.

(** γ: [Reachable] admits "is reached" for any concrete reachability
    bit [b : bool]; [Unreachable] admits only "not reached". This is the
    soundness reading — [Reachable] over-approximates. *)
Definition gamma_reach (a : reach) (b : bool) : Prop :=
  match a with
  | Reachable => True
  | Unreachable => b = false
  end.

(** ** [Reachable] is the sound top: it admits every concrete bit. *)
Theorem reachable_is_top : forall b, gamma_reach Reachable b.
Proof. intros b. simpl. exact I. Qed.

(** ** Join over-approximates the union of concrete reachability.

    If a concrete bit is admitted by [a] or by [b], it is admitted by
    [a ⊔ b] — the soundness of merging reachability at a join point. *)
Theorem rjoin_sound :
  forall a b cb, (gamma_reach a cb \/ gamma_reach b cb) -> gamma_reach (rjoin a b) cb.
Proof.
  intros [] [] cb H; simpl in *; exact I || (destruct H as [H|H]; exact H).
Qed.

(** ** Order is consistent with join: [a ⊑ b ↔ a ⊔ b = b]. *)
Theorem rleq_join_consistent :
  forall a b, rleq a b <-> rjoin a b = b.
Proof.
  intros [] []; simpl; split; intro H; try reflexivity; try exact I;
    try discriminate; try contradiction.
Qed.

(** ** [rleq] is reflexive and transitive (a partial order). *)
Theorem rleq_refl : forall a, rleq a a.
Proof. intros []; simpl; exact I. Qed.

Theorem rleq_trans : forall a b c, rleq a b -> rleq b c -> rleq a c.
Proof. intros [] [] []; simpl; intros H1 H2; exact I || exact H1 || exact H2. Qed.

(** ** Join is an upper bound (forward analysis never moves down). *)
Theorem rjoin_upper : forall a b, rleq a (rjoin a b) /\ rleq b (rjoin a b).
Proof. intros [] []; simpl; split; exact I. Qed.
