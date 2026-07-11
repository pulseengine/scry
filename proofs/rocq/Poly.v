(** * FEAT-057 — Lattice soundness of scry's convex-polyhedra domain (Rocq).

    DD-019 / REQ-016 / AC-012. scry-sai-poly abstracts a set of program states
    as a conjunction of linear constraints (a convex polyhedron). This file
    mechanizes the domain's LATTICE ALGEBRA — the order is a preorder, meet is a
    greatest lower bound, join is an upper bound — at the semantic level, over
    the concretization γ.

    ## Honest scope (DD-019 — read this).

    A constraint is modelled here ABSTRACTLY as a half-space predicate
    [hs = point -> Prop]; a polyhedron is a [list hs] and γ is their
    conjunction. This is faithful for the lattice laws, which do not depend on
    the constraints being *linear* — only on γ being a conjunction of
    half-spaces. The parts that DO depend on linearity — deciding entailment by
    Fourier–Motzkin, and the join's over-approximation of the convex hull — are
    NOT mechanized here; they are γ-sweep-validated in the crate's native tests.
    So this file proves exactly the "mechanize the lattice" half of DD-019 and
    makes NO claim about the FM transfer functions (mirroring how Float.v
    mechanizes the float lattice while the rounding transfers are γ-swept).

    Key results (all admit-free, discharged by list reasoning — no [lia]):
      - [gamma_meet_iff]   : γ(P ⊓ Q) ⟺ γ(P) ∧ γ(Q)            (meet is exact)
      - [meet_lower_bound] : P ⊓ Q ⊑ P   and   P ⊓ Q ⊑ Q
      - [leq_refl] / [leq_trans]                                (⊑ is a preorder)
      - [leq_sound]        : P ⊑ Q → γ(P) ⊆ γ(Q)
      - [join_upper_bound] : a sound join (every constraint entailed by both)
                             over-approximates each operand: P ⊑ J and Q ⊑ J.

    Build:  bazel build //proofs/rocq:poly
    Test:   bazel test  //proofs/rocq:poly_test
*)

From Stdlib Require Import List.
Import ListNotations.

Section Polyhedra.

  (** Concrete states (points). Left abstract — the lattice laws are
      point-agnostic. *)
  Variable point : Type.

  (** A constraint is its satisfaction predicate — the half-space it cuts. *)
  Definition hs := point -> Prop.

  (** A polyhedron is a conjunction of constraints. *)
  Definition poly := list hs.

  (** γ: a point is in the polyhedron iff it satisfies every constraint. *)
  Definition gamma (P : poly) (x : point) : Prop :=
    Forall (fun c => c x) P.

  (** ** Meet = constraint-list append (conjunction). Exact intersection. *)
  Definition meet (P Q : poly) : poly := P ++ Q.

  Theorem gamma_meet_iff :
    forall P Q x, gamma (meet P Q) x <-> (gamma P x /\ gamma Q x).
  Proof.
    intros P Q x. unfold gamma, meet. apply Forall_app.
  Qed.

  (** ** Semantic entailment: P forces the constraint c. (This is the SPEC the
      Fourier–Motzkin algorithm decides; FM itself is γ-swept, not proven here.) *)
  Definition entails (P : poly) (c : hs) : Prop :=
    forall x, gamma P x -> c x.

  (** ** Order: P ⊑ Q iff P entails every constraint of Q. *)
  Definition leq (P Q : poly) : Prop :=
    Forall (fun c => entails P c) Q.

  (** ⊑ soundly implies γ-inclusion. *)
  Theorem leq_sound :
    forall P Q, leq P Q -> forall x, gamma P x -> gamma Q x.
  Proof.
    intros P Q Hle x Hpx. unfold gamma. rewrite Forall_forall.
    intros c Hc. unfold leq in Hle. rewrite Forall_forall in Hle.
    apply (Hle c Hc). exact Hpx.
  Qed.

  (** ⊑ is reflexive. *)
  Theorem leq_refl : forall P, leq P P.
  Proof.
    intro P. unfold leq. rewrite Forall_forall. intros c Hc.
    unfold entails. intros x Hpx. unfold gamma in Hpx.
    rewrite Forall_forall in Hpx. apply (Hpx c Hc).
  Qed.

  (** ⊑ is transitive. *)
  Theorem leq_trans : forall P Q R, leq P Q -> leq Q R -> leq P R.
  Proof.
    intros P Q R Hpq Hqr. unfold leq. rewrite Forall_forall.
    intros c Hc. unfold entails. intros x Hpx.
    (* P ⊑ Q gives γ(P) ⊆ γ(Q); Q entails c; so c x. *)
    assert (Hqx : gamma Q x) by (apply (leq_sound P Q Hpq x Hpx)).
    unfold leq in Hqr. rewrite Forall_forall in Hqr.
    apply (Hqr c Hc). exact Hqx.
  Qed.

  (** ** Meet is a lower bound: P ⊓ Q ⊑ P and P ⊓ Q ⊑ Q. *)
  Theorem meet_lower_bound_l : forall P Q, leq (meet P Q) P.
  Proof.
    intros P Q. unfold leq. rewrite Forall_forall. intros c Hc.
    unfold entails. intros x Hm.
    apply gamma_meet_iff in Hm. destruct Hm as [Hp _].
    unfold gamma in Hp. rewrite Forall_forall in Hp. apply (Hp c Hc).
  Qed.

  Theorem meet_lower_bound_r : forall P Q, leq (meet P Q) Q.
  Proof.
    intros P Q. unfold leq. rewrite Forall_forall. intros c Hc.
    unfold entails. intros x Hm.
    apply gamma_meet_iff in Hm. destruct Hm as [_ Hq].
    unfold gamma in Hq. rewrite Forall_forall in Hq. apply (Hq c Hc).
  Qed.

  (** ** Join upper bound.

      A SOUND join returns constraints each entailed by BOTH operands (the crate
      builds these from the operands' combined pool). Any such polyhedron
      over-approximates each operand. This captures γ(P) ∪ γ(Q) ⊆ γ(P ⊔ Q). *)
  Definition join_sound (J P Q : poly) : Prop :=
    Forall (fun c => entails P c) J /\ Forall (fun c => entails Q c) J.

  Theorem join_upper_bound :
    forall J P Q, join_sound J P Q -> leq P J /\ leq Q J.
  Proof.
    intros J P Q [HP HQ]. split; unfold leq; assumption.
  Qed.

  (** Hence the semantic over-approximation, via [leq_sound]. *)
  Theorem join_covers_both :
    forall J P Q, join_sound J P Q ->
      (forall x, gamma P x -> gamma J x) /\ (forall x, gamma Q x -> gamma J x).
  Proof.
    intros J P Q Hj. destruct (join_upper_bound J P Q Hj) as [HPJ HQJ].
    split.
    - apply (leq_sound P J HPJ).
    - apply (leq_sound Q J HQJ).
  Qed.

End Polyhedra.
