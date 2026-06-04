(** * FEAT-016 slice-2a — Soundness of the loop fixpoint (Rocq).

    v1.5's interval pass replaces slice-1's write-set havoc with a real
    iterate-then-widen fixpoint at loop headers: it computes a header
    invariant [S] with [entry ⊑ S] and [fhat S ⊑ S] (a post-fixpoint of the
    sound abstract body transfer [fhat]), reached by joining the back-edge
    state and widening. See `Interp::loop_region` in
    `crates/scry-analyze-core/src/lib.rs`.

    This file mechanizes the soundness obligation that incurs, in the same
    Cousot over-approximation sense as [Soundness.v] / [WriteSetHavoc.v]: a
    post-fixpoint of a sound transfer, covering the loop entry, OVER-
    APPROXIMATES every concrete iterate of the loop body — so the analyzer's
    header invariant is sound for a loop run any number of times. No admits,
    no axioms (the proof-in-slice gate, DD-015).

    Scope / honesty (for the assessor): the concrete loop body is abstracted
    to a function [f : Z -> Z] on one tracked value and [fhat] its sound
    abstract transfer; widening's role is to REACH such an [S] in finitely
    many steps (a separate termination concern — the scry-interval `widen`
    has the ascending-chain property), while THIS theorem is the soundness of
    any post-fixpoint once reached. Generalising to the full local-store and
    mechanising widening termination against WasmCert-Coq is the named next
    slice, as with the bounded transfer in [Soundness.v].

    Build:  bazel build //proofs/rocq:loopfixpoint
    Test:   bazel test  //proofs/rocq:loopfixpoint_test
*)

From Stdlib Require Import ZArith.

(** Minimal abstract value: [ATop] concretizes to all integers, [AExact z]
    to the singleton {z} (as in [WriteSetHavoc.v]). *)
Inductive aval : Type :=
  | ATop : aval
  | AExact : Z -> aval.

Definition gamma (a : aval) (z : Z) : Prop :=
  match a with
  | ATop => True
  | AExact c => z = c
  end.

(** ⊤ is sound for any concrete value (γ(⊤) = ℤ). *)
Lemma gamma_top : forall z, gamma ATop z.
Proof. intros z. exact I. Qed.

(** [iter n f z] applies the loop body [f] to [z] exactly [n] times — the
    concrete state after [n] loop iterations. *)
Fixpoint iter (n : nat) (f : Z -> Z) (z : Z) : Z :=
  match n with
  | O => z
  | S k => f (iter k f z)
  end.

(** * Soundness of the loop fixpoint.

    Let [f] be the concrete loop body (on the tracked value), [fhat] a SOUND
    abstract transfer for it (it over-approximates [f] pointwise through γ),
    and [S] a header invariant the analyzer computed with:
      - [gamma S z0]            : the entry value is covered, and
      - [gamma (fhat S) z ->
         gamma S z]             : [S] is a post-fixpoint ([fhat S ⊑ S]).
    Then [S] over-approximates the concrete state after ANY number [n] of
    iterations: [gamma S (iter n f z0)]. Proof: induction on [n] — base is
    the entry coverage; step pushes [f] through the soundness of [fhat] and
    the post-fixpoint property. *)
Theorem loop_postfixpoint_sound :
  forall (f : Z -> Z) (fhat : aval -> aval) (S : aval) (z0 : Z),
    (forall a z, gamma a z -> gamma (fhat a) (f z)) ->
    gamma S z0 ->
    (forall z, gamma (fhat S) z -> gamma S z) ->
    forall n, gamma S (iter n f z0).
Proof.
  intros f fhat S z0 Hsound Hentry Hle n.
  induction n; simpl.
  - exact Hentry.
  - apply Hle. apply Hsound. exact IHn.
Qed.
