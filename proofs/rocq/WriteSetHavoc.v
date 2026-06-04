(** * FEAT-016 slice-1 — Soundness of write-set havoc (Rocq).

    v1.4's interval pass stops scrubbing every local to ⊤ on control flow.
    A structured-control region (block / loop / if) is modelled by WRITE-SET
    HAVOC: the analyzer widens exactly the locals the region writes
    ([local.set] / [local.tee] — the ONLY operators that write a Wasm local,
    so the static scan [region_write_set] captures every written index) to ⊤,
    and keeps every other local's precise pre-region abstraction. See
    [run_function_body] in [crates/scry-analyze-core/src/lib.rs].

    This file mechanizes the soundness obligation that move incurs, in the
    same Cousot over-approximation sense as [Soundness.v] (AC-001): the
    havocked abstract post-state OVER-APPROXIMATES every concrete post-state
    of the region. The key theorem [havoc_sound] holds for ANY concrete
    post-state that changes only locals in the write set — which includes the
    state after any number of loop iterations, since each iteration writes
    only within the set. No admits, no axioms (the proof-in-slice gate).

    Scope / honesty (for the assessor): the concrete "region execution" is
    abstracted to its NET EFFECT on the local store — "every local outside
    the write set is unchanged". That this models real Wasm structured
    control is exactly the [local.set]/[local.tee]-are-the-only-writers fact
    above; mechanizing it against the WasmCert-Coq operational semantics
    (proving region execution preserves locals outside its lexical
    [local.set]/[local.tee] set) is the named next slice, as with the
    wrap-aware bounded transfer in [Soundness.v].

    Build:  bazel build //proofs/rocq:writesethavoc
    Test:   bazel test  //proofs/rocq:writesethavoc_test
*)

From Stdlib Require Import ZArith.

(** Minimal abstract value: [ATop] concretizes to all integers, [AExact z]
    to the singleton {z}. Enough to state write-set havoc, whose only
    abstract action is to set written locals to ⊤. *)
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

(** A local store has an abstract part ([nat -> aval]) and a concrete part
    ([nat -> Z]). [sound sigma rho] is the pointwise γ-soundness the analyzer
    maintains: every concrete local lies in the concretization of its
    abstract. *)
Definition sound (sigma : nat -> aval) (rho : nat -> Z) : Prop :=
  forall l, gamma (sigma l) (rho l).

(** Write-set havoc: widen exactly the written locals ([W l = true]) to ⊤;
    keep every other local's abstract value. This is [region_write_set] plus
    the per-index assignment to ⊤ in [run_function_body]. [W] is the write
    set as a characteristic predicate. *)
Definition havoc (sigma : nat -> aval) (W : nat -> bool) (l : nat) : aval :=
  if W l then ATop else sigma l.

(** * Soundness of write-set havoc.

    If [sigma] over-approximates the pre-state [rho], and the region's
    concrete execution changes ONLY locals in the write set [W] (every local
    outside [W] is unchanged), then [havoc sigma W] over-approximates the
    concrete post-state [rho']. Holds for every such [rho'] — in particular
    the post-state after any number of loop iterations. *)
Theorem havoc_sound :
  forall (sigma : nat -> aval) (rho rho' : nat -> Z) (W : nat -> bool),
    sound sigma rho ->
    (forall l, W l = false -> rho' l = rho l) ->
    sound (havoc sigma W) rho'.
Proof.
  intros sigma rho rho' W Hpre Hwrites.
  unfold sound in *. intro l.
  unfold havoc.
  destruct (W l) eqn:E.
  - apply gamma_top.
  - rewrite (Hwrites l E). apply Hpre.
Qed.

(** Precision corollary (the FEAT-016 win over the v0.2 scrub-everything
    fallback): a local NOT in the write set keeps its exact pre-region
    abstraction across the region — it is not widened. *)
Lemma havoc_preserves_unwritten :
  forall sigma W l, W l = false -> havoc sigma W l = sigma l.
Proof. intros sigma W l E. unfold havoc. rewrite E. reflexivity. Qed.
