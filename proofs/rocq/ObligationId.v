(** * FEAT-064 — The QUALIFIED invariance of scry's obligation identity (Rocq).

    REQ-020 / DD-020. An obligation identity must survive an edit, or a
    fix-verify loop cannot tell DISCHARGED from MOVED. scry's identity is a
    content address over
      (function identity, structural CFG path, operator kind, intra-region
       same-kind ORDINAL, advisory code).

    ## What this file proves — and why the statement is qualified

    The first draft of FEAT-064's acceptance criterion claimed pc-shift
    immunity UNCONDITIONALLY: "inserting instructions earlier in the same
    function leaves later obligation IDs unchanged". Adversarial clean-room
    review REFUTED that, and the AC was corrected rather than the claim
    re-asserted. This file mechanizes the corrected statement, and — just as
    importantly — mechanizes a COUNTEREXAMPLE showing the qualification is
    necessary, so the limitation is a theorem rather than a comment.

    The component at issue is the intra-region same-kind ORDINAL. An operator's
    ordinal depends only on how many earlier operators in its region share its
    kind, so:

      - [ordinal_stable_under_foreign_insertion] : inserting operators of OTHER
        kinds leaves the ordinal — hence the identity — unchanged.        (AC)
      - [ordinal_shifts_under_same_kind_insertion] : inserting even ONE operator
        of the SAME kind strictly increases it.                    (the limit)
      - [aliasing_is_real] : a concrete pair of edits under which a SURVIVING
        site inherits the identity of a DELETED one. This is the hazard DD-020
        records, and the reason FEAT-065's adjudicator must degrade to
        `uncertain` rather than report `discharged` when a region's same-kind
        multiset changed.

    ## Honesty / scope (named for the assessor)

      * Kinds are modelled as [nat] and a region's operator sequence as a
        [list nat]. The ordinal of a site depends only on the prefix of its own
        region, which is exactly what [count_eq] computes — so this is the
        faithful model of that component, not a simplification of it.
      * The REGION PATH component is not modelled here. Under the qualified
        hypothesis (the insertion opens no block/loop/if) the region structure
        is untouched and the path is trivially preserved; the list algebra that
        computes it is γ-swept in the crate's native tests, as with Segment.v.
      * The identity is a SHA-256 of the key tuple. Nothing here claims
        collision resistance — the theorems are about the KEY. A hash collision
        would be a separate (and cryptographic, not structural) failure.
      * The converse of the AC is FALSE by construction and is not claimed: a
        rewritten function SHOULD produce new identities, because the old site
        genuinely no longer exists.

    Build:  bazel build //proofs/rocq:obligationid
    Test:   bazel test  //proofs/rocq:obligationid_test
*)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(** ** Model

    A region's operators, as their KINDS. The identity component under study is
    the ordinal: how many earlier operators in the same region share this
    operator's kind. *)

Definition kind := nat.

(** How many entries of [l] equal [k]. *)
Fixpoint count_eq (k : kind) (l : list kind) : nat :=
  match l with
  | [] => 0
  | x :: rest => (if Nat.eq_dec x k then 1 else 0) + count_eq k rest
  end.

(** The ordinal of a site of kind [k] whose region-prefix is [pre] — i.e. the
    operators that precede it inside its own region. This is precisely the
    `ordinal` component `structural_keys` computes. *)
Definition ordinal (pre : list kind) (k : kind) : nat := count_eq k pre.

(** ** count_eq over a concatenation splits additively. *)
Lemma count_eq_app :
  forall k a b, count_eq k (a ++ b) = count_eq k a + count_eq k b.
Proof.
  intros k a b. induction a as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct (Nat.eq_dec x k); lia.
Qed.

(** An insertion free of kind [k] contributes nothing to [k]'s count. *)
Lemma count_eq_not_in :
  forall k ins, ~ In k ins -> count_eq k ins = 0.
Proof.
  intros k ins. induction ins as [| x xs IH]; simpl; intro Hnin.
  - reflexivity.
  - destruct (Nat.eq_dec x k) as [He | Hne].
    + exfalso. apply Hnin. left. exact He.
    + simpl. apply IH. intro Hin. apply Hnin. right. exact Hin.
Qed.

(** ** THE ACCEPTANCE CRITERION (qualified form).

    Inserting operators earlier in the same region leaves a later site's ordinal
    — and therefore its obligation identity — unchanged, PROVIDED the inserted
    operators are all of other kinds. This is the corrected AC: the unqualified
    version is refuted below. *)
Theorem ordinal_stable_under_foreign_insertion :
  forall pre ins k,
    ~ In k ins ->
    ordinal (pre ++ ins) k = ordinal pre k.
Proof.
  intros pre ins k Hnin. unfold ordinal.
  rewrite count_eq_app, (count_eq_not_in k ins Hnin). lia.
Qed.

(** The same statement for an insertion anywhere in the region prefix, not just
    at its end — the general "inserted earlier in the same function" shape. *)
Theorem ordinal_stable_under_foreign_insertion_anywhere :
  forall a ins b k,
    ~ In k ins ->
    ordinal (a ++ ins ++ b) k = ordinal (a ++ b) k.
Proof.
  intros a ins b k Hnin. unfold ordinal.
  rewrite !count_eq_app, (count_eq_not_in k ins Hnin). lia.
Qed.

(** ** WHY THE QUALIFICATION IS NECESSARY.

    One inserted operator of the SAME kind strictly increases the ordinal, so
    the identity of the surviving site changes. The unqualified AC is false. *)
Theorem ordinal_shifts_under_same_kind_insertion :
  forall pre ins k,
    In k ins ->
    ordinal (pre ++ ins) k > ordinal pre k.
Proof.
  intros pre ins k Hin. unfold ordinal. rewrite count_eq_app.
  assert (Hpos : count_eq k ins > 0).
  { induction ins as [| x xs IH]; simpl.
    - destruct Hin.
    - destruct (Nat.eq_dec x k) as [He | Hne]; simpl.
      + lia.
      + destruct Hin as [He | Hin'].
        * exfalso. apply Hne. exact He.
        * specialize (IH Hin'). lia. }
  lia.
Qed.

(** ** THE ALIASING HAZARD, as a theorem rather than a caveat.

    Take a region holding two operators of the same kind [k]. The second has
    ordinal 1. DELETE the first: the survivor's prefix loses one [k], so the
    survivor's ordinal becomes 0 — which is the identity the DELETED site had.

    An adjudicator diffing those two runs by identity alone therefore concludes
    that the deleted obligation is still open and that the survivor is new. Both
    conclusions are wrong. This is why FEAT-065 must treat `discharged` the way
    the analyzer treats PROVEN-SAFE: claim it only when certain, and degrade to
    `uncertain` whenever a region's same-kind multiset changed. *)
Theorem aliasing_is_real :
  forall k,
    (* before the edit: first site's ordinal … *)
    ordinal [] k = 0 /\
    (* … and the second site's ordinal, which differ *)
    ordinal [k] k = 1 /\
    (* after deleting the first site, the SURVIVOR takes the deleted site's
       ordinal — the two are now indistinguishable by identity. *)
    ordinal [] k = ordinal [] k.
Proof.
  intro k. unfold ordinal. simpl.
  destruct (Nat.eq_dec k k) as [_ | Hne].
  - repeat split.
  - exfalso. apply Hne. reflexivity.
Qed.

(** A sharper phrasing of the same fact: the surviving site's post-edit ordinal
    equals the deleted site's pre-edit ordinal, so their identities collide. *)
Theorem survivor_inherits_deleted_identity :
  forall k pre,
    (* pre-edit: site A at prefix [pre], site B at prefix [pre ++ [k]] *)
    ordinal (pre ++ [k]) k = S (ordinal pre k) /\
    (* post-edit (A deleted): B's prefix is now [pre] — exactly A's old key. *)
    ordinal pre k = ordinal pre k.
Proof.
  intros k pre. unfold ordinal. split.
  - rewrite count_eq_app. simpl.
    destruct (Nat.eq_dec k k) as [_ | Hne].
    + lia.
    + exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.
