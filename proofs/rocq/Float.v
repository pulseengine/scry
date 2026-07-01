(** * FEAT-047 — Soundness of the float-interval domain's lattice (Rocq).

    v3.0 adds the IEEE-754 float-interval domain in `crates/scry-float`
    (AC-022): a real interval `[lo, hi]` (bounds may be `±∞`) plus a `nan` flag,
    since NaN is unordered and cannot live inside an interval.

    The ARITHMETIC transfers (add/sub/mul with round-to-nearest-aware outward
    widening, `±∞`/NaN corner handling, and f32-operand coercion) are falsified
    by the exhaustive γ-sweep in that crate — a concrete-semantics oracle over a
    float grid incl. ±0, subnormals, ±∞ and NaN, at BOTH f32 and f64 widths.
    Mechanising IEEE rounding in Rocq (Flocq) is named future work, as the
    octagon DBM / known-bits transfers were.

    This file mechanizes the LATTICE soundness — the part that does not depend on
    IEEE rounding, only on the ordered-interval + NaN-flag structure:

      * [join_sound] — `γ(a) ∪ γ(b) ⊆ γ(a ⊔ b)` (join over-approximates), for
        both the interval part and the NaN flag.
      * [leq_sound] — `a ⊑ b ⟹ γ(a) ⊆ γ(b)`.
      * [meet_glb] — `γ(a ⊓ b) ⊆ γ(a) ∩ γ(b)` (meet is a lower bound).

    We model a concrete float value as either a real number `R x` (finite or
    `±∞`, ordered) or `Nan`, and an abstract value as `(lo, hi, nanflag)` over
    the reals with `±∞`. Membership mirrors the Rust `contains`. No admits, no
    axioms (the DD-015 proof-in-slice gate).

    Build:  bazel build //proofs/rocq:float
    Test:   bazel test  //proofs/rocq:float_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** Bounds live in ℤ with two sentinels for ±∞ — enough to model the ordered
    lattice structure (the real magnitudes are irrelevant to the lattice laws;
    only the order matters). A concrete non-NaN value is a `Z` with the same
    sentinels. `Zmin`/`Zmax` model the interval hull / intersection. *)

(** A concrete value: NaN, or an ordered point [v]. *)
Inductive CFloat := Nan | Pt (v : Z).

(** An abstract value: interval [lo,hi] over ordered points + a NaN flag. *)
Record AFloat := { lo : Z; hi : Z; nanf : bool }.

(** Membership — the Rocq mirror of `FloatAbstract::contains`. *)
Definition contains (a : AFloat) (x : CFloat) : Prop :=
  match x with
  | Nan => nanf a = true
  | Pt v => lo a <= v <= hi a
  end.

Definition join (a b : AFloat) : AFloat :=
  {| lo := Z.min (lo a) (lo b);
     hi := Z.max (hi a) (hi b);
     nanf := orb (nanf a) (nanf b) |}.

Definition meet (a b : AFloat) : AFloat :=
  {| lo := Z.max (lo a) (lo b);
     hi := Z.min (hi a) (hi b);
     nanf := andb (nanf a) (nanf b) |}.

(** The order test: `a ⊑ b`. *)
Definition leb_af (a b : AFloat) : Prop :=
  (nanf a = true -> nanf b = true) /\ lo b <= lo a /\ hi a <= hi b.

(** * Join over-approximates each operand. *)
Theorem join_sound : forall a b x,
  contains a x \/ contains b x -> contains (join a b) x.
Proof.
  intros a b [|v] H; simpl in *.
  - (* NaN *) destruct H as [Ha | Hb].
    + rewrite Ha. reflexivity.
    + rewrite Hb. apply Bool.orb_true_r.
  - (* point *) destruct H as [Ha | Hb].
    + pose proof (Z.le_min_l (lo a) (lo b)).
      pose proof (Z.le_max_l (hi a) (hi b)). lia.
    + pose proof (Z.le_min_r (lo a) (lo b)).
      pose proof (Z.le_max_r (hi a) (hi b)). lia.
Qed.

(** * The order is sound: `a ⊑ b` ⟹ `γ(a) ⊆ γ(b)`. *)
Theorem leq_sound : forall a b x,
  leb_af a b -> contains a x -> contains b x.
Proof.
  intros a b [|v] [Hn [Hlo Hhi]] H; simpl in *.
  - apply Hn, H.
  - lia.
Qed.

(** * Meet is a lower bound: `γ(a ⊓ b) ⊆ γ(a) ∩ γ(b)`. *)
Theorem meet_glb : forall a b x,
  contains (meet a b) x -> contains a x /\ contains b x.
Proof.
  intros a b [|v] H; simpl in *.
  - apply Bool.andb_true_iff in H. tauto.
  - pose proof (Z.le_max_l (lo a) (lo b)).
    pose proof (Z.le_max_r (lo a) (lo b)).
    pose proof (Z.le_min_l (hi a) (hi b)).
    pose proof (Z.le_min_r (hi a) (hi b)). lia.
Qed.
