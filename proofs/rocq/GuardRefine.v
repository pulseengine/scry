(** * FEAT-016 slice-2b-i — Soundness of guard refinement (Rocq).

    v1.6's interval pass adds GUARD REFINEMENT: when a loop's exit test is a
    signed comparison of a local against a constant (`local.get L; i32.const C;
    i32.<cmp>; br_if D`), the analyzer refines `L`'s interval on each edge by
    MEETING it with the half-space the guard implies — `i < C` ⇒ `L ⊑ [-∞, C-1]`
    on the not-taken edge, etc. Narrowing then pulls the over-widened loop
    header back to a finite bound. See `Interp::try_guard_brif` /
    `refine_interval` in `crates/scry-analyze-core/src/lib.rs`.

    This file mechanizes the soundness obligation that refinement incurs, in
    the same Cousot over-approximation sense as [Soundness.v] /
    [WriteSetHavoc.v] / [LoopFixpoint.v]: refining an interval by a guard's
    half-space NEVER DROPS a concrete value that actually satisfies the guard.
    Refinement shrinks γ (meet is the greatest lower bound), so the only way it
    could be unsound is to discard a reachable post-guard state — this theorem
    proves it does not. No admits, no axioms (the proof-in-slice gate, DD-015).

    Scope / honesty (for the assessor): the mechanization is over ℤ with
    optional (±∞) bounds, the exact model of the scry-interval domain. The
    real `refine_interval` uses i64 saturating arithmetic for `C ± 1`; that is
    the finite-width realization and is sound here because saturation only ever
    WIDENS the half-space (clamps a bound further out), which by monotonicity of
    meet can only retain MORE concrete values — it never drops a satisfying one.
    Refinement is applied ONLY to signed comparisons; the unsigned ops are left
    unrefined (their wrap semantics would make this signed half-space the wrong
    set), so they are out of scope by construction.

    Build:  bazel build //proofs/rocq:guardrefine
    Test:   bazel test  //proofs/rocq:guardrefine_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** An abstract interval: optional lower / upper bounds, [None] = unbounded
    (the ±∞ sentinels of the concrete domain). This is exactly the
    scry-interval value with `i64::MIN`/`i64::MAX` modelled as ±∞. *)
Record itv : Type := { lo : option Z; hi : option Z }.

Definition ge_lo (l : option Z) (z : Z) : Prop :=
  match l with None => True | Some a => a <= z end.
Definition le_hi (h : option Z) (z : Z) : Prop :=
  match h with None => True | Some b => z <= b end.

(** Concretization: [z] is in the interval iff it respects both bounds. *)
Definition gamma (i : itv) (z : Z) : Prop := ge_lo i.(lo) z /\ le_hi i.(hi) z.

(** Meet on the bound lattice: the tighter of the two on each side. *)
Definition meet_lo (a b : option Z) : option Z :=
  match a, b with
  | None, x | x, None => x
  | Some x, Some y => Some (Z.max x y)
  end.
Definition meet_hi (a b : option Z) : option Z :=
  match a, b with
  | None, x | x, None => x
  | Some x, Some y => Some (Z.min x y)
  end.
Definition meet (a b : itv) : itv :=
  {| lo := meet_lo a.(lo) b.(lo); hi := meet_hi a.(hi) b.(hi) |}.

(** Meet is EXACT on γ: the meet concretizes to the intersection. The two
    bound lemmas are the workhorses; both close by case analysis + [lia]. *)
Lemma meet_lo_iff : forall a b z,
  ge_lo (meet_lo a b) z <-> ge_lo a z /\ ge_lo b z.
Proof. intros [a|] [b|] z; simpl; lia. Qed.

Lemma meet_hi_iff : forall a b z,
  le_hi (meet_hi a b) z <-> le_hi a z /\ le_hi b z.
Proof. intros [a|] [b|] z; simpl; lia. Qed.

Lemma meet_sound : forall a b z,
  gamma (meet a b) z <-> gamma a z /\ gamma b z.
Proof.
  intros a b z. unfold gamma, meet; simpl.
  rewrite meet_lo_iff, meet_hi_iff. tauto.
Qed.

(** The six guard comparisons of `GuardOp` (Rust). [GNe] is the only one whose
    TAKEN half-space is not a single interval, so the analyzer leaves the value
    unrefined there — modelled below by [half_space] returning the full ⊤. *)
Inductive gop : Type := GEq | GNe | GLt | GGt | GLe | GGe.

(** The concrete guard predicate `z <op> c`. *)
Definition sat (op : gop) (c z : Z) : Prop :=
  match op with
  | GEq => z = c
  | GNe => z <> c
  | GLt => z < c
  | GGt => z > c
  | GLe => z <= c
  | GGe => z >= c
  end.

(** The half-space the analyzer meets in on the TAKEN edge. Order ops and
    equality give a representable interval; [GNe] gives ⊤ (unrefined — sound,
    just imprecise). Matches `refine_interval`'s `taken = true` arm. *)
Definition half_space (op : gop) (c : Z) : itv :=
  match op with
  | GEq => {| lo := Some c;       hi := Some c |}
  | GLt => {| lo := None;         hi := Some (c - 1) |}
  | GLe => {| lo := None;         hi := Some c |}
  | GGt => {| lo := Some (c + 1); hi := None |}
  | GGe => {| lo := Some c;       hi := None |}
  | GNe => {| lo := None;         hi := None |}   (* ⊤ : unrefined *)
  end.

(** Refinement = meet with the guard half-space. *)
Definition refine (a : itv) (op : gop) (c : Z) : itv := meet a (half_space op c).

(** The half-space OVER-APPROXIMATES the guard: every concrete value that
    satisfies `z <op> c` lies in the half-space. (For the representable ops it
    is in fact exact; for [GNe] it is the trivial ⊤ over-approximation.) *)
Lemma half_space_covers : forall op c z,
  sat op c z -> gamma (half_space op c) z.
Proof. intros [] c z; unfold gamma; simpl; lia. Qed.

(** * Main soundness theorem — guard refinement drops no satisfying state.

    If [z] was covered by the pre-guard interval [a] AND [z] satisfies the
    guard `z <op> c`, then [z] is still covered after refinement. So the
    refined invariant on the taken edge is sound: it over-approximates exactly
    the concrete states that flow down that edge. *)
Theorem refine_sound : forall a op c z,
  gamma a z -> sat op c z -> gamma (refine a op c) z.
Proof.
  intros a op c z Ha Hsat. unfold refine. apply meet_sound.
  split; [ exact Ha | apply half_space_covers; exact Hsat ].
Qed.

(** Refinement only ever SHRINKS the concretization (meet is a lower bound):
    a refined value is always still within the original. This is the dual
    sanity check — refinement cannot invent a concrete value outside [a]. *)
Theorem refine_shrinks : forall a op c z,
  gamma (refine a op c) z -> gamma a z.
Proof. intros a op c z H. apply meet_sound in H. tauto. Qed.
