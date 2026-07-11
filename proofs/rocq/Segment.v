(** * FEAT-058 — Soundness of scry's linear-memory segmentation domain (Rocq).

    DD-018 / REQ-019. scry-sai-segment abstracts one linear-memory region as an
    ordered list of segments [lo,hi) carrying interval content, so a memory is
    tracked per-segment instead of as one havoc'd ⊤ blob. That list is a finite
    *representation* of a CONSTRAINT FUNCTION [c : offset -> option interval],
    where [None] means "unconstrained" (⊤) at that offset. This file mechanizes
    the domain's soundness AT THAT SEMANTIC LEVEL — over-approximation of the
    concrete memory [m : offset -> Z] — for the operations that matter:

      - [ojoin_left] / [ojoin_right] : the per-offset interval join
        over-approximates each operand (the join keystone).
      - [join_c_sound]      : γ(c1) ∪ γ(c2) ⊆ γ(c1 ⊔ c2).
      - [ile_sound]         : the syntactic order implies γ-inclusion.
      - [strong_store_sound]: the STRONG (singleton-offset) update is the sound
        abstract transfer of [m' = m[off ↦ v]], v ∈ γ(val).
      - [weak_store_sound]  : the WEAK (range) update — the soundness keystone
        for imprecise store addresses — over-approximates a write of v ∈ γ(val)
        to ANY address a ∈ [lo,hi).
      - [load_sound]        : a load returns a constraint containing m(off).

    The list-algebra (split/merge/canonicalise) that realises this constraint
    function in Rust is exhaustively γ-swept in the crate's native tests; here we
    prove the underlying transfers sound. Every theorem is discharged by [lia]
    with NO admits and NO axioms (the DD-015 proof-in-slice gate).

    Concrete semantics: mathematical integers Z (matching Soundness.v). The
    segmentation content domain is the same interval domain proven in
    Soundness.v; this file re-states the fragment it needs, self-contained.

    Build:  bazel build //proofs/rocq:segment
    Test:   bazel test  //proofs/rocq:segment_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Open Scope Z_scope.

(** ** Intervals and the per-offset constraint *)

(** An interval [(lo,hi)]; [lo > hi] denotes ⊥ (empty). *)
Definition itv := (Z * Z)%type.

(** Membership in an interval. *)
Definition inb (i : itv) (z : Z) : Prop := fst i <= z /\ z <= snd i.

(** The constraint at one offset: [None] = ⊤ (unconstrained, admits all). *)
Definition constr := option itv.

(** γ at one offset. *)
Definition gin (c : constr) (z : Z) : Prop :=
  match c with
  | None => True
  | Some i => inb i z
  end.

(** ** Per-offset interval join

    [None] (⊤) absorbs; two proper intervals join to their bounding box. *)
Definition ojoin (a b : constr) : constr :=
  match a, b with
  | None, _ => None
  | _, None => None
  | Some (la, ha), Some (lb, hb) => Some (Z.min la lb, Z.max ha hb)
  end.

(** The join over-approximates its left operand. *)
Lemma ojoin_left : forall a b z, gin a z -> gin (ojoin a b) z.
Proof.
  intros [[la ha]|] [[lb hb]|] z H; simpl in *; try exact I.
  unfold inb in *; simpl in *.
  split; [ pose proof (Z.le_min_l la lb) | pose proof (Z.le_max_l ha hb) ]; lia.
Qed.

(** The join over-approximates its right operand. *)
Lemma ojoin_right : forall a b z, gin b z -> gin (ojoin a b) z.
Proof.
  intros [[la ha]|] [[lb hb]|] z H; simpl in *; try exact I.
  unfold inb in *; simpl in *.
  split; [ pose proof (Z.le_min_r la lb) | pose proof (Z.le_max_r ha hb) ]; lia.
Qed.

(** ** The segmentation as a constraint function over offsets *)

Definition seg := Z -> constr.

(** γ of a whole segmentation: every offset's value respects its constraint. *)
Definition gamma_c (c : seg) (m : Z -> Z) : Prop := forall o, gin (c o) (m o).

Definition top_c : seg := fun _ => None.

(** Update a memory at one offset. *)
Definition upd (m : Z -> Z) (a v : Z) : Z -> Z :=
  fun o => if Z.eqb o a then v else m o.

(** Join of two segmentations = per-offset [ojoin]. *)
Definition join_c (c1 c2 : seg) : seg := fun o => ojoin (c1 o) (c2 o).

(** STRONG update: overwrite the single offset [off] with constraint [val]. *)
Definition strong_c (c : seg) (off : Z) (val : constr) : seg :=
  fun o => if Z.eqb o off then val else c o.

(** WEAK update over [lo,hi): join [val] into each covered offset's content. *)
Definition weak_c (c : seg) (lo hi : Z) (val : constr) : seg :=
  fun o => if (lo <=? o) && (o <? hi) then ojoin (c o) val else c o.

(** ** ⊤ admits everything. *)
Theorem top_c_admits_all : forall m, gamma_c top_c m.
Proof. intros m o; exact I. Qed.

(** ** Join over-approximates the union of the operands' γ. *)
Theorem join_c_sound :
  forall c1 c2 m, (gamma_c c1 m \/ gamma_c c2 m) -> gamma_c (join_c c1 c2) m.
Proof.
  intros c1 c2 m [H|H] o; unfold join_c.
  - apply ojoin_left; apply H.
  - apply ojoin_right; apply H.
Qed.

(** ** Syntactic order → γ-inclusion.

    [ilb c1 c2] is the check scry-interval's [leq] performs, lifted to the
    option: anything ⊑ ⊤; a ⊥ constraint ⊑ anything; otherwise bound-wise. *)
Definition ilb (c1 c2 : constr) : bool :=
  match c2 with
  | None => true
  | Some (l2, h2) =>
    match c1 with
    | None => false
    | Some (l1, h1) => (h1 <? l1) || ((l2 <=? l1) && (h1 <=? h2))
    end
  end.

Theorem ile_sound :
  forall c1 c2, ilb c1 c2 = true -> forall z, gin c1 z -> gin c2 z.
Proof.
  intros [[l1 h1]|] [[l2 h2]|] Hle z Hg; simpl in *; try exact I; try discriminate.
  unfold inb in *; simpl in *.
  apply orb_true_iff in Hle; destruct Hle as [Hbot | Hbnd].
  - apply Z.ltb_lt in Hbot; lia.
  - apply andb_true_iff in Hbnd; destruct Hbnd as [Hl Hh].
    apply Z.leb_le in Hl; apply Z.leb_le in Hh; lia.
Qed.

(** ** STRONG store is the sound transfer of [m' = m[off ↦ v]], v ∈ γ(val). *)
Theorem strong_store_sound :
  forall c off val m v,
    gamma_c c m -> gin val v -> gamma_c (strong_c c off val) (upd m off v).
Proof.
  intros c off val m v Hm Hv o.
  unfold strong_c, upd.
  destruct (Z.eqb o off) eqn:E.
  - exact Hv.
  - apply Hm.
Qed.

(** ** WEAK store over-approximates a write of v ∈ γ(val) to ANY a ∈ [lo,hi).

    The soundness keystone (DD-018): when scry cannot pin the store address to a
    single offset, the value at every possibly-touched offset becomes the join
    of its old content and [val] — so the abstract post-state admits both the
    written and the untouched cases. *)
Theorem weak_store_sound :
  forall c lo hi val m a v,
    gamma_c c m -> lo <= a -> a < hi -> gin val v ->
    gamma_c (weak_c c lo hi val) (upd m a v).
Proof.
  intros c lo hi val m a v Hm Hlo Hhi Hv o.
  unfold weak_c, upd.
  destruct (Z.eqb o a) eqn:Eoa.
  - (* o = a: the written offset. o is in [lo,hi), so weak_c joins val. *)
    apply Z.eqb_eq in Eoa; subst o.
    replace ((lo <=? a) && (a <? hi)) with true
      by (symmetry; apply andb_true_iff; split;
          [ apply Z.leb_le; lia | apply Z.ltb_lt; lia ]).
    apply ojoin_right; exact Hv.
  - (* o <> a: value unchanged; joined-or-not, old content still admits it. *)
    destruct ((lo <=? o) && (o <? hi)).
    + apply ojoin_left; apply Hm.
    + apply Hm.
Qed.

(** ** A load returns a constraint containing the concrete value at [off]. *)
Theorem load_sound :
  forall c m off, gamma_c c m -> gin (c off) (m off).
Proof. intros c m off Hm; apply Hm. Qed.
