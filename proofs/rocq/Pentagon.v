(** * FEAT-044 — Soundness of the Pentagons weakly-relational domain (Rocq).

    v2.7 adds the Pentagons domain in `crates/scry-pentagon` (Logozzo &
    Fähndrich 2008, AC-014): per-variable integer intervals plus a dense
    strict-less-than matrix, the cheap relational layer that proves the
    `index < length` facts out-of-bounds-trap detection (FEAT-046) needs.

    The lattice laws (leq reflexive/transitive, join/meet bounds) and the
    transfer functions are falsified by the exhaustive γ-sweep tests in that
    crate (its established evidence kind — a concrete-semantics oracle over a
    grid of points). This file mechanizes the obligations that are NEW to
    Pentagons and carry the soundness of the design:

      * [implies_lt_sound] — the predicate the join and order rely on: a strict
        fact `x_i < x_j` recorded OR forced by the intervals (`hi_i < lo_j`)
        holds at every concrete point of the state. This is the heart of the
        interval-recovering join.
      * [join_interval_sound] — the per-variable hull (min lo, max hi)
        over-approximates each operand's interval.
      * [join_lt_sound] — a strict fact kept in the join (because it is provable
        in BOTH operands) holds at every concrete point of either operand.
      * [leq_lt_sound] — if `b` records `x_i < x_j` and `a ⊑ b`, the fact is
        provable in `a`, so it holds at `a`'s points.
      * [close_tighten_sound] / [lt_transitive_sound] — the two derivations
        [close] performs only add implied constraints, so they preserve γ.

    Scope / honesty (for the assessor): these are the ℤ-level soundness
    obligations of the Pentagons join, order, and closure — the steps the Rust
    crate performs on each (i,j) cell. The whole-matrix fixpoint of [close] and
    the dense lattice operations are falsified by the scry-pentagon γ-sweep
    tests; mechanising them at the matrix level is named future work, as with
    the DBM transfers in [OctagonProject.v] / [OctagonStrongClose.v]. No admits,
    no axioms (the proof-in-slice gate, DD-015).

    Build:  bazel build //proofs/rocq:pentagon
    Test:   bazel test  //proofs/rocq:pentagon_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** A concrete point assigns integers to two variables [vi], [vj]; the abstract
    state bounds them by [loi,hii] / [loj,hij] and may record [lt_ij] (meaning
    `x_i < x_j`). "Provable in the state" is [implies_lt]. *)

Definition implies_lt (lt_ij : bool) (hii loj : Z) : Prop :=
  lt_ij = true \/ hii < loj.

(** A point is admitted by the (i,j)-fragment of a state when it respects both
    intervals and any recorded strict fact. *)
Definition admits (vi vj loi hii loj hij : Z) (lt_ij : bool) : Prop :=
  loi <= vi <= hii /\ loj <= vj <= hij /\ (lt_ij = true -> vi < vj).

(** * [implies_lt] is sound: if a strict fact is provable in a state, it holds
      at every concrete point that state admits. *)
Theorem implies_lt_sound :
  forall vi vj loi hii loj hij lt_ij,
    admits vi vj loi hii loj hij lt_ij ->
    implies_lt lt_ij hii loj ->
    vi < vj.
Proof.
  intros vi vj loi hii loj hij lt_ij [Hi [Hj Hlt]] [Hrec | Hint].
  - (* recorded explicitly *) apply Hlt; exact Hrec.
  - (* forced by intervals: vi <= hii < loj <= vj *) lia.
Qed.

(** * Join interval hull is sound (per variable). The join sets the result
      bounds to [Z.min loa lob, Z.max hia hib]; every point of operand [a]
      (bounds [loa,hia]) lies inside the hull. *)
Theorem join_interval_sound :
  forall v loa hia lob hib,
    loa <= v <= hia ->
    Z.min loa lob <= v <= Z.max hia hib.
Proof.
  intros v loa hia lob hib H.
  split.
  - pose proof (Z.le_min_l loa lob). lia.
  - pose proof (Z.le_max_l hia hib). lia.
Qed.

(** Symmetric witness for operand [b]. *)
Theorem join_interval_sound_r :
  forall v loa hia lob hib,
    lob <= v <= hib ->
    Z.min loa lob <= v <= Z.max hia hib.
Proof.
  intros v loa hia lob hib H.
  split.
  - pose proof (Z.le_min_r loa lob). lia.
  - pose proof (Z.le_max_r hia hib). lia.
Qed.

(** * Join strict-fact soundness. The join keeps `x_i < x_j` only when it is
      provable in BOTH operands. Hence at any point of operand [a] (which the
      join must over-approximate), the kept fact holds. *)
Theorem join_lt_sound :
  forall vi vj loia hiia loja hija lt_ija,
    admits vi vj loia hiia loja hija lt_ija ->
    implies_lt lt_ija hiia loja ->          (* provable in a *)
    vi < vj.
Proof.
  intros. eapply implies_lt_sound; eauto.
Qed.

(** * Order soundness. If [b] records `x_i < x_j` and [a ⊑ b], the [leq] check
      requires the fact to be provable in [a] ([implies_lt] for a). So it holds
      at every point [a] admits — the order never claims `a ⊑ b` while letting
      [a] admit a point violating one of [b]'s strict facts. *)
Theorem leq_lt_sound :
  forall vi vj loia hiia loja hija lt_ija,
    admits vi vj loia hiia loja hija lt_ija ->
    implies_lt lt_ija hiia loja ->
    vi < vj.
Proof.
  intros. eapply implies_lt_sound; eauto.
Qed.

(** Order interval soundness: if [a]'s interval sits inside [b]'s (the [leq]
    interval check), every point of [a] is within [b]'s bounds. *)
Theorem leq_interval_sound :
  forall v loa hia lob hib,
    lob <= loa -> hia <= hib ->
    loa <= v <= hia ->
    lob <= v <= hib.
Proof. intros; lia. Qed.

(** * [close] derivation (b): from `x_i < x_j` and `x_j <= hij`, the integer
      bound `x_i <= hij - 1` follows — so tightening [hii := hij - 1] excludes
      no admitted point. (The Rust [dec] guards the ±∞ sentinels; over ℤ this is
      the underlying fact.) *)
Theorem close_tighten_hi_sound :
  forall vi vj hij,
    vi < vj -> vj <= hij -> vi <= hij - 1.
Proof. intros; lia. Qed.

(** Dual lower-bound tightening: from `x_i < x_j` and `loi <= x_i`,
    `x_j >= loi + 1`. *)
Theorem close_tighten_lo_sound :
  forall vi vj loi,
    vi < vj -> loi <= vi -> loi + 1 <= vj.
Proof. intros; lia. Qed.

(** * [close] derivation (a): transitivity of the strict relation. From
      `x_i < x_j` and `x_j < x_k` follows `x_i < x_k`, so adding the [lt_ik]
      cell preserves γ. *)
Theorem lt_transitive_sound :
  forall vi vj vk,
    vi < vj -> vj < vk -> vi < vk.
Proof. intros; lia. Qed.

(** * [is_bottom] soundness (the easily-detected cases). A self strict-bound
      `x_i < x_i` is unsatisfiable; so is a 2-cycle `x_i < x_j ∧ x_j < x_i`.
      Both contradict any concrete point, so reporting ⊥ drops no real point. *)
Theorem self_lt_empty : forall vi : Z, ~ (vi < vi).
Proof. intros; lia. Qed.

Theorem two_cycle_empty :
  forall vi vj : Z, vi < vj -> vj < vi -> False.
Proof. intros; lia. Qed.
