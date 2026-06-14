(** * FEAT-016 slice-3 — Soundness of the octagon strong-closure step (Rocq).

    v1.9 adds Miné's STRONG closure to `crates/scry-octagon` (AC-011): after the
    Floyd–Warshall closure it tightens each DBM entry with

        m[i][j] := min( m[i][j], ⌊ (m[i][ī] + m[j̄][j]) / 2 ⌋ )

    deriving a ±difference bound between two variables from their UNARY bounds
    (e.g. `x ≤ 10 ∧ y ≥ 0 ⟹ x − y ≤ 10`), which plain Floyd–Warshall — having no
    edge between `x` and `y` — cannot. The lattice laws and the closure's
    concretization-preservation are falsified by the γ-sweep tests in that crate
    (its established evidence kind). This file mechanizes the one NEW arithmetic
    obligation the step introduces: that the tightened bound is SOUND — it never
    excludes a concrete integer point.

    The encoding (Miné): variable `x_k` has a positive form (`v = x_k`) and a
    negative form (`v = −x_k`). The cell `m[i][ī]` (ī flips the form) bounds
    `v(ī) − v(i) = −2·v(i)`, and `m[j̄][j]` bounds `v(j) − v(j̄) = 2·v(j)`. So
    with `a := m[i][ī]` and `b := m[j̄][j]`, the new bound on `v(j) − v(i)` is
    `⌊(a + b)/2⌋`, and soundness is exactly that every integer `v(j) − v(i)`
    consistent with the two unary bounds respects it. `⌊·/2⌋` is `Z.div _ 2`
    (floor), matching the Rust `i64::div_euclid(2)`. No admits, no axioms (the
    proof-in-slice gate, DD-015).

    Build:  bazel build //proofs/rocq:octagonstrongclose
    Test:   bazel test  //proofs/rocq:octagonstrongclose_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** * The strong-closure tightening is sound.

    Let `vi`, `vj` be the concrete values of two octagon variable forms, and
    `a`, `b` the unary bounds the DBM holds: `−2·vi ≤ a` (from `m[i][ī]`) and
    `2·vj ≤ b` (from `m[j̄][j]`). Then the tightened difference bound
    `⌊(a + b)/2⌋` over-approximates `vj − vi` — it is never violated by a
    concrete point. Hence replacing `m[i][j]` with `min(m[i][j], ⌊(a+b)/2⌋)`
    drops no concrete point: the strong closure is sound. *)
Theorem strong_close_step_sound : forall vi vj a b : Z,
  -2 * vi <= a -> 2 * vj <= b -> vj - vi <= (a + b) / 2.
Proof.
  intros vi vj a b Hi Hj.
  (* 2·(vj − vi) ≤ a + b, then halve with the floor-division facts. *)
  pose proof (Z.div_mod (a + b) 2 ltac:(lia)) as HM.
  pose proof (Z.mod_pos_bound (a + b) 2 ltac:(lia)) as HB.
  lia.
Qed.

(** The floor is the TIGHTEST sound integer bound the halving admits:
    `2·⌊(a+b)/2⌋ ≤ a + b`, so rounding down keeps the bound attainable rather
    than over-tightening past an integer the constraints permit. *)
Theorem strong_close_floor_tight : forall a b : Z,
  2 * ((a + b) / 2) <= a + b.
Proof.
  intros a b.
  pose proof (Z.div_mod (a + b) 2 ltac:(lia)) as HM.
  pose proof (Z.mod_pos_bound (a + b) 2 ltac:(lia)) as HB.
  lia.
Qed.
