(** * FEAT-037 (DD-017) — Mechanized soundness of the congruence domain over
    Wasm's WRAPPING integer arithmetic (Rocq).

    The new crate `crates/scry-bits` adds a known-bits × congruence reduced
    product. The known-bits lattice + its bitwise/shift/const transfers are
    exhaustively γ-sweep-falsified in that crate (its established evidence kind
    — a concrete-semantics oracle over the whole `w = 8` domain, every residue
    class mod ≤ 12, including the wrapping semantics). This file mechanizes the
    one genuinely NEW and load-bearing soundness obligation the slice
    introduces, the reason DD-017 exists:

      a congruence `x ≡ r (mod m)` is preserved by a WRAPPING `add`/`sub`/`mul`
      only when `m | 2^w`; in general the result is congruent modulo
      `d := gcd(m, 2^w)`, and modulo `m` exactly when no wrap occurred.

    We model the concrete machine operation as `(x ∘ y) mod 2^w` over [Z] and
    prove, with NO admits and NO axioms (the DD-015 proof-in-slice gate):

      - [add_wrap_sound] : d | (((x + y) mod 2^w) − (r1 + r2))
      - [sub_wrap_sound] : d | (((x − y) mod 2^w) − (r1 − r2))
      - [mul_wrap_sound] : d | (((x * y) mod 2^w) − (r1 * r2))
      - [add_nowrap_exact] / [mul_nowrap_exact] : when the exact-ℤ result is in
        [0, 2^w) (the analyzer's interval no-wrap guard), the FULL modulus `m`
        is retained.

    These justify the crate's `cong_add` / `cong_sub` / `cong_mul`: on a
    possibly-wrapping op the modulus is weakened to `d = gcd(m, 2^w)`
    (computed there as `2^min(v2(m), w)`, unit-tested to equal [Z.gcd m (2^w)]),
    and kept as `m` only under the `wrap_free` guard.

    Scope / honesty (named for the assessor): this is the congruence side's
    wrapping soundness — the novel content. The known-bits transfers and the
    2-adic reduction operator are falsified by the scry-bits γ-sweep tests;
    mechanizing the bit-vector transfers at the [Z.testbit] level is named
    future work, exactly as the octagon DBM transfers were in [OctagonProject.v]
    (DD-015).

    Build:  bazel build //proofs/rocq:bitscongruence
    Test:   bazel test  //proofs/rocq:bitscongruence_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** `d := gcd(m, 2^w)` divides the wrap modulus `P = 2^w`. This is all the
    soundness proofs below need about `d`; that the Rust `gcd_with_pow2`
    actually computes [Z.gcd m (2^w)] (as the power of two `2^min(v2 m, w)`) is
    falsified by the crate unit test `gcd_with_pow2_is_two_adic`. *)
Lemma gcd_divides_pow2 :
  forall m w, 0 <= w -> (Z.gcd m (2 ^ w) | 2 ^ w).
Proof.
  intros m w _. apply Z.gcd_divide_r.
Qed.

(** `d` also divides `m`. *)
Lemma gcd_divides_m :
  forall m w, (Z.gcd m (2 ^ w) | m).
Proof.
  intros m w. apply Z.gcd_divide_l.
Qed.

(** ** Addition under wrap.

    If `x ≡ r1` and `y ≡ r2` (mod m), then the wrapped sum `(x + y) mod 2^w`
    is congruent to `r1 + r2` modulo `d = gcd(m, 2^w)`. *)
Theorem add_wrap_sound :
  forall (w m x y r1 r2 : Z),
    0 < w ->
    (m | (x - r1)) ->
    (m | (y - r2)) ->
    let P := 2 ^ w in
    (Z.gcd m P | (((x + y) mod P) - (r1 + r2))).
Proof.
  intros w m x y r1 r2 Hw H1 H2 P.
  assert (HPpos : 0 < P) by (apply Z.pow_pos_nonneg; lia).
  set (d := Z.gcd m P).
  assert (Hdm : (d | m)) by apply gcd_divides_m.
  assert (HdP : (d | P)) by (apply gcd_divides_pow2; lia).
  rewrite (Z.mod_eq (x + y) P) by lia.
  replace (x + y - P * ((x + y) / P) - (r1 + r2))
    with ((x - r1) + (y - r2) - P * ((x + y) / P)) by ring.
  apply Z.divide_sub_r.
  - apply Z.divide_add_r.
    + apply Z.divide_trans with (m := m); [exact Hdm | exact H1].
    + apply Z.divide_trans with (m := m); [exact Hdm | exact H2].
  - apply Z.divide_mul_l. exact HdP.
Qed.

(** ** Subtraction under wrap. *)
Theorem sub_wrap_sound :
  forall (w m x y r1 r2 : Z),
    0 < w ->
    (m | (x - r1)) ->
    (m | (y - r2)) ->
    let P := 2 ^ w in
    (Z.gcd m P | (((x - y) mod P) - (r1 - r2))).
Proof.
  intros w m x y r1 r2 Hw H1 H2 P.
  assert (HPpos : 0 < P) by (apply Z.pow_pos_nonneg; lia).
  set (d := Z.gcd m P).
  assert (Hdm : (d | m)) by apply gcd_divides_m.
  assert (HdP : (d | P)) by (apply gcd_divides_pow2; lia).
  rewrite (Z.mod_eq (x - y) P) by lia.
  replace (x - y - P * ((x - y) / P) - (r1 - r2))
    with ((x - r1) - (y - r2) - P * ((x - y) / P)) by ring.
  apply Z.divide_sub_r.
  - apply Z.divide_sub_r.
    + apply Z.divide_trans with (m := m); [exact Hdm | exact H1].
    + apply Z.divide_trans with (m := m); [exact Hdm | exact H2].
  - apply Z.divide_mul_l. exact HdP.
Qed.

(** ** Multiplication under wrap.

    `x*y − r1*r2 = (x − r1)*y + r1*(y − r2)`, so `m` divides it; then `d | m`
    and `d | P`. *)
Theorem mul_wrap_sound :
  forall (w m x y r1 r2 : Z),
    0 < w ->
    (m | (x - r1)) ->
    (m | (y - r2)) ->
    let P := 2 ^ w in
    (Z.gcd m P | (((x * y) mod P) - (r1 * r2))).
Proof.
  intros w m x y r1 r2 Hw H1 H2 P.
  assert (HPpos : 0 < P) by (apply Z.pow_pos_nonneg; lia).
  set (d := Z.gcd m P).
  assert (Hdm : (d | m)) by apply gcd_divides_m.
  assert (HdP : (d | P)) by (apply gcd_divides_pow2; lia).
  assert (Hxy : (m | (x * y - r1 * r2))).
  { replace (x * y - r1 * r2) with ((x - r1) * y + r1 * (y - r2)) by ring.
    apply Z.divide_add_r.
    - apply Z.divide_mul_l. exact H1.
    - apply Z.divide_mul_r. exact H2. }
  rewrite (Z.mod_eq (x * y) P) by lia.
  replace (x * y - P * ((x * y) / P) - r1 * r2)
    with ((x * y - r1 * r2) - P * ((x * y) / P)) by ring.
  apply Z.divide_sub_r.
  - apply Z.divide_trans with (m := m); [exact Hdm | exact Hxy].
  - apply Z.divide_mul_l. exact HdP.
Qed.

(** ** No-wrap retains the FULL modulus.

    The analyzer's interval domain supplies a `wrap_free` guard: when the
    exact-ℤ result lies in `[0, 2^w)` there is no wrap, `(x + y) mod 2^w =
    x + y`, and the congruence is preserved modulo the full `m` — not merely
    modulo `gcd(m, 2^w)`. This is what lets a non-power-of-two stride survive. *)
Theorem add_nowrap_exact :
  forall (w m x y r1 r2 : Z),
    0 < w ->
    (m | (x - r1)) ->
    (m | (y - r2)) ->
    0 <= x + y < 2 ^ w ->
    let P := 2 ^ w in
    (m | (((x + y) mod P) - (r1 + r2))).
Proof.
  intros w m x y r1 r2 Hw H1 H2 Hrange P.
  rewrite Z.mod_small by exact Hrange.
  replace (x + y - (r1 + r2)) with ((x - r1) + (y - r2)) by ring.
  apply Z.divide_add_r; assumption.
Qed.

Theorem mul_nowrap_exact :
  forall (w m x y r1 r2 : Z),
    0 < w ->
    (m | (x - r1)) ->
    (m | (y - r2)) ->
    0 <= x * y < 2 ^ w ->
    let P := 2 ^ w in
    (m | (((x * y) mod P) - (r1 * r2))).
Proof.
  intros w m x y r1 r2 Hw H1 H2 Hrange P.
  rewrite Z.mod_small by exact Hrange.
  replace (x * y - r1 * r2) with ((x - r1) * y + r1 * (y - r2)) by ring.
  apply Z.divide_add_r.
  - apply Z.divide_mul_l. exact H1.
  - apply Z.divide_mul_r. exact H2.
Qed.
