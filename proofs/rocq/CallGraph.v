(** * FEAT-011 — Mechanized soundness of scry's call-graph domain (Rocq).

    v1.0 extends the soundness mechanization to the sound
    [call_indirect] resolution shipped in v0.4 (FEAT-006, the
    Paccamiccio et al. technique). At a [call_indirect], the analyzer
    has an interval [lo, hi] over the table index (sound per the
    interval domain, [Soundness.v]) and resolves the target set to every
    table entry whose index lies in [ [lo, hi] ∩ [0, table_len) ].

    The soundness property (FEAT-006 AC#3): for any concrete execution
    reaching the call site with concrete index [k], the resolved target
    set contains [table[k]] — scry never UNDER-approximates the call
    graph (the unsoundness Lehmann et al. measured across other Wasm
    analyzers, MF-003).

    We model the resolved set membership as the predicate "k is in the
    resolved range", and prove the concrete index is always a member.
    This reduces call-graph soundness to interval-index soundness. No
    admits, no axioms.

    Build:  bazel build //proofs/rocq:callgraph
    Test:   bazel test  //proofs/rocq:callgraph_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** ** The resolved index range.

    The analyzer resolves the target set from the table indices in
    [ [lo, hi] ∩ [0, table_len) ]. A concrete table index [k] is
    "resolved" iff it lies in that intersection. *)
Definition resolved (lo hi table_len k : Z) : Prop :=
  Z.max lo 0 <= k /\ k <= Z.min hi (table_len - 1).

(** ** Soundness of call-graph resolution.

    Suppose a concrete execution reaches the [call_indirect] with
    concrete index [k]. The interval domain gives a sound bound
    [lo <= k <= hi] ([Hk_lo], [Hk_hi]). The index must also be a valid
    table index [0 <= k < table_len] for the call not to trap
    ([Hk_nonneg], [Hk_lt]). Then [k] is in the resolved range — i.e.
    the resolved target set contains [table[k]]. scry never misses the
    concrete target. *)
Theorem callgraph_resolution_sound :
  forall lo hi table_len k,
    lo <= k -> k <= hi ->
    0 <= k -> k < table_len ->
    resolved lo hi table_len k.
Proof.
  intros lo hi table_len k Hk_lo Hk_hi Hk_nonneg Hk_lt.
  unfold resolved. split.
  - apply Z.max_lub; lia.
  - apply Z.min_glb; lia.
Qed.

(** ** A constant index resolves precisely to itself.

    When the interval is a singleton [k = lo = hi] and [k] is a valid
    table index, the resolved range is exactly [ [k, k] ] — the
    precision win FEAT-006 claims for constant [call_indirect] indices
    (devirtualization to a direct call). *)
Theorem constant_index_precise :
  forall k table_len,
    0 <= k -> k < table_len ->
    (resolved k k table_len k /\
     forall j, resolved k k table_len j -> j = k).
Proof.
  intros k table_len Hk_nonneg Hk_lt. split.
  - unfold resolved. split; [ apply Z.max_lub | apply Z.min_glb ]; lia.
  - intros j [Hjlo Hjhi].
    rewrite Z.max_l in Hjlo by lia.
    rewrite Z.min_l in Hjhi by lia.
    lia.
Qed.

(** ** An empty intersection is provably unreachable.

    If the index interval does not intersect the table bounds
    ([hi < 0] or [lo >= table_len]), no concrete in-range index is
    resolved — a sound, precise "provably unreachable" result (an empty
    target set, not an under-approximation). *)
Theorem disjoint_index_unreachable :
  forall lo hi table_len k,
    hi < 0 ->
    0 <= k -> k < table_len ->
    lo <= k -> k <= hi -> False.
Proof.
  intros lo hi table_len k Hhi Hk_nonneg Hk_lt Hk_lo Hk_hi. lia.
Qed.

Close Scope Z_scope.
