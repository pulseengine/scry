(** * FEAT-022 slice-1 — Soundness of reachable-from-exports (Rocq).

    scry's `reachable_from_exports` (REQ-011 / SCRY-001) is a BFS over the
    OVER-APPROXIMATED static call graph (`build_static_call_graph` — direct
    calls plus every over-approximated `call_indirect` target) from the export
    + start roots. A downstream consumer (synth's footprint analysis,
    VCR-MEM-001) prunes any function ABSENT from the set, so soundness requires
    the set to be a SUPERSET of the concretely-reachable functions: a reachable
    function must never be omitted.

    This file mechanizes exactly that: if the concrete call edge relation is a
    SUBSET of the abstract one scry searches (the over-approximation contract),
    then every concretely-reachable node is abstractly-reachable. Hence the
    reported set ⊇ the true reachable set, and pruning its complement is sound.
    No admits, no axioms (the proof-in-slice gate).

    Scope: this is the graph-reachability monotonicity that makes the
    over-approximation safe; that scry's `static_callees` actually
    over-approximates concrete control flow is the FEAT-006 call-graph property
    (its own soundness tag + tests), as cited by REQ-011.

    Build:  bazel build //proofs/rocq:reachable
    Test:   bazel test  //proofs/rocq:reachable_test
*)

Section Reachable.

(** Nodes are function indices. [cedge]/[aedge] are the concrete and abstract
    (analyzer) call-edge relations; [is_root] marks the export/start entry
    points. The over-approximation contract: every concrete edge is an abstract
    edge. *)
Variable node : Type.
Variable cedge : node -> node -> Prop.
Variable aedge : node -> node -> Prop.
Variable is_root : node -> Prop.

Hypothesis edge_over_approx : forall x y, cedge x y -> aedge x y.

(** Reachability over an edge relation [E] from the roots: a root is reachable,
    and an edge from a reachable node reaches its target. *)
Inductive reach (E : node -> node -> Prop) : node -> Prop :=
  | reach_root : forall r, is_root r -> reach E r
  | reach_step : forall x y, reach E x -> E x y -> reach E y.

(** * Soundness: the abstract reachable set is a SUPERSET of the concrete one.

    Every concretely-reachable node is abstractly-reachable. So scry's
    `reachable_from_exports` (= abstract reach) contains every truly-reachable
    function; a consumer that prunes the complement never drops a reachable
    function. *)
Theorem reach_superset :
  forall x, reach cedge x -> reach aedge x.
Proof.
  intros x H. induction H as [r Hr | x y Hcx IH Hxy].
  - apply reach_root. exact Hr.
  - eapply reach_step.
    + exact IH.
    + apply edge_over_approx. exact Hxy.
Qed.

(** Contrapositive, in the form the consumer relies on: a node that is NOT in
    the abstract reachable set is NOT concretely reachable — so pruning it is
    sound. *)
Corollary absent_is_unreachable :
  forall x, ~ reach aedge x -> ~ reach cedge x.
Proof.
  intros x Hna Hc. apply Hna. apply reach_superset. exact Hc.
Qed.

End Reachable.
