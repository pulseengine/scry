(** * FEAT-049 — Soundness of the affine handle-state lattice (Rocq).

    v3.0 adds the Component-Model handle-state domain in `crates/scry-handle`
    (MF-007): an affine lattice over a resource handle's status — `Alive` or
    `Dropped` concretely, with `Top` for a control-flow merge of the two. The
    analyzer's straight-line handle pass runs these transitions to detect
    use-after-drop / double-drop.

    This file mechanizes the lattice + transition soundness over the two-element
    concrete status set:

      * [join_sound]  — `γ(a) ∪ γ(b) ⊆ γ(a ⊔ b)`.
      * [leq_sound]   — `a ⊑ b ⟹ γ(a) ⊆ γ(b)`.
      * [after_drop_sound] — after a drop the state is `Dropped` (γ = {dropped}),
        and the double-drop flag fires exactly when the pre-state could already
        be dropped.
      * [uad_sound] — a use is flagged a DEFINITE use-after-drop only when the
        state is `Dropped` (γ = {dropped}); so a state admitting `alive` is never
        flagged — no false definite report on correct owned/borrowed code.

    No admits, no axioms (the DD-015 proof-in-slice gate).

    Build:  bazel build //proofs/rocq:handle
    Test:   bazel test  //proofs/rocq:handle_test
*)

(** Concrete handle status. *)
Inductive Concrete := Alive | Dropped.

(** Abstract handle state (mirrors the Rust `HandleState`). *)
Inductive HState := Bottom | AAlive | ADropped | Top.

Definition contains (s : HState) (c : Concrete) : Prop :=
  match s, c with
  | Bottom, _ => False
  | AAlive, Alive => True
  | AAlive, Dropped => False
  | ADropped, Dropped => True
  | ADropped, Alive => False
  | Top, _ => True
  end.

Definition join (a b : HState) : HState :=
  match a, b with
  | Bottom, x => x
  | x, Bottom => x
  | AAlive, AAlive => AAlive
  | ADropped, ADropped => ADropped
  | _, _ => Top
  end.

Definition leq (a b : HState) : Prop :=
  match a, b with
  | Bottom, _ => True
  | _, Top => True
  | AAlive, AAlive => True
  | ADropped, ADropped => True
  | _, _ => False
  end.

(** Drop transition: resulting state is always [ADropped]; the boolean is the
    double-drop flag (pre-state may already be dropped). *)
Definition after_drop (s : HState) : HState * bool :=
  (ADropped, match s with ADropped | Top => true | _ => false end).

Definition use_is_after_drop (s : HState) : bool :=
  match s with ADropped => true | _ => false end.

(** * Join over-approximates each operand. *)
Theorem join_sound : forall a b c,
  contains a c \/ contains b c -> contains (join a b) c.
Proof.
  intros a b c H.
  destruct a, b, c; simpl in *; tauto.
Qed.

(** * The order is sound. *)
Theorem leq_sound : forall a b c,
  leq a b -> contains a c -> contains b c.
Proof.
  intros a b c Hle Hc.
  destruct a, b, c; simpl in *; tauto.
Qed.

(** * After a drop the state denotes exactly {dropped}. *)
Theorem after_drop_state : forall s,
  fst (after_drop s) = ADropped.
Proof. intro s; destruct s; reflexivity. Qed.

Theorem after_drop_gamma : forall s c,
  contains (fst (after_drop s)) c -> c = Dropped.
Proof. intros s c; rewrite after_drop_state; destruct c; simpl; tauto. Qed.

(** The double-drop flag fires exactly when the pre-state can be dropped. *)
Theorem double_drop_iff : forall s,
  snd (after_drop s) = true <-> contains s Dropped.
Proof. intro s; destruct s; simpl; intuition (try discriminate). Qed.

(** * A use is flagged a DEFINITE use-after-drop only for a state whose γ is
      exactly {dropped}; in particular a state admitting [Alive] is never
      flagged, so correct owned/borrowed code raises no false definite. *)
Theorem uad_sound : forall s,
  use_is_after_drop s = true -> (forall c, contains s c -> c = Dropped).
Proof.
  intros s H c Hc. destruct s; simpl in *; try discriminate.
  destruct c; simpl in Hc; tauto.
Qed.

Theorem uad_not_flagged_when_alive_possible : forall s,
  contains s Alive -> use_is_after_drop s = false.
Proof. intro s; destruct s; simpl; tauto || reflexivity. Qed.
