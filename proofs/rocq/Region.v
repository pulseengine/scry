(** * FEAT-011 — Mechanized soundness of scry's region-memory domain (Rocq).

    v1.0 extends the v0.9 interval soundness ([Soundness.v]) to the
    region-based linear-memory domain shipped in v0.3 (FEAT-005). A
    region abstracts a pointer into Wasm linear memory as a pair
    [(region_id, offset)] where [offset] is an interval over the byte
    offset within the region (crates/wasm-lattice/src/lib.rs).

    We prove the two soundness properties the analyzer relies on:

      - [region_offset_sound] : shifting a region pointer by an interval
        over-approximates shifting the concrete address — the soundness
        of the [region-offset] transfer function.
      - [in_bounds_sound]     : if the abstract offset interval is
        proven within [0, size), then EVERY concrete address in the
        region's γ is a valid in-bounds access — the soundness of the
        bounds-check-elision decision (the loom use case, REQ-004).

    All theorems are discharged by [lia] with no admits and no axioms
    (the FEAT-011 AC#1 kill-criterion for this domain).

    Build:  bazel build //proofs/rocq:region
    Test:   bazel test  //proofs/rocq:region_test
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(** ** Region representation (matches the wasm-lattice [region] record).

    A region is [(region_id, lo, hi)] — an opaque region id plus the
    inclusive offset interval [lo, hi]. The concrete object it abstracts
    is a pair [(rid, off)] of a concrete region id and a concrete byte
    offset. *)
Record region := mk_region { rid : Z; rlo : Z; rhi : Z }.

(** γ for regions: the concrete [(crid, coff)] is admitted iff the
    region ids match and the concrete offset lies in the interval. The
    region-id match is what keeps distinct logical buffers from aliasing
    (the v0.3 non-relational-across-region-ids design). *)
Definition gamma_r (r : region) (crid coff : Z) : Prop :=
  crid = rid r /\ rlo r <= coff /\ coff <= rhi r.

(** ** [region-offset]: shift the offset interval by [d_lo, d_hi].

    Mirrors the crate: the region id is preserved, the offset interval
    is added to the delta interval (plain interval add). *)
Definition region_offset (r : region) (d_lo d_hi : Z) : region :=
  mk_region (rid r) (rlo r + d_lo) (rhi r + d_hi).

(** ** Soundness of [region-offset].

    If the concrete address [(crid, coff)] is in γ(r) and the concrete
    shift [d] is within the delta interval [d_lo, d_hi], then the
    shifted concrete address [(crid, coff + d)] is in
    γ(region_offset r d_lo d_hi). I.e. abstract shift over-approximates
    concrete shift. *)
Theorem region_offset_sound :
  forall r crid coff d d_lo d_hi,
    gamma_r r crid coff ->
    d_lo <= d -> d <= d_hi ->
    gamma_r (region_offset r d_lo d_hi) crid (coff + d).
Proof.
  intros r crid coff d d_lo d_hi [Hid [Hlo Hhi]] Hd_lo Hd_hi.
  unfold gamma_r, region_offset. simpl. repeat split; lia.
Qed.

(** ** Bounds-check predicate (the crate's [region_in_bounds]).

    The access [ [rlo, rhi] ] of width [w] fits a region of [size]
    bytes iff [0 <= rlo] and [rhi + w <= size]. (We bound the whole
    interval, not just one address — sound for every concrete offset.) *)
Definition in_bounds (r : region) (w size : Z) : bool :=
  if 0 <=? rlo r then (if rhi r + w <=? size then true else false) else false.

(** ** Soundness of bounds-check elision.

    If [in_bounds r w size = true], then for every concrete offset
    [coff] in γ(r), the access [ [coff, coff + w) ] lies within
    [ [0, size) ] — so eliding the runtime bounds check is sound. This
    is the property loom relies on (REQ-004 / FEAT-008). *)
Theorem in_bounds_sound :
  forall r crid coff w size,
    in_bounds r w size = true ->
    gamma_r r crid coff ->
    0 <= coff /\ coff + w <= size.
Proof.
  intros r crid coff w size Hib [Hid [Hlo Hhi]].
  unfold in_bounds in Hib.
  destruct (0 <=? rlo r) eqn:E1; [| discriminate].
  destruct (rhi r + w <=? size) eqn:E2; [| discriminate].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  split; lia.
Qed.

(** ** Distinct region ids never alias.

    If two concrete addresses are admitted by regions with different
    ids, their concrete region ids differ — so the analyzer never
    silently treats two distinct logical buffers as the same. *)
Theorem distinct_regions_no_alias :
  forall r1 r2 crid1 crid2 coff1 coff2,
    rid r1 <> rid r2 ->
    gamma_r r1 crid1 coff1 ->
    gamma_r r2 crid2 coff2 ->
    crid1 <> crid2.
Proof.
  intros r1 r2 crid1 crid2 coff1 coff2 Hneq [H1 _] [H2 _].
  subst. exact Hneq.
Qed.

Close Scope Z_scope.
