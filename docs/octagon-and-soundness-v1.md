---
id: DOC-OCTAGON-SOUNDNESS-V1
type: spec
status: draft
title: scry octagon relational domain + mechanized interval soundness (v0.9)
tags: [domains, octagon, relational, mechanization, rocq, v0.9]
references: [FEAT-010, AC-011, AC-003, AC-001, TE-004, REQ-002, FEAT-012, FEAT-003]
---

# scry octagon relational domain + mechanized interval soundness (v0.9)

This document specifies the two legs of [[FEAT-010]] (v0.9): the octagon
relational abstract domain ([[AC-011]], Miné HOSC 2006) and the first
mechanized Rocq soundness theorem for scry's interval domain
([[AC-003]] / [[TE-004]], reducing to the Cousot framework [[AC-001]]).

## Leg 1 — the octagon relational domain

The octagon domain tracks constraints of the form `±x_i ± x_j ≤ c` over
`dim` variables — the mid-precision relational domain between the
non-relational interval domain and exponential-cost polyhedra. It
composes *with* the interval and region domains (a reduced product); it
does not replace them.

### DBM encoding

The standard Difference-Bound-Matrix encoding (Miné). Each variable
`x_k` has a positive form at index `2k` and a negative form at `2k+1`;
writing `v(2k) = x_k`, `v(2k+1) = -x_k`, the row-major matrix entry
`m[i·n + j]` (with `n = 2·dim`) is an upper bound on `v(j) - v(i)`, and
`s64::MAX` is the `+∞` ("no bound") sentinel. Every octagonal constraint
maps to one or two DBM entries; e.g. `x_a - x_b ≤ c` is `m[2b][2a] = c`.

### Operations (pure `crates/scry-octagon`)

| Op | Meaning | Soundness |
|---|---|---|
| `top(dim)` / `bottom(dim)` | ⊤ (`γ = ℤ^dim`) / ⊥ (`γ = ∅`, negative diagonal) | — |
| `is-bottom` | infeasible? (negative diagonal) | exact |
| `close` | Floyd–Warshall shortest-path closure | preserves γ; never drops a point |
| `leq` | `a ⊑ b` ⇔ `γ(a) ⊆ γ(b)` (on closed `a`) | exact |
| `join` | pointwise max of closed DBMs | over-approximates `γ(a) ∪ γ(b)` |
| `meet` | pointwise min of DBMs | exact intersection |
| `widen` | keep stable bounds, drop growing ones (→∞) | fixpoint termination |
| `add-bound` | tighten with one `v(j)-v(i) ≤ c` | exact |

All arithmetic is saturating and `INF`-absorbing so a bound can never
silently wrap.

### WIT dogfood ([[DD-008]])

The `pulseengine:wasm-lattice/domain` interface gains an `octagon`
record — `{ dim: u32, m: list<s64> }`, variable-length because the DBM
is `(2·dim)²` — plus `octagon-top`/`bottom`/`is-bottom`/`close`/`leq`/
`join`/`meet`/`widen`/`add-bound`. The component delegates each to the
pure `scry-octagon` crate, so the *shipped* relational code is exactly
the code the host harness falsifies natively
(`crates/scry-host-tests/tests/octagon.rs`).

## Leg 2 — mechanized interval-domain soundness (`proofs/rocq/Soundness.v`)

The v0.2 `Lattice.v` proved only the *order laws* (reflexivity,
transitivity of `⊑`). `Soundness.v` proves the **soundness** of the
interval transfer functions in the Cousot sense ([[AC-001]]): they
over-approximate the concrete integer semantics through a concretization
`γ : interval → Z → Prop`, `γ(a) z := lo a ≤ z ≤ hi a`.

| Theorem | Statement |
|---|---|
| `gamma_bottom_empty` | `γ(⊥) = ∅` |
| `constant_sound` | `c ∈ γ(constant c)` |
| `leq_sound` | `a ⊑ b → γ(a) ⊆ γ(b)` (the Galois order) |
| `join_sound` | `γ(a) ∪ γ(b) ⊆ γ(a ⊔ b)` |
| `meet_sound` | `z ∈ γ(a ⊓ b) ↔ z ∈ γ(a) ∧ z ∈ γ(b)` |
| `add_sound` | `za ∈ γ(a) → zb ∈ γ(b) → za+zb ∈ γ(a ⊞ b)` |

`add_sound` is the key result: the soundness of the interval `add`
transfer function — exactly what a sound static analysis of `i32.add` /
`i64.add` (on the no-wrap range) reduces to. Every theorem is discharged
by `lia` with **no admits and no axioms** — the [[FEAT-010]] AC#2
kill-criterion — verified by `bazel test //proofs/rocq:soundness_test`.

### Honest scope (named for the assessor)

The concrete model is mathematical integer addition over `Z`. This is
exactly the semantics of scry's *unbounded* interval add and of
`i32.add`/`i64.add` on the no-wrap sub-range. The shipped `i32_add`
additionally widens to `⊤` when the result could straddle the 2³² wrap
boundary; `⊤` is trivially sound (`γ(⊤) = ℤ`), so the widen branch needs
no separate concrete-wrap proof. Importing the WasmCert-Coq `i32` module
([[TE-004]]) as the concrete model to mechanize the wrap-aware bounded
transfer is the named next [[FEAT-010]] slice; this file is the
admit-free core it extends.

## Deferred (a later FEAT-010 slice)

- The analyzer's **loop-carried relational fixpoint** — maintaining an
  octagon over local pairs across loop iterations (AC#1's "across loop
  iterations"). v0.9 ships the domain + WIT dogfood + native
  falsification; wiring the relational fixpoint into the analyzer's
  two-phase walk is next, mirroring how [[FEAT-008]] shipped the
  contract before the live `analyze()` path.
- Miné's **strong/tight closure** (a precision, not soundness,
  refinement).
- The **WasmCert-Coq-backed** wrap-aware bounded `i32.add` proof.

As with [[FEAT-008]], the live `analyze()` round-trip stays gated by the
wac_compose / wasmtime-45 root-import limitation, so the octagon algebra
is falsified natively rather than via a live component call.
