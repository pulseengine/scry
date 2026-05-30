---
id: DOC-CREDIT-DOSSIER-V1
type: spec
status: draft
title: scry six-domain credit dossier (v1.0)
tags: [dossier, regulatory, do-333, mechanization, v1.0]
references: [FEAT-011, FEAT-010, G-001, G-002, REQ-001, REQ-002, REQ-008, AC-001, MF-001]
---

# scry six-domain credit dossier (v1.0)

This dossier is the v1.0 capstone deliverable of [[FEAT-011]] (AC#3). It
assembles, in one place, the evidence-to-requirement mapping that lets a
safety assessor credit scry's abstract-interpretation analysis under each
of the six target regulatory standards, and it closes the top-level
safety goal [[G-001]] ("the PulseEngine verification chain covers all
three DO-333 technique classes for safety-critical Wasm").

The thesis ([[MF-001]]): DO-333 and the equivalent clauses in the other
five standards name **abstract interpretation** as a distinct
formal-methods technique class alongside deductive proof and model
checking. A verification chain that staffs only testing + model checking
+ deductive proof leaves that class unstaffed. scry staffs it, with
runnable, version-pinned, and — as of v0.9/v1.0 — *mechanically proven*
evidence.

## What changed at v1.0

The dossier is creditable now because the soundness story crossed from
*asserted* to *mechanized*:

- **v0.9 ([[FEAT-010]]):** first Rocq soundness theorem for the interval
  domain (`proofs/rocq/Soundness.v`, γ-soundness of bottom / constant /
  `⊑` / join / meet / `add`, 0 admits).
- **v1.0 ([[FEAT-011]]) AC#1:** the proof extends to the full shipped
  domain stack — region-memory (`Region.v`), call-graph resolution
  (`CallGraph.v`), and the reachability lattice (`Reachability.v`), each
  0 admits, 0 axioms. `bazel test //proofs/rocq:...` is the gate.

Deferred to v1.1 (named, not hidden): the SpecTec→interval-transfer
*soundness-by-construction* backend (FEAT-011 AC#2) and the
WasmCert-Coq-backed wrap-aware bounded `i32.add` proof ([[TE-004]]).

## Evidence kinds

| Kind | Meaning | Strength |
|---|---|---|
| **mechanized** | Rocq theorem, 0 admits/axioms, CI-gated | highest |
| **runnable** | version-pinned artifact + native falsifier in CI | high |
| **contract** | published, validated schema / typed boundary | medium |
| **paper** | soundness argued in design docs, not yet mechanized | baseline |

## Requirement → evidence map

| REQ | What it requires | Evidence | Kind |
|---|---|---|---|
| [[REQ-001]] | sound AI pass over Wasm Core | interval/region/call-graph analyzer (`//:scry`) + `Soundness.v`/`Region.v`/`CallGraph.v` | mechanized + runnable |
| [[REQ-002]] | soundness stated & (long-term) mechanized vs official semantics | `proofs/rocq/*.v` (interval+region+call-graph+reachability, 0 admits) | mechanized |
| REQ-003 | extend to Component Model | `component-provenance` typed boundary (`SCPV` v1, FEAT-002) + projection | contract |
| REQ-004 | machine-consumable invariants for loom | invariant JSON schema v1 (FEAT-008), bounds-check-elision soundness (`Region.in_bounds_sound`) | contract + mechanized |
| REQ-005 | attestable end-to-end (sigil) + traceable (rivet) | cosign-signed release assets + SLSA provenance + rivet compliance bundle | runnable |
| REQ-006 | reusable independent of the Wasm front-end | pure domain crates (`scry-octagon`/`-taint`/`-provenance`) compile native + wasm | runnable |
| [[REQ-008]] | sound call graphs under `call_indirect` | call-graph resolution (FEAT-006) + `CallGraph.callgraph_resolution_sound` | mechanized + runnable |
| REQ-007 | scale to fused modules | compositional summaries (FEAT-007) | runnable |

## Per-standard credit cross-walk

Each standard names abstract interpretation (or "static analysis by
sound over-approximation") as a creditable technique for the verification
objective in the cited clause. scry's evidence above is the artifact that
discharges it.

| Standard (domain) | Clause crediting abstract interpretation | scry evidence discharging it |
|---|---|---|
| **DO-178C / DO-333** (aerospace) | DO-333 FM.6.3.x — abstract interpretation as a formal method for accuracy/consistency & robustness | mechanized `Soundness.v` stack + runnable `//:scry` |
| **ISO 26262-6** (automotive) | §9 Table 8 — "abstract interpretation" / semantic static analysis (highly recommended ASIL C/D) | mechanized soundness + sound call-graph (`CallGraph.v`) |
| **IEC 61508-3** (industrial) | Annex B Table B.8 — "static analysis" incl. abstract interpretation (HR at SIL 3/4) | runnable analyzer + region bounds-check soundness (`Region.v`) |
| **IEC 62304** (medical) | §5.5 software unit verification — static analysis acceptance criteria | runnable analyzer + invariant contract (FEAT-008) |
| **EN 50128** (railway) | Table A.4/A.19 — "static analysis" / "abstract interpretation" (HR at SIL 3/4) | mechanized soundness + sigil attestation (REQ-005) |
| **ECSS-Q-ST-80C** (space) | software product assurance — formal verification / static analysis | full mechanized stack + SLSA provenance |

> Honest scope: the cross-walk asserts *which clause* each standard
> provides for abstract-interpretation credit and *which scry artifact*
> is offered against it. It is a credit-readiness map for an assessor,
> not a completed certification — formal qualification of the tool
> itself (DO-330 TQL / equivalent) is out of scope for v1.0 and named as
> future work.

## Honest gaps (named, not hidden)

- **Reachability** is lattice-proven (`Reachability.v`) but **not yet
  consumed by analyzer code** — the powerset/dead-code analysis was
  deferred when the v0.4 call-graph slice shipped. The dossier credits
  the lattice algebra, not a shipped reachability transfer.
- The **interval `add` soundness** (`Soundness.v`) models the *no-wrap*
  integer core; the shipped `i32_add` widens to ⊤ on possible 2³² wrap
  (trivially sound, `γ(⊤)=ℤ`). The WasmCert-Coq-backed wrap-aware proof
  is named future work ([[TE-004]]).
- The **SpecTec soundness-by-construction backend** (FEAT-011 AC#2) is
  deferred to v1.1.
- Tool qualification (DO-330 / ISO 26262-8 §11 confidence in software
  tools) is out of scope for v1.0.

## How the dossier is attested

The release pipeline (`.github/workflows/release.yml`) produces the
rivet compliance-evidence tarball and cosign-signs it (keyless OIDC)
alongside the composed `scry.wasm` and per-crate SBOMs. This document is
part of the `docs/` tree captured in that evidence bundle, so the
dossier ships with a verifiable signed digest (REQ-005). The
`rivet matrix` output is the machine-readable companion to the tables
above.

## Safety-case closure

With this dossier and the v0.9/v1.0 mechanized proofs in place:

- [[G-002]] (the abstract-interpretation layer soundly over-approximates
  all reachable behaviors) — its soundness evidence is upgraded from
  *asserted* to *mechanized* by the `proofs/rocq/*.v` stack (evidence
  node Sn-006).
- [[G-001]] (all three DO-333 technique classes staffed) — **closed**:
  abstract interpretation (the scry analyzer + the mechanized soundness
  stack), deductive proof (Verus + Rocq), and model checking (Kani) are
  each staffed with runnable, version-pinned evidence; this dossier
  (evidence node Sn-005) is the assembled per-standard credit map.
