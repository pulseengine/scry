---
id: DOC-ROADMAP-2.0
type: spec
status: draft
title: scry roadmap to 2.0
tags: [roadmap, planning, v2.0]
references: [FEAT-013, FEAT-014, FEAT-015, FEAT-016, FEAT-017, FEAT-018, FEAT-019, FEAT-020, REQ-009, REQ-010, DD-011, MF-005, TE-008, TE-009, TE-010, G-005]
---

# scry roadmap to 2.0

> Generated 2026-05-30, after the v1.0/v1.0.1 capstone. The typed
> backing for this narrative lives in `artifacts/roadmap-2.0.yaml`
> (FEAT-013..020, REQ-009/010, DD-011, MF-005, TE-008..010, G-005);
> `rivet list --status proposed` shows the forward features.

## Where v1.0 actually left us

scry shipped its entire planned v0.1→v1.0 ladder — interval, region,
call-graph, summaries, the loom contract, the component-provenance
boundary, taint/noninterference, the octagon domain, and a mechanized
Rocq soundness stack that closed safety goal [[G-001]]. That is real and
it is rare: **no commercial sound analyzer offers machine-checked
soundness** (see [[MF-005]]).

But the v1.0 dossier closed the goal on a narrower base than the headline
implies. Three structural gaps, found during the v1.0.1 release tail and
recorded honestly rather than papered over, define the real 2.0 work:

| # | Gap | What is actually true | Why it matters |
|---|---|---|---|
| 1 | **Analyzer ↔ composed-artifact decoupling** | A sentinel edit to `crates/scry-analyzer` produces a byte-identical `//:scry` (4.6 KB — the WASI shim, not the analyzer). | The shipped artifact does not contain the thing the dossier says was verified. |
| 2 | **`analyze()` never executes** | The `wac_compose` / wasmtime-45 root-import limit; all verification is native cargo tests. | "Runnable evidence" is aspirational; the live soundness oracle stays skipped. |
| 3 | **No structural coverage** | The witness MC/DC step has been blocked since v0.1 by gaps 1+2; coverage on the analyzer is 0%. | The third DO-178C/DO-330 evidence kind (structural coverage) is missing. |

Everything in v0.2–v1.0 added *breadth* (more domains, more proofs).
**2.0's honest thesis is depth: make the shipped artifact actually do —
and actually be measured doing — what the dossier claims, then build new
capability on a foundation that is real.**

## The competitive thesis (research-grounded)

A 2026-05-30 deep-research pass over primary vendor sources
([[MF-005]], [[TE-008]], [[TE-009]], [[TE-010]]) sharpened where scry
wins:

- **AbsInt Astrée** ([[TE-001]]) is the reference sound analyzer, but it
  is **C/C++ only** — no public Ada/Rust/Wasm/ML roadmap — and its
  2025 releases (25.04/25.10) *refine existing domains* (dynamic octagon
  packs, symbolic/Boolean-pack precision) rather than adding new domain
  theory. A maturity plateau.
- **Polyspace** ([[TE-009]]) and **Frama-C EVA** ([[TE-010]]) occupy the
  same sound-prover category; **Infer/Pulse is deliberately unsound** and
  is a contrast, not a competitor.
- Every incumbent's soundness is a **vendor design claim** backed by
  audit and qualification kits — **not a machine-checked theorem** against
  a formal language semantics.
- **TrustInSoft added Rust in 2025-11** ([[TE-008]]) — datable proof that
  sound AI is expanding to memory-safe / emerging-target languages.

scry's defensible niche is the intersection no incumbent occupies: **a
sound analyzer for Wasm whose soundness is mechanically proven in Rocq
against WasmCert-Coq** ([[REQ-002]]). Not "more domains" — Astrée has
more and better-tuned domains — but *soundness as a theorem, not a
brochure*. The 2.0 capability track and the qualification dossier
([[FEAT-020]]) are built to defend exactly that.

## How we get there — both gaps, sequenced

Per the chosen scope: the early 2.0 minors fix reality; the later minors
add capability on top of it.

### Reality track (v1.1 – v1.3)

| Ver | Feature | What ships | Closes |
|---|---|---|---|
| v1.1 | [[FEAT-013]] | Shipped artifact embeds + runs the analyzer (resolve [[DD-011]]). Sentinel edit changes the hash; `analyze()` runs in wasmtime. | [[REQ-009]]; the v1.0.1 open finding |
| v1.2 | [[FEAT-014]] | witness MC/DC on the analyzer — instrument the executable Wasm, drive it with the host-test fixtures as a witness harness, emit a signed truth-table report. | [[REQ-010]]; the witness step blocked since v0.1 |
| v1.3 | [[FEAT-015]] | Un-skip the abstract-vs-concrete soundness oracle (`soundness.rs`); the kill-criterion becomes live, not concrete-side-only. | [[REQ-001]] / FEAT-001 AC#3 |

The witness route is the key unlock. witness works at the **wasm+DWARF
layer with a `--harness` subprocess mode** — so the analyzer does not have
to be MC/DC-measured *as the wac-composed component*. Once [[FEAT-013]]
makes the analyzer executable, the existing host-test fixtures become the
witness harness and the analyzer's ~268 decision points get a real truth
table.

### Capability track (v1.4 – v2.0)

| Ver | Feature | The capability leap |
|---|---|---|
| v1.4 | [[FEAT-016]] | Analyzer loop-carried **octagon** relational fixpoint — *use* the octagon across loops (the deferred half of FEAT-010), + Miné strong/tight closure. |
| v1.5 | [[FEAT-017]] | **SpecTec soundness-by-construction** backend — derive transfer functions from the spec (the deferred FEAT-011 AC#2); soundness as a discharged side-condition. |
| v1.6 | [[FEAT-018]] | **Component-Model handle-state / use-after-drop** (the deferred FEAT-002 slice) — addresses the undeveloped sub-goal [[G-003]]. |
| v1.7 | [[FEAT-019]] | **Differential precision corpus** vs Wanilla + Wassail — make precision claims falsifiable against an external baseline. |
| v2.0 | [[FEAT-020]] | **Tool-qualification dossier** — match the QSK/QSLCD bar, differentiated by mechanized soundness; closes [[G-005]]. |

## What 2.0 is

v2.0 is the release where **the shipped artifact is the verified artifact,
its analysis decisions are structurally covered, its soundness is proven
*and* exercised live, and the whole thing is packaged as a qualification
dossier an assessor can act on** — the only sound Wasm analyzer whose
soundness is a machine-checked theorem.

## Sequencing note

The reality track ([[FEAT-013]]–[[FEAT-015]]) does not depend on the
research and could begin immediately; the capability track
([[FEAT-016]]–[[FEAT-020]]) is deliberately scheduled after, because each
capability is only worth measuring once the artifact it runs in is real.
This is the methodology's "fix the foundation, then build on it" applied
to a roadmap: breadth was v1.0's story; depth is v2.0's.
