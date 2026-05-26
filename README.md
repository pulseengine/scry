# scry — sound abstract interpretation for WebAssembly

**a verification pass built inside the [PulseEngine](https://pulseengine.eu)
toolchain.** scry over-approximates the reachable behaviour of fused Wasm
Core Model modules emitted by [meld](https://github.com/pulseengine/meld),
and (phase 2) lifts that analysis to Component-Model-level properties.
it closes the third [DO-333](https://en.wikipedia.org/wiki/DO-333)
technique-class gap — sound static analysis — that PulseEngine's existing
deductive-proof and bounded-model-checking layers do not staff.

> scry is part of the [PulseEngine](https://pulseengine.eu) verification
> chain. it consumes meld's fused output, feeds invariants to
> [loom](https://github.com/pulseengine/loom)'s optimizer, and produces
> [sigil](https://github.com/pulseengine/sigil)-signed in-toto evidence
> that [rivet](https://github.com/pulseengine/rivet) links back to
> requirements.

## tagline

*scry sees. loom acts.*

## what scry is

- **sound, not unsound**. scry over-approximates: it may flag behaviour
  that cannot happen, but it never misses behaviour that can. soundness
  is stated against the official [Wasm operational semantics](https://dl.acm.org/doi/10.1145/3062341.3062363)
  (PLDI 2017) and tracked toward mechanized proof against
  [WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq).
- **the missing DO-333 leg**. PulseEngine already covers deductive proof
  ([Verus](https://verus-lang.github.io/verus/),
  [Rocq](https://rocq-prover.org/),
  [Lean](https://lean-lang.org/)) and bounded model checking
  ([Kani](https://model-checking.github.io/kani/), Z3 translation
  validation in loom). scry is the third class —
  abstract interpretation per the
  [Cousot framework](https://dl.acm.org/doi/10.1145/512950.512973)
  (POPL 1977) — explicitly named as the unstaffed layer in the
  [2026-04-22 overdo post](https://pulseengine.eu/blog/2026-04-22-overdoing-the-verification-chain/).
- **post-meld for Core Wasm, pre-meld for Component Model**. scry's
  Core analysis runs on the fused module meld emits, so its invariants
  apply directly to loom's transformation preconditions. Component-
  Model analysis (handles, capabilities, host effects) runs upstream
  of meld on the still-WIT-typed components; meld emits a minimal
  `component-provenance` custom section so scry can project the
  Component-Model invariants onto fused-module locations for loom,
  witness, and the sigil/rivet evidence chain (DD-002).
- **a reusable lattice library**. the abstract domains (interval,
  region-memory, reachability, taint, capability, resource-lifetime)
  ship as a separate crate (`wasm-lattice`) reusable by
  [witness](https://github.com/pulseengine/witness) for coverage-gap
  prediction and [synth](https://github.com/pulseengine/synth) for
  ARM/RISC-V codegen invariant generation.
- **six safety domains, one chain**. evidence scry produces earns
  credit in DO-178C/DO-333 (avionics), ISO 26262-6 §9 (automotive
  ASIL-D), IEC 61508-3 Annex B (general FS), IEC 62304 (medical
  Class C), EN 50128 (railway SIL 4), ECSS-Q-ST-80C (space) — by
  inheriting the same overdo-chain attestation story as
  [meld](https://github.com/pulseengine/meld) and
  [loom](https://github.com/pulseengine/loom).

## status

**pre-v0.1**, scoped, no code yet. this directory holds the
research, requirements, design decisions, and safety case for scry as
typed rivet artifacts; the implementation crate will live in its own
repo. follow the [release plan](#release-plan) below — each numbered
release ships a specific verified-evidence increment.

`rivet validate` here is PASS with 0 warnings; 56 artifacts span 11
types across `common + dev + research + research-ext + safety-case`.
this README is a *requirements artifact*, not a code artifact.

## is this for you?

scry is **for** you if any of these match:

- you ship safety-critical Wasm components through the PulseEngine
  pipeline and need DO-333-credit-bearing static analysis alongside
  Kani BMC and Verus proofs.
- you're hitting Wasm static-analysis tools whose call graphs are
  empirically unsound on `call_indirect` (83% of real Wasm — per
  [Lehmann et al. ISSTA 2023](https://2023.issta.org/details/issta-2023-papers/16/That-s-a-Tough-Call-A-Study-of-the-Challenges-of-Call-Graph-Construction-for-Wasm))
  and need an analysis whose soundness story is named.
- you want sound capability-flow or resource-lifetime analysis on
  Component Model compositions and have noticed
  [no such tool exists publicly](https://popl25.sigplan.org/details/waw-2025-papers/4/The-WebAssembly-Component-Model)
  yet.
- you want invariants that the loom optimizer can consume directly to
  strengthen its translation-validation preconditions.

scry is **probably not** for you if you want:

- a vulnerability scanner with low setup overhead — use
  [Wasmati](https://github.com/wasmati/wasmati) (Code Property Graph)
  for fast pattern-matching on Wasm binaries.
- a dynamic Wasm analyzer — use
  [Wasabi](http://wasabi.software-lab.org/) (binary instrumentation)
  or [Wastrumentation](https://github.com/wastrumentation/wastrumentation)
  (source-level, ECOOP 2025) for execution-trace-based analysis.
- a Rust-only deductive verifier — use
  [Verus](https://verus-lang.github.io/verus/) or
  [Kani](https://model-checking.github.io/kani/) directly; scry's
  level is Wasm, not Rust MIR.
- the industrial commercial AI for C/Ada — use
  [Astrée](https://www.absint.com/astree/index.htm); scry doesn't
  target C/Ada and won't.

## quickstart — three runnable examples

each example will exercise the whole PulseEngine stack: WIT-typed
components → meld static fusion → **scry sound abstract interpretation**
→ loom optimization → witness coverage → sigil signed bundle → rivet
traceability evidence. *commands shown are aspirational and become real
at the version they're tagged to.*

### example 1: `scry-hello` (v0.1)

minimum viable analysis. parses a hand-written tiny Wasm module
(arithmetic only, no memory, no calls), runs the interval domain over
i32/i64 locals, prints per-instruction interval invariants. no
integration, no signing — proves the pipeline.

```sh
cd examples/scry-hello
bazel build //...
scry analyze target/scry-hello.wasm \
  --domain interval \
  --format json
# → {"invariants":[{"pc":7,"locals":[{"idx":0,"interval":"[0,255]"}]},...]}
```

exercises: wasm-parser, wasm-lattice (interval domain), scry CLI.

### example 2: `scry-fused-bounds` (v0.3)

real fused Wasm module from meld, sound call-graph construction via
value-domain AI on the operand stack, region-memory bounds invariants
that loom can consume. produces a JSON invariant bundle.

```sh
cd examples/scry-fused-bounds
bazel build //...                              # WIT → wasm components
meld fuse fused-bounds.world.wit \
  --output target/fused-bounds.bundle.wasm
scry analyze target/fused-bounds.bundle.wasm \
  --domain interval,region-memory,reachability \
  --call-graph sound \
  --output target/fused-bounds.scry.json
loom optimize target/fused-bounds.bundle.wasm \
  --consume-invariants target/fused-bounds.scry.json \
  --enable bounds-check-elision,constant-fold
# → loom reports N elided bounds checks, M folded constants, all proven by scry
```

exercises: scry core (interval + region + reachability), sound
indirect-call resolution per
[Paccamiccio et al. 2024](https://arxiv.org/abs/2407.14527),
loom invariant ingestion.

### example 3: `scry-component-handles` (v0.7)

Component Model resource-lifetime analysis. pre-meld pass over a
composition of three components that exchange owned/borrowed handles;
scry reports any use-after-drop on owned handles at link time.
produces a sigil-signed in-toto attestation linkable from rivet.

```sh
cd examples/scry-component-handles
bazel build //...
scry analyze-components \
  --composition components.wac \
  --check resource-lifetime,capability-flow,host-effects \
  --output target/component-handles.scry.json
sigil sign target/component-handles.scry.json \
  --predicate in-toto-spec-v1
rivet add -t safety-solution \
  --title "scry attests no use-after-drop in component-handles" \
  --field evidence-type=formal-proof \
  --field evidence-ref=$(sha256sum target/component-handles.scry.json | cut -d' ' -f1) \
  --link "supports:G-003"
rivet validate
# → safety-goal G-003 transitions from undeveloped to supported.
```

exercises: scry component-mode (Component Model AI), sigil attestation,
rivet evidence-to-safety-goal linking, end-to-end overdo chain.

## release plan

honest incremental scope, witness-style. each version closes a
specific gap. signed binaries, CHANGELOG-disciplined, rivet-validated
release artifacts. the per-version rivet feature artifacts (`FEAT-*`)
are in `artifacts/requirements.yaml`; provisional ones for v0.2+ carry
`status: proposed`.

| version | what ships | verification delta | example | feature artifact |
|---|---|---|---|---|
| v0.1 | scry CLI; wasm-parser + interval domain on i32/i64 locals; JSON invariant output; no memory, no calls | unit tests · soundness theorem stated paper-only for interval domain | `scry-hello` | FEAT-001 |
| v0.2 | region-based linear-memory model (CRAB-style); per-region offset tracking | property-based soundness tests on region+interval product | (extends v0.1) | FEAT-005 |
| v0.3 | sound `call_indirect` resolution via value-domain AI on the operand stack; reachability domain | proptest on indirect-call resolution vs ground-truth concrete graph; differential vs Wassail | `scry-fused-bounds` | FEAT-006 |
| v0.4 | compositional summary-based interprocedural AI per Stiévenart & De Roover SCAM 2020 | scaling benchmark on real fused PulseEngine modules; summary-precision metrics | (extends v0.3) | FEAT-007 |
| v0.5 | loom integration: invariant schema v1; loom consumes scry output to trigger bounds-check elision + constant folding | end-to-end test on a meld→scry→loom pipeline; loom reports invariants-derived transforms | (extends v0.3) | FEAT-008 |
| v0.6 | sigil attestation per scry run; rivet integration; full evidence-to-requirement traceability | DSSE-signed in-toto predicates; `rivet validate` links scry attestations as `verified-by` evidence | (extends v0.3) | FEAT-004 |
| v0.7 | Component Model AI (per DD-002): scry analyzes original component sources; meld emits `component-provenance` custom section; scry projects invariants onto fused-module locations. Tracks owned/borrowed handle states, capability flow, host-call effects | sound resource-lifetime detection on real WAC compositions; capability-graph soundness check; meld `component-provenance` round-trip test | `scry-component-handles` | FEAT-002 |
| v0.8 | taint domain (Wanilla-class noninterference) for security-property analysis | proptest on relational noninterference; differential vs Wanilla on shared corpus | (extends v0.3) | FEAT-009 |
| v0.9 | octagon + relational numerical domains for false-alarm reduction; mechanized soundness proof of interval domain in Rocq against WasmCert-Coq | Rocq build green; reduced false-alarm rate measured on benchmark corpus | (extends v0.3) | FEAT-010 |
| v1.0 | six-domain credit dossier; full mechanized soundness for the v0.1+v0.2+v0.3 domain stack; SpecTec-derived transfer-function backend prototype | rivet coverage at 100% across the full G-001 sub-tree; `rivet validate --qualification-mode` green | (HW+dossier) | FEAT-011 |

## verification matrix (per shipped abstract domain)

each shipped abstract domain carries the full overdo chain. early
versions allow paper-only soundness; mechanized proof against
WasmCert-Coq is the v1.0 gate.

| chain layer | interval (v0.1) | region-memory (v0.2) | call-graph (v0.3) | summaries (v0.4) | taint (v0.8) |
|---|---|---|---|---|---|
| Lean / Rocq (math) | TBD | TBD | TBD | TBD | TBD |
| Verus (SMT) | bounds on join/widen | region disjointness | call-target set monotonicity | summary join monotonicity | label-flow monotonicity |
| Kani (bounded) | wrap-around overflow paths | offset overflow paths | jump-table edge cases | recursion-frontier edge cases | declassification edges |
| Rocq mechanized proof vs WasmCert-Coq | v0.9 | v1.0 | v1.0 | v1.0 | post-v1.0 |
| proptest | random concrete program ⊆ abstract result | random region access patterns | random `call_indirect` programs | random call graphs | random taint flows |
| differential vs prior art | (none specific) | CRAB ground-truth on translated C | Wassail call-graph diff | Stiévenart summaries diff | Wanilla diff |
| sigil signed evidence | per analyzer run | per analyzer run | per analyzer run | per analyzer run | per analyzer run |
| rivet | every domain's soundness theorem linked to its `safety-solution` | same | same | same | same |
| witness MC/DC | on the scry implementation itself (Rust→Wasm) | same | same | same | same |

## six-domain credit alignment

| standard | scry-specific use case | credit class scry contributes |
|---|---|---|
| DO-178C + DO-333 | avionics components that pass through the PulseEngine pipeline | DO-333 §FM.4.4 "abstract interpretation" (third technique class) |
| ISO 26262 ASIL-D | ASIL-D control components running on Wasm runtimes | 26262-6 §9 static analysis ("abstract interpretation" recommended) |
| IEC 61508 SIL-4 | safety-related instrumentation control | 61508-3 Annex B static analysis credit |
| IEC 62304 Class C | medical device Class C software | static-analysis evidence for class C |
| EN 50128 SIL-4 | railway signaling components | static-analysis credit class T1/T2 |
| ECSS-Q-ST-80C | space flight software | static-analysis credit per ECSS-E-ST-40C |
| EU CRA | any commercial Wasm-component product in EU | "appropriate verification" evidence (Article 13) |

each row is a market where the same chain (meld + scry + loom + witness
+ sigil + rivet) earns credit without rebuilding the dossier.

## architecture — where scry sits

```
   ┌─────────────────────────────────────────────────────────┐
   │  Component Model layer (WIT-typed components)           │
   │  ┌─ scry pre-meld (v0.7+) ─────────────────────────┐    │
   │  │  resource-lifetime · capability-flow · effects  │    │
   │  └─────────────────────────────────────────────────┘    │
   └─────────────────────────────────────────────────────────┘
                            ▼ meld static fusion
   ┌─────────────────────────────────────────────────────────┐
   │  Core Wasm layer (fused module)                         │
   │  ┌─ scry post-meld (v0.1 baseline) ────────────────┐    │
   │  │  interval · region-memory · reachability ·      │    │
   │  │  sound call-graph · compositional summaries ·   │    │
   │  │  taint                                          │    │
   │  └──────────┬──────────────────────────────────────┘    │
   │             ▼ invariants (JSON, signed)                 │
   │  ┌─ loom optimizer ────────────────────────────────┐    │
   │  │  bounds-check elision · constant fold · DCE     │    │
   │  │  + Z3 translation validation per pass           │    │
   │  └─────────────────────────────────────────────────┘    │
   └─────────────────────────────────────────────────────────┘
                            ▼ optimized fused Wasm
   ┌─────────────────────────────────────────────────────────┐
   │  Downstream consumers                                   │
   │   • witness   ── MC/DC on the same module               │
   │   • synth     ── AOT to ARM/RISC-V (invariants help)    │
   │   • kiln      ── runtime executes the optimized Wasm    │
   │   • sigil     ── signs the whole evidence bundle        │
   │   • rivet     ── links scry attestations to requirements│
   └─────────────────────────────────────────────────────────┘
```

shared cross-layer flows:

- scry's Component-Model analysis runs on the original component
  sources upstream of meld; meld emits a minimal `component-provenance`
  custom section that maps fused-module function indices back to
  their originating component+function. scry uses this mapping to
  project Component-Model invariants onto fused-module locations
  (DD-002, closed 2026-05-26).
- the `wasm-lattice` crate is consumed by witness for coverage-gap
  prediction (an over-approximation of unreachable branches narrows
  the witness MC/DC coverage frontier).
- sigil signs the invariant JSON; rivet links the signed digest as
  `verified-by` evidence on the originating requirement.

## design decisions worth reading first

| decision | what's open | where |
|---|---|---|
| DD-001 | pipeline placement: post-meld between meld and loom | `artifacts/design.yaml#DD-001` |
| DD-002 | Component-Model AI placement: option (b) closed 2026-05-26 — scry analyzes original component sources; meld emits minimal `component-provenance` custom section | `artifacts/design.yaml#DD-002` |
| DD-003 | soundness substrate: WasmCert-Coq + Iris-Wasm | `artifacts/design.yaml#DD-003` |
| DD-004 | reusable wasm-lattice crate decoupled from Wasm front-end | `artifacts/design.yaml#DD-004` |
| DD-005 | v0 domain set: interval + region-memory + reachability + sound call-graph | `artifacts/design.yaml#DD-005` |
| DD-006 | compositional summary-based interprocedural AI | `artifacts/design.yaml#DD-006` |
| DD-007 | sigil-signed in-toto attestations linked from rivet | `artifacts/design.yaml#DD-007` |

## prior art — what we read, what we build on

every cited paper is a `academic-reference` rivet artifact in
`artifacts/research.yaml`. the most load-bearing:

- **[Cousot & Cousot, POPL 1977](https://dl.acm.org/doi/10.1145/512950.512973)**
  — the framework. every soundness theorem reduces to this.
  `AC-001`.
- **[Haas, Rossberg, Schuff et al., PLDI 2017](https://dl.acm.org/doi/10.1145/3062341.3062363)**
  — the official Wasm operational semantics. the concrete semantics
  scry over-approximates. `AC-002`.
- **[Watt, Rao et al., FM 2021](https://hal.science/hal-03353748)**
  — WasmCert-Coq and WasmCert-Isabelle, the mechanized semantics.
  the substrate scry's soundness proofs target. `AC-003`.
- **[Rao, Georges et al., PLDI 2023](https://dl.acm.org/doi/10.1145/3591265)**
  — Iris-Wasm. higher-order separation logic on top of WasmCert-Coq;
  the natural frame for modular/relational scry proofs. `AC-004`.
- **[Brandl, Erdweg, Keidel, Hansen, ECOOP 2023](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2023.5)**
  — modular abstract definitional interpreters for Wasm. proves AI
  for Wasm Core is practical (full Wasm 1.0 in ~1600 LOC). the
  pattern wasm-lattice imitates. `AC-006`.
- **[Scherer, Blaabjerg, Sjösten, Maffei, CCS 2025](https://arxiv.org/abs/2509.08758)**
  — Wanilla. first sound noninterference AI for Wasm; the v0.8 taint
  baseline. `AC-007`.
- **[Paccamiccio, Raimondi, Loreti, 2024](https://arxiv.org/abs/2407.14527)**
  — sound `call_indirect` resolution via value-domain AI; the v0.3
  call-graph technique. `AC-008`.
- **[Menon & Wagner, WAW 2025 at POPL](https://popl25.sigplan.org/details/waw-2025-papers/4/The-WebAssembly-Component-Model)**
  — the spec authors' opening of Component Model formalization; the
  named gap scry's v0.7+ phase 2 attacks. `AC-009`.

## where to look in this tree

```
unknown-project/                           (will be renamed to `scry/`)
├── README.md                              (this file)
├── rivet.yaml                             (project + schemas)
├── schemas/
│   └── research-ext.yaml                  (local schema: references-paper /
│                                           addresses-finding / evaluates-tech
│                                           link types)
├── artifacts/
│   ├── research.yaml                      (11 papers + 7 tech evals +
│                                           4 market findings)
│   ├── requirements.yaml                  (8 requirements + 4 features
│                                           [+ FEAT-005..011 proposed])
│   ├── design.yaml                        (7 design decisions; DD-002 open)
│   └── safety-case.yaml                   (4 GSN goals + 1 strategy +
│                                           4 solutions + 3 contexts +
│                                           3 justifications)
└── docs/
    └── roadmap.md                         (per-version research links +
                                            composition narrative —
                                            witness-style)
```

## related projects

- **[rivet](https://github.com/pulseengine/rivet)** — typed artifact
  graph + V-model traceability. scry artifacts live here.
- **[meld](https://github.com/pulseengine/meld)** — static WASM
  component fusion. scry's primary input source for post-meld analysis;
  scry's pre-meld pass runs upstream of meld for Component-Model
  properties.
- **[loom](https://github.com/pulseengine/loom)** — verified WASM
  optimizer. consumes scry invariants to strengthen transformation
  preconditions (bounds-check elision, constant fold, DCE).
- **[witness](https://github.com/pulseengine/witness)** — MC/DC
  branch coverage for WASM. consumes wasm-lattice's reachability for
  coverage-gap prediction.
- **[synth](https://github.com/pulseengine/synth)** — WASM-to-ARM
  AOT transcoder. consumes wasm-lattice for codegen invariant
  generation.
- **[kiln](https://github.com/pulseengine/kiln)** — Wasm runtime for
  safety-critical systems. executes the scry-vetted, loom-optimized
  output.
- **[sigil](https://github.com/pulseengine/sigil)** — supply-chain
  signing. produces the in-toto envelopes around scry's evidence.
- **[spar](https://github.com/pulseengine/spar)** — AADL v2.3
  toolchain. scry results allocate back to AADL components for
  architecture-level traceability.

## why this exists

PulseEngine's stack already has the deductive-proof leg (Verus, Rocq,
Lean) and the bounded-model-checking leg (Kani, Z3 in loom). DO-333,
ISO 26262-6 §9, IEC 61508-3 Annex B, and the rest of the credit-bearing
standards recognize a third leg: **abstract interpretation**. the
PulseEngine 2026-04-22 blog post named this gap. scry closes it.

separately: there is no publicly available sound abstract interpreter
for the WebAssembly Component Model as of 2026. the spec authors
themselves opened the formalization question at WAW 2025; the
literature on Core-Wasm AI is young (post-2020) and growing. scry's
phase-2 component pass is a real novel-contribution opportunity, not
a re-implementation of existing work.

*do the work once. earn credit six times. close the gap the literature
named.*

---

## status of this README

this README is a *requirements artifact*, not a code artifact. it
describes what scry will be. v0.1 is what makes the first row of the
release table green. follow `artifacts/requirements.yaml` for FEAT-*
status; provisional milestones carry `status: proposed`.

`rivet list --type feature --format json` returns the machine-readable
roadmap. `rivet coverage` returns the evidence-to-requirement
coverage. `rivet impact --since HEAD~1` shows which scry artifacts a
given commit changes.

if you're reading this in 2027 and v1.0 has shipped, this README
should already have been replaced by a *facts* artifact rather than an
*intent* artifact. if not, send a PR.
