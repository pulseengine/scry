# scry — roadmap

> Generated 2026-05-26 from the initial scope-out pass that landed
> README.md and the 56 rivet artifacts under `artifacts/`. The
> provisional artifacts (`status: proposed`) for v0.2 through v1.0 are
> auditable in `artifacts/requirements.yaml` from now —
> `rivet list --type feature --status proposed --format json` shows
> them.

## Where we are

| Version | Status | Capability |
|---|---|---|
| pre-v0.1 | shipped 2026-05-26 | research + requirements + design + safety-case as 56 rivet artifacts; `research-ext` local schema; PASS validate; README + this roadmap |
| v0.1 → v1.0 | shipped 2026-05-27 … 2026-05-29 | the capability ladder below, built in dependency order: interval fixpoint (v0.1/v0.2) → Verus+Rocq proof toolchain (v0.2) → region memory + host-oracle harness (v0.3) → sound `call_indirect` call graph (v0.4) → compositional interprocedural summaries (v0.5) → loom invariant JSON contract (v0.6) → `component-provenance` typed meld↔scry boundary + invariant projection (v0.7, FEAT-002 provenance slice) → taint / termination-insensitive-noninterference domain (v0.8, FEAT-009: `low ⊑ high` label lattice + explicit & implicit-flow propagation + High→Low findings) → octagon relational domain (DBM `±x±y ≤ c`) + first mechanized Rocq interval-soundness proof (v0.9, FEAT-010: `scry-octagon` crate dogfooded over WIT + `proofs/rocq/Soundness.v`, γ-soundness with 0 admits) → **full-stack mechanized soundness (interval+region+call-graph+reachability, 0 admits) + six-domain credit dossier closing safety goal G-001 (v1.0, FEAT-011)**. SpecTec soundness-by-construction backend (FEAT-011 AC#2) deferred to v1.1. See `CHANGELOG.md` for the per-release falsification kill-criteria. |

## Forward path

| Version | Scope | Driving research / artifacts | Status |
|---|---|---|---|
| **v0.1** | scry CLI; wasm-parser; interval domain on i32/i64 locals; JSON invariant output; `scry-hello` runnable | DD-001, DD-004, DD-005 (interval); AC-001 (Cousot framework); AC-002 (operational semantics) | provisional: FEAT-001 |
| **v0.2** | (a) CRAB-style region-based linear-memory model; per-region offsets; property-based soundness on region × interval. (b) Wire `rules_verus` + `rules_rocq_rust` into the Bazel build with one provable theorem per family (lattice algebra) — proof toolchain lights up end-to-end before heavier mechanization lands. | DD-005; AC-006 (Brandl modular AI); J-003 (region-memory rationale); TE-005 (CRAB reference); DD-003 (mechanization substrate) | provisional: FEAT-005, FEAT-012 |
| **v0.3** | sound `call_indirect` resolution via value-domain AI on the operand stack; reachability domain; `scry-fused-bounds` runnable | DD-005; AC-008 (Paccamiccio sound call-graph); MF-003 (call-graph-soundness pain-point); REQ-008 | provisional: FEAT-006 |
| **v0.4** | compositional summary-based interprocedural AI; scales to fused multi-component modules | DD-006; AC-010 (Stiévenart compositional summaries); REQ-007 | provisional: FEAT-007 |
| **v0.5** | loom integration: invariant schema v1; loom consumes scry output for bounds-check elision + constant fold | REQ-004; DD-001 | provisional: FEAT-008 |
| **v0.6** | sigil signed in-toto attestation per scry run; rivet `verified-by` integration; end-to-end overdo evidence | DD-007; REQ-005; FEAT-004 | provisional: FEAT-004 (already drafted) |
| **v0.7** | Component Model AI per DD-002 (closed 2026-05-26): scry analyzes original component sources; meld emits `component-provenance` custom section (~300 LOC bolt-on); scry projects invariants onto fused-module locations. Tracks owned/borrowed handle states + capability flow + host-call effects. `scry-component-handles` runnable | DD-002 (closed); AC-009 (Menon & Wagner WAW 2025); MF-002 (Component Model AI gap); REQ-003; FEAT-002 | provisional: FEAT-002 |
| **v0.8** | taint domain (Wanilla-class noninterference) | AC-007 (Wanilla CCS 2025) | provisional: FEAT-009 |
| **v0.9** | octagon / relational numerical domains; mechanized soundness proof of the interval domain in Rocq against WasmCert-Coq | AC-011 (Miné octagon); DD-003; TE-004 (WasmCert-Coq + Iris-Wasm) | provisional: FEAT-010 |
| **v1.0** | six-domain credit dossier; mechanized soundness for the v0.1+v0.2+v0.3 stack; SpecTec-derived transfer-function backend prototype | AC-005 (SpecTec); G-001 (top-level safety goal closes) | provisional: FEAT-011 |

## How the design decisions compose

The four design decisions that locked in this pass (`DD-001`, `DD-003`,
`DD-004`, `DD-005`) reinforce rather than collide:

- **DD-005 (initial domain set)** is intentionally narrow — interval +
  region-memory + reachability + sound call-graph — so v0.1 ships
  with paper-only soundness theorems against `AC-002` (operational
  semantics) and leaves relational and security domains as separable
  v0.8/v0.9 additions.
- **DD-004 (reusable lattice crate)** decouples the abstract domains
  from the Wasm front-end. The witness team can adopt `wasm-lattice`
  for coverage-gap prediction (`REQ-006`) without taking on Wasm
  parsing or the fixpoint engine. Brandl et al. (`AC-006`) demonstrate
  this modular pattern yields per-analysis costs under 210 LOC once
  the lattice library exists.
- **DD-001 (post-meld placement)** is the cheap path for Core Wasm
  analysis. It puts scry directly upstream of loom so invariants
  apply to loom's transformation preconditions without translation —
  the exact shape loom needs for translation-validation strengthening.
- **DD-003 (WasmCert-Coq + Iris-Wasm substrate)** ties the long-term
  mechanization story to PulseEngine's existing Rocq investment
  (`rules_rocq_rust`, meld's fusion proofs, synth's i32-semantics
  proofs). v0.9 lands the first mechanized soundness theorem for the
  interval domain; v1.0 extends to the full v0.1-v0.3 stack.

`DD-002` (Component Model AI placement) was closed 2026-05-26 in
favour of **option (b)**: scry analyzes original component sources
upstream of meld; meld emits a minimal `component-provenance` custom
section (~300 LOC bolt-on, infrastructure already present); scry
projects the resulting invariants onto fused-module locations using
the section. The boundary is clean: meld owns Core Wasm fusion
correctness (proven in Rocq); scry owns Component-Model semantics
(proven separately). See `artifacts/design.yaml#DD-002` for the full
rationale and the meld investigation that grounded the call.

## V-model traceability

Every release ships:

- `artifacts/{research,requirements,design,safety-case}.yaml` —
  rivet-validated artifact graph.
- `rivet list --format json` — current state, machine-readable.
- (v0.6+) `compliance/traceability-matrix.html` and `.json` —
  per-release matrix from `rivet matrix` bundled into the GitHub
  release asset.
- (v0.6+) sigil-signed in-toto evidence envelope per scry run, with
  the requirement-to-evidence mapping pre-resolved.

The V-model claim is provable, not asserted: a `safety-goal` opens
to its `safety-strategy` (`S-001`), which decomposes to `safety-solution`
artifacts that point at signed scry-run digests via `evidence-ref`.

## Open competitive risks

- **No competing PulseEngine-shaped tool exists** for sound AI on
  Wasm. The closest is Wassail (TE-003) but its call-graph is
  empirically unsound (`MF-003`), it's OCaml not Rust, and it has no
  attestation story. Brandl et al.'s framework (`AC-006`) is academic
  Haskell research, not production. The differentiation is real.
- **Astrée** (TE-001) is the industrial gold standard for C/Ada but
  doesn't target Wasm and is closed/commercial. Not a competitor;
  the reference point for "industrial sound AI is achievable."
- **MIRAI** (TE-002) does Rust MIR AI but is explicitly experimental
  with a disbanded team. Not a long-term basis. Useful tactical
  reference for Rust-side abstract-domain implementation patterns.
- **Wanilla** (AC-007, CCS 2025) is the closest published sound Wasm
  AI tool, but targets noninterference only — scry's v0.8 taint
  domain is the direct comparison point, with the rest of scry being
  out-of-scope for Wanilla.

## Where to look for what

| If you need... | Look at |
|---|---|
| Why scry exists | [`README.md`](../README.md) §why-this-exists; `MF-001`, `MF-004` |
| The literature pass | `artifacts/research.yaml` (11 papers, scored) |
| The requirements | `artifacts/requirements.yaml` (REQ-001..008, FEAT-001..011) |
| The design decisions | `artifacts/design.yaml` (DD-001..007; DD-002 open) |
| The safety case | `artifacts/safety-case.yaml` (G-001..004 GSN goals) |
| The local schema extension | `schemas/research-ext.yaml` |
| Provisional artifacts for next versions | `rivet list --status proposed --format json` |
| Per-version capability deltas | this file, "Forward path" table |
| The overdo-chain context | [pulseengine.eu blog 2026-04-22](https://pulseengine.eu/blog/2026-04-22-overdoing-the-verification-chain/) |
