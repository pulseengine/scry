# Changelog

All notable changes to scry are documented here.

Format: [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning: [SemVer 2.0](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0] — 2026-05-27

Headline: **scaffolding ships**. The full PulseEngine Wasm-component toolchain
proven end-to-end on scry's own build (the dogfood gate for `DD-008`).
No real abstract-interpretation logic yet — that lands with `FEAT-001`
acceptance criterion #1 in the v0.2 cycle. v0.1.0 ships the *structure*
so every subsequent change has typed traceability, CI gates, signed
release evidence, and a green Bazel build to anchor on.

### Architecture and source code

- **AADL architecture model** at `spar/scry.aadl` modelling the two-process
  composition (`LatticeProcess` + `AnalyzerProcess`). Validates with
  `spar parse`.
- **WIT interface definitions** per crate:
  - `crates/wasm-lattice/wit/wasm-lattice.wit` exports the
    `pulseengine:wasm-lattice/domain` interface (interval domain ops +
    i32 transfer functions).
  - `crates/scry-analyzer/wit/scry.wit` imports the lattice domain and
    exports the `pulseengine:scry/analyzer` interface.
- **Two wasm32-wasip2 component crates** under `crates/`:
  - `wasm-lattice` — interval-domain library, `#![no_std]`. Implements
    bottom / top / leq / join / meet / widen / constant-i32 / i32-add /
    i32-sub / i32-mul.
  - `scry-analyzer` — analyzer scaffold that exercises the
    cross-component lattice import end-to-end via
    `domain::constant_i32(42)` as the dogfood gate.
- **Bazel build via `rules_wasm_component` v1.0.0** (pinned to commit
  `d2347fbf` via `git_override` since v1.0.0 is not yet in BCR).
  `bazel build //:scry` produces a valid wasm32-wasip2 Component Model
  artifact at `bazel-bin/scry.wasm` via `wac_compose` and
  `composition.wac`.
- **Cargo workspace** with `[workspace.package]` single source of truth
  for `version` / `edition` / `license` / `repository` / `authors`.
  Both member crates inherit via `.workspace = true`. Rust edition
  pinned to **2024**.

### Rivet artifact graph

- **64 typed artifacts** across 11 types (academic-reference,
  technology-evaluation, market-finding, requirement, feature,
  design-decision, safety-goal, safety-strategy, safety-solution,
  safety-context, safety-justification). `rivet validate` PASS, 0
  warnings.
- **Local schema extension** at `schemas/research-ext.yaml` adding
  three cross-artifact link types: `references-paper`,
  `addresses-finding`, `evaluates-tech`.
- **Three new design decisions** added during the v0.1 cycle:
  - DD-008: scry ships as a Wasm Component Model component (dogfood).
  - DD-009: build with Bazel + `rules_wasm_component`.
  - DD-010: hand-write WIT to match the AADL model for v0.1;
    integrate spar-codegen in a later version.
- **DD-002 closed** in favour of option (b) — meld emits a minimal
  `component-provenance` custom section; scry analyzes original
  component sources upstream of meld. Cross-repo dependency tracked at
  `pulseengine/meld#192`.
- **FEAT-012 added** as a v0.2 proposed feature: wire `rules_verus` +
  `rules_rocq_rust` into the Bazel build with one provable theorem per
  family (lattice algebra).

### CI and release infrastructure

- **`.github/workflows/ci.yml`** — full CI pipeline: Format (cargo
  fmt), Clippy (placeholder until host crate lands), Test (placeholder
  until wasmtime harness lands), Rivet artifact validation, AADL
  model (`spar parse`), WIT round-trip (`wasm-tools component wit`),
  Bazel build (`//:scry`) + `wasm-tools validate` on the composed
  component, cargo-deny (licenses / advisories / bans).
- **`.github/workflows/release.yml`** — tag-triggered (`v*`) release
  workflow building the composed `bazel-bin/scry.wasm`, generating a
  CycloneDX SBOM, SHA256SUMS, cosign keyless-OIDC signatures
  (per-asset + bundle), SLSA v1 provenance via
  `actions/attest-build-provenance`, and a GitHub Release with notes
  auto-extracted from this CHANGELOG.
- **`deny.toml`** copied verbatim from the witness/rivet family
  pattern; allows the eight PulseEngine-standard licenses.

### Documentation

- **`README.md`** — falcon/witness aspirational style with a 10-row
  release plan and per-version `tags: [v0.x]` on proposed FEAT artifacts.
- **`docs/intro-to-abstract-interpretation.md`** — friendly explainer
  for readers who've never met "abstract interpretation". `safe_index`
  worked example, what "sound" means, widening for loops, where scry
  fits. ~10 min, no math. Tagged `id: DOC-INTRO-AI`.
- **`docs/architecture.md`** — how scry v0.1 works end-to-end with
  mermaid diagrams: two-component decomposition, 8-layer Bazel build
  pipeline, WAC composition contract, 8-step PulseEngine loop
  status, runtime cross-component probe, Bazel target dep graph.
  Tagged `id: DOC-ARCH-V01`.
- **`docs/roadmap.md`** — per-version plan with research links and
  composition narrative (witness-style).
- **`CHANGELOG.md`** — this file; release.yml extracts version
  sections as GitHub Release notes via awk.

### Known limitations and deferred work

- **No real interval-domain fixpoint** — the scaffold returns a
  hardcoded invariant bundle plus a single diagnostic confirming
  cross-component import wired correctly. Real `wasmparser`-driven
  analysis lands with FEAT-001 acceptance criterion #1 in v0.2.
- **No host wasmtime test harness** — FEAT-001 acceptance criterion
  #3, deferred to v0.2 (drops the Clippy + Test CI placeholders).
- **No Verus + Rocq proof targets** — FEAT-012, deferred to v0.2.
  Toolchain wiring (rules_verus + rules_rocq_rust + nix_repo for
  Rocq) lands first; mechanized soundness for the interval domain is
  v0.9 (FEAT-010).
- **No witness MC/DC integration** — scaffold has too few branches
  to measure usefully; integrate once the real fixpoint lands.
- **No spar-codegen Bazel rule** — per DD-010 the WIT is hand-derived
  from the AADL for v0.1; a CI check that they stay in sync is a
  follow-on task.

### Falsifiable kill-criterion for v0.1.0

This release is wrong if, on any well-formed Wasm Core Model module
the scry-analyzer component is invoked on, the diagnostic in the
returned `analysis-result` reports the lattice cross-component import
as `BROKEN` rather than `alive`. The v0.1 dogfood claim is that the
WIT cross-component import works end-to-end through wac_compose; the
`constant_i32(42)` probe in `crates/scry-analyzer/src/lib.rs` is the
falsifier.

## Earlier

See git history for pre-v0.1 work (initial scope-out + DD-002 closure
in PR #2).

[Unreleased]: https://github.com/pulseengine/scry/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/pulseengine/scry/releases/tag/v0.1.0
