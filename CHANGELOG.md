# Changelog

All notable changes to scry are documented here.

Format: [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning: [SemVer 2.0](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- `.github/workflows/ci.yml` — CI pipeline running fmt, clippy (wasm32-wasip2 target),
  `rivet validate`, `spar parse spar/scry.aadl`, WIT round-trip via `wasm-tools`,
  Bazel build of `//:scry`, `wasm-tools validate` on the composed component,
  and cargo-deny (informational at v0.1 until `deny.toml` lands).
- `.github/workflows/release.yml` — Tag-triggered release workflow building the
  composed `bazel-bin/scry.wasm`, generating a CycloneDX SBOM, SHA256SUMS, cosign
  keyless-OIDC signatures, and SLSA v1 provenance via `actions/attest-build-provenance`.
  Release body is auto-extracted from this CHANGELOG.
- `CHANGELOG.md` — this file, in Keep a Changelog format.
- Workspace-level `[workspace.package]` with single source of truth for
  `version` / `edition` / `license` / `repository` / `authors`. Both member crates
  reference these via `.workspace = true`. Rust edition pinned to **2024**.

### Changed

- `crates/wasm-lattice/Cargo.toml` and `crates/scry-analyzer/Cargo.toml`:
  switched from `edition = "2021"` to inheriting `edition.workspace = true`
  (resolved value: `2024`). MODULE.bazel rust toolchain bumped to edition 2024
  to match.

## [0.1.0] — pending

Headline: **scaffolding ships**. The full PulseEngine Wasm-component toolchain
proven end-to-end on scry's own build (the dogfood gate for DD-008).

### Added

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
  - `wasm-lattice` — interval-domain library, `#![no_std]`.
  - `scry-analyzer` — analyzer scaffold that exercises the cross-component
    lattice import end-to-end via `domain::constant_i32(42)`.
- **Bazel build via `rules_wasm_component` v1.0.0** (pinned to commit
  `d2347fbf` via `git_override` since v1.0.0 is not yet in BCR).
  `bazel build //:scry` produces a valid wasm32-wasip2 Component Model
  artifact at `bazel-bin/scry.wasm` via `wac_compose` and `composition.wac`.
- **Three new design decisions** added to the rivet artifact graph:
  - DD-008: scry ships as a Wasm Component Model component (dogfood).
  - DD-009: build with Bazel + `rules_wasm_component`.
  - DD-010: hand-write WIT to match the AADL model for v0.1; integrate
    spar-codegen in a later version.
- **FEAT-001 acceptance criteria** rewritten to gate on concrete Bazel
  targets and Wasm tooling.
- **Local schema extension** at `schemas/research-ext.yaml` adding three
  cross-artifact link types: `references-paper`, `addresses-finding`,
  `evaluates-tech`.
- **README + roadmap** in falcon/witness aspirational style with a
  10-row release plan and per-version `tags: [v0.x]` on the proposed
  FEAT artifacts.

### Known limitations

- No real interval-domain fixpoint yet — the scaffold returns a hardcoded
  invariant bundle. Real `wasmparser`-driven analysis lands with the next
  PR (FEAT-001 acceptance criterion #1).
- No host wasmtime test harness (FEAT-001 acceptance criterion #3).
- No `deny.toml` — cargo-deny runs with built-in defaults and is
  informational at v0.1.
- No witness MC/DC integration — the scaffold has too few branches to
  measure; integrate once the real fixpoint lands.
- spar-codegen Bazel rule not yet integrated (per DD-010); the WIT is
  hand-derived from `spar/scry.aadl` and a CI check that they stay in
  sync is a follow-on task.

### Cross-repo dependency

- `pulseengine/meld#192` — meld emits a minimal `component-provenance`
  custom section. Required for v0.7 (FEAT-002), not blocking v0.1.

## Earlier

See git history for pre-v0.1 work (initial scope-out + DD-002 closure).

[Unreleased]: https://github.com/pulseengine/scry/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/pulseengine/scry/releases/tag/v0.1.0
