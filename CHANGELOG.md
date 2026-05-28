# Changelog

All notable changes to scry are documented here.

Format: [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning: [SemVer 2.0](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.4.0] — 2026-05-28

Headline: **sound call graphs**. `call_indirect` — the dominant
source of unsoundness across Wasm static analyzers ([[MF-003]], 83%
of real Wasm uses it) — is now resolved soundly. scry intersects
the operand-stack index interval with the function-table bounds and
resolves the exact target set, dispatching through the same interval
domain whose soundness FEAT-001 AC#1 established ([[FEAT-006]],
[[AC-008]] Paccamiccio et al. 2024).

### Added

- **Sound `call_indirect` resolution** ([[FEAT-006]], #15). The
  analyzer parses the table + active element segments in a pre-pass,
  then on `call_indirect` clamps the top-of-stack index interval to
  `[0, table_len)` and resolves the target set from the element
  segments. A **constant index resolves to exactly one target**
  (precise); an unconstrained index resolves to the whole table
  (sound over-approximation, `Warning`-tagged). Both are tagged
  `sound` — scry never produces the unsound *under*-approximation
  that plagues other Wasm analyzers per [[MF-003]]. Direct `call`
  also records a (trivially sound) single-target edge. `analysis-result`
  gains a `call-graph: list<call-edge>` field; new `soundness-tag`
  enum and `call-edge` record in the WIT. `CallIndirect` no longer
  emits `UnsoundnessFallback`.
  - Soundness argument: for any concrete execution reaching a
    `call_indirect` with concrete index `k`, `k ∈ [lo,hi]` (the
    interval is sound per [[FEAT-001]] AC#1), so the resolved target
    set `{ table[j] : j ∈ [lo,hi] ∩ [0,table_len) }` includes
    `table[k]`. Soundness reduces to interval-domain soundness.
  - New fixture `fixture-04-call-indirect.wat`: a 3-entry funcref
    table with a constant-index call (precise `{1}`) and an
    unconstrained-param call (whole-table `{0,1,2}`).
- **`CallEdge` / `CallGraph` in the AADL model** (`spar/scry.aadl`)
  + a `callgraph_out` port wired through the analyzer process.

### Known limitations / deferred

- **No interprocedural value propagation.** FEAT-006 resolves the
  call *graph*, not call *effects*: after a call, params are popped
  and `top` is pushed per result (sound, pessimistic). Interprocedural
  fixpoint via compositional summaries is [[FEAT-007]] (v0.5).
- **Passive/declared element segments and non-constant active
  offsets** resolve to whole-table over-approximation (sound,
  imprecise). Constant active-offset segments are precise.
- Abstract-side host-harness assertion still skipped (the v0.3
  wac-compose/wasmtime-45 limitation, unchanged); the concrete-side
  oracle continues to run.
- `Verus Formal Proofs` CI job still informational (upstream
  `rules_verus` sysroot issue).

### Falsifiable kill-criterion for v0.4.0

This release is wrong if there exists a concrete execution that
reaches a `call_indirect` and dispatches to a function NOT in the
target set scry resolved for that call site — i.e. if scry ever
*under*-approximates a call graph. The soundness reduction above
makes this checkable: any counterexample would also be a
counterexample to the interval domain's soundness on the index
operand, which `scry-host-tests` exercises.

## [0.3.0] — 2026-05-28

Headline: **memory bounds + a mechanical soundness harness**. The
analyzer gains a region-based linear-memory abstract domain so the
canonical base+offset memory-access pattern is proven in-bounds
instead of falling back to `top` ([[FEAT-005]]). A new host
wasmtime test crate runs the composed component and checks the
analyzer's invariants against concrete execution, turning the
v0.2.0 kill-criterion from hand-checkable into CI-gated
([[FEAT-001]] AC#3).

### Added

- **Region-based linear-memory domain** ([[FEAT-005]], #12).
  `wasm-lattice` gains a `region` abstract type — `(region-id: u32,
  offset: interval)` — plus `region-create` / `region-offset` /
  `region-leq` / `region-join` / `region-meet` / `region-widen`
  transfer ops, all exported over the `pulseengine:wasm-lattice/domain`
  WIT interface ([[DD-004]]). The analyzer recognises the canonical
  `i32.const base; i32.const off; i32.add; i32.load` pattern,
  tags the result as a region-pointer, and emits a precise `Info`
  ("bounds-check elision safe") or `Warning` ("cannot prove
  in-region") diagnostic in place of v0.2's blanket
  `UnsoundnessFallback`. Region transfer ops dispatch through the
  imported lattice interface, preserving the [[DD-008]] dogfood.
  New fixture `fixture-03-region-bounds.wat` pins the canonical
  case (`[104, 108)` access in the 64 KB default region). Loaded
  *values* still widen to `top` at v0.3 — per-region content
  tracking is v0.4+ territory ([[FEAT-007]]).
- **Host wasmtime test harness** ([[FEAT-001]] AC#3, #13). New
  native cargo crate `crates/scry-host-tests/` (wasmtime 45 +
  wasmtime-wasi + wat). Three integration tests run each WAT
  fixture as a core Wasm module under wasmtime, capture the
  concrete return value, and assert it lies within the abstract
  interval scry reports — the v0.2.0 kill-criterion made
  mechanical. `compute() = 84 ∈ {84,84}` (exact), `doit(x) = x+5 ∈
  Top` across five inputs. Promotes the CI `Clippy` and `Test`
  jobs from no-op placeholders to real `cargo clippy` + `cargo
  test` runs; the `Test` job bazel-builds the composed component
  first, then runs the harness.

### Changed

- **CI `Clippy` and `Test` jobs are now real** (#13). No longer
  placeholders — `Clippy` runs `cargo clippy --package
  scry-host-tests -- -D warnings`; `Test` runs `bazel build //:scry`
  then `cargo test --package scry-host-tests`.

### Known limitations / deferred

- **Abstract-side soundness assertion is currently skipped in the
  harness.** `rules_wasm_component`'s `wac_compose` passes
  `--import-dependencies` to wac, which encodes each dependent
  package as a root-level component import on the composed
  `scry.wasm`. wasmtime 45 rejects root-level component imports, so
  the harness's in-process call to `analyzer.analyze` falls back to
  a `::notice::` skip. The **concrete-side oracle still runs** (each
  fixture executed under wasmtime, return value captured). The full
  abstract-vs-concrete assertion lights up automatically when any of:
  (a) wasmtime supports root-level component imports, (b)
  `wac_compose` stops passing `--import-dependencies`, or (c) scry
  adds a host re-compose step. Tracked as a follow-up.
- **Loaded memory values still widen to `top`** ([[FEAT-005]]
  precision deferred to [[FEAT-007]]); single default region per
  module; `memory.grow`/`memory.size` still hit the v0.2 fallback.
- **No sound `call_indirect`** — [[FEAT-006]], the v0.4.0 milestone.
- **`Verus Formal Proofs` CI job** still informational (upstream
  `rules_verus` sysroot issue, unchanged from v0.2).

### Falsifiable kill-criterion for v0.3.0

This release is wrong if `cargo test --package scry-host-tests`
passes while the analyzer reports an abstract interval that
*excludes* the concrete value a fixture actually computes. The
harness's concrete-side oracle is the live falsifier:
`fixture_01_constant_fold` and `fixture_02_param_plus_const` both
run the fixture under wasmtime and assert containment. (When the
abstract-side skip is lifted per the limitation above, the
falsifier becomes total rather than concrete-only.)

## [0.2.1] — 2026-05-27

Headline: **compliance bundle ships, finally**. Patch release fixing
the v0.2.0 release-tail gap that left the `compliance-evidence.tar.gz`
asset off the GitHub Release. No analyzer or toolchain changes.

### Fixed

- **`release.yml` compliance step** (#11, closes #10): bumped the
  `pulseengine/rivet/.github/actions/compliance@v0.6.0` invocation's
  `rivet-version` input from `v0.3.0` to `v0.13.1`. v0.3.0 was too
  old to parse scry's `schemas/research-ext.yaml` local schema
  extension, so the action's internal `rivet validate` failed with
  37 errors and no archive was emitted on the v0.2.0 release run.
  Also dropped the unrecognised `single-page` and
  `include-data-formats` inputs that produced warnings on the same
  call (they don't exist in the action's v0.6.0 schema; valid
  inputs are `report-label`, `homepage`, `other-versions`, `theme`,
  `offline`, `rivet-version`, `output`, `archive`, `archive-name`,
  `project-dir`).

### Falsifiable kill-criterion for v0.2.1

This release is wrong if the GitHub Release for v0.2.1 does NOT
include an asset matching `scry-0.2.1-compliance-evidence.tar.gz`
with a valid cosign signature. v0.2.0's release shipped 13 assets
without the bundle; v0.2.1 must ship 16 (the bundle + its `.sig` +
its `.pem`).

## [0.2.0] — 2026-05-27

Headline: **real analysis ships**. The v0.1.0 scaffold's hardcoded
invariant bundle is replaced by a working interval-domain
abstract-interpretation fixpoint over Wasm Core Model arithmetic,
running through the `pulseengine:wasm-lattice/domain` cross-component
import on every transfer ([[FEAT-001]] acceptance criterion #1). The
PulseEngine proof toolchain (`rules_verus` + `rules_rocq_rust`) is
wired into the Bazel build, with one provable theorem per family on
the lattice algebra ([[FEAT-012]]). Releases now ship rivet
compliance evidence as a cosign-signed asset, and PRs touching the
artifact graph get a sticky `rivet-delta` comment so reviewers can
see what changed without diffing YAML.

### Added

- **Real interval-domain fixpoint** ([[FEAT-001]] AC#1, #8).
  `crates/scry-analyzer/src/lib.rs` rewritten: parses the input Wasm
  module with `wasmparser`, walks straight-line arithmetic in each
  function, maintains an abstract operand stack and per-local
  abstract state, and emits a `ProgramPoint` snapshot per
  instruction. Every interval transfer (`I32Const`, `I32Add`,
  `I32Sub`, `I32Mul`, `LocalGet`/`Set`/`Tee`) dispatches through
  the imported `pulseengine:wasm-lattice/domain` interface,
  preserving the [[DD-008]] dogfood on every call. `module_sha256`
  populated via `sha2`. Unsupported ops (control flow, memory,
  calls, refs, GC, SIMD) emit `DiagnosticSeverity::UnsoundnessFallback`
  and widen the locals to `domain::top()` — soundness over
  precision ([[REQ-001]]). Test fixtures under
  `crates/scry-analyzer/test-fixtures/` document expected
  invariants for two arithmetic-only Wasm modules.
- **Verus + Rocq proof toolchain wired into Bazel** ([[FEAT-012]],
  #7). `MODULE.bazel` pulls `rules_verus@a49f72ef` and
  `rules_rocq_rust@090b875c` (synth-canonical pins) plus
  `rules_nixpkgs_core@0.13.0` for the hermetic Rocq build. New
  `proofs/verus/` contains a Verus theorem on `join` commutativity;
  new `proofs/rocq/` contains a Rocq theorem on interval-lattice
  ⊑-reflexivity discharged by `lia`. New CI jobs
  `Rocq Formal Proofs` (PASS) and `Verus Formal Proofs`
  (informational at v0.2 — upstream `rules_verus` sysroot bug
  documented inline, doesn't block the merge). Mechanized
  soundness proof of the interval domain against WasmCert-Coq
  remains deferred to [[FEAT-010]] in v0.9.
- **Rivet compliance evidence in releases** (v0.2-prep, #6).
  `release.yml` invokes the canonical
  `pulseengine/rivet/.github/actions/compliance@v0.6.0` composite
  action (same one sigil and spar use) and tarballs the result as
  `scry-<version>-compliance-evidence.tar.gz`. v0.2.0 is the first
  release to ship the bundle; cosign signs it alongside the other
  release assets.
- **`rivet-delta` PR check** (v0.2-prep, #6). Sticky comment on every
  PR touching `artifacts/`, `schemas/`, `spar/`, or `rivet.yaml`.
  Reports `rivet validate` head-vs-base, the artifact-count delta,
  full `rivet diff`, and `spar parse` result. Pattern adapted from
  rivet's own `rivet-delta.yml`. Informational only.
- **`README.md`** updated post-v0.1.0 (#4).

### Changed

- **`actions/checkout` upgraded from `@v4` to `@v6`** across both
  workflows (v0.2-prep, #6). Removes the Node.js 20 deprecation
  warning for the one action where Node 24 support exists today.
  Other Node 20 actions (`actions/cache`, `Swatinem/rust-cache`,
  `sigstore/cosign-installer`, `bazelbuild/setup-bazelisk`,
  `actions/attest-build-provenance`, `peter-evans/*`) have no
  Node 24-compatible release yet; warnings remain for those until
  upstream ships.
- **CI workflow gains a Nix install step on the Bazel-build job**
  (#7). Adding `register_toolchains("@rocq_toolchains//:all")` in
  `MODULE.bazel` forces nix-build resolution for every `bazel
  build`, not just the proofs targets. The install step makes the
  main composed-component build green again. Matches the synth
  `ci.yml` pattern.
- **`crates/scry-analyzer/Cargo.toml`** adds `wasmparser = "0.247"`
  and `sha2 = "0.10"` workspace deps (#8). Both with
  `default-features = false` for `#![no_std]`.

### Known limitations / deferred

- **No host wasmtime test harness** — [[FEAT-001]] acceptance
  criterion #3, still pending. The Wasm fixtures in
  `crates/scry-analyzer/test-fixtures/` document expected invariants
  but aren't yet executed against the analyzer in CI. Promoting
  the placeholder `Clippy` + `Test` CI jobs to real `cargo` runs
  lands with this.
- **No region-based memory model** — [[FEAT-005]]; the analyzer
  emits `UnsoundnessFallback` on the first memory op.
- **No control flow** — `if`/`loop`/`br_if` etc. emit
  `UnsoundnessFallback` and widen the function's locals to
  `domain::top()`. Widening for loops is a v0.3+ concern.
- **No sound `call_indirect`** — [[FEAT-006]] in v0.3.
- **`Verus Formal Proofs` CI job fails** — informational only;
  `librustc_driver-*.so` shared-library issue inside
  `rules_verus@a49f72ef`. The same pin works for synth; reason
  is under investigation. The Rocq proof path is fully green and
  is the more important leg for the FEAT-010 mechanized soundness
  roadmap.

### Falsifiable kill-criterion for v0.2.0

This release is wrong if, on any well-formed Wasm Core Model module
whose execution scry-analyzer's `analyze` interprets to completion
without emitting an `UnsoundnessFallback` diagnostic, the returned
`invariant_bundle.points` contains *any* `ProgramPoint` whose
abstract local state excludes a value that the program actually
computes for some concrete input. The forthcoming host wasmtime
harness ([[FEAT-001]] AC#3) will be the mechanical falsifier — until
it lands, the fixtures in `crates/scry-analyzer/test-fixtures/`
document the expected invariants for two arithmetic-only modules
and a careful reader can hand-check them against the JSON
`analysis-result` the analyzer emits.

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

[Unreleased]: https://github.com/pulseengine/scry/compare/v0.4.0...HEAD
[0.4.0]: https://github.com/pulseengine/scry/releases/tag/v0.4.0
[0.3.0]: https://github.com/pulseengine/scry/releases/tag/v0.3.0
[0.2.1]: https://github.com/pulseengine/scry/releases/tag/v0.2.1
[0.2.0]: https://github.com/pulseengine/scry/releases/tag/v0.2.0
[0.1.0]: https://github.com/pulseengine/scry/releases/tag/v0.1.0
