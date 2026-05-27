# scry-host-tests

Native Rust crate (NOT a Wasm component) that drives the composed
`bazel-bin/scry.wasm` analyzer component end-to-end via a wasmtime
embedding and asserts the v0.2.0 soundness kill-criterion holds on
the in-repo fixtures.

This crate satisfies **FEAT-001 acceptance criterion #3** — the
falsifier the v0.2.0 CHANGELOG promised but only hand-checked.

## What it asserts

The CHANGELOG kill-criterion:

> v0.2.0 is wrong if any program-point in the emitted invariant
> bundle excludes a value the program actually computes for any
> concrete reachable input.

Mechanized here as: for each `.wat` fixture under
`crates/scry-analyzer/test-fixtures/`, the harness

1. assembles the fixture to Wasm bytes (`wat::parse_file`);
2. instantiates the composed scry component in a wasmtime
   `wasmtime::component::Linker` (with WASI added via
   `wasmtime_wasi::add_to_linker_sync`), calls the exported
   `pulseengine:scry/analyzer@0.1.0` interface's `analyze` function
   on those bytes, and parses the returned `analysis-result` via the
   dynamic component `Val` API;
3. instantiates the **same** WAT as a runnable core Wasm module in
   a second wasmtime `Engine` (no WASI, no component model), invokes
   its exported entry point on a battery of concrete inputs;
4. cross-asserts: for every concrete input / abstract `local-
   invariant` pair, the concrete value lies inside the abstract
   interval that scry reported for that local.

If any one of those concrete values escapes its abstract interval,
the test fails — and v0.2.0's soundness claim is mechanically
falsified.

## Why a separate crate

The wasm-component crates (`wasm-lattice`, `scry-analyzer`) are
`crate-type = ["cdylib"]` and depend on Bazel-injected bindings
(`scry_analyzer_component_bindings` produced by
`rules_wasm_component::rust_wasm_component_bindgen`). Those bindings
don't exist on the cargo path, so a host-side `#[test]` cannot live
in the same crate. Splitting the host harness into its own native
crate keeps each side's build self-consistent.

The crate is a workspace member (root `Cargo.toml`'s `[workspace]
members`) so a top-level `cargo build`/`cargo test` picks it up and
so `cargo-bazel`'s `crate.from_cargo` resolves wasmtime, wat, and
the rest from the same lockfile that pins `wasmparser`. The wasmtime
crates resolve only for native triples (cargo-bazel's
`supported_platform_triples` includes the four PulseEngine-supported
host triples); the wasm-component crates never reference them.

## Why dynamic `Val` marshalling instead of `bindgen!`

The canonical scry world at `crates/scry-analyzer/wit/scry.wit`
carries a cross-package `import pulseengine:wasm-lattice/domain@0.1.0`
clause. `wasmtime::component::bindgen!` resolves that import through
a `wit/deps/<package>/<file>.wit` directory layout. The wasm-lattice
WIT file lives at `crates/wasm-lattice/wit/wasm-lattice.wit` — to
make bindgen happy on the cargo path we would have to maintain a
forked copy under this crate's `wit/deps/`. Forks drift.

The dynamic `wasmtime::component::Val` API takes the canonical WIT
shape as given by the composed component's actual exports and matches
against them at call time, so we never need a host-side static copy
of the WIT graph. The cost is some hand-rolled marshalling for the
`analysis-result` record — collected in `tests/soundness.rs` and
narrowly scoped.

If the WIT signature drifts in a way that changes the wire format
(e.g. a new required field on `analysis-result`), the dynamic decode
fails at runtime with a clear error pointing at the missing field
name — same coarse-but-mechanical drift detection a static binding
would give, just deferred from compile time to test time.

## Running

```
bazel build //:scry            # produces bazel-bin/scry.wasm
cargo test --package scry-host-tests
```

Override the component path:

```
SCRY_COMPONENT_PATH=/some/where/else/scry.wasm \
    cargo test --package scry-host-tests
```

If `bazel-bin/scry.wasm` is missing the tests **skip with a notice**
(stderr) instead of failing — `#[ignore]` would skip even when we
wanted to run, which defeats CI's whole point. CI's `Test` job runs
`bazel build //:scry` first so the component is always present by
the time `cargo test` is invoked.

## Why three tests instead of one big one

`composed_component_loads` is a fast triage signal: if wasmtime
can't even load the component the per-fixture tests don't add useful
diagnostic, they all fail the same way. The two `fixture_*` tests
are independent so a regression on one fixture doesn't mask
regressions on the other.

## Scope limits (v0.2 AC#3)

The analyzer's v0.2 WIT only emits per-`program-point` **locals**
snapshots — the abstract operand stack is not part of the WIT yet
(FEAT-008's loom integration will add it). So the soundness oracle
here can only cross-check locals against concrete locals (which for
both current fixtures is just the parameter list). When the WIT
extends to expose the abstract operand stack, the oracle here
extends to also cross-check function return values against the final
top-of-stack interval — no rewriting of the existing soundness
assertion path required.
