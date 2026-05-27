//! scry-host-tests — native wasmtime harness for the composed scry
//! Wasm component (FEAT-001 AC#3).
//!
//! The crate is a stub on purpose. The real harness lives in
//! `tests/soundness.rs` so it runs under `cargo test` without
//! needing any runtime consumer of a library API.
//!
//! Why a separate crate at all (rather than `cargo test` inside
//! `scry-analyzer`): the wasm component crates compile as
//! `crate-type = ["cdylib"]` to the `wasm32-wasip2` target and
//! depend on Bazel-injected bindings (the
//! `scry_analyzer_component_bindings` crate produced by
//! `rules_wasm_component::rust_wasm_component_bindgen`). Those
//! bindings don't exist on the native cargo path, so a host-side
//! `#[test]` cannot live in the same crate. Splitting the host
//! harness into its own native crate keeps each side's build
//! self-consistent.
//!
//! What this crate verifies — the v0.2.0 kill-criterion:
//!
//!     v0.2.0 is wrong if any program-point in the emitted
//!     invariant bundle excludes a value the program actually
//!     computes for any concrete reachable input.
//!
//! `tests/soundness.rs` mechanizes that check on the in-repo
//! fixtures from `crates/scry-analyzer/test-fixtures/`: each
//! fixture is run twice — once through the scry analyzer (via the
//! composed `bazel-bin/scry.wasm` component) to get an abstract
//! invariant bundle, and once as a concrete wasm module under
//! wasmtime to get a real output value. The harness then asserts
//! that every concrete output lies inside the matching abstract
//! interval.

#![forbid(unsafe_code)]
