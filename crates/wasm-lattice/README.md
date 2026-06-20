# scry-sai-lattice (`wasm-lattice`)

The interval/relational abstract-domain algebra exposed as a **Wasm component**
(the `pulseengine:wasm-lattice/domain` WIT interface) — the DD-008 cross-component
"dogfood" of [scry](https://github.com/pulseengine/scry)'s domains.

This crate is a `cdylib` Wasm component (built via Bazel `rules_wasm_component`),
**not** a crates.io library: it ships as a signed `.wasm` release asset. The
reusable algebra it delegates to is published as the pure
[`scry-sai-interval`](https://crates.io/crates/scry-sai-interval) /
[`scry-sai-octagon`](https://crates.io/crates/scry-sai-octagon) /
[`scry-sai-taint`](https://crates.io/crates/scry-sai-taint) crates.

License: MIT OR Apache-2.0.
