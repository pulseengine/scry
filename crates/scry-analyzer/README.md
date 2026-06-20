# scry-sai-analyzer (`scry-analyzer`)

[scry](https://github.com/pulseengine/scry)'s sound WebAssembly analyzer as a
**Wasm component** — the shipped `scry.wasm` (`//:scry`). A thin canonical-ABI
wrapper that exposes the `pulseengine:scry/analyzer` `analyze` function over the
pure [`scry-sai-core`](https://crates.io/crates/scry-sai-core) engine.

This crate is a `cdylib` Wasm component (built via Bazel `rules_wasm_component`),
**not** a crates.io library: it ships as a signed `.wasm` release asset with
SBOMs and a sigil attestation. To use scry as a Rust library, depend on
`scry-sai-core`; to run the analyzer, load the released component in a
WASIp2 host.

License: MIT OR Apache-2.0.
