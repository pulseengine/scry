# scry-sai-provenance

The **component-provenance boundary** between
[meld](https://pulseengine.eu) and [scry](https://github.com/pulseengine/scry).
Part of the `scry-sai-*` (Sound Abstract Interpretation) family.

A pure, `#![no_std]`, dependency-free crate: encode / decode / project the
`component-origin` map that meld emits in a fused Core Wasm module's custom
section, so scry can attribute a fused-module function back to its originating
component instance. The round-trip is the contract that lets scry report
findings in component-level terms.

Compiles natively and to `wasm32` (the shipped scry component links this code).
Imported as `scry_provenance`.

License: MIT OR Apache-2.0.
