# scry-sai-provenance

The **component-provenance boundary** between
[meld](https://pulseengine.eu) and [scry](https://github.com/pulseengine/scry).
Part of the `scry-sai-*` (Sound Abstract Interpretation) family.

A pure, `#![no_std]`, dependency-free crate: encode / decode / project the
`component-origin` map that meld emits in a fused Core Wasm module's custom
section, so scry can attribute a fused-module function back to its originating
component instance. The round-trip is the contract that lets scry report
findings in component-level terms.

The wire format is the strict little-endian binary **`SCPV` v3** (scry#63 /
meld#313): the canonical shape both meld (producer) and scry (consumer) build
to. v3 carries, in the section, the **fusion premises** meld knows by
construction — `bounded_memory` and `closed_world` — a `fused_module_sha256`
binding, a UTF-8 `component_id`, and an optional per-entry `code_range`. The
decoder is strict: a bad magic, unknown version, malformed flag, non-UTF-8 id,
truncation, or trailing bytes is a hard error, never a partial parse.

Compiles natively and to `wasm32` (the shipped scry component links this code).
Imported as `scry_provenance`.

License: MIT OR Apache-2.0.
