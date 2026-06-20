# scry-sai-interval

The **interval abstract domain** for [scry](https://github.com/pulseengine/scry) —
a sound static analyzer for WebAssembly. Part of the `scry-sai-*` (Sound
Abstract Interpretation) family.

A pure, `#![no_std]`, dependency-free crate holding the *algebra* of the interval
lattice over `i32`/`i64` and region pointers: `join` (⊔), `meet` (⊓), `widen`
(ascending-chain termination), `leq` (the Galois order ⊑), `top`/`bottom`, and
the constant + arithmetic transfer functions. All arithmetic is saturating —
a bound never silently wraps.

It compiles both natively and to `wasm32` (the shipped scry analyzer component
links exactly this code), and its soundness (γ-based over-approximation) is
mechanized admit-free in Rocq (`proofs/rocq/Soundness.v`).

Consumed by [`scry-sai-core`](https://crates.io/crates/scry-sai-core); the Rust
crate is imported as `scry_interval`.

License: MIT OR Apache-2.0.
