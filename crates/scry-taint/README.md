# scry-sai-taint

The **security-label (taint) lattice** for [scry](https://github.com/pulseengine/scry)'s
noninterference analysis. Part of the `scry-sai-*` (Sound Abstract
Interpretation) family.

A pure, `#![no_std]`, dependency-free crate: the two-point `Low ⊑ High` lattice
with its `join`, used by scry's information-flow / noninterference pass to track
whether a `High` (secret) value can reach a `Low` (public) sink. Forward
propagation never moves down the lattice — the algebraic kill-criterion is
exhaustively checked.

Compiles natively and to `wasm32` (the shipped scry component links this code).
Imported as `scry_taint`.

License: MIT OR Apache-2.0.
