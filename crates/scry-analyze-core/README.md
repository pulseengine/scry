# scry-sai-core

The pure, bindgen-free **analyzer core** of
[scry](https://github.com/pulseengine/scry) — a sound static analyzer for
WebAssembly. The reusable engine behind the `scry-sai-*` (Sound Abstract
Interpretation) family.

`#![no_std]` and free of WIT/component bindings, it holds scry's real analysis
decisions over the Wasm Core Model: the `wasmparser` parse, the structured-CFG
interval + region-memory fixpoint (with loop widening/narrowing and the octagon
relational product), the call graph (direct + over-approximated `call_indirect`)
with Tarjan-SCC condensation and bottom-up summaries, the taint
(noninterference) walk, and the FEAT-021 worst-case shadow-stack bound. Results
are plain Rust types (`AnalysisResult`: invariants, call graph, summaries,
taint findings, stack usage).

This is the exact code the shipped `scry.wasm` component runs (it is a thin
canonical-ABI wrapper around this crate) and that `witness` instruments for
MC/DC. Depends on the pure `scry-sai-interval` / `-taint` / `-octagon` /
`-provenance` domain crates. Imported as `scry_analyze_core`.

License: MIT OR Apache-2.0.
