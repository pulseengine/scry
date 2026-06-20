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

## Usage

The normal API: call `analyze` with a Core Wasm module's bytes and an
`AnalysisConfig`; get back an `AnalysisResult` of plain Rust types — no WIT,
no component, no `wasmtime`.

```toml
[dependencies]
scry-sai-core = "1"
```

```rust
use scry_analyze_core::{analyze, AnalysisConfig};

// `wasm` is a Core Wasm module (Vec<u8>). `AnalysisConfig::default()` =
// default widening, no diagnostics, no taint policy.
let r = analyze(wasm, AnalysisConfig::default())?;

for e in &r.call_graph {
    // e.indirect, e.resolved_targets: Vec<u32> (a sound over-approximation
    // for call_indirect), e.soundness — e.g. fold edges into a longest-path.
}
let has_cycle = r.function_summaries.iter().any(|s| s.recursive); // honest-fail gate
let reachable = &r.reachable_from_exports; // sound superset; prune anything absent
let stack = r.stack_usage.max_stack_bytes;  // Bytes(n) | Unbounded | Unknown
# Ok::<(), scry_analyze_core::AnalyzeError>(())
```

`AnalysisConfig` exposes `widening_threshold`, `emit_diagnostics`, and an
optional `taint_policy` if you need them. The crate is `#![no_std]` (over
`alloc`) — a fine dependency for a `std` tool. The soundness contract on the
call-graph / reachability output (the over-approximation a consumer's bound
relies on) is REQ-011 / SCRY-001.

License: MIT OR Apache-2.0.
