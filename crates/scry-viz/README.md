# scry-sai-viz

Static-HTML visualization of a [scry](https://github.com/pulseengine/scry)
`AnalysisResult` — the analyzer's own analogue of the witness-viz MC/DC
truth-table site, but for scry's static-analysis output.

Part of [scry](https://pulseengine.eu): a sound Wasm static analyzer. This is
a plain `std` host tool (binary `scry-viz` + library `scry_viz`) that consumes
the published analyzer library [`scry-sai-core`](https://crates.io/crates/scry-sai-core)
— no WIT, no component, no `wasmtime`.

## What it renders

A single self-contained HTML page (no server, no JavaScript, no external
assets) with:

- **Summary** — module SHA-256, schema, worst-case shadow-stack bound,
  stack-pointer global, and headline counts.
- **Functions** — per function: reachable-from-exports? · recursive? · params ·
  shadow-stack frame · worst-case stack.
- **Call graph** — caller · pc · `call`/`call_indirect` · resolved target set ·
  soundness tag.
- **Diagnostics** — severity · `fn:pc` · message.
- **Program points** — for each visited `(func, pc)`, the abstract `locals`
  *and* the abstract **operand stack** (bottom → top). A singleton interval
  shows as a bare constant (`i32 42`), the full domain as `⊤`, and an empty
  operand stack as an explicit `(empty)`.

## Usage

```bash
cargo install scry-sai-viz
scry-viz module.wasm                 # writes module.html
scry-viz module.wat -o report.html   # .wat is assembled in-process
scry-viz module.wasm --title "my firmware"

# Build a landing page linking the dashboard views present in a site dir
# (the analogue of `witness-viz pages-index`):
scry-viz index --site-dir dist --title "scry — verification dashboard"
```

scry uses this to publish a verification dashboard to GitHub Pages on every
release (`pulseengine.github.io/scry/`): a landing page linking the scry-viz
self-analysis (scry analyzing its own module) and the witness-viz MC/DC
truth-table dashboard.

Library:

```rust
use scry_analyze_core::{analyze, AnalysisConfig};

let result = analyze(wasm_bytes, AnalysisConfig::default())?;
let html = scry_viz::render_html(&result, "my-module");
std::fs::write("report.html", html)?;
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Soundness posture

scry-viz is a **faithful rendering**: it re-derives nothing and asserts nothing
beyond what the `AnalysisResult` already states. Every value shown is a verbatim
projection of an analyzer field. An empty operand-stack renders as `(empty)` —
the analyzer's honest "no operand-stack info here" (e.g. at a write-set-havoc
point), never a claim that the concrete stack is empty. Attacker-influenced
strings (diagnostic messages, schema URL, module name) are HTML-escaped.

License: MIT OR Apache-2.0.
