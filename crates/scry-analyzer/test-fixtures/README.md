# scry-analyzer test fixtures

In-repo Wasm Core Model fixtures plus expected post-analysis
documentation. These are the worked examples that pin down the v0.2
(FEAT-001 AC#1) abstract-interpretation semantics in concrete cases.

## Why they're documentation rather than tests (yet)

v0.2 ships the analyzer-side of FEAT-001 AC#1 only. The Wasm-host
harness that drives the composed component end-to-end and asserts on
the returned `analysis-result` (the `crates/scry-host-tests` crate
named in FEAT-001 AC#3) lands in a separate PR — Bazel doesn't
currently expose a way to spin up wasmtime + call into a composed
component as a `cargo test`-style assertion against a fixture, so the
end-to-end loop is deferred.

Until that lands, these `.wat` files plus their adjacent `.md` docs
serve three roles:

1. **Spec by example** — they make the supported instruction set and
   the expected interval-lattice behaviour readable, in one place,
   without anyone having to read the analyzer source.
2. **Sanity oracle** — anyone hand-running `wasmtime` against the
   composed component can paste a fixture in, eyeball the diagnostics,
   and check the result against the `.md`.
3. **Drop-in fixtures** for the FEAT-001 AC#3 host harness when it
   lands: no edits to these files; the harness just loads them via
   `wat::parse_str` and asserts on the `analysis-result`.

## Files

| file                              | purpose                                       |
|-----------------------------------|-----------------------------------------------|
| `fixture-01-constant-fold.wat`    | pure constant folding: `(10 + 32) * 2 = 84`   |
| `fixture-01-constant-fold.md`     | expected per-instruction operand-stack state  |
| `fixture-02-with-param.wat`       | unknown parameter + constant: result is top   |
| `fixture-02-with-param.md`        | expected per-instruction operand-stack state  |

## Adding fixtures

Each fixture is one `.wat` file (Wasm Core Model only, no component
type) plus one adjacent `.md` with two sections:

1. **Source** — verbatim copy of the `.wat`.
2. **Expected post-analysis state** — per-instruction table of the
   operand stack and locals after each instruction, matching the
   v0.2 AC#1 transfer functions.

Keep fixtures inside the v0.2 AC#1 supported instruction set:
`i32.const`, `i64.const`, `local.get`, `local.set`, `local.tee`,
`i32.add`, `i32.sub`, `i32.mul`, `end`, `return`. Anything else
hits the fallback path (UnsoundnessFallback diagnostic + locals
degraded to top) which is also a valid thing to demonstrate but
should be called out explicitly in the `.md`.
