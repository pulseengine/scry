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

## How the host harness uses these fixtures

As of FEAT-001 AC#3 (the `crates/scry-host-tests` crate), the host
wasmtime harness consumes every `.wat` here twice on every CI run:

1. **Abstract side** — assemble the `.wat` to Wasm bytes with
   `wat::parse_file`, pass them to the composed scry component's
   `analyzer.analyze` function in a `wasmtime::component::Linker`,
   and decode the returned `analysis-result` via the dynamic
   component `Val` API.
2. **Concrete side** — instantiate the same `.wat` as a runnable
   core Wasm module in a second wasmtime engine, call the fixture's
   exported entry point with hand-picked inputs, and capture the
   actual i32 result.

The harness then cross-asserts that every concrete input lies inside
the matching abstract `local-invariant` interval — a mechanical
falsifier for the v0.2.0 CHANGELOG kill-criterion. If a future
fixture's concrete output ever escapes its abstract interval, the
soundness theorem is mechanically refuted and CI goes red on that
exact fixture.

The fixture format is therefore frozen on two dimensions:

* The `.wat` file must export a function named in the harness's
  fixture table (`compute` for fixture-01, `doit` for fixture-02).
* The exported function must return a single `i32` so the dynamic
  result decoder doesn't need a per-fixture signature.

If you add a fixture that breaks either invariant, add a matching
fixture entry to `crates/scry-host-tests/tests/soundness.rs` rather
than working around it here.

## Files

| file                              | purpose                                                  |
|-----------------------------------|----------------------------------------------------------|
| `fixture-01-constant-fold.wat`    | pure constant folding: `(10 + 32) * 2 = 84`              |
| `fixture-01-constant-fold.md`     | expected per-instruction operand-stack state             |
| `fixture-02-with-param.wat`       | unknown parameter + constant: result is top              |
| `fixture-02-with-param.md`        | expected per-instruction operand-stack state             |
| `fixture-03-region-bounds.wat`    | v0.3 region-aware `i32.load` on a constant base+offset   |
| `fixture-03-region-bounds.md`     | expected operand-stack + diagnostic surface              |
| `fixture-04-call-indirect.wat`    | v0.4 sound `call_indirect`: constant + unconstrained idx |
| `fixture-04-call-indirect.md`     | expected call-graph edges + diagnostic surface           |
| `fixture-05-interproc.wat`        | v0.5 summary-based interproc: `add_one(41)` → `{42,42}`  |
| `fixture-05-interproc.md`         | expected summaries + context-sensitive re-eval + recursion |
| `fixture-07-bounded-local.wat`    | v1.3 (FEAT-015) non-vacuous oracle: local set to const 100 ⇒ bounded `[100,100]` |
| `fixture-08-counted-loop.wat`     | v1.4 (FEAT-016 slice-1) loop fixpoint: loop-invariant local `k=42` must survive the loop (today scrubbed) |
| `fixture-09-loop-converge.wat`    | v1.5 (FEAT-016 slice-2a) real loop fixpoint: loop-written `m` converges to bounded `[0,7]` (vs slice-1 havoc ⊤) |
| `fixture-10-guard-bound.wat`      | v1.6 (FEAT-016 slice-2b-i) guard refinement: guard-bounded counter `i` converges to bounded `[0,10]` (vs slice-2a widen-to-⊤) |
| `fixture-11-var-bound.wat`        | v1.8 (FEAT-016 slice-2b-ii) octagon product: counter bounded by a VARIABLE relation `i<n` (n in a local) converges to `[0,10]` (vs interval/const-guard widen-to-⊤) |
| `fixture-12-stack-chain.wat`      | v1.10 (FEAT-021 slice-1) shadow-stack bound: 3-deep call chain, frames 16/32/8 → worst-case 56 bytes (sound) |
| `fixture-13-stack-recursion.wat`  | v1.10 (FEAT-021 slice-1) shadow-stack: self-recursion (call-graph SCC) → UNBOUNDED, never a finite under-count |
| `fixture-14-stack-dynamic.wat`    | v1.10 (FEAT-021 slice-1) shadow-stack: dynamic (variable) frame → UNKNOWN, never zero |

## Adding fixtures

Each fixture is one `.wat` file (Wasm Core Model only, no component
type) plus one adjacent `.md` with two sections:

1. **Source** — verbatim copy of the `.wat`.
2. **Expected post-analysis state** — per-instruction table of the
   operand stack and locals after each instruction, matching the
   v0.2 AC#1 transfer functions plus v0.3 (FEAT-005) memory ops.

Keep fixtures inside the v0.3 supported instruction set:

* **Arithmetic core** (v0.2 AC#1): `i32.const`, `i64.const`,
  `local.get`, `local.set`, `local.tee`, `i32.add`, `i32.sub`,
  `i32.mul`, `end`, `return`.
* **Region-aware memory** (v0.3 FEAT-005, when the address operand
  is a singleton i32 interval — the canonical base+offset pattern):
  `i32.load`, `i32.store`, `i64.load`, `i64.store`. The fixture's
  `.md` should record whether each memory op is expected to emit
  an `Info` (bounds-check elision safe) or `Warning` (cannot
  prove in-region) diagnostic. Non-singleton addresses still
  hit the v0.2 fallback (`UnsoundnessFallback` + locals scrubbed
  to top), which is also a valid thing to demonstrate.
* **Call-graph** (v0.4 FEAT-006): `call` (direct, single-target
  edge) and `call_indirect` (resolved via the parsed table + the
  top-of-stack index interval). The fixture's `.md` should record
  the expected `call-graph` edges (caller / pc / resolved-targets /
  soundness) and whether each `call_indirect` emits an `Info`
  (constrained index, precise) or `Warning` (unconstrained index,
  whole-table over-approximation). Neither emits
  `UnsoundnessFallback`; neither scrubs locals.
* **Interprocedural summaries** (v0.5 FEAT-007): a `call` to a small
  non-recursive callee with concrete argument intervals now applies a
  context-sensitive re-evaluation of the callee and pushes the precise
  result interval (instead of v0.4's `top`); other callees use the
  sound context-insensitive `top`-summary. Recursive callees (in a
  non-trivial call-graph SCC) always use the `top`-summary,
  guaranteeing termination. The fixture's `.md` should record the
  expected `function-summaries` records (func-index / param-count /
  result-summary / context-sensitive / recursive) and the call-site
  result interval.

Anything else hits the fallback path which should be called out
explicitly in the `.md`.
