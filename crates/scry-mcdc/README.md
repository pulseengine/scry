# scry-mcdc — witness MC/DC over the real analyzer core (FEAT-014 / DD-012)

This crate measures **modified-condition/decision coverage** on the
analyzer's *real* decision logic — the same [`scry_analyze_core::analyze`]
body the shipped component runs (DD-012 extracted it into that pure crate so
it could be instrumented) — driven over the in-repo corpus fixtures.

It closes the witness step of the original scry feature loop, blocked since
v0.1 by the composition gap (the shipped artifact didn't contain a runnable
analyzer; FEAT-013/DD-011 fixed that, FEAT-014/DD-012 made it measurable).

## How it works

`witness` reconstructs an MC/DC independence pair for a condition only when
it sees that condition flip across executions with the other shared
conditions held (masking) and the outcome differing. A single no-arg export
is one fixed execution — one truth-table row — so no pair is possible.
(That is exactly why the v1.2 spike that swept *synthetic* domain inputs
proved zero conditions.)

So each `run_*` export in `src/lib.rs` drives the **same** `analyze` entry
over a different `(fixture, config)` pair. Five structurally different
fixtures — constant-fold, a bounded param, region/bounds, `call_indirect`,
interprocedural summaries — crossed with config variants (taint on/off,
diagnostics on/off, widening threshold 1 vs 3) hit the branchy decisions
inside `analyze` / `interpret_op` / the transfer functions / `run_taint_-
analysis` with genuinely varied operands. `witness run --invoke-all` calls
every export and accumulates the per-branch counters across all of them, so
flipping pairs exist for the decisions the corpus exercises.

The fixtures are baked in as pre-assembled core-Wasm bytes (the `.wat`
sources under `crates/scry-analyzer/test-fixtures/`, assembled with
`wasm-tools parse`); the harness owns no analysis logic of its own.

## Run it

```sh
WITNESS_BIN=/path/to/witness ./build-and-measure.sh
```

Builds the harness to `wasm32-wasip1` (debug=2, opt-level=1 — the wasi-sdk
linker preserves the DWARF line rows witness clusters into source-level
decisions, which the `wasm32-unknown-unknown` linker drops under inlining),
then `witness instrument` → `run --invoke-all` → `report --format mcdc`.
Read `evidence/report.json` (the canonical `witness-mcdc/v3` truth table) for
the authoritative gap rows — not the human stdout.

## Result (witness-mcdc/v3, witness 0.28.x; evidence/report.json)

The pipeline runs end-to-end over the **real** analyzer core and the **real**
corpus. witness reconstructs **662 source-level decisions** and proves
**119 conditions under MC/DC** (4 decisions at full MC/DC) — including
conditions inside the soundness-critical interval transfer functions.

This is the headline change from the v1.2 spike: instrumentation +
DWARF attribution + decision reconstruction + MC/DC proving all function
over the shipped logic, where the synthetic-domain prototype proved zero.
`trace_health.rows = 0` is harmless here (witness reconstructs from the
per-branch globals counters, not the trace buffer — 119 proved conditions
confirm it).

### Gap-closure applied (the v1.2 cycle)

Two closure levers were applied and are baked into this crate / scry-interval:

1. **`#[inline(never)]` on the scry-interval transfer functions** (DD-012):
   `i32_add` / `i32_sub` / `i32_mul` / `region_offset` keep standalone DWARF
   clusters rather than being folded into the core's `i32_binop` call site.

2. **`fixture-06-overflow`** drives the transfer functions' straddle→TOP
   guard `lo < i32::MIN || hi > i32::MAX` to its TRUE polarity (large-
   magnitude add/sub/mul that over/underflow i32). The rest of the corpus
   only ever evaluates that OR `(F,F)`; adding the `(T,F)`/`(F,T)` vectors is
   what MC/DC needs for the independent-effect pair. This raised proved
   conditions 114 → 119 and full-MC/DC decisions 3 → 4.

### Honest scope — residual gaps (FEAT-014 AC#1 escape hatch)

Not every safety-relevant condition is yet at full MC/DC. Named residuals:

1. **Some transfer-fn straddle decisions remain `no_witness`/`gap`.** A given
   source line (e.g. the `i32_mul` straddle, scry-interval `lib.rs:184`-ff)
   maps to several instrumented decision instances; the overflow fixture now
   executes the TRUE branch, but witness does not yet pair every instance.
   Closing approach: drive each instance with `--invoke-with-args` realizing
   the exact `gap_closure` vector witness prints per gap row in
   `report.json`, or split the straddle into two single-condition guards so
   each is a one-instance decision.

2. **A few `i32_add`/`i32_sub` straddle clusters still show `unreached`.**
   The corpus reaches the functions but not those specific instance copies.
   Same closing approach as (1).

The `dead` (~2791) / `unreached` (~437) bulk is std / wasi-libc / wasmparser
internal code linked into the harness module — outside the analyzer's
decision surface and not safety-relevant.

## Evidence artifacts (`evidence/`)

| file | what |
|------|------|
| `report.json` | canonical MC/DC truth table (`witness-mcdc/v3`) — committed |
| `mcdc-predicate.json` | unwrapped in-toto Statement (`witness-mcdc/v3`) carrying the truth tables + a sha256 binding to the report — the FEAT-014 AC#2 coverage-predicate body, which sigil wraps + signs at release time. Regenerate with `witness predicate --run evidence/run.json --module evidence/scry-mcdc.instrumented.wasm --kind mcdc` (gitignored — large + regenerable) |
| `run.json`, `*.instrumented.wasm`, `*.witness.json` | regenerable intermediates (gitignored) |
