# fixture-05-interproc

Compositional summary-based interprocedural abstract interpretation —
the Stiévenart & De Roover SCAM 2020 technique (AC-010) that FEAT-007
ships. v0.4 (FEAT-006) resolved the call *graph* soundly but modelled
call *effects* pessimistically: on any `call` / `call_indirect` it
popped the callee's params and pushed `top` per result. So
`main() = add_one(41)` yielded `top` even though the precise answer is
`{42, 42}`.

v0.5 (FEAT-007) computes a **per-function abstract summary** for every
function — a sound transfer function over-approximating every concrete
input→output behaviour — bottom-up over the (sound) call graph, and
applies it at each call site. For small non-recursive callees with
concrete argument intervals it goes one better and re-evaluates the
callee with the actual arguments bound to its params (context-sensitive
re-eval), recovering full precision at the call site.

## Source

```wat
(module
  (type (;0;) (func (param i32) (result i32)))
  (type (;1;) (func (result i32)))
  (func $add_one (;0;) (type 0) (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add)
  (func $main (;1;) (export "main") (type 1) (result i32)
    i32.const 41
    call $add_one)
  (func $factorial (;2;) (export "factorial") (type 0) (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.sub
    call $factorial
    local.get 0
    i32.mul))
```

## Function-index layout

No imports, so absolute index == defined index:

| func | export      | signature       | body                                  |
|------|-------------|-----------------|---------------------------------------|
|  0   | —           | `(i32) -> i32`  | `x + 1` (small, non-recursive leaf)   |
|  1   | `main`      | `() -> i32`     | `add_one(41)`                         |
|  2   | `factorial` | `(i32) -> i32`  | self-recursive `n * factorial(n-1)`   |

## Two-phase analysis

* **Phase 1 — bottom-up summary computation.** Build the call-graph
  SCC condensation (Tarjan) from the FEAT-006 edges and process SCCs
  in reverse-topological order (callees before callers): `add_one`,
  then `main`, then `factorial` (a singleton SCC with a self-loop).
  For each function run the intraprocedural fixpoint with parameters
  bound to `top` and record the per-result abstract value. Because
  callees are summarised first, a parameterless caller like `main`
  records the precise interprocedural result in its own summary.
* **Phase 2 — the real per-function walk.** Identical to v0.4 except
  at each `call` site the callee's summary (or, for a small
  non-recursive callee with concrete args, a context-sensitive
  re-evaluation) is applied instead of pushing `top`.

## The headline win: `main() = add_one(41)`

`add_one` is small (3 ops ≤ 64) and non-recursive, so its summary is
flagged **context-sensitive**. Its context-insensitive (`top`-input)
summary is `top -> top` (because `top + 1 = top`), which would not
help — so at the call site scry re-evaluates `add_one` with the
**actual** argument interval `{41, 41}` bound to param 0:

```
local.get 0  ->  {41, 41}
i32.const 1  ->  {1, 1}
i32.add      ->  {42, 42}
```

and pushes `{42, 42}` as the call result. The before/after:

| version | result of `add_one(41)` at the call site in `main` |
|---------|----------------------------------------------------|
| v0.4    | `top` (pessimistic — pop param, push top per result) |
| v0.5    | `{42, 42}` (context-sensitive re-evaluation)       |

### `main` operand-stack + locals state (phase 2)

`main` (func 1, no params, no locals):

| pc | op             | operand stack after | locals |
|----|----------------|---------------------|--------|
| 0  | `i32.const 41` | `[ {41,41} ]`       | `[]`   |
| 1  | `call $add_one`| `[ {42,42} ]`       | `[]`   |
| 2  | `end`          | `[ {42,42} ]`       | `[]`   |

## Recursion handling: `factorial`

`factorial` calls itself, so it sits in a **non-trivial call-graph
SCC** (a single node with a self-edge). It is flagged `recursive`,
uses the sound **context-insensitive `top`-summary**, and is **never**
re-evaluated context-sensitively. Its summary result is `top`
(sound — `factorial` of an arbitrary `top` input can be anything),
and the self-call inside its body applies that same `top`-summary
rather than descending — so the analysis terminates.

This is what makes the interprocedural analysis **provably
terminating**:

1. Re-evaluation is triggered *only* for callees flagged
   `context-sensitive`, which by construction are *not* `recursive`.
   A non-recursive callee cannot be part of a call cycle, so
   re-evaluating it descends strictly down the DAG of non-recursive
   functions.
2. A hard **call-depth backstop** (`REEVAL_MAX_DEPTH = 8`) caps
   re-evaluation depth even if SCC detection ever missed an edge —
   beyond it a `call` falls back to the context-insensitive summary
   (sound).
3. A **op-count threshold** (`REEVAL_MAX_OPS = 64`) excludes large
   callees from re-evaluation (they use the context-insensitive
   summary), bounding per-site re-analysis cost.

All three bounds default to the sound context-insensitive summary, so
the worst case is imprecision, never non-termination or unsoundness.

## Expected `function-summaries` records

`analysis-result.function-summaries` contains one record per defined
function:

| func | param-count | result-summary | context-sensitive | recursive |
|------|-------------|----------------|-------------------|-----------|
| 0 (`add_one`)   | 1 | `[ top ]`      | true  | false |
| 1 (`main`)      | 0 | `[ {42,42} ]`  | true  | false |
| 2 (`factorial`) | 1 | `[ top ]`      | false | true  |

`add_one`'s recorded summary is the context-insensitive `top -> top`
(the precise `{42,42}` only materialises at a call site with concrete
args, via re-eval); `main`'s recorded summary is already precise
because its single "input context" is the empty argument list and the
phase-1 fixpoint of `main` re-evaluates `add_one(41)`; `factorial`'s
summary is the sound `top`.

## Concrete-side oracle

The two exported entry points run as a core Wasm module:

| call            | concrete result | abstract (scry)        | sound? |
|-----------------|-----------------|------------------------|--------|
| `main()`        | `42`            | `{42, 42}`             | yes (42 ∈ {42,42}) |
| `factorial(0)`  | (recursive)     | `top`                  | yes (anything ∈ top) |

`main()` is the mechanical end-to-end check: the concrete value `42`
lies inside the abstract interval `{42, 42}` scry inferred
interprocedurally — soundness *and* full precision. (`factorial`'s
concrete oracle is omitted because the WAT recurses unconditionally;
its role here is to pin the recursion/termination behaviour of the
analysis, not a terminating concrete run.)

## Soundness argument

For any function `f` and abstract arguments `args`:

`summary_f(args)` over-approximates `{ f(concrete) : concrete ∈ γ(args) }`
because it is the result of the intraprocedural fixpoint (sound per
FEAT-001 AC#1) run with the params bound to `args`, and widening at
recursion frontiers guarantees the fixpoint terminates at a sound
post-fixpoint. Applying `summary_f` at a call site is sound because the
call-site argument abstract values are themselves sound abstractions of
the concrete arguments (interval-domain soundness, FEAT-001 AC#1). The
whole construction reduces to intraprocedural soundness + widening
termination.

For `call_indirect` (not exercised by this fixture but supported): when
the index resolves to a known target set, scry pushes the **join** of
the targets' context-insensitive summaries — sound because the runtime
dispatches exactly one target and the join over-approximates every
candidate.

## What this fixture intentionally does NOT cover

- **Full polyvariant context-sensitivity.** v0.5 keeps one summary per
  function (the context-insensitive one) plus on-demand re-eval at
  call sites; it does not cache a distinct summary per distinct
  abstract-argument tuple.
- **Cross-component summaries.** Summaries are computed within one
  module; the meld-fused multi-component case is future work.
- **Context-sensitive re-eval through `call_indirect` or into
  recursive / oversized callees.** Those always use the sound
  context-insensitive summary.

## Cross-references

- `crates/scry-analyzer/wit/scry.wit` — the new `function-summary`
  record and `analysis-result.function-summaries` field.
- `crates/scry-analyzer/src/lib.rs` — the two-phase analysis:
  `build_static_call_graph`, `tarjan_sccs`, `recursive_flags_from_sccs`,
  `run_function_body`, `handle_call` (summary application +
  context-sensitive re-eval), `emit_call_indirect_edge` (target-summary
  join), `extract_results`.
- `artifacts/requirements.yaml#FEAT-007` — acceptance criteria
  citing this fixture; status flipped `proposed → draft`, tagged
  `v0.5`.
- `spar/scry.aadl` — the `FunctionSummary` / `FunctionSummaries` data
  types and the `summaries_out` port.
