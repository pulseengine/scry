# fixture-04-call-indirect

Sound `call_indirect` target resolution via value-domain abstract
interpretation of the operand stack — the Paccamiccio et al. 2024
technique (AC-008) that FEAT-006 ships. v0.3 punted on
`call_indirect`: it produced an `UnsoundnessFallback` diagnostic and
scrubbed all locals to `top`. v0.4 (FEAT-006) parses the table +
active element segments in the pre-pass to build the function table,
then resolves each `call_indirect` to a sound target set from the
top-of-stack index interval intersected with the table bounds.

This fixture pins both resolution regimes in one module:

* **constant index → precise.** `dispatch_const` pushes the literal
  `1`; the index interval is the singleton `{1}`, so the resolved
  set is exactly `{table[1]} = {func 1}`. One target, `Info`
  diagnostic, edge tagged `sound`.
* **unconstrained index → whole-table over-approximation.**
  `dispatch_unknown` pushes its i32 parameter (abstract value
  `top`); the analyzer cannot constrain the index, so it
  over-approximates to the whole 3-entry table `{0, 1, 2}`. Three
  targets, `Warning` diagnostic ("index unconstrained — 3 targets"),
  edge still tagged `sound` — an over-approximation is sound (it
  never drops a concretely reachable target).

## Source

```wat
(module
  (type (;0;) (func (result i32)))
  (type (;1;) (func (param i32) (result i32)))
  (table (;0;) 3 3 funcref)
  (elem (;0;) (i32.const 0) func 0 1 2)
  (func (;0;) (type 0) (result i32) i32.const 100)
  (func (;1;) (type 0) (result i32) i32.const 200)
  (func (;2;) (type 0) (result i32) i32.const 300)
  (func (;3;) (export "dispatch_const") (type 0) (result i32)
    i32.const 1
    call_indirect (type 0))
  (func (;4;) (export "dispatch_unknown") (type 1) (param i32) (result i32)
    local.get 0
    call_indirect (type 0)))
```

## Function-index layout

No imports, so absolute index == defined index:

| func | export             | signature                      | body                       |
|------|--------------------|--------------------------------|----------------------------|
|  0   | —                  | `() -> i32`                    | `i32.const 100`            |
|  1   | —                  | `() -> i32`                    | `i32.const 200`            |
|  2   | —                  | `() -> i32`                    | `i32.const 300`            |
|  3   | `dispatch_const`   | `() -> i32`                    | const index 1, `call_indirect` |
|  4   | `dispatch_unknown` | `(i32) -> i32`                 | param index, `call_indirect`   |

## Function table (parsed in the pre-pass)

`(table 3 3 funcref)` → declared length 3, maximum 3 (non-growable,
so `contents_known = true`). One active element segment at constant
offset 0 with funcs `[0, 1, 2]`:

| table slot | resolved func |
|------------|---------------|
| 0          | 0             |
| 1          | 1             |
| 2          | 2             |

## Expected call-graph edges

The `analysis-result.call-graph` field contains exactly two edges
(one per `call_indirect`):

| caller | pc | indirect | resolved-targets | soundness |
|--------|----|----------|------------------|-----------|
| 3      | 1  | true     | `[1]`            | `sound`   |
| 4      | 1  | true     | `[0, 1, 2]`      | `sound`   |

Edge #1 is **precise** (the constant index resolves to a singleton);
edge #2 is a **sound over-approximation** (the unconstrained index
covers the whole table).

## Expected diagnostics

Beyond the lattice-probe `Info` the analyzer emits on every run
(unchanged), the two `call_indirect` sites produce:

```
severity: Info
func_index: 3
pc: 1
message: "call_indirect resolved to 1 target(s) (sound; type 0, 3-entry table)"
```

```
severity: Warning
func_index: 4
pc: 1
message: "call_indirect index unconstrained — 3 targets (whole-table over-approximation over a 3-entry table; sound)"
```

**No `UnsoundnessFallback` is emitted** for either `call_indirect`,
and locals are NOT scrubbed to top — this is the structural FEAT-006
win over v0.3.

## Expected operand-stack + locals state

`dispatch_const` (func 3, no locals):

| pc | op                       | operand stack after | locals snapshot |
|----|--------------------------|---------------------|-----------------|
| 0  | `i32.const 1`            | `[ {1,1} ]`         | `[]`            |
| 1  | `call_indirect (type 0)` | `[ top ]`           | `[]`            |
| 2  | `end`                    | `[ top ]`           | `[]`            |

The `call_indirect` pops the index `{1,1}` and pushes `top` for the
callee's single i32 result (FEAT-006 models call *effects*
pessimistically; precise interprocedural value propagation is
FEAT-007).

`dispatch_unknown` (func 4, one i32 param = local 0 = top):

| pc | op                       | operand stack after | locals snapshot      |
|----|--------------------------|---------------------|----------------------|
| 0  | `local.get 0`            | `[ top ]`           | `[ local0 = top ]`   |
| 1  | `call_indirect (type 0)` | `[ top ]`           | `[ local0 = top ]`   |
| 2  | `end`                    | `[ top ]`           | `[ local0 = top ]`   |

## Concrete-side oracle

Both entry points are runnable core-module functions returning a
single i32:

| call                        | concrete result | abstract target set | sound? |
|-----------------------------|-----------------|---------------------|--------|
| `dispatch_const()`          | `200` (func 1)  | `{1}`               | yes (1 ∈ {1}) |
| `dispatch_unknown(0)`       | `100` (func 0)  | `{0, 1, 2}`         | yes (0 ∈ set) |
| `dispatch_unknown(1)`       | `200` (func 1)  | `{0, 1, 2}`         | yes (1 ∈ set) |
| `dispatch_unknown(2)`       | `300` (func 2)  | `{0, 1, 2}`         | yes (2 ∈ set) |

The soundness oracle: for every concrete index `k`, the concretely
dispatched function `table[k]` is a member of the resolved target
set. This holds by construction (the resolved set is
`table[lo..=hi] ∩ [0, table-len)` and `k ∈ [lo, hi]` since the
index interval is sound per FEAT-001 AC#1).

## Soundness argument

For any concrete execution reaching the `call_indirect` at pc P with
concrete index `k`:

1. `k ∈ [lo, hi]` — the abstract index interval over-approximates the
   concrete index (interval-domain soundness, FEAT-001 AC#1).
2. The resolved target set includes `table[k]` for every
   `k ∈ [lo, hi] ∩ [0, table-len)`.
3. A concrete `k` outside `[0, table-len)` traps at runtime (no
   target is dispatched), so dropping it from the resolved set is
   sound.
4. Therefore the resolved target set includes the concretely
   dispatched target. Soundness reduces to the interval domain's
   soundness.

## What this fixture intentionally does NOT cover

- **Interprocedural value propagation.** FEAT-006 resolves the call
  *graph*, not call *effects*: after a call the operand stack is
  modelled pessimistically (pop the callee's params, push `top` per
  result). Precise summary-based propagation lands with FEAT-007.
- **Passive / declared element segments and `table.init`.** v0.4
  handles active segments with a constant i32 offset; other shapes
  mark the table contents unknown and a `call_indirect` then
  over-approximates to the whole table (sound).
- **`table.grow`.** A growable table (declared maximum, or no
  maximum) widens the resolution range to the maximum (or the
  populated extent) — over-approximating soundly. This fixture uses
  a fixed `3 3` table to keep the precise-resolution case clean.
- **Bounded-but-non-singleton indices** (e.g. an index proven to be
  in `[0, 1]`): these resolve to the sub-range `{table[0], table[1]}`
  (precise to the interval width). Demonstrated structurally by the
  resolver but not exercised by a dedicated entry point here.

## Cross-references

- `crates/scry-analyzer/wit/scry.wit` — the new `call-edge` record,
  `soundness-tag` enum, and `analysis-result.call-graph` field.
- `crates/scry-analyzer/src/lib.rs` — `FuncTable`, the table +
  element pre-pass, `handle_call`, `handle_call_indirect`,
  `emit_call_indirect_edge`, `apply_call_stack_effect`.
- `artifacts/requirements.yaml#FEAT-006` — acceptance criteria
  amended to cite this fixture.
- `spar/scry.aadl` — the `CallGraph` / `CallEdge` data types.
