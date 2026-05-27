# fixture-03-region-bounds

Bounds-check elision for the canonical "base + constant offset"
pointer pattern: a Wasm compiler emits `i32.const BASE; i32.const k;
i32.add; i32.load offset=0` for every stack-allocated local
dereference. v0.2 punted on this — the `i32.load` produced an
`UnsoundnessFallback` diagnostic and widened all locals to `top`.
v0.3 (FEAT-005) recognises the singleton-interval address as a
region-tagged pointer (via the new wasm-lattice `region-create` +
`region-offset` transfer functions) and proves the access is
in-bounds against the declared 1-page (= 65536-byte) memory.

## Source

```wat
(module
  (memory 1)
  (func (export "load_from_known_offset") (result i32)
    i32.const 100
    i32.const 4
    i32.add
    i32.load))
```

## Expected post-analysis state

Per-instruction operand stack (top-of-stack rightmost):

| pc | op             | operand stack after                                          |
|----|----------------|--------------------------------------------------------------|
|  0 | `i32.const 100`| `[ {lo:100,hi:100} ]`                                        |
|  1 | `i32.const 4`  | `[ {lo:100,hi:100}, {lo:4,hi:4} ]`                           |
|  2 | `i32.add`      | `[ {lo:104,hi:104} ]`                                        |
|  3 | `i32.load`     | `[ top ]` (loaded value pessimistic; bounds proven safe)     |
|  4 | `end`          | `[ top ]`                                                    |

Per-program-point locals snapshot (no locals, no parameters):

| pc | locals snapshot |
|----|-----------------|
|  0 | `[]`            |
|  1 | `[]`            |
|  2 | `[]`            |
|  3 | `[]`            |
|  4 | `[]`            |

## Expected diagnostics

Beyond the lattice-probe `Info` the analyzer emits on every run
(unchanged from v0.2), pc=3 produces one new diagnostic:

```
severity: Info
func_index: 0
pc: 3
message: "i32.load bounds-check elision safe at pc=3: access \
         [104, 108) fits in default region of 65536 bytes"
```

No `UnsoundnessFallback` is emitted; locals are NOT degraded to
top (there are no locals to degrade, but the `degraded` flag is
not flipped either, so subsequent program-points are emitted
normally).

The `end` at pc=4 produces no diagnostic.

## Why this fixture

Pins the v0.3 (FEAT-005) win in concrete terms:

1. **Detection of the canonical base+offset pattern.** The
   `i32.const 100; i32.const 4; i32.add` chain leaves a singleton
   interval `{104, 104}` on the operand stack. v0.3's
   `handle_memory_load` recognises this as a *known address* and
   synthesises a region pointer with `region-id = 104` and offset
   `{104, 104}` via the wasm-lattice's new `region-create` +
   `region-offset` ops (dogfooded across the WIT boundary per
   DD-008).

2. **In-bounds proof via the parsed memory section.** The
   `(memory 1)` declaration is parsed in the pre-pass and
   recorded as `memory_min_bytes = 65536`. The load width is 4;
   `region_in_bounds(104, 104, 4, 65536) == true`, so the
   analyzer emits an `Info` diagnostic loom can consume to
   *elide* the runtime bounds check at this site (per REQ-004
   / FEAT-008).

3. **Soundness preserved on the value.** The loaded *value* is
   pushed as `i32-interval(top)` — v0.3 doesn't track per-region
   contents, so the only sound abstraction of "what's at memory
   address 104" is the full i32 range. v0.4+ will strengthen
   this via summary-based interprocedural analysis (FEAT-007)
   or a richer content model.

4. **Distinct diagnostic surface for downstream.** v0.2 emitted
   `UnsoundnessFallback` here. v0.3 emits either `Info` (proven
   in-region) or `Warning` (cannot prove). Loom, sigil-attestation
   consumers, and rivet evidence-linking can all key off the
   severity to decide whether a transformation is licensed.

## What this fixture intentionally does NOT cover

- **Multi-load patterns** (`base + variable_offset`): if the
  offset is not a singleton (e.g. loop-induction variable in
  `[0, N)` form), the analyzer still computes the in-bounds
  check over the full interval; this is sound but precision
  depends on the interval bound being known. The current
  fixture exercises only the singleton case.
- **Stores updating region contents**: v0.3 drops the stored
  value on the floor (sound: any subsequent load is
  pessimistically `top` anyway). Per-region content tracking
  lands with FEAT-007 / v0.4+.
- **Cross-region aliasing**: v0.3 uses a single default region
  per module (covering all of declared linear memory). The
  region domain in wasm-lattice already supports multiple
  region-ids with the matching lattice ops (leq/join/meet/
  widen all parametric in region-id), but the analyzer
  doesn't yet split linear memory into per-allocation
  regions — that requires stack-pointer tracking which
  lands alongside FEAT-007.
- **`memory.grow` / `memory.size`**: still hit the v0.2
  fallback (UnsoundnessFallback + scrub locals to top). The
  region's `size_bytes` is fixed at the declared minimum;
  v0.3 cannot prove anything past `memory.grow`.

## Cross-references

- `crates/wasm-lattice/wit/wasm-lattice.wit` — the `region`
  record + `region-create` / `region-offset` / `region-leq` /
  `region-join` / `region-meet` / `region-widen` ops added in
  this PR.
- `crates/scry-analyzer/wit/scry.wit` — the new
  `region-pointer(region-pointer-payload)` case on
  `AbstractValue` (declared for v0.4+ use; v0.3 synthesises
  regions transiently at the memory op rather than storing
  them on the operand stack, which preserves fixture-01 /
  fixture-02 expectations). The payload type is declared
  locally inside the analyzer interface — structurally
  identical to `pulseengine:wasm-lattice/domain.region` but
  not re-exported through it, sidestepping a wac-compose
  validation issue with cross-package type aliases in
  exported interfaces.
- `crates/scry-analyzer/src/lib.rs` — `handle_memory_load` /
  `handle_memory_store` / `region_in_bounds`.
- `artifacts/requirements.yaml#FEAT-005` — acceptance criteria
  amended to cite this fixture.
