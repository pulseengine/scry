# fixture-01-constant-fold

Pure constant folding through `i32.add` and `i32.mul`. The analyzer
should see the operand stack collapse to a singleton interval at every
program point: `(10 + 32) * 2 = 84`.

## Source

```wat
(module
  (func (export "compute") (result i32)
    i32.const 10
    i32.const 32
    i32.add
    i32.const 2
    i32.mul))
```

## Expected post-analysis state

Per-instruction operand stack (top-of-stack rightmost):

| pc | op            | operand stack after                            |
|----|---------------|------------------------------------------------|
|  0 | `i32.const 10`| `[ {lo:10,hi:10} ]`                            |
|  1 | `i32.const 32`| `[ {lo:10,hi:10}, {lo:32,hi:32} ]`             |
|  2 | `i32.add`     | `[ {lo:42,hi:42} ]`                            |
|  3 | `i32.const 2` | `[ {lo:42,hi:42}, {lo:2,hi:2} ]`               |
|  4 | `i32.mul`     | `[ {lo:84,hi:84} ]`                            |
|  5 | `end`         | `[ {lo:84,hi:84} ]`                            |

Final operand top is `i32-interval { lo: 84, hi: 84 }`.

The function has no locals, so every `ProgramPoint` carries an empty
`locals` list. The interesting evidence here is on the operand stack —
the host harness (FEAT-008's loom integration) will pull it via a
follow-on extension to the WIT interface; v0.2 AC#1 only emits the
locals snapshot.

## Why this fixture

Demonstrates the lattice's constant-fold path end-to-end: every
`i32_add` / `i32_mul` call into the wasm-lattice component returns a
singleton interval, exercising the cross-component import on the
non-degenerate path.
