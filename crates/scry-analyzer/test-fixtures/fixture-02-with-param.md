# fixture-02-with-param

Adds an unknown parameter to the constant-fold pattern from
fixture-01. The analyzer initializes parameter 0 to `domain::top()`
(we know nothing about the caller's argument until summary-based AI
lands at FEAT-007), then adds a constant. Per the wasm-lattice's
overflow rule, the result widens back to top.

## Source

```wat
(module
  (func (export "doit") (param i32) (result i32)
    local.get 0
    i32.const 5
    i32.add))
```

## Expected post-analysis state

Per-instruction operand stack (top-of-stack rightmost):

| pc | op             | operand stack after                            |
|----|----------------|------------------------------------------------|
|  0 | `local.get 0`  | `[ top ]`                                      |
|  1 | `i32.const 5`  | `[ top, {lo:5,hi:5} ]`                         |
|  2 | `i32.add`      | `[ top ]` (overflow → widens to top)           |
|  3 | `end`          | `[ top ]`                                      |

Per-program-point locals snapshot (one local: param 0):

| pc | locals snapshot              |
|----|------------------------------|
|  0 | `[ local 0 = top ]`          |
|  1 | `[ local 0 = top ]`          |
|  2 | `[ local 0 = top ]`          |
|  3 | `[ local 0 = top ]`          |

The locals never change (no `local.set` / `local.tee`); the
interesting evidence is again on the operand stack.

## Why this fixture

Validates two things:
1. Parameter initialization: scry must mark function parameters as
   `top` (unknown), not as the analyzer's choice of constant.
2. The wasm-lattice's saturation rule (`i32_add` of `top + {5,5}` →
   `top`, because `i64::MAX + 5` would exceed `i32::MAX`) is
   exercised on a real input, not just unit-tested on the lattice
   crate.
