# fixture-13-stack-recursion

FEAT-021 **slice-1** corpus — recursion → **Unbounded** (DD-016 guardrail 2).

A self-recursive `$rec` (a `call $rec` in its body) makes the call graph have a
self-edge, so `$rec` is a non-trivial SCC. A shadow stack growing through
recursion has no finite bound without a ranking-function / termination
argument, so scry reports the worst-case usage as **UNBOUNDED** — never a
finite under-count. (The SP lives in linear memory; the interval/octagon
cannot bound the recursion depth, so claiming a finite bound here would be
unsound — slice-1 conservatively reports unbounded.)

## Source (abridged)

```wat
(func $rec (export "rec") (param i32) (result i32)
  global.get 0  i32.const 16  i32.sub  global.set 0    ;; frame 16 per level
  (block local.get 0 i32.eqz br_if 0
         local.get 0 i32.const 1 i32.sub call $rec drop)
  global.get 0  i32.const 16  i32.add  global.set 0
  i32.const 0)
```

Native oracle: `feat021_stack_recursion_is_unbounded` asserts
`max_stack_bytes == Unbounded`.
