# fixture-12-stack-chain

FEAT-021 **slice-1** corpus — the worst-case shadow-stack bound (the AbsInt
StackAnalyzer analogue for the Wasm linear-memory shadow stack, DD-016).

A 3-deep **direct** call chain `outer → mid → inner`, each function carrying a
constant frame established by the standard Rust/LLVM prologue
(`global.get $sp; i32.const F; i32.sub; global.set $sp`) and restored by the
`i32.add` epilogue. Global 0 is the mutable-i32 `__stack_pointer`.

## Source

```wat
(module
  (global (mut i32) (i32.const 65536))   ;; global 0 = __stack_pointer
  (func $inner (result i32)
    global.get 0  i32.const 8   i32.sub  global.set 0
    global.get 0  i32.const 8   i32.add  global.set 0
    i32.const 1)
  (func $mid (result i32)
    global.get 0  i32.const 32  i32.sub  global.set 0
    call $inner
    global.get 0  i32.const 32  i32.add  global.set 0)
  (func $outer (export "run") (result i32)
    global.get 0  i32.const 16  i32.sub  global.set 0
    call $mid
    global.get 0  i32.const 16  i32.add  global.set 0))
```

## Behaviour

- **Frames:** inner = 8, mid = 32, outer = 16 (recognised from each prologue).
- **Worst case** = the deepest weighted path through the call graph =
  `outer(16) + mid(32) + inner(8) = 56` bytes.
- **Concrete:** on the `outer → mid → inner` path the `__stack_pointer` is
  decremented by exactly 56 bytes at the deepest point, so scry's reported
  `max_stack_bytes = 56` is a sound (here exact) over-approximation.

The native oracle `feat021_stack_chain_sums_frames` asserts the bound is `56`,
the per-function frames are `8/32/16`, and the SP global is 0.

## Soundness obligation

`max_stack(f) = frame(f) + max over callees` folded callees-first over the
call-graph reverse-topological order (reusing the FEAT-006/007 call graph +
Tarjan SCCs). The reported bound over-approximates the true peak shadow-stack
usage on every execution; mechanized in `proofs/rocq/StackBound.v`.
