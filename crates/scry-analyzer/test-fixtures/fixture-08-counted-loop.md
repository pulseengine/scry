# fixture-08-counted-loop

FEAT-016 slice-1 corpus — the interval **loop fixpoint** (DD-014).

A terminating counted loop. `local 1` (k) is loop-invariant (set to `42`
before the loop, never written inside it); `local 0` (param i) is decremented
to zero, with the structured exit a `br_if` out of the enclosing `block`.

## Source

```wat
(module
  (func (export "counted") (param i32) (result i32)
    (local i32)            ;; local 1 = k (loop-invariant)
    i32.const 42
    local.set 1            ;; k = 42, set before the loop
    (block
      (loop
        local.get 0        ;; i
        i32.eqz
        br_if 1            ;; exit the block when i == 0
        local.get 0
        i32.const 1
        i32.sub
        local.set 0        ;; i = i - 1  (i is in the loop write-set)
        br 0))             ;; back-edge to the loop header
    local.get 1))          ;; return k
```

## Behaviour

- **Concrete:** `counted(n)` returns `42` for every `n >= 0` (verified:
  `counted(3) = counted(0) = 42`). Terminating, so the host soundness oracle
  can run it.
- **v1.1–v1.3 abstract:** the `block`/`loop` triggers the v0.2 fallback —
  every local is scrubbed to `⊤` and an `UnsoundnessFallback` diagnostic is
  emitted. k is lost despite being unchangeable.
- **FEAT-016 slice-1 target:** the loop is modelled soundly. k (not in the
  loop's write-set) keeps its precise interval `[42, 42]`; i widens soundly.
  The soundness oracle then asserts the concrete return `42` lies in k's
  abstract interval — a **non-vacuous** check that fails if the fixpoint
  wrongly drops the invariant.

## Soundness note (the slice-1 obligation)

The loop body executes an input-dependent number of times. Any sound loop
abstraction must over-approximate the join over all iteration counts. A local
**not** written anywhere in the loop body is identical in every iteration, so
keeping its pre-loop interval is sound; a written local must be widened (to a
post-fixpoint, or conservatively to `⊤`). The Rocq lemma for this lands in the
same slice (DD-014, user-directed: proof in-slice).
