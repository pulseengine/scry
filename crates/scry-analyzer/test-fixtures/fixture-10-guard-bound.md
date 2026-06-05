# fixture-10-guard-bound

FEAT-016 **slice-2b-i** corpus — *guard refinement*, the first step of the
relational track (DD-015). It distinguishes slice-2b-i (a guard-bounded loop
counter converges to a finite interval) from slice-2a (the same counter
widens to ⊤ because the interval fixpoint cannot see the exit test).

A counted loop increments local `i` while `i < 10` and exits the enclosing
block when `i >= 10`. The bound is a **constant in the loop's own exit
guard** — exactly the shape guard refinement targets.

## Source

```wat
(module
  (func (export "countup") (result i32)
    (local i32)            ;; local 0 = i, zero-init [0,0]
    (block
      (loop
        local.get 0
        i32.const 10
        i32.ge_s           ;; i >= 10 ?
        br_if 1            ;; exit the block when i >= 10
        local.get 0
        i32.const 1
        i32.add
        local.set 0        ;; i = i + 1   (refined: i <= 9 here ⇒ i <= 10)
        br 0))             ;; back-edge
    local.get 0))          ;; return i  (== 10)
```

## Behaviour

- **Concrete:** `countup() = 10` — the loop runs until `i` reaches 10, then
  exits. The single result is exactly `10`.
- **slice-2a (v1.5.0, interval fixpoint):** `i` is loop-written and the
  interval domain cannot read the `i >= 10` exit test, so the header fixpoint
  widens `i` upward to ⊤ — sound, but with no upper bound.
- **slice-2b-i target (guard refinement):** on the **not-taken** edge of
  `br_if (i >= 10)` the analyzer refines `i <= 9`; after `i = i + 1` that is
  `i <= 10`, so narrowing pulls the over-widened header back to `i = [0, 10]`
  instead of ⊤. On the **taken** (exit) edge `i >= 10` meets the header
  `[0,10]` to give `i = [10, 10]`, which is joined into the block exit. The
  post-loop result interval is the sound `[0, 10]` (`hi = 10`), a bounded,
  non-vacuous improvement over slice-2a's ⊤.

The soundness oracle asserts the concrete result `10` lies inside `i`'s
interval; the precision check asserts the interval is bounded with
`hi <= 10` — the slice-2b-i win.

## Soundness obligation

Refinement is only sound when the half-space implied by the guard is met
*into* the abstract value (an over-approximation can only shrink toward the
true set, never below it). Refinement is applied **only to signed
comparisons** against a constant on a `local.get` operand; unsigned
comparisons are left unrefined (their wrap semantics would make a naive
signed half-space unsound). The in-slice Rocq lemma proves that meeting an
interval with the guard's half-space over-approximates exactly the concrete
states that satisfy the guard (DD-015).
