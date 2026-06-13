# fixture-11-var-bound

FEAT-016 **slice-2b-ii** corpus — the *octagon relational product*. It
distinguishes slice-2b-ii (a loop counter bounded by a **variable** relation
converges to a finite interval) from slice-2b-i (which only handles a counter
bounded by a **constant** in the guard).

A counted loop increments local `i` while `i < n`, where `n` is held in a
**local** (set to `10` before the loop), not an i32 immediate. The exit guard
therefore compares two locals (`local.get i; local.get n; i32.ge_s`), so the
constant-guard peephole of slice-2b-i cannot fire — only the relational octagon
can bound `i`.

## Source

```wat
(module
  (func (export "countup_var") (result i32)
    (local i32)            ;; local 0 = i, zero-init [0,0]
    (local i32)            ;; local 1 = n, the variable bound (a local)
    i32.const 10
    local.set 1            ;; n = 10
    (block
      (loop
        local.get 0        ;; i
        local.get 1        ;; n
        i32.ge_s           ;; i >= n ?
        br_if 1            ;; exit the block when i >= n
        local.get 0
        i32.const 1
        i32.add
        local.set 0        ;; i = i + 1
        br 0))             ;; back-edge
    local.get 0))          ;; return i  (== 10)
```

## Behaviour

- **Concrete:** `countup_var() = 10` — `i` counts up to `n = 10`, then exits.
- **slice-2b-i (v1.6, interval + constant guard refinement):** the guard is
  local-vs-local, not local-vs-const, so `i`'s interval is never refined; the
  loop fixpoint widens `i` to ⊤ — sound, but with no upper bound.
- **slice-2b-ii target (v1.8, octagon product):** on the loop-entry (not-taken)
  edge the relational guard adds `i − n ≤ −1`; `i := i + 1` **shifts** that to
  `i − n ≤ 0`; the octagon fixpoint (widen, then narrow) carries `i ≤ n` across
  iterations. Reducing the octagon against `n = [10,10]` (interval bounds
  injected, closed, projected back) yields `i ≤ n ≤ 10`, so `i` converges to
  the bounded `[0, 10]` (`hi = 10`) instead of ⊤ — the relational win.

The soundness oracle asserts the concrete result `10` lies in `i`'s interval;
the precision check asserts `i.hi ≤ 10` — bounded via the relation, where the
interval domain (and the constant-guard refinement) alone give ⊤.

## Soundness obligation

The relational product rests on pieces proven / falsified in isolation:
the octagon transfers (`forget`-on-write, the assignment/increment-shift) are
γ-sweep-falsified in `scry-octagon`; the octagon→interval projection rounding
is mechanized in `proofs/rocq/OctagonProject.v` (`proj_interval_sound`); the
loop fixpoint's post-fixpoint soundness is the generic
`proofs/rocq/LoopFixpoint.v` (`loop_postfixpoint_sound`) instantiated at the
octagon transfer, joined/widened/narrowed in lockstep with the intervals. The
integration's safety net is the rule that any write the octagon transfer does
not model **forgets** that variable's relations (never retains a stale one).
