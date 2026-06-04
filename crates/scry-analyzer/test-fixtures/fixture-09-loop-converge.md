# fixture-09-loop-converge

FEAT-016 **slice-2a** corpus — the real iterate-then-widen interval loop
fixpoint (DD-015), distinguishing it from slice-1's write-set havoc.

A terminating counted loop writes local `m` to the constant `7` on every
iteration; param `i` is decremented to drive termination.

## Source

```wat
(module
  (func (export "converge") (param i32) (result i32)
    (local i32)            ;; local 1 = m
    (block
      (loop
        local.get 0        ;; i
        i32.eqz
        br_if 1            ;; exit the block when i == 0
        i32.const 7
        local.set 1        ;; m = 7  (constant, every iteration)
        local.get 0
        i32.const 1
        i32.sub
        local.set 0        ;; i = i - 1
        br 0))             ;; back-edge
    local.get 1))          ;; return m
```

## Behaviour

- **Concrete:** `converge(0) = 0` (loop never runs, `m` is zero-init);
  `converge(n>0) = 7`. So the result ∈ {0, 7} (verified `converge(5)=7`).
- **slice-1 (v1.4.0, write-set havoc):** `m` ∈ write-set ⇒ widened to ⊤.
- **slice-2a target:** the real fixpoint interprets the body; at the loop
  header `m` is `[0,0]` on entry, `[7,7]` after a body pass, join `[0,7]`
  (stable) ⇒ `m = [0,7]` after the loop, **not ⊤**. The soundness oracle
  asserts the concrete result lies in `m`'s interval, and the precision
  check asserts the interval is bounded (`[0,7]`, not ⊤) — the slice-2a win.

`i` (the loop counter) still widens under interval-alone; the relational
octagon of **slice-2b** is what bounds it (`i < n`). That is expected and
sound here — this fixture isolates the interval-fixpoint improvement.

## Soundness obligation

The fixpoint must over-approximate the locals at the loop header across all
iteration counts (`entry ⊔ body(header)`, widened to a post-fixpoint). The
in-slice Rocq lemma extends `WriteSetHavoc.v` to the iterate-then-widen
case (DD-015).
