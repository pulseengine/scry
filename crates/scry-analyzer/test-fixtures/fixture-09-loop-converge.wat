;; fixture-09-loop-converge — FEAT-016 slice-2a (real loop fixpoint) corpus.
;;
;; A terminating counted loop that writes a local `m` to a CONSTANT (7) on
;; every iteration. The decremented param `i` drives termination.
;;
;; slice-1 (write-set havoc, v1.4.0): `m` is in the loop's write-set, so it is
;; widened to ⊤ — all loop-carried precision is thrown away.
;;
;; slice-2a target (a real iterate-then-widen interval fixpoint): the analyzer
;; interprets the loop body, so `m` converges to the precise loop-invariant
;; range it actually holds. At the loop header `m` is `[0,0]` (zero-init) on
;; entry and `[7,7]` after a body pass; the join is `[0,7]`, which is stable —
;; so `m = [0,7]` after the loop, NOT ⊤. Concretely `converge(n)` returns 0
;; when n==0 (loop never runs) and 7 when n>0, so the result is in {0,7} ⊆
;; [0,7] — a non-vacuous soundness + precision check distinguishing slice-2a
;; (bounded) from slice-1 (⊤). (`i`, the counter, still needs the relational
;; octagon of slice-2b to stay bounded; interval-alone it widens — that is
;; expected and sound here.)
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
        br 0))             ;; back-edge to the loop header
    local.get 1))          ;; return m
