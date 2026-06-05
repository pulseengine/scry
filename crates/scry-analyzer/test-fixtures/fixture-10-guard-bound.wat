;; fixture-10-guard-bound — FEAT-016 slice-2b-i (guard refinement) corpus.
;;
;; A counted loop bounded by a CONSTANT via the loop's exit guard. `i` is
;; incremented while `i < 10` and the loop exits when `i >= 10`.
;;
;; slice-2a (interval loop fixpoint, v1.5.0): `i` is loop-written and the
;; interval domain cannot see the `i >= 10` exit test, so the fixpoint widens
;; `i` upward to ⊤ — sound but with no upper bound.
;;
;; slice-2b-i target (guard refinement): on the not-taken edge of
;; `br_if (i >= 10)` the analyzer refines `i <= 9`; after `i = i + 1` that is
;; `i <= 10`, so the loop-header fixpoint converges to `i = [0, 10]` instead
;; of ⊤. On the taken (exit) edge `i >= 10` meets the header `[0,10]` to give
;; `i = [10, 10]` after the loop. Concretely `countup()` returns 10, so the
;; result is bounded and exact — a non-vacuous soundness + precision check
;; distinguishing slice-2b-i (bounded) from slice-2a (⊤).
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
