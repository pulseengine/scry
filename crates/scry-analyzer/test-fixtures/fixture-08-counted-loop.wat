;; fixture-08-counted-loop — FEAT-016 slice-1 (interval loop fixpoint) corpus.
;;
;; A terminating counted loop. `local 1` (k) is set to a constant BEFORE the
;; loop and is never written inside it — it is loop-invariant. `local 0` (the
;; param i) is decremented each iteration until zero (the structured exit via
;; `br_if` out of the enclosing block).
;;
;; v1.1–v1.3 behaviour: the analyzer hits the `block`/`loop` and SCRUBS every
;; local to top (UnsoundnessFallback) — k is lost even though it cannot change.
;;
;; FEAT-016 slice-1 target: the loop is modelled soundly; k stays its precise
;; loop-invariant interval [42, 42] (a local not in the loop's write-set is not
;; havocked), while i widens soundly. Concrete `counted(n)` returns 42 for any
;; n >= 0, so the soundness oracle asserts 42 in k's abstract interval — a
;; non-vacuous check (it would fail if the fixpoint wrongly dropped k).
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
