;; fixture-11-var-bound — FEAT-016 slice-2b-ii (octagon relational product).
;;
;; A counted loop bounded by a VARIABLE relation: `i` is incremented while
;; `i < n`, where `n` is held in a LOCAL (not an i32 immediate). The exit guard
;; compares two locals (`local.get i; local.get n; i32.ge_s`), so slice-2b-i's
;; constant-guard peephole cannot fire — only the relational octagon can bound
;; `i`.
;;
;; slice-2b-i (v1.6, interval + constant guard refinement): the guard is
;; local-vs-local, not local-vs-const, so `i`'s interval is never refined; the
;; loop fixpoint widens `i` to ⊤ — sound but with no upper bound.
;;
;; slice-2b-ii target (v1.8, octagon product): the relational guard adds
;; `i − n ≤ −1` on the loop-entry (not-taken) edge; `i := i + 1` SHIFTS that to
;; `i − n ≤ 0`; the octagon fixpoint (widen, then narrow) carries `i ≤ n` across
;; iterations. The exit (taken) edge adds `i ≥ n`, so after the block `i = n`.
;; Reducing the octagon against `n = [10,10]` projects `i ≤ n ≤ 10`, so `i` is
;; bounded `[…,10]` instead of ⊤ — the relational win. Concretely
;; `countup_var()` returns 10.
(module
  (func (export "countup_var") (result i32)
    (local i32)            ;; local 0 = i, zero-init [0,0]
    (local i32)            ;; local 1 = n, the variable bound (a local, not an immediate)
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
