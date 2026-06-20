;; fixture-18-operand-stack — FEAT-023 (operand-stack invariants).
;;
;; A backend (synth) wants the abstract VALUE-STACK state at each pc, not just
;; the locals — the transient temps a register allocator / instruction selector
;; maps onto. scry's `Interp` already models the operand stack soundly over the
;; interval domain; FEAT-023 just surfaces it on each `ProgramPoint`.
;;
;; `$stack_const` pushes two constants and adds them. At the emitted program
;; points the abstract operand-stack is, in stack order (bottom → top):
;;   after `i32.const 42`  →  [ [42,42] ]
;;   after `i32.const 7`   →  [ [42,42], [7,7] ]
;;   after `i32.add`       →  [ [49,49] ]
;; so a consumer reads a known singleton off the stack top — the operand-stack
;; analogue of a constant local. Sound: every entry over-approximates the
;; concrete slot (here exactly, the constants being singletons).
(module
  (func $stack_const (export "run") (result i32)
    i32.const 42
    i32.const 7
    i32.add))
