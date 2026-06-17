;; fixture-13-stack-recursion — FEAT-021 slice-1 (worst-case shadow-stack).
;;
;; A self-recursive function: the call graph has a self-edge, so $rec is a
;; (non-trivial) SCC. Recursion through a linear-memory shadow stack has no
;; finite bound without a ranking-function/termination argument (DD-016
;; guardrail 2), so scry must report the worst-case shadow-stack usage as
;; UNBOUNDED — never a finite under-count.
(module
  (global (mut i32) (i32.const 65536))   ;; global 0 = __stack_pointer

  (func $rec (export "rec") (param i32) (result i32)
    global.get 0  i32.const 16  i32.sub  global.set 0   ;; frame 16, every level
    (block
      local.get 0
      i32.eqz
      br_if 0                                            ;; base case: stop
      local.get 0  i32.const 1  i32.sub  call $rec  drop ;; recurse
    )
    global.get 0  i32.const 16  i32.add  global.set 0    ;; restore
    i32.const 0))
