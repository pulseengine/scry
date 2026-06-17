;; fixture-14-stack-dynamic — FEAT-021 slice-1 (worst-case shadow-stack).
;;
;; A function with a DYNAMIC frame: it subtracts a runtime value (the param,
;; an alloca-style variable-size allocation) from the __stack_pointer rather
;; than a constant. The frame size is not statically known, so scry must
;; report UNKNOWN for this function (and hence for the whole module) — a sound
;; admission of ignorance, never a zero under-count (DD-016 guardrail 1).
(module
  (global (mut i32) (i32.const 65536))   ;; global 0 = __stack_pointer

  (func $dyn (export "dyn") (param i32) (result i32)
    global.get 0  local.get 0  i32.sub  global.set 0   ;; SP -= param  (dynamic)
    i32.const 0))
