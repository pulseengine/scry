;; fixture-15-stack-alloca — FEAT-021 slice-1 soundness regression.
;;
;; A function with a CONSTANT prologue frame (16) AND a later DYNAMIC decrement
;; of the __stack_pointer (an `alloca` of a runtime size). Its true peak frame
;; is 16 + param — NOT statically bounded. The detector must report UNKNOWN for
;; this function (and the module), never the constant 16: counting only the
;; recognised constant prologue and ignoring the dynamic decrement would be an
;; UNSOUND under-count. (Caught by clean-room review of the initial slice-1
;; detector, which checked the single-const-frame case before the dynamic one.)
(module
  (global (mut i32) (i32.const 65536))   ;; global 0 = __stack_pointer

  (func $allocish (export "allocish") (param i32) (result i32)
    global.get 0  i32.const 16   i32.sub  global.set 0   ;; constant frame 16
    global.get 0  local.get 0    i32.sub  global.set 0   ;; dynamic: SP -= param
    i32.const 0))
