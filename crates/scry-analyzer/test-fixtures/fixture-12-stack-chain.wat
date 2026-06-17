;; fixture-12-stack-chain — FEAT-021 slice-1 (worst-case shadow-stack bound).
;;
;; A 3-deep DIRECT call chain (outer -> mid -> inner), each function carrying a
;; constant shadow-stack frame established by the standard Rust/LLVM prologue
;; (global.get $sp; i32.const F; i32.sub; global.set $sp) and restored by the
;; epilogue (... i32.add ...). Global 0 is the mutable-i32 __stack_pointer.
;;
;; Frames: inner = 8, mid = 32, outer = 16.
;; Worst case along the deepest path outer -> mid -> inner = 16 + 32 + 8 = 56.
;; The concrete peak shadow-stack decrement on that path is exactly 56 bytes,
;; so scry's reported max-shadow-stack-bytes (56) is a sound (here exact) bound.
(module
  (global (mut i32) (i32.const 65536))   ;; global 0 = __stack_pointer

  (func $inner (result i32)
    global.get 0  i32.const 8   i32.sub  global.set 0   ;; frame 8
    global.get 0  i32.const 8   i32.add  global.set 0   ;; restore
    i32.const 1)

  (func $mid (result i32)
    global.get 0  i32.const 32  i32.sub  global.set 0   ;; frame 32
    call $inner
    global.get 0  i32.const 32  i32.add  global.set 0)  ;; restore

  (func $outer (export "run") (result i32)
    global.get 0  i32.const 16  i32.sub  global.set 0   ;; frame 16
    call $mid
    global.get 0  i32.const 16  i32.add  global.set 0)) ;; restore
