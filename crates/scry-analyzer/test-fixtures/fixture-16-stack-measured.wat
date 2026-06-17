;; fixture-16-stack-measured — FEAT-021 slice-2b (live kill-criterion).
;;
;; A 2-deep call chain (entry frame 32 -> deep frame 16) that SELF-MEASURES its
;; runtime shadow-stack peak: each function, after lowering the __stack_pointer
;; (global 0), records min(min_sp, sp) into a second global `min_sp` (global 1)
;; via `select`. Both globals are exported so the host harness can read the
;; true peak (sp_init - min_sp) after a concrete wasmtime run and cross-check it
;; against scry's reported max-stack-bytes (analyzed via the composed
;; component). True peak = 32 + 16 = 48; scry reports bytes(48); 48 >= 48.
;;
;; The min-recording `global.get $sp` reads are NOT followed by `i32.sub`, so
;; the analyzer's frame detector still sees exactly one constant frame per
;; function (32 / 16) — the self-measurement does not perturb the static bound.
(module
  (global $sp     (mut i32) (i32.const 65536))   ;; global 0 = __stack_pointer
  (global $min_sp (mut i32) (i32.const 65536))   ;; global 1 = running min(sp)
  (export "sp" (global $sp))
  (export "min_sp" (global $min_sp))

  (func $deep (result i32)
    global.get $sp  i32.const 16  i32.sub  global.set $sp        ;; frame 16
    ;; min_sp = min(min_sp, sp)   (select: cond ? val1 : val2)
    global.get $sp  global.get $min_sp  global.get $sp  global.get $min_sp
    i32.lt_u  select  global.set $min_sp
    global.get $sp  i32.const 16  i32.add  global.set $sp        ;; restore
    i32.const 7)

  (func $entry (export "run") (result i32)
    global.get $sp  i32.const 32  i32.sub  global.set $sp        ;; frame 32
    global.get $sp  global.get $min_sp  global.get $sp  global.get $min_sp
    i32.lt_u  select  global.set $min_sp
    call $deep
    global.get $sp  i32.const 32  i32.add  global.set $sp))      ;; restore
