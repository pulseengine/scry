;; fixture-19-named-functions — FEAT-027 (human-readable function metadata).
;;
;; A consumer (synth's footprint report, scry-viz) wants to show `$compute`
;; instead of `func 1`. scry resolves a name for every function index from
;; three sources, in priority order: the custom `name` section (the symbolic
;; `$id`s below assemble into one), else an export name, else an import
;; `module.field`.
;;
;;   func 0  $log     imported  → name "log"      (name section; import "env.log" is the fallback)
;;   func 1  $compute defined   → name "compute", exported "run"
;;   func 2  $helper  defined   → name "helper"   (called by $compute)
;;
;; So function_meta = [
;;   {0, name:"log",     imported:true,  exports:[]},
;;   {1, name:"compute", imported:false, exports:["run"]},
;;   {2, name:"helper",  imported:false, exports:[]},
;; ]
(module
  (import "env" "log" (func $log (param i32)))
  (func $compute (export "run") (result i32)
    call $helper
    i32.const 7)
  (func $helper
    nop))
