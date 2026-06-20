;; fixture-17-reachability — FEAT-022 slice-1 (reachable-from-exports).
;;
;; `$exported` (func 0, exported "run") calls `$helper` (func 1). `$dead`
;; (func 2) is neither exported nor called by anyone. scry's reachability is a
;; BFS over the (over-approximated) static call graph from the exported + start
;; roots, so:
;;   reachable_from_exports = [0, 1]   ($exported, $helper)
;;   $dead (2) is ABSENT — a consumer may soundly prune it.
;; Soundness: the set is a SUPERSET of concretely-reachable functions; a
;; reachable function is never omitted (REQ-011/SCRY-001).
(module
  (func $exported (export "run")
    call $helper)
  (func $helper
    nop)
  (func $dead
    nop))
