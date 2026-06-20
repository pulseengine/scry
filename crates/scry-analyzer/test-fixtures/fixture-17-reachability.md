# fixture-17-reachability

FEAT-022 slice-1 (REQ-011/SCRY-001) — `reachable_from_exports`.

`$exported` (func 0, exported `run`) calls `$helper` (func 1); `$dead` (func 2)
is neither exported nor called. scry's reachability is a BFS over the
over-approximated static call graph from the export + start roots:

- `reachable_from_exports = [0, 1]` — `$exported` and its callee `$helper`.
- `$dead` (2) is **absent** — a consumer may soundly prune it.

The set is a sound **superset** of concretely-reachable functions (a reachable
function is never omitted); mechanized in `proofs/rocq/Reachable.v`. Native
oracle: `feat022_reachable_from_exports`. Consumed via the crates.io library
`scry-sai-core` (`AnalysisResult.reachable_from_exports`), not the component.
