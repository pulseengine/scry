;; fixture-07-bounded-local — a NON-VACUOUS soundness-oracle input (FEAT-015).
;;
;; fixture-02's only checkable local is a function parameter, which the
;; analyzer initialises to ⊤ = [i64::MIN, i64::MAX]; "concrete ∈ ⊤" is
;; trivially true for every input, so that oracle can never falsify an
;; unsound analyzer (reviewer finding #4). This fixture gives the oracle
;; teeth: a *declared* local is set to a constant, so the analyzer infers a
;; BOUNDED interval [100, 100] for it (zero-init [0,0], then local.set of the
;; constant). The function returns that local, so its concrete value is
;; observable (100) and must lie inside the bounded abstract interval. A
;; buggy analyzer that dropped the local.set (leaving [0,0]) or inferred a
;; wrong bound would be caught — the assertion is real, not vacuous.
(module
  (func (export "bounded") (result i32)
    (local i32)        ;; local 0, zero-init ⇒ abstract [0, 0]
    i32.const 100
    local.set 0        ;; local 0 ⇒ abstract [100, 100]
    local.get 0))      ;; concrete result = 100
