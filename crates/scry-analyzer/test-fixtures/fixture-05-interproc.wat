(module
  ;; FEAT-007 — compositional summary-based interprocedural AI.
  ;;
  ;; The headline win over v0.4: a `call` site now applies the
  ;; callee's abstract summary (or, for a small non-recursive callee
  ;; with concrete argument intervals, a context-sensitive
  ;; re-evaluation) instead of pushing `top` per result. v0.4 modelled
  ;; `main()` calling `add_one(41)` as `top`; v0.5 infers `{42, 42}`.
  ;;
  ;; Three entry points exercise the regimes:
  ;;
  ;;   * `add_one(x) = x + 1` — a small, non-recursive leaf. Its
  ;;     context-insensitive summary is `top -> top` (because
  ;;     `top + 1 = top`), but it is flagged context-sensitive, so a
  ;;     caller with a concrete argument re-evaluates it precisely.
  ;;   * `main() = add_one(41)` — pushes the constant 41 and calls
  ;;     `add_one`. Because `add_one` is small + non-recursive and the
  ;;     argument interval `{41, 41}` is more precise than top, scry
  ;;     re-evaluates `add_one` with param 0 = `{41, 41}` and pushes
  ;;     the precise result `{42, 42}`. THIS is the interprocedural
  ;;     precision win.
  ;;   * `factorial(n)` — a self-recursive function. It is in a
  ;;     non-trivial call-graph SCC (a self-loop), so it is flagged
  ;;     `recursive` and uses the sound context-INSENSITIVE
  ;;     `top`-summary. Its summary result is `top` and it is never
  ;;     re-evaluated context-sensitively — guaranteeing termination.
  ;;
  ;; The recursion handling is what makes the analysis provably
  ;; terminating: a recursive callee NEVER triggers the re-eval path,
  ;; and a hard call-depth backstop (REEVAL_MAX_DEPTH = 8) plus an
  ;; op-count threshold (REEVAL_MAX_OPS = 64) bound re-evaluation even
  ;; if SCC detection ever missed an edge.

  (type (;0;) (func (param i32) (result i32))) ;; add_one / factorial
  (type (;1;) (func (result i32)))             ;; main

  ;; add_one(x) = x + 1. Small, non-recursive leaf.
  (func $add_one (;0;) (type 0) (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add)

  ;; main() = add_one(41). The call site re-evaluates add_one with
  ;; the concrete argument {41,41} and obtains {42,42} — where v0.4
  ;; would have pushed top.
  (func $main (;1;) (export "main") (type 1) (result i32)
    i32.const 41
    call $add_one)

  ;; factorial(n): self-recursive (n * factorial(n-1)). Modelled
  ;; soundly with the context-insensitive top-summary; the recursive
  ;; self-call uses the (sound, imprecise) summary so the analysis
  ;; terminates. The body uses i32.mul / i32.sub which are in the
  ;; supported set; the recursion itself is what forces the
  ;; top-summary. (The concrete branch is modelled imprecisely —
  ;; control flow degrades — but the summary stays sound: top.)
  (func $factorial (;2;) (export "factorial") (type 0) (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.sub
    call $factorial
    local.get 0
    i32.mul))
