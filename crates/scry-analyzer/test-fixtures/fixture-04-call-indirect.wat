(module
  ;; FEAT-006 — sound call_indirect resolution.
  ;;
  ;; A 3-entry funcref table populated by a single active element
  ;; segment at constant offset 0 with function indices [0, 1, 2].
  ;; Two entry points exercise the two resolution regimes:
  ;;
  ;;   * `dispatch_const` pushes a *constant* index (1) and calls
  ;;     through the table — scry resolves this PRECISELY to the
  ;;     single target table[1] = func 1 (an `Info` diagnostic,
  ;;     edge tagged `sound`).
  ;;   * `dispatch_unknown` pushes its i32 *parameter* (abstract
  ;;     value = top) as the index — scry cannot constrain it, so
  ;;     it over-approximates to the WHOLE table {0, 1, 2} (a
  ;;     `Warning` "call_indirect index unconstrained — 3 targets",
  ;;     edge still tagged `sound`: an over-approximation is sound).
  ;;
  ;; All three table targets share the type `(func (result i32))`
  ;; (type 0), which is the type named by both `call_indirect`s.

  (type (;0;) (func (result i32)))           ;; table-target signature
  (type (;1;) (func (param i32) (result i32))) ;; dispatch_unknown signature

  (table (;0;) 3 3 funcref)

  ;; Active element segment: constant offset 0, funcs [0, 1, 2].
  (elem (;0;) (i32.const 0) func 0 1 2)

  ;; Table targets — each returns a distinct constant.
  (func (;0;) (type 0) (result i32)
    i32.const 100)
  (func (;1;) (type 0) (result i32)
    i32.const 200)
  (func (;2;) (type 0) (result i32)
    i32.const 300)

  ;; Constant index → precise single-target resolution {func 1}.
  (func (;3;) (export "dispatch_const") (type 0) (result i32)
    i32.const 1
    call_indirect (type 0))

  ;; Parameter index (abstract top) → whole-table over-approximation.
  (func (;4;) (export "dispatch_unknown") (type 1) (param i32) (result i32)
    local.get 0
    call_indirect (type 0)))
