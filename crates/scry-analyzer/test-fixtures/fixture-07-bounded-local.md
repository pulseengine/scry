# fixture-07-bounded-local

The **non-vacuous soundness-oracle** input (FEAT-015, reviewer finding #4).

`fixture-02`'s only checkable local is a function parameter, which the
analyzer initialises to `⊤ = [i64::MIN, i64::MAX]`. The soundness assertion
there — "concrete ∈ ⊤" — is trivially true for every input, so it can never
falsify an unsound analyzer. This fixture gives the oracle teeth: a *declared*
local is set to a constant, so the analyzer infers a **bounded** interval for
it, and the concrete result is observable and must lie inside that interval.

## Source

```wat
(module
  (func (export "bounded") (result i32)
    (local i32)        ;; local 0, zero-init ⇒ abstract [0, 0]
    i32.const 100
    local.set 0        ;; local 0 ⇒ abstract [100, 100]
    local.get 0))      ;; concrete result = 100
```

## Expected post-analysis state

| instruction   | local 0 abstract | operand stack |
|---------------|------------------|---------------|
| (entry)       | `[0, 0]`         | —             |
| `i32.const 100` | `[0, 0]`       | `[100,100]`   |
| `local.set 0` | `[100, 100]`     | —             |
| `local.get 0` | `[100, 100]`     | `[100,100]`   |

At the final program point local 0 is `[100, 100]` — **bounded, not `⊤`**.

## Oracle

- Concrete: `bounded()` returns `100`.
- Soundness: `100 ∈ [100, 100]` (the analyzer's bounded interval for local 0).
- Non-vacuity: the harness asserts the interval is **not** `⊤`, so a buggy
  analyzer that dropped the `local.set` (leaving `[0,0]`) or computed a wrong
  bound would fail `100 ∈ …`. Verified live in
  `crates/scry-host-tests/tests/soundness.rs::fixture_07_bounded_local`.
