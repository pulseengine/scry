# Changelog

All notable changes to scry are documented here.

Format: [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versioning: [SemVer 2.0](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added — crates.io publishing

- **The reusable library crates are now publishable to crates.io**, mirroring
  `pulseengine/synth`: a `Publish to crates.io` workflow
  (`.github/workflows/publish-to-crates-io.yml`) fires on every `v*` tag
  alongside `release.yml`, driven by `scripts/publish.rs` — a leaf-first
  dependency-ordered publisher with a 10-attempt / 40s retry loop to ride out
  crates.io index propagation, using the org-wide `CRATES_IO_TOKEN`.
- **Published set** (the genuine reusable work body), under the **`scry-sai-*`
  namespace** (SAI = Sound Abstract Interpretation): `scry-sai-interval`,
  `scry-sai-taint`, `scry-sai-octagon`, `scry-sai-provenance` (leaves) →
  `scry-sai-core`. The crates.io **package** name is `scry-sai-*`; the Rust
  crate (`[lib] name`, e.g. `scry_interval`) and the on-disk directory
  (`crates/scry-interval/`) keep their existing names — the witness DEC-034
  trick — so `use scry_interval` and the Bazel target paths are unchanged.
  Internal path deps now carry `version` so `cargo publish` rewrites them to the
  crates.io coordinate.
- **Wasm-component crates** (`wasm-lattice`, `scry-analyzer`) are being migrated
  to the `scry-sai-*` namespace + self-contained `wit_bindgen::generate!`
  bindings so they build and publish under plain `cargo` as well as Bazel — in a
  follow-up PR (it touches the `//:scry` composition and needs full CI
  re-validation). Until then they remain `publish = false` and ship as signed
  `.wasm` release assets. The `scry-host-tests` and `scry-mcdc` harnesses remain
  unpublished.

### Changed

- **`workspace.package.version` aligned to the release-tag line: `0.1.0` →
  `1.9.0`** so the crate version on crates.io matches the `v1.x` release
  artifacts and `SCRY_VERSION`. A future release bump must move the tag, this
  version, and the internal path-dep `version` fields in lockstep (the
  crates.io publish workflow asserts tag == workspace version). The first
  crates.io publish therefore lands on the next release tag.

## [1.9.0] — 2026-06-14

Headline: **the octagon gains Miné strong (tight) closure — pure algebra,
no analyzer output change.** This closes the referenced-paper precision item
AC-011 (FEAT-016 slice-3). Strong closure derives a ±difference bound between
two variables from their unary bounds (`x ≤ 10 ∧ y ≥ 0 ⟹ x − y ≤ 10`) that
plain Floyd–Warshall cannot. FEAT-016's acceptance criterion was already met in
v1.8.0; this is the final precision refinement of the octagon arc.

### Added

- **`scry_octagon::strong_close`** — Floyd–Warshall closure followed by the
  octagon tightening `m[i][j] := min(m[i][j], ⌊(m[i][ī] + m[j̄][j])/2⌋)` and a
  re-close. Sound for integers via the floor (`div_euclid`), matching
  `bound_of`'s projection rounding. `bound_of` now projects through
  `strong_close`.
- **Mechanized soundness** (`proofs/rocq/OctagonStrongClose.v`,
  `strong_close_step_sound`): from `−2·vi ≤ a` and `2·vj ≤ b`, the tightened
  bound `⌊(a+b)/2⌋` over-approximates `vj − vi` — the step drops no concrete
  integer point. No admits/axioms; verified by the `rocq-proofs` CI job (and
  locally with Coq 9.0.1).
- **3 new γ-sweep tests** in scry-octagon: the precision win
  (`strong_close_derives_difference_from_unary_bounds`: derives `x_0 − x_1 ≤ 10`
  from unary where `close` gives INF), concretization-preservation over a grid,
  and bottom-preservation.

### Not changed (honest scope)

- **The analyzer output is identical to v1.8.0.** Strong closure tightens
  difference/sum bounds, never a variable's own unary bound, and the analyzer
  projects the octagon back to **per-variable intervals** (which read unary
  bounds) — so on the current corpus, where the analyzer generates only
  difference + unary constraints, strong vs. plain closure is invisible at the
  output. All fixture invariants (08–11) are byte-identical. `SCRY_VERSION` →
  1.9.0 is a release stamp. The precision becomes observable only when a
  consumer reads the relational (off-diagonal) bounds or the analyzer generates
  sum constraints — future work, not claimed here.

### Falsification statement

What v1.9 claims, made falsifiable: **strong closure is sound (drops no
concrete point) and strictly more precise than Floyd–Warshall on a constraint
system where a difference is implied only by unary bounds.** Falsifier: the
γ-sweep test asserts `strong_close` and the base system admit exactly the same
concrete points (soundness), and `strong_close_derives_difference_from_unary_bounds`
asserts it derives `x_0 − x_1 ≤ 10` where `close` leaves INF (precision); the
Rocq `strong_close_step_sound` independently proves the tightening step. What
v1.9 does **not** claim: any change to the analyzer's interval output (see
above), nor the full integer tight closure's extra unary even-ification.

## [1.8.0] — 2026-06-13

Headline: **the octagon relational product is wired into the analyzer — a loop
counter bounded by a VARIABLE relation (`i < n`, `n` not constant) now stays
bounded.** This is FEAT-016 slice-2b-ii (DD-015), the slice that moves the
FEAT-016 acceptance criterion: a relational constraint between two locals is
preserved across loop iterations instead of being widened away. It builds on
the v1.7 octagon primitives, now carried through the interpreter in lockstep
with the intervals.

### Added / Changed

- **Octagon carried through the structured-CFG interpreter** (`FuncCtx.octagon`,
  dimension = local count). It is joined / widened / **narrowed** in lockstep
  with the interval locals at every merge point — block exit, the loop
  `entry ⊔ back-edges` join, the widening threshold, and (crucially) the
  narrowing phase, because octagon widening drops a slowly-growing difference
  bound (`i − n`) to ⊤ exactly as interval widening drops a counter, and
  narrowing is what re-derives it from the guard. The branch break-state now
  carries the octagon too.
- **Relational guard refinement** (`try_guard_brif_rel`): the idiom
  `local.get A; local.get B; <signed cmp>; br_if D` adds the octagon difference
  constraint the comparison implies on each edge (`A − B ≤ c`) — the
  variable-relation case the v1.6 constant peephole cannot reach.
- **Octagon assignment transfers** (`octagon_transfer` / `classify_store`): a
  `local.set`/`local.tee` is classified by a look-behind over its producer ops
  into `x := c` / `x := y` / `x := y ± c` (the in-place increment `x := x + c`
  uses the v1.7 SHIFT, carrying a relation across the loop body). **The safety
  net: any write the transfer does not model `forget`s that variable's octagon
  relations** — a stale relation is never retained (the soundness rule for the
  whole slice). `br_table` / unsupported ops reset the octagon to ⊤.
- **Reduced product at emission** (`reduce_locals` / `inject_intervals`): inject
  the current interval bounds into the octagon, close, and project each variable
  back as an integer interval, `meet`-ing it with its interval (DD-015 2c
  observability — **no WIT change**). This is where `i ≤ n ∧ n ≤ 10 ⟹ i ≤ 10`.
  The entry octagon of each loop is likewise seeded with the entry interval
  bounds so the relation survives the first `entry ⊔ back-edge` join. A `top`
  octagon (no relations) projects to the identity, so all prior interval-only
  behaviour is preserved exactly.
- **New fixture** `fixture-11-var-bound` (counter bounded by `i < n`, `n` in a
  local) + native oracle `feat016_octagon_var_bounds_counter` (`i` converges to
  `[0,10]`, `hi ≤ 10`, where interval + constant-guard alone give ⊤) + the
  fixture in the live scry-mcdc corpus. MC/DC proved **164 → 180** (mac local;
  CI/linux is the gate), gate floor held at 155 (monotone). `SCRY_VERSION` →
  1.8.0.

### Soundness evidence

The integration composes pieces proven / falsified in isolation, applied at the
established merge points: the octagon transfers (`forget`, assign, the
increment shift) are γ-sweep-falsified in `scry-octagon` (v1.7); the
octagon→interval projection rounding is mechanized in
`proofs/rocq/OctagonProject.v` (`proj_interval_sound`, v1.7); the loop
fixpoint's post-fixpoint soundness is the generic `LoopFixpoint.v`
(`loop_postfixpoint_sound`, v1.5) instantiated at the octagon transfer; and
injecting true interval bounds only tightens. The integration-level gate is the
native + host soundness oracle over the whole fixture corpus (abstract ⊒
concrete), plus the forget-on-unmodelled-write safety net.

### Falsification statement

What v1.8 claims, made falsifiable: **a loop counter bounded by a variable
relation `i < n` converges to a finite interval, soundly.** Falsifier:
`fixture-11-var-bound` counts `i` up while `i < n` with `n = 10` held in a
local; if the analyzer reports `i` as ⊤ after the loop (the interval/const-guard
behaviour, since the guard compares two locals), or if the concrete result `10`
falls outside `i`'s interval, the claim is false (the native + host soundness
oracles check `hi ≤ 10` and `10 ∈ [lo,hi]`). What v1.8 does **not** claim:
Miné strong/tight closure (the extra octagon precision of AC-011) — that is the
remaining slice-3; and relations more complex than a single difference against
a guarded counter may still widen.

## [1.7.0] — 2026-06-13

Headline: **the octagon relational domain grows the primitives the analyzer
needs — pure algebra, no analyzer behavior change yet.** This is the
smallest-sound-first prerequisite for FEAT-016 slice-2b-ii (DD-015): the
relational loop fixpoint that will let a counter bounded by a *variable*
relation (`i < n`, `n` not constant) stay bounded — the case guard refinement
(v1.6, constant guards only) cannot reach. v1.7 lands and proves the octagon
operations in isolation; v1.8 wires them into the interpreter.

### Added

- **Analyzer-facing octagon primitives** (`crates/scry-octagon`), all
  coherence-maintaining (they set both a DBM cell and its `m[i][j] = m[j̄][ī]`
  twin, so `close` can propagate a difference bound + a unary bound into a
  tighter unary bound — the relational product's whole point):
  - `add_diff` / `set_upper` / `set_lower` — coherent difference and unary
    constraints.
  - `forget(k)` — the sound havoc transfer for a write of an unknown value to
    local `k` (close, then clear `x_k`'s rows/cols; constraints among the other
    variables are preserved).
  - `assign_const` / `assign_copy` / `assign_add_const` — the transfer
    functions for `local.set` of a const / a copy / `x := y + c`. The in-place
    increment `x_k := x_k + c` (the loop-counter case) does **not** forget — it
    SHIFTS every bound touching `x_k`, which is exactly what carries a
    relational bound like `x_k − x_n ≤ −1` across the increment (→ `≤ 0`).
  - `bound_of(k)` — project the closed octagon onto variable `x_k` as an
    integer interval, halving the doubled DBM bounds with floor/ceil rounding;
    `None` iff infeasible.
  - `narrow` — octagon narrowing, recovering bounds widening discarded.
- **Mechanized projection soundness** (`proofs/rocq/OctagonProject.v`,
  `proj_interval_sound`): reading `2·x ≤ U` back as `x ≤ ⌊U/2⌋` (and the lower
  dual) over-approximates the variable's true range — the soundness link the
  v1.8 octagon→interval fold will rely on. No admits/axioms; verified by the
  `rocq-proofs` CI job (and locally with Coq 9.0.1).
- **9 new γ-sweep tests** in scry-octagon falsifying every primitive against
  the concrete octagon semantics on a grid of points (the crate's established
  evidence kind), including the two that pin the relational mechanism:
  `coherent_diff_plus_unary_projects_to_tighter_unary` (`i ≤ n−1 ∧ n ≤ 10 ⟹
  i ≤ 9`) and `increment_shifts_relations_not_forgets`.

### Not changed

- **The analyzer output is identical to v1.6.0.** The octagon is not yet
  carried through the interpreter — `SCRY_VERSION` → 1.7.0 is a release stamp,
  not a behavior change. FEAT-016 remains `proposed`; the interpreter
  integration (fixture: a variable-bounded loop counter) is v1.8.0.

### Falsification statement

What v1.7 claims, made falsifiable: **the octagon primitives are sound — each
transfer over-approximates the concrete semantics, and projecting a bound to an
integer interval drops no concrete value.** Falsifier: the γ-sweep tests check
each primitive against `gamma` (the concrete DBM semantics) on a grid; if any
transfer admits fewer points than the concrete operation produces — e.g. if the
increment shift dropped the `x_k − x_n` relation, or `bound_of` rounded the
wrong way — a sweep assertion fails. The Rocq `proj_interval_sound` independently
proves the projection rounding. What v1.7 does **not** claim: any analyzer-
visible precision improvement — that is v1.8, when the octagon is integrated.

## [1.6.0] — 2026-06-05

Headline: **guard refinement — a loop counter bounded by its own exit test now
converges to a finite interval instead of ⊤.** v1.5 (slice-2a) gave loops a
real interval fixpoint, but a counter `i` bounded only by the exit test
`i < C` still widened to ⊤ because the interval domain could not read the
guard. v1.6 (FEAT-016 slice-2b-i, DD-015) lets the analyzer refine a local's
interval by the half-space implied by a signed `local <cmp> const` guard, then
**narrows** the over-widened header back down — the first step of the
relational track.

### Added / Changed

- **Guard refinement (FEAT-016 slice-2b-i).** A peephole (`try_guard_brif`)
  recognises the `local.get L; i32.const C; i32.<cmp>; br_if D` idiom (and the
  3-op `local.get L; i32.eqz; br_if D` form). On the **taken** edge it meets
  `L` with the guard's half-space (recorded to the branch target); on the
  **not-taken** edge it meets `L` with the complement (`refine_interval`). Only
  **signed** comparisons are refined — unsigned wrap semantics would make the
  signed half-space unsound, so they are deliberately left unrefined.
- **Interval narrowing at loop headers.** `loop_region` gains a narrowing phase
  after widening: it re-applies the body and replaces the header's infinite
  bounds with the recomputed finite ones, descending to a tighter sound
  post-fixpoint. A guard-bounded counter now converges to `[0,10]` where
  slice-2a widened it to ⊤.
- **Fixpoint state-leak fix.** The widening/narrowing passes re-run the loop
  body many times with deliberately-coarse (often ⊤) intermediate headers;
  their `br`-to-outer-label states are now snapshotted and restored so only the
  converged header contributes to the enclosing block's exit join. Without this
  the post-loop value stayed ⊤ (the stale ⊤-era taken edge poisoned the join).
- **Mechanized soundness, in-slice** (`proofs/rocq/GuardRefine.v`,
  `refine_sound`): meeting an interval with a guard's half-space never drops a
  concrete value that satisfies the guard, so the refined per-edge invariant
  over-approximates the states flowing down that edge. No admits/axioms;
  verified by the `rocq-proofs` CI job (and locally with Coq 9.0.1).
- **MC/DC proved rose 155 → 164** (macOS local; canonical x86_64-linux CI is
  the gate) with the new `fixture-10-guard-bound` in the live gate driving the
  guard-refinement / narrowing decisions. Gate floor raised 148 → 155 proved
  (still below the new value, monotone since added fixtures only add coverage);
  `full` stays floored at 3 (platform-sensitive). New native oracle
  `feat016_guard_bounds_counter` (counter converges to `[0,10]`, `hi ≤ 10`).
  `SCRY_VERSION` → 1.6.0.

### Known limitations

- **Constant guards only** (slice-2b-i). A counter bounded by a *variable*
  relation (`i < n`, `n` not constant) still widens to ⊤ — preserving such
  inter-variable constraints across iterations is the **octagon relational
  product** of slice-2b-ii, with Miné closure as slice-3 (DD-015). FEAT-016
  remains `proposed`.

### Falsification statement

What v1.6 claims, made falsifiable: **a loop counter bounded by a constant in
its own signed exit guard converges to a finite interval, soundly.** Falsifier:
`fixture-10-guard-bound` counts `i` up while `i < 10`; if the analyzer reports
`i` as ⊤ after the loop (the slice-2a behaviour), or if the concrete result
`10` falls outside `i`'s interval, the claim is false (the native + host
soundness oracles check exactly this — `hi ≤ 10` and `10 ∈ [lo,hi]`). What v1.6
does **not** claim: precision on variable-bounded counters, or refinement of
unsigned comparisons — both still widen until slice-2b-ii.

## [1.5.0] — 2026-06-04

Headline: **a real loop fixpoint — loop-carried values now converge instead
of being discarded.** v1.4 made loops sound by write-set havoc (widen every
written local to ⊤). v1.5 (FEAT-016 slice-2a, DD-015) replaces that with a
sound iterate-then-widen abstract interpreter, so a local written in a loop
keeps the precise interval it converges to.

### Added / Changed

- **Structured-CFG interval fixpoint (FEAT-016 slice-2a).** `run_function_body`
  becomes a recursive interpreter with **break-state accumulation** — the
  correct Wasm structured dataflow: `br`/`br_if` record the current locals
  into the targeted label; a `block`'s exit is the fall-through joined with
  its break states; a `loop` iterates `header = entry ⊔ back-edges`, widening
  after the threshold to a post-fixpoint (terminating via scry-interval's
  ascending-chain `widen`). `if` / `br_table` / non-empty block types keep
  the sound v1.4 havoc/scrub fallback. A loop-written local now converges
  (e.g. `[0,7]`) where v1.4 gave ⊤.
- **i32 comparison family lifted** (`eqz`/`eq`/`ne`/`lt`/`gt`/`le`/`ge` →
  the bounded `[0,1]`, no local scrub). Loop exit tests use these; under the
  v0.2 catch-all they scrubbed every local, which silently degraded loops
  (so v1.4's loop precision was partly masked — now genuinely exercised).
- **Mechanized soundness, in-slice** (`proofs/rocq/LoopFixpoint.v`,
  `loop_postfixpoint_sound`): a post-fixpoint of a sound transfer, covering
  the entry, over-approximates every concrete loop iterate. No admits/axioms;
  verified by the `rocq-proofs` CI job.
- **MC/DC proved rose 131 → 155** with the new `fixture-09-loop-converge` in
  the live gate (full-MC/DC = 4 on the canonical x86_64-linux CI build; it is
  5 on macOS — that metric is platform-sensitive, so the gate floors `proved`
  primarily). Floor calibrated to CI at 148 proved / 3 full. New native
  oracles for fixture-08
  (loop-invariant survives, now via the real fixpoint) and fixture-09
  (loop-written local converges to a bounded interval). `SCRY_VERSION` → 1.5.0.

### Known limitations

- **Interval-only** (slice-2a of FEAT-016). A loop *counter* like `i` (bounded
  only by the relation `i < n`) still widens to ⊤ — the **octagon relational
  product** that preserves such constraints across iterations is slice-2b
  (DD-015), with Miné closure as slice-3. FEAT-016 remains `proposed`.

### Falsification statement

What v1.5 claims, made falsifiable: **a local written to a constant inside a
loop converges to a bounded interval, soundly.** Falsifier:
`fixture-09-loop-converge` writes `m=7` each iteration; if the analyzer
reports `m` as ⊤ after the loop (the v1.4 havoc behaviour), or if the
concrete result (`0` or `7`) falls outside `m`'s interval, the claim is false
(the native + host soundness oracles check exactly this). What v1.5 does
**not** claim: precision on relationally-bounded loop counters — those still
widen until slice-2b.

## [1.4.0] — 2026-06-04

Headline: **the analyzer models loops.** Through v1.3 the interval pass
scrubbed every local to ⊤ on any control flow (`block` / `loop` / `if` hit
the v0.2 `UnsoundnessFallback`). v1.4 lands the first slice of FEAT-016
(DD-014): a sound structured-control model by **write-set havoc** — the
beginning of the 2.0 capability track and the prerequisite for the octagon
relational product (FEAT-016 slice-2).

### Added / Changed

- **Structured-control interval fixpoint via write-set havoc (FEAT-016
  slice-1).** `run_function_body` now intercepts `block` / `loop` / `if`
  regions (empty block type): it widens to ⊤ exactly the locals the region
  writes (`local.set` / `local.tee` — the only operators that write a Wasm
  local, so the static `region_write_set` scan is complete) and **preserves
  every other local's precise pre-region interval**, then continues analysis
  past the region. Non-empty block types and already-degraded state keep the
  sound v0.2 scrub fallback; `if` pops its condition operand. Loop-invariant
  locals now survive loops instead of being lost.
- **Mechanized soundness, in-slice (`proofs/rocq/WriteSetHavoc.v`).**
  `havoc_sound`: the havocked abstract post-state over-approximates every
  concrete post-state that writes only the region's write set (so: any number
  of loop iterations). No admits, no axioms; verified by the `rocq-proofs`
  CI job.
- **MC/DC coverage rose** (the new control-flow decisions, exercised by the
  new `fixture-08-counted-loop` in the live gate): proved conditions
  **119 → 131**, full-MC/DC decisions **4 → 5**. The `mcdc` gate floor is
  raised to 125 / 5 to lock in the gain (DD-013).
- New oracles: native `feat016_loop_invariant_local_survives` (drives
  `analyze()` directly) and the end-to-end host test
  `fixture_08_loop_invariant_survives`. `SCRY_VERSION` → 1.4.0.

### Known limitations

- This is slice-1 of FEAT-016: loop-**written** locals widen to ⊤ (no
  loop-carried precision yet); the relational octagon product that keeps
  `i < len` / `base+off` constraints across iterations is slice-2 (tracked in
  DD-014). FEAT-016 is therefore not yet complete.

### Falsification statement

What v1.4 claims, made falsifiable: **a loop-invariant local survives a loop
with its precise interval, soundly.** Falsifier: `fixture-08-counted-loop`'s
`k` is set to 42 before the loop and never written inside it; if the
analyzer reports `k` as ⊤ (or omits it) after the loop, or if the concrete
`counted(n) = 42` ever falls outside `k`'s abstract interval, the claim is
false (the native + host soundness tests check exactly this). What v1.4 does
**not** claim: precision on loop-**written** locals — those soundly widen.

## [1.3.1] — 2026-06-03

Headline: **MC/DC is now a live CI gate with a published truth-table
visualisation.** v1.2 landed the witness MC/DC measurement over the real
analyzer core but ran it as a release-time evidence step; v1.3.1 rolls it
into the test suite (DD-013) so it runs on every change and a coverage
regression turns the build red — REQ-010 becomes a live oracle, not a
one-shot artifact. The shipped analyzer artifact is behaviour-identical
(this is CI/tooling/evidence only; `SCRY_VERSION` → 1.3.1 to track the tag).

### Added

- **`crates/scry-mcdc/mcdc-gate.sh` + the `mcdc` CI job.** Builds the harness
  to `wasm32-wasip1`, runs `witness instrument / run --invoke-all / report`
  over the real analyzer decisions, and **fails the build** if
  `conditions_proved` (< 110) or `decisions_full_mcdc` (< 4) regress — read
  from `report.json`, not stdout. CI provisions `witness` + `witness-viz`
  pinned to a witness commit (so the floor stays meaningful across witness
  upgrades) and caches the built binaries.
- **Static truth-table visualisation (`witness-viz export`).** The same job
  turns the report into a static HTML site — an overview page plus one page
  per decision and per gap row, each rendering the truth table — uploaded as
  the `scry-mcdc-viz` CI artifact and GitHub-Pages-deployable. The witness
  philosophy ("the truth table is the artifact, not the percentage") made
  inspectable. Aggregate counts are committed as `evidence/viz-summary.json`.

### Falsification statement

What v1.3.1 claims, made falsifiable: **the MC/DC measurement is a gate, not
a snapshot — a code change that drops a proved condition fails CI.**
Falsifier: on a branch, weaken the analyzer so a transfer-function condition
no longer proves, push, and observe the `mcdc` job stay green; if it does,
the gate is not live. What it does **not** claim: that the residual gaps
(v1.2) are closed — the floor (110/4) sits below the full condition count by
design, gating against *regression* while the named gaps remain open.

## [1.3.0] — 2026-06-02

Headline: **the abstract-vs-concrete soundness oracle is now live, with no
skip.** Through v1.2 `scry-host-tests/tests/soundness.rs` ran the analyzer
behind a `skip_if_wac_limitation` fallback — the composed `//:scry` couldn't
load in wasmtime (the wac/wasmtime-45 root-import limitation), so the
abstract side silently degraded to a concrete-only check that could not
catch an unsound analyzer. FEAT-013 (v1.1) made the analyzer self-contained;
v1.3 removes the skip and makes the oracle total and non-vacuous.

### Changed

- **No skip (FEAT-015 / reviewer finding #3).** Deleted the dead
  `skip_if_wac_limitation` / `is_wac_import_dependencies_limitation` helpers.
  `fixture_01/02/05` now call `run_analyzer(...)?` and `composed_component_-
  loads` calls `Component::from_file(...)?` — every test **hard-fails** on an
  analyzer error. The abstract-vs-concrete soundness assertion runs on every
  CI invocation; there is no path that quietly downgrades to concrete-only.

### Added

- **`fixture-07-bounded-local` — a non-vacuous soundness oracle (FEAT-015 /
  reviewer finding #4).** `fixture-02`'s only checkable local is a parameter
  initialised to `⊤`, so "concrete ∈ ⊤" is trivially true and can never
  falsify an unsound analyzer. The new fixture sets a declared local to a
  constant, so the analyzer infers a **bounded** interval (`[100, 100]`,
  confirmed live). The harness asserts the interval is **not `⊤`** *and*
  contains the concrete return value (`100`), so a buggy analyzer (dropped
  `local.set`, or a wrong bound) would be caught.

### Falsification statement

What v1.3 claims, made falsifiable: **the shipped analyzer is run live on
every fixture and every observed concrete value lies inside the analyzer's
abstract result — including a bounded (non-`⊤`) interval.** Falsifier: run
`cargo test -p scry-host-tests --test soundness` against the shipped
component (`SCRY_COMPONENT_PATH` or `bazel build //:scry`); if any fixture's
abstract side is skipped, or `fixture-07`'s local 0 is `⊤`, or any concrete
value falls outside its abstract interval, the claim is false. The oracle no
longer has a skip path, so "green" now means "ran and held," not "didn't
run."

## [1.2.0] — 2026-05-31

Headline: **the analyzer's real decisions now carry MC/DC coverage
evidence.** v1.2 closes the witness step of the original feature loop,
blocked since v0.1 by the composition gap (v1.1 made `analyze()` runnable;
v1.2 makes it *instrumentable*). Per DD-012, the analyzer's decision logic
is extracted into a pure, bindgen-free core so witness can reconstruct an
MC/DC truth table over the **real** transfer functions driven by the
**real** corpus — not a synthetic proxy.

### Added / Changed

- **`crates/scry-analyze-core` (FEAT-014 / DD-012).** The analyzer's full
  pipeline — wasmparser parse, the interval + region-memory fixpoint, the
  call-graph / SCC / summary machinery, and the taint (noninterference)
  walk, with ~40 helpers — moves out of `scry-analyzer` into a pure
  `#![no_std]` crate with plain-Rust result types mirroring the WIT. Same
  dual-compile pattern as scry-interval: it builds natively, to
  `wasm32-unknown-unknown` (witness instruments it), and into the shipped
  `wasm32-wasip2` component. The soundness-critical transfer functions now
  run on pure types with no per-op WIT marshalling.
- **`scry-analyzer` is now a thin canonical-ABI wrapper.** It keeps only
  `struct Component`, the `Guest` impl, the field-by-field WIT⇄core
  conversions (pure boilerplate, no analysis), and the `export!` macro;
  `analyze()` delegates to `scry_analyze_core::analyze`. Its deps slim to
  `scry-analyze-core`. `bazel build //:scry` and the host-test soundness
  oracles stay green — the move is behaviour-identical.
- **`crates/scry-mcdc` — witness MC/DC over the real analyzer.** A harness
  whose 16 no-arg `run_*` exports drive `analyze()` over the corpus
  fixtures (5 fixtures × config variants: taint on/off, diagnostics on/off,
  widening 1 vs 3, plus an overflow fixture). `witness run --invoke-all`
  accumulates per-branch counters across all executions so MC/DC
  independence pairs exist. witness reconstructs **662 source-level
  decisions** and proves **119 conditions under MC/DC** (4 full-MC/DC),
  including conditions in the soundness-critical interval transfer
  functions — versus **0** proved by the discarded synthetic-domain spike.
- **`#[inline(never)]` on the scry-interval transfer functions** (per
  DD-012) so each keeps a standalone DWARF decision cluster for witness's
  reconstruction. The MC/DC predicate body (`witness-mcdc/v3`) is produced
  by `witness predicate --kind mcdc` for sigil to sign at release; the
  canonical truth table ships at `crates/scry-mcdc/evidence/report.json`.

### Known limitations

- MC/DC coverage is **partial-with-named-gaps**, not zero-gap. Some
  transfer-fn straddle→TOP decisions remain `no_witness`/`gap` (a witness
  multi-instance-attribution effect); each residual gap is named with its
  closing approach in `crates/scry-mcdc/README.md` (FEAT-014 AC#1's
  name-the-gap escape hatch). REQ-010 thus has initial structural-coverage
  evidence; full closure is tracked for v1.2.x.

### Falsification statement

What v1.2 claims, made falsifiable: **the witness MC/DC pipeline runs over
the analyzer's real decision logic and proves conditions inside the shipped
soundness-critical transfer functions.** Falsifier: rebuild
`crates/scry-mcdc` to `wasm32-wasip1` and run `witness instrument → run
--invoke-all → report --format mcdc-json`; if `report.json` does not show
proved (`full_mcdc`) conditions attributed to the interval transfer
functions' source lines, the claim is false. What v1.2 does **not** claim:
zero unresolved gap rows — the residual safety-relevant gaps are named, not
proved closed.

## [1.1.0] — 2026-05-30

Headline: **the shipped artifact is finally the real one.** v1.1 closes
the composition gap recorded as the v1.0.1 open finding (FEAT-013 /
DD-011): through v1.0 the composed `//:scry` was a ~4.6 KB hollow shell —
wac's `--import-dependencies` left both sub-components as root-level
component imports, which wasmtime 45 rejects, so `analyze()` could never
run and analyzer source never reached the shipped binary. v1.1 makes the
analyzer self-contained and executable.

### Added / Changed

- **`crates/scry-interval`** — new pure, zero-dep crate holding the
  interval + region-memory algebra, extracted from `wasm-lattice`
  (byte-identical transfer functions; soundness mechanized in
  `proofs/rocq/Soundness.v` + `Region.v`). Same dual-compile pattern as
  scry-octagon / scry-taint / scry-provenance.
- **Self-contained analyzer (FEAT-013 / DD-011).** The analyzer now links
  the interval/region (scry-interval), taint (scry-taint), and octagon
  (scry-octagon) algebra as Rust crate deps via a thin local `domain`
  module, instead of importing `pulseengine:wasm-lattice/domain` over WIT.
  The `scry` world drops the cross-component import (the `interval` record
  is declared locally), so the analyzer component imports only WASI and
  runs standalone. The wasm-lattice component still exports the same
  `domain` interface (DD-008 dogfood), now off the analyzer's execution
  path. `SCRY_VERSION` → 1.1.0.
- **`//:scry` is the analyzer component itself, not a `wac_compose`.** The
  actual mechanism that closes the gap: `wac compose` (as the
  `wac_compose` rule invokes it, with `--import-dependencies`) emits a
  component that *imports* `pulseengine:scry` at the root rather than
  embedding it — the hollow 2,669-byte shell wasmtime rejects. Since the
  analyzer is now self-contained, `//:scry` is a `genrule` that copies the
  public `scry_analyzer_component` alias (a multi-megabyte component with
  the analyzer embedded — ~3.17 MB on the verifying build, vs the prior
  2,669-byte hollow shell) to the stable `scry.wasm` name release.yml and
  the host harness read. 0 non-WASI imports, `wasm-tools validate` ok; the
  authoritative artifact digest ships in the release's `SHA256SUMS`. The
  genrule copies the macro's public `scry_analyzer_component` alias, not
  the private `_release` sub-target (a cross-package reference to the
  private target was the visibility error that broke an earlier cut).
- **Live runnable gate (`feat013_live_analyze_gate`).** A no-skip host
  test that loads the shipped component and invokes the live `analyze()`
  on a real module — the process exits non-zero if it cannot run. Prior
  to v1.1 it would have failed on the wasmtime root-level-import
  rejection; it now passes (6 program points on fixture-01).
- **Host-test config marshalling fixed.** `run_analyzer`'s dynamic
  `analysis-config` record sent only 2 fields; `analysis-config` has
  carried 3 since v0.8 (FEAT-009's `taint-policy`), so wasmtime rejected
  the call with "expected 3 fields, got 2". This was invisible until v1.1
  because the component never instantiated, so the call path was always
  skipped. With it fixed, the abstract-vs-concrete soundness oracle in
  `fixture_02` runs for the first time and passes — every concrete input
  lies in the reported abstract interval, with the unwritten param held
  at top.

### Falsifiable kill-criterion

Two binary properties, both now true (were both false through v1.0.1):
1. **AC#1** — a source edit to the analyzer changes the composed
   artifact's SHA-256 (the version bump moved it off the frozen
   `30f8d4e2…` hash that was identical across v0.9–v1.0.1).
2. **AC#2** — the live `analyze()` runs in wasmtime 45 on the shipped
   `//:scry` (`feat013_live_analyze_gate`, no skip path, exit 0).
If either regresses, the gap has reopened.


## [1.0.1] — 2026-05-30

### Fixed

- **`SCRY_VERSION` self-report corrected to the shipped version.** The
  `analyze()` diagnostic banner ("scry &lt;version&gt; — wasm-lattice
  cross-component import alive") hard-codes `SCRY_VERSION`, which was left
  at `"0.9.0"` when v1.0.0 shipped (the version-bump edit did not land in
  the v1.0.0 PR). The constant feeds only an `Info`-level diagnostic
  string — no soundness, invariant, or analysis behaviour was affected,
  and the v1.0.0 artifact is otherwise correct — but a v1.0.0 component
  that self-reports `0.9.0` is the kind of provenance mismatch scry
  exists to catch, so it is corrected here to `"1.0.1"`.

### Falsifiable kill-criterion

`grep 'SCRY_VERSION: &str = "1.0.1"' crates/scry-analyzer/src/lib.rs`
matches, and the released artifact's `analyze()` diagnostic reports the
same version string as the release tag. If the constant and the tag ever
disagree again, this release is wrong.

## [1.0.0] — 2026-05-29

Headline: **the safety goal closes**. v1.0 is the capstone: the mechanized
soundness proof now covers the full shipped v0.1–v0.4 domain stack, and
the six-domain credit dossier assembles the per-standard evidence map
that closes the top-level safety goal [[G-001]] — all three DO-333
technique classes (abstract interpretation, deductive proof, model
checking) are staffed with runnable, version-pinned, and now
mechanically-proven evidence. This is the "AI writes the code; here is
the proof it's sound" thesis made concrete.

### Added

- **Full-stack mechanized soundness** ([[FEAT-011]] AC#1). The Rocq
  proof extends from the v0.9 interval theorem to the whole shipped
  stack, each with **no admits and no axioms** (verified by
  `bazel test //proofs/rocq:...`):
  - `proofs/rocq/Region.v` — region-offset soundness and bounds-check-
    elision soundness (`in_bounds_sound`: a proven-in-bounds offset
    interval means every concrete access is in range — the loom
    REQ-004 use case), plus distinct-region non-aliasing.
  - `proofs/rocq/CallGraph.v` — the resolved `call_indirect` target set
    always contains the concrete target (`callgraph_resolution_sound`),
    reducing call-graph soundness to interval-index soundness; constant
    indices resolve precisely; disjoint indices are provably unreachable.
  - `proofs/rocq/Reachability.v` — the reachability lattice algebra
    (`Reachable` is the sound top; join over-approximates; partial
    order). Honest scope: lattice-proven, not yet analyzer-consumed.
- **Six-domain credit dossier** ([[FEAT-011]] AC#3) —
  `docs/credit-dossier-v1.md` ([[DOC-CREDIT-DOSSIER-V1]]). A
  REQ-001..008 → evidence map (mechanized / runnable / contract / paper)
  and a per-standard credit cross-walk for the abstract-interpretation
  technique class across DO-178C/DO-333, ISO 26262-6, IEC 61508,
  IEC 62304, EN 50128, and ECSS. Ships inside the cosign-signed release
  compliance bundle (REQ-005).
- **Safety-case closure.** New evidence nodes `Sn-005` (dossier →
  [[G-001]]) and `Sn-006` (mechanized stack → [[G-002]]); the G-002
  soundness evidence is upgraded from asserted/placeholder to
  mechanized. `SCRY_VERSION` → 1.0.0.

### Known limitations (deferred to v1.1+)

- **SpecTec→interval-transfer soundness-by-construction backend**
  ([[FEAT-011]] AC#2) — the one research-grade leg with real unknowns —
  is deferred to v1.1 rather than risk it blocking the milestone.
- The mechanized **interval `add`** models the no-wrap integer core; the
  shipped `i32_add` widens to ⊤ on possible 2³² wrap (trivially sound,
  `γ(⊤)=ℤ`). The WasmCert-Coq-backed wrap-aware proof is the named
  [[TE-004]] future slice.
- **Reachability** is lattice-proven but not yet consumed by analyzer
  code (deferred when the v0.4 call-graph slice shipped); the dossier
  credits the lattice algebra, not a shipped reachability transfer.
- Tool qualification (DO-330 / ISO 26262-8 §11) is out of scope.

### Falsifiable kill-criterion

The full v0.1–v0.4 domain-stack soundness proof builds with **no admits
and no axioms** — `bazel test //proofs/rocq:soundness_test
//proofs/rocq:region_test //proofs/rocq:callgraph_test
//proofs/rocq:reachability_test` all PASS. If any γ-soundness theorem
fails to close, the proof build goes red and v1.0's central claim — that
the shipped abstract domains over-approximate the concrete Wasm
semantics — is falsified.

## [0.9.0] — 2026-05-29

Headline: **relational reasoning + the first mechanized soundness proof**.
Two legs of [[FEAT-010]] land together: the octagon relational abstract
domain ([[AC-011]], Miné) and the first Rocq theorem proving scry's
interval transfer functions are *sound* — they over-approximate the
concrete integer semantics ([[AC-003]] / [[AC-001]]). Where the v0.2
`Lattice.v` proved only the order laws, v0.9 proves the Galois
soundness, including `add_sound` — the soundness of the interval `add`
the analyzer reduces `i32.add`/`i64.add` to.

### Added

- **Octagon relational domain** ([[FEAT-010]], [[AC-011]]). New pure,
  zero-dependency crate `crates/scry-octagon`: the standard
  Difference-Bound-Matrix encoding of `±x±y ≤ c` constraints —
  `top`/`bottom`/`is-bottom`, Floyd–Warshall `close`, `leq`/`join`
  (pointwise max of closed DBMs, over-approximating the union)/`meet`
  (pointwise min, exact intersection)/`widen` (keep-stable-drop-growing,
  for fixpoint termination)/`add-bound`. Like `scry-taint` /
  `scry-provenance`, the same source compiles to `wasm32-wasip2` (where
  `wasm-lattice`'s new WIT `octagon` record + `octagon-*` ops delegate to
  it — [[DD-008]] dogfood, so shipped == falsified code) and natively
  (where the host harness checks the lattice laws AND concretization
  soundness). The octagon crosses the WIT boundary as `(dim, list<s64>)`
  because the DBM is variable-length. Composes with the interval/region/
  taint domains rather than replacing them.
- **Mechanized interval-domain soundness** ([[FEAT-010]] AC#2,
  [[AC-003]]). `proofs/rocq/Soundness.v` proves, in Rocq with **no
  admits and no axioms**, that the interval transfer functions
  over-approximate the concrete integer semantics via a concretization
  `γ`: `γ(⊥)=∅`, constant soundness, `⊑`→γ-inclusion (the Galois
  order), `join` over-approximates the union, `meet` = intersection, and
  `add_sound` (`za∈γ(a) → zb∈γ(b) → za+zb ∈ γ(a⊞b)`). Extends the v0.2
  Rocq scaffold ([[FEAT-012]]). Verified by
  `bazel test //proofs/rocq:soundness_test` (9 theorems, 9 `Qed`, 0
  admits).
- **AADL `data Octagon`** in `spar/scry.aadl` (the relational domain on
  the lattice surface, mirroring `Interval`/`MemoryRegion`); rivet
  FEAT-010 flipped to `draft` with the narrow v0.9 scope; new
  `docs/octagon-and-soundness-v1.md` ([[DOC-OCTAGON-SOUNDNESS-V1]]);
  roadmap capability ladder extended.

### Known limitations (deferred to a later FEAT-010 slice)

- The analyzer's **loop-carried relational fixpoint** (maintaining an
  octagon over local pairs across loop iterations — AC#1's "across loop
  iterations"). v0.9 ships the domain + WIT dogfood + native
  falsification; wiring the relational fixpoint into the analyzer's
  two-phase walk is next (mirrors how FEAT-008 shipped the contract
  before the live `analyze()` path).
- Miné's **strong/tight closure** (a precision, not soundness,
  refinement).
- Importing the **WasmCert-Coq** `i32` module ([[TE-004]]) as the
  concrete model to mechanize the wrap-aware bounded `i32.add` transfer.
  `Soundness.v` proves the unbounded/no-wrap core; the shipped `i32_add`
  widens to `⊤` on possible wrap, which is trivially sound (`γ(⊤)=ℤ`).
- As with FEAT-008, the live `analyze()` round-trip stays gated by the
  wac_compose / wasmtime-45 limitation, so the octagon algebra is
  falsified natively (`crates/scry-octagon` +
  `crates/scry-host-tests/tests/octagon.rs`).

### Falsifiable kill-criterion

Two, both mechanical and CI-gated:
1. **Octagon soundness:** closure preserves the concretization γ, `join`
   over-approximates the union, `meet` is exactly the intersection, and
   `add-bound` encodes the intended difference constraint — checked
   against an independently-recomputed γ over dense concrete sweeps in
   `crates/scry-octagon` and `crates/scry-host-tests/tests/octagon.rs`.
   If any op drops a concrete point, the build goes red.
2. **Interval soundness:** `proofs/rocq/Soundness.v` builds with no
   admits and no axioms (`bazel test //proofs/rocq:soundness_test`). If
   any γ-soundness theorem fails to close, the proof build goes red.

## [0.8.0] — 2026-05-29

### Added

- **Taint / noninterference domain (FEAT-009, AC-007 — Wanilla-class).**
  A two-point security-label lattice `low ⊑ high` lifted pointwise over
  values and the control-context, giving a sound *termination-insensitive
  noninterference* analysis that composes with (does not replace) the
  interval and region domains.
  - **`scry-taint` crate.** A new pure, zero-dependency crate holding the
    label-lattice algebra (`bottom`/`top`/`leq`/`join`/`meet`). Like
    `scry-provenance`, it compiles to both `wasm32-wasip2` (where
    `wasm-lattice`'s WIT `label-*` exports delegate to it, so the shipped
    lattice code is exactly the falsified code) and natively (where the
    host harness checks the lattice laws).
  - **`wasm-lattice` label domain.** The `pulseengine:wasm-lattice/domain`
    interface gains `label` + `label-bottom`/`label-top`/`label-leq`/
    `label-join`/`label-meet`, dogfooded across the WIT boundary (DD-008)
    like the interval/region ops.
  - **Analyzer taint pass.** Opt-in via `analysis-config.taint-policy`
    (declared High `high-params` sources / Low `low-results` sinks). A
    dedicated shadow-taint walk propagates labels through the operand
    stack and locals and — unlike the interval pass, which scrubs on
    control flow — interprets structured `if`/`else`/`block`/`end` to
    raise a control-context label, capturing the *implicit* flows that
    distinguish noninterference from mere explicit-flow taint. A
    noninterference finding is emitted when a declared Low result carries
    the High label at exit, surfaced on the new additive
    `analysis-result.taint-findings` field (and an additive
    `taint-findings` block in the v1 invariant contract). Any unmodelled
    operator (`loop`, `br*`, value-typed blocks, `call*`, memory/global
    ops) conservatively raises the taint state to High — sound: it can
    only add taint, never miss a flow.
- AADL (`SecurityLabel` / `TaintPolicy` / `TaintFindings` data + ports),
  rivet FEAT-009 flipped to `draft` with the narrow v0.8 scope, and the
  capability ladder updated (`docs/roadmap.md`,
  `docs/taint-noninterference-v1.md`).

### Known limitations (deferred to a later FEAT-009 slice)

- Tainted store/load tracking through linear memory (memory as a sink),
  multi-principal / lattice-of-sets labels, value-sensitive
  declassification, unstructured-control implicit flows (`loop` taint
  fixpoint, `br_table` post-dominator analysis), and the Wanilla
  shared-benchmark differential corpus (AC#2).
- As with FEAT-008, the live `analyze()` round-trip stays gated by the
  wac_compose / wasmtime-45 root-import limitation, so the lattice and
  finding shapes are falsified natively (`crates/scry-taint` +
  `crates/scry-host-tests/tests/taint.rs` + `tests/contract.rs`), not via
  a live component call.

### Falsifiable kill-criterion

- The security-label lattice obeys its algebraic laws AND forward
  propagation never moves *down* the lattice (`join` is an upper bound;
  `high` is absorbing) — so a Low result is provably independent of every
  High source and "absence of a finding implies noninterference" is
  sound. Checked exhaustively over the (height-1) lattice in
  `crates/scry-taint` (12 tests) and `crates/scry-host-tests/tests/taint.rs`
  (6 tests); the `taint-finding` contract shape is pinned in
  `tests/contract.rs`. If any law fails, the build goes red.

## [0.7.0] — 2026-05-29

Headline: **the meld→scry typed boundary**. scry can now decode the
`component-provenance` custom section meld emits into a fused module and
*project* every analyzed fused-module function index back to the
component + function it was lowered from. This is the provenance-first
slice of [[FEAT-002]] (Component-Model AI), realizing the option-(b)
decision locked in [[DD-002]]: meld owns Core Wasm fusion correctness,
scry owns Component-Model semantics, and the custom section is the typed
contract between them.

### Added

- **`crates/scry-provenance`** — a pure, zero-dependency crate ([[FEAT-002]],
  [[DD-002]]) defining the `component-provenance` section's binary format
  (`SCPV` v1: magic + version + little-endian function-origin entries),
  a strict `decode`, an `encode`, and the `project()` lookup. The *same
  source* compiles into the `wasm32-wasip2` scry-analyzer component
  (`#![no_std]` + `alloc`) and natively into the host harness, so the
  contract is mechanically falsifiable on the cargo path. Carries inline
  round-trip / strict-rejection / projection unit tests.
- **Analyzer provenance pre-pass + projection** (`crates/scry-analyzer`).
  The pre-pass decodes a `component-provenance` custom section via
  `scry_provenance::decode` (a malformed section is a `Warning` + `none`,
  never a partial parse); after the analysis phases, every analyzed fused
  function is projected to its component origin via
  `scry_provenance::project` and surfaced as a per-function diagnostic.
- **WIT + contract additions** (additive, backward-compatible).
  `analysis-result` gains `provenance: option<component-provenance>`
  (records `component-provenance` / `component-origin`); the v1 JSON
  contract (`contracts/scry-invariants-v1.schema.json`) gains an optional
  `provenance` object — a v0.6 document with no `provenance` key still
  validates.
- **`docs/component-provenance-v1.md`** (`DOC-COMPONENT-PROVENANCE-V1`) —
  the section's binary format, the meld⇄scry data flow (mermaid), and how
  scry consumes it. `docs/invariant-schema-v1.md` extended with the
  provenance field mapping.
- **Native provenance test** (`crates/scry-host-tests/tests/provenance.rs`)
  — exercises the boundary crate end-to-end, including round-tripping the
  payload through a *real Wasm custom section* parsed back with the exact
  `wasmparser` API the analyzer uses. The contract test gains a
  `provenance_is_optional_and_tight` case. CI grows
  `cargo clippy/test --package scry-provenance`.

### Known limitations / deferred

- **The meld-side section emitter is a separate cross-repo concern**
  (the producer half), mirroring the [[FEAT-008]] / meld#192 pattern.
  v0.7.0 ships scry's half: the format, the strict decoder, and the
  projection primitive.
- **Handle-state analysis is a later FEAT-002 slice.** The resource
  handle lattice (fresh/owned/borrowed/dropped) + use-after-drop
  detection (AC#1), host-call may-reach effect sets (AC#3), and WIT
  refinement-predicate discharge (AC#4) are deferred.
- **Projection validated against constructed origin tables**, not a live
  `analyze()` call — the abstract-side host harness stays skipped on the
  `wac_compose` root-import / wasmtime-45 limitation. The decode/project
  mapping is well-defined and tested; live end-to-end projection lights
  up when that limitation lifts.
- `Verus Formal Proofs` CI job still informational.

### Falsifiable kill-criterion for v0.7.0

This release is wrong if a function-origin table that meld could
legitimately emit fails to survive `decode(encode(x)) == x` lossless
round-trip, or if `project()` ever mis-attributes a fused-module
function index to the wrong component origin — or invents an origin for
an unmapped index. The `crates/scry-provenance` unit tests and
`crates/scry-host-tests/tests/provenance.rs` are the live falsifiers:
they assert lossless round-trip (including through a real Wasm custom
section), exact attribution, `None` for unmapped indices, and strict
rejection of every malformed payload shape (bad magic, unknown version,
truncation, trailing garbage).

## [0.6.0] — 2026-05-28

Headline: **the analyzer→optimizer contract**. scry's invariant
output is now a stable, versioned JSON-schema contract that loom (or
any consumer) can validate against without coupling to scry's WIT
types. Five releases of *proving* things — intervals, regions, call
graphs, summaries — become a machine-consumable artifact another
tool can act on ([[FEAT-008]], satisfies [[REQ-004]]).

### Added

- **Versioned invariant JSON-schema contract** ([[FEAT-008]], #19).
  `contracts/scry-invariants-v1.schema.json` — JSON Schema draft
  2020-12, `$id https://pulseengine.eu/scry-invariants/v1`,
  `additionalProperties: false` throughout, faithful to the WIT
  `analysis-result`. This is the URL the `invariant-bundle.schema`
  field has carried since v0.1; v0.6.0 formally defines it.
- **`docs/invariant-schema-v1.md`** (`DOC-INVARIANT-SCHEMA-V1`) —
  the field-by-field WIT→JSON mapping, a mermaid scry→loom data-flow
  diagram, a worked `fixture-01-constant-fold` example, and the
  rationale tying each invariant kind to the loom transform it
  unlocks:
  - **singleton interval** (`lo == hi`) on an instruction result →
    loom can **constant-fold** to `i32.const lo`.
  - **in-region load** (region-pointer offset proven within
    `memory.size`) → loom can **elide the bounds check**.
  - **singleton call-edge target set** → loom can **devirtualize**
    `call_indirect` to a direct `call`.
- **Native contract test** (`crates/scry-host-tests/tests/contract.rs`)
  — builds a representative `analysis-result` value, serializes it
  via `serde_json`, validates against the schema with `jsonschema`,
  and asserts 7 malformed instances are rejected. Runs in CI's Test
  job (pure native serde+jsonschema; independent of the skipped
  component-loading path).

### Known limitations / deferred

- **Loom-side consumption is a separate cross-repo issue** (filed
  against `pulseengine/loom`, the FEAT-002/meld#192 pattern). v0.6.0
  is scry's half of the contract: publish + validate the schema.
  loom ingesting it to drive transforms + Z3 translation-validation
  is loom's half.
- **Contract validated against a hand-built `analysis-result`**, not
  a live `analyze()` call — the abstract-side host harness stays
  skipped on the `wac_compose` root-import / wasmtime-45 limitation.
  The serialization mapping is well-defined and tested; live
  end-to-end serialization lights up when that limitation lifts.
- `Verus Formal Proofs` CI job still informational.

### Falsifiable kill-criterion for v0.6.0

This release is wrong if a representative `analysis-result` value —
one the analyzer could legitimately emit — serializes to JSON that
*fails* validation against `contracts/scry-invariants-v1.schema.json`,
or if a structurally-malformed bundle *passes* it. The
`crates/scry-host-tests/tests/contract.rs` suite is the live
falsifier: it asserts both directions (valid bundle accepted, 7
malformed bundles rejected).

## [0.5.0] — 2026-05-28

Headline: **interprocedural precision**. scry no longer throws away
information at function-call boundaries. Per-function abstract
summaries, computed bottom-up over the sound call graph from
FEAT-006, let a call return a precise interval instead of `top`
([[FEAT-007]], [[AC-010]] Stiévenart & De Roover SCAM 2020). The
demonstrable win: `main()` calling `add_one(41)` now infers
`{42, 42}` where v0.4.0 yielded `top`.

### Added

- **Compositional summary-based interprocedural analysis**
  ([[FEAT-007]], #17). Two-phase: phase 1 computes a per-function
  summary in reverse-topological order over the call-graph SCC
  condensation (an iterative `#![no_std]`-safe Tarjan — callees
  before callers); phase 2 is the existing per-function fixpoint,
  but each call site applies the callee's summary instead of
  pushing `top`. For small (≤64 op) non-recursive direct callees
  with concrete arguments, scry re-evaluates the callee with the
  actual argument intervals (context-sensitive precision). New
  `function-summary` record + `function-summaries` field on
  `analysis-result` in the WIT; `FunctionSummary` data type +
  `summaries_out` port in the AADL model. New fixture
  `fixture-05-interproc.wat` (precise `add_one(41) = {42,42}` plus
  a recursive function whose summary is soundly `top`).
  - Soundness: `summary_f(args)` over-approximates
    `{ f(c) : c ∈ γ(args) }` because it is the intraprocedural
    fixpoint (sound per [[FEAT-001]] AC#1) run with params bound to
    `args`, with widening at recursion frontiers guaranteeing a
    sound post-fixpoint. Applying it at a call site is sound because
    the call-site arguments are themselves sound abstractions.
    Reduces to interval-domain soundness + the sound call graph.
  - Termination: functions in a non-trivial call-graph SCC use the
    context-insensitive `top`-summary and are never re-evaluated;
    re-eval is bounded by `REEVAL_MAX_DEPTH=8` and
    `REEVAL_MAX_OPS=64` backstops. Provably terminating regardless
    of SCC-detection correctness — worst case falls back to `top`.

### Known limitations / deferred

- **Context-insensitive for recursive / large / indirect callees.**
  Functions in an SCC, beyond the 64-op threshold, or reached only
  through `call_indirect` use the sound `top`-summary. Full
  polyvariant context-sensitivity and re-eval through
  `call_indirect` are future work.
- **No cross-component summaries.** Summaries are computed within a
  single fused module; cross-component summary reuse pairs with the
  meld `component-provenance` story ([[DD-002]], meld#192) and is
  deferred.
- **The ≥50k-instruction / ≥60%-precise benchmark milestone** (the
  [[AC-010]] corpus target) is not yet measured — needs a benchmark
  harness over real fused PulseEngine modules.
- Abstract-side host-harness assertion still skipped (wac-compose /
  wasmtime-45 limitation, unchanged); concrete oracle runs.
- `Verus Formal Proofs` CI job still informational.

### Falsifiable kill-criterion for v0.5.0

This release is wrong if, for any function `f` and concrete inputs
`c`, scry's computed summary excludes the value `f(c)` actually
produces — i.e. if an interprocedural result *under*-approximates.
The `scry-host-tests` concrete oracle on `fixture-05` runs
`main()` under wasmtime, observes `42`, and asserts `42` is within
scry's interprocedurally-inferred `{42,42}` — exact match, so both
soundness and the precision claim are checked in one shot.

## [0.4.0] — 2026-05-28

Headline: **sound call graphs**. `call_indirect` — the dominant
source of unsoundness across Wasm static analyzers ([[MF-003]], 83%
of real Wasm uses it) — is now resolved soundly. scry intersects
the operand-stack index interval with the function-table bounds and
resolves the exact target set, dispatching through the same interval
domain whose soundness FEAT-001 AC#1 established ([[FEAT-006]],
[[AC-008]] Paccamiccio et al. 2024).

### Added

- **Sound `call_indirect` resolution** ([[FEAT-006]], #15). The
  analyzer parses the table + active element segments in a pre-pass,
  then on `call_indirect` clamps the top-of-stack index interval to
  `[0, table_len)` and resolves the target set from the element
  segments. A **constant index resolves to exactly one target**
  (precise); an unconstrained index resolves to the whole table
  (sound over-approximation, `Warning`-tagged). Both are tagged
  `sound` — scry never produces the unsound *under*-approximation
  that plagues other Wasm analyzers per [[MF-003]]. Direct `call`
  also records a (trivially sound) single-target edge. `analysis-result`
  gains a `call-graph: list<call-edge>` field; new `soundness-tag`
  enum and `call-edge` record in the WIT. `CallIndirect` no longer
  emits `UnsoundnessFallback`.
  - Soundness argument: for any concrete execution reaching a
    `call_indirect` with concrete index `k`, `k ∈ [lo,hi]` (the
    interval is sound per [[FEAT-001]] AC#1), so the resolved target
    set `{ table[j] : j ∈ [lo,hi] ∩ [0,table_len) }` includes
    `table[k]`. Soundness reduces to interval-domain soundness.
  - New fixture `fixture-04-call-indirect.wat`: a 3-entry funcref
    table with a constant-index call (precise `{1}`) and an
    unconstrained-param call (whole-table `{0,1,2}`).
- **`CallEdge` / `CallGraph` in the AADL model** (`spar/scry.aadl`)
  + a `callgraph_out` port wired through the analyzer process.

### Known limitations / deferred

- **No interprocedural value propagation.** FEAT-006 resolves the
  call *graph*, not call *effects*: after a call, params are popped
  and `top` is pushed per result (sound, pessimistic). Interprocedural
  fixpoint via compositional summaries is [[FEAT-007]] (v0.5).
- **Passive/declared element segments and non-constant active
  offsets** resolve to whole-table over-approximation (sound,
  imprecise). Constant active-offset segments are precise.
- Abstract-side host-harness assertion still skipped (the v0.3
  wac-compose/wasmtime-45 limitation, unchanged); the concrete-side
  oracle continues to run.
- `Verus Formal Proofs` CI job still informational (upstream
  `rules_verus` sysroot issue).

### Falsifiable kill-criterion for v0.4.0

This release is wrong if there exists a concrete execution that
reaches a `call_indirect` and dispatches to a function NOT in the
target set scry resolved for that call site — i.e. if scry ever
*under*-approximates a call graph. The soundness reduction above
makes this checkable: any counterexample would also be a
counterexample to the interval domain's soundness on the index
operand, which `scry-host-tests` exercises.

## [0.3.0] — 2026-05-28

Headline: **memory bounds + a mechanical soundness harness**. The
analyzer gains a region-based linear-memory abstract domain so the
canonical base+offset memory-access pattern is proven in-bounds
instead of falling back to `top` ([[FEAT-005]]). A new host
wasmtime test crate runs the composed component and checks the
analyzer's invariants against concrete execution, turning the
v0.2.0 kill-criterion from hand-checkable into CI-gated
([[FEAT-001]] AC#3).

### Added

- **Region-based linear-memory domain** ([[FEAT-005]], #12).
  `wasm-lattice` gains a `region` abstract type — `(region-id: u32,
  offset: interval)` — plus `region-create` / `region-offset` /
  `region-leq` / `region-join` / `region-meet` / `region-widen`
  transfer ops, all exported over the `pulseengine:wasm-lattice/domain`
  WIT interface ([[DD-004]]). The analyzer recognises the canonical
  `i32.const base; i32.const off; i32.add; i32.load` pattern,
  tags the result as a region-pointer, and emits a precise `Info`
  ("bounds-check elision safe") or `Warning` ("cannot prove
  in-region") diagnostic in place of v0.2's blanket
  `UnsoundnessFallback`. Region transfer ops dispatch through the
  imported lattice interface, preserving the [[DD-008]] dogfood.
  New fixture `fixture-03-region-bounds.wat` pins the canonical
  case (`[104, 108)` access in the 64 KB default region). Loaded
  *values* still widen to `top` at v0.3 — per-region content
  tracking is v0.4+ territory ([[FEAT-007]]).
- **Host wasmtime test harness** ([[FEAT-001]] AC#3, #13). New
  native cargo crate `crates/scry-host-tests/` (wasmtime 45 +
  wasmtime-wasi + wat). Three integration tests run each WAT
  fixture as a core Wasm module under wasmtime, capture the
  concrete return value, and assert it lies within the abstract
  interval scry reports — the v0.2.0 kill-criterion made
  mechanical. `compute() = 84 ∈ {84,84}` (exact), `doit(x) = x+5 ∈
  Top` across five inputs. Promotes the CI `Clippy` and `Test`
  jobs from no-op placeholders to real `cargo clippy` + `cargo
  test` runs; the `Test` job bazel-builds the composed component
  first, then runs the harness.

### Changed

- **CI `Clippy` and `Test` jobs are now real** (#13). No longer
  placeholders — `Clippy` runs `cargo clippy --package
  scry-host-tests -- -D warnings`; `Test` runs `bazel build //:scry`
  then `cargo test --package scry-host-tests`.

### Known limitations / deferred

- **Abstract-side soundness assertion is currently skipped in the
  harness.** `rules_wasm_component`'s `wac_compose` passes
  `--import-dependencies` to wac, which encodes each dependent
  package as a root-level component import on the composed
  `scry.wasm`. wasmtime 45 rejects root-level component imports, so
  the harness's in-process call to `analyzer.analyze` falls back to
  a `::notice::` skip. The **concrete-side oracle still runs** (each
  fixture executed under wasmtime, return value captured). The full
  abstract-vs-concrete assertion lights up automatically when any of:
  (a) wasmtime supports root-level component imports, (b)
  `wac_compose` stops passing `--import-dependencies`, or (c) scry
  adds a host re-compose step. Tracked as a follow-up.
- **Loaded memory values still widen to `top`** ([[FEAT-005]]
  precision deferred to [[FEAT-007]]); single default region per
  module; `memory.grow`/`memory.size` still hit the v0.2 fallback.
- **No sound `call_indirect`** — [[FEAT-006]], the v0.4.0 milestone.
- **`Verus Formal Proofs` CI job** still informational (upstream
  `rules_verus` sysroot issue, unchanged from v0.2).

### Falsifiable kill-criterion for v0.3.0

This release is wrong if `cargo test --package scry-host-tests`
passes while the analyzer reports an abstract interval that
*excludes* the concrete value a fixture actually computes. The
harness's concrete-side oracle is the live falsifier:
`fixture_01_constant_fold` and `fixture_02_param_plus_const` both
run the fixture under wasmtime and assert containment. (When the
abstract-side skip is lifted per the limitation above, the
falsifier becomes total rather than concrete-only.)

## [0.2.1] — 2026-05-27

Headline: **compliance bundle ships, finally**. Patch release fixing
the v0.2.0 release-tail gap that left the `compliance-evidence.tar.gz`
asset off the GitHub Release. No analyzer or toolchain changes.

### Fixed

- **`release.yml` compliance step** (#11, closes #10): bumped the
  `pulseengine/rivet/.github/actions/compliance@v0.6.0` invocation's
  `rivet-version` input from `v0.3.0` to `v0.13.1`. v0.3.0 was too
  old to parse scry's `schemas/research-ext.yaml` local schema
  extension, so the action's internal `rivet validate` failed with
  37 errors and no archive was emitted on the v0.2.0 release run.
  Also dropped the unrecognised `single-page` and
  `include-data-formats` inputs that produced warnings on the same
  call (they don't exist in the action's v0.6.0 schema; valid
  inputs are `report-label`, `homepage`, `other-versions`, `theme`,
  `offline`, `rivet-version`, `output`, `archive`, `archive-name`,
  `project-dir`).

### Falsifiable kill-criterion for v0.2.1

This release is wrong if the GitHub Release for v0.2.1 does NOT
include an asset matching `scry-0.2.1-compliance-evidence.tar.gz`
with a valid cosign signature. v0.2.0's release shipped 13 assets
without the bundle; v0.2.1 must ship 16 (the bundle + its `.sig` +
its `.pem`).

## [0.2.0] — 2026-05-27

Headline: **real analysis ships**. The v0.1.0 scaffold's hardcoded
invariant bundle is replaced by a working interval-domain
abstract-interpretation fixpoint over Wasm Core Model arithmetic,
running through the `pulseengine:wasm-lattice/domain` cross-component
import on every transfer ([[FEAT-001]] acceptance criterion #1). The
PulseEngine proof toolchain (`rules_verus` + `rules_rocq_rust`) is
wired into the Bazel build, with one provable theorem per family on
the lattice algebra ([[FEAT-012]]). Releases now ship rivet
compliance evidence as a cosign-signed asset, and PRs touching the
artifact graph get a sticky `rivet-delta` comment so reviewers can
see what changed without diffing YAML.

### Added

- **Real interval-domain fixpoint** ([[FEAT-001]] AC#1, #8).
  `crates/scry-analyzer/src/lib.rs` rewritten: parses the input Wasm
  module with `wasmparser`, walks straight-line arithmetic in each
  function, maintains an abstract operand stack and per-local
  abstract state, and emits a `ProgramPoint` snapshot per
  instruction. Every interval transfer (`I32Const`, `I32Add`,
  `I32Sub`, `I32Mul`, `LocalGet`/`Set`/`Tee`) dispatches through
  the imported `pulseengine:wasm-lattice/domain` interface,
  preserving the [[DD-008]] dogfood on every call. `module_sha256`
  populated via `sha2`. Unsupported ops (control flow, memory,
  calls, refs, GC, SIMD) emit `DiagnosticSeverity::UnsoundnessFallback`
  and widen the locals to `domain::top()` — soundness over
  precision ([[REQ-001]]). Test fixtures under
  `crates/scry-analyzer/test-fixtures/` document expected
  invariants for two arithmetic-only Wasm modules.
- **Verus + Rocq proof toolchain wired into Bazel** ([[FEAT-012]],
  #7). `MODULE.bazel` pulls `rules_verus@a49f72ef` and
  `rules_rocq_rust@090b875c` (synth-canonical pins) plus
  `rules_nixpkgs_core@0.13.0` for the hermetic Rocq build. New
  `proofs/verus/` contains a Verus theorem on `join` commutativity;
  new `proofs/rocq/` contains a Rocq theorem on interval-lattice
  ⊑-reflexivity discharged by `lia`. New CI jobs
  `Rocq Formal Proofs` (PASS) and `Verus Formal Proofs`
  (informational at v0.2 — upstream `rules_verus` sysroot bug
  documented inline, doesn't block the merge). Mechanized
  soundness proof of the interval domain against WasmCert-Coq
  remains deferred to [[FEAT-010]] in v0.9.
- **Rivet compliance evidence in releases** (v0.2-prep, #6).
  `release.yml` invokes the canonical
  `pulseengine/rivet/.github/actions/compliance@v0.6.0` composite
  action (same one sigil and spar use) and tarballs the result as
  `scry-<version>-compliance-evidence.tar.gz`. v0.2.0 is the first
  release to ship the bundle; cosign signs it alongside the other
  release assets.
- **`rivet-delta` PR check** (v0.2-prep, #6). Sticky comment on every
  PR touching `artifacts/`, `schemas/`, `spar/`, or `rivet.yaml`.
  Reports `rivet validate` head-vs-base, the artifact-count delta,
  full `rivet diff`, and `spar parse` result. Pattern adapted from
  rivet's own `rivet-delta.yml`. Informational only.
- **`README.md`** updated post-v0.1.0 (#4).

### Changed

- **`actions/checkout` upgraded from `@v4` to `@v6`** across both
  workflows (v0.2-prep, #6). Removes the Node.js 20 deprecation
  warning for the one action where Node 24 support exists today.
  Other Node 20 actions (`actions/cache`, `Swatinem/rust-cache`,
  `sigstore/cosign-installer`, `bazelbuild/setup-bazelisk`,
  `actions/attest-build-provenance`, `peter-evans/*`) have no
  Node 24-compatible release yet; warnings remain for those until
  upstream ships.
- **CI workflow gains a Nix install step on the Bazel-build job**
  (#7). Adding `register_toolchains("@rocq_toolchains//:all")` in
  `MODULE.bazel` forces nix-build resolution for every `bazel
  build`, not just the proofs targets. The install step makes the
  main composed-component build green again. Matches the synth
  `ci.yml` pattern.
- **`crates/scry-analyzer/Cargo.toml`** adds `wasmparser = "0.247"`
  and `sha2 = "0.10"` workspace deps (#8). Both with
  `default-features = false` for `#![no_std]`.

### Known limitations / deferred

- **No host wasmtime test harness** — [[FEAT-001]] acceptance
  criterion #3, still pending. The Wasm fixtures in
  `crates/scry-analyzer/test-fixtures/` document expected invariants
  but aren't yet executed against the analyzer in CI. Promoting
  the placeholder `Clippy` + `Test` CI jobs to real `cargo` runs
  lands with this.
- **No region-based memory model** — [[FEAT-005]]; the analyzer
  emits `UnsoundnessFallback` on the first memory op.
- **No control flow** — `if`/`loop`/`br_if` etc. emit
  `UnsoundnessFallback` and widen the function's locals to
  `domain::top()`. Widening for loops is a v0.3+ concern.
- **No sound `call_indirect`** — [[FEAT-006]] in v0.3.
- **`Verus Formal Proofs` CI job fails** — informational only;
  `librustc_driver-*.so` shared-library issue inside
  `rules_verus@a49f72ef`. The same pin works for synth; reason
  is under investigation. The Rocq proof path is fully green and
  is the more important leg for the FEAT-010 mechanized soundness
  roadmap.

### Falsifiable kill-criterion for v0.2.0

This release is wrong if, on any well-formed Wasm Core Model module
whose execution scry-analyzer's `analyze` interprets to completion
without emitting an `UnsoundnessFallback` diagnostic, the returned
`invariant_bundle.points` contains *any* `ProgramPoint` whose
abstract local state excludes a value that the program actually
computes for some concrete input. The forthcoming host wasmtime
harness ([[FEAT-001]] AC#3) will be the mechanical falsifier — until
it lands, the fixtures in `crates/scry-analyzer/test-fixtures/`
document the expected invariants for two arithmetic-only modules
and a careful reader can hand-check them against the JSON
`analysis-result` the analyzer emits.

## [0.1.0] — 2026-05-27

Headline: **scaffolding ships**. The full PulseEngine Wasm-component toolchain
proven end-to-end on scry's own build (the dogfood gate for `DD-008`).
No real abstract-interpretation logic yet — that lands with `FEAT-001`
acceptance criterion #1 in the v0.2 cycle. v0.1.0 ships the *structure*
so every subsequent change has typed traceability, CI gates, signed
release evidence, and a green Bazel build to anchor on.

### Architecture and source code

- **AADL architecture model** at `spar/scry.aadl` modelling the two-process
  composition (`LatticeProcess` + `AnalyzerProcess`). Validates with
  `spar parse`.
- **WIT interface definitions** per crate:
  - `crates/wasm-lattice/wit/wasm-lattice.wit` exports the
    `pulseengine:wasm-lattice/domain` interface (interval domain ops +
    i32 transfer functions).
  - `crates/scry-analyzer/wit/scry.wit` imports the lattice domain and
    exports the `pulseengine:scry/analyzer` interface.
- **Two wasm32-wasip2 component crates** under `crates/`:
  - `wasm-lattice` — interval-domain library, `#![no_std]`. Implements
    bottom / top / leq / join / meet / widen / constant-i32 / i32-add /
    i32-sub / i32-mul.
  - `scry-analyzer` — analyzer scaffold that exercises the
    cross-component lattice import end-to-end via
    `domain::constant_i32(42)` as the dogfood gate.
- **Bazel build via `rules_wasm_component` v1.0.0** (pinned to commit
  `d2347fbf` via `git_override` since v1.0.0 is not yet in BCR).
  `bazel build //:scry` produces a valid wasm32-wasip2 Component Model
  artifact at `bazel-bin/scry.wasm` via `wac_compose` and
  `composition.wac`.
- **Cargo workspace** with `[workspace.package]` single source of truth
  for `version` / `edition` / `license` / `repository` / `authors`.
  Both member crates inherit via `.workspace = true`. Rust edition
  pinned to **2024**.

### Rivet artifact graph

- **64 typed artifacts** across 11 types (academic-reference,
  technology-evaluation, market-finding, requirement, feature,
  design-decision, safety-goal, safety-strategy, safety-solution,
  safety-context, safety-justification). `rivet validate` PASS, 0
  warnings.
- **Local schema extension** at `schemas/research-ext.yaml` adding
  three cross-artifact link types: `references-paper`,
  `addresses-finding`, `evaluates-tech`.
- **Three new design decisions** added during the v0.1 cycle:
  - DD-008: scry ships as a Wasm Component Model component (dogfood).
  - DD-009: build with Bazel + `rules_wasm_component`.
  - DD-010: hand-write WIT to match the AADL model for v0.1;
    integrate spar-codegen in a later version.
- **DD-002 closed** in favour of option (b) — meld emits a minimal
  `component-provenance` custom section; scry analyzes original
  component sources upstream of meld. Cross-repo dependency tracked at
  `pulseengine/meld#192`.
- **FEAT-012 added** as a v0.2 proposed feature: wire `rules_verus` +
  `rules_rocq_rust` into the Bazel build with one provable theorem per
  family (lattice algebra).

### CI and release infrastructure

- **`.github/workflows/ci.yml`** — full CI pipeline: Format (cargo
  fmt), Clippy (placeholder until host crate lands), Test (placeholder
  until wasmtime harness lands), Rivet artifact validation, AADL
  model (`spar parse`), WIT round-trip (`wasm-tools component wit`),
  Bazel build (`//:scry`) + `wasm-tools validate` on the composed
  component, cargo-deny (licenses / advisories / bans).
- **`.github/workflows/release.yml`** — tag-triggered (`v*`) release
  workflow building the composed `bazel-bin/scry.wasm`, generating a
  CycloneDX SBOM, SHA256SUMS, cosign keyless-OIDC signatures
  (per-asset + bundle), SLSA v1 provenance via
  `actions/attest-build-provenance`, and a GitHub Release with notes
  auto-extracted from this CHANGELOG.
- **`deny.toml`** copied verbatim from the witness/rivet family
  pattern; allows the eight PulseEngine-standard licenses.

### Documentation

- **`README.md`** — falcon/witness aspirational style with a 10-row
  release plan and per-version `tags: [v0.x]` on proposed FEAT artifacts.
- **`docs/intro-to-abstract-interpretation.md`** — friendly explainer
  for readers who've never met "abstract interpretation". `safe_index`
  worked example, what "sound" means, widening for loops, where scry
  fits. ~10 min, no math. Tagged `id: DOC-INTRO-AI`.
- **`docs/architecture.md`** — how scry v0.1 works end-to-end with
  mermaid diagrams: two-component decomposition, 8-layer Bazel build
  pipeline, WAC composition contract, 8-step PulseEngine loop
  status, runtime cross-component probe, Bazel target dep graph.
  Tagged `id: DOC-ARCH-V01`.
- **`docs/roadmap.md`** — per-version plan with research links and
  composition narrative (witness-style).
- **`CHANGELOG.md`** — this file; release.yml extracts version
  sections as GitHub Release notes via awk.

### Known limitations and deferred work

- **No real interval-domain fixpoint** — the scaffold returns a
  hardcoded invariant bundle plus a single diagnostic confirming
  cross-component import wired correctly. Real `wasmparser`-driven
  analysis lands with FEAT-001 acceptance criterion #1 in v0.2.
- **No host wasmtime test harness** — FEAT-001 acceptance criterion
  #3, deferred to v0.2 (drops the Clippy + Test CI placeholders).
- **No Verus + Rocq proof targets** — FEAT-012, deferred to v0.2.
  Toolchain wiring (rules_verus + rules_rocq_rust + nix_repo for
  Rocq) lands first; mechanized soundness for the interval domain is
  v0.9 (FEAT-010).
- **No witness MC/DC integration** — scaffold has too few branches
  to measure usefully; integrate once the real fixpoint lands.
- **No spar-codegen Bazel rule** — per DD-010 the WIT is hand-derived
  from the AADL for v0.1; a CI check that they stay in sync is a
  follow-on task.

### Falsifiable kill-criterion for v0.1.0

This release is wrong if, on any well-formed Wasm Core Model module
the scry-analyzer component is invoked on, the diagnostic in the
returned `analysis-result` reports the lattice cross-component import
as `BROKEN` rather than `alive`. The v0.1 dogfood claim is that the
WIT cross-component import works end-to-end through wac_compose; the
`constant_i32(42)` probe in `crates/scry-analyzer/src/lib.rs` is the
falsifier.

## Earlier

See git history for pre-v0.1 work (initial scope-out + DD-002 closure
in PR #2).

[Unreleased]: https://github.com/pulseengine/scry/compare/v1.1.0...HEAD
[1.1.0]: https://github.com/pulseengine/scry/releases/tag/v1.1.0
[1.0.1]: https://github.com/pulseengine/scry/releases/tag/v1.0.1
[1.0.0]: https://github.com/pulseengine/scry/releases/tag/v1.0.0
[0.9.0]: https://github.com/pulseengine/scry/releases/tag/v0.9.0
[0.8.0]: https://github.com/pulseengine/scry/releases/tag/v0.8.0
[0.7.0]: https://github.com/pulseengine/scry/releases/tag/v0.7.0
[0.6.0]: https://github.com/pulseengine/scry/releases/tag/v0.6.0
[0.5.0]: https://github.com/pulseengine/scry/releases/tag/v0.5.0
[0.4.0]: https://github.com/pulseengine/scry/releases/tag/v0.4.0
[0.3.0]: https://github.com/pulseengine/scry/releases/tag/v0.3.0
[0.2.1]: https://github.com/pulseengine/scry/releases/tag/v0.2.1
[0.2.0]: https://github.com/pulseengine/scry/releases/tag/v0.2.0
[0.1.0]: https://github.com/pulseengine/scry/releases/tag/v0.1.0
