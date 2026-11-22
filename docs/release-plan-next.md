# scry: the next releases, measured against the North Star

Status: work in progress, drafted 2026-11-19, progress recorded 2026-11-22.
The items are rivet artifacts in `artifacts/roadmap-next-bets.yaml` (FEAT-104
to FEAT-110). The owner approved the release split below on 2026-11-19;
nothing in it is tagged yet.

The yardstick is the North Star in pulseengine.eu (`data/north-star.toml`):
a safety-critical team takes a WebAssembly component from architecture model
to signed code on a microcontroller, with evidence an assessor can re-check,
using open tools only. scry's part of that is sound static analysis: evidence
about a module that an assessor can re-check without running it.

## How this plan was made

1. A planner pass read the North Star, the rivet state (v3.4.0: 22 items, 11
   not ready), the open issues, the v3.3.0 notes and the repository, and
   proposed five bets.
2. A checker pass in a fresh context read only the North Star and the draft,
   and gave each bet a confirm, refute or cannot-verify verdict on three
   questions: does it move an indicator as `north-star.toml` words it, can its
   acceptance fail, is anything overclaimed.
3. The bets were revised from those findings, and the dependencies the
   checker marked unverified were checked where that was cheap (below).

The checker's main findings, and what changed:

| Finding | Revision |
|---|---|
| Only the proof-check bet moves an indicator as written (O3 counts repositories). | Each item now says which indicator it moves, or that none moves. |
| The "proved on the shipped Rust" title overclaims a trusted translator against a hand model. | FEAT-106 is retitled, states its trust base and its fallback, and is counted on the O3 guard (ledger shrinks), not on O3. |
| A budgeted analysis can "return a result" with every function a gap. | FEAT-107 has a floor that can fail (50% of functions finish), a deterministic budget unit, and is labelled a baseline, not evidence. |
| The WCET target could be lowered after the fact; the wrong-hint control was in the kill criterion. | FEAT-108 freezes its target after a fixed classification rule; the wrong-hint control is an acceptance criterion. |
| The kiln half of the last bet does not match "signed WASI components under kiln" and is blocked. | Split: FEAT-109 (release integrity, no indicator) and FEAT-110 (O5, unscheduled until kiln#480 closes). |
| "Re-checked on every CI run" is false today, and the minimal fix is the sentence. | FEAT-104 corrects the claim in v3.4.0, guarded by claim-check. |
| Backlog arithmetic counted conditional closures. | Recomputed below with unconditional closures only. |

## The trust base, as found

- All 20 Rocq files import only Stdlib and prove properties of hand-written
  models that mirror the Rust (`proofs/rocq/WrapAdd.v` says so).
  rocq-of-rust is enabled in `MODULE.bazel` but no proof uses it.
- There is no WasmCert-Coq import; the concrete semantics is modelled directly.
- `Admitted`, `Axiom` and `admit.` occur 0 times by grep, but nothing runs
  `Print Assumptions`, so "axiom-free" is a text search, not a kernel audit.
- Section hypotheses (`Reachable.v`, `StackBound.v`) are premises that no
  ledger lists.
- Verus builds from an unmerged rules_verus branch (`MODULE.bazel`).
- The proof workflows are path-filtered, `continue-on-error: true`, and not
  in `.github/required-checks.txt` (#207).

## The items, in order

| ID | Release (proposed) | Objective and indicator | Acceptance that can fail | Kill criterion | Cross-repo |
|---|---|---|---|---|---|
| FEAT-104 | v3.4.0 | O3 summary; no indicator moves | claim-check fails while the dossier or dashboard says "CI-gated" and the jobs are not | none needed (S) | none |
| FEAT-105 | v3.5.0 | O3: scry 0 → 1 proof-carrying repo with required check + kernel audit + ledger | required in the live ruleset; reports on every PR; audit completeness (audited = declared theorems); planted `Axiom` and broken proof go red; ledger growth fails CI | median job > 30 min or > 1 flake in 20 runs: release-blocking on main instead, and scry does not count toward O3 | rules_rocq_rust; rules_verus fork branch unmerged |
| FEAT-108 | v3.5.0 | O1: WCET bound (one of three numbers), Cortex-M, gale fixture, functions bounded from 3/31 to a target frozen after classification | synth accepts at least the target and rejects none of scry's hints; a planted too-small hint is rejected in CI | fewer than 3 of the 13 loops are counted loops | gale fixture; synth `--wcet-hints` (present in 0.90.0) |
| FEAT-109 | v3.5.0 | no indicator moves (O2 counts consumer repos) | every primary asset in the signed manifest; dry run with one asset dropped fails, per asset kind | none needed (S) | none |
| FEAT-107 | v3.5.0 | no indicator moves; baseline on released components | native file-path run on relay's falcon-flight; budget gap is a named kind; at least 50% of functions finish; results re-derived in CI | under 50%: fails, REQ-007 gets no link; under 2% proven-safe: next release is precision work | relay release asset (component, 49,402 B); meld fuse; v3.4.0 native binaries |
| FEAT-106 | v3.6.0 | O3 guard: ledger shrinks by 2 (or 0 on fallback); O3 count unchanged | mutants in i32_add/sub/mul turn the job red with no .v change; all five #210 transfers tested | 10-day time-box on i32_add fails: take the conformance fallback | rules_rocq_rust's rocq-of-rust path (unused so far) |
| FEAT-110 | unscheduled | O5: 0 → 1 of N tools under kiln, wasmtime differential (N for the owner) | signed component runs under kiln with no `*_GAP`; byte-identical results; a result-changing input to one side fails | kiln#480 open | kiln#480 (open since 2026-08-08) |

Ordering: FEAT-104 rides with v3.4.0. FEAT-105 first in v3.5.0, because the
ledger it creates is what FEAT-106 is measured against. FEAT-107 waits for the
v3.4.0 native binaries. FEAT-108 refines FEAT-081, which is already scoped to
v3.5.0.

## The release split (approved by the owner, 2026-11-19)

- **v3.4.0 ships near its current scope plus FEAT-104.** Six of its 11
  not-ready items (FEAT-098 to FEAT-103) have commits on main; their
  acceptance criteria still have to be re-run before they are promoted.
  FEAT-057, FEAT-064/REQ-020 and FEAT-094/REQ-021 have measured blockers
  and would hold the first native binaries (FEAT-099) back. Moving them out
  of v3.4.0 is part of the decision.
- **v3.5.0 takes FEAT-105, FEAT-107, FEAT-108 (with FEAT-081) and FEAT-109**,
  next to the existing FEAT-069 and FEAT-095.
- **v3.6.0 takes FEAT-106**, which depends on FEAT-105's ledger.
- **FEAT-110 stays unscheduled** until kiln#480 closes.

## Progress (2026-11-22)

- FEAT-104 merged in #246.
- FEAT-109 merged in #247: the signed manifest covers the MC/DC evidence.
- FEAT-105, three of its slices merged:
  - #248: "Rocq Formal Proofs" is a required check, listed in
    `.github/required-checks.txt` and in ruleset 16891064.
  - #249: kernel axiom audit, 101 theorems declared and 101 audited, 0
    allow-listed axioms.
  - #250: trust-escape ledger, 36 rows.
  - In CI, a planted `Axiom`, a planted `Hypothesis` and a false lemma each turn
    the job red.
  - `tools/check-required-checks.py` in live-ruleset mode reports the
    file and the ruleset agree on 13 contexts (exit 0, 2026-11-22).
  - Still open: a docs-only pull request whose run shows the Rocq context
    completed (this change is that pull request), and the O3 release asset
    `north-star-input.O3.json`.
- FEAT-107 and FEAT-108 not started.

## Backlog effect

Unconditional closures if the scheduled items land: #207, #210, #212, #135,
#144, #237. The needs-decision queue would go from 29 to 23; with FEAT-110
(#118) 22. #214 closes only if its remaining wording items ride along. The
plan files no new issue; new work is these rivet items.

## Not verified

- Whether scry's native binary accepts a component directly, or needs
  `meld fuse` first.
- Proof job wall-clock and flake rate: FEAT-105's kill criterion times 20
  runs. As of 2026-11-22 there are 17 runs of the job (it was added in #248).
  - 13 succeeded, with a median of 123 s (100 to 144 s), against the 30-minute
    limit.
  - 4 were cancelled by `cancel-in-progress` within seconds of a newer push to
    the same branch.
  - 0 failed, and 0 flaked on toolchain fetch. 7 more completed runs reach the
    criterion's 20.
- Whether rules_rocq_rust's rocq-of-rust path translates scry-interval.
- That FEAT-098 to FEAT-103 meet their acceptance criteria.
- Whether toolchain repositories count for O2, and the O5 denominator.
