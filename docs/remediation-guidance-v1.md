---
id: DOC-REMEDIATION-GUIDANCE-V1
type: spec
status: draft
title: scry remediation guidance — advisory schema + AI-agent fix-verify loop (v1)
tags: [remediation, guidance, ai-agent, schema, oracle-gate, v3.1]
references: [FEAT-059, FEAT-060, REQ-018, TE-011]
---

# scry remediation guidance (v1)

FEAT-059/060 ([[REQ-018]]). scry turns its **sound** findings into ranked,
actionable guidance for improving the analyzed code — consumable by a human
(the scry-viz *Guidance* panel) and by an AI agent (the structured
`AnalysisResult.advisories` records described here). This document is the stable
contract an agent codes against.

## 1. The honesty rule (why the class matters)

scry is a *sound* analyzer: a soundness claim never overclaims, and neither does
its guidance. Every advisory is tagged with an **actionability class** that says
exactly how much the finding licenses you to conclude:

| Class | Meaning | What to do | Do NOT |
|---|---|---|---|
| `DefiniteFault` | scry **proved** a bug (use-after-drop, double-drop, a divisor provably `{0}`) | fix it | — |
| `UnprovenObligation` | scry **could not prove** a trap cannot fire (a POTENTIAL-TRAP) | prove it, add a guard, or tighten a bound | do **not** treat it as a confirmed bug |
| `PrecisionGap` | scry **lost precision** (degraded to ⊤ at an unmodelled op) | restructure for analyzability, or accept the limit | do not treat it as a defect in the code |
| `LeverageableFact` | scry **proved** a property (PROVEN-SAFE, a bound) | rely on it / elide a redundant defensive check | do not remove a check whose safety scry did *not* prove |

An agent that promotes an `UnprovenObligation` to "bug" has made the same error
as a tool that claims unsound soundness. The class is the guard against that.

## 2. Advisory record schema

Each entry of `AnalysisResult.advisories` (Rust `Advisory`; sorted by
`(class rank, func_index, pc)`, faults first):

| Field | Type | Meaning |
|---|---|---|
| `func_index` | u32 | absolute function index (`0`-based; imports occupy the low indices) |
| `pc` | u32 | operator index of the site (`0` for a function-level advisory) |
| `class` | enum | `DefiniteFault \| UnprovenObligation \| PrecisionGap \| LeverageableFact` |
| `code` | string | machine-stable category, e.g. `use-after-drop`, `double-drop`, `div-by-zero`, `signed-overflow`, `out-of-bounds`, `proven-safe`, `unsupported-op`, `unmodeled-branch`, `unmodeled-memory-address`, `unmodeled-control-flow`, `unbounded-stack` |
| `detail` | string | human rationale — what was found and why it matters |
| `suggested_action` | string | the concrete change to make |
| `verification` | string | the **oracle** — what re-running scry should show once the fix lands |

Resolve `func_index` to a name via `AnalysisResult.function_meta` (FEAT-027).
Library-only: not in the WIT mirror or the frozen v1 invariant-JSON contract
(so this schema may evolve independently of that frozen contract).

## 3. The fix-verify loop (for AI agents)

The `verification` field makes each advisory a **checkable task**, closing the
`oracle-gate-a-change` loop against a *sound* checker:

```
1. read advisories, highest class first (DefiniteFault → UnprovenObligation → …)
2. for a chosen advisory A:
     a. apply A.suggested_action as a code edit
     b. re-run scry on the edited module
     c. check A.verification:
          - DefiniteFault    → the handle_findings / trap entry is GONE
          - UnprovenObligation → the trap_check flips PotentialTrap → ProvenSafe
                                  (or, with FEAT-055, its counterexample no longer reproduces)
          - PrecisionGap     → the gap at (func_index, pc) is absent / unreached
     d. if the oracle is satisfied, the fix is verified by a sound analysis;
        otherwise revert and try another action.
```

Because the oracle is a sound over-approximation, a satisfied `UnprovenObligation`
oracle (`ProvenSafe`) is a *proof* the trap cannot fire — not just "tests pass".
That is the value of gating an agent's edits on scry rather than on tests alone.

Structured-primary (TE-011): agents MUST consume the `advisories` records, not
the rendered HTML — the panel is a human projection of the same data.

## 4. Scope / honesty notes

- Guidance is **finding-driven**: no findings → no fault/obligation advisories
  (a clean module is quiet, not falsely reassured — absence of an advisory is
  not a proof of correctness, only that scry surfaced nothing at that site).
- `LeverageableFact` advisories are informational; scry cannot see whether a
  redundant runtime check actually exists, so "may be elided" means "the
  property it would check is proven", not "a check is present here".
- `suggested_action` is advice, not an auto-applied patch; the agent authors the
  edit and the `verification` oracle judges it.
