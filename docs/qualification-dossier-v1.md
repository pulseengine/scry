---
id: DOC-QUAL-DOSSIER-V1
type: spec
status: draft
title: scry tool-qualification dossier (DO-330 TQL-5 / ISO 26262-8 §11)
tags: [dossier, qualification, do-330, iso-26262, tql-5, tcl, capstone, v3.0]
references: [FEAT-050, G-005, FEAT-040, FEAT-045, FEAT-046, FEAT-048, REQ-002, MF-006, CA-011]
---

# scry tool-qualification dossier (v1, DO-330 TQL-5 / ISO 26262-8 §11)

The G-005 capstone ([[FEAT-050]], [[CA-011]]). This dossier assembles the
assessor-facing qualification package for **scry** as a *verification* tool
(a tool that can fail to detect an error in the item, but cannot itself insert
one) and maps every objective of the two target qualification frameworks —
**DO-330 Tool Qualification Level 5 (TQL-5)** and **ISO 26262-8:2018 §11 Tool
Confidence Level (TCL)** — to a concrete scry artifact: a mechanized proof, a
runnable test, a CI gate, or an explicit scope/limitation statement.

> **Honesty stance (assessor, read this first).** Every "mechanized" claim below
> names an admit-free, axiom-free Rocq or Verus file that `bazel test`
> re-checks in CI. Evidence that is *test-* or *γ-sweep-validated but not
> machine-proven* is labelled as such and never presented as mechanized. The
> scope/limitation statement (§5) enumerates exactly what scry does NOT soundly
> analyze. This dossier deliberately under-claims: see the "not yet mechanized"
> column and the honesty notes in §6.

## 1. Tool operational requirements (what scry is qualified to do)

scry is a **sound static analyzer for Core WebAssembly**. Its qualified
outputs, each an over-approximation of the concrete semantics, are:

| Output | Meaning | Feature |
|---|---|---|
| Interval / region invariants | per-program-point value ranges & memory regions | FEAT-005/007 |
| Octagon relational constraints | `x − y ≤ c`, `x + y ≤ c` between locals | FEAT-016/041 |
| Known-bits / congruence facts | alignment / stride of locals | FEAT-037 |
| Pentagon guards | proven `index < length` strict relations | FEAT-044 |
| Worst-case shadow-stack bound | sound upper bound (or `Unbounded`) | FEAT-021/043 |
| Reachable-from-exports set | sound superset of live functions | FEAT-022/039 |
| **Gap report** | every site scry was conservative (⊤) — the scope oracle | FEAT-040 |
| **Trap verdicts** | div-by-zero / signed-overflow / OOB-memory: PROVEN-SAFE vs POTENTIAL-TRAP | FEAT-045/046 |
| **Float intervals** | sound f32/f64 abstraction incl. NaN/±∞ | FEAT-047 |
| **Handle-lifetime faults** | Component-Model use-after-drop / double-drop | FEAT-049 |

**Tool operational requirement (soundness).** For every output, the reported
abstract value over-approximates every concrete execution; a PROVEN-SAFE /
`Bytes(n)` / no-fault verdict is issued only when the property provably holds on
all runs. This is the single property qualification credits, and the one the
falsification statements in each release's CHANGELOG entry commit to.

## 2. Why scry qualifies more cheaply than a test-only QSK

The differentiating evidence (stronger than the test-based Qualification Support
Kits competitors ship, per [[CA-011]]): scry's soundness-critical transfers are
**mechanically proven** admit-free, its decisions are **MC/DC-covered** on the
shipped Wasm, and its headline bounds carry **live kill-criteria** (runtime
cross-checks in CI). An assessor credits proofs + coverage + executable
falsification, not a test report alone.

## 3. DO-330 TQL-5 objective → artifact map

TQL-5 (the level for a verification tool that cannot insert an error) requires,
per DO-330 Table T-0/T-1 (tool operational requirements & verification):

| DO-330 objective | scry artifact | Kind |
|---|---|---|
| T-0(1) Tool Operational Requirements defined | §1 above; `artifacts/` rivet REQ-001..017 | scope |
| T-0(2) TOR correct & complete | `rivet validate` + `rivet coverage` (CI gate) | gate |
| T-1(1) Tool operational use verified vs TOR | `crates/scry-host-tests` (host runs the composed `scry.wasm`) + `SCRY_COMPONENT_PATH` release-wasm oracle | test |
| T-1(3) Robustness of tool operation | γ-sweep tests (interval/octagon/bits/pentagon/float/handle), adversarial clean-room per soundness feature | test |
| T-1(4) TOR verification complete | `bazel test //...` + `cargo test` + MC/DC gate (all CI) | gate |
| Soundness of the analysis (credit basis) | admit-free Rocq (§4), Verus join proof, MC/DC truth tables | **proof** |
| Configuration management | git + version-pinned deps (`Cargo.lock`, Bazel `MODULE.bazel`), `sigil`-signed release artifacts | gate |
| Tool operational environment defined | `MODULE.bazel` (Bazel+Nix pins: Rocq 9.0.1, wasmparser 0.252), `rust-toolchain` | scope |

## 4. Mechanized-soundness inventory (the credit basis)

Admit-free, axiom-free, re-checked by `bazel test //proofs/rocq:...` and
`//proofs/verus:...` on every CI run:

| Proof file | Property | Feature |
|---|---|---|
| `Soundness.v` | interval γ-soundness: ⊥/const/⊑/join/meet/**add** over ℤ | FEAT-010 |
| `Lattice.v` | interval order reflexive+transitive | FEAT-012 |
| `Region.v` | region-memory domain γ-soundness | FEAT-011 |
| `CallGraph.v`, `Reachability.v`, `Reachable.v` | call-graph + reachable-from-exports superset soundness | FEAT-011/022 |
| `WriteSetHavoc.v`, `LoopFixpoint.v`, `GuardRefine.v` | loop/branch abstraction soundness | FEAT-016 |
| `OctagonProject.v`, `OctagonStrongClose.v` | octagon→interval rounding + Miné strong-closure soundness | FEAT-016 |
| `StackBound.v` | worst-case shadow-stack bound ≥ true peak | FEAT-021 |
| `BitsCongruence.v` | congruence over wrapping ints | FEAT-037 |
| `Pentagon.v` | pentagon join/order/close soundness | FEAT-044 |
| `Float.v` | float-interval **lattice** soundness (join/order/meet) | FEAT-047 |
| **`WrapAdd.v`** | **`i32.add` sound vs the OFFICIAL two's-complement wrapping semantics, incl. the wrap case** | FEAT-048 |
| `Handle.v` | affine handle-state lattice + drop/use transition soundness | FEAT-049 |
| `proofs/verus/join_proofs.rs` | interval join commutative + bottom-identity **up to γ** (semantic) | FEAT-012 |

**Executable evidence** (runnable, version-pinned; not deductive proof):

- **MC/DC** — `witness` reconstructs the truth table of every soundness-critical
  decision on the shipped `scry_mcdc.wasm`; the `mcdc` CI job is a live gate
  (floor tracked). The transfer functions carry `#[inline(never)]` so each stays
  an MC/DC-visible DWARF cluster (DD-012).
- **γ-sweeps** — each pure domain crate brute-forces its lattice laws + transfer
  soundness against a concrete-semantics oracle over a value grid (the float
  sweep spans f32+f64 incl. ±0/subnormals/±∞/NaN; the interval/octagon/bits
  sweeps span the small-width grid).
- **Live kill-criterion** — the shadow-stack bound is cross-checked at runtime in
  wasmtime (host asserts reported ≥ measured peak, FEAT-021 slice-2).

## 5. Scope / limitation statement (fed by the FEAT-040 gap report)

The machine-readable [[FEAT-040]] gap report (`AnalysisResult.gaps`) enumerates,
per analyzed module, **every** site where scry was conservative (degraded to ⊤):
unsupported ops, `br_table`, non-i32 memory addresses, and havocked control-flow
regions. An assessor reads that report as the *concrete, per-artifact* scope
boundary. The **general** limitations qualification must account for:

- **Interval interpreter** degrades to ⊤ (and the gap report records it) on:
  unsupported operators, `drop`/`select`/`nop` (not modelled in the interval
  transfer), `br_table`, and non-i32-shaped memory addresses.
- **Trap detection** (FEAT-045/046) is loop-conservative: a divisor/address
  widened by the loop fixpoint yields POTENTIAL-TRAP even when a tighter analysis
  could prove safety (sound; imprecise). Narrow/float memory widths and
  imported/growable memory ⇒ POTENTIAL-TRAP.
- **Float domain** (FEAT-047) is surfaced by a straight-line pass
  (`compute_float_facts`), sound but stopping at the first control-flow op; its
  rounding transfers are **γ-sweep-validated, not Rocq-mechanized** (only the
  lattice is mechanized — see §6).
- **Handle-state** (FEAT-049) detects use-after-drop / double-drop on
  single-basic-block straight-line paths via the canonical-ABI `[resource-drop]`
  / `[method]` call convention; handles round-tripped through globals/linear
  memory, or across control flow, are conservatively not flagged (no false
  report; real bugs on those paths are missed — a completeness gap, not a
  soundness one).
- **`call_indirect` stack weighting** (FEAT-043) is `Unknown` for non-zero /
  growable / runtime-mutated / host-writable tables (sound).

## 6. Honesty notes (deltas from an aspirational reading)

Recorded so the dossier never over-credits:

1. **REQ-002 ("proven vs the OFFICIAL Wasm semantics")** — now **literally true
   for `i32.add`** via `WrapAdd.v` (FEAT-048), which proves scry's shipped
   transfer sound against two's-complement wraparound mod 2³² (the semantics the
   spec mandates and WasmCert-Coq mechanizes). It is modelled directly; scry does
   **not** yet import the WasmCert-Coq development, and the other integer/float
   transfers are **not** yet proven against the official semantics (γ-sweep /
   `Soundness.v`-over-ℤ only). Do not read REQ-002 as discharged tool-wide.
2. **Float rounding** — `Float.v` mechanizes the *lattice*; the round-to-nearest
   arithmetic transfers are γ-sweep-validated only (Flocq mechanization is named
   future work, as with the octagon DBM and known-bits value transfers).
3. **The Verus join proof** was, at one point, a false structural-equality claim
   masked by a broken toolchain; it is now the true **semantic (γ) equality**
   statement and the Verus CI job verifies it. The history is recorded, not
   hidden.
4. **MC/DC** credits decision coverage of the shipped analyzer, not a soundness
   proof; it is complementary evidence, not a substitute for §4.

## 7. ISO 26262-8:2018 §11 — Tool Confidence Level

Per §11.4.5, TCL is derived from Tool Impact (TI) × Tool error Detection (TD):

- **TI2** — a scry error (a missed unsoundness → a wrongly-credited property)
  *could* lead to a violation of a safety requirement of the item ⇒ TI2.
- **TD1** — there is **high confidence of detecting** a scry malfunction: the
  soundness-critical transfers are mechanically proven (§4), MC/DC-covered, and
  each release ships a **falsification statement** with a concrete falsifier a
  reviewer can run; the adversarial clean-room process has, on this project,
  repeatedly caught real unsoundness before release (documented per feature).
- ⇒ **TCL1** (TI2 × TD1). At TCL1 no further tool qualification is required by
  §11; the §4/§5 evidence is nonetheless provided as the confidence argument.

| ISO 26262-8 §11 objective | scry artifact | Kind |
|---|---|---|
| §11.4.4.2 Tool use case / TI | §1, §7 | scope |
| §11.4.5 TD argument | §2, §4 (proofs), MC/DC gate, per-release falsification | proof + gate |
| §11.4.6 Qualification (if > TCL1) | not required at TCL1; §4/§5 provided as confidence evidence | — |
| §11.4.8 Increased confidence from use | version-pinned CI history; per-feature clean-room verdicts | gate |

## 8. Assessor entry points

- Soundness proofs: `proofs/rocq/*.v`, `proofs/verus/*.rs` — `bazel test
  //proofs/rocq/... //proofs/verus/...`.
- Coverage: the `mcdc` CI job (witness truth tables).
- Scope per artifact: `scry analyze <module>` → `AnalysisResult.gaps`.
- Traceability: `rivet coverage` over `artifacts/` (STK→SYS→SR + dev
  REQ/FEAT/DD, and the parallel ASPICE V-model spine, FEAT-033).
- Release falsification statements: `CHANGELOG.md` per version.
