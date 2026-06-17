# fixture-16-stack-measured

FEAT-021 **slice-2b** — the LIVE kill-criterion.

A 2-deep call chain (`entry` frame 32 → `deep` frame 16) that **self-measures**
its runtime shadow-stack peak: each function records `min(min_sp, sp)` (via
`select`) into a second global after lowering the `__stack_pointer` (global 0).
Both `sp` and `min_sp` are exported, so the host harness reads the true peak
(`sp_init − min_sp`) after a concrete wasmtime run and cross-checks it against
scry's reported `max-stack-bytes` (analyzed via the composed component).

- **Analyzer (abstract):** `entry(32) + deep(16) = 48` → `max-stack-bytes =
  bytes(48)`. The min-recording `global.get $sp` reads are not followed by
  `i32.sub`, so frame detection is unperturbed; two mutable i32 globals still
  resolve SP to global 0.
- **Runtime (concrete):** the deepest point is inside `deep` at `sp_init − 48`,
  so `min_sp = sp_init − 48` and the measured peak = 48 bytes.
- **Kill-criterion:** `reported (48) ≥ measured (48)` — sound (here exact). A
  fixture whose measured peak exceeded the reported bound would falsify the
  soundness claim.

Native oracle: `feat021_measured_chain_bound` (analyzer side → 48). Host oracle:
`fixture_16_runtime_peak_within_bound` (component bound ≥ wasmtime-measured peak).
