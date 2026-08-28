# scry-sai-mcp

MCP (Model Context Protocol) server exposing the scry sound abstract
interpreter to AI agents (FEAT-066): JSON-RPC 2.0, newline-delimited, over
stdio. Agents cannot run `cargo`; this crate replaces shelling out to a CLI or
scraping a multi-MB JSON dump with two structured tools:

- **`analyze`** — run scry over a Wasm module (`.wasm` or `.wat`, by path) and
  get a compact summary: advisory counts by actionability class and code,
  runtime-trap verdicts (proven-safe vs potential-trap), and precision-gap
  counts. Never HTML, never a full dump.
- **`query`** — filter the advisories (FEAT-067): `class`, `code`,
  `func_index`, `op`, `gap_kind`, ANDed, each optional. Matches carry their
  stable obligation identities (REQ-020) and honesty flags.

`verify` is deliberately absent from the v3.3.0 tool list — the deferral is
enforced structurally, not by documentation: REQ-021 measured that on real
inputs the FEAT-065 adjudicator's `discharged` is 0 and every verdict degrades
to `uncertain`, which must not sit inside an agent's tool loop. It follows
FEAT-065 into v3.4.0.

## Use

```jsonc
// MCP client config (stdio server):
{ "command": "scry-mcp" }
```

Install: `cargo install scry-sai-mcp`.

The JSON-RPC layer is hand-rolled on `serde_json` — no MCP SDK dependency.
