#!/usr/bin/env bash
# scry-mcdc — build the harness to wasm32-wasip1 and run the witness MC/DC
# pipeline over the real analyzer core (FEAT-014 / DD-012).
#
# Usage:  WITNESS_BIN=/path/to/witness ./build-and-measure.sh
# Default WITNESS_BIN: /Users/r/git/pulseengine/witness/target/release/witness
#
# Emits, under ./evidence/:
#   scry-mcdc.instrumented.wasm        instrumented module
#   *.witness.json                     instrument manifest (decisions)
#   run.json                           per-branch counters from --invoke-all
#   report.json                        MC/DC report (witness-mcdc/v3 schema)
# and prints the human truth table. Read report.json (not stdout) for the
# authoritative gap rows.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

W="${WITNESS_BIN:-/Users/r/git/pulseengine/witness/target/release/witness}"
if [ ! -x "$W" ]; then
    echo "witness binary not found/executable at: $W" >&2
    echo "build it: (cd /Users/r/git/pulseengine/witness && cargo build --release -p witness)" >&2
    exit 127
fi

rustup target add wasm32-wasip1 >/dev/null 2>&1 || true

echo "== build harness (wasm32-wasip1, debug=2) =="
cargo build --release --target wasm32-wasip1
WASM="target/wasm32-wasip1/release/scry_mcdc.wasm"
test -f "$WASM" || { echo "missing $WASM" >&2; exit 1; }

mkdir -p evidence
echo "== witness instrument =="
"$W" instrument "$WASM" -o evidence/scry-mcdc.instrumented.wasm
echo "== witness run --invoke-all =="
"$W" run evidence/scry-mcdc.instrumented.wasm --invoke-all -o evidence/run.json
echo "== witness report (human truth table) =="
"$W" report --input evidence/run.json --format mcdc || true
echo "== witness report (mcdc-json -> evidence/report.json) =="
"$W" report --input evidence/run.json --format mcdc-json > evidence/report.json
echo "done. Inspect evidence/report.json gap rows (NOT this stdout)."
