#!/usr/bin/env bash
# scry-mcdc — the CI MC/DC gate (FEAT-014 rollout). Runs the witness pipeline
# over the real analyzer core and FAILS if structural coverage regresses, then
# exports the static-HTML truth-table visualisation.
#
# This is the "live oracle, not a one-shot artifact" step: it runs on every
# change (the .github/workflows/ci.yml `mcdc` job calls it), so a code change
# that silently drops a proved condition turns the build red.
#
# Env:
#   WITNESS_BIN        witness binary           (default: `witness` on PATH)
#   WITNESS_VIZ_BIN    witness-viz binary       (default: `witness-viz` on PATH)
#   MCDC_PROVED_FLOOR  min conditions_proved    (default: 155; v1.6 mac = 164, CI/linux v1.5 = 155)
#   MCDC_FULL_FLOOR    min full-MC/DC decisions (default: 3;   CI/linux v1.5 = 4)
#   MCDC_SITE_DIR      static viz output dir    (default: ./viz-site)
#
# Floors are calibrated to CI (x86_64-linux) — the canonical gate. NOTE:
# conditions_proved is stable across hosts, but decisions_full_mcdc is
# platform-sensitive (DWARF / instrumentation differ; e.g. macOS reports 5,
# linux 4 for the same code), so `proved` is the primary regression gate and
# `full` is floored conservatively (with margin below the CI value).
#
# Reads the authoritative numbers from evidence/report.json (NOT stdout).
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE"

W="${WITNESS_BIN:-witness}"
VIZ="${WITNESS_VIZ_BIN:-witness-viz}"
FLOOR="${MCDC_PROVED_FLOOR:-155}"
FULL_FLOOR="${MCDC_FULL_FLOOR:-3}"
SITE="${MCDC_SITE_DIR:-$HERE/viz-site}"

command -v "$W"   >/dev/null 2>&1 || { echo "witness binary not found: $W" >&2; exit 127; }
command -v "$VIZ" >/dev/null 2>&1 || { echo "witness-viz binary not found: $VIZ" >&2; exit 127; }

rustup target add wasm32-wasip1 >/dev/null 2>&1 || true

echo "== build harness (wasm32-wasip1, debug=2) =="
cargo build --release --target wasm32-wasip1
WASM="target/wasm32-wasip1/release/scry_mcdc.wasm"
test -f "$WASM" || { echo "missing $WASM" >&2; exit 1; }

mkdir -p evidence
echo "== witness instrument / run --invoke-all / report =="
"$W" instrument "$WASM" -o evidence/scry-mcdc.instrumented.wasm
"$W" run evidence/scry-mcdc.instrumented.wasm --invoke-all -o evidence/run.json
"$W" report --input evidence/run.json --format mcdc-json > evidence/report.json

# ── Baseline gate — read overall.* from the report (not stdout) ──────────
PROVED=$(jq -r '.overall.conditions_proved' evidence/report.json)
FULL=$(jq -r '.overall.decisions_full_mcdc' evidence/report.json)
DTOT=$(jq -r '.overall.decisions_total' evidence/report.json)
echo "MC/DC over the real analyzer core: decisions_total=$DTOT conditions_proved=$PROVED decisions_full_mcdc=$FULL"
echo "         floors: conditions_proved>=$FLOOR  decisions_full_mcdc>=$FULL_FLOOR"

fail=0
if [ "$PROVED" -lt "$FLOOR" ]; then
    echo "::error title=MC/DC regression::conditions_proved=$PROVED dropped below floor $FLOOR" >&2
    fail=1
fi
if [ "$FULL" -lt "$FULL_FLOOR" ]; then
    echo "::error title=MC/DC regression::decisions_full_mcdc=$FULL dropped below floor $FULL_FLOOR" >&2
    fail=1
fi
[ "$fail" -eq 0 ] || { echo "MC/DC gate FAILED" >&2; exit 1; }
echo "MC/DC gate PASSED"

# ── Visualisation — static HTML site (CI uploads it / GitHub Pages) ──────
echo "== witness-viz export -> $SITE =="
REPORTS="$(mktemp -d)/verdict-evidence"
mkdir -p "$REPORTS/scry-mcdc"
cp evidence/report.json "$REPORTS/scry-mcdc/report.json"
cp evidence/scry-mcdc.instrumented.wasm.witness.json "$REPORTS/scry-mcdc/manifest.json"
"$VIZ" export --reports-dir "$REPORTS" --out "$SITE" \
    --source-root "$HERE/../.." --site-title "scry · MC/DC (FEAT-014)"
cp "$SITE/summary.json" evidence/viz-summary.json
echo "MC/DC viz site at $SITE ; summary copied to evidence/viz-summary.json"
