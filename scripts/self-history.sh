#!/usr/bin/env bash
# FEAT-073 — the self-adjudication harness, in OBSERVATION MODE.
#
# scry already analyzes its own compiled module at a single commit (FEAT-025).
# This extends that instrument across TIME: build `scry_mcdc.wasm` at each of
# the last N commits, then compare consecutive pairs BY STABLE OBLIGATION
# IDENTITY (FEAT-064/072) and publish the distribution.
#
# ─────────────────────────────────────────────────────────────────────────────
# WHY THIS EXISTS, AND WHY IT DOES NOT GATE
#
# scry#122 lists nine wrong-verdict paths in the (withdrawn) adjudicator and
# nothing yet says which of them fire on real code. scry's own history is a
# better adversary than any fixture we would write for ourselves: it contains
# real deletions, real same-kind insertions and real renames, at a scale of
# thousands of obligations. The measurement ORDERS the rework instead of
# guessing at it.
#
# This script therefore reports and never judges:
#   * it EXITS 0 unconditionally — observation mode is a property of the code,
#     not a convention a later edit can quietly drop;
#   * every artifact it writes names scry#122, so no reader — human or agent —
#     mistakes a count here for a verdict;
#   * it claims nothing beyond "alias-free", which holds because aliasing needs
#     a same-kind sibling to inherit an ordinal from (ObligationId.v:
#     survivor_inherits_deleted_identity) and a singleton ordinal domain has none.
#
# It graduates to a gate only when REQ-021 has closed. See DD-022.
#
# FEAT-065 (REQ-021 rework): each pair now ALSO carries the ADJUDICATED verdict
# distribution (delta-*.verify.json, aggregated below) from `verify_against` —
# conservative by construction. The harness itself still exits 0: adjudication
# per pair exists; the harness gate is REQ-021's closure, not this script.
# ─────────────────────────────────────────────────────────────────────────────
#
# Usage:  scripts/self-history.sh [N_COMMITS] [OUT_DIR]
# Default: last 6 commits of the current branch, into ./self-history/
set -uo pipefail   # deliberately NOT -e: a failed build of one old commit must
                   # not abort the sweep, it must be reported and skipped.

N="${1:-6}"
OUT="${2:-self-history}"
REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT" || exit 0

STAGE="$OUT/modules"
mkdir -p "$STAGE"

echo "== FEAT-073 self-adjudication harness (OBSERVATION MODE) =="
echo "   No verdict is produced. Adjudication is scry#122 / REQ-021."
echo

# ── 1. Build the delta tool ONCE, from the working tree ─────────────────────
# The tool must be the CURRENT producer: identity is a hash over a key tuple
# whose derivation is not a cross-version contract, so old modules are analyzed
# with today's analyzer — never old-analyzer-vs-new-analyzer.
echo "== build scry-viz (current working tree) =="
cargo build --release -p scry-sai-viz || {
  echo "!! could not build scry-viz — nothing to measure with"; exit 0; }
VIZ="$REPO_ROOT/target/release/scry-viz"

# ── 2. Build scry_mcdc.wasm at each commit ──────────────────────────────────
# Portable to bash 3.2 (macOS default): no `mapfile`, no negative subscripts.
COMMITS=()
while IFS= read -r line; do COMMITS+=("$line"); done < <(git log --format=%H -n "$N")
echo
echo "== building scry_mcdc.wasm at ${#COMMITS[@]} commit(s) =="
BUILT=()
for sha in "${COMMITS[@]}"; do
  short="${sha:0:8}"
  dest="$STAGE/$short.wasm"
  if [[ -f "$dest" ]]; then
    echo "   $short — cached"; BUILT+=("$short"); continue
  fi
  wt="$(mktemp -d)/wt"
  if ! git worktree add --detach -q "$wt" "$sha" 2>/dev/null; then
    echo "   $short — SKIP (cannot check out)"; continue
  fi
  if (cd "$wt/crates/scry-mcdc" && cargo build --release --target wasm32-wasip1 -q 2>/dev/null) \
     && cp "$wt/crates/scry-mcdc/target/wasm32-wasip1/release/scry_mcdc.wasm" "$dest" 2>/dev/null; then
    echo "   $short — ok ($(wc -c <"$dest" | tr -d ' ') bytes)"
    BUILT+=("$short")
  else
    # An old commit that no longer builds is a fact about the history, not a
    # failure of the harness. Report it and carry on.
    echo "   $short — SKIP (build failed at this commit)"
  fi
  git worktree remove --force "$wt" 2>/dev/null
done

if (( ${#BUILT[@]} < 2 )); then
  echo
  echo "!! fewer than two modules built — nothing to compare."
  echo "   Reporting this rather than pretending agreement. Exit 0 (observation mode)."
  exit 0
fi

# ── 3. Compare consecutive pairs (oldest → newest) ──────────────────────────
# git log is newest-first; reverse so a delta reads forward in time.
REV=()
for (( i=${#BUILT[@]}-1 ; i>=0 ; i-- )); do REV+=("${BUILT[i]}"); done

echo
echo "== deltas over ${#REV[@]} module(s), oldest → newest =="
SUMMARY="$OUT/summary.json"
{
  echo "{"
  echo "  \"harness\": \"FEAT-073 self-adjudication (observation mode)\","
  echo "  \"adjudicated\": false,"
  echo "  \"adjudication_issue\": \"scry#122\","
  echo "  \"note\": \"Delta counts describe what CHANGED between two analyses and claim no verdict (positional-ordinal matching was refuted in review). Each pair additionally carries a FEAT-065 'verify' block: the conservative adjudicator's verdict distribution, in which discharged is a certainty claim (unreachable on stripped modules) and uncertain is the honest degradation.\","
  echo "  \"pairs\": ["
} > "$SUMMARY"

first=1
for (( i=0 ; i<${#REV[@]}-1 ; i++ )); do
  a="${REV[i]}"; b="${REV[i+1]}"
  page="$OUT/delta-$a-$b.html"
  if ! "$VIZ" delta "$STAGE/$a.wasm" "$STAGE/$b.wasm" \
        -o "$page" --title "$a → $b" 2>&1 | sed 's/^/   /'; then
    echo "   $a → $b — SKIP (delta failed)"
    continue
  fi
  dj="${page%.html}.delta.json"
  vj="${page%.html}.verify.json"
  if [[ -s "$dj" ]]; then
    [[ $first -eq 0 ]] && echo "," >> "$SUMMARY"
    first=0
    { printf '    {"from":"%s","to":"%s","delta":' "$a" "$b"
      cat "$dj"
      if [[ -s "$vj" ]]; then
        printf ',"verify":'
        cat "$vj"
      fi
      printf '}'; } >> "$SUMMARY"
  fi
done

{ echo; echo "  ]"; echo "}"; } >> "$SUMMARY"

# ── 4. SELF-COMPARISON CONTROL ──────────────────────────────────────────────
# The harness's own vacuity check, and the same invariant REQ-021 will be held
# to. If comparing a module with ITSELF reports changes, every number above is
# meaningless and the run says so — loudly, and still exits 0.
echo
echo "== self-comparison control (newest module vs itself) =="
newest="${REV[$(( ${#REV[@]} - 1 ))]}"
ctl="$OUT/control-self.html"
"$VIZ" delta "$STAGE/$newest.wasm" "$STAGE/$newest.wasm" -o "$ctl" \
  --title "control: $newest vs itself" 2>&1 | sed 's/^/   /'
ctlj="${ctl%.html}.delta.json"
if [[ -s "$ctlj" ]] && grep -q '"changed":0' "$ctlj" \
   && grep -q '"only_before":0' "$ctlj" && grep -q '"only_after":0' "$ctlj"; then
  echo "   CONTROL OK — a module compared with itself shows no change."
else
  echo "   !! CONTROL FAILED — identity is not stable under a no-op."
  echo "      Every count in this run is suspect. (Still exit 0: observation mode.)"
fi
# FEAT-065: the ADJUDICATED control — a self-comparison must contain no
# discharged, no regressed, no moved, no removal and nothing introduced
# (REQ-021's adversarial bar, run against the real module, not a fixture).
ctlv="${ctl%.html}.verify.json"
if [[ -s "$ctlv" ]] && grep -q '"discharged":0' "$ctlv" \
   && grep -q '"regressed":0' "$ctlv" && grep -q '"moved":0' "$ctlv" \
   && grep -q '"removed-with-code":0' "$ctlv" && grep -q '"introduced":0' "$ctlv" \
   && grep -q '"gate_pass":true' "$ctlv"; then
  echo "   VERIFY CONTROL OK — self-comparison adjudicates to still-open only."
else
  echo "   !! VERIFY CONTROL FAILED — the adjudicator claims progress on a no-op."
  echo "      Every verdict in this run is suspect. (Still exit 0: observation mode.)"
fi

echo
echo "== wrote $SUMMARY and $(ls "$OUT"/delta-*.html 2>/dev/null | wc -l | tr -d ' ') delta page(s) =="
echo "   Reminder: observation only. No verdict. scry#122 / REQ-021."
exit 0
