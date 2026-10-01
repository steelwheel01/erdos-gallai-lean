#!/usr/bin/env bash
# Elaborate one Lean file under a wall-clock limit (PLAN_FORMALIZATION.md §5 per-sandbox tooling).
#   scripts/check.sh FILE.lean [TIMEOUT_SECONDS=900]
# Prints Lean's messages; exit 0 = no errors (sorry warnings allowed), 1 = errors, 124 = timeout.
# Dependencies of FILE must already be built (`lake build <Module>` for its imports).
set -uo pipefail
cd "$(dirname "$0")/.."
FILE=${1:?usage: scripts/check.sh FILE.lean [TIMEOUT]}
T=${2:-900}
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-$(nproc)}
OUT=$(timeout "$T" lake env lean "$FILE" 2>&1); RC=$?
echo "$OUT"
NS=$(grep -c "declaration uses 'sorry'\|declaration uses \`sorry\`" <<<"$OUT")
NE=$(grep -c ": error" <<<"$OUT")
echo "check.sh: $FILE rc=$RC errors=$NE sorry-warnings=$NS"
if [ $RC -eq 124 ]; then exit 124; fi
if [ $RC -ne 0 ] || [ "$NE" -gt 0 ]; then exit 1; fi
exit 0
