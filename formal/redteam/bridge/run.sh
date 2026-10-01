#!/usr/bin/env bash
# Comparator red-team regression for the bridge layout (formal/redteam/bridge/README.md).
# Runs comparator (scripts/comparator.sh run --allow-sorry --prebuilt --scratch ...) once with the
# real Solution and once per fixture F*.lean used as Solution, and checks exit code + message.
# Usage (from formal/, tools built with scripts/comparator.sh tools):
#   redteam/bridge/run.sh [--tools DIR] [--keep]
# Scratch copies go to $RT_DIR (default: a fresh `mktemp -d`), removed unless --keep.
# Case C0 (trust3.opus B2) replaces landrun by a pass-through wrapper that runs the command
# UNCONFINED (what `landrun --best-effort` does on a kernel without Landlock): the harness's Landlock
# canary must refuse to start comparator.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"   # formal/
RT="$HERE/redteam/bridge"
OUT="${RT_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/eg-comparator-redteam.XXXXXX")}"
TOOLS=()
KEEP=0
while [ $# -gt 0 ]; do
  case "$1" in
    --tools) TOOLS=(--tools "$2"); shift;;
    --keep) KEEP=1;;
    *) echo "unknown option $1" >&2; exit 2;;
  esac
  shift
done
mkdir -p "$OUT"
# C0: a landrun that drops every sandbox flag (created at run time, outside the tree).
printf '#!/bin/sh\nwhile [ "$#" -gt 0 ] && [ "$1" != "--" ]; do shift; done\nshift\nexec "$@"\n' > "$OUT/unconfined-landrun"
chmod +x "$OUT/unconfined-landrun"

# name | solution file | extra environment (VAR=value) | expected exit | expected message (substring)
CASES=(
  "C0_UnconfinedLandrun|$HERE/comparator/Solution.lean|COMPARATOR_LANDRUN=$OUT/unconfined-landrun|2|Landlock canary:"
  "honest|$HERE/comparator/Solution.lean||0|Your solution is okay!"
  "F1_DefinitionChanged|$RT/F1_DefinitionChanged.lean||1|Const does not match between challenge and target 'Erdos184.IsCycleOrEdge'"
  "F2_StatementWeakened|$RT/F2_StatementWeakened.lean||1|Challenge and solution theorem statement do not match: 'Erdos184.erdos_184'"
  "F3_KernelBypass|$RT/F3_KernelBypass.lean||1|Lean default kernel rejects the solution"
  "F4_ExtraAxiom|$RT/F4_ExtraAxiom.lean||1|Illegal axiom detected: 'Erdos184.cheat'"
  "F5_ImportsUpstream|$RT/F5_ImportsUpstream.lean||1|Child exited with"
)

fails=0
for c in "${CASES[@]}"; do
  IFS='|' read -r name sol extra want msg <<<"$c"
  log="$OUT/$name.log"
  # extra = optional VAR=value environment for this case
  env $extra "$HERE/scripts/comparator.sh" run --allow-sorry --prebuilt --scratch "$OUT/$name" --solution "$sol" \
    "${TOOLS[@]}" >"$log" 2>&1
  got=$?
  if [ "$got" = "$want" ] && grep -qF "$msg" "$log"; then
    echo "ok    $name: exit $got, \"$msg\""
  else
    echo "FAIL  $name: exit $got (want $want), message \"$msg\" $(grep -qF "$msg" "$log" && echo found || echo 'NOT found'); log: $log"
    # Diagnostics only (CI cannot read $log after the job): show its non-build lines.
    grep -vE '^[[:space:]]*$|^✔|^⚠|^(warning|Note|Hint):' "$log" | tail -n 40 | sed 's/^/    | /'
    fails=$((fails + 1))
  fi
  [ $KEEP = 1 ] || rm -rf "$OUT/$name"
done
echo "comparator red-team: $fails failure(s)"
[ $fails = 0 ]
