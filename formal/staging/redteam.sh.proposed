#!/usr/bin/env bash
# Red-team the OUT-OF-BAND acceptance checks (trust audits of 2026-09-26).
#
#   formal/redteam/external/redteam.sh [--with-leanchecker] [--keep] [--final FILE] [ATTACK...]
#
#   --final FILE  use FILE as EGCheck/Final.lean of the temporary copy (the in-band target), instead
#                 of the real one; e.g. `--final staging/Final.lean.proposed` checks the expectations
#                 for a proposed Final.lean before it is applied. The real tree is never written.
#
# For each attack it applies a self-contained patch to a TEMPORARY COPY of formal/ (source files
# copied with cp; .lake/packages is a symlink to the real, read-only package store; nothing in the
# real tree is ever written — the build runs under a read-only bind mount of the repo), then runs
# the out-of-band checks this agent owns and reports caught/missed against the expected table.
#
# Out-of-band checks:
#   * scripts/FinalCheck.lean  — importModules-based (no project elaborator runs): provenance,
#     import-clash, strict Expr.equal of the statement, exact axiom set, kernel replay, the
#     EG/EGCheck axiom+attribute policy, and a meta-type scan.  (this agent)
#   * leanchecker --fresh <final module>  — kernel replay of the whole environment (bundled with
#     the toolchain).  Optional (--with-leanchecker): ~20 min, ~10 GB RSS per attack.
# For reference each attack is also run against the IN-BAND check (`lake build` of the real
# EGCheck/Final.lean, whose #guard_msgs/run_cmd the auditors spoofed) and the current lint.
#
# Comparator is NOT run here (its Challenge/Solution layout is the bridge agent's; see
# formal/work/trust/bridge.md). `release.yml`'s comparator job is the third out-of-band check.
#
# Exit code 1 if any attack's out-of-band verdict differs from the expected table below.
#
# Two expectation tables, selected by the Final.lean in use (TRUST.md §8 item 8, trust3.opus R1):
#   * committed-style Final.lean (imports only EGCheck.Bridge; `type_of% @Erdos184.erdos_184`):
#     B1 and C build green in-band and must be caught by FinalCheck;
#   * HARDENED Final.lean (staging/Final.lean.proposed: first line imports the upstream module,
#     statement `type_of% @_root_.Erdos184.erdos_184`): B1 (shadow + neutralised run_cmd) is a type
#     mismatch and C (own Erdos184.erdos_184) an import clash, so both are caught IN-BAND by their
#     own error, and FinalCheck is still run on them against a DEV FINAL (the committed-style
#     theorem without in-band checks) so that its out-of-band coverage of B1/C stays exercised.
set -uo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
FORMAL=$(cd "$HERE/../.." && pwd)                 # the real formal/
REPO=$(cd "$FORMAL/.." && pwd)                    # the repo root (bind-mounted read-only)
PATCHES="$HERE/patches"
export PATH="$HOME/.elan/bin:$PATH"
# Python never imports from the working directory or the script directory (trust2.opus N2/N3):
# every call uses -I; PYTHONSAFEPATH covers any call that might lack it.
export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1

WITH_LC=0; KEEP=0; SELECT=(); FINAL_SRC="$FORMAL/EGCheck/Final.lean"
while [ $# -gt 0 ]; do
  case "$1" in
    --with-leanchecker) WITH_LC=1;;
    --keep) KEEP=1;;
    --final) [ $# -ge 2 ] || { echo "--final needs a file"; exit 2; }
             FINAL_SRC=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
             [ -f "$FINAL_SRC" ] || { echo "no such file: $2"; exit 2; }; shift;;
    -*) echo "unknown flag $1"; exit 2;;
    *) SELECT+=("$1");;
  esac
  shift
done

# Is the in-band target the hardened Final.lean (staging/Final.lean.proposed)? Recognised by its
# two load-bearing features: the upstream module is its FIRST import, and the statement is
# `type_of% @_root_.Erdos184.erdos_184`. Anything else keeps the committed-style expectations.
hardened_final() {
  [ "$(head -n 1 "$1")" = 'import FormalConjectures.ErdosProblems.«184»' ] \
    && grep -q 'type_of% @_root_\.Erdos184\.erdos_184' "$1"
}
if hardened_final "$FINAL_SRC"; then FINAL_KIND=hardened; else FINAL_KIND=committed-style; fi

# The canonical serialisation block must be byte-identical in FinalCheck.lean and Statement.lean.
canon_block() { sed -n '/## BEGIN CANON/,/## END CANON/p' "$1"; }
if ! diff <(canon_block "$FORMAL/scripts/FinalCheck.lean") <(canon_block "$FORMAL/scripts/Statement.lean") >/dev/null; then
  echo "FATAL: the BEGIN CANON..END CANON blocks of FinalCheck.lean and Statement.lean differ"; exit 2
fi

# Statement / closure pins: read from the generated STATEMENT.md (EG-PIN lines), else fall back.
pin_of() { sed -n "s/.*EG-PIN $1 \([0-9a-f]\{64\}\).*/\1/p" "$FORMAL/STATEMENT.md" 2>/dev/null | head -1; }
STMT_SHA=$(pin_of statement-sha256); CLOS_SHA=$(pin_of closure-sha256); LEAN_GITHASH=$(pin_of lean-githash)
[ -n "$STMT_SHA" ]   || STMT_SHA=4cb2cd5697e7916ea244e8b58041fcb2c7fa4338621335eeeb3a1d05452f6734
[ -n "$CLOS_SHA" ]   || CLOS_SHA=39d6e8c358b1482f9af513370d6edfba52da96857fa1066a309fa87c0ccf66fd
[ -n "$LEAN_GITHASH" ] || LEAN_GITHASH=819816b2e0a3bf405af45ae5c7af2491d8f5bee6

WORK=$(mktemp -d /tmp/rt-external.XXXXXX)
COPY="$WORK/formal"
IO_OUT="$WORK/io"; mkdir -p "$IO_OUT"
cleanup() { [ "$KEEP" -eq 1 ] || rm -rf "$WORK"; }
trap cleanup EXIT

echo "== building the working copy under $COPY (real tree stays read-only) =="
mkdir -p "$COPY/.lake"
tar -C "$FORMAL" --exclude=./.lake --exclude=./redteam --exclude=./work --exclude=./APPROVALS \
  --exclude=./staging --exclude=./status -cf - . | tar -C "$COPY" -xf -
cp -a "$FORMAL/.lake/build" "$FORMAL/.lake/config" "$COPY/.lake/"
ln -s "$FORMAL/.lake/packages" "$COPY/.lake/packages"
cp "$FINAL_SRC" "$COPY/EGCheck/Final.lean"      # a no-op copy unless --final is given
echo "== in-band target: $FINAL_SRC ($FINAL_KIND Final.lean)"
# pristine EGCheck / root for resetting between attacks
cp -a "$COPY/EGCheck" "$WORK/EGCheck.orig"
cp "$COPY/EGCheck.lean" "$WORK/EGCheck.lean.orig"

# The in-band build uses the in-band target (the REAL EGCheck/Final.lean, or --final) unchanged.
# For attacks expected "inband+oob" (hardened Final.lean only), the out-of-band check runs against
# this DEV FINAL instead: the theorem of the committed-style Final.lean, without #guard_msgs/run_cmd,
# i.e. what the in-band check would leave if an attacker got past it.
FINALCHECK="$FORMAL/scripts/FinalCheck.lean"
DEV_FINAL="$WORK/DevFinal.lean"
cat > "$DEV_FINAL" <<'LEAN'
import EGCheck.Bridge

/-! Red-team DEV FINAL (formal/redteam/external/redteam.sh; TRUST.md §8 item 8): the theorem of the
committed-style `EGCheck/Final.lean` without its in-band checks. Used only in the temporary copy. -/

theorem EGCheck.erdos_184.{u} : type_of% @Erdos184.erdos_184.{u} :=
  EGCheck.Bridge.solution
LEAN

# run a lean build inside a read-only bind mount of the repo (defence: no write can reach it)
build() {  # build <module> ; stdout+stderr to $2
  local mod="$1" log="$2"
  unshare -m bash -c "
    mount --bind -o ro '$REPO' '$REPO' 2>/dev/null
    cd '$COPY' && RT_IO_OUT='$IO_OUT' RT_REAL_TREE='$REPO' LEAN_NUM_THREADS=2 lake build '$mod'
  " >"$log" 2>&1
}

run_finalcheck() {  # run_finalcheck <id> ; FinalCheck on the copy's EGCheck.Final -> $WORK/<id>.finalcheck.log
  ( cd "$COPY" && timeout 900 lake env lean --run "$FINALCHECK" --final-module EGCheck.Final \
    --expect-statement-sha256 "$STMT_SHA" --expect-closure-sha256 "$CLOS_SHA" \
    --expect-lean-githash "$LEAN_GITHASH" ) >"$WORK/$1.finalcheck.log" 2>&1
}

reset_copy() {
  rm -rf "$COPY/EGCheck" "$COPY/RTHack"
  cp -a "$WORK/EGCheck.orig" "$COPY/EGCheck"
  cp "$WORK/EGCheck.lean.orig" "$COPY/EGCheck.lean"
  # drop stale attack oleans so a failed build cannot reuse a previous success
  rm -f "$COPY"/.lake/build/lib/lean/EGCheck/{Bridge,Final,RTEvade,BridgeHack,RTX1,RTX2}.olean 2>/dev/null
  rm -rf "$COPY"/.lake/build/lib/lean/RTHack 2>/dev/null
}

apply_overlay() { # copy every file under patches/<id>/ (except spec) into the copy
  local id="$1"
  ( cd "$PATCHES/$id" && find . -type f ! -name spec -printf '%P\n' ) | while read -r rel; do
    mkdir -p "$COPY/$(dirname "$rel")"
    cp "$PATCHES/$id/$rel" "$COPY/$rel"
  done
}

verdict() { [ "$1" -eq 0 ] && echo miss || echo catch; }   # exit 0 = check did not fire

# expected OUT-OF-BAND (FinalCheck) verdict per attack
declare -A EXPECT=(
  [A]=catch [A1]=catch [A2]=inband [A3]=catch [A4]=catch [B1]=catch [C]=catch [D]=catch
  [t1]=catch [t2]=catch [t3]=catch [t4]=miss [t5]=catch [t6]=catch [t7]=catch [t8]=catch [t9]=catch
  [IO]=miss [N4]=catch )
# hardened Final.lean (TRUST.md §8 item 8): B1 and C are caught in-band by their own error, and the
# out-of-band check must still catch them against the dev final ("inband+oob").
if [ "$FINAL_KIND" = hardened ]; then EXPECT[B1]=inband+oob; EXPECT[C]=inband+oob; fi
# for [A2] the attack is expected to be caught IN-BAND (run_cmd), so the build fails and there is no
# out-of-band artifact — recorded as "inband".  for [IO] and [t4] out-of-band correctly does not
# fire (build-time IO / a bare option are not statement/axiom defects); lint / CI job separation
# cover them.

# the SPECIFIC out-of-band check that must fire (a bare non-zero exit is not enough: the current
# pre-γ tree has ambient sorries that fail the policy check regardless, so a caught verdict is only
# credited when the attack's own defect is what the log reports).
declare -A EXPECT_RE=(
  [A]='\[FAIL\] axioms:.*(sorryAx|depends)'
  [A1]='\[FAIL\] statement:'
  [A3]='\[FAIL\] axioms:.*(sorryAx|depends)'
  [B1]='\[FAIL\] statement:'
  [C]='\[FAIL\] import:.*already contains'
  [A4]='\[FAIL\] replay:'
  [D]='\[FAIL\] replay:'
  [t1]='\[FAIL\] policy:.*declares an axiom'
  [t2]='\[FAIL\] policy:.*declares an axiom'
  [t3]='\[FAIL\] policy:.*declares an axiom'
  [t5]='\[FAIL\] policy:.*(sorryAx|uses sorry)'
  [t6]='\[FAIL\] policy:.*declares an axiom'
  [t7]='\[FAIL\] policy:.*(implemented_by|extern|axiom Lean.ofReduceBool)'
  [t8]='\[FAIL\] (policy:.*sorry|meta:)'
  [t9]='\[FAIL\] meta:'
  [N4]='\[FAIL\] (origin|replay):.*EGCheck\.RTX\.bogus' )

# for "inband+oob": the error the in-band build log must show (the attack's own defect, not an
# unrelated build failure). B1: EGCheck.Bridge.solution (trivial) does not have the upstream type;
# C: the attacker's Erdos184.erdos_184 clashes with the directly imported upstream one.
declare -A EXPECT_INBAND_RE=(
  [B1]='[Tt]ype mismatch'
  [C]='already contains.*Erdos184\.erdos_184' )

ALL=(A A1 A2 A3 B1 C A4 D N4 t1 t2 t3 t4 t5 t6 t7 t8 t9 IO)
[ ${#SELECT[@]} -gt 0 ] && ALL=("${SELECT[@]}")

printf '\n%-5s %-9s %-9s %-7s %-9s %-9s  %s\n' ATTACK MODE IN-BAND LINT OUT-BAND LEANCHK RESULT
printf '%.0s-' {1..96}; echo
FAILS=0
for id in "${ALL[@]}"; do
  [ -f "$PATCHES/$id/spec" ] || { echo "no such attack: $id"; FAILS=$((FAILS+1)); continue; }
  MODE=$(sed -n 's/^MODE=//p' "$PATCHES/$id/spec")
  TARGET=$(sed -n 's/^TARGET=//p' "$PATCHES/$id/spec")
  reset_copy
  apply_overlay "$id"

  LINTV="-"; INBAND="-"; OUTBAND="-"; LC="-"

  if [ "$MODE" = finalattack ]; then
    # in-band: the REAL EGCheck/Final.lean, with the attacker's Bridge
    build "EGCheck.Final" "$WORK/$id.inband.log"; rc=$?
    INBAND=$([ $rc -eq 0 ] && echo green || echo caught)   # green = attacker won in-band
    ARTIFACT=$([ $rc -eq 0 ] && echo final || echo none)
    if [ $rc -ne 0 ] && [ "${EXPECT[$id]:-}" = inband+oob ]; then
      # caught in-band; exercise the out-of-band check anyway, on the dev final
      cp "$DEV_FINAL" "$COPY/EGCheck/Final.lean"
      build "EGCheck.Final" "$WORK/$id.devfinal.log" && ARTIFACT=devfinal || ARTIFACT=devfinal-builderr
    fi
    if [ "$ARTIFACT" = final ] || [ "$ARTIFACT" = devfinal ]; then
      run_finalcheck "$id"
      OUTBAND=$(verdict $?)
      if [ "$WITH_LC" -eq 1 ]; then
        ( cd "$COPY" && timeout 2400 lake env leanchecker --fresh EGCheck.Final ) \
          >"$WORK/$id.leanchecker.log" 2>&1
        LC=$(verdict $?)
      fi
      [ "$ARTIFACT" = devfinal ] && OUTBAND="$OUTBAND(dev)"
    elif [ "$ARTIFACT" = devfinal-builderr ]; then
      OUTBAND="builderr(dev)"
    else
      OUTBAND="n/a"   # nothing to check: the fake never builds
    fi
  else # evasion
    build "EGCheck.RTEvade" "$WORK/$id.inband.log"; rc=$?
    INBAND=$([ $rc -eq 0 ] && echo built || echo "builderr")
    if [ $rc -eq 0 ]; then
      ( cd "$COPY" && timeout 900 lake env lean --run "$FINALCHECK" --scan-only \
        --policy-roots EGCheck.RTEvade ) >"$WORK/$id.finalcheck.log" 2>&1
      OUTBAND=$(verdict $?)
    else
      OUTBAND="builderr"
    fi
    # IO fixture: confirm the attack actually wrote a file (and could NOT write the real tree)
    if [ "$id" = IO ]; then
      [ -f "$IO_OUT/rt_pwned.txt" ] && INBAND="wrote/tmp"
      [ -f "$REPO/formal/rt_pwned_real.txt" ] && { echo "SECURITY: real tree was written!"; FAILS=$((FAILS+1)); }
    fi
  fi

  # informational: the current (tooling-hardened) lint's verdict on the attack file(s)
  if [ "$MODE" = evasion ]; then
    python3 -I "$FORMAL/scripts/lint.py" "$COPY/EGCheck/RTEvade.lean" >/dev/null 2>&1
    LINTV=$(verdict $?)
  else
    python3 -I "$FORMAL/scripts/lint.py" "$COPY/EGCheck/Bridge.lean" >/dev/null 2>&1
    LINTV=$(verdict $?)
  fi

  # compare with expectation. a "catch" is credited only if the attack-specific check fired.
  exp="${EXPECT[$id]:-?}"
  got="$OUTBAND"
  ok=OK; why=""
  case "$exp" in
    catch)
      if [ "$got" != catch ]; then ok=MISMATCH; why="(out-band did not fire)"
      elif [ -n "${EXPECT_RE[$id]:-}" ] && ! grep -Eq "${EXPECT_RE[$id]}" "$WORK/$id.finalcheck.log"; then
        ok=MISMATCH; why="(wrong check fired; expected /${EXPECT_RE[$id]}/)"
      fi;;
    miss)  [ "$got" = miss ]  || { ok=MISMATCH; why="(out-band fired unexpectedly)"; };;
    inband) { [ "$INBAND" = caught ] && [ "$got" = "n/a" ]; } || { ok=MISMATCH; why="(not caught in-band)"; };;
    inband+oob)
      if [ "$INBAND" != caught ]; then ok=MISMATCH; why="(not caught in-band)"
      elif ! grep -Eq "${EXPECT_INBAND_RE[$id]}" "$WORK/$id.inband.log"; then
        ok=MISMATCH; why="(in-band build failed for another reason; expected /${EXPECT_INBAND_RE[$id]}/)"
      elif [ "$got" != "catch(dev)" ]; then ok=MISMATCH; why="(out-band on the dev final did not fire: $got)"
      elif [ -n "${EXPECT_RE[$id]:-}" ] && ! grep -Eq "${EXPECT_RE[$id]}" "$WORK/$id.finalcheck.log"; then
        ok=MISMATCH; why="(wrong check fired on the dev final; expected /${EXPECT_RE[$id]}/)"
      fi;;
  esac
  [ "$ok" = OK ] || FAILS=$((FAILS+1))
  printf '%-5s %-9s %-9s %-7s %-9s %-9s  %s %s\n' "$id" "$MODE" "$INBAND" "$LINTV" "$OUTBAND" "$LC" "$ok" "$why"
done

echo
echo "logs in $WORK ; $( [ "$KEEP" -eq 1 ] && echo 'kept (--keep)' || echo 'removed on exit')"
echo "expectations: $FINAL_KIND Final.lean ($FINAL_SRC)"
if [ "$FAILS" -eq 0 ]; then echo "REDTEAM: PASS (all out-of-band verdicts match)"; else echo "REDTEAM: FAIL ($FAILS mismatches)"; fi
exit $([ "$FAILS" -eq 0 ] && echo 0 || echo 1)
