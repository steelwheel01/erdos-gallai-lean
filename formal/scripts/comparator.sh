#!/usr/bin/env bash
# Comparator harness (leanprover/comparator) for the Erdős–Gallai formalization.
# Layout and rationale: formal/comparator/README.md; details and measured dry runs:
# formal/work/trust/bridge.md; acceptance criterion: TRUST.md (proposal in staging/TRUST.md.proposed).
#
# Usage (from formal/):
#   scripts/comparator.sh check
#       Challenge.lean is byte-identical to the pinned upstream 184.lean (cmp + SHA-256 + git blob
#       of the pinned formal-conjectures commit); comparator/config.json is the release config;
#       Solution.lean does not import the upstream module; prints diff Challenge -> Solution.
#   scripts/comparator.sh tools [DIR]
#       Build landrun, lean4export and comparator at the pinned commits into DIR (default
#       $COMPARATOR_TOOLS, else $HOME/comparator-tools). comparator is built with the project
#       toolchain (Lean v4.33.1) plus comparator/patches/*.patch (see comparator/README.md).
#   scripts/comparator.sh canary [--tools DIR | --landrun FILE] [--expect-nnp]
#       Landlock canary (trust3.opus B2): fail (exit 2) unless the kernel has Landlock ABI >=
#       LANDLOCK_MIN_ABI and this landrun, called with comparator's own flags (--best-effort ...),
#       really confines writes and sets no_new_privs. --expect-nnp also requires the CALLING process
#       to have no_new_privs (used inside the systemd unit, to prove NoNewPrivileges=yes took effect).
#   scripts/comparator.sh run [--release] [--allow-sorry] [--scratch DIR] [--prebuilt]
#                             [--solution FILE] [--tools DIR]
#       Run comparator with comparator/config.json. Every run first runs the canary (all modes);
#       in --release mode it runs again inside the systemd unit, with --expect-nnp.
#       --scratch DIR  run in a fresh copy of formal/ at DIR (emptied first) whose lakefile.toml gets
#                      the `Challenge`/`Solution` lean_libs appended. Needed until the lakefile
#                      change in comparator/README.md is approved; .lake/packages is symlinked
#                      (read-only inside the sandbox), the project itself is rebuilt by comparator
#                      inside landrun unless --prebuilt.
#       --prebuilt     copy formal/.lake/build into the scratch copy (fast; NOT a faithful run:
#                      the project was then compiled outside the sandbox).
#       --solution F   use F as comparator/Solution.lean in the scratch copy (red-team fixtures).
#       --allow-sorry  also permit `sorryAx` (dry runs while the proof is incomplete; never
#                      acceptance).
#       --release      acceptance mode: refuses --allow-sorry/--prebuilt/--solution, refuses to run
#                      as root, runs comparator under `systemd-run --user` with
#                      RestrictAddressFamilies=~AF_UNIX (comparator README) and NoNewPrivileges=yes
#                      (no setuid path, e.g. sudo, from inside the unit: trust3.opus B2).
#       --system-unit  with --release: use `sudo systemd-run --uid=$(id -u) --gid=$(id -g)` (the
#                      system manager; for CI runners without a user systemd instance).
#
# Exit code: comparator's exit code (0 = "Your solution is okay!"), or 2 for a harness error.
set -euo pipefail

# ---- pins (TRUST.md; comparator/README.md) ----------------------------------------------------
LEAN_TOOLCHAIN="leanprover/lean4:v4.33.1"
LEAN_GITHASH="819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
FC_REV="2424bb480c590237ffbb2cc831ae4cb8977e045a"
CHALLENGE_UPSTREAM_PATH="FormalConjectures/ErdosProblems/184.lean"
CHALLENGE_SHA256="9f36e4e053285cd8b886042eb609ace5f21f49bd81903eebca8000ff03e020d6"
CHALLENGE_BLOB="36cc140cb3d8e60b08a842f1691fe9b73602f92b"
LANDRUN_URL="https://github.com/Zouuup/landrun"
LANDRUN_REV="811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"          # main, 2026-07-23 (v0.1.18)
LEAN4EXPORT_URL="https://github.com/leanprover/lean4export"
LEAN4EXPORT_REV="66f1fb4bc256072069767fce52d39480e4524869"      # master, 2026-09-24 (= comparator's manifest pin)
COMPARATOR_URL="https://github.com/leanprover/comparator"
COMPARATOR_REV="fd5d5bcf14177b187f66d4502071268d877887c3"       # master, 2026-09-25
AXIOMS_RELEASE='["propext", "Quot.sound", "Classical.choice"]'
# Landlock ABI 3 (Linux 6.2) is the first that also confines truncate(2); below it the canary fails.
LANDLOCK_MIN_ABI=3

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # formal/
FC_DIR="$HERE/.lake/packages/formal_conjectures"
export PATH="$HOME/.elan/bin:$PATH"
# Python never imports from the working directory or the script directory (trust2.opus N2/N3):
# every call uses -I; PYTHONSAFEPATH covers any call that might lack it.
export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1

die() { echo "comparator.sh: $*" >&2; exit 2; }
say() { echo "comparator.sh: $*" >&2; }

# ---- check ------------------------------------------------------------------------------------
cmd_check() {
  local ok=1 ch="$HERE/comparator/Challenge.lean" so="$HERE/comparator/Solution.lean"
  local cfg="$HERE/comparator/config.json" up="$FC_DIR/$CHALLENGE_UPSTREAM_PATH"
  [ -f "$ch" ] || die "missing $ch"
  [ -f "$so" ] || die "missing $so"
  [ -f "$cfg" ] || die "missing $cfg"
  [ -f "$up" ] || die "missing pinned upstream file $up (run lake to fetch packages)"
  local sha; sha=$(sha256sum "$ch" | cut -d' ' -f1)
  if [ "$sha" = "$CHALLENGE_SHA256" ]; then echo "ok   Challenge.lean SHA-256 = pin $CHALLENGE_SHA256"
  else echo "FAIL Challenge.lean SHA-256 $sha != pin $CHALLENGE_SHA256"; ok=0; fi
  local blob; blob=$(git hash-object "$ch")
  if [ "$blob" = "$CHALLENGE_BLOB" ]; then echo "ok   Challenge.lean git blob = pin $CHALLENGE_BLOB"
  else echo "FAIL Challenge.lean git blob $blob != pin $CHALLENGE_BLOB"; ok=0; fi
  local head; head=$(git -C "$FC_DIR" rev-parse HEAD)
  if [ "$head" = "$FC_REV" ]; then echo "ok   formal-conjectures HEAD = pin $FC_REV"
  else echo "FAIL formal-conjectures HEAD $head != pin $FC_REV"; ok=0; fi
  local tblob; tblob=$(git -C "$FC_DIR" rev-parse "HEAD:$CHALLENGE_UPSTREAM_PATH")
  if [ "$tblob" = "$CHALLENGE_BLOB" ]; then echo "ok   $CHALLENGE_UPSTREAM_PATH at the pinned commit has blob $tblob"
  else echo "FAIL $CHALLENGE_UPSTREAM_PATH at HEAD has blob $tblob != pin"; ok=0; fi
  if cmp -s "$ch" "$up"; then echo "ok   Challenge.lean is byte-identical to .lake/packages/formal_conjectures/$CHALLENGE_UPSTREAM_PATH"
  else echo "FAIL Challenge.lean differs from the upstream working-tree file"; ok=0; fi
  if python3 -I - "$cfg" "$AXIOMS_RELEASE" <<'EOF'
import json, sys
c = json.load(open(sys.argv[1])); want = json.loads(sys.argv[2]); bad = []
if c.get("challenge_module") != "Challenge": bad.append(f"challenge_module = {c.get('challenge_module')!r}")
if c.get("solution_module") != "Solution": bad.append(f"solution_module = {c.get('solution_module')!r}")
if c.get("theorem_names") != ["Erdos184.erdos_184"]: bad.append(f"theorem_names = {c.get('theorem_names')!r}")
ax = c.get("permitted_axioms", [])
if sorted(ax) != sorted(want) or len(set(ax)) != len(ax): bad.append(f"permitted_axioms = {ax!r}")
if c.get("definition_names"): bad.append("definition holes are not allowed")
extra = set(c) - {"challenge_module", "solution_module", "theorem_names", "permitted_axioms",
                  "enable_nanoda", "external_kernels"}
if extra: bad.append(f"unknown keys {sorted(extra)}")
for b in bad: print("FAIL config.json:", b)
if not bad: print("ok   config.json: Challenge/Solution, theorem Erdos184.erdos_184, axioms", sorted(want))
sys.exit(1 if bad else 0)
EOF
  then :; else ok=0; fi
  # Solution must not import the upstream file (the restated declarations would clash) and must
  # declare the theorem itself.
  if grep -Eq '^\s*(public\s+|meta\s+)*import\s+FormalConjectures\.ErdosProblems' "$so"; then
    echo "FAIL Solution.lean imports FormalConjectures.ErdosProblems.*"; ok=0
  else echo "ok   Solution.lean does not import FormalConjectures.ErdosProblems.*"; fi
  echo "---- diff Challenge.lean Solution.lean (informational) ----"
  diff "$ch" "$so" || true
  echo "----"
  if [ $ok = 1 ]; then echo "comparator check: OK"; else echo "comparator check: FAILED"; exit 1; fi
}

# ---- tools ------------------------------------------------------------------------------------
fetch_rev() { # url rev dir
  if [ ! -d "$3/.git" ]; then git clone -q "$1" "$3"; fi
  git -C "$3" fetch -q origin || true
  git -C "$3" checkout -q --force "$2"
  git -C "$3" reset -q --hard "$2"
  git -C "$3" clean -qfdx -e .lake
  [ "$(git -C "$3" rev-parse HEAD)" = "$2" ] || die "$3 is not at $2"
}

cmd_tools() {
  local T="${1:-${COMPARATOR_TOOLS:-$HOME/comparator-tools}}"
  mkdir -p "$T/bin"; T="$(cd "$T" && pwd)"
  command -v go >/dev/null || die "go is needed to build landrun"
  [ "$(lean --githash)" = "$LEAN_GITHASH" ] || die "lean on PATH is not $LEAN_TOOLCHAIN ($LEAN_GITHASH)"
  say "landrun $LANDRUN_REV"
  fetch_rev "$LANDRUN_URL" "$LANDRUN_REV" "$T/landrun"
  (cd "$T/landrun" && go build -o "$T/bin/landrun" ./cmd/landrun)
  say "lean4export $LEAN4EXPORT_REV (toolchain overridden to $LEAN_TOOLCHAIN)"
  fetch_rev "$LEAN4EXPORT_URL" "$LEAN4EXPORT_REV" "$T/lean4export"
  echo "$LEAN_TOOLCHAIN" > "$T/lean4export/lean-toolchain"
  (cd "$T/lean4export" && lake build lean4export)
  say "comparator $COMPARATOR_REV (toolchain overridden to $LEAN_TOOLCHAIN, patches applied)"
  fetch_rev "$COMPARATOR_URL" "$COMPARATOR_REV" "$T/comparator"
  echo "$LEAN_TOOLCHAIN" > "$T/comparator/lean-toolchain"
  local p
  for p in "$HERE"/comparator/patches/*.patch; do
    say "  applying $(basename "$p")"
    git -C "$T/comparator" apply "$p"
  done
  (cd "$T/comparator" && lake build comparator)
  [ "$(git -C "$T/comparator/.lake/packages/lean4export" rev-parse HEAD)" = "$LEAN4EXPORT_REV" ] \
    || die "comparator's lean4export package is not at $LEAN4EXPORT_REV"
  ln -sf "$T/lean4export/.lake/build/bin/lean4export" "$T/bin/lean4export"
  ln -sf "$T/comparator/.lake/build/bin/comparator" "$T/bin/comparator"
  (cd "$T/bin" && sha256sum landrun "$(readlink -f lean4export)" "$(readlink -f comparator)")
  say "tools ready in $T/bin"
}

# ---- Landlock canary (trust3.opus B2) -----------------------------------------------------------
# comparator (Main.lean buildLandrunArgs) always passes --best-effort to landrun. With go-landlock
# v0.9.0, best-effort on a kernel without Landlock restricts NOTHING (and does not even set
# no_new_privs), while landrun still reports success. So the harness proves, before comparator
# starts, that the kernel supports Landlock and that this very landrun binary, with comparator's
# flags, denies a write outside its writable directory. Anything unexpected fails closed.
landlock_canary() {  # $1 = landrun binary, $2 = 1 to require no_new_privs in the calling process
  local landrun="$1" want_nnp="${2:-0}" abi d c rc nnp=0 line
  [ -x "$landrun" ] || die "Landlock canary: landrun $landrun is not executable"
  if [ "$want_nnp" = 1 ]; then
    while IFS= read -r line; do
      case "$line" in NoNewPrivs:*1) nnp=1;; esac
    done < /proc/self/status
    [ "$nnp" = 1 ] || die "Landlock canary: this process lacks no_new_privs (systemd NoNewPrivileges=yes did not take effect)"
  fi
  # landlock_create_ruleset(NULL, 0, LANDLOCK_CREATE_RULESET_VERSION) returns the ABI version, or -1.
  abi=$(python3 -I -c '
import ctypes, platform
nr = {"x86_64": 444, "aarch64": 444}.get(platform.machine())
if nr is None:
    print(-1)
else:
    libc = ctypes.CDLL(None, use_errno=True)
    libc.syscall.restype = ctypes.c_long
    print(libc.syscall(nr, None, ctypes.c_size_t(0), ctypes.c_uint32(1)))
') || abi=-1
  case "$abi" in ''|*[!0-9]*) abi=-1;; esac
  [ "$abi" -ge "$LANDLOCK_MIN_ABI" ] \
    || die "Landlock canary: kernel Landlock ABI is $abi (need >= $LANDLOCK_MIN_ABI); landrun --best-effort would run the Solution build unsandboxed. Refusing."
  d=$(mktemp -d "${TMPDIR:-/tmp}/eg-canary-rw.XXXXXX") && c=$(mktemp -d "${TMPDIR:-/tmp}/eg-canary-ro.XXXXXX") \
    || die "Landlock canary: mktemp failed"
  # Same flags as comparator's buildLandrunArgs, with one writable directory $d. Only shell builtins
  # run inside (no other executable is in --rox).
  rc=0
  "$landrun" --best-effort --ro / --rw /dev -ldd -add-exec --rwx "$d" -- /bin/sh -c ': > "$1/inside"' sh "$d" \
    >/dev/null 2>&1 || rc=$?
  if [ "$rc" != 0 ] || [ ! -f "$d/inside" ]; then
    rm -rf "$d" "$c"; die "Landlock canary: landrun could not write inside its writable directory (rc $rc); refusing"
  fi
  rc=0
  "$landrun" --best-effort --ro / --rw /dev -ldd -add-exec --rwx "$d" -- /bin/sh -c '
      n=0; while IFS= read -r l; do case "$l" in NoNewPrivs:*1) n=1;; esac; done < /proc/self/status
      [ "$n" = 1 ] || exit 97
      ( : > "$1/escaped" ) 2>/dev/null || exit 98
      exit 0' sh "$c" >/dev/null 2>&1 || rc=$?
  if [ -e "$c/escaped" ] || [ "$rc" = 0 ]; then
    rm -rf "$d" "$c"; die "Landlock canary: a write OUTSIDE the sandbox succeeded; landrun is not confining. Refusing."
  fi
  if [ "$rc" != 98 ]; then
    rm -rf "$d" "$c"; die "Landlock canary: unexpected result $rc (97 = no_new_privs not set inside landrun); refusing"
  fi
  rm -rf "$d" "$c"
  say "Landlock canary: ABI $abi; a write outside the sandbox was denied; no_new_privs set inside landrun$([ "$want_nnp" = 1 ] && echo '; this unit has NoNewPrivileges')"
}

cmd_canary() {
  local tools="${COMPARATOR_TOOLS:-$HOME/comparator-tools}" landrun=""
  local nnp=0
  while [ $# -gt 0 ]; do
    case "$1" in
      --tools) tools="$2"; shift;;
      --landrun) landrun="$2"; shift;;
      --expect-nnp) nnp=1;;
      *) die "unknown option $1";;
    esac
    shift
  done
  [ -n "$landrun" ] || landrun="${COMPARATOR_LANDRUN:-$tools/bin/landrun}"
  landlock_canary "$landrun" "$nnp"
}

# ---- run --------------------------------------------------------------------------------------
cmd_run() {
  local release=0 system_unit=0 allow_sorry=0 scratch="" prebuilt=0 solution="" tools="${COMPARATOR_TOOLS:-$HOME/comparator-tools}"
  while [ $# -gt 0 ]; do
    case "$1" in
      --release) release=1;;
      --system-unit) system_unit=1;;
      --allow-sorry) allow_sorry=1;;
      --scratch) scratch="$2"; shift;;
      --prebuilt) prebuilt=1;;
      --solution) solution="$2"; shift;;
      --tools) tools="$2"; shift;;
      *) die "unknown option $1";;
    esac
    shift
  done
  if [ $release = 1 ]; then
    [ $allow_sorry = 0 ] && [ $prebuilt = 0 ] && [ -z "$solution" ] \
      || die "--release excludes --allow-sorry, --prebuilt and --solution"
    [ "$(id -u)" != 0 ] || die "--release: comparator must not run as a privileged user (README assumption 6)"
    command -v systemd-run >/dev/null && [ -d /run/systemd/system ] \
      || die "--release: systemd-run and a running systemd are required (RestrictAddressFamilies=~AF_UNIX)"
  fi
  local landrun="${COMPARATOR_LANDRUN:-$tools/bin/landrun}"
  local l4e="${COMPARATOR_LEAN4EXPORT:-$tools/bin/lean4export}"
  local bin="${COMPARATOR_BIN:-$tools/bin/comparator}"
  for f in "$landrun" "$l4e" "$bin"; do [ -x "$f" ] || die "missing tool $f (run: scripts/comparator.sh tools)"; done
  [ "$(lean --githash)" = "$LEAN_GITHASH" ] || die "lean on PATH is not $LEAN_TOOLCHAIN"
  (cd "$HERE" && cmd_check >/dev/null) || die "scripts/comparator.sh check fails; run it for details"
  landlock_canary "$landrun" 0

  local proj="$HERE"
  if [ -n "$scratch" ]; then
    [ "$(readlink -f "$scratch")" != "$HERE" ] || die "--scratch must not be formal/ itself"
    if [ -e "$scratch" ] && [ -n "$(ls -A "$scratch" 2>/dev/null)" ] && [ ! -f "$scratch/.comparator-scratch" ]; then
      die "--scratch $scratch exists, is not empty and was not made by this script; refusing to delete it"
    fi
    rm -rf "$scratch"; mkdir -p "$scratch/.lake" "$scratch/comparator"; touch "$scratch/.comparator-scratch"
    proj="$(cd "$scratch" && pwd)"
    (cd "$HERE" && cp lakefile.toml lake-manifest.json lean-toolchain EG.lean EGTest.lean EGCheck.lean "$proj/" \
      && cp -r EG EGTest EGCheck "$proj/" \
      && cp comparator/Challenge.lean comparator/Solution.lean comparator/config.json "$proj/comparator/")
    [ -z "$solution" ] || cp "$solution" "$proj/comparator/Solution.lean"
    ln -s "$HERE/.lake/packages" "$proj/.lake/packages"
    [ $prebuilt = 0 ] || cp -a "$HERE/.lake/build" "$proj/.lake/build"
    if ! grep -q '^name = "Solution"' "$proj/lakefile.toml"; then
      cat >> "$proj/lakefile.toml" <<'EOF'

# Comparator challenge and solution (formal/comparator/README.md). Appended by
# scripts/comparator.sh --scratch; only comparator builds them.
[[lean_lib]]
name = "Challenge"
srcDir = "comparator"

[[lean_lib]]
name = "Solution"
srcDir = "comparator"
EOF
    fi
  else
    grep -q '^name = "Solution"' "$HERE/lakefile.toml" && grep -q '^name = "Challenge"' "$HERE/lakefile.toml" \
      || die "lakefile.toml has no Challenge/Solution lean_libs yet (proposed change, comparator/README.md); use --scratch DIR"
  fi

  local cfg="$proj/comparator/config.json"
  if [ $allow_sorry = 1 ]; then
    cfg="$proj/comparator/config.allow-sorry.json"
    python3 -I - "$proj/comparator/config.json" "$cfg" <<'EOF'
import json, sys
c = json.load(open(sys.argv[1])); c["permitted_axioms"] = c["permitted_axioms"] + ["sorryAx"]
json.dump(c, open(sys.argv[2], "w"), indent=4)
EOF
    say "DRY RUN: sorryAx is permitted (never an acceptance run)"
  fi
  [ "$(id -u)" != 0 ] || say "WARNING: running as root (comparator README assumption 6 not met; dry run only)"
  say "project: $proj"
  say "config:  $cfg"
  cd "$proj"
  local rc=0
  if [ $release = 1 ]; then
    local sd=(systemd-run --user)
    [ $system_unit = 0 ] || sd=(sudo systemd-run --uid="$(id -u)" --gid="$(id -g)")
    "${sd[@]}" --property=RestrictAddressFamilies=~AF_UNIX --property=NoNewPrivileges=yes \
      --wait --pipe --collect \
      -E PATH="$PATH" -E HOME="$HOME" -E COMPARATOR_LANDRUN="$landrun" -E COMPARATOR_LEAN4EXPORT="$l4e" \
      --working-directory="$proj" -- \
      bash -c "'$HERE/scripts/comparator.sh' canary --landrun '$landrun' --expect-nnp && lake env '$bin' '$cfg'" \
      || rc=$?
  else
    say "WARNING: not using systemd-run (no AF_UNIX restriction; dry run only)"
    COMPARATOR_LANDRUN="$landrun" COMPARATOR_LEAN4EXPORT="$l4e" lake env "$bin" "$cfg" || rc=$?
  fi
  say "comparator exit code $rc"
  return $rc
}

case "${1:-}" in
  check) shift; cd "$HERE"; cmd_check "$@";;
  tools) shift; cmd_tools "$@";;
  run) shift; cmd_run "$@";;
  canary) shift; cmd_canary "$@";;
  *) sed -n '2,/^set -euo/p' "$0" | sed '$d'; exit 2;;
esac
