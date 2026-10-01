#!/bin/sh
# Red-team regression for the gate, formal/scripts/pristine.sh (formal/work/trust/gate2.md).
#
#   formal/redteam/gate/run.sh [--keep] [--demo] [--from-worktree] [--repo DIR] [CASE...]
#
# Every case clones the repository into a `mktemp -d` directory, applies one attack (a file from
# fixtures/, installed WITHOUT its `.fixture` suffix, or a git/worktree manipulation), commits it in
# the temporary clone when the attack is a committed file, and runs the gate on the clone. The
# verdict must match the table: REJECT with the given category and path (regex on the gate's
# output), or PASS for the positive controls. Nothing is ever written to the real tree, and no
# fixture is ever executed (no lake, lean or python on a fixture), except with --demo.
#
#   --from-worktree  base = the source checkout's working tree (tracked + untracked, not ignored)
#                    committed in the clone, instead of its HEAD (local runs with uncommitted work).
#   --repo DIR       source repository (default: the checkout containing the current directory).
#   --demo           additionally show, in separate temporary directories, that the N1/N2/N3
#                    vectors really run code without the defences: `lake env true` with the
#                    fixture lakefile.lean (Lake imports only; no build), `python3 -c 'import json'`
#                    next to the fixture json.py, and lock.py next to the fixture hashlib.py.
#   --keep           keep the temporary directory.
# The gate under test is the copy next to this script (../../scripts/pristine.sh), i.e. the
# snapshot's copy in CI. Exit code 1 if any verdict differs from the table.
set -u
LC_ALL=C; export LC_ALL
HERE=$(cd "$(dirname "$0")" && pwd)
FX="$HERE/fixtures"
GATE="$HERE/../../scripts/pristine.sh"
KEEP=0; DEMO=0; FROM_WT=0; REPO=""; SELECT=""
while [ $# -gt 0 ]; do
  case "$1" in
    --keep) KEEP=1;;
    --demo) DEMO=1;;
    --from-worktree) FROM_WT=1;;
    --repo) REPO=$2; shift;;
    -*) echo "unknown option $1" >&2; exit 2;;
    *) SELECT="$SELECT $1";;
  esac
  shift
done
[ -f "$GATE" ] || { echo "gate not found: $GATE" >&2; exit 2; }
[ -n "$REPO" ] || REPO=$(git rev-parse --show-toplevel 2>/dev/null) \
  || { echo "run inside the repository or pass --repo DIR" >&2; exit 2; }
REPO=$(cd "$REPO" && pwd)
W=$(mktemp -d "${TMPDIR:-/tmp}/gate-redteam.XXXXXX") || exit 2
cleanup() { if [ "$KEEP" = 1 ]; then echo "kept $W"; else rm -rf "$W"; fi; }
trap cleanup EXIT HUP INT TERM
G() { git -c user.name=gate-redteam -c user.email=gate-redteam@invalid -c commit.gpgsign=false \
        -c core.hooksPath=/dev/null "$@"; }

# ---- base clone -----------------------------------------------------------------------------------
G clone -q --no-hardlinks "$REPO" "$W/base" || { echo "clone failed" >&2; exit 2; }
if [ "$FROM_WT" = 1 ]; then
  (cd "$W/base" && git ls-files) | while IFS= read -r p; do rm -f "$W/base/$p"; done
  (cd "$REPO" && git ls-files -co --exclude-standard) | while IFS= read -r p; do
    [ -f "$REPO/$p" ] && [ ! -L "$REPO/$p" ] || continue
    mkdir -p "$W/base/$(dirname "$p")" && cp -p "$REPO/$p" "$W/base/$p"
  done
  (cd "$W/base" && G add -A && G commit -q --allow-empty -m "worktree of $REPO") || exit 2
fi
BASEC=$(git -C "$W/base" rev-parse HEAD)
cp "$GATE" "$W/gate.sh"
TRUSTED_GATE="$W/gate.sh"          # the gate under test (never modified by a case)
git -C "$W/base" show "$BASEC:formal/scripts/pristine.sh" > "$W/refgate.sh" 2>/dev/null

echo "== gate red-team: source $REPO ($([ "$FROM_WT" = 1 ] && echo 'working tree' || echo HEAD)), base $BASEC"
echo "== gate under test: $GATE (sha256 $(sha256sum "$GATE" | cut -c1-16)...)"
if ! sh "$TRUSTED_GATE" -C "$W/base" > "$W/baseline.log" 2>&1; then
  echo "BASELINE FAIL: the gate rejects the unmodified base; its pins are stale or the tree is not clean:"
  grep '^REJECT' "$W/baseline.log" | head -20 | sed 's/^/    /'
  echo "(the integrator refreshes pins with: sh formal/scripts/pristine.sh --write-pins, at an approval)"
  exit 1
fi
echo "ok   baseline: $(tail -1 "$W/baseline.log")"

# ---- helpers ----------------------------------------------------------------------------------------
C="$W/c"
new_case() { rm -rf "$C"; G clone -q "$W/base" "$C" 2>/dev/null || { echo "clone failed" >&2; exit 2; }; }
commit_all() { (cd "$C" && G add -A -f . && G commit -q -m "$1") >/dev/null 2>&1 || { echo "commit failed: $1" >&2; exit 2; }; }
put() { mkdir -p "$C/$(dirname "$2")" && cp "$FX/$1" "$C/$2"; }         # put FIXTURE DEST
append() { printf '%s\n' "$2" >> "$C/$1"; }                                # append FILE LINE
FAILS=0; N=0
selected() { [ -z "$SELECT" ] && return 0; case " $SELECT " in *" $1 "*) return 0;; esac; return 1; }
# expect ID DESCRIPTION EXPECT(PASS|regex) [gate args...]   (gate: $GATE_USED, default the trusted one)
expect() {
  id=$1; desc=$2; want=$3; shift 3
  N=$((N + 1))
  sh "${GATE_USED:-$TRUSTED_GATE}" -C "$C" "$@" > "$W/$id.log" 2>&1; rc=$?
  if [ "$want" = PASS ]; then
    if [ $rc = 0 ]; then echo "ok   $id: PASS  -- $desc"
    else echo "FAIL $id: expected PASS, got rc=$rc -- $desc"; grep '^REJECT' "$W/$id.log" | head -5 | sed 's/^/       /'; FAILS=$((FAILS + 1)); fi
  else
    if [ $rc = 1 ] && grep -Eq "$want" "$W/$id.log"; then
      echo "ok   $id: $(grep -E "$want" "$W/$id.log" | head -1 | cut -c1-150)  -- $desc"
    else
      echo "FAIL $id: expected rc=1 and /$want/, got rc=$rc -- $desc"
      grep '^REJECT\|^PRISTINE' "$W/$id.log" | head -5 | sed 's/^/       /'; FAILS=$((FAILS + 1))
    fi
  fi
  GATE_USED=""
}

# ---- positive controls ----------------------------------------------------------------------------
if selected P0; then new_case; expect P0 "unmodified base" PASS; fi
if selected P1; then
  new_case
  printf 'import Mathlib\n\ntheorem gateRT : True := trivial\n' > "$C/formal/EG/Proof/GateRT.lean"
  append formal/comparator/Solution.lean "-- proof zone edit (gate red-team)"
  printf '# notes\n' > "$C/formal/work/gate-rt.md"
  commit_all "proof-zone and docs changes"
  expect P1 "ordinary proof/docs/Solution changes are not blocked" PASS
  expect P2 "same, with --trust-ref (gate taken from the ref)" PASS --trust-ref "$BASEC"
fi

# ---- N1: Lake configuration ------------------------------------------------------------------------
if selected N1; then new_case; put lakefile.lean.fixture formal/lakefile.lean; commit_all N1
  expect N1 "trust2.opus N1: committed formal/lakefile.lean" 'REJECT forbidden: formal/lakefile.lean: Lake'; fi
if selected N1u; then new_case; put lakefile.lean.fixture formal/lakefile.lean
  expect N1u "N1 left untracked" 'REJECT untracked: formal/lakefile.lean'; fi
if selected N1x; then new_case; put lakefile.lean.fixture formal/lakefile.lean
  echo 'lakefile.lean' >> "$C/.git/info/exclude"
  expect N1x "N1 untracked and hidden by .git/info/exclude (gate lists files with find)" 'REJECT untracked: formal/lakefile.lean'; fi
if selected N1g; then new_case; printf 'lakefile.lean\n' > "$C/formal/.gitignore"; commit_all "N1g gitignore"
  put lakefile.lean.fixture formal/lakefile.lean
  expect N1g "N1 hidden by a committed formal/.gitignore" 'REJECT untracked: formal/lakefile.lean'; fi
if selected N1c; then new_case; put lakefile.lean.fixture formal/Lakefile.lean; commit_all N1c
  expect N1c "N1 spelled Lakefile.lean (case-insensitive file systems)" 'REJECT forbidden: formal/Lakefile.lean'; fi
if selected N1n; then new_case; put lakefile.lean.fixture formal/EG/lakefile.lean; commit_all N1n
  expect N1n "nested lakefile.lean in the proof zone" 'REJECT forbidden: formal/EG/lakefile.lean'; fi
if selected N1k; then new_case; mkdir -p "$C/formal/.lake"; printf 'x' > "$C/formal/.lake/lakefile.olean"; commit_all N1k
  expect N1k "committed Lake workspace (cached lakefile.olean)" 'REJECT forbidden: formal/\.lake/lakefile\.olean'; fi
if selected N1t; then new_case; append formal/lakefile.toml 'moreLeanArgs = ["--plugin=/tmp/evil.so"]'; commit_all N1t
  expect N1t "lakefile.toml gains a Lean plugin" 'REJECT pin: formal/lakefile.toml'; fi
if selected N1m; then new_case; sed 's|https://github.com/google-deepmind/formal-conjectures|https://github.com/attacker/formal-conjectures|' \
    "$C/formal/lake-manifest.json" > "$W/m" && cp "$W/m" "$C/formal/lake-manifest.json"; commit_all N1m
  expect N1m "lake-manifest.json points a package at another repository" 'REJECT pin: formal/lake-manifest.json'; fi
if selected N1v; then new_case; printf 'leanprover/lean4:v4.99.0\n' > "$C/formal/lean-toolchain"; commit_all N1v
  expect N1v "lean-toolchain changed" 'REJECT pin: formal/lean-toolchain'; fi
if selected N1e; then new_case; printf 'attacker/lean4:evil\n' > "$C/formal/scripts/lean-toolchain"; commit_all N1e
  expect N1e "elan override file in formal/scripts" 'REJECT forbidden: formal/scripts/lean-toolchain'; fi
if selected N1r; then new_case; printf 'attacker/lean4:evil\n' > "$C/lean-toolchain"; commit_all N1r
  expect N1r "elan override file at the repository root" 'REJECT forbidden: lean-toolchain'; fi

# ---- N2: the lock / checker scripts ---------------------------------------------------------------
if selected N2; then new_case; put hashlib.py.fixture formal/scripts/hashlib.py; commit_all N2
  expect N2 "trust2.opus N2: formal/scripts/hashlib.py" 'REJECT unpinned: formal/scripts/hashlib.py'; fi
if selected N2m; then new_case; append formal/scripts/lock.py '# weakened'; commit_all N2m
  expect N2m "lock.py modified" 'REJECT pin: formal/scripts/lock.py'; fi
if selected N2p; then new_case; append formal/scripts/lock.py '# weakened'; commit_all "N2p lock"
  sh "$C/formal/scripts/pristine.sh" -C "$C" --write-pins > /dev/null 2>&1; commit_all "N2p repin"
  cp "$C/formal/scripts/pristine.sh" "$W/treegate.sh"
  expect N2p "attacker re-pins consistently: the TRUSTED gate still rejects" 'REJECT (pin: formal/scripts/lock.py|self: )'
  GATE_USED="$W/refgate.sh"
  expect N2p-ref "same, gate taken from the trust ref with --trust-ref" 'REJECT trustref: formal/scripts/(lock.py|pristine.sh)' --trust-ref "$BASEC"
  GATE_USED="$W/treegate.sh"
  expect N2p-self "same, but running the ATTACKER's gate: passes (self-verification is no defence; use --trust-ref)" PASS
  # trust3.fable Y11b: the attacker moves a lightweight tag to the re-pinned commit and the job takes
  # its gate from that tag. The gate now accepts only a full 40-hex commit id as trust ref.
  (cd "$C" && G tag -f trust-v1 HEAD && G tag -f -a -m "annotated" trust-v2 "$BASEC") >/dev/null 2>&1
  GATE_USED="$W/treegate.sh"
  expect N2p-tag "same, trust ref = a MOVED lightweight tag (attacker's gate from the tag): rejected, not a commit id" 'REJECT trustref: trust-v1: not a full 40-hex' --trust-ref trust-v1
  GATE_USED="$W/refgate.sh"
  expect N2p-short "same, trust ref = abbreviated commit id of the approved commit: rejected" 'REJECT trustref: [0-9a-f]{12}: not a full 40-hex' --trust-ref "$(printf '%.12s' "$BASEC")"
  GATE_USED="$W/refgate.sh"
  expect N2p-tagobj "same, trust ref = the 40-hex id of an annotated TAG object: rejected" 'REJECT trustref: [0-9a-f]{40}: names a tag object' --trust-ref "$(git -C "$C" rev-parse trust-v2)"
fi
if selected N2c; then new_case; mkdir -p "$C/formal/scripts/__pycache__"; printf 'x' > "$C/formal/scripts/__pycache__/lock.cpython-311.pyc"; commit_all N2c
  expect N2c "committed bytecode cache" 'REJECT forbidden: formal/scripts/__pycache__/lock.cpython-311.pyc'; fi
if selected N2s; then new_case; cp "$C/formal/scripts/lint.py" "$C/code/lint_copy.py"; rm "$C/formal/scripts/lint.py"
  ln -s ../../code/lint_copy.py "$C/formal/scripts/lint.py"; commit_all N2s
  expect N2s "pinned file replaced by a symlink to an identical copy (hash would match)" 'REJECT git: formal/scripts/lint.py: symlink'; fi

# ---- N3: Python path shadowing / start-up hooks --------------------------------------------------------
if selected N3; then new_case; put json.py.fixture formal/json.py; commit_all N3
  expect N3 "trust2.opus N3: formal/json.py" 'REJECT python: formal/json.py'; fi
if selected N3r; then new_case; put json.py.fixture json.py; commit_all N3r
  expect N3r "json.py at the repository root" 'REJECT forbidden: json.py'; fi
if selected N3s; then new_case; put json.py.fixture formal/scripts/json.py; commit_all N3s
  expect N3s "json.py next to the checker scripts" 'REJECT unpinned: formal/scripts/json.py'; fi
if selected N3c; then new_case; put sitecustomize.py.fixture formal/sitecustomize.py; commit_all N3c
  expect N3c "sitecustomize.py" 'REJECT forbidden: formal/sitecustomize.py'; fi
if selected N3p; then new_case; printf 'import os; os.system("true")\n' > "$C/code/evil.pth"; commit_all N3p
  expect N3p ".pth file anywhere" 'REJECT forbidden: code/evil.pth'; fi
if selected N3n; then new_case; printf 'x' > "$C/formal/scripts/_json.cpython-311-x86_64-linux-gnu.so"; commit_all N3n
  expect N3n "native module shadowing _json" 'REJECT forbidden: formal/scripts/_json'; fi
if selected N3v; then new_case; printf '3.11.0-evil\n' > "$C/.python-version"; commit_all N3v
  expect N3v "pyenv .python-version" 'REJECT forbidden: \.python-version'; fi

# ---- other code-before-check vectors ------------------------------------------------------------
if selected X1; then new_case; put envrc.fixture .envrc; commit_all X1
  expect X1 "direnv .envrc" 'REJECT forbidden: \.envrc'; fi
if selected X2; then new_case; put gitattributes.fixture .gitattributes; commit_all X2
  expect X2 ".gitattributes filter/diff driver" 'REJECT forbidden: \.gitattributes'; fi
if selected X3; then new_case
  printf '[submodule "x"]\n\tpath = formal/x\n\turl = https://example.invalid/x\n' > "$C/.gitmodules"
  (cd "$C" && G update-index --add --cacheinfo "160000,$BASEC,formal/x" && G add .gitmodules && G commit -q -m X3) >/dev/null 2>&1
  expect X3 "submodule" 'REJECT git: formal/x: submodule'; fi
if selected X4; then new_case; put evil.yml.fixture .github/workflows/evil.yml; commit_all X4
  expect X4 "extra workflow" 'REJECT unpinned: \.github/workflows/evil.yml'; fi
if selected X5; then new_case; put settings.local.json.fixture .claude/settings.local.json; commit_all X5
  expect X5 "Claude Code hook in .claude/settings.local.json" 'REJECT unpinned: \.claude/settings.local.json'; fi
if selected X6; then new_case; put settings.local.json.fixture formal/.claude/settings.json; commit_all X6
  expect X6 "nested .claude/ (hooks when an agent runs in formal/)" 'REJECT forbidden: formal/\.claude/settings.json'; fi
if selected X7; then new_case; put tasks.json.fixture .vscode/tasks.json; commit_all X7
  expect X7 "VS Code task that runs on folder open" 'REJECT forbidden: \.vscode/tasks.json'; fi
if selected X8; then new_case; printf '#!/bin/sh\necho pwned\n' > "$C/.git/hooks/post-checkout"; chmod +x "$C/.git/hooks/post-checkout"
  expect X8 "local git hook" 'REJECT githook: .*post-checkout'; fi
if selected X9; then new_case; git -C "$C" config core.fsmonitor "$W/fsmon.sh"
  expect X9 "local core.fsmonitor (runs on git status/diff)" 'REJECT gitconfig: core.fsmonitor'; fi
if selected X10; then new_case; git -C "$C" config filter.x.clean "sh -c true"
  expect X10 "local filter driver" 'REJECT gitconfig: filter.x.clean'; fi
if selected X11; then new_case; append formal/EG.lean "-- uncommitted"
  expect X11 "worktree differs from HEAD (strict)" 'REJECT modified: formal/EG.lean'
  expect X11-dev "same in --dev mode: not rejected, but not a trusted verdict" PASS --dev; fi
if selected X12; then new_case; printf 'x\n' > "$C/formal/work/caf$(printf '\303\251').md"; commit_all X12
  expect X12 "non-ASCII file name" 'REJECT names: '; fi
if selected X13; then new_case; printf '#!/bin/sh\n' > "$C/formal/EG/run.sh"; commit_all X13
  expect X13 "non-Lean file in the proof zone" 'REJECT zone: formal/EG/run.sh'; fi
if selected X14; then new_case; sed 's/^\(    EG-PIN closure-sha256 \).*/\1'"$(printf '%064d' 0)"'/' "$C/formal/TRUST.md" > "$W/t" \
    && cp "$W/t" "$C/formal/TRUST.md"; append formal/TRUST.md ""; commit_all X14
  expect X14 "TRUST.md pin edited (FinalCheck reads its pins from TRUST.md)" 'REJECT pin: formal/TRUST.md'; fi
if selected X15; then new_case; sed 's/"Classical.choice"/"Classical.choice", "sorryAx"/' "$C/formal/comparator/config.json" > "$W/cfg" \
    && cp "$W/cfg" "$C/formal/comparator/config.json"; commit_all X15
  expect X15 "comparator config permits sorryAx" 'REJECT pin: formal/comparator/config.json'; fi
if selected X16; then new_case; printf 'import Lean\n' > "$C/formal/redteam/tooling/RT/Extra.lean"; commit_all X16
  expect X16 "new red-team fixture (compiled by the trusted verify job)" 'REJECT unpinned: formal/redteam/tooling/RT/Extra.lean'; fi
if selected X17; then new_case; printf '[tools]\nlean = "evil"\n' > "$C/mise.toml"; commit_all X17
  expect X17 "mise.toml tool manager" 'REJECT forbidden: mise.toml'; fi
if selected X18; then new_case; grep -v 'pristine.sh' "$C/.github/workflows/release.yml" > "$W/r" && cp "$W/r" "$C/.github/workflows/release.yml"; commit_all X18
  expect X18 "release.yml without the gate step (detectable offline, not by the run itself)" 'REJECT pin: \.github/workflows/release.yml'; fi
if selected X19; then new_case; mkdir -p "$C/formal/.lake/build"; printf 'x' > "$C/formal/.lake/build/x.olean"
  expect X19 "formal/.lake present before the gate (restored cache / earlier lake call)" 'REJECT untracked: formal/\.lake: Lake directory present'
  expect X19-build "same with --allow-build (post-build re-check)" PASS --allow-build; fi
if selected X20; then new_case; printf '{"mcpServers":{"x":{"command":"sh"}}}\n' > "$C/.mcp.json"; commit_all X20
  expect X20 "MCP server config (.mcp.json)" 'REJECT forbidden: \.mcp.json'; fi
if selected X21; then new_case; printf 'go 1.24\nuse ./x\n' > "$C/go.work"; commit_all X21
  expect X21 "go.work (would redirect go builds in the tree)" 'REJECT forbidden: go.work'; fi
if selected X22; then new_case; mkfifo "$C/formal/work/fifo" 2>/dev/null || printf 'x' > "$C/formal/work/fifo"
  expect X22 "FIFO in the worktree" 'REJECT (special|untracked): formal/work/fifo'; fi

echo "gate red-team: $N checks, $FAILS unexpected verdict(s)"

# ---- demos: the vectors are real (separate temporary directories; never the real tree) ---------------
if [ "$DEMO" = 1 ]; then
  echo "== demo (temporary directories under $W/demo)"
  D="$W/demo"; mkdir -p "$D/n1" "$D/n3" "$D/n2/scripts"
  # N3
  cp "$FX/json.py.fixture" "$D/n3/json.py"
  (cd "$D/n3" && python3 -c 'import json' 2>/dev/null; [ -f PWNED-by-json.py.txt ] && echo "demo N3: python3 -c 'import json' in formal/ ran the repository json.py" )
  rm -f "$D/n3/PWNED-by-json.py.txt"
  (cd "$D/n3" && python3 -I -c 'import json' 2>/dev/null; [ -f PWNED-by-json.py.txt ] && echo "demo N3: STILL RAN with -I (unexpected)" || echo "demo N3: python3 -I -c 'import json': not imported")
  # N2
  cp "$HERE/../../scripts/lock.py" "$D/n2/scripts/lock.py"; cp "$FX/hashlib.py.fixture" "$D/n2/scripts/hashlib.py"
  (cd "$D/n2" && python3 scripts/lock.py files >/dev/null 2>&1; [ -f PWNED-by-hashlib.py.txt ] && echo "demo N2: STILL RAN (the -I re-exec guard failed)" || echo "demo N2: python3 scripts/lock.py (re-exec as -I): repository hashlib.py not imported")
  grep -v 'sys.flags.isolated\|os.execv' "$HERE/../../scripts/lock.py" | sed 's/^    # Never import.*$//' > "$D/n2/scripts/lock_noguard.py"
  (cd "$D/n2" && python3 scripts/lock_noguard.py files >/dev/null 2>&1; [ -f PWNED-by-hashlib.py.txt ] && echo "demo N2: without the guard, python3 scripts/lock.py imported the repository hashlib.py")
  # N1 (Lake imports only; one small `lake env` in a temp dir, no build)
  if command -v lake >/dev/null 2>&1; then
    cp "$FX/lakefile.lean.fixture" "$D/n1/lakefile.lean"
    printf 'name = "eg"\n' > "$D/n1/lakefile.toml"
    cp "$HERE/../../lean-toolchain" "$D/n1/lean-toolchain"
    (cd "$D/n1" && timeout 600 lake env true > "$D/n1.log" 2>&1)
    if [ -f "$D/n1/PWNED-by-lakefile.lean.txt" ]; then echo "demo N1: \`lake env true\` elaborated lakefile.lean next to lakefile.toml and ran its #eval ($(grep -o 'using lakefile.lean' "$D/n1.log" | head -1))"
    else echo "demo N1: marker not written; log:"; head -5 "$D/n1.log" | sed 's/^/    /'; fi
  else
    echo "demo N1: lake not on PATH; skipped"
  fi
fi

[ "$FAILS" = 0 ] && echo "GATE REDTEAM: PASS" || echo "GATE REDTEAM: FAIL"
[ "$FAILS" = 0 ]
