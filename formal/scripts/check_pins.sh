#!/usr/bin/env bash
# Verify the trusted pins recorded in TRUST.md (PLAN_FORMALIZATION.md §1, §12 risk 8), plus the
# integrity of every package checkout (trust audits of 2026-09-26, APPROVALS/reviews/trust.*.md).
#
#   scripts/check_pins.sh
#
# Checks (each prints `pin ok: ...` or `PIN MISMATCH ...`; exit 1 on any mismatch):
#   * lean-toolchain text, and the commit of the Lean binary that actually runs (`lean --githash`);
#   * lakefile.toml: the formal_conjectures `rev` and the mathlib `rev` (tag);
#   * lake-manifest.json: the formal_conjectures and mathlib revs;
#   * EVERY package of lake-manifest.json: checkout HEAD == manifest rev, and a clean worktree
#     (`git status --porcelain --untracked-files=all`, ignoring the package's own `.lake/` build
#     directory), so no source file that feeds the statement can be edited locally;
#   * formal-conjectures: its own lean-toolchain == ours, its lake-manifest's mathlib rev == ours
#     (and every package it shares with our manifest has the same rev);
#   * the two upstream files of TRUST.md item 3: SHA-256 and git blob id (worktree and HEAD tree).
#
# What this does NOT check: that the `.olean` build products correspond to these sources (the
# Mathlib cache is downloaded; FC/project oleans may be cached). That is covered by
# scripts/FinalCheck.lean (statement/closure hash pins, kernel replay), `leanchecker --fresh` and
# comparator in the release workflow (TRUST.md).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
# Python never imports from the working directory or the script directory (trust2.opus N2/N3):
# every call uses -I; PYTHONSAFEPATH covers any call that might lack it.
export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1
fail=0
want() { if [ "$2" != "$3" ]; then echo "PIN MISMATCH $1: want $2 got $3"; fail=1; else echo "pin ok: $1"; fi; }

LEAN_COMMIT=819816b2e0a3bf405af45ae5c7af2491d8f5bee6
FC_REV=2424bb480c590237ffbb2cc831ae4cb8977e045a
ML_REV=0df444a360eaa60ab8c11dca51a86af692955474
ML_TAG=v4.33.1
TOOLCHAIN="leanprover/lean4:v4.33.1"
FC=.lake/packages/formal_conjectures
ML=.lake/packages/mathlib
F184=FormalConjectures/ErdosProblems/184.lean
FDEC=FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean

# --- toolchain -------------------------------------------------------------------------------
want lean-toolchain "$TOOLCHAIN" "$(cat lean-toolchain)"
want lean-githash "$LEAN_COMMIT" "$(lean --githash 2>/dev/null || echo '<lean --githash failed>')"
case "$(lean --version 2>/dev/null)" in
  *"commit $LEAN_COMMIT"*) echo "pin ok: lean-version";;
  *) echo "PIN MISMATCH lean-version: want commit $LEAN_COMMIT in: $(lean --version 2>&1 | head -1)"; fail=1;;
esac
echo "info: $(lake --version 2>/dev/null | head -1 || echo 'lake --version failed')"

# --- lakefile.toml and lake-manifest.json ----------------------------------------------------
read_lakefile_rev() {  # $1 = package name; prints the `rev` of its [[require]] block
  python3 -I - "$1" <<'EOF'
import re, sys
name, cur, revs = sys.argv[1], None, {}
for line in open("lakefile.toml", encoding="utf-8"):
    line = line.split("#", 1)[0].strip()
    if line.startswith("[["):
        cur = None
    m = re.fullmatch(r'name\s*=\s*"([^"]*)"', line)
    if m:
        cur = m.group(1)
    m = re.fullmatch(r'rev\s*=\s*"([^"]*)"', line)
    if m and cur is not None:
        revs.setdefault(cur, []).append(m.group(1))
r = revs.get(name, [])
print(r[0] if len(r) == 1 else f"<{len(r)} rev entries>")
EOF
}
want lakefile-fc-rev "$FC_REV" "$(read_lakefile_rev formal_conjectures)"
want lakefile-mathlib-rev "$ML_TAG" "$(read_lakefile_rev mathlib)"

manifest_field() {  # $1 = manifest file, $2 = package, $3 = field
  python3 -I - "$1" "$2" "$3" <<'EOF'
import json, sys
f, name, field = sys.argv[1:4]
ps = [p for p in json.load(open(f, encoding="utf-8"))["packages"] if p["name"] == name]
print(ps[0].get(field) if len(ps) == 1 else f"<{len(ps)} entries for {name}>")
EOF
}
want manifest-fc-rev "$FC_REV" "$(manifest_field lake-manifest.json formal_conjectures rev)"
want manifest-mathlib-rev "$ML_REV" "$(manifest_field lake-manifest.json mathlib rev)"
want manifest-mathlib-inputRev "$ML_TAG" "$(manifest_field lake-manifest.json mathlib inputRev)"

# --- every package: HEAD == manifest rev, clean worktree --------------------------------------
PKGDIR=$(python3 -I -c 'import json;print(json.load(open("lake-manifest.json"))["packagesDir"])')
want manifest-packagesDir ".lake/packages" "$PKGDIR"
while IFS=$'\t' read -r name rev typ; do
  dir="$PKGDIR/$name"
  if [ "$typ" != "git" ]; then echo "PIN MISMATCH package $name: type $typ (only git packages are allowed)"; fail=1; continue; fi
  if [ ! -d "$dir" ]; then echo "PIN MISMATCH package $name: $dir missing"; fail=1; continue; fi
  want "package $name HEAD" "$rev" "$(git -C "$dir" rev-parse HEAD 2>/dev/null || echo '<not a git checkout>')"
  dirty=$(git -C "$dir" status --porcelain --untracked-files=all 2>&1 | grep -vE '^.. "?\.lake/' || true)
  if [ -n "$dirty" ]; then
    echo "PIN MISMATCH package $name: worktree not clean:"; echo "$dirty" | head -20 | sed 's/^/    /'; fail=1
  else
    echo "pin ok: package $name clean"
  fi
done < <(python3 -I -c '
import json
for p in json.load(open("lake-manifest.json"))["packages"]:
    print(p["name"], p.get("rev", ""), p.get("type", ""), sep="\t")')
extra=$(comm -13 <(python3 -I -c 'import json;[print(p["name"]) for p in json.load(open("lake-manifest.json"))["packages"]]' | sort) \
                 <(ls -1 "$PKGDIR" | sort) || true)
if [ -n "$extra" ]; then echo "PIN MISMATCH packages dir has entries not in the manifest: $extra"; fail=1; else echo "pin ok: no extra packages"; fi

# --- formal-conjectures' own pins -------------------------------------------------------------
want fc-lean-toolchain "$TOOLCHAIN" "$(cat $FC/lean-toolchain)"
want fc-manifest-mathlib-rev "$ML_REV" "$(manifest_field $FC/lake-manifest.json mathlib rev)"
while IFS=$'\t' read -r name rev; do
  ours=$(manifest_field lake-manifest.json "$name" rev)
  want "fc-manifest $name rev == ours" "$ours" "$rev"
done < <(python3 -I -c '
import json
for p in json.load(open(".lake/packages/formal_conjectures/lake-manifest.json"))["packages"]:
    print(p["name"], p.get("rev", ""), sep="\t")')

# --- the two upstream files (TRUST.md item 3) -------------------------------------------------
want 184.lean-sha256 9f36e4e053285cd8b886042eb609ace5f21f49bd81903eebca8000ff03e020d6 \
  "$(sha256sum $FC/$F184 | cut -d' ' -f1)"
want 184.lean-blob 36cc140cb3d8e60b08a842f1691fe9b73602f92b "$(git -C $FC hash-object $F184)"
want 184.lean-blob-HEAD 36cc140cb3d8e60b08a842f1691fe9b73602f92b "$(git -C $FC rev-parse HEAD:$F184)"
want Decomposition.lean-sha256 86bf339ad988733c67e443e7fc922bbc278fc48871f7e9ba515f0659d8fceff2 \
  "$(sha256sum $FC/$FDEC | cut -d' ' -f1)"
want Decomposition.lean-blob a4d3f066158b799e851dd8c6ac511ef2b6731111 "$(git -C $FC hash-object $FDEC)"
want Decomposition.lean-blob-HEAD a4d3f066158b799e851dd8c6ac511ef2b6731111 "$(git -C $FC rev-parse HEAD:$FDEC)"
want mathlib-tag "$ML_TAG" "$(git -C $ML tag --points-at HEAD 2>/dev/null | grep -x "$ML_TAG" || echo '<tag not at HEAD>')"

[ "$fail" = 0 ] && echo "check_pins: all pins ok" || echo "check_pins: MISMATCH"
exit $fail
