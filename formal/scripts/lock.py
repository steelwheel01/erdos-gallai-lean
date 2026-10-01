#!/usr/bin/env python3
"""Statement lock (PLAN_FORMALIZATION.md §4 "Lock").

    scripts/lock.py dump            # print current lock records (JSON) to stdout
    scripts/lock.py files [--strict]
        # only the file-hash part of `check` (no lake, no Lean): run it FIRST in the trusted jobs,
        # from the snapshot taken by scripts/pristine.sh (trust2.opus N2), before any lake call.
    scripts/lock.py check [--strict]
        # exit 1 if a LOCKED constant/file changed or disappeared. Constants and files that are not
        # locked yet are reported as PENDING (an error only with --strict, used from the P2→P3
        # statement freeze on and in release CI).
    scripts/lock.py update --approval APPROVALS/<file>.md [--modules M1 M2 ...]
        # (integrator only) lock the current records of the given modules (default: all), keeping
        # every other existing lock entry; the trust-boundary files are always re-hashed.

A record covers every constant declared in `EG/Spec/**` and `EG/Defs/**` (module prefixes
`EG.Spec`, `EG.Defs`) AND every `EG` constant (e.g. from `EG/Lib/**`) reachable from them through
types and definition bodies, plus a SHA-256 of every file under those directories and of the protected
check files. For each constant it stores
  * `hash`:    SHA-256 of kind, universe names, kernel type, and (for definitions) kernel value;
  * `closure`: SHA-256 of `hash` together with the closure hashes of the locked constants it uses,
               so a change to any definition a statement depends on changes the statement's
               closure hash.
The modules must be built first (`lake build EG`).
"""
import os
import sys
if __name__ == "__main__" and not sys.flags.isolated:
    # Never import from the script or the working directory (trust2.opus N2/N3): re-run as python3 -I.
    os.execv(sys.executable, [sys.executable, "-I"] + sys.argv)
import hashlib
import json
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LOCK = os.path.join(ROOT, "LOCK.json")
ROOT_PREFIXES = ["EG.Spec", "EG.Defs"]
DUMP_PREFIX = "EG"
PROTECTED_DIRS = ["EG/Spec", "EG/Defs"]
# Trust-boundary and tooling files, hashed as a whole. Paths are relative to formal/; `../` reaches
# the repository root. This list is TRUST.md §6 ("Protected files"; keep the two, CODEOWNERS and the
# `.claude/settings.json` deny list aligned). `scripts/**`, `redteam/**` (the checkers' regression
# fixtures and their expected verdicts), `comparator/patches/**` and `../.github/workflows/**` are
# expanded at run time, so a NEW file there shows up as PENDING (an error under --strict) until the
# integrator locks it. `EG/Spec/**`, `EG/Defs/**` are PROTECTED_DIRS below. Not listed on purpose:
# `EGCheck/Bridge*.lean`, `comparator/Solution.lean` and the rest of `EG/` are untrusted proof code
# that the out-of-band criterion (TRUST.md §4) checks.
PROTECTED_FILES = ["EGCheck/Final.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
                   "TRUST.md", "STATEMENT.md", "CONVENTIONS.md", "status/ratchet.json",
                   "comparator/Challenge.lean", "comparator/config.json",
                   "../.claude/settings.json", "../.github/CODEOWNERS"] + sorted(
    os.path.relpath(os.path.join(dp, f), ROOT)
    for sub in ("scripts", "redteam", os.path.join("comparator", "patches"),
                os.path.join("..", ".github", "workflows"))
    for dp, _, fs in os.walk(os.path.join(ROOT, sub))
    if "__pycache__" not in dp.split(os.sep)
    for f in fs if not f.endswith(".pyc"))
# Auto-generated companions of inductive types; determined by the inductive itself.
GENERATED = {"noConfusionType", "noConfusion", "ctorElimType", "ctorElim", "ctorIdx", "toCtorIdx",
             "sizeOf_spec", "casesOn", "recOn", "rec", "brecOn", "below", "binductionOn",
             "ibelow", "elim", "injEq", "inj"}


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def spec_modules():
    mods = []
    for d in PROTECTED_DIRS:
        for dirpath, _, files in os.walk(os.path.join(ROOT, d)):
            for f in sorted(files):
                if f.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(dirpath, f), ROOT)[:-5]
                    mods.append(rel.replace(os.sep, "."))
    return sorted(mods)


def file_hashes():
    out = {}
    paths = list(PROTECTED_FILES)
    for d in PROTECTED_DIRS:
        for dirpath, _, files in os.walk(os.path.join(ROOT, d)):
            for f in files:
                paths.append(os.path.relpath(os.path.join(dirpath, f), ROOT))
    for p in sorted(set(paths)):
        full = os.path.join(ROOT, p)
        if os.path.exists(full):
            with open(full, "rb") as fh:
                out[p] = hashlib.sha256(fh.read()).hexdigest()
    return out


def dump_records():
    mods = spec_modules()
    if not mods:
        return {}
    cmd = ["lake", "env", "lean", "--run", "scripts/Lock.lean", "--prefix", DUMP_PREFIX] + mods
    res = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(res.stdout + res.stderr)
        sys.exit("lock: scripts/Lock.lean failed (are the modules built? run `lake build EG`)")
    recs = {}
    for line in res.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        r = json.loads(line)
        last = r["name"].split(".")[-1]
        if r["aux"] or last in GENERATED:
            continue
        r["hash"] = sha("\x00".join([r["kind"], ",".join(r["levels"]), r["type"], r["value"]]))
        recs[r["name"]] = r
    # keep the roots (Spec/Defs modules) and everything reachable from them
    def is_root(r):
        return any(r["module"] == p or r["module"].startswith(p + ".") for p in ROOT_PREFIXES)
    keep, todo = set(), [n for n, r in recs.items() if is_root(r)]
    while todo:
        n = todo.pop()
        if n in keep or n not in recs:
            continue
        keep.add(n)
        todo.extend(recs[n]["deps"])
    recs = {n: r for n, r in recs.items() if n in keep}
    # closure hashes
    memo = {}

    def closure(n, stack=()):
        if n in memo:
            return memo[n]
        if n in stack:  # mutual recursion: fall back to own hash
            return recs[n]["hash"]
        deps = [d for d in recs[n]["deps"] if d in recs]
        h = sha(recs[n]["hash"] + "".join(closure(d, stack + (n,)) for d in sorted(deps)))
        memo[n] = h
        return h

    out = {}
    for n, r in sorted(recs.items()):
        out[n] = {"module": r["module"], "kind": r["kind"], "hash": r["hash"],
                  "closure": closure(n)}
    return out


def current():
    return {"constants": dump_records(), "files": file_hashes()}


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    cmd = sys.argv[1]
    if cmd == "dump":
        json.dump(current(), sys.stdout, indent=1, sort_keys=True)
        print()
    elif cmd in ("check", "files"):
        strict = "--strict" in sys.argv
        files_only = cmd == "files"
        cur = {"constants": {}, "files": file_hashes()} if files_only else current()
        if not os.path.exists(LOCK):
            sys.exit("lock: LOCK.json missing")
        with open(LOCK) as fh:
            locked = json.load(fh)
        bad, pending = [], []
        lc, cc = locked.get("constants", {}), cur["constants"]
        for n in ([] if files_only else sorted(set(lc) | set(cc))):
            if n not in cc:
                bad.append(f"removed locked constant {n}")
            elif n not in lc:
                pending.append(f"unlocked constant {n} ({cc[n]['module']})")
            elif lc[n]["closure"] != cc[n]["closure"]:
                what = "statement/definition" if lc[n]["hash"] != cc[n]["hash"] else "dependency"
                bad.append(f"changed locked {what}: {n}")
        lf, cf = locked.get("files", {}), cur["files"]
        for p in sorted(set(lf) | set(cf)):
            if p not in lf:
                pending.append(f"unlocked file {p}")
            elif lf[p] != cf.get(p):
                bad.append(f"locked file changed or missing: {p}")
        for b in bad:
            print("LOCK:", b)
        for q in pending:
            print("PENDING:", q)
        print(f"lock{' (files only)' if files_only else ''}: "
              f"{'-' if files_only else len(lc)} locked constants, {len(lf)} locked files; {len(bad)} violations, "
              f"{len(pending)} pending{' (strict)' if strict else ''}")
        sys.exit(1 if bad or (strict and pending) else 0)
    elif cmd == "update":
        if "--approval" not in sys.argv:
            sys.exit("lock: update requires --approval APPROVALS/<file>.md")
        appr = sys.argv[sys.argv.index("--approval") + 1]
        if not os.path.exists(os.path.join(ROOT, appr)):
            sys.exit(f"lock: approval file {appr} does not exist")
        mods = None
        if "--modules" in sys.argv:
            mods = [a for a in sys.argv[sys.argv.index("--modules") + 1:] if not a.startswith("--")]
        cur = current()
        old = {}
        if os.path.exists(LOCK):
            with open(LOCK) as fh:
                old = json.load(fh)
        consts = dict(old.get("constants", {}))
        files = dict(old.get("files", {}))
        added = 0
        for n, r in cur["constants"].items():
            if mods is None or r["module"] in mods:
                consts[n] = r
                added += 1
        for p, h in cur["files"].items():
            mod = p[:-5].replace(os.sep, ".") if p.endswith(".lean") else None
            if mods is None or p in PROTECTED_FILES or (mod is not None and mod in mods):
                files[p] = h
        # a locked constant that no longer exists is only dropped when its module is re-approved
        for n in list(consts):
            if n not in cur["constants"] and (mods is None or consts[n]["module"] in mods):
                del consts[n]
        history = old.get("history", [])
        history.append({"approval": appr, "modules": mods or "all"})
        out = {"constants": consts, "files": files, "history": history}
        with open(LOCK, "w") as fh:
            json.dump(out, fh, indent=1, sort_keys=True)
            fh.write("\n")
        print(f"lock: LOCK.json updated under {appr}: {added} constants (re)locked, "
              f"{len(consts)} locked in total")
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
