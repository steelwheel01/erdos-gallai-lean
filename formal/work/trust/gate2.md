# Trust hardening, round 3: the gate (agent id `gate`, 2026-09-26)

This round responds to the second trust audit: `APPROVALS/reviews/trust2.opus.md` (REJECT on N1–N4) and
`trust2.fable.md` (approve with notes). This agent owns the code-before-check attack class, which covers
opus N1 (`lakefile.lean`), N2 (the lock verifies itself) and N3 (Python stdlib shadowing), and the
workflow items of both audits. N4 (FinalCheck attribution) and the text of TRUST.md belong to other
agents.

Constraints I kept:
* No protected file was touched: TRUST.md, `EGCheck/Final.lean`, `lakefile.toml`, `lake-manifest.json`,
  `lean-toolchain`, `.claude/**`.
* No git command modified the repository. Commits were made only inside `mktemp -d` clones.
* Every attack ran in `mktemp -d` clones or directories.

## Files changed

| File | Change |
|---|---|
| `scripts/pristine.sh` (new) | The gate. Pure POSIX sh plus git and coreutils, tested with dash. It never executes a repository file. |
| `redteam/gate/run.sh`, `redteam/gate/fixtures/*.fixture` (new) | 53 checks: 5 positive controls, the N1/N2/N3 attacks and their variants, and 20 other code-before-check vectors. `--demo` shows that N1/N2/N3 really do run code. |
| `.github/workflows/ci.yml` | Gate first, then a snapshot; everything else runs from the snapshot. A gate re-check after the build. New steps: `FinalCheck --scan-only`, the `STATEMENT.md` regeneration diff, and the gate red-team. The slow red-team suites run weekly, on dispatch, or when the checkers change. |
| `.github/workflows/release.yml` | Gate first in all three jobs. `verify` and `comparator` run from the snapshot. `lock.py files --strict` is the first Python call. `STATEMENT.md` is regenerated and diffed. The comparator job now uses `scripts/comparator.sh check|tools|run --release --system-unit`. |
| `scripts/lock.py` | New subcommand `files [--strict]`: the file-hash part only, with no lake or Lean. |
| `scripts/{lint,lock,status,gen_roots}.py` | When run as `__main__` without `-I`, each script re-executes itself as `python3 -I …`, before importing anything except `os` and `sys`. |
| `scripts/check_pins.sh`, `scripts/comparator.sh`, `redteam/tooling/run.sh`, `redteam/external/redteam.sh` | Every `python3` call uses `-I`, and the scripts export `PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1`. |
| `staging/TRUST.md.gate.md` (new) | Proposed TRUST.md text for §2 items 8–9, §4 step 0 and item 1, and §6. It should be merged into `TRUST.md.proposed`. |

## 1. `scripts/pristine.sh`

### How to run it

```
sh formal/scripts/pristine.sh [-C DIR] [--allow-build | --dev] [--trust-ref REF]
                              [--snapshot DIR [--link-lake]]
sh formal/scripts/pristine.sh --verify-snapshot DIR
sh formal/scripts/pristine.sh --print-pins | --write-pins      # integrator, at an approval
```

It prints one `REJECT <category>: <path>: <reason>` line per finding, then `PRISTINE: PASS` or
`PRISTINE: FAIL`. The exit code is 0, 1, or 2 for a usage error.

### Modes

**Strict (the default).** Four conditions must hold:
* The worktree is byte-identical to HEAD. Files are compared by git blob id of the raw bytes
  (`hash-object --no-filters`), so no filter, textconv, fsmonitor or autocrlf setting is involved.
* There are no untracked files.
* There are no ignored files. The file list comes from `find`, so `.gitignore` and
  `.git/info/exclude` cannot hide anything (cases N1g and N1x).
* `formal/.lake` does not exist.

**`--allow-build`.** The same, but `formal/.lake` may exist and is not analysed. Use it for re-checks
after a lake call.

**`--dev`.** Local work: modified and untracked files are allowed, but the policy still applies to
them. The verdict is `DEV-PASS`, which is not a trusted verdict.

### The file policy

This is the list of code-before-check vectors, enumerated. Each rule applies to HEAD and to the worktree.

1. **Lake and elan.** Rejected anywhere except the three pinned files:
   * `lakefile.lean`, `lakefile.toml`, `lakefile.olean*`, `lakefile.ilean`, `leanpkg.toml`,
     `lake-manifest.json`, `lean-toolchain`, `lean-toolchain.toml`. These names are matched
     case-insensitively, for macOS.
   * Any `.lake/` or `lake-packages/` directory. That includes a committed workspace, a cached
     `lakefile.olean` or a package checkout.

   `formal/lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are pinned by SHA-256. Pinning
   catches:
   * `moreLeanArgs` / `--plugin` / `--load-dynlib`;
   * `leanOptions`;
   * package URL or rev changes;
   * `path` packages.
2. **Python.** Rejected:
   * `.py` in `formal/` outside `formal/scripts/`;
   * any file in `formal/scripts/` that is not in the pinned allowlist;
   * `*.py` at the repository root.

   Rejected anywhere:
   * `*.pth`, `sitecustomize.py`, `usercustomize.py`;
   * `__pycache__/`, `*.pyc`, `*.pyo`, `*.pyd`;
   * native modules `*.so*`, `*.dylib`, `*.dll`;
   * `pyvenv.cfg`, `.python-version`.

   This is the second layer. The first layer is that every Python call now uses `-I`.
3. **Tool managers, shells, editors and agents.** Rejected:
   * `.envrc` (direnv), `.env*`, `.tool-versions` (asdf), `mise*.toml`, `.mise*`, `.rtx.toml`;
   * `.node-version`, `.nvmrc`, `.ruby-version`, `.sdkmanrc`;
   * `go.work*`, `go.env`, `.npmrc`, `.yarnrc*`;
   * shell rc files, `.curlrc`, `.wgetrc`, `.netrc`;
   * `.vscode/`, `.devcontainer/`, `.idea/`, `.husky/`, `.mise/`, `.flox/`;
   * `.pre-commit-config.yaml`, `.mcp.json`, `CLAUDE.local.md`;
   * `.claude/` or `.github/` anywhere except the pinned top-level ones. A nested `formal/.claude`
     would load Claude Code hooks for an agent running in `formal/`.
4. **Git.** Rejected:
   * `.gitattributes`, `.gitmodules`, `.lfsconfig`, `.gitconfig`, nested `.git`;
   * symlinks and submodules in HEAD. A symlink to an identical copy would even match its pin
     (case N2s);
   * symlinks, FIFOs and devices in the worktree;
   * control, non-ASCII, quote or backslash characters in file names;
   * unmerged index entries.

   Local state is also checked, because it runs code on git commands. The local and worktree git
   config may not set `core.hooksPath`, `fsmonitor`, `sshCommand`, `pager`, `askPass`, `gitProxy` or
   `editor`, nor `filter.*`, `diff.external`, `diff.*.command`/`textconv`, `merge.*.driver`,
   credential helpers, `protocol.*`, `uploadpack.packObjectsHook`, `gpg` programs or
   `url.*.insteadOf`. Also rejected: any non-sample hook in the hooks directory, and a non-empty
   `info/attributes`.

   The gate's own git calls run with `core.fsmonitor=false`, `core.hooksPath=/dev/null` and
   `GIT_OPTIONAL_LOCKS=0`. They never run `status` or `diff`.
5. **Zones of `formal/`.**
   * Proof zone: `EG.lean`, `EGTest.lean`, `EGCheck.lean`, `EG*/**.lean` (path components must match
     `[A-Za-z_][A-Za-z0-9_]*`) and `comparator/Solution.lean`.
   * Inert data: top-level `*.md`, `LOCK.json`, `APPROVALS/**.md`, `work/**.{md,json}`,
     `status/**.{md,json}`, `staging/**.{md,proposed}`.
   * Anything else in `formal/` is rejected.
6. **Trusted zone, as an allowlist with SHA-256 pins.** Every file must be in the pin block with its
   hash; a new, missing or changed file is rejected. The zone is:
   * `formal/scripts/**` (except the gate itself);
   * `formal/redteam/**`;
   * `formal/comparator/**` except `Solution.lean`;
   * the three lake files;
   * `TRUST.md` (FinalCheck reads its pins from it), `STATEMENT.md`, `EGCheck/Final.lean`;
   * `.github/**` and `.claude/**`.

   Today that is 100 files. The pin block sits inside the script, so the whole gate is one file with
   one hash.

### The gate cannot pin itself

This is the N2 root cause, and I state it plainly. An attacker who changes `lock.py` and runs
`--write-pins` gets a tree whose *own* gate passes. Case N2p-self measures this, as expected.

Two remedies:
* **Use a trusted copy of the gate.** Take it from the snapshot or from the trust commit. That copy
  rejects the tree (N2p). It also rejects if the tree's copy of the gate differs from the running
  one ("self").
* **Use `--trust-ref REF`.** Run REF's copy of the gate (`git show REF:formal/scripts/pristine.sh`).
  Every trusted-zone file and the gate itself must then equal REF (N2p-ref).

In the workflows, REF is the repository variable `EG_TRUST_REF`. Repository variables are set by
admins, not by commits. Without the variable, the workflows run the checkout's gate, and the reader
must compare the logged gate SHA-256 with the approved value (proposed §2 item 8).

The workflow file itself cannot be protected by a step inside it. A GitHub run is evidence only if
`.github/workflows/*.yml` at the tested commit are the pinned ones. The gate verifies that offline in
seconds (case X18).

### Snapshot

`--snapshot DIR` runs only after a PASS. It works as follows:
* It copies every checked file of `formal/`, `.github/` and `.claude/` to `DIR`.
* It checks each copy with `cmp` and against the pins, then makes the copied files read-only.
* `DIR/formal/.lake` is an empty real directory. With `--link-lake` it is a symlink to the
  checkout's `formal/.lake` instead; CI uses that, so the cache and build are shared.
* `--verify-snapshot DIR` re-checks a snapshot later.

**Measured on a clean clone of the current working tree** (all from the snapshot, with `.lake`
pointing at the real packages and build):
* `pristine.sh --snapshot`: PASS in 3.4 s, 560 files, 100 of 100 pins.
* `check_pins.sh`: all pins ok.
* `comparator.sh check`: OK.
* `lint --self-test`: 62/62.
* `lint`: 0 findings.
* `lock.py files`: runs. It reports 2 violations, `EG/Defs/Graph.lean` and `EG/Defs/Objects.lean`,
  which another agent is currently editing. That is not a gate issue.
* `redteam/tooling/run.sh`: all 14 verdicts as expected.
* `lake env lean --run scripts/Statement.lean`, then `diff` against `STATEMENT.md`: **identical**,
  in 17 s at 8.8 GB RSS.
* `FinalCheck.lean --scan-only --allow-sorry --policy-roots EG,EGTest,EGCheck`: `FINALCHECK: PASS`
  with 1 warning (the 3 known `sorryAx` users). `oleans` also passed through the symlinked `.lake`.
  46 s, 9.0 GB RSS.
* `actionlint` 1.7.7 on both workflows: no findings. `shellcheck` was not available, so the shell
  lints inside it did not run.

## 2. Red-team: `redteam/gate/run.sh` (53 checks, all as expected)

Command: `sh formal/redteam/gate/run.sh --from-worktree --demo`. It took about 2 min and never runs
lake, lean or python on a fixture outside `--demo`. Full output:
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/gate_rt.log`.

| Case | Attack | Gate verdict |
|---|---|---|
| P0, P1, P2, X11-dev, X19-build | positive controls: unmodified tree; new proof module, docs and `Solution.lean` edits (also with `--trust-ref`); `--dev`; `--allow-build` | PASS |
| **N1** | `formal/lakefile.lean` (trust2.opus N1) | `forbidden: formal/lakefile.lean` |
| N1u / N1x / N1g | same, left untracked / hidden by `.git/info/exclude` / hidden by a committed `formal/.gitignore` | `untracked: formal/lakefile.lean` |
| N1c, N1n | `Lakefile.lean`; `formal/EG/lakefile.lean` | `forbidden` |
| N1k | committed `formal/.lake/lakefile.olean` | `forbidden` (`.lake`) |
| N1t, N1m, N1v | `lakefile.toml` gets a `--plugin`; manifest URL points to an attacker; toolchain changed | `pin: …` |
| N1e, N1r | `lean-toolchain` in `formal/scripts/` or at the repository root | `forbidden` |
| **N2** | `formal/scripts/hashlib.py` (trust2.opus N2) | `unpinned: formal/scripts/hashlib.py` |
| N2m | `lock.py` modified | `pin: formal/scripts/lock.py` |
| N2p / N2p-ref / N2p-self | `lock.py` modified **and** pins rewritten by the attacker; checked with the trusted gate / the trust-ref gate / the attacker's own gate | `pin` / `trustref` / **PASS (documented: self-verification is no defence)** |
| N2c, N2s | committed `__pycache__/*.pyc`; `lint.py` replaced by a symlink to an identical copy | `forbidden`; `git: symlink` |
| **N3** | `formal/json.py` (trust2.opus N3) | `python: formal/json.py` (and `zone`) |
| N3r, N3s, N3c, N3p, N3n, N3v | root `json.py`; `scripts/json.py`; `sitecustomize.py`; `code/evil.pth`; `_json…so`; `.python-version` | `forbidden` / `unpinned` |
| X1, X2, X3 | `.envrc`; `.gitattributes`; submodule | `forbidden`; `forbidden`; `git: submodule` |
| X4, X5, X6, X7 | extra workflow; `.claude/settings.local.json` hook; nested `formal/.claude`; `.vscode/tasks.json` (`runOn: folderOpen`) | `unpinned` / `forbidden` |
| X8, X9, X10 | local `post-checkout` hook; `core.fsmonitor`; `filter.x.clean` | `githook`; `gitconfig` |
| X11 | uncommitted edit of `formal/EG.lean` (strict) | `modified` |
| X12, X13, X22 | non-ASCII name; `formal/EG/run.sh`; FIFO | `names`; `zone`; `special` |
| X14, X15, X16, X18 | TRUST.md pin edited; comparator config allows `sorryAx`; new red-team fixture; `release.yml` without the gate step | `pin` / `unpinned` |
| X17, X20, X21 | `mise.toml`; `.mcp.json`; `go.work` | `forbidden` |
| X19 | `formal/.lake` present in strict mode | `untracked: formal/.lake: Lake directory present` |

**`--demo`: the vectors are real.** Each demo ran in its own temporary directory:
* **N1.** `lake env true` next to `lakefile.toml` and the fixture `lakefile.lean` printed
  `using lakefile.lean` and ran its `#eval`: the marker file was written.
* **N3.** `python3 -c 'import json'` imported the repository `json.py`. With `-I`, it did not.
* **N2.** `python3 scripts/lock.py files` with `scripts/hashlib.py` present did not import it,
  because of the `-I` re-exec guard. The same `lock.py` with the guard removed imported it.

## 3. Workflows

### `ci.yml` (regression guard)

1. `actions/checkout` with `fetch-depth: 0`.
2. **Gate plus snapshot** (`--link-lake`). If `EG_TRUST_REF` is set, the gate comes from that ref
   with `--trust-ref`.
3. Gate red-team (pure sh).
4. elan and Lean install, then the actions/cache restore.
5. From the snapshot:
   * `lock.py files`, the first Python call;
   * `lake exe cache get`;
   * `check_pins`;
   * `lint --self-test` and `lint`;
   * `redteam/tooling`;
   * the toolchain fingerprint.
6. **Build**, in the checkout.
7. **Gate again**: `--allow-build` on the checkout, `--verify-snapshot`, and the toolchain
   fingerprint. This replaces the old `git diff` / `git status` check, which could not see ignored
   files.
8. From the snapshot:
   * `check_pins`;
   * Axioms + MetaScan;
   * **`FinalCheck --scan-only --allow-sorry --policy-roots EG,EGTest,EGCheck`** (fable §8.4);
   * **`STATEMENT.md` regeneration and diff** (fable §5, opus §4.2);
   * `lock check`;
   * `status --check`;
   * `leanchecker`.
9. The in-band Final check (`continue-on-error`).
10. **The slow red-team suites** (fable §8.4). They run on the weekly schedule, on dispatch, or when
    `scripts/`, `redteam/`, `comparator/`, the lake files, `Final.lean`, `TRUST.md`, `STATEMENT.md`
    or `.github/` changed:
    * `redteam/external/redteam.sh` under `sudo`, which it needs for its read-only bind mount;
    * `comparator.sh tools`, then `redteam/bridge/run.sh` with `RT_DIR=$(mktemp -d)`, which fixes
      fable's fixed-`/tmp` note.

    Both run from the checkout, not the snapshot. A snapshot made with `--link-lake` would let the
    external harness write through symlinks into the real `EGCheck/`. The checkout was re-verified
    by the gate in step 7.

### `release.yml`

**`build` (untrusted).** Gate first. It is not a trust boundary here; it only makes a bad tree fail
early. Otherwise unchanged.

**`verify` (trusted).**
1. Memory preflight, then checkout.
2. **Gate plus snapshot** (plain `.lake` directory; optional trust ref).
3. elan install.
4. Every later step runs in `$RUNNER_TEMP/trusted/formal`:
   * **`python3 -I scripts/lock.py files --strict`**, the first Python call (opus §7.2);
   * cache get;
   * pins;
   * lint `--release`;
   * tooling red-team;
   * build FC 184 from source;
   * **`STATEMENT.md` regeneration and diff**;
   * artifact install, with the tar validator run as `python3 -I`;
   * `lock check --strict`;
   * Axioms;
   * status;
   * FinalCheck;
   * leanchecker;
   * leanchecker `--fresh`.

**`comparator` (trusted).**
1. Gate plus snapshot, then elan install.
2. **`scripts/comparator.sh tools $RUNNER_TEMP/comparator-tools`**. This builds the patched, pinned
   v4.33.1 comparator with lean4export `66f1fb4b` and landrun `811cfff5`. It replaces the old
   unpatched v4.35.0-rc3 build with lean4export `15f6055e`.
3. Cache get, then pins.
4. **`comparator.sh check`**. It uses the correct `comparator/Challenge.lean` path; the old step
   hashed a nonexistent `formal/Challenge.lean`.
5. **`comparator.sh run --release --system-unit --tools …`**.

Until `staging/lakefile.toml.proposed` is applied, `comparator.sh run` refuses to start
("lakefile.toml has no Challenge/Solution lean_libs"), so the job fails closed.

The removed env variables (`COMPARATOR_REV`, `LEAN4EXPORT_REV`, `LANDRUN_REV`, `COMPARATOR_CONFIG`)
now live only in `comparator.sh`.

**Not verifiable here** (no push is allowed):
* Neither workflow has run on GitHub.
* Untested on a runner: `sudo redteam/external/redteam.sh`, the read-only snapshot files together
  with `lake build`, and `systemd-run`/landrun.
* Go comes from the runner image and is not pinned. landrun needs Go ≥ 1.24, and the job prints
  `go version`.
* Runs as they should: `lake env`, FinalCheck, Statement, lint and lock from a snapshot, which I
  measured locally.

### Manual release audit

This replaces the first lines of the recipe in `work/trust/tooling.md`. Use a fresh clone, and run
nothing else before the gate:

```
T=$(mktemp -d); git clone <repo> "$T/B"; cd "$T/B"
git show "$EG_TRUST_REF:formal/scripts/pristine.sh" > "$T/gate.sh"   # or: sha256sum-compare the tree copy with TRUST.md
sh "$T/gate.sh" --trust-ref "$EG_TRUST_REF" --snapshot "$T/trusted"
cd "$T/trusted/formal"; export PATH=$HOME/.elan/bin:$PATH
python3 -I scripts/lock.py files --strict
lake exe cache get && ./scripts/check_pins.sh && scripts/comparator.sh check
python3 -I scripts/lint.py --self-test && python3 -I scripts/lint.py --release && redteam/tooling/run.sh
lake build 'FormalConjectures.ErdosProblems.«184»'
lake env lean --run scripts/Statement.lean "$T/S.md" && diff -u STATEMENT.md "$T/S.md"
# then: install the untrusted build's EG*/EGTest*/EGCheck* .oleans into .lake/build/lib/lean, and run the
# release.yml verify steps; comparator: scripts/comparator.sh tools DIR && scripts/comparator.sh run --release --tools DIR
```

Do not run the audit inside an agent that loads repository config. The gate rejects `.claude/`
additions, `.mcp.json` and nested `.claude/` directories, but a plain shell is the safe setting.

## 4. What remains and what the integrator must do

1. **Pins go stale** whenever a trusted-zone file changes. Other agents are editing
   `scripts/FinalCheck.lean` (N4), `TRUST.md.proposed` and `EG/Defs` concurrently.
   * At each approval, run `sh formal/scripts/pristine.sh --write-pins`, review the diff of the pin
     block, and put the resulting `sha256sum formal/scripts/pristine.sh` into TRUST.md (proposed
     §2 item 8). Then run `lock.py update` and move `EG_TRUST_REF`.
   * The same applies when applying `staging/{Final.lean,TRUST.md,lakefile.toml}.proposed`.
   * Current gate SHA-256: `12a7eb969f635211c86dfdc95a403ff1b6741799ec09197d8f62b5b19032d6de`, with
     100 pins, of this working tree at the time of writing.
2. **`lock.py files --strict`** in `verify` fails until `lock.py update` is run: 108 files are
   pending today. This is fail-closed, as before.
3. **Set the repository variable `EG_TRUST_REF`** to the approved trust commit or tag. Without it, CI
   and release run the checkout's own gate. That still catches N1–N3 in an unmodified pipeline, but
   an attacker who rewrites the pins and the workflow together is caught only by the offline check
   (N2p-self).
4. **Merge `staging/TRUST.md.gate.md`** into `TRUST.md.proposed` (owner: the TRUST agent).
   * It adds the gate and the release-commit files to the trusted list.
   * It adds GitHub runners and the artifact store, which opus §4.1 items 1 and 2 ask for.
   * It updates the comparator command in §4.
   * CODEOWNERS already covers `scripts/`, `redteam/` and `.github/`.
5. **Not closed by the gate:**
   * A malicious `.olean` loader exploit (fable §4.2).
   * Build-time IO in the untrusted build. The release job separation handles this, and CI is
     regression-only.
   * N4 and N6, which are FinalCheck's replay set and are owned elsewhere.
   * Anything that the pinned upstream packages (Mathlib's `lakefile.lean`, the cache tool) run.
     That is trusted under TRUST.md §2 item 6.
