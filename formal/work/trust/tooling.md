# Trust hardening — tooling (agent id: `tooling`, 2026-09-26)

Response to the two trust audits (`APPROVALS/reviews/trust.opus.md`, `trust.fable.md`). This agent owns the
checkers; the acceptance criterion itself (TRUST.md, `EGCheck/Final.lean`, `scripts/FinalCheck.lean`,
comparator layout) belongs to other agents and to the user.

No protected file was touched (TRUST.md, `EGCheck/Final.lean`, lake files, `lean-toolchain`, `.claude/**`).
No git command that modifies the repository was run. `lock.py update` was NOT run. Attack fixtures live only in
`formal/redteam/tooling/` (no `lean_lib` builds it) and in the scratchpad under `/tmp`.

## Files changed

| File | Change |
|---|---|
| `scripts/Axioms.lean` | New independent axiom walk (replaces per-constant `collectAxioms`, 12× faster, identical results) and a lint-independent **MetaScan** (always on). New flag `--cross-check`. |
| `scripts/lint.py` | Rewritten around a Lean tokenizer; many new rules; `--self-test` (59 cases); file arguments. |
| `scripts/check_pins.sh` | Lean binary commit, lakefile/manifest revs, every package HEAD + clean worktree, no extra packages, FC's toolchain and manifest, blob ids, Mathlib tag. |
| `scripts/lock.py` | Only `PROTECTED_FILES`: adds `CONVENTIONS.md`, `status/ratchet.json`, `../.claude/settings.json`, `../.github/CODEOWNERS`, and — expanded at run time — `scripts/**`, `redteam/tooling/**`, `../.github/workflows/**`. |
| `.github/workflows/ci.yml` | Pinned tools (elan release + Lean archive by SHA-256, actions by commit SHA); pins/lint/red-team BEFORE the build; pristine snapshot; post-build integrity check; scans from the snapshot; non-fresh `leanchecker`. |
| `.github/workflows/release.yml` | New. Three jobs: untrusted `build` → trusted `verify` (separate runner, never runs project code) and `comparator`. |
| `redteam/tooling/run.sh`, `redteam/tooling/RT/*.lean` | New. 14 Init/Lean-only fixtures with an expected-verdict table for Axioms (dev / `--no-sorry`), lint (dev / `--release`) and `leanchecker`. Runs in CI and release. |

## 1. `scripts/Axioms.lean`

### Independent axiom walk
* It walks the kernel `ConstantInfo`s of the loaded environment: the types and values of every reachable
  constant. An inductive type is merged with its constructors and its mutual block, so the graph is acyclic
  (checked: no cycle over the whole closure; a cycle would stop the run with exit code 2).
* Results are memoised across constants, and the DFS is iterative (no stack overflow).
* A reference to a constant missing from the environment is reported as the pseudo-axiom
  `«missing constant».X`, which is a violation.
* **Correction to trust.opus §4.2.** Under `lean --run` with `importModules` (`loadExts := false`), the
  `exportedAxiomsExt` state is never populated. So the old `collectAxioms` call did *not* trust the per-module
  `.olean` tables. It re-walked the whole closure for every constant, which is why it took 3 min.
  * The new walk does not depend on that detail.
  * `--cross-check` runs `collectAxioms` too and flags any axiom it reports that the walk missed.
* **Verified.** The per-constant axiom sets match the old script on all 1530 constants of
  EG/EGTest/EGCheck (JSON diff: 0 differences).
  * Time: 3:03 → 0:15.
  * Maximum RSS: 8.5 GB in both, mostly mmapped `.olean` files.

### MetaScan (always on; exit 1 on a hit)
* **Per constant.** A constant is a hit if its **type** mentions any of: `Lean.Elab`, `Lean.Meta`,
  `Lean.Macro(M)`, `Lean.(T)Syntax`, `Lean.Parser`, `Lean.(Trailing)ParserDescr`, `Lean.PrettyPrinter`, `IO`,
  `EIO`, `BaseIO`, `ST`, `EStateM`, `unsafe*IO`, `Lean.Environment`, `Lean.Kernel`, `Lean.Core(M)`, `Lean.Expr`,
  `Lean.Declaration`, `Lean.ConstantInfo`, `Lean.Options`, `Lean.KVMap`, `Lean.MessageData`, `Lean.Exception`,
  `Lean.*EnvExtension`, `Lean.KeyedDeclsAttribute`, `Lean.AttributeImpl`, `Lean.AttrM`, `Lean.ImportM`,
  `Lean.Compiler`, `Lean.IR`, `Lean.Server`, `Lean.Widget` or `Lean.Linter`.
  * For a `def` or `opaque`, the same test applies to the **value**.
  * Also a hit: marked `meta`, `[init]`/`[builtin_init]`, `@[export]`.
  * Also a hit: declared under `Erdos184`, `FormalConjectures*` or `SimpleGraph.IsDecomposition`, or with an
    `Erdos184` name component anywhere (attacks C and B0).
* **Per module.** A module is a hit if its `.olean` has entries for any of these environment extensions:
  command, term, tactic, do-element, inductive and grind elaborators; macros; the parser extension (`syntax`,
  `notation`); delaborators and unexpanders; init and builtin_init; csimp; implemented_by, extern and export;
  simprocs; code actions; RPC; the module system's `metaExt`/`declMetaExt`; widgets. This catches
  `attribute [...]` applied to foreign constants.
  * Also a hit: any `meta import` other than the implicit `Init`, or an `EG*`/`EGTest*` module importing
    `FormalConjectures*`.
  * The extension names are checked against the toolchain's registry at start-up. A renamed extension stops
    the run with exit code 2; it is never skipped silently.
* **No imported code runs.** `loadExts := false`; only ConstantInfos and raw `.olean` entries are read.
* **0 false positives on the current tree.** 1530 constants, 0 hits, 0 violations. This also holds on the
  byte-identical `Final.lean` (the `run_cmd` leaves only `EGCheck.erdos_184`) and on `deriving Repr/DecidableEq/
  Inhabited/BEq/Hashable`, `instance ToString`, and `omega`/`decide` inside definitions.
* **Consequence for provers: no notation.** Even a `local notation` leaves a `meta` macro and a `ParserDescr`
  constant, and MetaScan rejects both (fixture `Notation`). Lint now rejects notation too. The tree uses none.

## 2. `scripts/lint.py` (hygiene, not the guarantee — its docstring says so)
* **Tokenizer**, based on Lean's lexical rules. It handles:
  * nested block and doc comments, and line comments;
  * strings with escapes;
  * **interpolated strings**: after `s!`, `m!`, `f!`, `throwError`, `trace[..]`, …, the `{code}` parts are
    lexed as code;
  * raw strings `r#"…"#`;
  * **character literals** (`'"'`, `'\''`);
  * identifiers with `'`, `!` and `?`;
  * `«»` components, normalised (`«debug».skipKernelTC` → `debug.skipKernelTC`).

  The words inside every string literal are also checked, so a mis-classified string cannot hide a forbidden
  word. Tested on 1962 upstream files (FC, `Mathlib/Combinatorics`, `Mathlib/Tactic`): 0 tokenizer errors,
  4.5 s. On the project tree it runs in 0.3 s.
* **Rules.**
  * `axiom` as a token (at end of line, after `@[simp]`, `private`).
  * `admit`, `native_decide`, `native` (`decide +native` / config), `bv_decide`, `implemented_by`, `extern`,
    `unsafe`, `opaque`.
  * `ofReduceBool/Nat`, `trustCompiler`, `debug.*`.
  * `skipKernelTC` in any spelling, including inside strings.
  * `addDecl*`, `addAndCompile`, `modifyEnv`, `setEnv`.
  * `run_cmd`, `run_elab`, `run_meta`, `run_tac`, `by_elab`.
  * `#eval` and `#eval!` everywhere.
  * `#guard` except under EGTest. It evaluates a closed `Bool`, which cannot do IO without the forbidden
    `unsafe`/`implemented_by`/`extern`.
  * `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `declare_syntax_cat`, `initialize`,
    `builtin_initialize`, simprocs, `register_option`, and more.
  * `meta` (covers `meta def` and `meta import`).
  * Meta attributes in `@[..]` and `attribute [..]` (with `local`/`scoped` and `-`): `command_elab`,
    `term_elab`, `tactic`, `csimp`, `init`, `macro`, `delab`, `app_unexpander`, `export`, `norm_num`,
    `positivity`, `builtin_*`, `*_elab`, `*_parser`, and more.
  * Meta-programming identifiers: `Lean.Elab.*`, `CommandElabM`, `MetaM`, `IO`, `getEnv`, `withOptions`,
    `mkConst`, `throwError`, and more.
  * Notation of any kind.
  * **`set_option` allowlist:**
    * `maxHeartbeats N` and `*.maxHeartbeats N` with 0 < N ≤ 10⁶;
    * `maxRecDepth`;
    * `synthInstance.*`, `linter.*`, `pp.*`.
  * **`import` of `FormalConjectures*` outside EGCheck**, checked on every `import` token (fixes L6).
  * **Upstream names.** `Erdos184` may not appear in EG/EGTest. Nothing may be declared with an `Erdos184`
    component, and no `namespace Erdos184` may be opened (catches attack C with no meta code at all).
  * **Release mode:** `sorry`, `sorryAx`.
* **`EGCheck/Final.lean` allowlist.** Only the categories "run_cmd/run_elab/run_meta" and "meta-programming
  identifier" are allowed there. The current file and a plausible hardened version (upstream import first,
  `_root_`, provenance check in `run_cmd`) both lint clean.
* **Current tree: 0 findings.** In release mode it gives 3 findings: the known `sorry`s in `EG/Proof/Main`,
  `EG/Proof/Ext/BMLemma25` and `EGCheck/Smoke`.
* **Reviewer fixtures.** Every fixture file of both audits gets a substantive finding. That covers the
  scratchpad copies of `lt*`, `lintroot*` t1–t10, A, B, C, D, D′, E, M, atk1–4, atk6, `Evasions2`, `Char`,
  `Native` and `Bypass*`. Previously most of them got 0 findings.

## 3. `scripts/check_pins.sh`
It now checks all of the following:
* `lean-toolchain`;
* `lean --githash` and `lean --version` against `819816b2…`;
* the lakefile FC `rev` and mathlib `rev` (tag);
* the manifest's FC rev, mathlib rev and mathlib `inputRev`, and that `packagesDir` is `.lake/packages`;
* **for every manifest package** (git type only): HEAD equals the manifest rev, and
  `git status --porcelain --untracked-files=all` is empty, ignoring the package's own `.lake/`;
* that no package directory is missing from the manifest;
* FC's `lean-toolchain`, FC's manifest mathlib rev, and every rev FC's manifest shares with ours;
* for 184.lean and Decomposition.lean: SHA-256, blob id in the worktree, blob id in HEAD;
* that the Mathlib tag `v4.33.1` points at HEAD.

Results:
* **Current tree:** all pins ok, 0.7 s.
* **Negative tests** (scratch root with the opus tampered clones): the modified `Subgraph.lean` and
  `FormalConjecturesUtil.lean` are caught (as "worktree not clean"), as are a tampered lakefile FC rev and an
  extra package directory.
* **Not covered** (documented in the script): whether the `.olean`s match these sources. That is the job of
  FinalCheck's closure-hash pin, `leanchecker --fresh` and comparator.

## 4. `scripts/lock.py`
* Only the `PROTECTED_FILES` list changed (see the table above).
* `lock.py check` currently gives 0 violations and 15 **PENDING** new files. It passes in non-strict mode.
* **Integrator:** run `lock.py update --approval …` once the new scripts and workflows are approved; after
  that, `--strict` passes.

## 5. CI (`.github/workflows/ci.yml`) and release (`.github/workflows/release.yml`); both pass `actionlint`

**Pins used by both workflows:**
* Actions by commit SHA: checkout v7.0.1 `3d3c42e5…`, cache v6.1.0 `55cc8345…`, upload-artifact v7.0.1
  `043fb46d…`, download-artifact v8.0.1 `3e5f45b2…`.
* elan v4.2.4 release tarball, SHA-256 `42b94d42…`. This replaces the unpinned `curl elan-init.sh` from
  `master`, which also installed the "latest" elan.
* The Lean v4.33.1 archive, SHA-256 `890afd18…`, extracted into elan's toolchain directory. I checked that
  elan uses a pre-populated directory as is, and that the archive's `lean` is byte-identical to the local
  toolchain, githash `819816b2…`.

**CI order:**
1. Before any project code runs: pins, `lint --self-test`, lint, red-team fixtures.
2. A pristine snapshot, `$RUNNER_TEMP/pristine/{formal,.github,.claude}`:
   * copies of `scripts/`, `LOCK.json`, TRUST.md, CONVENTIONS.md, the lake files, `lean-toolchain`,
     `status/` and `redteam/`;
   * symlinks to EG, EGTest, EGCheck, the root files and `.lake`;
   * a SHA-256 fingerprint of `~/.elan`.
3. `lake build`.
4. Checks that the build changed nothing: `git diff --exit-code`, an empty
   `git status --porcelain --untracked-files=all`, the toolchain fingerprint, and `check_pins` again.
5. From the pristine copy: Axioms + MetaScan, `lock.py check`, `status.py --check`, and
   `leanchecker EG EGTest EGCheck` (non-fresh).
6. The in-band `Final` check, with `continue-on-error`.

I verified locally that `lake env`, `lock.py`, `status.py` and `Axioms.lean` work from such a symlink tree:
lock 0 violations, status unchanged, 0 meta hits.

* **Cost of non-fresh `leanchecker`** (measured on this loaded machine, `LEAN_NUM_THREADS=2`): 10 min 34 s wall
  time, 10.2 GB maximum RSS, exit code 0, so today's tree replays clean. It is affordable next to the build.
  Most of the RSS is mmapped `.olean`s, but on a 7–8 GB private-repository runner it may be tight.
* **Limit (stated in the file header).** Regular CI runs its checks on the runner that just executed project
  code, and a build-time adversary with the runner's sudo can defeat any in-VM check. CI is a regression guard;
  `release.yml` is the acceptance criterion.

**`release.yml`** runs on `workflow_dispatch` and on tags `formal-v*` / `release-*`.
* **`build` (untrusted).**
  1. Pinned toolchain, Mathlib cache and pins.
  2. A fresh `lake build EG EGTest EGCheck EGCheck.Final`. No `actions/cache` is used.
  3. Uploads only `.lake/build/lib/lean/{EG,EGTest,EGCheck}*`, which is about 18 MB today.
* **`verify` (trusted, separate VM; it never compiles or runs project code).** It runs these checks, in order:
  1. A memory preflight: it fails early if the runner has less than 16 GB.
  2. The pinned toolchain, the Mathlib cache and the pins.
  3. `lint --self-test` and `lint --release`.
  4. The red-team fixtures.
  5. **`lake build 'FormalConjectures.ErdosProblems.«184»'` from pinned sources, before any artifact exists.**
  6. The artifact:
     * its tar member names are validated (only `EG*`/`EGTest*`/`EGCheck*`, no `..`, only files and
       directories);
     * it is extracted into an empty `.lake/build/lib/lean`.
  7. The scans over the artifact:
     * `lock.py check --strict`;
     * `Axioms.lean --no-sorry --cross-check` on `EG EGTest EGCheck EGCheck.Final`;
     * `status.py --check`;
     * `lean --run scripts/FinalCheck.lean` (strict, pins from TRUST.md);
     * `leanchecker EG EGTest EGCheck`;
     * `leanchecker --fresh EGCheck.Final`.
  * The runner is `${{ vars.EG_RELEASE_RUNNER || 'ubuntu-latest' }}`. Standard private-repo runners are
    below 16 GB: set the variable to a larger runner or use the manual fallback below.
* **`comparator` (trusted harness).**
  1. It fails unless `formal/comparator/config.json` exists. The Challenge/Solution layout is still to be
     designed (trust review §6; bridge agent).
  2. It builds the checkers at pinned commits:
     * landrun `811cfff5…` (`go install`);
     * lean4export tag v4.33.0 `15f6055e…`, **built with the toolchain overridden to v4.33.1**, because it
       must read v4.33.1 `.olean`s;
     * comparator `fd5d5bcf…`, built with its own toolchain, v4.35.0-rc3.
  3. `lake exe cache get` (allowed by comparator's README) and pins.
  4. The Challenge must be either the pinned FC module itself or a file with the SHA-256 of `184.lean`.
  5. The config must satisfy all of the following:
     * `theorem_names == ["Erdos184.erdos_184"]`;
     * the permitted axioms are exactly the three;
     * there are no definition holes.
  6. It runs comparator unprivileged through
     `sudo systemd-run --uid=<runner> --property=RestrictAddressFamilies=~AF_UNIX`, as its README requires.
     No project code is compiled before comparator runs.

**Untested on GitHub** (no push was allowed):
* the whole of `release.yml`;
* landrun/Landlock on GitHub's kernel;
* `systemd-run` on the runner;
* building lean4export v4.33.0 with v4.33.1.

These must be exercised in the planned comparator dry run (trust review §6).

### Manual release audit (fallback for a ≥ 16 GB cloud session)
It runs the same commands as the `verify` job, in a **fresh clone**. The artifact separation is replaced by
"build in one clone, verify in another".

```
git clone <repo> A && git clone <repo> B      # A: untrusted build, B: verification
export PATH=$HOME/.elan/bin:$PATH             # toolchain v4.33.1, githash checked by check_pins
(cd A/formal && lake exe cache get && lake build EG EGTest EGCheck EGCheck.Final)
cd B/formal && lake exe cache get && ./scripts/check_pins.sh
python3 scripts/lint.py --self-test && python3 scripts/lint.py --release && redteam/tooling/run.sh
lake build 'FormalConjectures.ErdosProblems.«184»'          # before copying anything from A
mkdir -p .lake/build/lib/lean && (cd ../../A/formal/.lake/build/lib/lean && tar -cf - EG EG.* EGTest EGTest.* EGCheck EGCheck.*) | tar -xf - -C .lake/build/lib/lean
python3 scripts/lock.py check --strict
lake env lean --run scripts/Axioms.lean --no-sorry --cross-check --prefix EG --prefix EGTest --prefix EGCheck EG EGTest EGCheck EGCheck.Final
python3 scripts/status.py --check
lake env lean --run scripts/FinalCheck.lean
lake env leanchecker EG EGTest EGCheck
/usr/bin/time -v lake env leanchecker --fresh EGCheck.Final   # ~21 min, ~10.2 GB RSS (trust.opus §3.3)
# plus comparator, as in release.yml's comparator job, in a third fresh clone
```
The build in A runs project code as the session user. Use separate users or VMs if a hostile build is part of
the threat model.

## 6. Red-team regression (`formal/redteam/tooling/run.sh`)
* It compiles 14 fixtures (Init/Lean only) into a temporary directory.
* It checks each verdict against the table below.
* All verdicts match. The full run takes 2.6 min.

| fixture | Axioms | Axioms `--no-sorry` | lint | lint `--release` | leanchecker |
|---|---|---|---|---|---|
| CmdElab (B1), TermElab (A1), PrintAxioms (A/A3), MacroRules, ModHook (M), Init, CSimp, Fake (C), Notation, Axiom | catch | catch | catch | catch | miss |
| Bypass (D: `elab` + skipKernelTC `addDecl`) | catch | catch | catch | catch | catch |
| RunTac (D′: `run_tac` bypass, no meta constant left) | **miss** | **miss** | catch | catch | catch |
| Sorry (`sorryAx` spelled out) | miss | catch | miss | catch | miss |
| Benign | miss | miss | miss | miss | miss |

**Scratch fixtures of both reviewers, run through the new Axioms.lean:**
* **Caught:** A, B1, C, D, M, atk1, atk2 (`EGCheck.Erdos184.erdos_184`), atk3, atk6.
* **Missed by design, as expected:**
  * F/RunTac (D′) and atk4 (`#eval addDecl` with an honest type): caught by lint and by kernel replay.
  * E (`#eval` IO): caught by lint only.
  * atk2b (`export` alias into `namespace Erdos184`): aliases are not constants, so MetaScan misses it. Lint
    flags `namespace Erdos184`, and the attack fails at elaboration anyway.

## 7. Residual gaps and notes for the integrator
1. **What only the release can catch.**
   * Build-time IO that leaves no trace (fixture E) is caught only by lint and by the job separation in
     `release.yml`.
   * A kernel bypass with a meta-free result (D′, atk4) is caught only by kernel replay (`leanchecker`,
     FinalCheck's replay, comparator).
2. **The `verify` job still loads untrusted `.olean`s into a process** (mmap). A crafted `.olean` exploiting
   the loader is outside what `leanchecker`, FinalCheck or Axioms can rule out. Comparator (sandboxed build,
   lean4export, ndjson) covers this, which is why it is a required job.
3. **Remaining trust in downloads.**
   * The Mathlib cache (`lake exe cache get`) is still trusted. TRUST.md should say so, or the release could
     build Mathlib from source.
   * elan fetches comparator's own toolchain (v4.35.0-rc3) without a hash pin. Pin it once the dry run works.
4. **Policy changes that provers will notice.** AGENTS.md rule 2 should list them (AGENTS.md is not mine):
   * no notation of any kind, not even `local`;
   * no `#eval`, and `#guard` only in EGTest;
   * the `set_option` allowlist;
   * no meta-programming identifiers;
   * no `Erdos184` in EG/EGTest.
5. **`lock.py update`** is needed for the 15 new protected files (item 4).
6. **Suggested for the `.claude/settings.json` deny list, at the freeze:** `scripts/**`, `redteam/tooling/**`,
   `.github/**`. This is not needed for soundness, because the lock and CODEOWNERS cover them.
7. **TRUST.md "How to check"** (owned by the TRUST/bridge work) should name `release.yml`'s `verify` and
   `comparator` jobs as the criterion. It should also list the pinned checker versions above and the runner
   RAM requirement.
8. The `lakefile.toml` comment still says `scripts/lint.sh` (cosmetic; it is a protected file).
