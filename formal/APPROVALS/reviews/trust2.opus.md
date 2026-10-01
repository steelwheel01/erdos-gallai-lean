# Independent re-audit of the hardened trust setup (opus)

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent re-auditor.

**Scope.** I evaluated the setup as if `staging/Final.lean.proposed`, `staging/TRUST.md.proposed` and
`staging/lakefile.toml.proposed` had been applied. I applied them only in temporary copies, never in
the repository.

**What I read.**
* The two earlier audits: `trust.opus.md` and `trust.fable.md`.
* The three hardening reports: `work/trust/{tooling,bridge,external}.md`.
* The staged proposals.
* The scripts: `FinalCheck.lean`, `Statement.lean`, `check_pins.sh`, `comparator.sh`, `lock.py`,
  and `lint.py` (usage only).
* The workflows: `.github/workflows/{ci,release}.yml`.
* The comparator sources and their patch, `comparator/*`, and `STATEMENT.md`.
* Lean v4.33.1 sources: `Environment.lean` (import/merge), `Replay.lean`, `LeanChecker.lean`,
  `AddDecl.lean`.

**What I changed.**
* This file is the only repository file I wrote.
* I ran no git command that modifies anything.
* All fixtures live in the scratchpad:
  `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/r2o/`
  (called `$R` below).
* The external harness kept its own copy in `/tmp/rt-external.z5YREc/`.

## Verdict: REJECT (targeted; the fixes are small)

**What works.** The design of the proposed acceptance criterion is right. It rests on three checks:
* comparator against a byte-identical Challenge;
* `leanchecker --fresh`;
* an `importModules`-based statement/axiom check.

Every attack from the two earlier audits is caught out-of-band, and I re-ran all of them myself
(§1).

**What fails.** The criterion, as specified in TRUST.md.proposed and implemented in `release.yml`
and `scripts/`, can still be defeated completely, with no Lean proof code at all:

* **N1.** A new file `formal/lakefile.lean` is elaborated by *every* `lake` invocation of the
  trusted jobs. Lake prefers it over `lakefile.toml`.
  * I measured this: `lake env lean --run scripts/FinalCheck.lean` printed
    `FINALCHECK: PASS` with no project `.olean` present at all.
  * `check_pins.sh`, `lint.py` and `comparator.sh check` all passed.
* **N3.** A new file `formal/json.py` shadows the Python standard library inside `check_pins.sh`,
  `comparator.sh check` and the inline Python steps of `release.yml`. That is arbitrary code in the
  trusted jobs, outside any sandbox. Measured.

Neither file is covered by `lock.py`, `lint.py` or `check_pins.sh`. Because every checker, comparator
included, is started through `lake env` or after these steps, **comparator and
`leanchecker --fresh` do not cover N1 or N3**.

**Other findings.**
* `scripts/FinalCheck.lean` has a real soundness bug (**N4**, measured): strict mode passes a
  "proof" of `Erdos184.erdos_184` from a declaration the kernel never checked. Non-fresh
  `leanchecker` catches it; by design so do `leanchecker --fresh` and comparator (§3).
* `release.yml`'s comparator job does not implement what TRUST.md.proposed pins (§4.2).

## 1. Re-run of the attacks from both earlier audits

**Harnesses I re-ran myself on this tree:**

| Harness | Result |
|---|---|
| `redteam/external/redteam.sh --keep` | `REDTEAM: PASS`; all 18 verdicts as documented |
| `redteam/tooling/run.sh` | 14/14 verdicts as expected |
| `redteam/bridge/run.sh --tools /root/tools` | comparator: honest run accepted; F1–F5 rejected with the documented messages |

In the table below:
* "FC" = `scripts/FinalCheck.lean` (strict);
* "lc" = non-fresh `leanchecker`;
* "lc-fresh" = `leanchecker --fresh EGCheck.Final`;
* "cmp" = comparator.
* "(design)" marks a verdict that follows from how the checker works and was not measured by me.
* In-band verdicts for `Final.lean.proposed` are the bridge agent's measurements, checked against
  the file's text.

| Attack (origin) | In-band, **proposed** Final | lint | Axioms / MetaScan | FC | lc | lc-fresh | cmp |
|---|---|---|---|---|---|---|---|
| A / A3: spoofed `#print axioms` with a `sorryAx` proof | spoofable (advisory) | catch | catch | **catch** (axioms: sorryAx) | miss | miss | catch (F-suite; design) |
| A1 / B1: `type_of%` or `run_cmd` elaborator hijack | spoofable | catch | catch | **catch** (statement ≠ upstream) | miss | miss | catch (F2) |
| A2 / B0: `EGCheck.Erdos184.erdos_184` shadow | **catch** (`_root_`) | catch | catch | n/a | – | – | – |
| A2b: `export` alias | catch (elaboration) | catch | – | – | – | – | – |
| C: fake `Erdos184.erdos_184` in Bridge | **catch** (import clash) | catch | catch | **catch** (import clash) | miss | miss | catch (F5 clash) |
| A4 / D: kernel bypass via `#eval`/`elab` + `skipKernelTC` | spoofable | catch | D catch, A4 miss | **catch** (replay) | catch | catch (measured by external and opus-1) | catch (F3) |
| D′: `run_tac` bypass | spoofable | catch | miss | catch (design: same replay path as A4) | catch | catch | catch |
| E / IO: build-time IO | n/a | catch | – | miss (by design) | – | – | sandboxed; `release.yml` job separation |
| t1–t9 / L1–L6: lint evasions | – | catch (self-test, fixtures) | catch or miss per table | catch except t4 (benign) | – | – | – |
| Tampered package worktree (opus-1 §2.2) | – | – | – | catch (`oleans`, pins) | – | – | – |

In this table `check_pins.sh` also catches the tampered package worktree (tooling measurement).

**Also verified independently:**
* **Proj-only structures in the closure.** Canon's `deps` and `reachableAxioms` use v4.33.1
  `getUsedConstants`, which skips `Expr.proj` structure names (the comparator issue-68 behaviour). I
  measured that all 129 structures that appear as a `proj` in the pinned 1572-constant statement
  closure are already in the closure (`$R/ProjClosure.lean`). So the pin is not weakened today.
  Hygiene recommendation: use the proj-aware fold of the comparator patch.
* **Challenge elaboration matches upstream.** Comparator's `Challenge` is built with the project's
  `leanOptions` (`maxSynthPendingDepth = 3`, which formal-conjectures does not set). Compiled that
  way, `Erdos184.erdos_184` and `Erdos184.IsCycleOrEdge` are identical to the upstream-built
  constants up to binder names, which is what comparator's `eqv` compares (`$R/chal/Cmp.lean`).
  The Challenge therefore means the pinned statement.
* **Pins cross-check.** The STATEMENT.md pins equal the TRUST.md.proposed pins. The `dbgToString`
  hash `33e21327…` equals the value in the first opus audit. Mathlib here was built from source
  (STATE.md), so the closure pin really is tied to sources. TRUST.md should say this (§4.3).

## 2. New attacks

### N1. `formal/lakefile.lean` hijacks every `lake` call (MISSED by everything; blocking)

**Mechanism.** Lake 4.33.1 prints `lakefile.lean and lakefile.toml are both present; using
lakefile.lean` and elaborates the `.lean` file on every invocation. Its `#eval` runs as the job's
user.

**Fixture.** `$R/lk/formal/lakefile.lean`: the real lakefile translated to the Lean DSL, plus one
`#eval` that replaces `scripts/FinalCheck.lean` with a stub.

**Results (measured):**
* `./scripts/check_pins.sh`: all pins ok.
* `python3 scripts/lint.py`: 0 findings.
* `scripts/comparator.sh check`: OK.
* `lake env lean --run scripts/FinalCheck.lean`: `FINALCHECK: PASS (0 failures, 0 warnings)`, exit
  0, with **no EG build present**.

**Scope.** The same code runs:
* in `release.yml` `verify`, at `lake exe cache get`: the first step after install, before pins,
  lock or artifact;
* before `lake env leanchecker`, and it can replace the binary in `~/.elan`;
* in the `comparator` job, before and around `lake env comparator config.json`, outside landrun,
  where it can replace `$COMPARATOR_BIN`. Inside comparator's own sandboxed `lake build Challenge`
  it can also redefine the `Challenge` library, which breaks comparator's README assumption 1.

`lock.py` hashes only listed paths, so a new root file is not even PENDING. **Not covered by
comparator or `leanchecker --fresh`.**

### N2. Standard-library shadowing defeats the lock's self-check (measured)

**Fixture.** `$R/py/scripts/hashlib.py`, in a copy where `TRUST.md` and `EGCheck/Final.lean` were
also modified.

**Result.** `python3 scripts/lock.py check --strict` prints a fake "0 violations" and exits 0. The
control (file-hash part without the shadow) reports both changed files and 28 pending files.
`sys.path[0]` is `scripts/`.

**Root cause.** The lock verifies itself. The same holds for any change to `lock.py` or `LOCK.json`
in the commit under test. In `release.yml` the lock runs *after* `lint.py`, `redteam/tooling/run.sh`
(which compiles repository Lean fixtures) and `lake`. So it cannot protect the job that runs it.

### N3. `formal/json.py` runs code in the trusted shell checkers (MISSED; blocking)

**Mechanism.** `python3 -c` / `python3 -` put the current directory first on `sys.path`.

**Fixture.** `$R/lk/formal/json.py`. It re-exports the real `json` and logs every use to
`$R/pwn.txt`.

**Result (measured).** It ran on every Python call inside `check_pins.sh` (16 calls) and inside
`comparator.sh check`, and both still reported OK. `release.yml` has further inline
`python3 -c 'import json…'` steps in the `comparator` job, right before comparator runs.

**Coverage.** Not caught by lint, lock or pins. Not covered by comparator or `leanchecker --fresh`,
because it controls the jobs that run them.

### N4. IR-name attribution theft: strict `FinalCheck` passes on a kernel-unchecked proof (measured)

**Setup.** In `$R/ir/src/EGCheck/`:
* `RTX1` plants an IR-only declaration named `EGCheck.RTX.bogus`, using `#eval` on
  `IR.declMapExt`.
* `RTX2` then adds the kernel constant `EGCheck.RTX.bogus : False := True.intro` without kernel
  checking (the A4 technique), and `EGCheck.RTX.final : False`.
* `Final` proves `type_of% @_root_.Erdos184.erdos_184` from it.

**Why FinalCheck misses it.**
* `finalizeImport` attributes names in `const2ModIdx` with `insertIfNew`, and that includes each
  module's IR `extraConstNames`. So `EGCheck.RTX.bogus` is attributed to `RTX1`, where it is not a
  kernel constant.
* FinalCheck's `projectConstants` keeps only names whose attribution equals the declaring module.
  The bogus constant is therefore **never renamed or replayed**.
* `checkOrigins` counts it as a harmless "duplicate project-internal theorem".

**Result.** The exact release command, `lean --run scripts/FinalCheck.lean` with pins from
`TRUST.md.proposed` and no flags, gives:
* `[PASS]` on every check: lean, import, oleans, origin (with "1 duplicate"), replay, kinds,
  statement, axioms (exactly the three), policy, meta, and both pins;
* `FINALCHECK: PASS`.

The log is `$R/ir/finalcheck.N4.log`.

**Control.** The same module without `RTX1` gives `[FAIL] replay: … declaration type mismatch`.

**Other checkers:**
* `Axioms.lean --no-sorry` and MetaScan: 0 hits.
* lint: catches the source (`#eval`, `skipKernelTC`). Lint is hygiene only, and the build job is
  untrusted.
* Non-fresh `leanchecker EGCheck.RTX2`: **catch** (`declaration type mismatch`).
* `leanchecker --fresh EGCheck.Final` on the N4 final: **catch**, measured. It reported `while replaying
  declaration 'EGCheck.RTX.bogus': (kernel) declaration type mismatch` and exited 1, after 2430 s at
  10.3 GB max RSS (`$R/ir/lcfresh.N4.log`).
* comparator: it replays the lean4export of the theorem's closure from an empty environment, so it
  catches this (design, and consistent with F3).

**Impact.** The documented claim that FinalCheck performs "a kernel replay of every project
constant" (FinalCheck header, TRUST.md.proposed §4.3) is false. FinalCheck on its own is not a
kernel check. The release still holds only because comparator and `leanchecker --fresh` also run.

### N6 (hypothesis, NOT demonstrated): different checkers see different copies of a duplicated theorem

`importModules` keeps the *later* copy of a duplicated theorem with the same name and type
(`subsumesInfo`). Non-fresh `leanchecker` and `Environment.replay` *skip* a theorem whose duplicate
is already in the environment.

FinalCheck imports `EG` and `EGCheck` besides `EGCheck.Final`, while `leanchecker --fresh` imports
`EGCheck.Final` alone. So the two checks can see different stored copies of such a theorem.
Combined with N4, the two checks that cover the `EGCheck.erdos_184` artifact might be satisfied by
different, individually acceptable views. I did not build this; my attempt stopped at the kernel's
duplicate-name check.

Comparator checks statement, axioms and replay on **one** exported view, so by design it is not
affected.

**Recommendation:** make FinalCheck reject any duplicate declaration that involves a project module,
and run its statement/axiom/replay part on `importModules #[184, EGCheck.Final]` only (the same view
as `leanchecker --fresh`).

## 3. Are the remaining gaps covered at release?

| Gap | Comparator | `leanchecker --fresh` | Covered? |
|---|---|---|---|
| N1 `lakefile.lean` | no: it runs outside and inside comparator's lake calls | no: it runs before it via `lake env` | **no** |
| N3 `json.py` / Python shadowing | no: it runs in the comparator job before comparator | no | **no** |
| N2 lock self-check | lock is not in the trust argument | – | only by the user's diff review, which the lock was meant to support |
| N4 FinalCheck attribution theft | yes (design) | yes (measured) | yes, but FinalCheck adds nothing against kernel bypasses |
| Loader-exploit `.olean` (tooling §7.2) | yes (lean4export sandboxed, ndjson checked) | no (loads the oleans) | comparator only |
| Build-time IO | yes (sandbox); `release.yml` job separation | – | yes, *if* N1/N3 are closed |

**Conclusion.** Once N1, N2 and N3 are closed, comparator is the single check that is robust to
every attack in this report. `leanchecker --fresh` and FinalCheck are useful defence in depth, but
they do not independently establish the claim for the `EGCheck.erdos_184` artifact (N4, N6).
TRUST.md should say this plainly.

## 4. `TRUST.md.proposed`: does it say exactly what a reader must trust?

It is a large improvement: complete pins, elaborated statement, advisory in-band checks, an
out-of-band criterion, a coherent α/β/γ, and a process note. It is not yet exact.

### 4.1 Missing trusted items

1. **The non-proof files of the release commit.** The acceptance steps run repository code:
   * `check_pins.sh`, `comparator.sh`, `Statement.lean`, `FinalCheck.lean`, `lint.py`, `lock.py`,
     `status.py`;
   * `redteam/tooling/run.sh` and its Lean fixtures;
   * `release.yml`;
   * `lakefile.toml`, including its `leanOptions`, which elaborate the Challenge;
   * the **absence** of `lakefile.lean` and of stray `*.py` files.

   A reader must either trust that these match a user-approved commit, or run comparator with
   their own config and an upstream-fetched Challenge. §2 lists neither.
2. **GitHub-hosted runners and the artifact store**, if `release.yml` is the criterion.
3. **Comparator's kernel**, if the comparator is built as `release.yml` builds it: unpatched, on
   Lean v4.35.0-rc3 fetched by elan without a pin (see §4.2).

### 4.2 Inaccurate statements

* **§2 item 1 and the §4 pin table vs `release.yml`.** The table pins comparator with the patch on
  v4.33.1 and lean4export `66f1fb4b`, built by `comparator.sh tools`. `release.yml` builds
  comparator **unpatched on v4.35.0-rc3** with lean4export `15f6055e`. Its Challenge check hashes
  `formal/Challenge.lean`, which does not exist, so the job fails closed. It does not use
  `comparator.sh`.
* **§4 step 0.** It says `STATEMENT.md` is regenerated and diffed; `release.yml` does not do this.
  It says there is a snapshot or `git diff` "after the build"; the verify job does not build, but it
  runs repository code (redteam fixtures, Python, the lakefile) before `lock --strict`.
* **§4 step 2.** "catches kernel bypasses in any module" should read "in any module of
  `EGCheck.Final`'s import closure".
* **§4 step 3.** "a kernel replay of every project constant" is false (N4).
* **"Checks 1–3 overlap on purpose … cover the `EGCheck.erdos_184` artifact".** This overstates
  the redundancy (§3). Comparator is load-bearing.
* **§2 item 6.** "only closure-sha256 ties the statement's definitions to the pinned sources" is
  true only because the pin was computed from a from-source Mathlib build. Record that fact (date
  and procedure), or have the release recompute the pin from source.
* **§6.** It says protected files are "hashed in LOCK.json" and lists `STATEMENT.md`,
  `comparator/Challenge.lean`, `comparator/config.json`, `comparator/patches/**` and
  `redteam/**`. `lock.py`'s `PROTECTED_FILES` hashes none of these except `redteam/tooling/**`.

### 4.3 Correct and complete

* The claim and the `STATEMENT.md` pins.
* The kernel, axioms and upstream pins.
* The Init / Batteries / Mathlib / FC closure.
* The elaboration frontend.
* The Mathlib-cache caveat.
* The advisory status of the in-band checks.
* The α/β/γ section: "EG not trusted" only at γ under §4, and the α hypotheses trusted.

## 5. `Final.lean.proposed`

The proposed file is correct as an advisory check:
* upstream imported first;
* `_root_` anchoring;
* provenance and kind checks, then the old `Expr.equal`;
* the second `/-! -/` fixed.

Note that the out-of-band checks never compile `Final.lean`: the untrusted build job produces
`EGCheck/Final.olean`, and an attacker controls its contents. So hardening this file has no effect
on the acceptance decision. That is consistent with TRUST.md.proposed calling it advisory.

**No objection to applying it.**

## 6. CI (`ci.yml`)

CI works as a regression guard: pins, lint and red-team run before the build, and scans run after
it. Its header correctly says it is not the acceptance criterion.

It cannot resist a deliberate adversary:
* build-time code runs as the same user, so it can rewrite the "pristine" snapshot in
  `$RUNNER_TEMP`, the toolchain fingerprint file, and package `.olean`s;
* `check_pins` ignores packages' `.lake/`;
* N1 and N3 also apply to CI;
* non-fresh `leanchecker` is exposed to the duplicate skip (N6).

This is acceptable only because CI is documented as non-acceptance.

## 7. Required changes

### Blocking

1. **Tree allowlist, before any `lake`, `python3` or `lean` call in every trusted job and in the
   manual audit.** Use a pure-shell/`git` check of `git ls-files` against an approved list, and
   reject `formal/lakefile.lean`, any `*.py` outside `scripts/`, and any file outside the list.
   Better still, require the release commit to differ from a user-approved "trust commit" only
   under `EG/`, `EGTest/`, `EGCheck/{Bridge*,…}` and `comparator/Solution.lean`
   (`git diff --quiet <trust-tag> HEAD -- ':!formal/EG' …`), and take the checker scripts from the
   trust tag, not from the commit under test.
2. **Run Python with `-I` (or `-P` / `PYTHONSAFEPATH=1`) everywhere**, including `check_pins.sh`,
   `comparator.sh` and the workflow heredocs. Run `lock.py check --strict` (file part) first in the
   verify job, from the trusted copy.
3. **Fix FinalCheck's replay set (N4, N6).**
   * Treat as project constants all names in any project module's `constNames`, regardless of
     `const2ModIdx`.
   * Fail on any name declared in two modules when either is a project module, and on any
     `extraConstNames` entry of a project module that names a kernel constant.
   * Replay and walk axioms per declaring module's own `ConstantInfo`.
   * Use `#[184, EGCheck.Final]` as the statement/axiom view.
   * Correct the header and TRUST.md claims until this is done.
4. **Reconcile `release.yml`'s comparator job with TRUST.md.proposed.** Use `comparator.sh check`,
   `comparator.sh tools` (patched, v4.33.1, lean4export `66f1fb4b`) and `comparator.sh run
   --release --system-unit`, or change TRUST.md's pins and kernel list to match. Fix the Challenge
   path. Add the `STATEMENT.md` regeneration diff.
5. **TRUST.md.proposed edits.** Items §4.1 and §4.2 above. State that comparator is the one check
   robust to a malicious build, and that FinalCheck and `leanchecker --fresh` are defence in depth.

### Recommended

6. Add `comparator/**`, `STATEMENT.md`, `redteam/**` and `EGCheck/Bridge*.lean` (as untrusted but
   reviewed) to `lock.py` `PROTECTED_FILES`, matching TRUST.md §6.
7. Make Canon `deps` and `reachableAxioms` proj-aware; they are harmless today, but this keeps them
   robust.
8. Give a reader's minimal recipe in TRUST.md: fresh clone; delete nothing but check that there is
   no `lakefile.lean`; `cmp` the Challenge against upstream; write the 5-line config by hand; run
   pinned comparator.

## 8. Evidence index (all under `$R`)

| Item | Files |
|---|---|
| N1 | `lk/formal/lakefile.lean` (the copy's `FinalCheck.lean` was restored afterwards) |
| N2 | `py/` |
| N3 | `lk/formal/json.py`, `pwn.txt` |
| N4 | `ir/src/EGCheck/{RTX1,RTX2,RTY2,Final}.lean`, `ir/finalcheck.N4.log`, `ir/lc.log`, `ir/lcfresh.N4.log` |
| Challenge vs upstream | `chal/` |
| Proj-closure check | `ProjClosure.lean` |
| Harness logs | `external.log`, `bridge.log` |
