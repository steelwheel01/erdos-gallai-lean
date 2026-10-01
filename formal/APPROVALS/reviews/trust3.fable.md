# Independent re-audit, round 3 (fable): gate, workflows, FinalCheck N4 fix, TRUST.md.proposed

Reviewer: independent re-auditor (Fable 5.1), 2026-09-26. Read-only audit. The only repository file
written is this report. No git command that changes the repository was run. Every experiment ran in
`mktemp -d` copies (`/tmp/fable3-staged.*`, `/tmp/fable3-gatex.*`, the harnesses' own `mktemp -d`
dirs), with the real repository additionally bind-mounted read-only for every build.

**Setup evaluated ("as if applied").** A temporary clone of the working tree with
`EGCheck/Final.lean := staging/Final.lean.proposed` (sha256 `7e50b44d…`), `TRUST.md :=
staging/TRUST.md.proposed` (`c04aad09…`), `lakefile.toml := staging/lakefile.toml.proposed`
(`6aa41d0c…`), `.claude/settings.json := staging/claude-settings.json.proposed`; `.lake/build` copied,
`.lake/packages` symlinked (read-only inside every sandbox). The working-tree `scripts/pristine.sh`
(sha256 `12a7eb96…`, 100 pins), `scripts/FinalCheck.lean` (N4 fix), `lock.py`, `lint.py`,
`check_pins.sh`, `comparator.sh`, `redteam/**` and both workflows (`.github/workflows/{ci,release}.yml`,
gate-first rewrite) are the ones audited.

**Read:** `trust2.opus.md`, `trust2.fable.md`, `trust.{opus,fable}.md`, `work/trust/{gate2,finalcheck2,
tooling,bridge,external}.md`, `staging/*`, `scripts/*` (all), `redteam/**` (all four harnesses and
their fixtures), both workflows, `.github/CODEOWNERS`, `.claude/settings.json`, comparator `fd5d5bcf`
sources + the v4.33.1 patch (`/root/tools/comparator`), and Lean v4.33.1 `Environment.lean`
(`mkModuleData`, `finalizeImport`, `subsumesInfo`), `Replay.lean`, `LeanChecker.lean`.

## Verdict: APPROVE WITH NOTES (the design is now right; three things block a first release claim)

* **Every attack of all three earlier rounds is caught** by the proposed setup, re-measured here
  (§2): opus N1/N2/N3 by the gate (53/53 gate cases + 20 new cases of mine, §2.1), N4 by the new
  FinalCheck `origin`+`replay` (external harness 19/19, §2.2), the 14 tooling fixtures (§2.2), the
  comparator F1–F5 fixtures and the honest faithful comparator run (§2.3), and the honest tree passes
  FinalCheck with the proposed pins (§2.4).
* **I found no new way to make a false theorem pass** the criterion as implemented (comparator with
  `comparator.sh` pins, `leanchecker --fresh`, FinalCheck), given the trusted list of
  `TRUST.md.proposed` + `TRUST.md.gate.md`. The new vectors I tried against the gate, the artifact
  path filter, the snapshot, comparator's sandbox order and FinalCheck's replay set are in §3.
* **Blocking before any "Final passes" claim** (none is a soundness hole; two are fail-closed bugs and
  one is documentation):
  1. `TRUST.md.proposed` is out of date with respect to the working tree it will be applied to: its
     §2 item 7 ("No check enforces this absence yet"), §4.1 ("N1–N3 are open"), §4.2 markers (0a, 0b,
     0d, 0e, 1 "not implemented") and §2 item 1 (release.yml builds comparator on v4.35.0-rc3) describe
     the *previous* `release.yml`. The gate agent's `staging/TRUST.md.gate.md` (§2 items 8–9, §4 step
     0, §4 item 1, §6) must be merged and the markers updated before the file is applied — the file
     itself says so, but as it stands it does not state exactly what a reader must trust (§4).
  2. **`release.yml` cannot pass on a GitHub runner as written**: the snapshot files are `chmod a-w`,
     and `scripts/status.py --check` (a `verify` step, and a CI post-build step) writes
     `status/STATUS.md` and `status/frontier.json` unconditionally. As the non-root `runner` user this
     is `EACCES` (measured as `nobody`, §3.5); the local measurements in `gate2.md` were made as root,
     where `a-w` is not enforced. Fail-closed, but the criterion is not runnable.
  3. **`EG_TRUST_REF` must be a commit SHA (or a signature-verified tag), not a lightweight tag.**
     Measured (§3.1 Y11b): an attacker who weakens `lock.py`, re-pins, and moves the tag gets
     `PRISTINE: PASS` from `--trust-ref <tag>`; the same with the original commit SHA is rejected.
     Neither the workflows nor `TRUST.md.gate.md` require a SHA today.
* **Recommended** (§6): pin `LOCK.json` in the gate; make the trusted workflow independent of the
  commit under test (`workflow_dispatch` from a protected branch checking out `inputs.commit` as data);
  state in TRUST.md that comparator's sandbox writes `.lake/packages`; a few TRUST.md wording items.

---

## 1. What was run

| # | What | Where | Result |
|---|---|---|---|
| 1 | `sh scripts/pristine.sh --dev` | real tree (read-only) | `DEV-PASS`; 582 files; 100/100 pins match the working tree (so the pins are current) |
| 2 | strict gate on a fresh clone of the staged tree | `/tmp/fable3-staged.*/fresh` | `FAIL (4 rejected)`: pins of `Final.lean`, `TRUST.md`, `lakefile.toml`, `.claude/settings.json` — correct: applying the proposals requires `--write-pins` at the approval |
| 3 | `--write-pins` in the temp copy, strict gate again, `--snapshot` | same | `PASS`, 100/100; snapshot of 289 files; gate sha256 `18337c5c…` |
| 4 | `redteam/gate/run.sh --from-worktree --demo` | real repo → mktemp clones | **53/53 as expected, `GATE REDTEAM: PASS`**; demo: N1 `lake env true` ran the fixture `#eval`; N3 `python3 -c` imported the repo `json.py` and `-I` did not; N2 guard works |
| 5 | 20 new gate cases (mine, §3.1) | mktemp clones | all as designed (§3.1) |
| 6 | `redteam/tooling/run.sh` | from the read-only snapshot | 14/14 verdicts as expected |
| 7 | `check_pins.sh`, `comparator.sh check`, `lint --self-test`/dev/`--release`, lint of the proposed `Final.lean`, `lock.py files --strict`, CANON-block diff, `EG-PIN` agreement | staged copy | all pins ok; comparator check OK (7 ok lines); 62/62, 0 findings, release: the 2 known `sorry`s (`EG/Proof/Main`, `EGCheck/Smoke`); proposed Final.lean 0 findings; lock: 5 violations (the 4 applied proposals + `EG/Defs/{Graph,Objects}.lean` being edited by another agent) and 111 PENDING — fail-closed until `lock.py update`; CANON blocks identical; the three `EG-PIN` lines identical in `TRUST.md.proposed` and `STATEMENT.md` |
| 8 | `redteam/external/redteam.sh --keep` | from the staged copy, real repo bind-mounted ro | §2.2 |
| 9 | `lake build EGCheck.FinalDev` (proposed Final.lean minus `#guard_msgs`) + `FinalCheck.lean --final-module EGCheck.FinalDev --allow-sorry` with pins from the proposed TRUST.md | staged copy | §2.4 |
| 10 | `Statement.lean` regeneration + `diff STATEMENT.md` | staged copy | §2.4 |
| 11 | `redteam/bridge/run.sh --tools /root/tools` with `RT_DIR=$(mktemp -d)`; `comparator.sh run --allow-sorry --tools /root/tools` (faithful: staged lakefile has Challenge/Solution) | staged copy | §2.3 |

Not re-run: `leanchecker --fresh` (21–40 min, 10.3 GB; measured by opus-2 on N4 and by the external
agent on A4/D, all caught; §3.4 explains from `LeanChecker.lean` what it replays).

## 2. Re-run of every earlier attack against the proposed setup

### 2.1 Code-before-check (opus N1, N2, N3) — the gate

`redteam/gate/run.sh` (53 cases, 5 positive controls): all verdicts as documented in `gate2.md` §2,
including N1/N1u/N1x/N1g/N1c/N1n/N1k/N1t/N1m/N1v/N1e/N1r, N2/N2m/N2p/N2p-ref/N2c/N2s (and N2p-self
PASS, the documented self-verification limit), N3/N3r/N3s/N3c/N3p/N3n/N3v, X1–X22. `--demo` confirmed
the three vectors are real and that `-I` closes N2/N3 at the Python level. My 20 additional cases are
in §3.1. Exact log: scratchpad `gate_rt.log`.

### 2.2 In-band spoofing, kernel bypasses, lint evasions, N4 — FinalCheck (external harness)

`redteam/external/redteam.sh --keep` run from the staged copy (IN-BAND = `lake build EGCheck.Final`
with the **proposed** `Final.lean` and the attacker's Bridge; OUT-BAND = the new
`scripts/FinalCheck.lean`; the harness's OK/MISMATCH column is calibrated for the *committed*
`Final.lean`; kept logs in `/tmp/rt-external.p8E7yG`):

```
ATTACK MODE        IN-BAND   LINT   OUT-BAND  RESULT
A     finalattack  green     catch  catch     OK    [FAIL] axioms: EGCheck.erdos_184 depends on sorryAx
A1    finalattack  green     catch  catch     OK    [FAIL] statement:
A2    finalattack  caught    catch  n/a       OK    in-band Type mismatch (_root_)
A3    finalattack  green     catch  catch     OK
B1    finalattack  caught    catch  n/a       MISMATCH*  in-band: EGCheck/Final.lean:33:2: Type mismatch (_root_)
C     finalattack  caught    catch  n/a       MISMATCH*  in-band: import EGCheck.Bridge failed, environment already contains 'Erdos184.erdos_184'
A4    finalattack  green     catch  catch     OK    [FAIL] replay: … '_egFinalCheckReplay.EGCheck.Bridge.solution'
D     finalattack  green     catch  catch     OK    [FAIL] replay: … '_egFinalCheckReplay.EGCheck.BridgeHack.helper'
N4    finalattack  green     catch  catch     OK    [FAIL] origin ×2 (extraConstNames; attribution) + [FAIL] replay: … 'EGCheck.RTX.bogus'
t1–t3, t5–t9  evasion  built  (t5: release only)  catch  OK
t4    evasion      built     catch  miss      OK    (bare option, correctly not a defect)
IO    evasion      wrote/tmp catch  miss      OK    (build-time IO; the read-only bind held: real tree untouched)
REDTEAM: FAIL (2 mismatches)   * = caught EARLIER than the table expects, by the proposed Final.lean
```

So 19/19 attacks are caught (17 out-of-band as expected, B1 and C additionally in-band with no
artifact left). N4's three independent failures are exactly those `finalcheck2.md` §1.7 reports.

`redteam/tooling/run.sh` (Axioms/MetaScan, lint, non-fresh leanchecker): 14/14 as in the table of
`tooling.md` §6 (RunTac and Sorry are the documented misses closed by lint/replay and release mode).

### 2.3 Comparator (bridge fixtures + honest faithful run)

`redteam/bridge/run.sh --tools /root/tools` with `RT_DIR=$(mktemp -d)` (comparator `fd5d5bcf` + the
v4.33.1 patch, lean4export `66f1fb4b`, landrun `811cfff5`; `--prebuilt`, `sorryAx` permitted, root ⇒
dry run, no `systemd-run`):

```
ok    honest:               exit 0  "Your solution is okay!"
ok    F1_DefinitionChanged: exit 1  "Const does not match between challenge and target 'Erdos184.IsCycleOrEdge'"
ok    F2_StatementWeakened: exit 1  "Challenge and solution theorem statement do not match: 'Erdos184.erdos_184'"
ok    F3_KernelBypass:      exit 1  "Lean default kernel rejects the solution"
ok    F4_ExtraAxiom:        exit 1  "Illegal axiom detected: 'Erdos184.cheat'"
ok    F5_ImportsUpstream:   exit 1  "Child exited with"
comparator red-team: 0 failure(s)
```

Honest **faithful** run on the staged copy (`lakefile.toml.proposed` in place, so no `--scratch`;
`scripts/comparator.sh run --allow-sorry --tools /root/tools`): comparator built `Challenge`,
exported it, built `Solution` inside landrun, exported it, `Lean default kernel accepts the solution`,
`Your solution is okay!`, exit 0 (`comparator_honest.log`). `--release` was not exercisable here
(root, no systemd), as in every earlier round.

### 2.4 Honest tree under the proposed criterion

* `lake build EGCheck.FinalDev` (the proposed `Final.lean` minus its `#guard_msgs`, same theorem)
  elaborates against the real bridge: the new `run_cmd` (provenance, kinds, `Expr.equal`) passes.
* `lake env lean --run scripts/FinalCheck.lean --final-module EGCheck.FinalDev --allow-sorry`, pins
  read from the **proposed** `TRUST.md`: `FINALCHECK: PASS (0 failures, 2 warnings)` in 45 s wall,
  8.86 GB max RSS — lean githash; import (11273 modules); oleans (9 packages at manifest revs,
  clean); **origin** (attribution consistent; the 4 realized same-type duplicates listed); **replay**
  (1464 declarations incl. 4 extra copies, 2 `_unsafe_rec` skipped, 6 s); kinds; statement
  (`Expr.equal`, `[u] ↔ [u_1]`); axioms exactly the three + `sorryAx` warning, `collectAxioms`
  agrees; policy (4 pre-γ `sorryAx` users as warnings); meta; both pins equal the `EG-PIN` lines
  (`4cb2cd56…`, `39d6e8c3…`, 1572 constants). Log: `finalcheck_honest.log`.
* `lake env lean --run scripts/Statement.lean` then `diff -u STATEMENT.md`: **identical**, same two
  pins, 14 s, 8.7 GB (`statement_diff.log`).

## 3. New attack surface examined this round

### 3.1 Gate: 20 new cases (mktemp clones of the staged tree; verdicts as designed)

| Case | Attack | Verdict |
|---|---|---|
| Y1 | `formal/lakefile.lean/` as a *directory* with a file inside | `zone` reject |
| Y2 | `formal/comparator/Solution/Evil.lean` (a submodule of the untrusted `Solution` lib, which `srcDir = comparator` would compile) | `unpinned` reject (trusted zone) |
| Y3 | `formal/LOCK.json` replaced | **PASS** — `LOCK.json` is not in the gate's trusted zone (see §6 R1) |
| Y4 | `formal/work/evil.json` | PASS (inert data; nothing in the trusted jobs reads `work/**`) |
| Y5 | root `pyproject.toml` + `conftest.py` | `forbidden: conftest.py` (root `.py`) |
| Y6 | `release.yml` with the gate step neutralised, checked with `--trust-ref` | `pin` + `trustref` reject (offline detection, as `gate2.md` says) |
| Y7 | `EG/Spec/Main.lean` edited (locked statement) | PASS — by design (proof zone; the lock, not the gate, covers Spec) |
| Y8 | `formal/EG/A B/C.lean` (space in a proof-zone path) | `zone` reject |
| Y9 | `formal/EG/lint.py` | `zone` + `python` reject |
| Y10 | `formal/EGCheck/Final.lean.orig` | `zone` reject |
| Y11b | attacker weakens `lock.py`, `--write-pins`, moves the lightweight tag `trust-v1` to the new commit; workflow-style `git show trust-v1:…pristine.sh` then `--trust-ref trust-v1` | **PASS** (the trust ref is the attacker's) |
| Y11c | same tree, `--trust-ref <original commit SHA>` | `pin` + 2 × `trustref` reject |
| Y12 | hard link of `pristine.sh` as `EG/Defs/HL.lean` | PASS (a regular file in the proof zone; harmless) |
| Y13 | `formal/scripts/.hidden` | `unpinned` reject |
| Y14 | `.github/actions/x/action.yml` | `unpinned` reject |
| Y15 | `EG/Proof/foo.lean.lean` | `zone` reject |
| Y16 | `EG/Proof/9Foo.lean` | `zone` reject |
| Y17 | `EGTest/Foo.olean` committed | `zone` reject |
| Y18 | new `redteam/gate/fixtures/new.fixture` | `unpinned` reject |
| Y19 | `staging/x.py.proposed` | PASS (inert; nothing executes `staging/`) |
| Y20 | `APPROVALS/reviews/x.py` | `zone` + `python` reject |

Code reading of `pristine.sh` (588 lines, dash): file list from `find` (not `git status`), so
`.gitignore`/`info/exclude` cannot hide files; byte comparison via `hash-object --no-filters` on both
sides; symlinks/FIFOs/devices, submodules, quoted/non-ASCII names, local hooks and command-running git
config rejected; `PATH` reset, `GIT_*` env cleared, `GIT_OPTIONAL_LOCKS=0`. The `join`/`comm`
pipelines rely on identical byte order of the path lists (`LC_ALL=C`, both plain `sort` and
`sort -t TAB -k1,1` on the path field) — consistent for the ASCII-only names the gate admits. One
limit stated by the script and confirmed by Y6/Y11: it cannot protect a workflow that does not run
it, and `--trust-ref` is only as immutable as the ref.

### 3.2 Artifact path filter (`release.yml` `verify`)

`^(EG|EGTest|EGCheck)(\.[A-Za-z0-9_.]+|/[A-Za-z0-9_./«»-]*)?$` with the `..` component check and
`isfile()/isdir()` only (no symlinks, no hard links). The build artifact therefore cannot place a file
outside `.lake/build/lib/lean/{EG,EGTest,EGCheck}*`, cannot shadow a toolchain or package module
(`Lean/…`, `Mathlib/…`, `Init/…`), and cannot touch `.lake/packages/**` (so the dependency
`lakefile.olean` caches that later `lake env` calls load stay the trusted ones). Python's `tarfile`
and GNU `tar` agree on PAX/GNU-long names; `$` matching before a trailing newline in a member name
only yields an oddly named file inside the allowed directory. No finding.

### 3.3 Comparator: sandbox write set and order

From `Main.lean` (`compareIt`): `lake build Challenge` → `lean4export Challenge` → `lake build
Solution` → `lean4export Solution` → compare + replay. Both builds and both exports run under landrun
with `--ro / --rwx .lake`; in **release mode `.lake/packages` is a real directory inside `.lake` and
is therefore writable by the Solution build** (in the `--scratch` red-team mode it is a symlink out
of `.lake`, hence read-only). Consequences, all covered: the Challenge export is taken before any
project code runs, so it is uncontaminated; a Solution-side rewrite of a Mathlib `.olean` in the
statement closure is a `Const does not match` (eqv over the closure); outside the closure it is
re-checked by the full replay; no `lake` call follows the Solution build (the export uses the outer
`lake env`'s `LEAN_PATH`, and `comparator.sh run` ends with comparator). The residual is the
documented loader exploit (§2 item 9). TRUST.md should state the writable set explicitly (§6 R4).

### 3.4 FinalCheck replay set completeness (N4/N6 class, re-derived from Lean source)

`lean --run` imports at `OLeanLevel.private` (`importModules` default), so `importAll := true` for
every module and `header.moduleData[i]` is the module's private-level `ModuleData`, whose
`constNames/constants` is exactly what `finalizeImport` puts into `env.constants`
(`Environment.lean` 2329–2364). Hence `collectProjDecls` (constNames ⨝ constants of every project
module) is the complete set of project kernel constants; a project constant that FinalCheck does not
replay cannot exist in the environment. A missing `.olean.private` part only removes constants (fail
closed: `axioms`/`replay` report missing names). The four `origin` rules make attribution
(`const2ModIdx`, `extraConstNames`) irrelevant to which constants are replayed, which is the N4 fix;
I confirmed the honest tree's 4 realized duplicates and 2 `_unsafe_rec` skips are the only
exceptions and are handled as `finalcheck2.md` describes. `Replay.lean` re-checks constructors and
recursors against the stored ones (lines 152, 163). `leanchecker --fresh` replays
`env.constants.map₁` of `withImportModules #[M]`, i.e. the *kept* copy of a merged duplicate — the N6
view; FinalCheck now replays every copy and comparator replays the exported view, so N6 is closed
across the three.

### 3.5 Workflow runnability: read-only snapshot vs `status.py`

`pristine.sh --snapshot` does `find "$SNAP" -type f -exec chmod a-w`. `scripts/status.py` writes
`status/STATUS.md` (line 67) and `status/frontier.json` on every run, `--check` included. Measured as
uid 65534: `open(f, "w")` on an `a-w` file → `PermissionError: [Errno 13]`. On GitHub the jobs run as
`runner`, not root, so **`verify` fails at "Status and sorry ratchet" and CI fails at "Status and sorry
ratchet (pristine copy)"** before FinalCheck/leanchecker run. Fix: write to `$RUNNER_TEMP` (or make
`--check` read-only), or drop the step from `verify` (it is hygiene).

### 3.6 Other vectors considered (no finding)

* Elan `lean-toolchain` lookup walks up from cwd: in the snapshot it finds the pinned copy; any other
  `lean-toolchain` in the tree is `forbidden`. `LAKE`/`LEAN_PATH`/`PYTHON*` env are not
  repository-controlled; `-I` ignores `PYTHON*`.
* `redteam/tooling/run.sh` compiles pinned fixtures (some with `#eval`) in the trusted `verify` job:
  trusted-zone content executing, acceptable but worth one sentence in TRUST.md.
* CI (`ci.yml`): the `--link-lake` snapshot shares `formal/.lake` with the build, so post-build
  `lake env` calls load dependency `lakefile.olean` caches the build could rewrite; `--allow-build`
  and `--verify-snapshot` do not see `.lake`. CI is documented as regression-only; the header should
  say this specific limit (it says the general one).
* `comparator.sh tools`: `git clone` + `checkout --force <sha>` + HEAD verified; Go modules via
  `go.sum`. Trusted per §2 item 8; add "Go module proxy/sumdb".
* `subsumesInfo` also merges `thmInfo`/`axiomInfo` pairs: a project `axiom` twin of a package theorem
  is rejected by `origin` (1) and `policy`.

## 4. Does `TRUST.md.proposed` state exactly what a reader must trust?

Correct and complete: the claim as the elaborated statement with `STATEMENT.md` and the three
`EG-PIN`s (verified equal to what FinalCheck/Statement compute); kernel v4.33.1 as run by the three
checkers; the three axioms; the two upstream files with blob+SHA; Init/Batteries/Mathlib/FC closure
with the from-source provenance of the pins; the elaboration frontend with `leanOptions`; Lake, the
Mathlib cache, pinned CI installers; runners and artifact store; comparator/lean4export/landrun pins
and README assumptions plus comparator's code; the `.olean` loader residual (item 9, correcting the
round-2 overstatement); in-band checks advisory; §4.1 roles (comparator load-bearing); §4.4 reader's
recipe; the α/β/γ section. `Final.lean.proposed` (docstring-only change) is accurate about the
same-type merge and is fine to apply.

Not yet exact (must change before applying):

1. **Stale against the working tree** (blocking item 1 above): §2 item 1 (release.yml/v4.35.0-rc3),
   §2 item 7 last sentence, §4.1 "N1–N3 are open", §4.2 markers 0a/0b/0d/0e/1 and the closing
   sentence "release.yml does not implement §4". Merge `TRUST.md.gate.md` (§2 items 8–9 with the gate
   sha256 and `EG_TRUST_REF`, §4 step 0, §4 item 1, §6 addition) and re-mark 0a–0f and 1 as
   implemented; keep "never run on GitHub" until it has.
2. **`EG_TRUST_REF` semantics.** Say: a full commit SHA, set as a repository variable by an admin;
   or a tag whose signature the gate step verifies (`git verify-tag`); a movable tag is not a trust
   anchor (§3.1 Y11b). Say also that a run is evidence only if `.github/workflows/*` at the tested
   commit equal the trust commit (the gate checks this offline; the run cannot check itself).
3. **§2 item 8:** add that landrun's writable set is the whole `.lake`, packages included, and why
   this is sound (export order, closure eqv, full replay) — §3.3.
4. **§2 item 7:** add `LOCK.json` (read by `lock.py files --strict`, which is a release step) — it is
   not gate-pinned (Y3); either pin it or say the lock step is hygiene and can be defeated by editing
   `LOCK.json` together with a Spec file.
5. **§4.2 step 3:** say `status.py --check` is hygiene (and fix §3.5).
6. **§5 stage α:** "checked by the criterion of §4 adapted to the premises" — comparator compares
   against the unconditional upstream Challenge and cannot check an α artifact as is
   (`bridge.md` §8 item 7). Say the α criterion is to be designed in P2.
7. Small: `redteam/tooling` fixtures execute in `verify` (trusted content); Go module proxy; the
   `--link-lake` CI limit.

## 5. Attack ↔ catcher matrix (proposed setup, this round's measurements)

| Attack | Gate | lint | Axioms/MetaScan | FinalCheck | `leanchecker --fresh` | comparator |
|---|---|---|---|---|---|---|
| N1 `lakefile.lean` (+ variants, Lake/elan files, `.lake/`) | **catch** | – | – | – | – | – |
| N2 `scripts/hashlib.py`, modified `lock.py` (+ re-pin, with trust ref) | **catch** (+`-I`) | – | – | – | – | – |
| N3 `formal/json.py`, root `.py`, `.pth`, `sitecustomize`, native modules | **catch** (+`-I`) | – | – | – | – | – |
| N2p-self / moved lightweight tag as trust ref | miss (documented; use a SHA) | – | – | – | – | – |
| N4 IR attribution theft | – | catch | miss | **catch** (origin ×2 + replay) | catch (opus-2) | catch (design) |
| A/A3 spoofed `#print axioms`, `sorryAx` | – | catch | catch | **catch** | miss | **catch** |
| A1/B1 elaborator hijack | – | catch | catch | **catch** (statement) / in-band `_root_` | miss | **catch** |
| A2/B0 shadow | – | catch | catch | in-band (`_root_`) | – | – |
| C fake upstream | – | catch | catch | in-band clash / origin | – | **catch** |
| A4/D/D′ kernel bypass | – | catch/miss | catch/miss | **catch** (replay) | **catch** | **catch** (F3) |
| t1–t9 lint evasions | – | catch (t5 release only) | per table | catch (t4 benign miss) | – | – |
| IO build-time write | – | catch | – | miss (by design) | – | sandbox; job separation |
| F1/F2/F4/F5 Solution attacks | – | – | – | – | – | **catch** |
| crafted `.olean` (loader exploit) | – | – | – | miss | miss | miss (documented, §2 item 9) |

## 6. Recommendations (ranked)

Blocking before the first release claim:
1. Merge `TRUST.md.gate.md` into `TRUST.md.proposed` and update every stale marker/sentence (§4
   items 1–2); apply the four proposals together with `pristine.sh --write-pins`, `lock.py update`
   and a new `EG_TRUST_REF`.
2. Require `EG_TRUST_REF` to be a 40-hex commit SHA in both workflows (reject anything else, or
   `git verify-tag` it) and say so in TRUST.md.
3. Fix `status.py --check` for the read-only snapshot (§3.5), then do one real run of `release.yml`
   on a branch (dry run, `sorryAx` permitted) — it has never run on GitHub, and landrun/Landlock,
   `sudo systemd-run` and the ≥ 16 GB runner are unverified.

Recommended:
- R1. Add `formal/LOCK.json` to the gate's trusted zone (it is a release input).
- R2. Make the trusted workflow independent of the commit under test: a `workflow_dispatch`-only
  release workflow on a protected branch that checks out `inputs.commit` as data; then the workflow
  definition cannot be edited by the commit under test and `EG_TRUST_REF` reduces to that branch's
  head.
- R3. `ci.yml`: run `FinalCheck --scan-only` and the STATEMENT diff already added (good); note the
  `--link-lake` limit in the header.
- R4. TRUST.md §2 item 8 wording on the writable `.lake` (§3.3); §5 α wording; Go proxy.
- R5. `redteam/bridge/run.sh`: default `RT_DIR` to `mktemp -d` (CI already passes one).
- R6. Remove `EGCheck/Smoke.lean` before release (still `sorry`).

## 7. Evidence index (scratchpad `/tmp/claude-0/…/scratchpad/`)

`gate_rt.log` (53 cases + demo), `rt_tooling.log`, `rt_external.log` (+ kept harness dir printed in
it), `finalcheck_honest.log`, `statement_diff.log`, `rt_bridge.log`, `comparator_honest.log`,
`staged_dir.txt` / `gatex_dir.txt` (the temporary trees; `/tmp/fable3-*`).
