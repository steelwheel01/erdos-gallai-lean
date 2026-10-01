# Independent re-audit of the hardened trust setup (`staging/Final.lean.proposed`, `staging/TRUST.md.proposed`, out-of-band checks, CI)

Reviewer: independent re-auditor (Fable 5.1), 2026-09-26. Read-only audit. The only repository file
written is this report. No git command that changes the repository was run. Every experiment ran in
a temporary copy of the tree under the session scratchpad
(`/tmp/claude-0/…/scratchpad/staged/formal`) with the three staged proposals applied
(`EGCheck/Final.lean` := `staging/Final.lean.proposed`, sha256 `9cf18135…`; `TRUST.md` :=
`staging/TRUST.md.proposed`; `lakefile.toml` := `staging/lakefile.toml.proposed`), `.lake/build`
copied and `.lake/packages` symlinked read-only. Attack fixtures used are the committed ones under
`formal/redteam/` (none was added to `EG/`, `EGTest/`, `EGCheck/`).

Question audited: with the staged `Final.lean` and `TRUST.md` applied, does the OUT-OF-BAND acceptance
criterion (comparator, `leanchecker --fresh`, `scripts/FinalCheck.lean`) catch every attack of the two
earlier audits (`trust.opus.md`, `trust.fable.md`) plus new ones, is what remains covered at release,
and does `TRUST.md.proposed` say exactly what a reader must trust?

**Verdict: APPROVE WITH NOTES.** The acceptance criterion is now sound in design and in measurement:
every soundness attack of both audits is caught out-of-band by at least two independent mechanisms
(FinalCheck and comparator; kernel bypasses additionally by `leanchecker --fresh`), and the proposed
`Final.lean` additionally stops attacks B0/A2, B1 and C already at elaboration. The notes are (i) the
committed `release.yml` does not implement what `TRUST.md.proposed` §4 describes (its comparator job
cannot pass as written, uses a different comparator/lean4export build than the one TRUST.md pins, and
never regenerates `STATEMENT.md`); (ii) three sentences in `TRUST.md.proposed` overstate coverage
(comparator does not close the crafted-`.olean` loader residual; the in-band "import clash" claim in
`Final.lean.proposed` holds only for a *different-type* re-declaration); (iii) the protection lists
(lock, CODEOWNERS, deny rules) lag behind the files TRUST.md §6 calls protected. None of (i)–(iii) is a
way to make a false theorem pass; (i) makes the release fail closed. All three must be fixed before the
first "Final passes" claim, and (ii) before `TRUST.md.proposed` is applied.

---

## 1. What was run (evidence)

| Step | Command (in the staged copy unless noted) | Result |
|---|---|---|
| pins | `./scripts/check_pins.sh` (repo) | all pins ok (toolchain text + `lean --githash`, lakefile/manifest revs, 10 packages at rev and clean, FC toolchain/manifest, both file hashes and blob ids, Mathlib tag) |
| lint | `python3 scripts/lint.py --self-test`; `lint.py`; `lint.py --release` (repo and staged copy) | 59/59; 0 findings; release: exactly the 3 known `sorry`s (`EG/Proof/Main`, `EG/Proof/Ext/BMLemma25`, `EGCheck/Smoke`), exit 1. `lint.py EGCheck/Final.lean` on the proposed file: 0 findings |
| comparator layout | `scripts/comparator.sh check` (repo) | OK: `Challenge.lean` byte-identical to pinned `184.lean` (sha256, blob, HEAD blob, `cmp`), config = release config, Solution does not import `FormalConjectures.ErdosProblems.*` |
| canon | `diff` of the `BEGIN CANON..END CANON` blocks of `FinalCheck.lean` and `Statement.lean` | identical |
| in-band, honest | `lake build EGCheck.Final` with the proposed `Final.lean` and the real bridge | fails **only** at the `#guard_msgs` (`[propext, sorryAx, Classical.choice, Quot.sound]`); the new `run_cmd` (provenance, kinds, `Expr.equal`) passes; no linter warning |
| out-of-band, honest | dev copy `EGCheck/FinalDev.lean` (= proposed file minus the `#guard_msgs` block), `lake env lean --run scripts/FinalCheck.lean --final-module EGCheck.FinalDev --allow-sorry` with **pin file = `TRUST.md.proposed`** | `FINALCHECK: PASS (0 failures, 2 warnings)`: lean githash, import (11271 modules), oleans (9 packages at manifest revs, clean), origin, replay (1383 constants, 5 s), kinds, statement (`Expr.equal`, `[u] ↔ [u_1]`), axioms exactly the three (+ `sorryAx` warning) with `collectAxioms` agreeing, policy, meta, `statement-sha256` and `closure-sha256` (1572 constants) equal to the `EG-PIN` lines of the proposed TRUST.md. 38 s wall, 8.8 GB max RSS |
| tooling red team | `redteam/tooling/run.sh` (repo) | all 14 verdicts as expected (table in `work/trust/tooling.md`), exit 0 |
| external red team | `redteam/external/redteam.sh --keep` from the **staged** copy (so the in-band column is the proposed `Final.lean`) | §2 |
| comparator red team | `redteam/bridge/run.sh --tools /root/tools` from the staged copy (`sorryAx` permitted) | §3 |
| comparator, honest, faithful | `scripts/comparator.sh run --allow-sorry --tools /root/tools` from the staged copy (lakefile with `Challenge`/`Solution`; comparator builds both inside landrun) | §3 |

Not re-run: `leanchecker --fresh EGCheck.Final` (21 min, ~10 GB; measured by trust.opus §3.3 and by the
external agent on attacks D and A4, both caught with `(kernel) declaration type mismatch`). I rely on
those measurements and on the Lean source (`Lean/Replay.lean`: every non-`unsafe`/non-`partial`
constant goes through `addDeclCore`).

## 2. Attacks of both audits against the proposed criterion (measured)

Harness output (`redteam/external/redteam.sh` run from the staged copy; IN-BAND = `lake build EGCheck.Final`
with the **proposed** `Final.lean` and the attacker's Bridge; OUT-BAND = `scripts/FinalCheck.lean` on the
resulting `.olean`; RESULT = the harness's expectation table, which is calibrated for the *current*
`Final.lean`):

```
ATTACK MODE      IN-BAND   LINT    OUT-BAND  RESULT
A     finalattack green     catch   catch     OK
A1    finalattack green     catch   catch     OK
A2    finalattack caught    catch   n/a       OK
A3    finalattack green     catch   catch     OK
B1    finalattack caught    catch   n/a       MISMATCH (out-band did not fire)   <- caught EARLIER, at elaboration
C     finalattack caught    catch   n/a       MISMATCH (out-band did not fire)   <- caught EARLIER, at import
A4    finalattack green     catch   catch     OK
D     finalattack green     catch   catch     OK
t1    evasion     built     catch   catch     OK
t2    evasion     built     catch   catch     OK
t3    evasion     built     catch   catch     OK
t4    evasion     built     catch   miss      OK   (benign option only; correctly not a defect)
t5    evasion     built     miss    catch     OK   (lint dev mode; release mode catches)
t6    evasion     built     catch   catch     OK
t7    evasion     built     catch   catch     OK
t8    evasion     built     catch   catch     OK
t9    evasion     built     catch   catch     OK
IO    evasion     wrote/tmp catch   miss      OK   (build-time IO; the read-only bind held: no write to the real tree)
REDTEAM: FAIL (2 mismatches)   <- the two rows above; every other verdict matches
```

Exact messages (logs in `/tmp/rt-external.oTQ0YI/`): A2, B1: `EGCheck/Final.lean:28:2: Type mismatch`
(the theorem itself, thanks to `_root_`); C: `EGCheck/Final.lean:1:0: import EGCheck.Bridge failed,
environment already contains 'Erdos184.erdos_184' from FormalConjectures.ErdosProblems.«184»`; A, A3:
`[FAIL] axioms: _egFinalCheckReplay.EGCheck.erdos_184 depends on sorryAx` + `[FAIL] meta:
EGCheck.Bridge.printAxiomsQuiet … mentions [Lean.Elab.Command.CommandElab]`; A1: `[FAIL] statement:`;
A4: `[FAIL] replay: … while replaying declaration '_egFinalCheckReplay.EGCheck.Bridge.solution':
(kernel) declaration type mismatch`; D: `[FAIL] replay: … '_egFinalCheckReplay.EGCheck.BridgeHack.helper'`
+ two `[FAIL] meta:` hits (`commandRt_register_helper : Lean.ParserDescr`, its elab rule).

Reading of the table (the harness's OK/MISMATCH column is calibrated for the *current* `Final.lean`;
with the proposed one, three attacks die earlier, which the harness reports as a mismatch):

* **A, A3 (spoofed `#print axioms`, `sorryAx` proof)** — in-band green (the proposed `run_cmd` passes:
  statement and provenance are honest). Out-of-band: `[FAIL] axioms: … depends on sorryAx`, plus
  `[FAIL] meta: EGCheck.Bridge.printAxiomsQuiet … mentions Lean.Elab.Command.CommandElab`. Caught.
* **A1 (hijacked `type_of%` + `run_cmd`)** — in-band green (the hijacked `run_cmd` is a no-op, so the
  new provenance checks never run: **the hardened `run_cmd` adds nothing against an elaborator
  override**, as the file itself now says). Out-of-band: `[FAIL] statement:`. Caught.
* **A2/B0 (shadow `EGCheck.Erdos184.erdos_184`)** — with `_root_` the theorem no longer elaborates
  (type mismatch); caught at elaboration, no artifact.
* **B1 (shadow + `run_cmd` no-op)** — same: `_root_` kills it before the `run_cmd` matters.
* **C (fake upstream, no meta)** — `import EGCheck.Bridge failed, environment already contains
  'Erdos184.erdos_184' from FormalConjectures.ErdosProblems.«184»`. Caught at import.
* **A4, D (kernel bypass, honest type)** — in-band green; out-of-band `[FAIL] replay: kernel rejected a
  project constant: … (kernel) declaration type mismatch`. Caught (and by `leanchecker --fresh`, per the
  external agent's run).
* **t1–t3, t6 (axiom evasions)** — `[FAIL] policy: … declares an axiom`; **t5, t8** `uses sorryAx`; **t7**
  `implemented_by/extern/ofReduceBool`; **t9** `[FAIL] meta:`. Caught.
* **t4 (`«debug».skipKernelTC` option, nothing planted)** and **IO (build-time file write)** — not a
  statement/axiom defect, correctly not flagged out-of-band; lint flags both; the harness's read-only
  bind mount confirmed the IO attack cannot reach the real tree; in release the build runs on a
  separate runner and only the project `.olean`s cross over (§5).

## 3. Comparator (bridge layout) — measured

`redteam/bridge/run.sh --tools /root/tools` (comparator `fd5d5bcf` + v4.33.1 patch, lean4export `66f1fb4b`,
landrun `811cfff5`; `--prebuilt`, `sorryAx` permitted; run as root without `systemd-run`, so a dry run):

```
ok    honest:               exit 0  "Your solution is okay!"
ok    F1_DefinitionChanged: exit 1  "Const does not match between challenge and target 'Erdos184.IsCycleOrEdge'"
ok    F2_StatementWeakened: exit 1  "Challenge and solution theorem statement do not match: 'Erdos184.erdos_184'"
ok    F3_KernelBypass:      exit 1  "Lean default kernel rejects the solution"
ok    F4_ExtraAxiom:        exit 1  "Illegal axiom detected: 'Erdos184.cheat'"
ok    F5_ImportsUpstream:   exit 1  "Child exited with" (Solution build fails: declaration clash)
comparator red-team: 0 failure(s)
```

Faithful honest run on the staged copy (`lakefile.toml.proposed` in place, so no `--scratch`; comparator
itself built `Challenge` and then `Solution` inside landrun, exported both, compared, replayed):
`Lean default kernel accepts the solution` / `Your solution is okay!`, exit 0 (`comparator_honest.log`).

Observation: another agent ran `redteam/bridge/run.sh` at the same time; both runs used the script's
fixed default `RT_DIR=/tmp/eg-comparator-redteam` and each case does `rm -rf $OUT/<case>`, so
concurrent runs can clobber each other's scratch copies and logs. My verdict lines were captured before
the other run reached the same cases, but the default should be `mktemp -d`.

Comparator's checks, read from the source at `fd5d5bcf` (+ the project's v4.33.1 patch): the theorem's
`ConstantVal` (name, universe params, type) must be `BEq` to the Challenge's; every constant reachable
from the statement (types **and** definition bodies, via `runForUsedConsts`, `Expr.proj` structure names
included by the patch) must be `BEq` to the Challenge's; axioms reachable from the theorem (types and
bodies) must be permitted; the whole exported Solution environment is replayed in the kernel
(`Environment.replay`), with a Quot post-check. The Solution and `lean4export` run inside landrun
(`--ro /`, `--rwx .lake`). That is an independent second implementation of everything FinalCheck
checks except the closure pin.

## 4. New attack surface examined (analysis + code reading; no new fixtures were written)

1. **Same-type duplicate declarations (the `subsumesInfo` merge).** Lean v4.33.1
   `Environment.lean:2268–2285, 2336–2343`: two imported constants with the same name are an import
   error *unless* both are theorems (or theorem/axiom) with `==`-equal types and equal `all`; then the
   **later** module's `ConstantInfo` silently replaces the earlier one, while `const2ModIdx` keeps the
   **first** module. Consequences:
   * `Final.lean.proposed`'s docstring says a second declaration of `Erdos184.erdos_184` "is an import
     clash". True only when the type differs (attack C). A project module may re-declare
     `Erdos184.erdos_184` with the identical type and any proof, and the in-band build merges it
     (harmless in-band: only the type is used), or re-declare a Mathlib theorem with the identical type
     and a bogus proof, which the in-band `#print axioms` would only see if honest.
   * FinalCheck handles exactly this: `origin` fails when a project module's `constNames` contains a
     constant attributed to a package module (`re-declares … attributed to package module`); the merged
     copy of a *project* theorem is replayed (it is the one in `env`), so a bogus body fails the kernel;
     a `sorryAx` body fails the axiom walk. Comparator replays and walks the exported environment, so a
     merged copy is checked there too. `leanchecker --fresh` replays module by module and catches an
     ill-typed body. Axioms.lean/MetaScan would *miss* such a copy (it is attributed to the package
     module), which is fine since MetaScan is hygiene. **Recommendation:** reword the docstring
     ("a second declaration with a different type is an import clash; a same-type one is caught by
     FinalCheck's origin check").
2. **Crafted `.olean` bytes.** In the release `build` job project code runs with IO, so the artifact
   is arbitrary bytes. Every checker that reads it (`importModules` in FinalCheck/Axioms/Lock,
   `leanchecker`, and comparator's `lean4export`) maps the compacted region without structural
   validation. `TRUST.md.proposed` §3/§4 and `work/trust/tooling.md` §7.2 say comparator covers this.
   It does not: comparator's Solution build runs inside the sandbox with `.lake` writable, a build-time
   `#eval` can rewrite an earlier module's `.olean`, `lean4export` then reads it (inside the sandbox) and
   comparator trusts the *text* it prints. A loader exploit would let the export describe any
   environment. This is a residual shared by all three checkers and by every Lean project; the honest
   statement is "the Lean v4.33.1 `.olean` loader on adversarial input is trusted; the mitigations
   (lint, MetaScan, job separation) are hygiene". Optional hardening: in the `verify` job rebuild each
   project module from source with the pinned `lean` in its own landrun sandbox (read-only build dir
   except the module's own outputs), so every `.olean` the checkers read was written by the trusted
   `lean` binary. Not blocking; a TRUST.md wording fix is.
3. **`partial` definitions.** `Environment.replay` skips `unsafe` and `partial` constants; a safe
   theorem using a `partial def` then fails replay with an unknown constant (fail closed). The tree has
   none; lint does not forbid `partial`. Document it in AGENTS.md rule 2 (or add a lint rule) so a prover
   does not discover it at release.
4. **FinalCheck coverage of the artifact.** Every constant in the environment is either in a package
   module (built in `verify` from pinned sources / trusted cache) or listed in a project module's
   `constNames` (the import zips `constNames` with `constants`), and every project-attributed constant
   is renamed and replayed, with a leak check that no original project name survives renaming. Module
   roots outside `EG/EGTest/EGCheck` fail `oleans` ("belongs to no pinned package") and are rejected by
   the artifact path regex anyway. I found no way for a project constant to reach the final theorem's
   proof without being replayed, other than item 2.
5. **Universe/binder tricks, `mdata`, aliases, notation, instances, options in imports** — unchanged
   from the first audits: `type_of%` fixes the `Expr`; `Expr.equal` is binder-sensitive; aliases are not
   constants; notation and instances leave meta constants (MetaScan) and cannot change a kernel type.
6. **Comparator Solution imports.** `Solution.lean` imports `EG.Proof.Main` and `EGCheck.BridgeCore`;
   `comparator.sh check` only greps `Solution.lean` itself for an upstream import. A transitive import
   of `FormalConjectures.ErdosProblems.«184»` is caught by comparator (F5, build clash) — at release
   only. A cheap lint rule ("nothing under `EGCheck/BridgeCore|BridgeLemmas` imports
   `FormalConjectures.ErdosProblems`") would move that to CI.

## 5. CI and the release workflow vs. `TRUST.md.proposed` §4

`ci.yml` (regression guard, not the criterion — its header says so): pins, lint self-test, lint and
the tooling red team run before the build; scans run from a pristine copy after the build; post-build
`git diff`, `git status`, toolchain fingerprint and `check_pins` re-run; non-fresh `leanchecker`.
Coverage of the attacks in CI: lint + MetaScan catch A, A1, A3, B1, C, D, t1–t3, t6–t9; `leanchecker`
catches A4/D′; IO is caught by lint only (a write into `.lake/packages/*/.lake/build` is invisible to
`git status`, since `formal/.lake/` is git-ignored; acknowledged as regression-only). CI never runs
`FinalCheck.lean` (not even `--scan-only`) and never regenerates `STATEMENT.md`.

`release.yml` **does not yet implement §4 of `TRUST.md.proposed`**:

* **comparator job cannot pass as written.** Its byte-identity step derives the Challenge path from the
  module name (`Challenge.lean` at `formal/`), but the file is `comparator/Challenge.lean`
  (`sha256sum -c` fails); it runs comparator in `formal/` whose `lakefile.toml` has no
  `Challenge`/`Solution` libraries until `lakefile.toml.proposed` is applied; it builds comparator
  **unpatched with its own toolchain v4.35.0-rc3** and lean4export `15f6055e` (v4.33.0 tag), whereas
  TRUST.md.proposed §4 pins comparator `fd5d5bcf` **+ the v4.33.1 patch**, lean4export `66f1fb4b`, both
  built with v4.33.1 (and item 1 says the kernel that replays is v4.33.1's). The bridge agent measured
  that the unpatched build accepts comparator's own `proj_trick` counterexample (issue 68) when built
  with v4.33.1; with v4.35.0-rc3 it is comparator upstream's configuration, but then the replaying kernel
  is not the pinned one. Replace the step by `scripts/comparator.sh check` and the run by
  `scripts/comparator.sh tools DIR && scripts/comparator.sh run --release --system-unit --tools DIR`.
* **`STATEMENT.md` is never regenerated** (no `Statement.lean` step in `verify`), although §4 step 0
  requires an empty diff. Add `lake env lean --run scripts/Statement.lean /tmp/S.md && diff /tmp/S.md
  STATEMENT.md` after the FC build and before the artifact is installed.
* §4 step 0 "snapshot `scripts/`, TRUST.md, …" is unnecessary in `verify` (it never runs project code)
  but is not done in `build` either; harmless because `build` only exports `.olean`s.
* `redteam/external/redteam.sh` and `redteam/bridge/run.sh` are run nowhere in CI (only
  `redteam/tooling/run.sh`). They are the regression tests of FinalCheck and of the comparator layout.
* The `verify` runner requirement (≥ 16 GB) and the `EG_RELEASE_RUNNER` variable are documented; the
  workflow has never run on GitHub (tooling §5), so landrun/Landlock and `systemd-run` on the runner are
  unverified.

## 6. Does `TRUST.md.proposed` say exactly what a reader must trust?

Mostly yes, and far better than the current file: the claim is stated as the *elaborated* statement
with `STATEMENT.md` and two closure pins (verified equal to what FinalCheck computes); Init, Batteries
(`4488d40d`, 6 declarations), Mathlib (949), FC (3) are listed and add up to the 1572 of `STATEMENT.md`;
the elaboration frontend, Lake, the Mathlib cache, the CI installers, the checkers and comparator's
assumptions are listed; the in-band checks are declared advisory with the reason; the acceptance
criterion is out-of-band with an order; stage α/β/γ is coherent ("EG is not trusted" only at γ under §4;
the three classical hypothesis texts are trusted at α/β). Items to correct or add before applying it:

1. **Overstated coverage (§3, §4 and `work/trust/*.md`):** "comparator covers a crafted loader-exploit
   `.olean`" — it does not (§4.2 above). List the `.olean` loader as trusted.
2. **Trusted code, not only the kernel.** Item 1 lists the kernel "as run by" the three checkers, but the
   criterion also trusts the *correctness of the checker code*: `scripts/FinalCheck.lean` (statement
   comparison, axiom walk, canonical serialisation), `scripts/Statement.lean`, `scripts/check_pins.sh`,
   `scripts/comparator.sh`, the comparator patch, `release.yml` (artifact validation regex, job
   separation), lean4export, and the Lean interpreter that runs the scripts. §6 lists them as protected
   files; say explicitly that they are trusted code, and that comparator and FinalCheck are two
   independent implementations so a permissive bug must be in both to matter.
3. **§4 vs. the workflow.** §4 says `release.yml` "implements steps 0–3"; today it does not (§5). Either
   fix the workflow first or say "will implement".
4. **§6 protected list vs. the lock/CODEOWNERS/deny rules.** §6 names `STATEMENT.md`,
   `comparator/Challenge.lean`, `comparator/config.json`, `comparator/patches/**`, `redteam/**`. The
   committed `lock.py` hashes `scripts/**`, `redteam/tooling/**`, `.github/workflows/**`,
   `../.claude/settings.json`, `../.github/CODEOWNERS`, but **not** `STATEMENT.md`, `comparator/**`,
   `redteam/bridge/**`, `redteam/external/**`; CODEOWNERS lacks `comparator/`, `redteam/`,
   `STATEMENT.md`; the deny list lacks all of them. Also `lock.py check` currently reports 0 violations and **32 PENDING** unlocked files (all of
   `scripts/**`, `redteam/tooling/**`, `status/ratchet.json`, …); `--strict`, which the release `verify`
   job uses, fails until `lock.py update` is run under an approval.
5. **Same-type duplicate wording** in `Final.lean.proposed` (§4.1 above).
6. **Small:** `TRUST.md.proposed` §2 item 1 says FinalCheck runs the kernel via `Environment.replay`
   (correct); add that `unsafe`/`partial` constants are skipped by design and therefore unusable.
   `lake exe cache get` in `verify` and `comparator` jobs is stated as trusted (good). The `lakefile.toml`
   comment fix (`lint.py`) is in `lakefile.toml.proposed` (good).

## 7. Which attacks are caught by what (final matrix, proposed setup)

| Attack | proposed `Final.lean` in-band | lint | Axioms/MetaScan | FinalCheck | `leanchecker --fresh` | comparator |
|---|---|---|---|---|---|---|
| A / A3 spoofed `#print axioms`, `sorryAx` | miss | catch | catch (meta) | **catch** (axioms, meta) | miss | **catch** (axioms) |
| A1 hijacked `type_of%`+`run_cmd` | miss | catch | catch | **catch** (statement) | miss | **catch** (statement) |
| A2/B0 shadow | **catch** (`_root_`) | catch | catch | n/a | n/a | n/a |
| B1 shadow + `run_cmd` no-op | **catch** (`_root_`) | catch | catch | n/a | n/a | n/a |
| C fake upstream (different type) | **catch** (import clash) | catch | catch | catch (import) | – | catch (F1/F2-type) |
| C′ same-type re-declaration of a package theorem, bogus/sorry body | miss (merged) | catch (reserved name) / miss for a Mathlib name | miss (attributed to package) | **catch** (origin; axioms/replay) | catch if ill-typed | **catch** (replay/axioms) |
| A4 / D / D′ kernel bypass | miss | catch / miss (D′ leaves no token only if hidden) | catch / miss (D′) | **catch** (replay) | **catch** | **catch** (F3) |
| F1 changed `IsCycleOrEdge`, F2 weakened statement (Solution) | n/a | – | – | n/a (Final imports upstream) | miss | **catch** |
| F4 extra axiom | – | catch | catch | catch (policy/axioms) | miss | **catch** |
| F5 Solution imports upstream | – | – | – | – | – | **catch** (clash) |
| t4 bare option, IO build-time write | – | catch | miss | miss (by design) | miss | miss (sandbox contains it) |
| crafted `.olean` (loader exploit) | – | – | miss | miss | miss | **miss** (see §4.2) |

## 8. Recommendations (ranked)

Blocking before the first "Final passes"/release claim:
1. Fix `release.yml`'s comparator job (use `scripts/comparator.sh check|tools|run --release
   --system-unit`, pinned patched build) and add the `STATEMENT.md` regeneration/diff to `verify`;
   apply `lakefile.toml.proposed`; do one real GitHub run of `release.yml` (dry run, `sorryAx`
   permitted, on a branch) to exercise landrun/systemd-run/RAM.
2. Correct `TRUST.md.proposed` per §6 items 1–3 (loader residual, trusted checker code, workflow
   status) and `Final.lean.proposed`'s docstring per §4.1.
3. Bring `lock.py` `PROTECTED_FILES`, CODEOWNERS and the deny list in line with TRUST.md §6; run
   `lock.py update` under an approval so `--strict` passes.

Strongly recommended:
4. Add to `ci.yml`: `FinalCheck.lean --scan-only --policy-roots EG,EGTest,EGCheck` and
   `redteam/external/redteam.sh`/`redteam/bridge/run.sh` (weekly or on `scripts/**` changes), and the
   `STATEMENT.md` diff.
5. Lint rule: no `FormalConjectures.ErdosProblems` import under `EGCheck/BridgeCore.lean`,
   `EGCheck/BridgeLemmas.lean` (comparator layout); forbid `partial`; AGENTS.md rule 2 updated with the
   tooling agent's list (no notation, no `#eval`, `set_option` allowlist, no meta identifiers, no
   `Erdos184`).
6. Consider the per-module sandboxed rebuild in `verify` (§4.2) if the loader residual is judged
   unacceptable; otherwise document it.
7. Remove `EGCheck/Smoke.lean` before release; pin comparator's toolchain download if the unpatched
   v4.35.0-rc3 route is ever used.

## 9. Evidence index (scratchpad `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-…/scratchpad/`)

`staged/` (temporary tree with the proposals applied), `finalcheck_dev.log` (+ `.err`),
`rt_tooling.log`, `rt_external.log` with per-attack logs in `/tmp/rt-external.oTQ0YI/` (staged
`Final.lean`, sha `9cf18135…`), `rt_bridge.log`, `comparator_honest.log`, `chain.log`.
