# Trust hardening round 3: FinalCheck N4 fix and TRUST.md alignment (agent id: `finalcheck`, 2026-09-26)

This round responds to the re-audits `APPROVALS/reviews/trust2.opus.md` (REJECT, attacks N1–N4) and
`APPROVALS/reviews/trust2.fable.md` (approve with notes).

**Owned here:**
- `scripts/FinalCheck.lean` and its red-team fixture (`redteam/external/patches/N4`);
- the staged proposals `staging/TRUST.md.proposed`, `staging/Final.lean.proposed` and
  `staging/claude-settings.json.proposed` (new);
- `scripts/lock.py` (`PROTECTED_FILES` only);
- `scripts/lint.py` (one rule: `partial`);
- `.github/CODEOWNERS`.

**Rules kept:**
- No protected file was touched: `TRUST.md`, `EGCheck/Final.lean`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain`, `.claude/**`.
- No Lean statement was changed.
- No git command that modifies the repository was run. (The orchestrator committed a WIP snapshot
  of the tree while this round was running; that snapshot includes part of this work.)
- Attack fixtures live only in `redteam/external/patches/N4` and in `mktemp -d` copies under
  `/tmp`. The builds ran inside the harness's read-only bind mount of the repository.
- One `lake build` ran at a time. `leanchecker --fresh` was not run: opus had already measured it
  on N4, and it caught the attack.

## 1. What changed in `scripts/FinalCheck.lean` (N4, N6)

The recommendation was trust2.opus §7 item 3. This is how each part was carried out, measured on
Lean v4.33.1 sources and on the real tree.

### 1.1 Project declarations without the attribution filter

The new `collectProjDecls` records every `(name, ConstantInfo)` of every project module's
`constNames`/`constants` pair, together with the declaring module's index.

The old `projectConstants` kept only names with `const2ModIdx[n] = this module`. `const2ModIdx`
is built with `insertIfNew`, including IR `extraConstNames`. So a module that planted an IR entry
under a name could make the kernel constant of that name "belong" to itself. The constant was then
never replayed (N4).

### 1.2 Duplicates and attribution (the `origin` check)

The check now fails in each of these cases:
- A name is declared by a project module and also by any non-project module.
- A name is declared by two or more project modules, **unless** every copy is a `.thmInfo` with
  equal type, `levelParams` and `all`.
  - That exception is exactly what `importModules` merges silently (`subsumesInfo`).
  - Lean produces such copies for **realized** lemmas.
  - The honest tree has 4:

    ```
    EG.Obj.edges.eq_1, EG.Obj.edges.eq_2   (EG.Lib.Found.Orient, EGCheck.BridgeLemmas)
    EG.cycleEdges.eq_1                     (EG.Lib.Found.Fnum, EGCheck.BridgeLemmas)
    EG.FinDist.rsubset.congr_simp          (EG.Lib.Found.ColourClass, EG.Lib.Prob.Indep)
    ```

  - So "fail on every duplicate" (opus's literal recommendation) would reject the honest proof.
    Instead, every copy is replayed and axiom-walked separately (§1.3, §1.4). Which copy a
    checker "sees" (N6) then no longer matters.
- One of the four fixed names (`Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge`,
  `SimpleGraph.IsDecomposition`, `EGCheck.erdos_184`) has any duplicate at all.
- A project module's `extraConstNames` (in the `.olean` header) names a kernel constant that the
  module does not declare.
  - The honest tree has 3 modules whose `extraConstNames` contain one of their **own** kernel
    constants. That is why the rule is "not own" rather than "any kernel constant".
- Any `const2ModIdx` entry involving a project module is inconsistent with the declaring modules,
  in either direction:
  - a project name attributed to a module that does not declare it;
  - a kernel constant attributed to a project module that does not declare it.

  This last rule acts on the effect, so it also covers the `.ir` files of module-system files.
  Their `extraConstNames` are not in `env.header` and cannot be re-read after `importModules`,
  because the region is already mapped. A measurement attempt failed with
  `'unreachable' code was reached`.

### 1.3 Replay (the `replay` check)

- Each declaring module's **own** stored `ConstantInfo` is replayed.
- The first copy in module order becomes `_egFinalCheckReplay.<n>`, which is what the renamed
  references point to.
- Further copies are replayed as `_egFinalCheckCopy.<k>.<n>`, with `all := [that name]`.
- The environment is also checked for pre-existing names under the new prefix.

### 1.4 Statement and axioms

- **Statement:** computed on the `importModules` environment, as before.
- **Axioms:** now also computed on that environment. `reachableAxioms` takes a lookup that
  returns **every** stored copy of a duplicated project theorem (`ProjDecls.look`) and follows
  all of them.
  - Before, the walk ran on the replayed (renamed) environment and followed a single copy.
  - `collectAxioms`, which follows only the kept copy, remains as a cross-check.
- **Policy:** walks the extra copies too.
- **Meta:** runs on every copy.
- **Messages:** policy and meta messages name the declaring modules, not the attributed module.

### 1.5 `unsafe` and `partial` constants

The replay skips `unsafe`/`partial` constants **by design**, and this is now documented in the
header, in `checkReplay` and in TRUST.md.proposed §2 item 1.

- `Environment.replay` does not add them.
- A replayed constant that refers to one fails with an unknown constant.

The honest tree has 2 such constants: `EGCheck.Bridge.lastOf._unsafe_rec` and
`EGCheck.Bridge.listWalk._unsafe_rec`.
- Both are compiler auxiliaries of safety `partial`, for ordinary structural definitions.
- So `policy` does **not** reject `isPartial` constants; that would reject the honest tree.

A real `partial def` is rejected three times over:
- by lint (new rule, §3);
- by `policy`, through the `@[implemented_by]` on its safe wrapper;
- by replay, for anything that uses its `_unsafe_rec`.

### 1.6 Modes and header

- `--scan-only` and `--solution-module` use the same declaration collection and run the
  duplicate/attribution part of `origin` (without the four fixed names).
- The header was corrected:
  - "A second declaration of any upstream name is an import clash" now reads "with a different
    type".
  - The replay and axioms paragraphs were rewritten.
  - A "Role" paragraph was added: defence in depth; comparator is load-bearing; the `.olean` loader
    is trusted.

### 1.7 Measurements

**Honest tree.** Measured on a `mktemp -d` copy, with a dev final: the proposed `Final.lean`
without the `#guard_msgs`, `--allow-sorry`, and pins from `staging/TRUST.md.proposed`.
- Result: `FINALCHECK: PASS (0 failures, 2 warnings)`, in 50 s, at 8.9 GB max RSS.
- `origin`: PASS, with the 4 duplicates listed above.
- `replay`: 1462 declarations re-checked, including 4 extra copies; 2 unsafe/partial constants
  skipped.
- `axioms`: exactly the three, plus `sorryAx` as a warning; `collectAxioms` agrees.
- The pins match.
- Log: scratchpad `fc/honest.log`.

**N4.** Measured on `redteam/external/redteam.sh --keep N4`, which uses the real
`EGCheck/Final.lean` and the attacker's Bridge.
- In-band: green.
- **New FinalCheck:**

  ```
  [FAIL] origin: EGCheck.RTX1 lists kernel constant EGCheck.RTX.bogus in extraConstNames without declaring it
  [FAIL] origin: EGCheck.RTX.bogus (declared by #[EGCheck.RTX2]) is attributed to (some EGCheck.RTX1)
  [FAIL] replay: kernel rejected a project constant: while replaying declaration
         '_egFinalCheckReplay.EGCheck.RTX.bogus': (kernel) declaration type mismatch ... True ... False
  ```

- **Old FinalCheck** (`fc/FinalCheck.before.lean`, same copy):
  - `origin` PASS ("5 duplicate project-internal theorems");
  - `replay` PASS;
  - `axioms` PASS.
  - Its only failures are the ambient pre-γ `sorry`s. With opus's single-module setup it printed
    `FINALCHECK: PASS`; log in `trust2.opus` §8.

So N4 is now caught by three independent rules.

## 2. External red-team (`redteam/external/redteam.sh`), full re-run

`N4` was added:
- `patches/N4/{spec,EGCheck/RTX1.lean,EGCheck/RTX2.lean,EGCheck/Bridge.lean}`;
- `EXPECT[N4]=catch`, with `EXPECT_RE[N4]='\[FAIL\] (origin|replay):.*EGCheck\.RTX\.bogus'`;
- `reset_copy` now also removes `RTX1`/`RTX2` `.olean`s;
- a row in the README table.

**Full run** (`redteam/external/redteam.sh --keep`, current committed `EGCheck/Final.lean` for the
in-band column, new FinalCheck): **`REDTEAM: PASS`, 19/19 verdicts as expected, exit 0**:

```
A  green catch catch OK   A1 green catch catch OK   A2 caught catch n/a OK   A3 green catch catch OK
B1 green catch catch OK   C  green catch catch OK   A4 green catch catch OK  D  green catch catch OK
N4 green catch catch OK   t1–t3, t5–t9 built … catch OK   t4 built catch miss OK   IO wrote/tmp catch miss OK
```

The harness credits a catch only when the attack's own defect is what the log reports
(`EXPECT_RE`). N4's log shows the two `origin` failures and the `replay` kernel mismatch quoted in
§1. The logs are in scratchpad `fc/rt_logs/`. The temporary copies were removed after the run.

**Honest re-run after all edits:** `FINALCHECK: PASS (0 failures, 2 warnings)`
(scratchpad `fc/honest2.log`). The same copy with `staging/Final.lean.proposed` as
`EGCheck/Final.lean` elaborates. It fails only at its `#guard_msgs`, on the expected pre-γ
`sorryAx`, so the docstring edit is harmless.

**Solution mode** (`--solution-module`): it now uses the same declaration collection. It passes
its own scope predicate to `origin`, so that the Solution module is not counted as a
"non-project" re-declarer of itself. This mode is still **untested**: the `Solution` library needs
`lakefile.toml.proposed`.

## 3. `scripts/lint.py`: `partial` forbidden

- `"partial": "partial def (not kernel-replayable)"` was added to `KEYWORDS`.
  - It applies to `EG/`, `EGTest/` and `EGCheck/`, which is lint's scope. That is stricter than
    asked (EG/EGCheck), and nothing in the tree uses the keyword.
  - A code comment and a docstring line give the reason.
- Three self-test cases were added:
  - `partial def`;
  - `private partial def`;
  - a doc comment containing the word "partial", which must give no finding.
- Self-test: 62/62.
- Tree:
  - Development mode: 1 finding, `EG/Proof/Found/EG0.lean:161` (`infix`). It comes from another
    agent's work in progress and is unrelated to this rule.
  - Release mode: that finding plus the 2 known `sorry`s. `BMLemma25` no longer has one.

**Proposed AGENTS.md rule 2 text** (AGENTS.md is integrator-owned; for the integrator to apply):

> 2. Forbidden anywhere in `EG/`, `EGTest/`, `EGCheck/`: `axiom`, `admit`, `native_decide`,
>    `decide +native`, `bv_decide`, `implemented_by`, `extern`, `unsafe`, **`partial`** (a `partial
>    def` is not kernel-checkable: the kernel replay of the release checks skips it by design, so
>    anything using it fails the release; use structural or well-founded recursion), `opaque`,
>    `ofReduceBool`, `trustCompiler`, `debug.*` options, `maxHeartbeats 0`, `run_cmd`/`run_elab`/
>    `run_meta`/`run_tac`, `#eval`, `modifyEnv`/`setEnv`/`addDecl`, any notation, meta attributes and
>    meta-programming identifiers, and any name with an `Erdos184` component. `sorry` is allowed only
>    where your task says so. `python3 -I scripts/lint.py` checks this.

This also folds in fable §8 item 5 (the tooling agent's list).

## 4. `staging/Final.lean.proposed` (trust2.fable §4.1)

The attack-C bullet now says precisely:
- a re-declaration is an import clash for the two definitions, or for `Erdos184.erdos_184` with
  a **different** type;
- a same-type re-declaration of a theorem is merged silently (the later module's proof wins);
  `Final.lean` cannot see it, and FinalCheck's `origin` check rejects it and its replay checks every
  copy.

The acceptance-criterion sentence now names comparator as load-bearing, with the other two checks
as defence in depth.

Only docstring text changed. Lint, run as `EGCheck/Final.lean`, gives 0 findings. SHA-256 of the
new file: `7e50b44d…`.

## 5. `staging/TRUST.md.proposed` (both audits)

- **Header:** points to the trust2 reviews and this report.
- **§2** (now 9 items):
  - Item 1: the kernel comparator **actually** runs. `release.yml` builds comparator unpatched on
    v4.35.0-rc3, without a hash pin, and this is stated. `unsafe`/`partial` are skipped by design.
  - Item 4: provenance of the pins. They were computed from Mathlib and formal-conjectures built
    from source (STATE.md, 2026-09-26).
  - Item 5: `lakefile.toml` `leanOptions` elaborate the Challenge.
  - Item 6: GitHub runners, runner images and the artifact store.
  - Item 7 (new): the trusted non-proof files of the release commit — every script,
    `redteam/**`, both workflows, the lake files, the comparator files — and **the absence** of
    `formal/lakefile.lean` and of stray `*.py` files (N1–N3).
  - Item 8: correctness of comparator's code.
  - Item 9 (new): the `.olean` loader on adversarial input, which comparator does **not** cover
    (fable §4.2).
- **§4:**
  - **4.1 Roles:** comparator is the load-bearing check. `leanchecker --fresh` and FinalCheck are
    defence in depth and do not independently establish the claim.
  - **4.2 Steps:** each step is marked implemented, partly implemented or not implemented in
    today's `release.yml`.
    - 0a gate: not wired. `pristine.sh` is in progress by a parallel agent.
    - 0b `-I`: partly implemented.
    - 0c pins: implemented.
    - 0d `comparator.sh check`: not implemented; the wrong Challenge path fails closed.
    - 0e `STATEMENT.md` diff: not implemented.
    - 0f lock: partly implemented (N2; it fails until an approved `lock.py update`).
    - 0g Challenge-closure build first: implemented.
    - 1 comparator: not as specified.
    - 2 `leanchecker --fresh`: implemented. It covers "EGCheck.Final's import closure only".
    - 3 FinalCheck: implemented, and its description is updated for N4.
    - The section ends: "no release may be claimed through `release.yml` yet".
  - **4.3:** the pin table is unchanged.
  - **4.4 (new):** a reader's minimal recipe that does not rely on repository scripts (opus §7
    item 8).
- **§6:** one protected-files table, aligned with `lock.py`, CODEOWNERS and the proposed deny
  list, with a reason for each exception.

## 6. Protection lists (aligned with TRUST.md.proposed §6)

**`scripts/lock.py` `PROTECTED_FILES`:**
- Added `STATEMENT.md`, `comparator/Challenge.lean` and `comparator/config.json`.
- Expanded at run time: `redteam/**` (was `redteam/tooling/**`) and `comparator/patches/**`.
- 92 files in all.
- The comment names TRUST §6 and lists what is unprotected on purpose: `EGCheck/Bridge*.lean`,
  `comparator/Solution.lean` and the rest of `EG/`, which are untrusted and checked by §4.
- `lock.py check --strict` will report the new paths as PENDING until the integrator runs
  `lock.py update` under an approval.

**`.github/CODEOWNERS`** (editable): added `STATEMENT.md`, `CONVENTIONS.md`,
`status/ratchet.json`, `redteam/`, `comparator/{Challenge.lean,config.json,patches/}` and
`lakefile.lean`.

**`staging/claude-settings.json.proposed`:** the current deny list plus `STATEMENT.md`,
`LOCK.json`, `lakefile.lean` and `comparator/{Challenge.lean,config.json,patches/**}`. Deliberately
**not** denied, per the §6 table:
- `scripts/**` and `redteam/**`: agents own them under explicit tasks.
- `EG/Spec/**` and `EG/Defs/**`: to be denied from the P2→P3 freeze.
- `/.github/**`: to be denied once `release.yml` implements §4. It must stay editable until then.

## 7. Still open (not in this agent's scope, or needing the user)

1. **The committed `release.yml` does not implement §4.** A parallel rewrite, the gate agent's,
   is in the working tree but not committed at the time of writing. It targets 0a, 0b, 0d, 0e, 0f
   and 1. When it lands, the "implemented" markers in TRUST.md.proposed §4.2 must be updated;
   §4.2's intro says so. Open items: step 0a (gate), the rest of 0b, 0d, 0e, and
   step 1, the comparator pins (patched v4.33.1 build via `comparator.sh`). Until they are done,
   no release may be claimed through it. The gate (`pristine.sh`) and the `-I` changes are being
   done by a parallel agent.
2. The user must approve and apply `staging/TRUST.md.proposed`, `staging/Final.lean.proposed` and
   `staging/claude-settings.json.proposed`. After that, `lock.py update` is needed under an
   approval, so that `--strict` passes.
3. CI does not run `redteam/external/redteam.sh` (the FinalCheck regression suite) or
   `FinalCheck --scan-only` (fable §8 item 4).
4. The `.olean` loader residual is only documented. The per-module sandboxed rebuild in `verify`
   is not implemented.
5. **Hygiene (opus §7 item 7).** Canon `deps` and `reachableAxioms` are not proj-aware. This is
   harmless today: all 129 proj structures are already in the closure. Changing it needs the
   `CANON` block to stay identical with `Statement.lean`, and the pins to be re-checked.
6. AGENTS.md rule 2: the proposed text is in §3.
