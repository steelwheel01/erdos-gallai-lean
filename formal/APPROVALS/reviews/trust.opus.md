# Independent audit: trust boundary (`TRUST.md`, pins, `EGCheck/Final.lean`, lint, axiom scan)

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent agent.

**What I did and did not change**
* This file is the only file I wrote in the repository.
* I ran no git command that changes anything.
* Every experiment ran on copies outside the repository, under
  `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/trust/`.
  Each copy was compiled with `lake env lean --root=<scratch> -o <scratch olean>`. The copies were
  put in front of the project's `LEAN_PATH`. `.lake/` was never written.

**What I read**
* `formal/AGENTS.md`, `TRUST.md`, `README.md`, `APPROVALS/README.md`.
* `PLAN_FORMALIZATION.md` §1, §4, §8, §9 and §13.
* `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`.
* `.github/workflows/ci.yml`, `.github/CODEOWNERS`, `.claude/settings.json`.
* All of `scripts/`, all of `EGCheck/`, and `EG/Spec/Main.lean`.
* The pinned upstream files.
* The comparator source (`leanprover/comparator` at `fd5d5bcf`, cloned to scratch).

## Verdict: REJECT

This rejects the boundary *as currently specified and enforced*. All the pins are correct. The
problems are fixable before release, and the fixes are listed in §7.

TRUST.md makes this promise: if `lake build EGCheck.Final` passes, the reader may trust exactly
what TRUST.md lists. That promise does not hold today.

I built a **byte-identical copy of `EGCheck/Final.lean`**. It compiles with exit code 0 and passes
both its `#guard_msgs` and its `run_cmd` meta-check in each of the cases below:

* **(C)** `EGCheck.erdos_184` has the trivial type `∀ _ : PUnit, 0 < Real.exp 0`. The only change
  is to the *unprotected* `EGCheck/Bridge.lean`. It uses **no meta-programming at all**.
* **(B1)** The same trivial type, obtained by overriding the `run_cmd` elaborator from the
  unprotected Bridge file.
* **(A)** The real upstream type, with a proof that depends on `sorryAx`. The `#print axioms`
  elaborator is overridden so that it prints the expected three axioms.
* **(D)** The real upstream type, with a "proof" of `False` that the kernel never saw. It comes
  from an EG-style `module` file.

In every case `python3 scripts/lint.py --release` reports **0 findings**.

The checks that *would* catch these attacks exist only as plans: `lean4checker --fresh` and
comparator (PLAN §4). TRUST.md mentions them only in passing. It does not make them the
acceptance criterion and does not pin them. The current EGCheck layout is also incompatible with
how comparator works (see §6).

---

## 1. Pins: recomputed from `.lake/packages`. All match.

| Item | TRUST.md | Recomputed | How |
|---|---|---|---|
| toolchain name | `leanprover/lean4:v4.33.1` | same | `cat lean-toolchain`, `elan show` |
| toolchain commit | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | same | `lean --version`, `lean --githash` |
| formal-conjectures commit | `2424bb480c590237ffbb2cc831ae4cb8977e045a` (2026-09-24) | same; commit date Thu Sep 24 19:42:19 2026 | `git -C … rev-parse HEAD`, `git log -1` |
| `184.lean` blob | `36cc140cb3d8e60b08a842f1691fe9b73602f92b` | same | `git hash-object`, and `git ls-tree HEAD` |
| `184.lean` SHA-256 | `9f36e4e0…d6` | same | `sha256sum` |
| `Decomposition.lean` blob | `a4d3f066158b799e851dd8c6ac511ef2b6731111` | same | `git hash-object`, `git ls-tree HEAD` |
| `Decomposition.lean` SHA-256 | `86bf339a…f2` | same | `sha256sum` |
| Mathlib commit | `0df444a360eaa60ab8c11dca51a86af692955474` (tag `v4.33.1`) | same; `git tag --points-at HEAD` = `v4.33.1` | `git rev-parse` |
| manifest revs (FC, Mathlib) | as above | same | JSON |

* All 10 packages in `lake-manifest.json` have `HEAD` equal to their manifest `rev`.
* All 10 have a clean working tree (`git status --porcelain --untracked-files=all` is empty).
* `./scripts/check_pins.sh` prints 7 × `pin ok` and exits with code 0.
* The statement text quoted in TRUST.md matches upstream `184.lean` line for line. This includes
  the `open scoped Classical` and the `IsCycleOrEdge` and `IsDecomposition` paraphrases.

## 2. `scripts/check_pins.sh`: what it checks and what it does not

It checks:
* the `lean-toolchain` *text*;
* `git rev-parse HEAD` of FC and of Mathlib;
* the SHA-256 of the two FC files;
* the two manifest revs.

It does not check the following.

1. **The toolchain commit.** TRUST.md item 1 pins commit `819816b2…`, but only the *name* in
   `lean-toolchain` is checked. The binary that actually runs is never checked. Add
   `lean --githash`; I confirmed it prints `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
2. **Working-tree tampering.** `rev-parse HEAD` does not look at the working tree. I made a
   scratch `git clone --shared` of FC and Mathlib at the pinned commits. I appended text to
   `Mathlib/Combinatorics/SimpleGraph/Subgraph.lean` and to `FormalConjecturesUtil.lean`. The copied
   `check_pins.sh` still printed 7 × `pin ok` with exit code 0. `git status` showed the change.
   Only the two hashed files are protected. Every other file that feeds the statement is not.
3. **Transitive packages.** Batteries, Aesop, Qq, ProofWidgets, Plausible, importGraph,
   LeanSearchClient and Cli are pinned only in the manifest. Nothing checks them. Batteries is
   in the *semantic* closure of the statement; see §5.
4. **The FC `rev` in `lakefile.toml`.** It is not compared with the pin.
5. **Build products.**
   * Mathlib `.olean`s come from `lake exe cache get`, a download.
   * FC and project `.olean`s may be restored by `actions/cache` with a `restore-keys` prefix
     (`ci.yml`).
   * Nothing checks that these files come from the pinned sources.
6. The git blob ids in TRUST.md are never checked. The SHA-256 checks cover the same content, so
   this is harmless, but one of the two should be dropped.

## 3. `EGCheck/Final.lean`

### 3.1 What it does

* **The statement is exact.** The theorem is `EGCheck.erdos_184.{u} : type_of%
  @Erdos184.erdos_184.{u}`, so it is exactly the type of whatever constant that name resolves to.
* **The axiom list must match exactly.** The `#guard_msgs` block demands exactly
  `[propext, Classical.choice, Quot.sound]`. In v4.33.1, `#print axioms` sorts the list by
  `Name.lt` (`Lean/Elab/Print.lean:245`), so the order is deterministic.
* **The meta-check is strict.**
  * It uses `Expr.equal`, which compares binder names and binder annotations
    (`Lean/Expr.lean:814-819`).
  * It compares the number of universe parameters, and instantiates them by position.
  * I tested this in scratch (`Strict.lean`) with four restatements, compared the way Final.lean
    compares:

    | Restatement | Result |
    |---|---|
    | the verbatim upstream text, restated in another module | `DIFFERENT`: hygienic instance binder names `inst._@.FormalConjectures.ErdosProblems.184…` differ; `eqv` is true |
    | `(V : Type*)` explicit | `DIFFERENT` |
    | `V : Type` | "universe parameter counts differ" |
    | the `type_of%` form | `EQUAL` |

  So the check can only be met by `type_of%` of the very constant it compares against.

### 3.2 Attacks (each on a byte-identical copy of Final.lean; `cmp` confirmed identical)

Scratch directories are `A/ B/ C/ D/`, and each has an output directory `*o/`.

**B0: namespace shadowing (caught).**
* The attacker's Bridge declares `EGCheck.Erdos184.erdos_184` with a weak statement.
* `theorem EGCheck.erdos_184 : type_of% @Erdos184.erdos_184.{u}` is elaborated with namespace
  `EGCheck` open, so the name **resolves to the attacker's constant**. The theorem elaborated, and
  `#guard_msgs` passed.
* The `run_cmd` check rejected it: `EGCheck.erdos_184 and Erdos184.erdos_184 have different
  statements`.
* The meta-check earns its place here. `_root_.` would stop this attack outright.

**C: fake upstream constant, no meta-programming (NOT caught).**
* `Final.lean` does not import the upstream module. It gets `Erdos184.erdos_184` only through
  `EGCheck.Bridge`.
* My scratch `EGCheck/Bridge.lean` imports only `Mathlib.Analysis.SpecialFunctions.Exp` and
  declares:
  ```lean
  theorem Erdos184.erdos_184.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 := fun _ => Real.exp_pos 0
  theorem EGCheck.Bridge.solution.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 := fun _ => Real.exp_pos 0
  ```
* Final.lean then compiles with exit code 0. `type_of%`, `#guard_msgs` and `run_cmd` all compare
  against the fake constant.
* `lint.py --release` reports 0 findings. `lint.py` limits which files may *import*
  FormalConjectures. It does not limit which files may *declare* names in `Erdos184`.

**B1: `run_cmd` neutralised (NOT caught).**
* I added three lines to the attacker's Bridge from B0:
  `@[command_elab Lean.runCmd] def EGCheck.Bridge.skipRunCmd : CommandElab := fun _ => pure ()`.
* Imported command elaborators take priority over the builtin ones. Result:
  * Final.lean compiled with exit code 0;
  * `#check @EGCheck.erdos_184` gives `∀ (x : PUnit.{u_1 + 1}), 0 < Real.exp 0`;
  * `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]`.

**A: `#print axioms` spoofed (NOT caught).**
* I took the real `Bridge.lean` and appended a
  `@[command_elab Lean.Parser.Command.printAxioms]` elaborator. It logs
  `'<id>' depends on axioms: [propext, Classical.choice, Quot.sound]`.
* Final.lean compiled with exit code 0 **today**, although `EG.Proof.mainInternal` is `sorry`.
* **The same works from a `module` file (EG/\*\*).** `public meta import Lean` plus a
  `@[command_elab Lean.runCmd] meta def …` in scratch `M/EGZ/Hook.lean` made
  `run_cmd throwError "…"` in an importing file compile with exit code 0.

**D: kernel bypass in an EG-style `module` file (NOT caught in-band).**
* `D/EGW/Lemma.lean` (`module`, `public meta import Lean`) defines a command with `elab`. The
  command calls `addDecl` under `withOptions (·.setBool (Name.mkStr (Name.mkSimple "debug")
  "skipKernelTC") true)`. It adds `EGW.helper : False := True.intro`.
* The unmodified-looking Bridge proves the **real** upstream type with `have := Real.exp_pos 0;
  exact EGW.helper.elim`.
* Byte-identical Final.lean: exit code 0, with exactly the three axioms.
* The same bypass works in several other forms:
  * inside an ordinary proof, via the core tactic `run_tac` (scratch `F/EGU/RunTac.lean`; the
    helper must be named under the theorem's prefix);
  * via `set_option «debug».skipKernelTC true in` plus a tactic that assigns an ill-typed term
    (`Bypass1.lean`);
  * via `#eval show CommandElabM Unit from …`, which persists changes to the environment.

**Build-time I/O.** A `module` file containing `#eval IO.FS.writeFile "<path>" …` compiled with
exit code 0 and wrote the file. The lint reports 0 findings. Any EG module can therefore rewrite,
*during `lake build`*, any of the following:
* `scripts/*.py` and `scripts/*.lean`;
* `LOCK.json`;
* the FC `184.olean` that later modules compare against.

In CI, `lake build` runs before the axiom scan, the lock check and the final check.

### 3.3 Which checks catch which attack (measured)

| Attack | lint `--release` | `Axioms.lean --no-sorry` | env meta-scan (prototype, §7) | out-of-band `FinalCheck.lean` (prototype, §7) | `leanchecker` (non-fresh) on the attack module | `leanchecker EGCheck.Final` (non-fresh) | `leanchecker --fresh EGCheck.Final` | comparator |
|---|---|---|---|---|---|---|---|---|
| A (spoofed axioms, sorry) | miss | **catch** (`uses sorryAx`) | **catch** | **catch** | miss | miss | miss² | catch¹ |
| B1 (run_cmd hijack) | miss | miss | **catch** | **catch** (statement differs) | miss | miss | miss² | catch¹ |
| C (fake `Erdos184.erdos_184`) | miss | miss | miss | **catch** (import clash) | miss | miss | miss² | catch¹ |
| D (kernel bypass) | miss | miss | **catch** (elab/parser consts) | miss | **catch** (`declaration type mismatch`) | **miss** | **catch** (measured) | catch¹ |
| D′ (`run_tac` bypass) | miss | miss | **miss** | miss | **catch** | miss | catch² | catch¹ |

¹ This is by design: comparator re-derives the statement from an independently built Challenge,
walks the axioms of the solution's exported environment itself, and replays that environment in
the kernel. I did not run it; it needs landrun and lean4export.
² I did not run this case; the entry follows from the design. leanchecker checks only that each
declaration is well-typed in the kernel. It does not check which axioms are used or what the
statement is. It replays every constant, so it catches any bypassed declaration.

* `leanchecker` ships with the toolchain (`~/.elan/toolchains/…/bin/leanchecker`).
* **`leanchecker --fresh EGCheck.Final` on attack D catches it.** Its message is `while replaying
  declaration 'EGW.helper': (kernel) declaration type mismatch`, with exit code 1. It took
  **21 min 16 s** of wall-clock time, single-threaded, with a **maximum RSS of 10.2 GB**
  (`/usr/bin/time -v`, log in `fresh_D.log`).
* **Plan release CI for this:** a GitHub-hosted runner for a private repository may be too
  small. Use a runner with ≥ 16 GB RAM.
* Note that **non-fresh `leanchecker EGCheck.Final` misses D**. It replays only Final's own
  constants. Either replay every project module (`leanchecker EG`, `EGTest`, `EGCheck`) or use
  `--fresh`.

### 3.4 Other attack vectors I considered

* **Instances, notation, scoped `open`, options in imports.** These cannot change the theorem.
  `type_of%` elaborates no instances. Options are not inherited through imports.
* **Local overrides of Mathlib or upstream names.** These are impossible, because an import clash
  is an error (see C and the prototype check). The only exception is when the upstream module
  is *not* imported, which is exactly attack C.
* **`@[implemented_by]`, `@[extern]`, `@[csimp]`.**
  * They affect only compiled code.
  * `implemented_by` cannot be attached to an imported declaration.
  * `csimp` needs a proof of equality, so it is dangerous only together with a kernel bypass.
  * In compiled code they can influence two things. The first is `native_decide`: in v4.33.1 it
    adds an auxiliary *axiom*, `EGX.n1._native.native_decide.ax_1_1`, which `#print axioms`, the
    axiom scan and comparator all see. The second is the in-band meta-checks, which are already
    shown to be spoofable in other ways.
* **`decide +kernel` and kernel reduction.** These are sound: no axioms, and the kernel checks
  them. They are a denial-of-service risk only.

## 4. `scripts/lint.py` and `scripts/Axioms.lean`

### 4.1 Lint evasions

Each item below was tested in a scratch tree with a copy of `lint.py`. Each compiles in Lean
v4.33.1.

* **L1. A character literal hides everything after it.** `strip()` (lines 41-73) treats the `"`
  in `'"'` as the start of a string. It then deletes everything up to the next `"`.
  * The scratch file contained `def q : Char := '"'`, then `axiom EGX.bad : False`, then
    `theorem … := by native_decide`, then `set_option debug.skipKernelTC true`, then
    `def r : String := "x"`.
  * The lint reported 0 findings, and `lean` exited with code 0.
* **L2. The `axiom` pattern `(^|\s)axiom\s` (line 20) is too narrow.** It misses:
  * `axiom` at the end of a line (lines are split before matching);
  * `@[simp]axiom`;
  * `(axiom …` inside quotations.
* **L3. The `\bdebug\.` pattern misses other spellings.** It misses `«debug».skipKernelTC` (used
  in `Bypass1.lean`) and option names assembled from strings or `Name.mkStr`.
* **L4. The `maxHeartbeats\s+0\b` pattern** misses `«maxHeartbeats» 0` and `maxHeartbeats 00`.
* **L5. Nothing covers code-running constructs.** None of these is checked:
  * `run_tac`, `by_elab`, `#eval`, `#eval!`, `#guard`;
  * `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`;
  * `initialize`, `builtin_initialize`;
  * `@[command_elab]`, `@[term_elab]`, `@[tactic]`, `@[csimp]`, `meta def`, `meta import`;
  * `withOptions`, `addDecl`, and `modify fun s => { s with env := … }`, which mutates the
    environment without the words `modifyEnv` or `setEnv`.

  This is the root cause of A, B1, D and D′.
* **L6. The FormalConjectures import rule (line 101) only looks at the start of a line.** It
  misses `meta import`, `import all`, a second `import` on the same line, and an `import` whose
  module name is on the next line.

### 4.2 Limits of the axiom scan

* **It trusts a table stored in the project's own `.olean` files.** In v4.33.1, `collectAxioms`
  does not walk the bodies of imported declarations. It reads a table of axioms for each module,
  computed when that module's `.olean` is written (`exportedAxiomsExt`,
  `Lean/Util/CollectAxioms.lean:88-140`). So both `#print axioms` and `scripts/Axioms.lean`
  trust tables written by the compilation of untrusted project modules.
* **What it does and does not catch.**
  * It reliably catches honest `sorry`, `axiom`, `native_decide`, `unsafe`, `extern` and
    `implemented_by`.
  * It cannot catch kernel bypasses (D, D′) or spoofed elaboration (B1, C).
  * Comparator, which walks the exported environment itself (`Comparator/Axioms.lean`), is the
    independent check.
* **Two gaps in how CI calls it.**
  * CI never runs it on `EGCheck.Final`, which is not in the `EGCheck` root.
  * CI never passes `--no-sorry`. That is expected before P4, but the release job must do both.

## 5. What TRUST.md is missing, and whether the staged trust is coherent

### 5.1 The semantic closure of the upstream statement

I measured it with scratch `Closure.lean` and `StmtHash.lean`, on the pinned build. It is the
constants reached from types, definition bodies and constructors:
* 1563 constants in total;
* **Init (Lean core) 614, Mathlib 940, Batteries 6, FC 3.**

The three FC constants are `Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge` and
`SimpleGraph.IsDecomposition`. Nothing else from FC reaches the elaborated statement. The six
Batteries constants are `RatCast`, `RatCast.mk`, `RatCast.ratCast`, `Rat.cast`, `instRatCastRat`
and `congr_arg`.

### 5.2 Items TRUST.md should list

1. **The definitions in Lean core (`Init`) and Batteries.** Both are in the closure. Name them next
   to Mathlib, with the Batteries commit `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d`.
2. **The elaborated statement itself.**
   * A reader who reads the text also trusts that elaborating the pinned text gave the `Expr` that
     is checked. That elaboration runs every macro, elaborator and instance of Mathlib, FC,
     Batteries, Aesop, Qq, ProofWidgets and Plausible. `FormalConjecturesUtil` imports all of
     Mathlib and all of FormalConjecturesForMathlib.
   * TRUST.md should say this explicitly: "the statement as elaborated from the pinned file in an
     environment containing only the pinned upstream closure (no project code)".
   * It should also publish that `Expr` (for example as an `AXIOMS.md`-style appendix) with a
     hash pin. The elaborated type is the `dbgToString` output in `Closure.lean`. Its SHA-256 on
     this build is `33e213279405c3580cb185430dcb66f5ec7caa6e7bd150731e000ad6a928012d`. The
     deterministic dump of the whole closure has SHA-256
     `a6decb644ad3af0bdf80df7593538619481ba0e567400397b1faa344bddcab47`: 1572 rows, including
     `opaque` bodies. I reproduced it twice.
   * This hash pins the *meaning* (every definition the statement reaches), not just two files. It
     also catches tampering in the working tree or in the `.olean` files.
3. **Build inputs.**
   * The Mathlib `.olean` cache (`lake exe cache get`). Comparator's README says the same thing:
     using the cache means trusting it. The alternative is a release build from source.
   * Lake, which fetches packages by SHA-1 commit and runs the `lakefile.lean` of Mathlib and
     ProofWidgets.
   * The elan installer, which CI pipes from `elan/master` without a pin.
   * The GitHub Actions `@v4` tags, which are mutable.
4. **Release checkers, pinned.**
   * `leanchecker` (bundled, so it is covered by the toolchain pin).
   * comparator (commit), lean4export (commit; it must support v4.33.1, while comparator `master`
     itself now builds on v4.35.0-rc3), landrun (commit), and nanoda if it is used.
   * Comparator's own stated assumptions. The Challenge's import closure must be built **before**
     any project code is compiled. The solution build runs under landrun, via `systemd-run` as the
     README shows. The checker must not run as a privileged user.
5. **The Lean compiler and interpreter.** They matter only for the in-band checks and for the
   `lean --run` scripts. Once the acceptance criterion is out-of-band (§7), TRUST.md should say
   plainly that `#guard_msgs` and `run_cmd` in Final.lean are a developer convenience and not part
   of the trust argument.

### 5.3 Is the staged trust (α/β/γ) coherent?

The PLAN and TRUST.md agree on the principle that only γ may be called "formally verified", but
four points are not coherent as written.

* **There is no stage-α artifact.** Final.lean demands the *unconditional* upstream type, so it
  cannot pass at α. TRUST.md defines neither the α claim nor where it is checked.
* **At α, the hypothesis texts are trusted and must be listed.** Suppose the three classical
  hypotheses are wrong: stronger than the literature, or false. Then the α theorem is vacuous.
* **The "Not trusted" paragraph is false at α.** At α, the EG definitions that the hypotheses
  mention *are* trusted. `EG/Spec` has no Lovász, Haxell or Euler statement yet.
* **Even at γ, "Not trusted" holds only under a condition.** It holds only under an out-of-band
  acceptance criterion (§3). Under the present "How to check", untrusted EG and EGCheck code
  decides the outcome.

### 5.4 Smaller inaccuracies

* **TRUST.md line 62.** It says the build "must print" the axiom line. It does not: `#guard_msgs`
  consumes matching messages, so a passing build prints nothing for it. It does print a
  Mathlib `linter.style.moduleDocstring` warning at Final.lean:18, because of the second `/-! -/`.
* **The lakefile comment** says "enforced by scripts/lint.sh". The script is `lint.py`.
* **LOCK coverage.** `LOCK.json` / `lock.py` hash `EGCheck/Final.lean`, the lake files and
  TRUST.md. They do not hash `scripts/**`, `.github/workflows/ci.yml` or
  `.claude/settings.json`, which the checks depend on. Only CODEOWNERS covers those.
* **`.claude/settings.json`** denies only `Edit(...)`. Bash writes are not covered. That is fine
  for defence in depth, but it should be stated.

## 6. Comparator vs. the current EGCheck layout (design issue for P4)

* **Comparator requires the Solution module to declare the *same* theorem name**
  (`Erdos184.erdos_184`). It compares each constant the statement uses (`Erdos184.IsCycleOrEdge`
  and every Mathlib definition) against the Challenge with `ConstantInfo` BEq; see
  `Comparator/Compare.lean` in the scratch clone.
* **Its `Expr` equality is `eqv`.** It ignores binder names and binder info. So a verbatim
  restatement matches even though the hygienic names differ.
* **The layout therefore has to change.** The Solution must restate `IsCycleOrEdge` and
  `erdos_184` itself. Nothing it imports may import `FormalConjectures.ErdosProblems.«184»`, or the
  two declarations clash. Today `EGCheck/Bridge.lean` and `EGCheck/BridgeLemmas.lean` both import
  it.
* **Plan the refactor and a comparator dry run now:** bridge lemmas stated against the unfolded
  `IsCycleOrEdge` body, and a `Solution.lean` shaped like `Challenge.lean`. Run comparator once
  with `sorryAx` temporarily permitted, to test the plumbing.

## 7. Recommended changes (for the integrator; items marked † change the trusted boundary)

**Blocking before any "Final passes" claim**

1. **† Rewrite the acceptance criterion in TRUST.md ("How to check").** A release is accepted only
   if all of the following hold, run in a fresh environment with no restored `.lake` caches:
   * comparator, configured per its README assumptions (`Challenge.lean` byte-identical to the
     pinned `184.lean`, `theorem_names = ["Erdos184.erdos_184"]`, `permitted_axioms` = the three;
     nanoda optional);
   * `leanchecker --fresh EGCheck.Final` (or `leanchecker EG EGTest EGCheck`, per module);
   * an out-of-band `lean --run scripts/FinalCheck.lean` (item 3).

   The `#guard_msgs` and `run_cmd` in Final.lean become explicitly advisory. Also pin comparator,
   lean4export and landrun.
2. **† Harden `EGCheck/Final.lean`.**
   * Make the first import `FormalConjectures.ErdosProblems.«184»`, so that any other
     `Erdos184.erdos_184` is an import clash. This defeats C.
   * Write `type_of% @_root_.Erdos184.erdos_184.{u}`. This defeats B0 even without the meta-check.
   * In `run_cmd`, require both constants to be `.thmInfo`, and check the source module of
     `Erdos184.erdos_184` and `Erdos184.IsCycleOrEdge` (`FormalConjectures.ErdosProblems.«184»`)
     and of `SimpleGraph.IsDecomposition`
     (`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Decomposition`).
   * Turn the second `/-! -/` into `/- -/`.
3. **Add `scripts/FinalCheck.lean`**, modelled on my prototype `FinalCheck.lean`. It uses
   `importModules` of FC 184 *and* `EGCheck.Final`, so no project elaborator or initializer runs.
   It checks source modules, strict type equality (as in Final.lean), and
   `collectAxioms ⊆ {propext, Classical.choice, Quot.sound}`. Measured on the attacks: A FAIL
   (`sorryAx`), B FAIL (statement differs), C FAIL (import clash), D PASS. That result is why
   item 1 also requires leanchecker.

**Strongly recommended**

4. **Extend `check_pins.sh`.**
   * `lean --githash` = `819816b2…`.
   * For **every** package in the manifest: `HEAD` = manifest `rev` and
     `git status --porcelain --untracked-files=all` empty.
   * The FC `rev` in `lakefile.toml` = the pin.
   * † A statement and closure hash pin, computed by a `lean --run` script like `StmtHash.lean`
     (values in §5.2).
5. **† TRUST.md content.**
   * List Init and Batteries (with its commit) next to Mathlib.
   * List the Mathlib cache or a from-source build, Lake, and the release checkers with their
     versions and comparator's assumptions.
   * Publish the elaborated statement (`Expr`) and its hash.
   * Add a stage-α section. It names the α artifact (e.g. a protected `EGCheck/FinalAlpha.lean`
     checking `Lovasz → Haxell → Euler → type_of% @_root_.Erdos184.erdos_184`). It lists the three
     hypothesis Props (locked Tier-1 in `EG/Spec/Classical.lean`) as trusted *at α and β*. It
     notes that "Not trusted: EG" holds only at γ, under the out-of-band criterion.
   * Correct "must print" to "must succeed".
6. **Add a lint-independent environment scan to `scripts/Axioms.lean`.**
   * Flag any constant from an `EG*` or `EGCheck` module whose type mentions any of: `Lean.Elab`,
     `Lean.Meta`, `Lean.Macro*`, `Lean.Syntax`, `Lean.Parser`, `Lean.ParserDescr`,
     `Lean.TrailingParserDescr`, `IO`, `EIO`, `BaseIO`, `Lean.Environment`, `Lean.CoreM`,
     `Lean.Expr`, `Lean.Declaration`, `Lean.Kernel`.
   * My prototype `MetaScan.lean` found **0 hits on the current 1530 EG/EGTest/EGCheck
     constants** and flagged A, B1 and D.
   * Also flag constants registered under `[init]` or `[csimp]`.
7. **Fix the lint (defence in depth; it is not a soundness tool).**
   * Use a real tokenizer that handles `'"'`, raw strings, and `«»` normalisation (fixes L1, L3,
     L4).
   * Use `\baxiom\b` (L2).
   * Use an *allowlist* for `set_option`: `maxHeartbeats N` with 0 < N ≤ 10⁶, `maxRecDepth`,
     `synthInstance.*`, `linter.*`, `pp.*`.
   * Ban `run_tac`, `by_elab`, `#eval`, `#eval!`, `#guard`, `elab`, `elab_rules`, `macro`,
     `macro_rules`, `syntax`, non-`local` `notation`, `initialize`, `builtin_initialize`,
     `meta def`, `meta import`, and `@[command_elab|term_elab|tactic|csimp|init]` in
     EG/EGTest/EGCheck (Final.lean excepted) (L5).
   * Check FormalConjectures imports on the parsed header, not line by line (L6).
8. **CI.**
   * Run check_pins, lint, lock and the scans from a pristine copy of `scripts/`, taken *before*
     `lake build`, or run `git diff --exit-code` after the build. The build executes arbitrary
     project code.
   * Add `leanchecker EG EGTest EGCheck` (non-fresh; cheap) to regular CI.
   * In the release job, do not restore `actions/cache` for `.lake/build` or FC's `.lake`, pin
     actions and the elan installer by SHA, and build the Challenge closure before compiling any
     project module.
   * Add `scripts/**`, `.github/workflows/**` and `.claude/settings.json` to the lock's
     `PROTECTED_FILES`.
9. **Redesign EGCheck for comparator (§6).** The Solution restates upstream verbatim and imports a
   bridge core that does not import `…ErdosProblems.«184»`. Do a comparator dry run in P2, not at
   P4.
10. **Housekeeping.** Remove `EGCheck/Smoke.lean` before release (the release lint already flags
    it). Correct the lakefile comment (`lint.py`).

## 8. Scratch evidence index

All paths are relative to
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/trust/`.

* **Pins and statement closure:** `Closure.lean`, `StmtHash.lean`, `closure_dump.tsv`.
* **`leanchecker --fresh` log for attack D:** `fresh_D.log`.
* **Pin blind spot:** `pins/` (a tampered working-tree clone that passes `check_pins.sh`).
* **Type-comparison strictness:** `Strict.lean`.
* **Attacks on byte-identical Final.lean:**
  * `A/` (spoofed axioms);
  * `B/` (B0 caught, then B1);
  * `C/` (fake upstream constant);
  * `D/` (kernel bypass in a module file).
* **Other bypasses:**
  * `M/` (elaborator hijack from a `module` file);
  * `F/` (`run_tac` bypass);
  * `Bypass1.lean` and `BypassMod.lean` (bypasses caught by leanchecker);
  * `E/` (build-time I/O).
* **Lint evasions:** `lt/` to `lt5/`, `Evasions2.lean`, `Char.lean`, `Native.lean`.
* **Prototype checks:** `FinalCheck.lean`, `MetaScan.lean`.
* **Comparator source:** `../comparator/`.
