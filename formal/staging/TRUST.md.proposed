# TRUST.md — what a reader must trust

Status: **DRAFT — pre-release; the acceptance procedure has not yet been exercised on GitHub.**
The proof is incomplete (see `status/STATUS.md`), so nothing described here has passed yet. This
file fixes the trusted boundary in advance (PLAN_FORMALIZATION.md §1). Any change to this file, to
the pins below, to the allowed axioms or to the acceptance criterion is a trusted-boundary change
and needs the user (PLAN §9).

History. The version of 2026-09-25 was rejected by two trust audits
(`APPROVALS/reviews/trust.{opus,fable}.md`): its checks ran inside the Lean elaborator, which any
imported module can override. The hardened setup was re-audited twice:
* round 2, `trust2.{opus,fable}.md`: attacks N1–N4;
* round 3, `trust3.{opus,fable}.md`: the design is sound, but the text was stale and there were
  three enforcement gaps (Landlock not self-verified, `EG_TRUST_REF` accepted a movable tag,
  `status.py` wrote into the read-only snapshot).

This revision describes the implementation at the revision of §7, with one kind of exception: a
sentence that names a staged proposal (`staging/*.proposed`) describes that proposal, which is
applied together with this file (§8 item 9). Each sentence was checked against the committed
`.github/workflows/{release,ci}.yml`, `scripts/pristine.sh`, `scripts/FinalCheck.lean`,
`scripts/comparator.sh`, `scripts/lock.py` and `scripts/lint.py`. What is still missing before a
release claim is listed in §8. Work notes:
* `work/trust/consolidate.md` and `work/trust/docfix.md` (this revision);
* `work/trust/{gate2,finalcheck2,tooling,bridge,external}.md` (earlier rounds).

## 1. The claim being checked

The claim is a kernel-checked proof of `Erdos184.erdos_184` from
google-deepmind/formal-conjectures. It may use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The statement is **as elaborated from the pinned file, in an environment that
contains only the pinned upstream closure (no project code)**. The text is

```
open scoped Classical in
theorem erdos_184 :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)
```

It lives in namespace `Erdos184` under `open Filter SimpleGraph`. The two definitions it uses are:
* `IsCycleOrEdge H := open scoped Classical in (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1`;
* `IsDecomposition G D`: the edge sets of the members of `D` are pairwise disjoint and their union
  is `G.edgeSet`.

**The statement a reader actually trusts is the elaborated one, `STATEMENT.md`.** It is generated
by `lake env lean --run scripts/Statement.lean` from the pinned build, importing only
`FormalConjectures.ErdosProblems.«184»`. It contains:
* the `pp.all` forms of `Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge` and
  `SimpleGraph.IsDecomposition`;
* the constants they use;
* the closure of the statement: 1572 declarations (`Init` 614, Mathlib 949, Batteries 6,
  formal-conjectures 3).

Its canonical serialisations are pinned here. The lines are machine-readable: `scripts/FinalCheck.lean`
reads them from this file by default.

    EG-PIN lean-githash 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
    EG-PIN statement-sha256 4cb2cd5697e7916ea244e8b58041fcb2c7fa4338621335eeeb3a1d05452f6734
    EG-PIN closure-sha256 39d6e8c358b1482f9af513370d6edfba52da96857fa1066a309fa87c0ccf66fd

The closure pin fixes the *meaning* of the statement: every definition it unfolds to, not only
the two upstream files. It therefore also detects tampered package working trees or `.olean`
files.

Two artifacts carry the claim. Both are derived from the same kernel-checked bridge,
`EGCheck.Bridge.of_mainInternal_unfolded` (`EGCheck/BridgeCore.lean`), applied to
`EG.Proof.mainInternal`:
* `EGCheck.erdos_184` in the protected `EGCheck/Final.lean`. In the version proposed in
  `staging/Final.lean.proposed`, which is applied together with this file (§8 item 9), its type is
  `type_of% @_root_.Erdos184.erdos_184.{u}` and the upstream module is imported first and
  directly. The committed `EGCheck/Final.lean` (at the revision of §7) still imports only
  `EGCheck.Bridge`, uses `type_of% @Erdos184.erdos_184.{u}`, and its `run_cmd` only compares the
  two statements;
* `Erdos184.erdos_184` in `comparator/Solution.lean`. This is comparator's Solution for the
  Challenge `comparator/Challenge.lean`, which is a byte-identical copy of the pinned `184.lean`.

## 2. Trusted components (complete list)

1. **The Lean kernel** of toolchain `leanprover/lean4:v4.33.1` (commit
   `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). Three checkers run it:
   * `leanchecker`;
   * `scripts/FinalCheck.lean`, through `Environment.replay`;
   * comparator. `scripts/comparator.sh tools` builds comparator with this same toolchain plus the
     patch of §4.4, and release.yml's `comparator` job uses exactly that build.

   No other kernel is used. If comparator is ever run with an external kernel (nanoda), that kernel
   must be added here.

   `Environment.replay` skips `unsafe` and `partial` constants **by design**, so FinalCheck and
   comparator's replay skip them too. Two consequences:
   * such constants are unusable by any replayed declaration, because a reference to one fails the
     replay;
   * the project may not declare them. `scripts/lint.py` forbids `unsafe` and `partial`, and
     FinalCheck's policy forbids `unsafe`, `@[implemented_by]` and `@[extern]`.
2. **The axioms** `propext`, `Classical.choice` and `Quot.sound`, and no others.
3. **The text of the upstream statement** and the definitions it uses, at the pinned commit:
   - repository: https://github.com/google-deepmind/formal-conjectures
   - commit: `2424bb480c590237ffbb2cc831ae4cb8977e045a` (2026-09-24)
   - `FormalConjectures/ErdosProblems/184.lean`: git blob `36cc140cb3d8e60b08a842f1691fe9b73602f92b`,
     SHA-256 `9f36e4e053285cd8b886042eb609ace5f21f49bd81903eebca8000ff03e020d6`.
     `comparator/Challenge.lean` is byte-identical to it (checked by `scripts/comparator.sh check`).
   - `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`: git blob
     `a4d3f066158b799e851dd8c6ac511ef2b6731111`, SHA-256
     `86bf339ad988733c67e443e7fc922bbc278fc48871f7e9ba515f0659d8fceff2`
4. **The definitions in the closure of the statement.** They are listed in `STATEMENT.md` and
   pinned by `closure-sha256`:
   - Lean core `Init` of the toolchain in item 1;
   - Batteries `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d`, 6 declarations: `RatCast`,
     `RatCast.mk`, `RatCast.ratCast`, `Rat.cast`, `instRatCastRat`, `congr_arg`;
   - Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (tag `v4.33.1`): `SimpleGraph`,
     `Subgraph`, `Connected`, `IsRegularOfDegree`, `edgeFinset`, `Asymptotics.IsBigO`, `Real`, …;
   - formal-conjectures (item 3): `Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge`,
     `SimpleGraph.IsDecomposition`.

   **Provenance of the pins.** `statement-sha256` and `closure-sha256` were computed on 2026-09-26
   by `scripts/Statement.lean`:
   * Mathlib v4.33.1 was built **from source** in this project's sandbox. `lake exe cache get` was
     not used because the cache hosts were unreachable (STATE.md, "P0 — DONE": 2 h 29 min on 4
     cores).
   * formal-conjectures was built from source at the commit of item 3.

   This is what ties the closure pin to the pinned *sources*. Every job of `release.yml` uses the
   Mathlib `.olean` cache, and relies on this pin, and on comparator's own Challenge build (item 9),
   to detect a cache that does not match the sources.
5. **The elaboration of the pinned text into the checked `Expr`.** This is the Lean v4.33.1
   frontend with the import closure of `184.lean`:
   * `FormalConjecturesUtil`, hence all of Mathlib;
   * the other modules it imports, all from the packages of `lake-manifest.json` at the commits
     recorded there. The manifest lists ten packages, and Lake fetches all of them: `mathlib`,
     `formal_conjectures` (which also provides FormalConjecturesForMathlib), `plausible`,
     `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries` and `Cli`.

   It runs **with the project's `lakefile.toml` `leanOptions`**, because comparator builds the
   Challenge in this package. The option `maxSynthPendingDepth = 3` is set there and not in
   formal-conjectures' own `lakefile.toml`, the package that elaborates `184.lean` upstream.
   (Mathlib's `lakefile.lean` sets the same value for Mathlib's own modules.)
   The audit measured that the Challenge compiled this way equals the upstream-built constants up
   to binder names, which is what comparator compares.

   A reader who does not want to trust this elaboration reads `STATEMENT.md` instead of the source
   text; the pins of §1 tie the two together.
6. **Build and cache infrastructure.**
   - Lake, bundled with item 1. It fetches the ten packages by the commits in `lake-manifest.json`
     and runs the `lakefile.lean` of Mathlib and of ProofWidgets. `scripts/check_pins.sh` checks,
     in every job of `release.yml`:
     * every package's `HEAD` and a clean working tree;
     * the `lakefile.toml` and manifest revs;
     * `lean --githash`.
   - The Mathlib `.olean` cache (`lake exe cache get`). All three jobs of `release.yml` use it.
     `leanchecker --fresh` re-checks those `.olean`s in the kernel, but only for the import closure
     of `EGCheck.Final`. Only `closure-sha256` (item 4) ties the statement's definitions to the
     pinned *sources*.
   - In the workflows:
     * the elan installer v4.2.4 and the Lean v4.33.1 release archive, both SHA-256-pinned;
     * GitHub Actions pinned by commit SHA;
     * git's SHA-1 commit ids;
     * the runner image's `python3`, `bash`/`sh`, coreutils, findutils, `grep`, `sed`, `awk`,
       `diff`/`cmp`, GNU `tar` with `zstd`, `curl` (its downloads are checked against the
       SHA-256 pins above), `/usr/bin/time`, `git`, `sudo` and systemd;
     * the runner image's Go toolchain, which is **not pinned** and builds landrun, together with
       the Go module proxy and checksum database, checked against landrun's `go.sum`.
7. **The gate and the trusted non-proof files of the tested commit.** Every step of §4 runs
   repository code, and Lake and Python pick up files by name. So the non-proof files must be the
   user-approved ones. `scripts/pristine.sh` (the gate; POSIX `sh`, git, coreutils and the
   standard `find`, `grep`, `sed`, `awk`, `cmp` and `diff`; it never executes a repository file)
   runs in every job of `release.yml` and `ci.yml` directly after the checkout (in `verify`, a
   memory preflight that only reads `/proc/meminfo` comes before the checkout), before any `lake`,
   `lean` or `python3` call. It enforces three things:

   **a. Absence of files that run code before the checks.** It rejects:
   * a `lakefile.lean` or any other Lake/elan configuration file (`lakefile.*`, `leanpkg.toml`,
     `lake-manifest.json`, `lean-toolchain*`) outside the three pinned files. Names are matched
     case-insensitively;
   * a committed `.lake/` or `lake-packages/`;
   * every `*.py` file in `formal/` outside `formal/scripts/`, and every `*.py` file at the
     repository root (a path without `/`); in `formal/scripts/` only the pinned files may exist
     (b). Anywhere in the repository: `.pth`, `sitecustomize.py`/`usercustomize.py`,
     `__pycache__/`, bytecode (`*.pyc`/`*.pyo`/`*.pyd`), native modules (`*.so*`/`*.dylib`/`*.dll`),
     `pyvenv.cfg` and `.python-version`.

     Other `*.py` files outside `formal/`, such as those under `code/`, are **accepted**: no step
     of `release.yml` or `ci.yml` executes, imports or sources a repository file outside `formal/`.
     The trusted jobs run from the snapshot (below), which contains only `formal/`, `.github/` and
     `.claude/`. Every Python call the workflows make, directly or through the scripts they run
     with the arguments used there, is `python3 -I` on a file of `formal/scripts/` or on an inline
     program. `-I` (with `PYTHONSAFEPATH=1`) puts neither the working directory nor the script's
     directory on `sys.path`. CI's gate red-team clones the whole repository, `code/` included,
     into a temporary directory as data and executes none of it;
   * direnv, tool-manager, shell-rc, editor, container and agent hook files, and nested
     `.claude/`/`.github/` directories;
   * `.gitattributes`, `.gitmodules`, symlinks, submodules and special files, and file names with
     control or non-ASCII characters;
   * local git hooks and command-running local git configuration;
   * any file of `formal/` outside the trusted zone (b), the proof zone (`EG.lean`, `EGTest.lean`,
     `EGCheck.lean`, `EG*/**.lean`, `comparator/Solution.lean`) and the inert-data zone (top-level
     `*.md`, `LOCK.json`, `APPROVALS/**.md`, `work/**`, `status/**`, `staging/**` Markdown/JSON/
     `.proposed` files).

   **b. Pins.** Every file of the **trusted zone** must equal its SHA-256 pin in the pin block
   inside the gate. The zone is:
   * `formal/scripts/**` (the gate itself excepted: see c), `formal/redteam/**`;
   * `formal/comparator/**` except `Solution.lean`;
   * `formal/{lakefile.toml, lake-manifest.json, lean-toolchain, TRUST.md, STATEMENT.md,
     EGCheck/Final.lean}`;
   * `.github/**` and `.claude/**`.

   In strict mode the whole worktree must also be byte-identical to `HEAD`, with no untracked or
   ignored file (the file list comes from `find`).

   **c. The gate cannot pin itself.** A reader therefore trusts one of two anchors:
   * the gate script with the SHA-256 recorded at the approval (§7). Every job prints the SHA-256
     of the gate it ran;
   * better, the user-approved **trust commit**. Its identity is set as the repository variable
     `EG_TRUST_REF` by a repository admin. It must be a **full 40-hex commit id**, because anyone
     with push rights can move a tag (trust3.fable Y11b). Tag names, branch names and abbreviated
     ids fail the workflow step's hex-and-length test, before any git call. A 40-hex id that is not
     a commit, such as a tag-object id, passes that test and is rejected afterwards: the step (after
     a `git fetch` of the id if it is not present) requires
     `git rev-parse --verify -q "$EG_TRUST_REF^{commit}"` to return the same id. The gate
     (`--trust-ref`) repeats both checks.

     With `EG_TRUST_REF` set, the trusted jobs run that commit's copy of the gate
     (`git show $EG_TRUST_REF:formal/scripts/pristine.sh`) with `--trust-ref`. That also requires
     every trusted-zone file, and the gate itself, to be byte-identical to the trust commit.
     Without it, `release.yml` prints a warning and runs the tested commit's own gate, which is
     self-verification only.

   The gate then copies the checked files to a **snapshot** (`$RUNNER_TEMP/trusted`; files
   read-only, `.lake` an empty directory). Every later step of the trusted jobs runs from the
   snapshot. Python always runs with `-I` and `PYTHONSAFEPATH=1`.

   **Not pinned by the gate**, although some of these files are read by trusted steps:
   * `LOCK.json` (read by `lock.py`);
   * `status/**` (read by `status.py`);
   * `CONVENTIONS.md`;
   * `EG/Spec/**` and `EG/Defs/**`, which are in the proof zone;
   * `APPROVALS/**`, `work/**` and `staging/**`.

   At stage γ this does not matter: those steps are hygiene (§3), and the claim is checked against
   the upstream statement. At stage α it does (§8 item 5).
8. **GitHub-hosted runners, GitHub Actions and the Actions artifact store**, when `release.yml` is
   the criterion. The untrusted `build` job hands the project `.olean`s to the trusted `verify`
   job through the artifact store. `verify` validates the archive's member names and types, but
   not the contents.

   A run executes the workflow file of the commit it tests, and a modified workflow can simply
   skip the gate. So **a run is evidence only together with the offline check of §4.2**: the
   tested commit's trusted zone, workflows included, equals the approved trust commit. A run
   cannot certify itself. `EG_TRUST_REF` protects the run's own steps. It does not replace that
   offline check.
9. **The release checkers and their assumptions.**
   - comparator, lean4export and landrun at the commits of §4.4, and comparator's code: the
     statement `eqv`, the axiom walk, the replay driver, and the ndjson it reads from lean4export.
     comparator is the load-bearing check (§4.1), so a permissive bug there is not compensated by
     FinalCheck or `leanchecker --fresh` for the comparator artifact.
   - comparator's README assumptions:
     * the Challenge's import closure and the lakefile are trusted;
     * the Challenge closure is built and exported **before** any project code is compiled;
     * the Solution is built only inside the sandbox;
     * comparator runs as an unprivileged user with AF_UNIX sockets restricted.

     `scripts/comparator.sh run --release --system-unit` refuses to run as root, and runs
     comparator in a transient unit:
     `sudo systemd-run --uid --gid --property=RestrictAddressFamilies=~AF_UNIX --property=NoNewPrivileges=yes`.
     `NoNewPrivileges=yes` means that no setuid program, `sudo` in particular, can regain
     privileges from inside the unit. On GitHub-hosted runners the `runner` user otherwise has
     password-less `sudo`.
   - **The Linux kernel's Landlock LSM is actually enforced.** comparator always passes
     `--best-effort` to landrun. On a kernel without Landlock, go-landlock v0.9.0 then restricts
     nothing and does not set `no_new_privs`, while landrun still reports success (trust3.opus B2).

     `scripts/comparator.sh` therefore runs a **canary** that fails closed, before comparator
     starts and again inside the systemd unit. The canary requires:
     * a Landlock ABI ≥ 3 from `landlock_create_ruleset(…, LANDLOCK_CREATE_RULESET_VERSION)`;
     * that the pinned landrun, with comparator's own flags, can write inside its writable
       directory;
     * that it is denied a write outside that directory;
     * that it sets `no_new_privs`;
     * inside the unit only, that the unit's own process has `no_new_privs`, which proves that
       `NoNewPrivileges=yes` took effect.
   - **landrun's writable set is the whole project `.lake`.** In the release layout this includes
     `.lake/packages`, so the Solution build can rewrite package `.olean`s. This is covered for
     three reasons:
     * the Challenge is built and exported first;
     * a Solution-side change to any constant in the statement's closure is a comparator
       `Const does not match`;
     * every other constant of the Solution environment is replayed by comparator's kernel.

     What remains is the loader (item 10).
   - The operating system and hardware of the runner.
10. **The Lean v4.33.1 `.olean` loader on adversarial input.** In a release the project `.olean`s
    are produced by project code with IO, so they are arbitrary bytes. Every checker reads them with
    the same unvalidated memory-mapping loader:
    * FinalCheck and `leanchecker` in the `verify` job;
    * comparator's `lean4export`, inside the sandbox, where a build-time `#eval` can also rewrite an
      earlier module's `.olean` before export.

    A loader exploit could make any of them see any environment, and **comparator does not cover
    this**. Lint, MetaScan and the job separation are hygiene against it, not a guarantee (§8
    item 6).

## 3. Not trusted

- **Stage γ, and only under the acceptance criterion of §4:** every definition and statement in
  `EG/`, `EGTest/`, `EGCheck/` (except `EGCheck/Final.lean`, which is pinned) and
  `comparator/Solution.lean`.

  A wrong internal definition can block the proof, but it cannot make the checked claim false:
  §4 compares the final theorem against the independently built upstream statement and replays
  every declaration it depends on in the kernel. The internal representation (`EG.Obj`,
  `EG.IsDecomp`) is connected to the upstream statement by the kernel-checked bridge
  (`EGCheck/BridgeLemmas.lean`, `EGCheck/BridgeCore.lean`, `EGCheck/Bridge.lean`).
- **This is not a stage-α or stage-β claim.** At α and β, the hypothesis texts of §5 and the EG
  definitions they mention *are* trusted.
- **The in-band checks are ADVISORY.** `lake build EGCheck.Final` succeeding is **not evidence** on
  its own. That covers its `type_of%`, the `#guard_msgs` on `#print axioms` and the `run_cmd`
  meta-check. They run inside the elaborator, where every imported module can:
  * extend or override them (`@[command_elab]`/`@[term_elab]`/macro overrides of `run_cmd`,
    `#print axioms` or `type_of%`);
  * bypass them (`debug.skipKernelTC` in `#eval`/`elab`/`run_tac`);
  * subvert them at build time (IO from `#eval`).

  They are a fast first line for developers. A passing `#guard_msgs` prints nothing: the build
  must *succeed*.
- **Hygiene and regression guards, not part of the trust argument:**
  * `scripts/lint.py`;
  * the MetaScan of `scripts/Axioms.lean`;
  * `scripts/lock.py` and `LOCK.json`;
  * `scripts/status.py` (the sorry ratchet);
  * CODEOWNERS;
  * the `.claude/settings.json` deny rules, which cover edit tools only;
  * the whole of `ci.yml`.

  CI restores build caches and runs the checks on the runner that just executed project code. Its
  post-build gate re-check cannot exclude tampering: the build runs as the snapshot's owner, and
  with `--link-lake` it shares `formal/.lake` with the snapshot.

## 4. Acceptance criterion ("How to check") — out-of-band

### 4.1 Roles of the three checks

* **comparator is the load-bearing check.** It is the one check that establishes the claim
  against a malicious build. It builds the byte-identical Challenge from the pinned sources before
  any project code, and builds the Solution only inside its Landlock sandbox (verified by the
  canary, §2 item 9). It then checks three things on **one** exported view of the Solution
  environment:
  * statement equality (`eqv` against the Challenge);
  * the permitted axioms;
  * a kernel replay.

  It does not cover a loader exploit (§2 item 10). It is only as good as the files that start it,
  which is why the gate and the offline check of §4.2 exist (§2 items 7 and 8).
* **`leanchecker --fresh EGCheck.Final` and `scripts/FinalCheck.lean` are defence in depth.** They
  check the other artifact, `EGCheck.erdos_184`, and are useful redundancy. They do not
  independently establish the claim:
  * both load the untrusted `.olean`s into their own process;
  * `leanchecker --fresh` covers only the import closure of `EGCheck.Final`, and checks neither the
    statement nor the axioms;
  * FinalCheck's kernel replay had an attribution gap (trust2.opus N4). It is fixed, with the
    regression fixture `redteam/external/patches/N4`.

  A reader should not treat "FinalCheck and `leanchecker --fresh` pass" as sufficient without
  comparator.

### 4.2 Offline precondition: which run counts

Let `T` be the user-approved trust commit (40-hex) and `R` the commit a `release.yml` run tested.
The gate step of each job logs `R` as `HEAD`. The run is evidence only if, in a fresh clone
containing both commits:

```
git show T:formal/scripts/pristine.sh > /tmp/gate.sh
sh /tmp/gate.sh -C <clone checked out at R> --trust-ref T      # must print PRISTINE: PASS
```

This requires the whole trusted zone of `R` to be byte-identical to `T`: `.github/**` (workflows
and CODEOWNERS), `.claude/**`, `scripts/**`, `redteam/**`, `comparator/**` except `Solution.lean`,
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `TRUST.md`, `STATEMENT.md` and
`EGCheck/Final.lean`. It also rejects every code-before-check file (§2 item 7a).

A reader who does not want to trust the gate script instead reviews
`git diff T R -- formal/scripts formal/redteam formal/comparator formal/lakefile.toml formal/lake-manifest.json formal/lean-toolchain formal/TRUST.md formal/STATEMENT.md formal/EGCheck/Final.lean .github .claude`.
It must be empty apart from `formal/comparator/Solution.lean`. The reader must also confirm that
`git ls-files` at `R` contains no `lakefile.lean`, no `lean-toolchain` other than
`formal/lean-toolchain`, no `*.py` file in `formal/` outside `formal/scripts/`, and no `*.py` file
at the repository root. Each of these must print nothing:

```
git ls-files | grep -i -E '(^|/)(lakefile\.lean|lean-toolchain)$' | grep -vx 'formal/lean-toolchain'
git ls-files | grep -E '^formal/.*\.py$' | grep -v '^formal/scripts/'
git ls-files | grep -E '^[^/]*\.py$'
```

`*.py` files elsewhere outside `formal/` (for example under `code/`) are allowed; no job executes
them (§2 item 7a). This is a subset of the gate's rules (§2 item 7a), not a replacement for them.

### 4.3 The steps, as `release.yml` implements them

A release is accepted **only if** all of the following hold:
* the offline check of §4.2 passes;
* **all three jobs** of a `release.yml` run on `R` pass: fresh runners, no restored `.lake` build
  directory, no `actions/cache`;
* the project is at stage γ: no `sorry` anywhere, so `lint --release`, `Axioms --no-sorry`,
  FinalCheck in strict mode and comparator with the release config all pass.

The run is triggered by a tag push (`formal-v*`, `release-*`) or by `workflow_dispatch`.

Every step below is implemented in the committed `release.yml` at the revision of §7. **None has
yet run on GitHub** (§8 item 1).

**`build` job (UNTRUSTED; its only output is an artifact):**
1. The gate (not a trust boundary here: it only fails early on a tree the trusted jobs reject).
2. Install elan and Lean (both checksum-verified), then `lake exe cache get` and
   `./scripts/check_pins.sh`.
3. `lake build EG EGTest EGCheck EGCheck.Final`. This runs project code, with IO.
4. Pack `.lake/build/lib/lean/{EG,EGTest,EGCheck}*` into a tar archive and upload it as the
   artifact `project-build`.

**`verify` job (TRUSTED; never compiles or executes project code):**

0. Setup and the gate:
   a. Memory preflight: at least 16 GB of RAM + swap, needed for `leanchecker --fresh`. On a runner
      with less (GitHub's standard private-repository runners have 7 GiB), a 12 GiB swap file is
      added first, outside the checkout and before any project code. Swap changes speed only, never a
      verdict: an out-of-memory kill fails the job.
   b. Checkout with full history.
   c. Validate `EG_TRUST_REF` (40-hex, a commit of this repository; fetch by id if needed).
   d. Run the gate and take the snapshot: with `EG_TRUST_REF` set, T's gate with `--trust-ref`;
      without it, the checkout's own gate plus a warning.
   e. Everything below runs in `$RUNNER_TEMP/trusted/formal`.
1. Install elan and Lean (both checksum-verified).
2. `python3 -I scripts/lock.py files --strict`, the first Python call. This is hygiene (§3).
3. `lake exe cache get`, then `./scripts/check_pins.sh`.
4. `python3 -I scripts/lint.py --self-test`, then `python3 -I scripts/lint.py --release`.
5. `redteam/tooling/run.sh`. This compiles the pinned red-team fixtures, some of which contain
   `#eval`, in a temporary directory. That is trusted-zone content executing.
6. `lake build 'FormalConjectures.ErdosProblems.«184»'`: the Challenge closure is built from the
   pinned sources before any project artifact is present.
7. `lake env lean --run scripts/Statement.lean "$RUNNER_TEMP/STATEMENT.regen.md"` must produce an
   empty `diff -u` against `STATEMENT.md`.
8. Download the artifact and install it as data:
   * Python `tarfile` checks every member name against
     `^(EG|EGTest|EGCheck)(\.[A-Za-z0-9_.]+|/[A-Za-z0-9_./«»-]*)?$`, with no `..` component and
     regular files and directories only;
   * GNU `tar` then extracts into the empty `.lake/build/lib/lean`.

   Validation and extraction use two different parsers (§8 item 3).
9. `python3 -I scripts/lock.py check --strict` (hygiene).
10. `lake env lean --run scripts/Axioms.lean --no-sorry --cross-check …` (axioms and MetaScan;
    hygiene).
11. `python3 -I scripts/status.py --check --no-write`: the sorry ratchet. It is hygiene and writes
    nothing.
12. **`lake env lean --run scripts/FinalCheck.lean`** in strict mode (no `--allow-sorry`, no
    `--allow-unpinned`, pins from `TRUST.md`) must print `FINALCHECK: PASS`.

    FinalCheck runs no imported code (`importModules`, `loadExts := false`). It checks:
    * the Lean githash;
    * that every `.olean` lies in its package and each package is at its manifest rev with a
      clean worktree;
    * **origin**, the N4/N6 fix:
      - the four fixed names are each declared by exactly one module, the expected one;
      - no name is declared by both a project module and another module;
      - duplicates between project modules are only same-type theorems (Lean's realized
        `eq_N`/`congr_simp` lemmas; their number for a given tree is in FinalCheck's output);
      - no project module's `extraConstNames` or `const2ModIdx` attribution claims a kernel
        constant it does not declare;
    * a kernel replay (`Environment.replay`) of **every declaration of every project module, from
      that module's own stored `ConstantInfo`**. Every copy of a duplicate is replayed separately;
      `unsafe`/`partial` constants are skipped by design and hence unusable;
    * that both theorems are theorems, and `Expr.equal` of the two statements;
    * that the axioms of `EGCheck.erdos_184` are exactly the three, following every stored copy;
    * the project policy: no `axiom`, `unsafe`, `extern`, `implemented_by` or `init`, and no
      meta-level constants;
    * `statement-sha256` and `closure-sha256`.
13. `lake env leanchecker EG`, then `lake env leanchecker EGTest` (separately: the joint call
    `leanchecker EG EGTest EGCheck` exhausts a 16 GB runner): kernel replay of every module of EG and
    EGTest. Measured: EG 13.8 min / 12.1 GB, EGTest 1.3 min / 10.7 GB max RSS. The modules of EGCheck
    (`Bridge`, `BridgeCore`, `BridgeLemmas`) all lie in the import closure of `EGCheck.Final` and are
    replayed by step 14.
14. **`lake env leanchecker --fresh EGCheck.Final`** must exit 0. This is a kernel replay of the
    whole import closure of `EGCheck.Final`, packages included. Measured: 21–40 min, 10.2–10.3 GB
    max RSS.

    It catches kernel bypasses in any module **of that closure**. It does not reach modules
    outside the closure, nor `comparator/Solution.lean`, and it checks neither the statement nor
    the axioms.

**`comparator` job (TRUSTED harness):**

0. Setup and the gate:
   a. Checkout.
   b. Validate `EG_TRUST_REF` and run the gate with the snapshot, as in `verify`.
   c. Install elan and Lean.
1. `scripts/comparator.sh tools "$RUNNER_TEMP/comparator-tools"` builds landrun (Go), lean4export
   and comparator (Lean v4.33.1, patch applied) at the pinned commits, and verifies each checkout's
   `HEAD`.
2. `lake exe cache get`, then `./scripts/check_pins.sh`.
3. `scripts/comparator.sh check` verifies:
   * the Challenge's SHA-256 and git blob against the pins;
   * the pinned formal-conjectures commit, and `cmp` against the package file;
   * the release config;
   * that the Solution does not import `FormalConjectures.ErdosProblems.*`.
4. **`scripts/comparator.sh run --release --system-unit --tools DIR`** must end with
   `Your solution is okay!` (exit 0). In order, it:
   * refuses root, `--allow-sorry`, `--prebuilt` and `--solution`;
   * re-runs `check`;
   * runs the Landlock canary (§2 item 9);
   * starts the systemd unit (AF_UNIX restricted, `NoNewPrivileges=yes`);
   * inside the unit, runs the canary again with `--expect-nnp`, then `lake env comparator
     comparator/config.json`.

   The config is: challenge `Challenge`, solution `Solution`,
   `theorem_names = ["Erdos184.erdos_184"]`, `permitted_axioms` = the three of §2 item 2. These
   are its only four keys; there is no `definition_names` key, so no definition holes. The run
   needs `lakefile.toml` with the `Challenge`/`Solution` libraries
   (`staging/lakefile.toml.proposed`); until that is applied, the job fails closed.

Measured by hand (dry runs as root without systemd, `sorryAx` permitted; see
`work/trust/bridge.md` and `consolidate.md`):
* comparator accepts the honest Solution;
* it rejects the five F-attacks;
* the harness refuses to start comparator with an unconfined landrun (case C0).

### 4.4 Pinned checker versions

`scripts/comparator.sh tools` builds these; details and measured dry runs are in
`comparator/README.md` and `work/trust/bridge.md`.

| Checker | Version |
|---|---|
| leanchecker | bundled with Lean v4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` + `comparator/patches/comparator-fd5d5bcf-lean-v4.33.1.patch`, built with Lean v4.33.1 |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869`, built with Lean v4.33.1 |
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18), built with the runner's Go (≥ 1.24) |
| nanoda (optional external kernel) | not used |

The comparator patch backports a Lean v4.34 fix that comparator relies on for soundness:
`Expr.proj` structure names in `getUsedConstants` (comparator issue 68). Without it, comparator
built with v4.33.1 accepts comparator's own `proj_trick` counterexample (measured).

### 4.5 A reader's minimal recipe (independent of the repository's scripts)

0. First do the offline check of §4.2 for the release commit `R` against the approved trust commit
   `T`: the trust-commit gate, or the `git diff` review together with the three `git ls-files`
   checks. Step 1 below is only a spot check of the files that matter most to this recipe; it does
   not replace §4.2.
1. Take a fresh clone of the release commit and check its files:
   * `git ls-files | grep -i -E '(^|/)(lakefile\.lean|lean-toolchain)$'` shows only
     `formal/lean-toolchain` (a plain substring `grep` also matches the gate red-team fixture
     `formal/redteam/gate/fixtures/lakefile.lean.fixture`, which is inert data);
   * `formal/lean-toolchain` reads `leanprover/lean4:v4.33.1`. elan follows that file to any
     GitHub-hosted toolchain, so it must be checked;
   * no `*.py` file is tracked in `formal/` outside `formal/scripts/`, and none at the repository
     root (the second and third commands of §4.2 print nothing). `*.py` files elsewhere, such as
     under `code/`, are allowed; no job executes them (§2 item 7a);
   * read `formal/lakefile.toml` (short; its `leanOptions` elaborate the Challenge) and
     `formal/lake-manifest.json` against §2 items 3–5.
2. `cmp formal/comparator/Challenge.lean <184.lean fetched from GitHub at the commit of §2 item 3>`.
3. Write `config.json` by hand, with the four keys of §4.3, `comparator` job, step 4
   (`challenge_module`, `solution_module`, `theorem_names`, `permitted_axioms`) and no
   `definition_names`.
4. Build landrun, lean4export and comparator at the commits of §4.4 by hand, applying the
   comparator patch.
5. Confirm that landrun really confines on the reader's kernel: a write outside `--rwx DIR` must
   fail.
6. Build the Challenge closure, then run comparator as its README prescribes: unprivileged, AF_UNIX
   restricted, no setuid path.

This still trusts §2 items 1–5, 9 and 10 and the reader's own machine, but none of the
repository's checker code.

## 5. Staged trust (PLAN_FORMALIZATION.md §1)

- **Stage α.** A protected artifact proves `type_of% @_root_.Erdos184.erdos_184.{u}` from exactly
  three hypotheses. The planned artifact is `EGCheck/FinalAlpha.lean`, with its own acceptance
  check; both are to be designed and approved in phase P2.

  Each hypothesis is a locked Tier-1 `Prop` in `EG/Spec/**`, hashed in `LOCK.json` together with
  the closure hash of every EG definition it mentions. Each states a published classical result:
  * **Lovász 1968**: path/cycle decomposition;
  * **Haxell 1995**: a hypergraph matching condition;
  * **Euler**: a connected graph with all degrees even has an Euler circuit.

  No `axiom`, no `sorry`, and no Bucić–Montgomery-specific hypothesis is allowed. The exact texts
  are written and approved in phase P2, then listed here with their hashes. The approval requires
  two independent reviewers (one cross-model), a back-translation, a `False`-from-hypotheses check
  and non-vacuity tests.

  **At stage α the reader additionally trusts:**
  * the three hypothesis texts;
  * every EG definition they mention;
  * that each text is implied by the cited published result. A hypothesis that is stronger than
    the literature, or false, makes the α result vacuous.

  The α acceptance criterion is **not yet designed**. comparator compares against the
  unconditional upstream Challenge, so it cannot check an α artifact as it stands
  (`work/trust/bridge.md` §8 item 7). The locked texts are not yet gate-pinned (§2 item 7, §8
  item 5).
- **Stage β.** The hypotheses are discharged one at a time by kernel-checked proofs: Euler first,
  then Haxell, then Lovász. A discharged hypothesis leaves the trusted list; the α trust applies to
  the ones that remain.
- **Stage γ.** `EGCheck.erdos_184` and comparator's `Erdos184.erdos_184` are unconditional, and §4
  passes. **Only stage γ may be called "formally verified"**, and only after the out-of-band
  criterion of §4 has passed. "EG is not trusted" (§3) holds only at stage γ and only under §4.

## 6. Process (not part of the trust argument)

**The operative protection list is the gate's pin block** (`scripts/pristine.sh`, between
`BEGIN-PINS` and `END-PINS`), together with the trust commit and the offline check of §4.2.

Every approved change to a trusted-zone file is applied in four steps:
1. apply the change together with `sh formal/scripts/pristine.sh --write-pins`;
2. review the diff of the pin block and the changed files;
3. run `python3 -I scripts/lock.py update --approval APPROVALS/<file>.md`;
4. record the new gate SHA-256 in the approval file, commit, and set `EG_TRUST_REF` to the new
   commit id.

The other mechanisms support the user's review; none of them is part of the trust argument:
* CODEOWNERS binds only with branch protection and a pull-request flow;
* `.claude/settings.json` denies file-edit tools only, not shell writes;
* `scripts/lock.py` checks the tree against the `LOCK.json` of the same tree, so it detects
  accidents, not an adversary.

| Path (under `formal/` unless noted) | gate pin | LOCK.json | CODEOWNERS | edit-deny (`.claude/settings.json`) |
|---|---|---|---|---|
| `TRUST.md`, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `EGCheck/Final.lean` | yes | yes | yes | yes |
| `STATEMENT.md` | yes | yes | yes | proposed |
| `comparator/Challenge.lean`, `comparator/config.json`, `comparator/patches/**` | yes | yes | yes | proposed |
| `comparator/README.md` | yes | no | no | no |
| `lakefile.lean` and every other Lake/elan file (must not exist) | rejected anywhere | — | yes (`lakefile.lean`) | proposed (`lakefile.lean`) |
| `scripts/**` (the gate: via the trust commit), `redteam/**` | yes | yes | yes | no: integrator/agent-owned under an explicit task (AGENTS.md rule 3) |
| `/.github/**` (workflows, CODEOWNERS) | yes | workflows and CODEOWNERS | yes | no |
| `/.claude/**` | yes | `settings.json` | yes | yes |
| `LOCK.json` | **no** | (itself) | yes | proposed |
| `CONVENTIONS.md`, `status/ratchet.json` | **no** | yes | yes | no (integrator-owned) |
| `EG/Spec/**`, `EG/Defs/**` | **no** (proof zone) | yes (constants and files) | yes | from the P2→P3 statement freeze on |

The proposed deny list is `staging/claude-settings.json.proposed`.

Not protected on purpose: `EGCheck/Bridge*.lean`, `comparator/Solution.lean` and the rest of
`EG/`, `EGTest/` and `EGCheck/`. They are untrusted proof code, checked by §4.

## 7. Revision record

The gate SHA-256 and the trust commit **cannot be written into a pinned file**, because the gate
pins `TRUST.md`: recording the gate's hash here would change the gate's hash. The authoritative
record is therefore twofold:
* the approval file in `APPROVALS/` (not pinned), with the gate SHA-256 and the trust commit id;
* the repository variable `EG_TRUST_REF`.

For this *proposal*, as refreshed at the end of the consolidation of 2026-09-26
(`work/trust/consolidate.md`):

    gate scripts/pristine.sh SHA-256 (working tree, 100 pins, proposals NOT applied): a29e7d7dc3dfa93f9b9e4fa42ba3431f4308b2b2eb879f1db6cddcd83c94cd9b

Applying this file, `staging/Final.lean.proposed`, `staging/lakefile.toml.proposed`,
`staging/claude-settings.json.proposed` and `staging/redteam.sh.proposed` changes five pinned files
(`TRUST.md`, `EGCheck/Final.lean`, `lakefile.toml`, `.claude/settings.json` and
`redteam/external/redteam.sh`). It therefore requires
`--write-pins`, which produces a new gate SHA-256; that new value is the one to record at the
approval.

## 8. Open release blockers

No release may be claimed until every item below is closed. Items 1–4 are enforcement or
verification gaps. Items 5–8 are residual trust that must be stated or reduced. Items 9–13 are
approval steps.

1. **RESOLVED (2026-09-30): the acceptance procedure has run on GitHub.** Release run 36767721300
   (tag `release-2026-09-30b` → f7398e1 = `EG_TRUST_REF`) passed all three jobs on GitHub-hosted
   `ubuntu-latest` runners (7 GiB RAM + 12 GiB swap file): comparator in
   `--release --system-unit` mode ("Your solution is okay!"); build; verify (PRISTINE: PASS, 0 sorryAx,
   FINALCHECK: PASS, `leanchecker EG`, `leanchecker EGTest` and `leanchecker --fresh EGCheck.Final`
   exit 0). This exercised Go 1.24.13 on the image, `sudo systemd-run --uid … --wait --pipe` with both
   properties, `lake exe cache get` from the snapshot, the artifact round trip, and fetching
   `EG_TRUST_REF` by id. Record: `work/p3/ACCEPT.md`. Earlier release run 36758690862 stopped at the
   memory preflight (7 GiB, before the swap step existed); its comparator job passed.
2. **RESOLVED (2026-09-30): Landlock and `NoNewPrivileges` enforcement verified on the target.** In the
   comparator jobs of release runs 36758690862 and 36767721300 (GitHub runner kernel, inside the
   systemd unit), the canary reported "ABI 7; a write outside the sandbox was denied; no_new_privs set
   inside landrun; this unit has NoNewPrivileges", and `--release --system-unit` ran to completion.
   The fail-closed tests (pass-through landrun, hidden exit code, low ABI, missing `no_new_privs`)
   remain local-only (`redteam/bridge`, case C0 also runs in CI).
3. **Artifact tar-parser consistency.** `verify` validates the artifact with Python `tarfile` and
   extracts it with GNU `tar`. The member-name allowlist is only as strong as the agreement of the
   two parsers. The impact is bounded: writes stay under the snapshot's `.lake/build/lib/lean`, and
   the statement pins and comparator are independent. Fix: validate and extract with one parser
   (`tarfile.extractall(filter="data")` into a fresh directory outside the snapshot, then check the
   extracted tree against the allowlist with `find`).
4. **Offline evidence check not automated.** A run proves nothing about its own workflow file
   (§2 item 8). Two options:
   * a `workflow_dispatch`-only release workflow on a protected branch, which checks out the tested
     commit as data (trust3.fable R2);
   * a published procedure that records `T`, `R` and the §4.2 output with each release.

   Until then, §4.2 is a manual step.
5. **Stage-α pinning of `LOCK.json` and `EG/Spec/**`.** The gate does not pin `LOCK.json`,
   `EG/Spec/**`, `EG/Defs/**`, `CONVENTIONS.md` or `status/ratchet.json`, and `lock.py` verifies the
   tree against its own `LOCK.json`. At stage α the locked hypothesis texts are trusted, and nothing
   non-self-verifying protects them. They must enter the trust-commit comparison, as gate pins or
   as a `--trust-ref` zone, from the P2→P3 freeze on. The α acceptance criterion itself is still to
   be designed (§5).
6. **`.olean` loader residual** (§2 item 10). It is not closed by any checker. Optional hardening:
   rebuild every project module from source in `verify`, each in its own sandbox, so that every
   `.olean` a checker reads was written by the pinned `lean`.
7. **IO in the untrusted build.** The `build` job (and CI's build) runs project code with
   unrestricted IO: `#eval`, `initialize` and elaborators run at `lake build`. Nothing constrains
   that job; the defences are:
   * job separation: `verify` never runs project code, and the only hand-over is the artifact,
     which is filtered by path (item 3) and whose contents are untrusted;
   * the Landlock sandbox in the `comparator` job (item 2);
   * lint, which rejects `#eval` and similar as hygiene.

   A build-time write is a "miss by design" for FinalCheck (`redteam/external`, case IO). In CI,
   the same IO can rewrite the snapshot and the shared `.lake` (§3). CI is regression-only.
8. **External red-team expectations for the proposed `Final.lean`** (trust3.opus R1). With
   `staging/Final.lean.proposed` applied, attacks B1 and C are caught *in-band*, and
   the committed `redteam/external/redteam.sh` then reports `REDTEAM: FAIL (2 mismatches)`. That is
   CI's slow red-team step. Its expectation table must be updated in the same approval. The
   update is prepared in `staging/redteam-expectations.proposed.md`, with the full harness as
   `staging/redteam.sh.proposed`: when `EGCheck/Final.lean` is the hardened version, B1 and C must
   be caught in-band by the attack's own error, and FinalCheck still runs on B1/C against a dev
   final (the committed `Final.lean`'s theorem without its in-band checks), so that out-of-band
   coverage of B1/C stays exercised. With the committed `Final.lean` its verdicts are unchanged.
9. **Apply the proposals under one approval:** this file, `staging/Final.lean.proposed`,
   `staging/lakefile.toml.proposed`, `staging/claude-settings.json.proposed` and
   `staging/redteam.sh.proposed` (item 8). Then:
   * `--write-pins` and a review of the pin diff;
   * `lock.py update`: `lock.py files --strict` fails on the current working tree (for the
     violations and PENDING entries, see the output of
     `python3 -I scripts/lock.py files --strict`);
   * set `EG_TRUST_REF` to the approved commit id.

   Until this file is applied, the committed `TRUST.md` has no `EG-PIN` lines, so FinalCheck in
   strict mode fails. Until the lakefile is applied, the comparator job fails closed.
10. **Stage γ.** `sorry` remains in the tree, so `lint --release` fails (for the files, see the
    output of `python3 -I scripts/lint.py --release`). `EGCheck/Smoke.lean` must be removed before
    release (trust3.fable R6).
11. **Go toolchain not pinned.** landrun is built with the runner image's Go. Pinning it (a
    checksum-verified Go archive) would remove the Go toolchain from the trusted list, apart from
    the module checksums.
12. **CI's slow red-team suites** (`redteam/external`, `redteam/bridge`) run in CI only weekly, on
    dispatch, or when the checkers change. The gate red-team runs on every CI run.
    `redteam/bridge` now also runs the Landlock canary, so on a runner without Landlock it fails
    (closed); untested on GitHub (item 1).
13. **Mathlib `.olean` cache.** Every job uses the cache. Only the closure pin, `leanchecker
    --fresh` (for `EGCheck.Final`'s closure) and comparator's replay tie cached `.olean`s to the
    sources (§2 items 4 and 6). A from-source Mathlib build in `verify` would remove the cache from
    the trusted list, at a cost of about 2.5 h on 4 cores.
