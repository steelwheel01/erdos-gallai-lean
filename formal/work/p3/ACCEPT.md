# Acceptance record (TRUST.md §4) — local runs, 2026-09-30

Status: **local checks only.** The acceptance criterion of TRUST.md is the out-of-band run in
`release.yml` on GitHub (comparator in `--release --system-unit` mode, which refuses root; FinalCheck
and `leanchecker --fresh` in the `verify` job) from a snapshot pinned by `EG_TRUST_REF`. None of that
has run yet. Nothing here is a release; the proof has had no human review.

Tree: branch `claude/magical-ritchie-f0rl2d`, commit after `d264c23` (Lovász proved; smoke test
removed). Toolchain Lean v4.33.1 (819816b2), Mathlib v4.33.1, formal-conjectures 2424bb48.

| Step (TRUST.md §4.3) | Command | Result |
|---|---|---|
| gate (dev) | `sh scripts/pristine.sh --dev` | DEV-PASS, 100/100 pins |
| build | `lake build EG EGTest EGCheck EGCheck.Final` | OK (601 EG modules, 37 EGTest, 3 EGCheck); `EGCheck.Final` in-band guard passes |
| lint (release) | `python3 -I scripts/lint.py --release` | 0 findings |
| lock | `python3 -I scripts/lock.py check --strict` | 1,234 constants / 277 files, 0 violations, 0 pending |
| axioms | `lake env lean --run scripts/Axioms.lean --no-sorry --prefix EG --prefix EGTest --prefix EGCheck EG EGTest EGCheck` | 11,056 constants, 0 sorryAx, 0 meta-scan hits, 0 violations |
| FinalCheck (strict) | `lake env lean --run scripts/FinalCheck.lean` | **FINALCHECK: PASS (0 failures, 0 warnings)**; statement `Expr.equal` to `Erdos184.erdos_184`; axioms exactly propext, Classical.choice, Quot.sound (two methods); kernel replay of 10,085 project declarations; statement-sha256 `4cb2cd5697e7916ea244e8b58041fcb2c7fa4338621335eeeb3a1d05452f6734`, closure-sha256 `39d6e8c358b1482f9af513370d6edfba52da96857fa1066a309fa87c0ccf66fd` match the pins; 2 min 51 s, 9.1 GB RSS |
| comparator tools | `scripts/comparator.sh tools $HOME/comparator-tools` | built at pinned commits (landrun, lean4export, comparator + patch) |
| comparator check | `scripts/comparator.sh check` | OK (Challenge byte-identical to pinned upstream 184.lean; release config; Solution does not import the upstream module) |
| leanchecker (project) | `lake env leanchecker EG EGTest EGCheck` | joint run OOM-killed by the 15 GB container cgroup (no verdict). Per library, alone: **EG exit 0** (13 min 49 s, 12.1 GB); **EGTest exit 0** (1 min 16 s, 10.7 GB); EGCheck OOM-killed at 13.5 GB (no verdict) — but all three EGCheck modules (Bridge, BridgeCore, BridgeLemmas) lie in the import closure of `EGCheck.Final` (Final → Bridge → BridgeCore → BridgeLemmas), which `leanchecker --fresh EGCheck.Final` replayed with exit 0, so they are covered. The GitHub runner (≥ 16 GB, TRUST.md §4.3) runs the joint command. |
| leanchecker --fresh | `lake env leanchecker --fresh EGCheck.Final` | **exit 0** (1 h 11 min, 10.7 GB max RSS): kernel replay of the whole import closure of `EGCheck.Final`, packages included |
| comparator run | `scripts/comparator.sh run --tools $HOME/comparator-tools` (non-release; as root: **local dry run only**, the harness itself warns that comparator README assumption 6 is not met) | **"Your solution is okay!"**, exit 0 (4 min 52 s, 7.0 GB): release config (`theorem_names = ["Erdos184.erdos_184"]`, `permitted_axioms` = propext, Quot.sound, Classical.choice; no `sorryAx`); Landlock canary passed (ABI 7, write outside the sandbox denied, no_new_privs set); Solution rebuilt inside landrun; Lean default kernel accepts the exported solution |

## Summary (2026-09-30)

Every local check of TRUST.md §4 passes: FinalCheck (strict), `leanchecker --fresh EGCheck.Final`,
`leanchecker` on EG and EGTest, the axiom scan (0 sorryAx), release lint, strict lock, and comparator
(dry run). **What this is:** a Lean proof of the formal-conjectures statement `Erdos184.erdos_184`,
verified by local checks on this machine. **What it is not yet:** (1) the acceptance run — `release.yml`
on GitHub from the snapshot pinned by `EG_TRUST_REF` (repository variable not yet set; a user action),
with comparator in `--release --system-unit` mode as a non-root user; (2) human review of the
formalization and of the upstream statement's fidelity to the conjecture. Open release blockers:
TRUST.md §8.

The target statement (upstream, verbatim): `Erdos184.erdos_184 : ∃ f : ℕ → ℝ, (f =O[atTop] fun n ↦ (n : ℝ)) ∧
∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), ∃ (D : Finset G.Subgraph), (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
IsDecomposition G D ∧ (D.card : ℝ) ≤ f (Fintype.card V)`.

## GitHub CI (2026-09-30)

**formal-ci run 36739517378 (commit daf12f4): SUCCESS — all 26 steps green on a GitHub-hosted runner**
(https://github.com/steelwheel01/Erdos-Proof/actions/runs/36739517378): gate + gate red-team; checksum-
verified toolchain; trusted pins; lint; checker red-team; toolchain fingerprint; full build; gate
re-check; axiom scan + MetaScan; FinalCheck scan; STATEMENT.md vs pinned upstream; statement lock;
sorry ratchet; per-library leanchecker (EG, EGTest); `EGCheck.Final` (in-band guard passes);
out-of-band FinalCheck red-team; comparator-layout red-team. Earlier failures on the way were
infrastructure only: toolchain fingerprint (elan known-projects), runner memory (joint leanchecker),
runner disk (comparator red-team) — each fixed with an APPROVALS record.

Still NOT done: the acceptance run (`release.yml` from the snapshot pinned by `EG_TRUST_REF`, with
comparator in release mode as a non-root user), which needs the user to apply
`staging/TRUST.md.proposed` (step 13) and then set `EG_TRUST_REF`; and human review.

## Release run 1 (2026-09-30): formal-release run 36758690862, tag `release-2026-09-30` → d249d5f (= `EG_TRUST_REF`)

https://github.com/steelwheel01/Erdos-Proof/actions/runs/36758690862

* **comparator job: SUCCESS** (34 min 36 s). Gate against `EG_TRUST_REF`, checksum-verified toolchain,
  checkers built at pinned commits, trusted pins, `comparator.sh check` (Challenge byte-identical to the
  pinned upstream 184.lean; release config), then comparator in **release mode as an unprivileged
  systemd unit**: Solution rebuilt (9410 jobs), exported `Erdos184.erdos_184` with axioms propext,
  Quot.sound, Classical.choice only; **"Lean default kernel accepts the solution" / "Your solution is
  okay!"**, unit exit status 0, comparator exit code 0. This is the load-bearing check of TRUST.md §4.
* **build job: SUCCESS** (41 min 33 s): gate, fresh build, `project-build` artifact uploaded.
* **verify job: FAILED at the memory preflight** (before checkout; nothing was checked): the
  GitHub-hosted `ubuntu-latest` runner of this private repository has MemTotal 7 GiB, below the
  16 GB the preflight requires for `leanchecker --fresh EGCheck.Final`. Not a proof failure.
  For reference, formal-ci run 36756211520 on the same commit and the same runner class passed
  per-library `leanchecker EG` / `EGTest` and the FinalCheck scan.

So the acceptance run is **not complete**: the verify job (strict FinalCheck, per-library
`leanchecker`, `leanchecker --fresh EGCheck.Final` on GitHub) has not run. Its checks pass locally
(table above).

## Release run 2 (2026-09-30): formal-release run 36767721300 — **SUCCESS (all three jobs)**

https://github.com/steelwheel01/Erdos-Proof/actions/runs/36767721300 — tag `release-2026-09-30b` → f7398e1 = `EG_TRUST_REF`
(swap-backed verify preflight, APPROVALS/2026-09-30-release-swap-preflight.md). GitHub-hosted `ubuntu-latest` runners (7 GiB RAM).

* **comparator job: SUCCESS** (19:44–20:19): gate vs `EG_TRUST_REF`, checksum-verified toolchain, checkers at pinned commits, pins,
  `comparator.sh check`, comparator in **release mode as an unprivileged systemd unit**: "Lean default kernel accepts the solution",
  "Your solution is okay!".
* **build job: SUCCESS** (19:44–20:09): gate, fresh build, `project-build` artifact.
* **verify job: SUCCESS** (20:09–21:59; never compiles or runs project code):
  swap + preflight; `EG_TRUST_REF` validated; **PRISTINE: PASS** (trusted gate); lock files strict (277 files, 0 violations); Mathlib cache;
  pins; lint self-test 62/62 + release lint; checker red-team (all 14 cases ok); upstream statement built from pinned sources;
  STATEMENT.md regenerated: statement-sha256 `4cb2cd56…`, closure-sha256 `39d6e8c3…`; artifact installed (paths validated);
  lock strict (1234 constants / 277 files, 0 violations); **axiom scan: 11,057 constants under EG/EGTest/EGCheck, 0 sorryAx, 0 meta-scan
  hits, 0 violations**; sorry ratchet: frontier 0; **FINALCHECK: PASS (0 failures, 0 warnings)** — 11,840 modules imported without running
  imported code, packages clean at manifest revs, kernel replay of 10,085 project declarations, `EGCheck.erdos_184` type `Expr.equal` to
  `Erdos184.erdos_184`, axioms exactly propext / Classical.choice / Quot.sound (two methods), policy and meta clean, both hash pins match;
  **`leanchecker EG` exit 0** (13 min 25 s, 5.9 GB max RSS); **`leanchecker EGTest` exit 0** (1 min 7 s); **`leanchecker --fresh
  EGCheck.Final` exit 0** (36 min 48 s, 6.8 GB max RSS, 0 swaps).

**This is the acceptance run of TRUST.md §4, and it passed.** What it establishes: a Lean 4 proof of the formal-conjectures statement
`Erdos184.erdos_184`, checked by the Lean kernel (three independent replays) and by comparator in release mode, from the snapshot pinned by
`EG_TRUST_REF`. What it does not establish: human review of the formalization's trust setup and of the upstream statement's fidelity to the
conjecture; human review of the manuscript. The mathematics remains a candidate proof until human experts have reviewed it.
Note for TRUST.md §8 item 1 ("The acceptance procedure has never run on GitHub"): now resolved by this run (TRUST.md is user-edited).

### TRUST.md §4.2 offline check for release run 2 (2026-09-30)

T = R = `f7398e12758c1898ca60614263a2455a9f1dc78f`. The gate steps of the verify and comparator jobs log `HEAD` = f7398e1 (and
`EG_TRUST_REF` = f7398e1); the build job's head_sha is f7398e1 (GitHub API). In a fresh clone checked out at R:
`git show T:formal/scripts/pristine.sh > gate.sh; sh gate.sh -C <clone> --trust-ref T` → gate script sha256 99f1f34f… (= tree copy),
1264 files checked, trusted zone 100/100 matching pins, **PRISTINE: PASS**. `git diff T R -- …` is empty (R = T); the three
`git ls-files` checks print nothing. **Run 36767721300 therefore counts as evidence under §4.2.** (Performed by the integrator; a
reader can repeat it with the commands above.)
