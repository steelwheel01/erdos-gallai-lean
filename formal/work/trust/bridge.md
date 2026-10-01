# Trust hardening — bridge and comparator (agent id: `bridge`, 2026-09-26)

Response to the trust audits `APPROVALS/reviews/trust.opus.md` (§6, §7 items 1, 2, 5, 9) and
`APPROVALS/reviews/trust.fable.md` (R1, R2, R4, R9). Scope: make the bridge comparator-compatible,
build and dry-run comparator on Lean v4.33.1, propose the new `EGCheck/Final.lean` and `TRUST.md`.

No protected file was modified (TRUST.md, `EGCheck/Final.lean`, lake files, `lean-toolchain`,
`.claude/**`); proposals are in `staging/`. No git command that modifies the repository was run.
Attack fixtures are in `redteam/bridge/` (built by no `lean_lib`) and in the scratchpad. Tools were
cloned and built under `/root/tools` (outside the repository).

## 1. Files

| File | Change |
|---|---|
| `EGCheck/BridgeLemmas.lean` | Now a `module` (`@[expose] public section`) that does **not** import `FormalConjectures.ErdosProblems.«184»` (imports `EG.Defs.Objects`, `FormalConjecturesForMathlib…Decomposition`, `Mathlib…Connectivity.Subgraph`). The cycle-or-edge lemmas are restated against the unfolded body of `IsCycleOrEdge`, for arbitrary instances `i₁ : H.coe.LocallyFinite`, `i₂ : Fintype H.coe.edgeSet`. Proofs unchanged otherwise. |
| `EGCheck/BridgeCore.lean` | New `module`, FC-184-free: `EGCheck.Bridge.of_mainInternal_unfolded (h : EG.Spec.MainInternal)` : the upstream statement with `IsCycleOrEdge H.coe` replaced by `∀ i₁ i₂, (H.coe.Connected ∧ @IsRegularOfDegree _ H.coe i₁ 2) ∨ (@edgeFinset _ H.coe i₂).card = 1` (stronger than the upstream statement, which it implies). |
| `EGCheck/Bridge.lean` | Thin FC-importing wrapper for `Final.lean`: `of_mainInternal : type_of% @_root_.Erdos184.erdos_184.{u}` (two lines: unfold + instantiate the instances), `solution := of_mainInternal EG.Proof.mainInternal`. Names unchanged. |
| `comparator/Challenge.lean` | Byte-identical copy of the pinned `184.lean`. |
| `comparator/Solution.lean` | Upstream text; proof of `erdos_184` replaced by the FC-free bridge applied to `EG.Proof.mainInternal`; two private imports (`EG.Proof.Main`, `EGCheck.BridgeCore`); the five `sorry` variants removed; Apache-2.0 modification notice. |
| `comparator/config.json` | Release config (three axioms; `theorem_names = ["Erdos184.erdos_184"]`). |
| `comparator/patches/comparator-fd5d5bcf-lean-v4.33.1.patch` | Port of comparator master to Lean v4.33.1 (§3). |
| `comparator/README.md` | Layout, lakefile change, tool pins, patch rationale. |
| `scripts/comparator.sh` | `check` (byte identity + pins + config), `tools` (build pinned tools), `run` (dry run / `--release`). |
| `redteam/bridge/{README.md,run.sh,F1…F5}.lean` | Comparator red-team fixtures (§5). |
| `staging/Final.lean.proposed` | Proposed `EGCheck/Final.lean` (§6). |
| `staging/TRUST.md.proposed` | Proposed `TRUST.md` (§7). |
| `staging/lakefile.toml.proposed` | Proposed `lakefile.toml`: `Challenge`/`Solution` libs (srcDir `comparator`); comment `lint.sh` → `lint.py`. |

## 2. Lean results (all measured on the current tree)

* `lake build EGCheck` succeeds. BridgeLemmas 1.8 s, BridgeCore 1.3 s, Bridge 6.5 s.
* Axiom scan `lake env lean --run scripts/Axioms.lean --prefix EGCheck --cross-check EGCheck`:
  71 constants, **sorryAx only in `EGCheck.Bridge.solution`** (through `EG.Proof.mainInternal`) and
  in the old `EGCheck.smoke`; 0 meta-scan hits, 0 violations. `EGCheck.Bridge.of_mainInternal`:
  `[propext, Classical.choice, Quot.sound]`. 0 `sorry` in BridgeLemmas/BridgeCore/Bridge.
* `python3 scripts/lint.py`: 0 findings (release mode: only the 3 known `sorry`s, none in the bridge).
* The current (protected) `EGCheck/Final.lean` still fails only at the `#guard_msgs`
  (`[propext, sorryAx, Classical.choice, Quot.sound]`); its `run_cmd` passes.
* `lock.py check`: 0 violations.
* The statement of `of_mainInternal_unfolded` is kernel-checked to imply `Erdos184.erdos_184`
  twice: in `EGCheck/Bridge.lean` (against the imported upstream constant) and in
  `comparator/Solution.lean` (against the verbatim restatement). Quantifying over all instances
  `i₁`, `i₂` makes it independent of which (classical) instances the upstream elaboration picked
  (they are `neighborSet.memDecidable`/`fintypeEdgeSet`-based, see `STATEMENT.md`).

## 3. Tools (versions compatible with Lean v4.33.1)

| Tool | Commit | Built with | SHA-256 of binary (this machine) |
|---|---|---|---|
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (main, v0.1.18) | Go 1.24.7 | `82165faf…6690c` |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869` (master, = comparator's manifest pin) | Lean v4.33.1 (toolchain overridden) | `46f6a14f…f1fa1` |
| comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` (master) + patch | Lean v4.33.1 (toolchain overridden) | `5792f681…96590` |

Commands (all encoded in `scripts/comparator.sh tools DIR`):
```
git clone https://github.com/Zouuup/landrun && git -C landrun checkout 811cfff5… && (cd landrun && go build -o DIR/bin/landrun ./cmd/landrun)
git clone https://github.com/leanprover/lean4export && git -C lean4export checkout 66f1fb4b…
echo leanprover/lean4:v4.33.1 > lean4export/lean-toolchain && (cd lean4export && lake build lean4export)
git clone https://github.com/leanprover/comparator && git -C comparator checkout fd5d5bcf…
echo leanprover/lean4:v4.33.1 > comparator/lean-toolchain
git -C comparator apply formal/comparator/patches/comparator-fd5d5bcf-lean-v4.33.1.patch
(cd comparator && lake build comparator)
```
`scripts/comparator.sh tools /root/tools` reproduced byte-identical binaries.

**Why a patch.** Comparator master is on v4.35.0-rc3. Built with v4.33.1 unpatched:
1. it does not compile: `Lean.Kernel.Environment.replay` does not exist in v4.33.1 (`Main.lean:222`).
   Patched to `(← env.replay kernelConstMap).toKernelEnv` (`Lean/Replay.lean` of v4.33.1: same
   `addDeclCore` checks, returns the final environment); the issue-71 Quot post-check is kept.
2. after (1) only, comparator's own test suite (`lean --run runtests.lean` with the real landrun)
   **accepts `proj_trick`** (comparator issue 68: a statement that mentions a structure only through
   `Expr.proj` is not compared, so the Solution can change the structure). Cause: Lean v4.33.1's
   `Expr.getUsedConstants` skips `Expr.proj` structure names; Lean v4.34 includes them
   (`src/Lean/Util/FoldConsts.lean` at `v4.34.0`), and comparator relies on that. The patch copies
   the v4.34 fold into `Comparator/Util.lean` (`usedConstants`) and uses it in `Compare.lean` and
   `runForUsedConsts`. After the patch: **17/20 tests pass; the 3 failures are the nanoda tests**
   (`simple_nanoda`, `simple_nanoda_compat`, `simple_multi_nanoda`: no `nanoda_bin` built;
   nanoda is optional). `quot_mismatch`, `primitive_issue`, `olean_issue`, `opaque_value`,
   `theorem_hole_issue` etc. pass.

**Alternative measured:** comparator master **unpatched, built with its own toolchain
v4.35.0-rc3** (downloaded from GitHub releases; `release.lean-lang.org` is blocked here), with the
same lean4export (v4.33.1 build): accepts the honest Solution (allow-sorry) and rejects F3 (kernel
bypass). It works, but the replaying kernel is then v4.35.0-rc3, not the pinned v4.33.1 kernel, and
its hard-coded primitives (`String.ofList`, `eagerReduce`, …) are those of a newer core than the
exported declarations. I recommend the patched v4.33.1 build (kernel = TRUST.md item 1); TRUST.md
must list whichever is used.

## 4. Dry runs (`sorryAx` temporarily permitted)

Environment facts:
* Landlock: kernel `6.18.44-fc`, Landlock ABI **v7**. landrun refuses without `--best-effort`
  ("wanted Landlock V9"); comparator always passes `--best-effort`, and then the sandbox is
  enforced: measured, a write outside the `--rwx` directory gives `Permission denied`, network
  (`curl https://github.com`) fails.
* **Not met here** (comparator README assumptions 6 and the systemd note): the session runs as
  **root**, and PID 1 is not systemd (`process_api`), so `systemd-run
  --property=RestrictAddressFamilies=~AF_UNIX` is unavailable. `scripts/comparator.sh run --release`
  refuses both situations; the dry runs below use the non-release path, which warns.
* `.lake/packages` (Mathlib, FC, …) prebuilt; in the scratch copy it is a symlink, hence read-only
  inside the sandbox (the sandbox may write only `<scratch>/.lake`).

Runs (`scripts/comparator.sh run --allow-sorry --scratch DIR --tools /root/tools`, config
`comparator/config.json` plus `sorryAx`):

| Run | What | Result | Wall time |
|---|---|---|---|
| D1 | `--prebuilt` (project `.olean`s copied) | `Lean default kernel accepts the solution` / `Your solution is okay!`, exit 0 | 53 s |
| D2 | D1 with the **release** config (no `sorryAx`) | `uncaught exception: Illegal axiom detected: 'sorryAx'`, exit 1 (expected until P4) | 33 s |
| D3 | faithful: no `--prebuilt`; comparator builds `Challenge`, then builds `EG.*`, `EGCheck.BridgeLemmas`, `EGCheck.BridgeCore` and `Solution` **inside landrun** | `Your solution is okay!`, exit 0 | 56 s |
| D4 | D1 with the unpatched v4.35.0-rc3 comparator | `Your solution is okay!`, exit 0 | 69 s |

Order as required by comparator: `lake build Challenge` (FC closure only) runs before any project
module is compiled; in D3 no project `.olean` existed before comparator started.

## 5. Red team (`redteam/bridge/run.sh --tools /root/tools`; all with `sorryAx` permitted)

| Case | Result | Message |
|---|---|---|
| honest (`comparator/Solution.lean`) | accepted, exit 0 | `Your solution is okay!` |
| F1 `IsCycleOrEdge := True` | rejected, exit 1 | `Const does not match between challenge and target 'Erdos184.IsCycleOrEdge'` |
| F2 `O(n^2)` statement | rejected, exit 1 | `Challenge and solution theorem statement do not match: 'Erdos184.erdos_184'` |
| F3 `bogus : False := True.intro` via `addDecl` under `debug.skipKernelTC` (attack D) | rejected, exit 1 | `while replaying declaration 'Erdos184.bogus': (kernel) declaration type mismatch` |
| F4 `axiom cheat : False` | rejected, exit 1 | `Illegal axiom detected: 'Erdos184.cheat'` |
| F5 Solution imports the upstream module | rejected, exit 1 | build fails (declaration clash), `Child exited with 1` |

Total 4 min 13 s. F3 was also rejected by the v4.35.0-rc3 build (D4 setting).

## 6. `staging/Final.lean.proposed`

* First line `import FormalConjectures.ErdosProblems.«184»`, then `import EGCheck.Bridge`.
* `theorem EGCheck.erdos_184.{u} : type_of% @_root_.Erdos184.erdos_184.{u} := EGCheck.Bridge.solution`.
* `#guard_msgs` on `#print axioms` unchanged.
* `run_cmd`: module origin of `Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge`
  (`FormalConjectures.ErdosProblems.«184»`) and `SimpleGraph.IsDecomposition`
  (`FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Decomposition`); `EGCheck.erdos_184`
  declared in the current module; both theorems `.thmInfo`; both definitions `.defnInfo`; then the
  old universe-count and `Expr.equal` checks.
* Second `/-! -/` turned into `/- -/`; module docstring states that the in-band checks are advisory.

Measured (scratch copies; nothing in the repository was replaced):
* Against the real bridge: the only error is the `#guard_msgs` (sorryAx); no linter warning.
* Attack C (fake `Erdos184.erdos_184` in a Mathlib-only `EGCheck/Bridge.olean`): **proposed:
  `import EGCheck.Bridge failed, environment already contains 'Erdos184.erdos_184' from
  FormalConjectures.ErdosProblems.«184»`**; current Final.lean: exit 0, no message (passes).
* Attack B0 (`EGCheck.Erdos184.erdos_184` shadow): proposed: type mismatch at elaboration
  (`_root_`); current: caught only by `run_cmd`/guard.
* `lint.py` and `lint.py --release` on a scratch tree with the proposed file as
  `EGCheck/Final.lean`: 0 findings.
* `scripts/FinalCheck.lean --allow-sorry --pin-file staging/TRUST.md.proposed` on the proposed file
  (compiled without the `#guard_msgs` into a scratch `EGCheck/Final.olean`): origin, replay (1383
  project constants), kinds, statement (`Expr.equal`), axioms (exactly the three + sorryAx warning),
  policy, meta and both pins **PASS**; the only FAIL is `oleans` (the scratch `.olean` location).
* The in-band checks remain spoofable by elaborator overrides and kernel bypasses in imported
  modules (A, A1, A3, B1, D): by design they are advisory now.

## 7. `staging/TRUST.md.proposed`

Merges the three hardening proposals (`staging/TRUST.md.external.md`, `work/trust/tooling.md`,
this file): claim as elaborated from the pinned file in an upstream-only environment;
`STATEMENT.md` as the elaborated statement with the `EG-PIN` lines (FinalCheck reads them from
TRUST.md; **verified**: `lean-githash`, `statement-sha256 4cb2cd56…`, `closure-sha256 39d6e8c3…`
PASS against the proposed file); complete trusted list (kernel v4.33.1 as run by the three checkers;
the three axioms; the two upstream files; Init, Batteries `4488d40d`, Mathlib `0df444a3`, FC's three
constants; the elaboration frontend; Lake, the Mathlib cache, CI installers/actions; the pinned
checkers and comparator's assumptions); in-band checks advisory; out-of-band acceptance criterion
(check_pins + comparator check → comparator `--release` + `leanchecker --fresh EGCheck.Final` +
strict `FinalCheck.lean`, order and snapshot); pinned checker versions; stage α/β/γ section (α: a
protected artifact proving the upstream statement from three locked Props — Lovász 1968, Haxell 1995,
Euler — whose texts are trusted at α/β and written/approved in P2; "EG is not trusted" only at γ and
only under the out-of-band criterion); process note (user's diff review is the operative guarantee).

## 8. For the integrator (outside my files)

1. **Protected changes to approve:** `staging/TRUST.md.proposed`, `staging/Final.lean.proposed`,
   `staging/lakefile.toml.proposed` (adds the `Challenge`/`Solution` libs; until then
   `scripts/comparator.sh run --scratch DIR` works on a copy). Re-lock afterwards.
2. **`.github/workflows/release.yml` comparator job** (tooling agent's file) needs updating:
   * its byte-identity step derives the path from the module name (`Challenge` → `Challenge.lean`
     at `formal/`), but the file is `comparator/Challenge.lean`: replace the step by
     `scripts/comparator.sh check`;
   * it builds comparator unpatched with v4.35.0-rc3 and lean4export `15f6055e` (v4.33.0 tag).
     That combination is viable (D4), but the pinned setup measured here is
     `scripts/comparator.sh tools` (patched, v4.33.1; lean4export `66f1fb4b`) and
     `scripts/comparator.sh run --release --system-unit` (runs `sudo systemd-run --uid/--gid` with
     `RestrictAddressFamilies=~AF_UNIX`, as the workflow does now).
3. **`scripts/lock.py` PROTECTED_FILES:** add `comparator/Challenge.lean`, `comparator/config.json`,
   `comparator/patches/**`, `redteam/bridge/**` (`scripts/comparator.sh` is covered by `scripts/**`).
4. **Lint rule suggestion:** nothing that `comparator/Solution.lean` imports may import
   `FormalConjectures.ErdosProblems.*` — today `EGCheck/BridgeLemmas.lean` and
   `EGCheck/BridgeCore.lean`. Comparator catches a violation (F5) but only at release.
5. **AGENTS.md:** `EGCheck/BridgeLemmas.lean` and `EGCheck/BridgeCore.lean` are now `module`s (the
   Solution is a module and can only import modules); the "EGCheck files are non-module" rule has
   this exception.
6. `scripts/gen_roots.py` would add `EGCheck.BridgeCore` to `EGCheck.lean` (not needed: it is built
   through `EGCheck.Bridge`).
7. **Stage α and comparator.** Comparator compares against the *unconditional* upstream
   Challenge, so it cannot check a stage-α artifact directly. A stage-α Challenge must contain the
   three hypothesis Props; if they mention EG definitions, those definitions become part of the
   trusted Challenge closure at α. To be designed in P2 together with `EGCheck/FinalAlpha.lean`.
8. Remove `EGCheck/Smoke.lean` before release (it still has `sorry`; both audits).
9. Optional: build nanoda (`cargo` is available) and register it in `external_kernels` for a
   second, independent kernel; not done.
