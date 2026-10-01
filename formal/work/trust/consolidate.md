# Trust consolidation after round 3 (agent `consolidate`, 2026-09-26)

This round consolidates the findings of the two round-3 audits:
* `APPROVALS/reviews/trust3.opus.md`: REJECT (targeted), blocking items B1 and B2;
* `APPROVALS/reviews/trust3.fable.md`: APPROVE WITH NOTES, three items that block a first release.

It also draws on `work/trust/*.md` and `staging/*`.

Rules kept:
* No edit-denied file was touched: `TRUST.md`, `EGCheck/Final.lean`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain`, `.claude/**`.
* No git command modified the repository. Commits were made only inside `mktemp -d` clones.
* No Lean statement was changed.
* Every experiment ran in `mktemp -d` directories.
* The external red-team ran under a read-only bind mount of the real repository.

## 1. Files changed

| File | Change | Audit item |
|---|---|---|
| `staging/TRUST.md.proposed` | Rewritten against the current implementation (see §2) | opus B1, R6; fable §4 items 1–7 |
| `scripts/status.py` | New `--no-write`: compute and enforce the ratchet, print the dashboard, write no file. Unknown arguments are an error. | fable blocking 2 (§3.5) |
| `.github/workflows/release.yml`, `ci.yml` | Status step becomes `status.py --check --no-write` | fable blocking 2 |
| | Gate step validates `EG_TRUST_REF`: 40 lower-case hex, checked *before* git sees it; fetched by id if missing; must resolve to itself as a commit. Anything else is `::error::` and exit 1. | fable blocking 3 |
| | `release.yml` without `EG_TRUST_REF` emits a `::warning::` that the run self-verifies | opus §2 |
| | Header comments corrected, including CI's post-build limit | opus R7; fable R3 |
| `scripts/pristine.sh` | `--trust-ref` accepts only a full 40-hex commit id. A tag, branch, abbreviated id or tag-object id is a `REJECT trustref` (exit 1). Pins refreshed as the last step (§4). | fable blocking 3, Y11b |
| `redteam/gate/run.sh` | New cases `N2p-tag` (moved lightweight tag), `N2p-short` (abbreviated id), `N2p-tagobj` (annotated tag object id) | same |
| `scripts/comparator.sh` | New `canary` subcommand and `landlock_canary`, run by every `run` (all modes) | opus B2 |
| | `--release`: systemd unit gets `--property=NoNewPrivileges=yes`, and runs the canary again inside the unit with `--expect-nnp` before comparator | opus B2 |
| `redteam/bridge/run.sh`, `README.md` | New case `C0_UnconfinedLandrun`: a pass-through landrun must make the harness refuse. `RT_DIR` now defaults to `mktemp -d`. | opus B2; fable R5 |
| `comparator/README.md` | New section "Sandbox checks of the harness" | opus B2 |

### The Landlock canary

`scripts/comparator.sh canary [--tools DIR | --landrun FILE] [--expect-nnp]` fails closed (exit 2)
unless all of the following hold:
1. `landlock_create_ruleset(NULL, 0, LANDLOCK_CREATE_RULESET_VERSION)` (syscall 444, via
   `python3 -I` + ctypes) reports ABI ≥ 3. ABI 3 is the first that confines `truncate(2)`.
2. The pinned landrun, with comparator's exact flags (`--best-effort --ro / --rw /dev -ldd
   -add-exec --rwx DIR`), can create a file inside `DIR`. This is the positive control.
3. The same landrun cannot create a file in another directory, and `/proc/self/status` inside it
   shows `NoNewPrivs: 1`. go-landlock sets that only when it really restricts.
4. With `--expect-nnp`, the calling process itself has `NoNewPrivs: 1`. Inside the systemd unit
   this proves that `NoNewPrivileges=yes` took effect.

Inside landrun only shell builtins are used: `/bin/sh` is the only executable in `--rox`. The
out-of-sandbox write runs in a subshell, because in dash a failed redirection on the special
builtin `:` exits the shell (found while testing: exit 2 instead of 98).

`/sys/kernel/security/lsm` is not mounted in this sandbox, so the LSM list is not used. The syscall
query is the kernel's own answer.

## 2. TRUST.md.proposed: what changed

The file was rewritten against `release.yml`, `ci.yml`, `pristine.sh`, `FinalCheck.lean`,
`comparator.sh`, `lock.py` and `lint.py` as they are now. `staging/TRUST.md.gate.md` is merged
into §2 items 7–8, §4.2, §4.3 and §6.

Stale statements removed. Both auditors listed these:
* "release.yml builds comparator unpatched with toolchain v4.35.0-rc3" (§2 item 1, §4 step 1);
* "No check enforces this absence yet" (§2 item 7);
* "N1–N3 are open" (§4.1);
* the "Not implemented / partly implemented" markers of steps 0a, 0b, 0d, 0e, 0f and 1;
* "release.yml does not implement §4 … no release may be claimed through it".

Status line: "DRAFT — pre-release; the acceptance procedure has not yet been exercised on GitHub".

New or changed content:
* **§2 item 7**: the gate (absence rules, pins, zones, snapshot), and the two anchors: the gate
  SHA-256, or the trust commit `EG_TRUST_REF`, which must be a full 40-hex commit id.
  - It lists what the gate does **not** pin: `LOCK.json`, `status/**`, `CONVENTIONS.md`,
    `EG/Spec/**`, `EG/Defs/**` (opus §2, fable Y3/Y7).
* **§2 item 8**: a run is evidence only with the offline check. The run executes the tested
  commit's workflow file.
* **§2 item 9**:
  - Landlock is actually enforced, checked by the canary;
  - `NoNewPrivileges=yes`;
  - landrun's writable set is the whole `.lake`, packages included, and why that is sound (fable
    §3.3).
* **§2 item 6**: the runner-image tools, and the unpinned Go toolchain plus the Go module
  proxy/sumdb (fable §3.6).
* **§3**: `status.py` and all of `ci.yml` are hygiene or regression, with the `--link-lake` limit.
* **§4.2 (new)**: the offline precondition, as `gate.sh --trust-ref T` on the tested commit `R`, or
  a `git diff T R` of the whole trusted zone.
* **§4.3**: every step as it is implemented, job by job. The artifact validation and extraction
  are described exactly, including the two parsers.
* **§4.5**: the reader's recipe now checks `lean-toolchain`, and that landrun confines (opus §3).
* **§5**: the α criterion is not yet designed. comparator cannot check an α artifact as it stands
  (fable §4 item 6).
* **§6**: the gate's pin block is the operative list, with a new "gate pin" column, and the
  approval procedure (`--write-pins`, `lock.py update`, move `EG_TRUST_REF`).
* **§7 (new)**: the revision record. The gate SHA-256 cannot be recorded inside a pinned file,
  because the gate pins `TRUST.md` (a circularity). §7 therefore records the value for this
  *proposal*, and says that applying the proposals requires a re-pin and a new value, recorded in
  `APPROVALS/`.
* **§8 (new)**: open release blockers, 13 items. They include every audit item not fixed here:
  - opus R1 (external red-team expectations for B1/C once the proposed `Final.lean` is applied);
  - opus R4/fable (single-parser artifact extraction);
  - opus R5/fable R1 (stage-α pinning of `LOCK.json` and `EG/Spec/**`);
  - fable R2 (a workflow independent of the tested commit);
  - fable R6 (`EGCheck/Smoke.lean`);
  - the Go pin, the Mathlib cache, the loader residual, IO in the untrusted build;
  - the GitHub run and the Landlock verification on the target.

## 3. Re-runs (all in `mktemp -d` directories)

`$R` is `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/cons.NpD8aU`. It is a `mktemp -d` under the scratchpad containing:
* `wt/`: a clone of the working tree, committed there and re-pinned there with `--write-pins`;
* the logs.

| Harness | Where | Result | Log |
|---|---|---|---|
| gate red-team (`redteam/gate/run.sh --repo $R/wt`) | re-pinned clone | **56/56 as expected** (the 53 earlier cases plus `N2p-tag`, `N2p-short`, `N2p-tagobj`), `GATE REDTEAM: PASS` | `gate_rt.log` |
| gate red-team (`--from-worktree`, after the final pin refresh) | clones of the real working tree | **56/56**, baseline `PRISTINE: PASS`, gate `a29e7d7d…` | `gate_rt_final.log` |
| workflow gate steps (`scratchpad/wfgate.py`: the `run:` blocks of release.yml `verify`/`comparator` and ci.yml `build`, extracted with PyYAML and run in bash `-eo pipefail`) | clone | **21/21 as expected** (see below) | `wf_gate.log` |
| `status.py` in a read-only snapshot, as uid 65534, fake `lake` | `/tmp/cons-status.vRAPXE` | old `--check`: `PermissionError: [Errno 13] … status/STATUS.md` (fable §3.5 reproduced); `--check --no-write`: exit 0 and no file changed; with `enforce: true` and a grown frontier: `RATCHET: …`, exit 1; unknown argument: exit 1 | — |
| Landlock canary (`comparator.sh canary`) | this kernel (6.18.44, ABI 7, root) | see below | — |
| tooling red-team (`redteam/tooling/run.sh`) | read-only snapshot of `$R/wt` | **14/14 as expected** | `tooling.log` |
| external red-team (`redteam/external/redteam.sh --keep`, committed `Final.lean`) | `$R/wt`, under `unshare -m` with the real repo bind-mounted read-only; work dir `/tmp/rt-external.KmlLYU` | **19/19 OK, `REDTEAM: PASS`** (see below) | `external.log` |
| comparator red-team (`redteam/bridge/run.sh --tools /root/tools`, `RT_DIR=$R/bridge`) | `$R/wt`, real repo read-only | **7/7, 0 failures** (see below) | `bridge.log`, `bridge/*.log` |
| `comparator.sh check`, `lint.py --self-test` | `$R/wt` | `comparator check: OK` (7 ok lines); lint 62/62 | — |
| `lock.py files --strict` | snapshot | fails closed: 2 violations (`EG/Defs/{Graph,Objects}.lean`, changed after locking) and 111 PENDING; needs `lock.py update` under an approval | — |
| actionlint 1.7.7 on both workflows | real tree | no findings | — |

**Workflow gate steps.** Each case ran on each of the three jobs:
* unset `EG_TRUST_REF`: pass. `release.yml` prints the `::warning::`;
* full commit id: `PRISTINE: PASS`;
* lightweight tag, abbreviated id, or a string that starts like an option
  (`--upload-pack=…`): `::error::… full 40-hex commit id`, exit 1, before any git call;
* 40-hex id of an annotated tag object: `::error::… is not a commit of this repository`;
* unknown 40-hex id: the fetch fails, and the step fails.

**Landlock canary.**
* The pinned landrun passes: "ABI 7; a write outside the sandbox was denied; no_new_privs set
  inside landrun".
* It fails closed, with exit 2, in each of these cases:
  - a pass-through landrun: exit 97, no `no_new_privs`;
  - the same wrapper with the caller already under `no_new_privs` (as it would be inside the
    unit): "a write OUTSIDE the sandbox succeeded";
  - a wrapper that hides its exit code: same message;
  - a simulated minimum ABI of 99: "kernel Landlock ABI is 7 (need >= 99)";
  - `--expect-nnp` without `no_new_privs`;
  - a missing landrun.
* Under `setpriv --no-new-privs`, `--expect-nnp` passes.

**External red-team** (committed `Final.lean`):

```
A A1 A3 B1 C A4 D N4   finalattack green  → out-of-band catch   OK
A2                     finalattack caught in-band (n/a)          OK
t1 t2 t3 t5–t9         evasion built      → catch               OK
t4, IO                 evasion            → miss (by design)    OK   (IO wrote only to /tmp)
N4: [FAIL] origin: EGCheck.RTX1 lists kernel constant EGCheck.RTX.bogus in extraConstNames without declaring it
    [FAIL] origin: EGCheck.RTX.bogus (declared by #[EGCheck.RTX2]) is attributed to (some EGCheck.RTX1)
    [FAIL] replay: … '_egFinalCheckReplay.EGCheck.RTX.bogus'
```

With `staging/Final.lean.proposed` applied, B1 and C are caught in-band and the harness reports 2
mismatches (opus R1). This is listed as TRUST §8 item 8 and was not re-run here.

**Comparator red-team** (dry runs as root, `sorryAx` permitted, `--prebuilt --scratch`):

```
ok    C0_UnconfinedLandrun: exit 2, "Landlock canary:"   (canary: exit 97, no no_new_privs)
ok    honest: exit 0, "Your solution is okay!"
ok    F1_DefinitionChanged: exit 1, "Const does not match between challenge and target 'Erdos184.IsCycleOrEdge'"
ok    F2_StatementWeakened: exit 1, "Challenge and solution theorem statement do not match: 'Erdos184.erdos_184'"
ok    F3_KernelBypass: exit 1, "Lean default kernel rejects the solution"
ok    F4_ExtraAxiom: exit 1, "Illegal axiom detected: 'Erdos184.cheat'"
ok    F5_ImportsUpstream: exit 1, "Child exited with"
```

In the six non-C0 runs the canary passed before comparator started.

## 4. Pin refresh (last step)

Command: `sh formal/scripts/pristine.sh --write-pins` in the real working tree, as the last change
to any trusted-zone file. It wrote 100 pins. Exactly the 8 files changed in this round got new
pins:
* `.github/workflows/{ci,release}.yml`;
* `comparator/README.md`;
* `redteam/bridge/{README.md,run.sh}`;
* `redteam/gate/run.sh`;
* `scripts/comparator.sh`;
* `scripts/status.py`.

`pristine.sh --dev` then reports 100/100 pins matching (`DEV-PASS`, because the tree has
uncommitted work). The `--from-worktree` gate red-team baseline, a strict gate on a committed copy,
gives `PRISTINE: PASS`.

**New gate SHA-256: `a29e7d7dc3dfa93f9b9e4fa42ba3431f4308b2b2eb879f1db6cddcd83c94cd9b`**, recorded
in `staging/TRUST.md.proposed` §7. It is valid for the tree with the proposals **not** applied.
Applying the four proposals changes four pins and therefore this hash. The integrator must re-pin
at the approval and record the new value in the approval file, which cannot be inside a pinned
file (TRUST §7).

## 5. Not done / not possible here

* No GitHub run. There is no systemd in this sandbox and it runs as root, so
  `comparator.sh run --release --system-unit` is still unexercised: the canary inside the unit and
  `NoNewPrivileges=yes` are tested only by `setpriv --no-new-privs` locally.
* shellcheck is not available, so the shell inside the workflows was not linted. actionlint 1.7.7
  (built into the scratchpad) reports no findings on both workflows.
* `leanchecker --fresh` was not re-run: nothing it checks changed.
