# Independent re-audit, round 3, of the trust setup (opus)

Date: 2026-09-26. Reviewer: Claude Opus 5.5, independent re-auditor.
Scope: the setup as if `staging/TRUST.md.proposed`, `staging/Final.lean.proposed`,
`staging/lakefile.toml.proposed` (and `staging/claude-settings.json.proposed`) were applied, together
with the committed round-3 hardening: `scripts/pristine.sh` (the gate), the rewritten
`.github/workflows/{release,ci}.yml`, the N4/N6 fix in `scripts/FinalCheck.lean`, `python3 -I`
everywhere. Read first: `trust2.opus.md` (REJECT, N1–N4), `trust2.fable.md`,
`work/trust/{finalcheck2,gate2,tooling,bridge,external}.md`, `staging/TRUST.md.gate.md`,
`redteam/**`, comparator sources (`fd5d5bcf` + patch), landrun `811cfff5` and go-landlock v0.9.0.

Rules kept: this file and `work/trust/trust3-opus2.md` (details, commands, logs) are the only
repository files I wrote. No git command modified the repository. Every experiment ran in
`mktemp -d` clones under the scratchpad (`…/scratchpad/r3o.23iV/`, "`$R`"); the proposals were
applied only in the clone `$R/staged` (committed there, gate re-pinned there with `--write-pins`).
The external red-team ran inside a mount namespace in which the real repository was bind-mounted
read-only. One lake build at a time; `leanchecker --fresh` was not re-run (opus-2 measured it on
N4; nothing it checks changed).

## Verdict: REJECT (targeted)

The **design and the committed implementation are now sound against every attack of the three
previous audits**, measured (§1): N1–N3 are closed by the gate, N4/N6 by the new FinalCheck, and
comparator still rejects F1–F5. I found no new way to make a false theorem pass *when the release
procedure is run with a user-approved trust commit and Landlock is really enforced*.

The rejection is about the two conditions in that sentence, which the proposed trust document
does not state and the workflow does not enforce:

* **B1 (blocking, documentation). `TRUST.md.proposed` does not describe the procedure that now
  exists, and omits what a reader must trust for it.** It was written before the gate landed and
  `staging/TRUST.md.gate.md` was never merged. Concretely it says, falsely at this revision:
  release.yml "builds comparator unpatched with toolchain v4.35.0-rc3" (§2 item 1, §4.2 step 1);
  "No check enforces this absence yet" (§2 item 7); steps 0a, 0b, 0d, 0e and 1 "not implemented"
  and "no release may be claimed through `release.yml` yet" (§4.2). It does **not** list the gate
  (`scripts/pristine.sh`, its SHA-256 or the trust commit) as trusted, does not say that a
  `release.yml` run is evidence only if the workflow and the whole trusted zone at the tested
  commit equal the approved trust commit (checked offline), and does not mention `EG_TRUST_REF`.
* **B2 (blocking before any release claim, enforcement). The load-bearing check's sandbox is not
  self-verified.** comparator always calls landrun with `--best-effort` (hard-coded,
  `Main.lean` `buildLandrunArgs`). In go-landlock v0.9.0 (`restrict.go`), best-effort on a kernel
  without Landlock downgrades to an empty ruleset and returns success ("Nothing to restrict") —
  no filesystem restriction and not even `PR_SET_NO_NEW_PRIVS`; landrun still logs "Landlock
  restrictions applied successfully". `comparator.sh run --release --system-unit` starts the unit
  with `sudo systemd-run` and only `RestrictAddressFamilies=~AF_UNIX`, without
  `NoNewPrivileges=yes`, and GitHub-hosted runners give the `runner` user password-less sudo. So on
  a runner whose kernel does not enable Landlock, the Solution build (project code with IO) runs
  unsandboxed with a path to root in the same job as the comparator process, silently. Landlock on
  GitHub's runner kernel has never been measured (tooling.md, gate2.md). *Source-verified, not
  demonstrated* (I cannot disable Landlock on this kernel). Fix (small): a canary step that must
  fail (e.g. `landrun --best-effort --ro / --rwx "$d" -- touch "$HOME/canary"`), a check of
  `/sys/kernel/security/lsm` / the Landlock ABI, and `--property=NoNewPrivileges=yes` on the
  systemd unit; add "Landlock is enforced (checked by the canary)" to TRUST §2 item 8.

`Final.lean.proposed` and `lakefile.toml.proposed`: **no objection**, provided they are applied
together with the red-team expectation update of R1 below and a gate re-pin.

## 1. Re-run of every earlier attack (proposals applied in `$R/staged`)

| Harness | Result |
|---|---|
| gate: `redteam/gate/run.sh --repo $R/staged` (N1, N1c/e/g/k/m/n/r/t/u/v/x, N2, N2c/m/p/p-ref/p-self/s, N3, N3c/n/p/r/s/v, X1–X22, controls) | **53/53 as expected**, `GATE REDTEAM: PASS` |
| gate on the staged clone (strict, after `--write-pins`) and on a fresh clone of HEAD | `PRISTINE: PASS` (100/100 pins); HEAD gate sha256 `12a7eb96…` = gate2.md; staged gate `18337c5c…` |
| snapshot of a fresh staged clone, `lock.py files --strict` from it | snapshot PASS (281 files); lock: 108 PENDING / 5 violations (unlocked + other agents' EG/Defs edits): fails closed, as documented |
| external: `redteam/external/redteam.sh --keep` (staged; proposed `Final.lean` in-band) | A, A1, A3, A4, D, **N4**, t1–t3, t5–t9: out-of-band **catch**; A2, **B1, C**: caught in-band (proposed `_root_`/import order) and so never reach FinalCheck; t4, IO: miss by design. Harness prints `REDTEAM: FAIL (2 mismatches)` = B1, C (see R1) |
| N4 log | `[FAIL] origin: EGCheck.RTX1 lists kernel constant EGCheck.RTX.bogus in extraConstNames without declaring it`; `[FAIL] origin: … attributed to (some EGCheck.RTX1)`; `[FAIL] replay: … '_egFinalCheckReplay.EGCheck.RTX.bogus'` — three independent rules |
| tooling: `redteam/tooling/run.sh` | 14/14 as expected (incl. Init, ModHook, RunTac, Bypass) |
| comparator: `redteam/bridge/run.sh --tools /root/tools` (staged lakefile, `RT_DIR=mktemp -d`) | honest accepted; F1 `Const does not match … IsCycleOrEdge`, F2 `statement do not match`, F3 `kernel rejects`, F4 `Illegal axiom … Erdos184.cheat`, F5 clash: **0 failures** |

N6 (different checkers see different copies of a duplicated theorem): closed by design in the new
FinalCheck — `collectProjDecls` takes each declaring module's own `ConstantInfo`, every copy is
replayed separately and the axiom walk follows every copy; duplicates are only allowed for
same-type theorems and never for the four fixed names. I read the code (`FinalCheck.lean`
560–720, 832–875) and found no remaining attribution path (a short `constants` array is skipped
exactly as `importModules` skips it).

## 2. New search: code-before-check, attribution, loader, workflow, self-verification

| Probe | Result |
|---|---|
| Gate coverage of Lake/elan/Python/git/editor vectors | complete for the vectors I could name beyond the 53 cases (root and nested `lean-toolchain`, `leanpkg.toml`, committed `.lake`, `.pth`, native modules, `.gitattributes`, local hooks/config); Python additionally runs with `-I` everywhere I looked |
| Self-verification (N2 class) | **still open unless `EG_TRUST_REF` is set and the tested workflow is the approved one.** Without it every job runs the checkout's own gate (`N2p-self` PASS, as documented). Even with it, a tag/dispatch run uses the workflow file of the tested commit, which can simply skip the gate. Only an offline `--trust-ref` check (or `git diff --quiet <trust> <release> -- <trusted zone>`) makes a green run evidence. Not in TRUST.md.proposed (B1) |
| `EG_TRUST_REF` kind | the workflows fetch it only as a tag; tags (and branches) are movable by anyone with push rights. Recommend a full commit id |
| Comparator ordering | Challenge built and **exported before** the Solution is built (`compareIt`), so the Solution build's write access to `.lake` (it includes `.lake/packages` in the release layout) can only affect the Solution export, which is compared and replayed. Holds only with Landlock enforced (B2) |
| Artifact install in `verify` | validation (Python `tarfile`) and extraction (GNU `tar`) are different parsers, so the member-name allowlist is only as good as their agreement. Impact is bounded (writes stay under the snapshot's `lib/lean`; the statement pins and comparator are independent), but use one parser: validate and extract with `tarfile.extractall(filter="data")` into a fresh directory outside the snapshot, then `find` it against the allowlist |
| Unpinned data read by trusted-job scripts | `LOCK.json`, `status/ratchet.json` (and `CONVENTIONS.md`, `EG/Spec/**`, `EG/Defs/**`) are *not* in the gate's pinned zone; `lock.py` checks the tree against the `LOCK.json` of the same tree. Harmless at γ (lock is hygiene), but at **stage α** the locked hypothesis texts are trusted, and nothing non-self-verifying protects them. Put `EG/Spec/**` + `LOCK.json` into the trusted zone / trust-ref comparison from the P2→P3 freeze |
| `.olean` loader residual | unchanged; correctly listed as trusted (§2 item 9) |
| CI | regression guard only; its comment "nothing the checks rely on may have changed" overstates (build-time code runs as the snapshot's owner and can `chmod`/rewrite it, including the gate copy used for the re-check) |

## 3. Does TRUST.md.proposed state exactly what a reader must trust?

Correct and complete: the claim, `STATEMENT.md` and its pins (provenance now recorded), kernel,
axioms, upstream pins, the closure, the elaboration frontend with `leanOptions`, the Mathlib cache
caveat, the loader residual, the α/β/γ staging, comparator as the load-bearing check with
FinalCheck and `leanchecker --fresh` as defence in depth, and the N4 description of FinalCheck.

Not exact (all must be fixed before it is applied): B1 above; §2 item 8 must add "Landlock is
actually enforced" (B2); §4.4 (reader's recipe) must also check `formal/lean-toolchain` (elan
follows it to any GitHub-hosted toolchain) and should use the trust-ref gate or a `git diff` of the
whole trusted zone against the trust commit instead of the two spot checks; §6 must say the gate's
pin block is the operative protection list and which listed files it does *not* pin (above).

## 4. Required changes

Blocking:
1. **Merge `staging/TRUST.md.gate.md` into `TRUST.md.proposed` and re-mark §4.2** against the
   committed `release.yml` (0a–0g and 1 are now implemented; 0f is file part first, from the
   snapshot). Add to §2: the gate (sha256 or trust commit) as trusted; "a `release.yml` run is
   evidence only together with an offline check that the tested commit's trusted zone and
   workflows equal the approved trust commit"; `EG_TRUST_REF` = a full commit id.
2. **Landlock enforcement (B2):** canary + LSM/ABI check in the comparator job before comparator
   runs, `NoNewPrivileges=yes` on the systemd unit (`comparator.sh`), and the TRUST §2 item 8 text.

Required with applying `Final.lean.proposed`:
3. **R1.** Update `redteam/external/redteam.sh` expectations: B1 and C become `caught` in-band,
   and the harness should still run FinalCheck on them against a dev final so that out-of-band
   coverage of B1/C stays exercised. Otherwise CI's slow red-team step fails as soon as the file
   is applied. Re-pin the gate (`--write-pins`) and review the pin diff in the same approval.

Recommended:
4. Single-parser artifact extraction (§2).
5. Gate-pin `EG/Spec/**` and `LOCK.json` from the statement freeze on (stage α).
6. Reader's recipe: add the `lean-toolchain` check and the trust-ref `git diff`.
7. Soften the CI post-build comment; keep calling CI regression-only.

## 5. Evidence

`$R` = `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/r3o.23iV`:
`gate_rt.log`, `external.log` (per-attack logs in `/tmp/rt-external.EhNo27/`), `tooling.log`,
`bridge.log`, `staged/` (proposals applied, gate re-pinned), `snap.*/`. Commands and details:
`formal/work/trust/trust3-opus2.md`.
