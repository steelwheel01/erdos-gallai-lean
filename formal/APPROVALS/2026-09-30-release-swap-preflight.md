# 2026-09-30 — Release verify job: swap-backed memory preflight (TRUST.md §4.3 step 0a)

**User approval (2026-09-30):** chose "Add swap on runner (Recommended)" in answer to the choice between
(1) adding swap on the runner and requiring RAM + swap ≥ 16 GB, (2) a larger paid GitHub runner
(`EG_RELEASE_RUNNER`), and (3) stopping and documenting that the verify job did not run on GitHub.

**Trigger.** Release run 36758690862 (tag `release-2026-09-30` → d249d5f = `EG_TRUST_REF`): comparator
job SUCCESS in release mode ("Your solution is okay!"), build job SUCCESS, verify job stopped at the memory
preflight before checkout: `MemTotal: 7 GiB` (GitHub's standard runner for this private repository).

**Change.**
* `.github/workflows/release.yml` (verify job):
  * new step "Add swap if RAM + swap < 16 GB", before the preflight and the checkout: if
    MemTotal + SwapTotal < 16.5 GB, `fallocate` a 12 GiB `/eg-swapfile`, `mkswap`, `swapon`
    (system level, outside the checkout, before any project code);
  * the preflight now requires MemTotal + SwapTotal ≥ 15.5 GB (was MemTotal alone);
  * `timeout-minutes` 300 → 360 (the GitHub-hosted maximum), since swapping slows `leanchecker --fresh`;
  * header comment updated. Nothing else changes; every check step is untouched.
* `TRUST.md` §4.3 step 0a and §8 item 1 (runner bullet): new wording staged as
  `staging/TRUST.md.proposed` (sha256 803dee98…). TRUST.md is edit-denied for the integrator: the user applies it.

**Why rigor is unchanged.** Swap is transparent to every program: it changes speed, never results. An
out-of-memory kill ends the step with a non-zero status, which fails the job; it cannot produce a pass.
The verify job still never compiles or executes project code, and every check it runs (gate against
`EG_TRUST_REF`, FinalCheck strict, `leanchecker EG`, `leanchecker EGTest`, `leanchecker --fresh
EGCheck.Final`) is unchanged. Evidence the runner class copes: formal-ci run 36756211520 (same commit,
same 7 GiB runner class) passed per-library `leanchecker EG` / `EGTest` and the FinalCheck scan.
Risk: `--fresh` may be slow under swap; if it exceeds 360 min the job fails (no verdict), and the
remaining options are a larger runner or the manual audit.

**Integrator run (workflows).** `sh scripts/pristine.sh --write-pins`: exactly one pin changed
(`.github/workflows/release.yml` f9a772c5… → 8121c569…); `--dev` DEV-PASS. Gate SHA-256 after this step:
`11a0ab30f4d0335f6d621a105c9f1292e6c596be6b52491bf97096ef9876c10c`. After the user applies
`staging/TRUST.md.proposed`, the integrator re-pins (TRUST.md pin) and records the final gate SHA-256 and
the new `EG_TRUST_REF`; the user then updates the variable and pushes a new `release-*` tag.

**TRUST.md applied (2026-09-30)** by the user from their own machine (commit `09b5366`, "Apply TRUST.md 4.3 0a:
swap-backed memory preflight (user-applied)"); byte-identical to `staging/TRUST.md.proposed`.
`--write-pins`: exactly one pin changed (`formal/TRUST.md` 664d47f7… → 803dee98…); `--dev` DEV-PASS.
Lock re-hashed under this record (`lock.py update --modules EG.Spec.Main`: release.yml, TRUST.md,
pristine.sh file hashes); `lock.py check --strict`: 1234 constants / 277 files, 0 violations.
**Final gate SHA-256:** `99f1f34f03a9f56bd036d12b7523b3dffc4c15820b4c6209363dfbb99a0f234c`.
The integrator commit following `09b5366` is the new `EG_TRUST_REF`; its full SHA is recorded in STATE.md.
