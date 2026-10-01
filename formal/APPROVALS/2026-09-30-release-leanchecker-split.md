# 2026-09-30 — Release acceptance: leanchecker per library (TRUST.md §4.3 step 13)

**User approval (quoted, 2026-09-30):** "approve the split" — in answer to the choice between a larger
release runner (`EG_RELEASE_RUNNER`) and splitting the joint `leanchecker EG EGTest EGCheck` call in
`release.yml` and TRUST.md §4.3 step 13 per library (recommended).

**Change.**
* `.github/workflows/release.yml` (verify job): `lake env leanchecker EG` and
  `lake env leanchecker EGTest` as two steps in place of the joint call; the
  `leanchecker --fresh EGCheck.Final` step (TRUST.md §4.3 step 14) is unchanged.
* `.github/workflows/ci.yml`: comment only (already split, APPROVALS/2026-09-30-ci-leanchecker-split.md).
* `TRUST.md` §4.3 step 13: new wording staged as `staging/TRUST.md.proposed` (only that item differs;
  sha256 664d47f7…). TRUST.md is edit-denied for the integrator: the user applies it.

**Why coverage is unchanged.** Every EGCheck module (Bridge, BridgeCore, BridgeLemmas) lies in the
import closure of `EGCheck.Final` (Final → Bridge → BridgeCore → BridgeLemmas); step 14 replays that
whole closure from fresh (measured locally: exit 0, 71 min, 10.7 GB). EG and EGTest keep their own
per-library replay (EG 13.8 min / 12.1 GB, EGTest 1.3 min / 10.7 GB). The joint call needs more than
a 16 GB runner offers (CI run 36693519203 lost its runner in it).

**Integrator run (workflows).** `sh scripts/pristine.sh --write-pins`: exactly two pins changed
(`.github/workflows/ci.yml` 42f897c0… → f4522e68…, `.github/workflows/release.yml` 48b331fe… →
e8665222…); `--dev` DEV-PASS 100/100. Gate SHA-256 after this step: `05493a5717b6f1565c23c17e5be15a1596251070617d272700678aa6b2f9bddf`.
After the user applies `staging/TRUST.md.proposed`, the integrator re-pins once more (the TRUST.md
pin changes) and records the final gate SHA-256 and the commit to use as `EG_TRUST_REF` below.

**TRUST.md applied (2026-09-30)** by the user from their own machine (commit `e0217c5`, "Apply TRUST.md
step 13: leanchecker per library (user-applied)"); byte-identical to `staging/TRUST.md.proposed`.
`--write-pins`: exactly one pin changed (`formal/TRUST.md`); `--dev` DEV-PASS.
**Final gate SHA-256:** `83632a5dd3b03efe9324d21f0d4a4550ff466cf40e4e098d9c9c68fe2324d9d9`.
The commit that carries these pins (the integrator commit following `e0217c5`) is the value for the
repository variable `EG_TRUST_REF`; its full SHA is recorded in STATE.md.
