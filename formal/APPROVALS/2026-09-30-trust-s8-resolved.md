# 2026-09-30 — TRUST.md §8 items 1–2 marked resolved (documentation only)

**User approval (2026-09-30):** asked for "the terminal command to run" to apply the staged change, then applied it from their own
machine (commit `fc15866`, "Apply TRUST.md 8: items 1-2 resolved by release run 36767721300 (user-applied)"); byte-identical to
`staging/TRUST.md.proposed` (sha256 64bd8179…).

**Change.** TRUST.md §8 item 1 ("The acceptance procedure has never run on GitHub") and item 2 ("Landlock and NoNewPrivileges
enforcement is unverified on the target") are replaced by RESOLVED entries citing release run 36767721300 (all three jobs SUCCESS;
record in work/p3/ACCEPT.md) and the Landlock canary lines of the comparator jobs of runs 36758690862 and 36767721300 ("ABI 7; a
write outside the sandbox was denied; no_new_privs set inside landrun; this unit has NoNewPrivileges"). No procedure, pin, check or
workflow changes. The release run's `EG_TRUST_REF` (f7398e1) stays the commit that was checked.

**Integrator run.** `sh scripts/pristine.sh --write-pins`: exactly one pin changed (`formal/TRUST.md`); lock re-hashed under this
record (`lock.py update --modules EG.Spec.Main`); `lock.py check --strict` and `pristine.sh --dev` clean (see commit).
**Final gate SHA-256:** `e8e10825a36148c00db43e5110937782ee2cf5553675e6a8e689f2252ca5051a`; pin `formal/TRUST.md` 803dee98… → b428e6b3…; lock strict 1234/277, 0 violations.
