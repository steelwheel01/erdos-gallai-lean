# Approvals (PLAN_FORMALIZATION.md §4, §9)

Every change to a protected path (`EG/Spec/**`, `EG/Defs/**`, `EGCheck/Final.lean`, `LOCK.json`,
`TRUST.md`, `scripts/**`, lake files, `.github/**`, `.claude/**`) is recorded here as
`APPROVALS/<YYYY-MM-DD>-<label>.md` containing:

1. what changed (constants / files) and why;
2. the reviewer verdicts: two independent clean-room agent reviews of each Tier-1 statement or
   definition (at least one from a different model where available) and the back-translation;
3. the resulting `scripts/lock.py update --approval <this file>` run.

Trusted-boundary changes (pins, allowed axioms, `TRUST.md` after GNG-6) additionally need the
user's explicit approval, quoted in the record.
