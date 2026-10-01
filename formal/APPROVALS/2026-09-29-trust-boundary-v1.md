# 2026-09-29 — Trust boundary v1 (TRUST.md §8 items 9–10): approval

**User approval (quoted, AskUserQuestion, 2026-09-26T18:17Z).** Question:

> May I apply the audited trust-boundary proposals (staging/*.proposed) under one approval record?
> They: (1) replace formal/TRUST.md (64→~700 lines, marked DRAFT/pre-release): acceptance becomes
> out-of-band — comparator is the load-bearing check, FinalCheck + leanchecker --fresh are defence
> in depth, the in-band Final.lean checks are advisory; full trusted-components list; 13 open
> release blockers listed (e.g. nothing yet run on GitHub, sandbox unverified on the runner,
> stage-α texts not yet pinned, proof not finished); (2) harden EGCheck/Final.lean (imports
> upstream 184 first, @_root_ statement, module-origin + theorem-kind checks, advisory docstring);
> (3) add the comparator Challenge/Solution libs to lakefile.toml; (4) extend the .claude deny
> list (STATEMENT.md, LOCK.json, lakefile.lean, comparator challenge/config/patches). I'd then
> refresh the gate pins, update the lock, and record the approval. None of this changes any
> mathematics or the target statement pin.

Answer: **"Yes, apply all four (Recommended)"**.

## What changed

| File (pinned by the gate) | Source | Change |
|---|---|---|
| `formal/TRUST.md` | `staging/TRUST.md.proposed` | full trust document (DRAFT, pre-release); out-of-band acceptance; 13 open release blockers |
| `formal/EGCheck/Final.lean` | `staging/Final.lean.proposed` | imports upstream `FormalConjectures.ErdosProblems.«184»` first; `type_of% @_root_.Erdos184.erdos_184.{u}`; origin and kind checks; ADVISORY docstring |
| `formal/lakefile.toml` | `staging/lakefile.toml.proposed` | adds `Challenge`/`Solution` libs (srcDir `comparator`, not default targets); comment fix `lint.sh` → `lint.py` |
| `.claude/settings.json` | `staging/claude-settings.json.proposed` | deny list extended by `STATEMENT.md`, `LOCK.json`, `lakefile.lean`, `comparator/{Challenge.lean,config.json,patches/**}` |
| `formal/redteam/external/redteam.sh` | `staging/redteam.sh.proposed` | consequence of the `Final.lean` change (test harness only): B1 and C are now caught in-band, verdict `inband+oob` (`staging/redteam-expectations.proposed.md`, TRUST.md §8 item 8). Applied in this same approval as the proposal specifies; it changes no check, only the expected verdicts of two attacks. |

Unchanged: `lean-toolchain`, `lake-manifest.json`, the formal-conjectures pin
(2424bb480c590237ffbb2cc831ae4cb8977e045a), the target statement, the allowed axioms
(`propext`, `Classical.choice`, `Quot.sound`), every `EG/Spec` statement and `EG/Defs` definition.

## Reviews

Four audit/hardening rounds and two consistency checks: `APPROVALS/reviews/trust.{opus,fable}.md`,
`trust2.*`, `trust3.*`, `trust4.consistency.md`, `trust5.consistency.md` (verdict: consistent),
work notes `work/trust/*.md`.

## Integrator run

Recorded below after application (gate pins, gate SHA-256, lock, build).

**Status 2026-09-29: NOT APPLIED.** The user re-authorized the copies explicitly (AskUserQuestion,
2026-09-29: "Yes, run the copies (Recommended)"), but the session's permission layer denied every
write to the edit-denied files, including a plain `cp`. No workaround was attempted. The five
proposals remain in `staging/`; the trusted zone and all 100 gate pins are unchanged. To apply,
the user (or a session whose permissions allow it) runs the integrator steps in
`staging/redteam-expectations.proposed.md` and `sh formal/scripts/pristine.sh --write-pins`,
then records the new gate SHA-256 here.

**Applied 2026-09-29** by the user from their own machine (commit `1021ca9`, "Apply trust boundary v1
(user-applied …)"), after the user was given the exact command (the session's permission layer
blocked the integrator). Integrator checks on this tree:
* each of the six files is byte-identical to its `staging/*.proposed` source; `redteam.sh` mode 100755;
* `sh scripts/pristine.sh --write-pins`: exactly six pins changed (`.claude/settings.json`,
  `.github/workflows/ci.yml`, `EGCheck/Final.lean`, `TRUST.md`, `lakefile.toml`,
  `redteam/external/redteam.sh`); `--dev`: 100/100 pins match, DEV-PASS;
* the `.github/workflows/ci.yml` change is the one-line toolchain-fingerprint fix
  (`! -path "$HOME/.elan/known-projects"`) that CI run #3 needed; the user's command applied it
  together with the other five, as the integrator's instructions to the user said;
* `lock.py update --approval <this file> --modules EG.Spec.Main`: re-hashes the protected files only
  (no probe draft locked); `lock.py check`: 865 constants, 153 files, 0 violations;
* `lake build EGCheck.Final` fails ONLY at the axiom guard: expected
  `[propext, Classical.choice, Quot.sound]`, got `[propext, sorryAx, Classical.choice, Quot.sound]`
  (the open `EG.Proof.mainInternal`); the type equality, origin and theorem-kind checks pass.

**New gate SHA-256 (`formal/scripts/pristine.sh`, 100 pins):**
`940ccbf0da5cbd2f0890523cac098f1857f326042864f678b56c5c34dd559c5c`

**Remaining user action (TRUST.md §7):** set the repository variable `EG_TRUST_REF` to the full
40-hex SHA of the commit that carries these pins (the integrator's commit following `1021ca9`).
