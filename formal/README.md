# formal/ — Lean 4 formalization of the Erdős–Gallai candidate proof

**Status: candidate proof, AI-generated and AI-reviewed; a Lean 4 proof of the formal-conjectures
statement Erdos184.erdos_184 passes the project's acceptance checks; not yet reviewed by human
experts.** The mathematics being formalized is a *candidate* proof (`../proofs/manuscript/`),
checked so far only by AI referees. The current state, the trust model in brief and the
verification record are in the repository's `../README.md`; the acceptance record is
`work/p3/ACCEPT.md`. The rest of this file is the working guide written during the formalization
and is partly out of date (for example "fails until P4" below: the final check now passes).

Target: `Erdos184.erdos_184` from google-deepmind/formal-conjectures, pinned in `TRUST.md`.
Toolchain Lean `v4.33.1`, Mathlib `v4.33.1`. Plan: `../PLAN_FORMALIZATION.md`.

## Layout

| Path | Contents | Protected? |
|---|---|---|
| `EG/Defs/**` | definitions (objects, graphs, distributions, …) | yes |
| `EG/Spec/**` | frozen statements, as `def X : Prop` | yes |
| `EG/Lib/**` | general helper lemmas | no |
| `EG/Proof/**` | proofs of the `Spec` statements | no |
| `EGTest/**` | unit tests, non-vacuity, multigraph falsity | no |
| `EGCheck/Bridge.lean` | internal theorem ⇒ upstream statement | no (kernel-checked) |
| `EGCheck/Final.lean` | final check: type equality, `#print axioms` guard | yes |
| `scripts/`, `LOCK.json`, `TRUST.md`, lake files | tooling and pins | yes |

"Protected" paths are changed only by the integrator through the procedure in
`APPROVALS/README.md`; `scripts/lock.py check` (CI) detects any change to a locked statement or
to a definition it depends on. `.claude/settings.json` denies file-edit tools on the
trust-boundary files (`TRUST.md`, lake files, `EGCheck/Final.lean`) now, and on `EG/Spec/**`,
`EG/Defs/**` and the tooling from the P2→P3 statement freeze on (phased; user decision
2026-09-25).

## Commands (from `formal/`)

```
lake exe cache get              # Mathlib cache (host must be reachable; else Mathlib builds from source)
lake build EG EGTest EGCheck    # build everything except the final check
scripts/check.sh EG/Proof/X.lean              # elaborate one file with a time limit
lake env lean --run scripts/Axioms.lean EG    # axiom scan + sorry frontier
python3 scripts/lint.py [--release]           # forbidden tokens
python3 scripts/lock.py check                 # statement lock
python3 scripts/status.py                     # dashboard (status/STATUS.md)
./scripts/check_pins.sh                       # trusted pins
lake build EGCheck.Final                      # the release check (fails until P4)
```
