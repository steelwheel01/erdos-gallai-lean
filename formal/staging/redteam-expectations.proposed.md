# Proposal: external red-team expectations for the hardened `Final.lean` (TRUST.md §8 item 8)

Status: **PROPOSED, not applied.** Prepared 2026-09-26 (`work/trust/docfix.md`). To be applied in the
same approval as `staging/Final.lean.proposed` (TRUST.md §8 item 9).

## Why

`redteam/external/redteam.sh` (CI's slow red-team step) expects the attacks **B1** and **C** to
build green in-band and to be caught by the out-of-band `scripts/FinalCheck.lean`
(`EXPECT[B1]=catch`, `EXPECT[C]=catch`). With `staging/Final.lean.proposed` applied, both are
caught **in-band**. The build of `EGCheck.Final` fails, so the committed harness has no artifact
for FinalCheck, records `OUT-BAND n/a`, and reports `REDTEAM: FAIL (2 mismatches)`:

* **B1** declares `EGCheck.Erdos184.erdos_184` (trivial) and turns `run_cmd` into a no-op. The
  hardened statement is `type_of% @_root_.Erdos184.erdos_184.{u}`, so the shadow is no longer
  picked up, and `EGCheck.Bridge.solution` (trivial type) is a type mismatch.
* **C** declares its own `Erdos184.erdos_184` in a Bridge that does not import the upstream
  module. The hardened `Final.lean` imports the upstream module first and directly, so the two
  declarations clash at import.

No other attack changes verdict: A, A1, A3, A4, D and N4 keep the honest upstream statement or
hijack `type_of%`/`run_cmd`/`#print axioms` themselves, so they still build green and remain
FinalCheck catches. A2 remains an in-band catch. The t-series and IO attacks are `evasion` mode and
do not build `EGCheck.Final`.

## Why the change is in `staging/`, not `redteam/**`

`redteam/external/redteam.sh` is in the gate's trusted zone, pinned as
`c6705aaa6c6537fb7509f4eaf46b0b56a4e2c0266c080f807a3ed86917ab288b` in `scripts/pristine.sh`.
Editing it now would make the gate reject the tree (`REJECT pin`, in strict mode and in `--dev`) and
fail CI's gate step until the next `--write-pins`. The complete new harness is therefore staged
as **`staging/redteam.sh.proposed`**, to be copied over `redteam/external/redteam.sh` in the same
approval as the other proposals, before `--write-pins`. The gate admits `staging/*.proposed`
files as inert data. The harness is also guarded, as described next, so it can be applied before
or after `Final.lean` without a false failure.

## What changes (the whole diff is `diff -u redteam/external/redteam.sh staging/redteam.sh.proposed`)

1. **Guard: which `Final.lean` is in use.** The new `hardened_final` function checks for the two
   load-bearing features of `staging/Final.lean.proposed`: its first line is
   `import FormalConjectures.ErdosProblems.«184»`, and it contains
   `type_of% @_root_.Erdos184.erdos_184`. If both are present, `FINAL_KIND=hardened`; otherwise
   `committed-style`. The harness prints the kind at the start and in its summary line.
2. **Expectation lines.** The table itself is unchanged. One line is added after it:

   ```
   if [ "$FINAL_KIND" = hardened ]; then EXPECT[B1]=inband+oob; EXPECT[C]=inband+oob; fi
   ```

   | attack | committed-style `Final.lean` (unchanged) | hardened `Final.lean` (new) |
   |---|---|---|
   | B1 | `catch`: in-band green, FinalCheck `[FAIL] statement:` | `inband+oob`: in-band build fails with a type mismatch; FinalCheck on the dev final `[FAIL] statement:` |
   | C  | `catch`: in-band green, FinalCheck `[FAIL] import:.*already contains` | `inband+oob`: in-band build fails with an import clash (`already contains … Erdos184.erdos_184`); FinalCheck on the dev final `[FAIL] import:.*already contains` |
   | all others | unchanged | unchanged |

3. **New verdict `inband+oob`.** It is credited only if all of the following hold:
   * the in-band build of the real `Final.lean` fails;
   * its log shows the attack's own error. A new table `EXPECT_INBAND_RE` holds
     `[B1]='[Tt]ype mismatch'` and `[C]='already contains.*Erdos184\.erdos_184'`, so an unrelated
     build failure is not credited;
   * FinalCheck, run against the **dev final**, fires;
   * FinalCheck's log matches the unchanged `EXPECT_RE` entry for the attack.
4. **Dev final.** This is the theorem of the committed-style `Final.lean` without its in-band
   checks:

   ```lean
   import EGCheck.Bridge
   theorem EGCheck.erdos_184.{u} : type_of% @Erdos184.erdos_184.{u} :=
     EGCheck.Bridge.solution
   ```

   It is written to the run's temporary directory and copied over the **temporary copy's**
   `EGCheck/Final.lean` only after the real one was caught in-band. `reset_copy` restores the real
   one before the next attack. So FinalCheck's out-of-band coverage of B1/C stays exercised, as
   TRUST.md §8 item 8 asks. The OUT-BAND column shows `catch(dev)`.
5. **`--final FILE`** (new option). It uses FILE as the temporary copy's `EGCheck/Final.lean`
   instead of the real one, which lets the new expectations be checked before the proposal is
   applied:
   `redteam/external/redteam.sh --final staging/Final.lean.proposed B1 C`. Without the option, the
   copy is byte-identical to the real file, as before.
6. The FinalCheck invocation moved into a `run_finalcheck` function, with the same arguments. The
   stale comment about a dev final that the old harness never built was replaced by the real
   one.

With the committed-style `Final.lean` the behaviour is unchanged: same expectations, same
commands, and a failed in-band build of a non-`inband+oob` attack is still `n/a`.

`redteam/external/README.md` needs no change: its table lists the *out-of-band* catch per attack
("statement ≠ upstream" for B1, "import clash" for C), and those still fire on the dev final.

## Verification

See `work/trust/docfix.md` §3 for the runs of the staged harness, with both the hardened and the
committed `Final.lean`.

## Integrator steps (in the approval of TRUST.md §8 item 9)

```
cp staging/redteam.sh.proposed redteam/external/redteam.sh   # keep mode 755
chmod 755 redteam/external/redteam.sh
# ... together with TRUST.md, EGCheck/Final.lean, lakefile.toml, .claude/settings.json ...
sh scripts/pristine.sh --write-pins    # the redteam/external/redteam.sh pin changes too
```
