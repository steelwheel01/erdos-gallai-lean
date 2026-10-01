# Trust hardening — out-of-band checks (agent id: `external`, 2026-09-26)

Response to the two trust audits (`APPROVALS/reviews/trust.opus.md`, `trust.fable.md`), which
REJECTED the trust setup because the in-band checks in `EGCheck/Final.lean` (`type_of%`,
`#guard_msgs` on `#print axioms`, the `run_cmd` comparison) are spoofable by any imported untrusted
module. This agent builds the **out-of-band** acceptance checks and a red-team that proves they catch
every auditor attack.

## Scope and rules honoured

* Owned/created: `scripts/FinalCheck.lean`, `scripts/Statement.lean`, `STATEMENT.md` (generated),
  `redteam/external/**`, `redteam/external/redteam.sh`.
* No protected file was modified by any means: `TRUST.md`, `EGCheck/Final.lean`, `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain`, `.claude/**`. Proposed `TRUST.md` changes are written to
  `staging/TRUST.md.external.md` for the user to approve. No Lean statement was weakened.
* No git command that modifies the repo. Attack fixtures live only under `redteam/external/` (no
  `lean_lib` builds them) and in temporary copies under `/tmp`; the real tree is never written (the
  red-team builds inside a read-only bind mount of the repo).
* Coordination: read `work/trust/tooling.md` (the tooling agent owns lint/`Axioms.lean`/
  `check_pins.sh`/CI/`leanchecker`). The bridge agent is refactoring `EGCheck` (added
  `BridgeCore.lean`, uses `_root_.Erdos184.erdos_184`, references `comparator/Solution.lean`); no
  `work/trust/bridge.md` and no `comparator/` exist yet, so `FinalCheck.lean` targets the primary
  layout `#[FormalConjectures.ErdosProblems.«184», EGCheck.Final]` and has a `--solution-module` hook
  ready (untested) for when the Solution layout lands.

## 1. `scripts/FinalCheck.lean` — the out-of-band statement/axiom check

Run: `lake env lean --run scripts/FinalCheck.lean`. It uses `importModules` with
`loadExts := false`, so **no project (or package) elaborator, macro, delaborator, environment-import
hook or `initialize` runs** — this is what makes it out-of-band. Every constant is looked up by a
literal `Name`. Verified against Lean core source: `loadExts := false` means `finalizePersistent
Extensions` is never called, so no imported code executes; the constant map and raw `.olean` entries
are still readable.

Checks (each `[PASS]`/`[WARN]`/`[FAIL]`; exit 1 on any `[FAIL]`):

* **lean** — running Lean commit == pin (`819816b2…`).
* **import** — `importModules #[…«184», EGCheck.Final, EG, EGCheck]` succeeds; a second declaration of
  any upstream name is an import clash (defeats a fake upstream, attack C).
* **oleans** — every imported module's `.olean` comes from its package (project modules under
  `.lake/build`, others under the toolchain or `.lake/packages/<pkg>`), with a git-tracked source;
  each package used is at its `lake-manifest.json` rev with a clean worktree.
* **origin** — `Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge` from `…«184»`,
  `SimpleGraph.IsDecomposition` from `…Decomposition`, `EGCheck.erdos_184` from `EGCheck.Final`; no
  project module re-declares a package constant (a re-declared theorem would be silently merged by
  `importModules`, so it is checked here explicitly).
* **kinds** — both theorems are `.thmInfo`, both upstream definitions `.defnInfo`.
* **statement** — strict `Expr.equal` (binder names + annotations) of the two types after renaming
  universe parameters by position (defeats A1/B1).
* **replay** — kernel re-checks every project constant, **renamed** onto the imported package
  environment (`_egFinalCheckReplay.<n>`), so the unchecked imported originals can neither clash nor
  be used. Catches `debug.skipKernelTC`/`addDecl` bypasses (A4, D) that leave a valid-looking
  `.olean`. Uses one `importModules` (a second import of the 6 GB Mathlib `.olean`s would not
  memory-map again and would double RSS).
* **axioms** — `collectAxioms EGCheck.erdos_184` (own traversal of the stored bodies, in the replayed
  environment) is exactly `{propext, Classical.choice, Quot.sound}`; `sorryAx` reported separately, a
  failure unless `--allow-sorry`; cross-checked against Lean's `collectAxioms`.
* **policy** — the `EG`/`EGCheck` policy of `scripts/Axioms.lean` with `--no-sorry`, over every
  project constant, computed by one memoised iterative axiom-mask traversal (inductive blocks merged
  with their constructors so the graph is acyclic): no axiom outside the three, no
  `axiom`/`unsafe`/`@[extern]`/`@[implemented_by]`/`@[init]`.
* **meta** — no project constant's type mentions a meta-level type (`Lean.Elab`/`Meta`/`Macro`/
  `Parser`/`Syntax`/`IO`/`Environment`/…); the project is pure mathematics, so such a constant is an
  elaborator/macro/initializer hook (catches t9 and the meta half of A/A1/A3/B1/D).
* **pin** — `sha256sum` of a canonical serialisation of the statement `Erdos184.erdos_184` and of its
  full closure equals `statement-sha256` / `closure-sha256` (in `TRUST.md` or via `--expect-*`). Pins
  the *meaning* of the target against tampered/stale `.olean`s and dirty worktrees.

Options: `--allow-sorry`, `--allow-unpinned`, `--pin-file`, `--expect-statement-sha256`,
`--expect-closure-sha256`, `--expect-lean-githash`, `--final-module`, `--policy-roots`, `--no-replay`,
`--scan-only` (policy+meta+replay over arbitrary modules, used by the red-team for the evasion
fixtures), `--solution-module`/`--restated-thm` (comparator Solution layout, untested pending the
bridge agent), `--dump-canon`.

Measured on a copy with a dev final (`EGCheck.erdos_184 := Bridge.solution`, `mainInternal` still
`sorry`): PASS with `--allow-sorry`, wall ~20–30 s warm / ~5 min cold, max RSS ~12 GB (dominated by
the mmapped Mathlib `.olean`s; a ≥ 16 GB runner is advisable, same as `leanchecker --fresh`). Without
`--allow-sorry` it correctly FAILS on the ambient `sorry`s (`EG.Proof.mainInternal`, `EG.bmLemma25`,
`EG.cap_graph`, `EGCheck.smoke`).

### What it establishes / does not

Establishes (given the pinned toolchain + package `.olean`s): the statement of `EGCheck.erdos_184` is
exactly the pinned upstream statement, it depends only on the three axioms, and every project
constant is kernel-valid and free of the forbidden constructs. Does **not** establish that the
package `.olean`s were compiled from the pinned sources (→ `leanchecker --fresh`, from-source
Challenge build, `check_pins` clean-worktree), and it loads untrusted `.olean`s into its own process
(a loader-exploit `.olean` is out of scope → comparator's sandboxed build). So it is one of three
required out-of-band checks; see `staging/TRUST.md.external.md`.

## 2. `scripts/Statement.lean` → `STATEMENT.md` (the semantic pin the reader reads)

Run: `lake env lean --run scripts/Statement.lean [STATEMENT.md]`. Imports only
`FormalConjectures.ErdosProblems.«184»`. Emits, for `Erdos184.erdos_184`, `Erdos184.IsCycleOrEdge`
and `SimpleGraph.IsDecomposition`: the `pp.all` form, the constants used grouped by module, the full
statement closure grouped by package/module (1572 declarations), and the pins

```
EG-PIN lean-githash 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
EG-PIN statement-sha256 4cb2cd5697e7916ea244e8b58041fcb2c7fa4338621335eeeb3a1d05452f6734
EG-PIN closure-sha256 39d6e8c358b1482f9af513370d6edfba52da96857fa1066a309fa87c0ccf66fd
```

The canonical serialisation (the `BEGIN CANON..END CANON` block) is byte-identical in
`Statement.lean` and `FinalCheck.lean`; `redteam.sh` `diff`s the two blocks and aborts if they
differ. Cross-check with the trust audits: SHA-256 of `Expr.dbgToString` of the statement type is
`33e213279405c3580cb185430dcb66f5ec7caa6e7bd150731e000ad6a928012d` (= trust.opus §5.2). The three FC
constants and the closure composition match both audits.

## 3. Red-team (`redteam/external/`) — result: all attacks caught out-of-band

`redteam/external/redteam.sh` reproduces every auditor attack as a self-contained overlay on a
temporary copy of `formal/` (sources copied; `.lake/packages` symlinked read-only; build inside a
read-only bind mount of the repo). Full run, `REDTEAM: PASS`:

```
ATTACK MODE      IN-BAND   LINT   OUT-BAND  RESULT
A     finalattack green     catch  catch     OK    (axioms: sorryAx — the spoofed in-band #print axioms is defeated)
A1    finalattack green     catch  catch     OK    (statement ≠ upstream)
A2    finalattack caught    catch  n/a       OK    (caught in-band by run_cmd; build fails)
A3    finalattack green     catch  catch     OK    (axioms: sorryAx)
B1    finalattack green     catch  catch     OK    (statement ≠ upstream)
C     finalattack green     catch  catch     OK    (import clash on Erdos184.erdos_184)
A4    finalattack green     catch  catch     OK    (kernel replay: declaration type mismatch)
D     finalattack green     catch  catch     OK    (kernel replay; also leanchecker --fresh)
t1    evasion     built     catch  catch     OK    (policy: declares an axiom)
t2    evasion     built     catch  catch     OK    (policy: declares an axiom)
t3    evasion     built     catch  catch     OK    (policy: declares an axiom; char-literal hidden)
t4    evasion     built     catch  miss      OK    (benign option only — correctly not a statement/axiom defect)
t5    evasion     built     miss   catch     OK    (policy: uses sorryAx; lint dev-mode misses, release catches)
t6    evasion     built     catch  catch     OK    (policy: declares an axiom via #eval addDecl)
t7    evasion     built     catch  catch     OK    (policy: implemented_by/extern/ofReduceBool)
t8    evasion     built     catch  catch     OK    (meta / policy: macro→sorryAx)
t9    evasion     built     catch  catch     OK    (meta-type scan)
IO    evasion     wrote/tmp catch  miss      OK    (build-time IO; read-only bind blocked the real tree; caught by lint + CI job separation)
```

The harness credits a "catch" only when the attack's *own* defect is what the log reports
(`EXPECT_RE` in `redteam.sh`), so a catch is not an artefact of the ambient pre-γ `sorry`s.

Key confirmations from the logs:
* C: `import EGCheck.Bridge failed, environment already contains 'Erdos184.erdos_184' from
  FormalConjectures.ErdosProblems.«184»`.
* A1: `statement: type of EGCheck.erdos_184 differs from Erdos184.erdos_184 … different`.
* A4/D: `replay: kernel rejected a project constant: while replaying declaration '…': (kernel)
  declaration type mismatch` (A4 on `Bridge.solution`, D on `BridgeHack.helper`).
* A/A3: the spoofed in-band build is green with `[propext, Classical.choice, Quot.sound]`, yet
  out-of-band `axioms` reports `sorryAx`.

`leanchecker --fresh EGCheck.Final` was run on the two kernel-bypass attacks (D, A4) as the
independent second check and **caught both** (elapsed ~24 min, ~8 GB RSS each on this loaded
machine): D → `while replaying declaration 'EGCheck.BridgeHack.helper': (kernel) declaration type
mismatch, has type True but it is expected to have type False`; A4 → `while replaying declaration
'EGCheck.Bridge.solution': (kernel) declaration type mismatch, has type True but it is expected to
have type [the upstream ∃ f, …]`. (Not run on the other attacks: leanchecker checks
only kernel validity, so it does not catch statement/axiom/sorry attacks — those are FinalCheck's and
comparator's job; running it per-attack costs ~20 min / ~10 GB each.)

## 4. Coordination and residual gaps

1. **Comparator Solution layout.** The bridge agent split the bridge into FC-184-free
   `BridgeCore`/`BridgeLemmas` and references `comparator/Solution.lean` (not yet created).
   `FinalCheck.lean` has a `--solution-module` mode that pins the *restated* statement by canonical
   hash (equals the upstream pins) and checks axioms/replay/policy/meta; finalise and test it once
   `work/trust/bridge.md` and `comparator/Solution.lean` exist.
2. **`EGCheck.Final` build fails until stage γ** (its `#guard_msgs` demands no `sorry`). The red-team
   uses the real `Final.lean` for the in-band column and a dev final only where a built `.olean` is
   needed; the release runs `FinalCheck.lean` on the real `EGCheck.Final` once it is sorry-free.
3. **Not covered by any in-VM check** (documented, and the reason comparator + job separation are
   required): build-time IO with no residual constant (attack IO), and a loader-exploit `.olean`.
4. **Lock / freeze.** Add `scripts/FinalCheck.lean`, `scripts/Statement.lean`, `STATEMENT.md` and
   `redteam/external/**` to `LOCK.json` `PROTECTED_FILES` (tooling agent's `lock.py` expands
   `scripts/**`; confirm the rest), and re-lock after approval. CI should regenerate `STATEMENT.md`
   and fail on any diff.
5. **TRUST.md** is not mine to edit; `staging/TRUST.md.external.md` holds the pin block and the
   out-of-band acceptance criterion naming `FinalCheck.lean`/`Statement.lean`. Merge with the tooling
   and bridge agents' TRUST.md proposals; the user approves.
