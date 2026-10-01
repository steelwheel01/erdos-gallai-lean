# redteam/external — red-team of the OUT-OF-BAND acceptance checks

Owner: agent id `external`. Reproduces the attacks in the two trust audits
(`../../APPROVALS/reviews/trust.opus.md`, `trust.fable.md`) and checks that the **out-of-band**
acceptance checks catch each one. Nothing here is built by any `lean_lib` (no `EG*`/`EGCheck*` glob
covers it); it never touches the real tree.

## Run

```
export PATH=$HOME/.elan/bin:$PATH
formal/redteam/external/redteam.sh                 # all attacks (FinalCheck; ~10–15 min)
formal/redteam/external/redteam.sh --with-leanchecker D A4   # + leanchecker --fresh (~20 min each)
formal/redteam/external/redteam.sh --keep A1 C t5  # selected attacks; keep the temp copy + logs
```

For each attack the harness:
1. copies the real `formal/` sources into a temp dir under `/tmp` (with `cp`/`tar`; `.lake/packages`
   is a **symlink** to the real read-only package store — `git worktree` and copying `.lake` are not
   used), and applies the attack's overlay from `patches/<id>/`;
2. runs the **in-band** build (`lake build EGCheck.Final`, the auditors' spoofing target) **inside a
   read-only bind mount of the whole repo**, so no write — including a build-time-IO attack — can
   reach the real tree;
3. runs the out-of-band checks this agent owns and compares each verdict, and the specific check that
   fired, against `EXPECT`/`EXPECT_RE` in `redteam.sh`.

## Out-of-band checks

* `scripts/FinalCheck.lean` — `importModules` (`loadExts := false`, so no imported elaborator/macro/
  initializer runs): provenance, import-clash, strict `Expr.equal` of the statement, exact axiom
  set, kernel replay of every project constant, the `EG`/`EGCheck` axiom+attribute policy, a
  meta-type scan, and the `statement`/`closure`/`lean-githash` pins (read from `../../STATEMENT.md`).
* `leanchecker --fresh <final module>` — bundled kernel replay of the whole environment (opt-in).
* comparator is **not** run here; its Challenge/Solution layout is the bridge agent's
  (`../../work/trust/bridge.md`), and `release.yml`'s comparator job is the third check.

## Attacks (`patches/<id>/`)

| id | class | what it does | expected out-of-band catch |
|----|-------|--------------|----------------------------|
| A  | spoof `#print axioms` | real type, `sorryAx` proof, hijacked `#print axioms` | axioms (sorryAx) |
| A1 | hijack `type_of%`+`run_cmd` | `EGCheck.erdos_184 : PUnit → True`, 3 axioms | statement ≠ upstream |
| A2 | namespace shadow | `EGCheck.Erdos184.erdos_184` trivial | **in-band** `run_cmd` (build fails) |
| A3 | hijack `#print axioms` | honest type, `sorryAx` proof | axioms (sorryAx) |
| B1 | neutralise `run_cmd` | trivial shadow + `run_cmd` no-op | statement ≠ upstream |
| C  | fake upstream, no meta | Bridge declares its own `Erdos184.erdos_184` | import clash |
| A4 | kernel bypass (`#eval`) | `«debug».skipKernelTC` + `#eval addDecl` honest type/bogus value | kernel replay |
| D  | kernel bypass (module) | EG-style `module` + `elab` `addDecl` skipping the kernel | kernel replay (+ leanchecker) |
| t1 | lint evasion | `axiom` split across lines | policy (declares an axiom) |
| t2 | lint evasion | `@[simp]axiom` | policy (declares an axiom) |
| t3 | lint evasion | char literal hides an `axiom` | policy (declares an axiom) |
| t4 | lint evasion (benign) | `«debug».skipKernelTC` option only, no bad constant | **none** (correctly missed) |
| t5 | lint evasion | `sorryAx` spelled out | policy (uses sorryAx) |
| t6 | lint evasion | `#eval addDecl` an axiom | policy (declares an axiom) |
| t7 | lint evasion | `implemented_by`/`extern`/`native_decide` | policy (implemented_by/extern/ofReduceBool) |
| t8 | lint evasion | `macro` expanding to `sorryAx` | meta / policy |
| t9 | lint evasion | imported `term_elab`/`command_elab`/`macro`/`initialize` | meta-type scan |
| N4 | IR-name attribution theft (trust2.opus) | `RTX1` plants an IR-only entry `EGCheck.RTX.bogus` (attributed to `RTX1` via `extraConstNames`); `RTX2` adds the kernel constant `EGCheck.RTX.bogus : False := True.intro` without kernel checking; Bridge proves the honest type from it. The old attribution-filtered FinalCheck passed | origin (`extraConstNames`, attribution) + replay (`declaration type mismatch`) |
| IO | build-time IO | `#eval IO.FS.writeFile` at build time | **none** by out-of-band (caught by lint + CI job separation); the read-only bind blocks the real tree |

`t4` and `IO` are expected to be *missed* by the out-of-band statement/axiom checks: a bare option
and build-time IO are not statement or axiom defects. They are the documented coverage of the lint
(tooling agent) and of `release.yml`'s untrusted-build/trusted-verify separation. For sorry-class
attacks (`A`, `A3`) the current pre-γ tree already contains legitimate `sorry`s, so the harness
credits a catch only when the log shows the attack's own defect (see `EXPECT_RE`); the point those
attacks make is that the spoofed in-band `#print axioms` reports the three axioms while the
out-of-band walk still reports `sorryAx`.

The lint column is informational (the current tooling-hardened `scripts/lint.py`, dev mode); several
evasions are `sorry`-only and are flagged by lint only in `--release` mode.
