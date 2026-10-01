# redteam/bridge — comparator fixtures for the Challenge/Solution layout

Attack fixtures, **never built by any `lean_lib`** and never placed in `EG/`, `EGTest/` or
`EGCheck/`. `run.sh` copies `formal/` to a scratch directory (`$RT_DIR`, default a fresh
`mktemp -d`), uses the fixture as `comparator/Solution.lean` there, and runs
comparator through `scripts/comparator.sh run --allow-sorry --prebuilt --scratch …`. `sorryAx` is
permitted in these runs (the proof is incomplete), so every rejection below comes from another
check.

| Case | Solution | Expected verdict (comparator message) |
|---|---|---|
| `C0_UnconfinedLandrun` | honest; landrun replaced by a pass-through wrapper (the `--best-effort` no-Landlock case, trust3.opus B2) | harness refuses before comparator starts: `Landlock canary: …` (exit 2) |
| `honest` | `comparator/Solution.lean` | accepted: `Your solution is okay!` |
| `F1_DefinitionChanged` | `Erdos184.IsCycleOrEdge := True`, proof `sorry` | `Const does not match between challenge and target 'Erdos184.IsCycleOrEdge'` |
| `F2_StatementWeakened` | `O(n^2)` instead of `O(n)`, proof `sorry` | `Challenge and solution theorem statement do not match: 'Erdos184.erdos_184'` |
| `F3_KernelBypass` | honest statement; "proof" from `Erdos184.bogus : False := True.intro` added by `addDecl` under `debug.skipKernelTC` from an `elab` command (audit attack D) | `Lean default kernel rejects the solution` |
| `F4_ExtraAxiom` | honest statement proved from `axiom cheat : False` | `Illegal axiom detected: 'Erdos184.cheat'` |
| `F5_ImportsUpstream` | imports `FormalConjectures.ErdosProblems.«184»` and restates it | Solution build fails (declaration clash): `Child exited with 1` |

Usage (from `formal/`, after `scripts/comparator.sh tools DIR`):

```
redteam/bridge/run.sh --tools DIR [--keep]
```

Measured results: `work/trust/bridge.md`.
