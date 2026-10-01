# Guide for agents working in formal/ (read fully before writing Lean)

Project: Lean 4 formalization of a CANDIDATE proof (AI-reviewed only) of the Erdős–Gallai cycle
decomposition conjecture. Plan: `../PLAN_FORMALIZATION.md`. Manuscript: `../proofs/manuscript/`.
Never call the conjecture solved.

## Non-negotiable rules
1. **Never weaken a statement** to make a proof go through; never change a `Spec` statement or a
   `Defs` definition yourself. If a statement looks false, stop and report it with a concrete
   counterexample or reason (policy: PLAN §7, classes T0–T3). A proof that won't go through is
   not a refutation.
2. Forbidden anywhere in `EG/`, `EGTest/`, `EGCheck/`: `axiom`, `admit`, `native_decide`,
   `decide +native`, `bv_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`,
   `ofReduceBool`, `trustCompiler`, `debug.*` options, `maxHeartbeats 0`, `run_cmd`/`run_elab`/
   `run_meta`, `modifyEnv`/`setEnv`. `sorry` is allowed only where your task says so.
   `python3 scripts/lint.py` checks this.
3. Trust-boundary files are edit-denied for every agent: `TRUST.md`, `lean-toolchain`,
   `lakefile.toml`, `lake-manifest.json`, `EGCheck/Final.lean`, `.claude/**`. Never try to
   change them by other means. Statements and definitions (`EG/Spec/**`, `EG/Defs/**`),
   `scripts/**`, `LOCK.json` and `status/ratchet.json` are integrator-owned: edit them only if
   your task explicitly says so. From the P2→P3 statement freeze on they are edit-denied too
   (decision recorded in STATE.md, 2026-09-25), and `scripts/lock.py check` in CI detects any
   change to a locked statement or to a definition it depends on.
4. Do not run git commands that change the repository (add/commit/push/checkout/stash/reset);
   the orchestrator commits. Do not modify files outside your task's scope.
5. Only `EGCheck` may import `FormalConjectures`. `EG` and `EGTest` import Mathlib only.

## Toolchain
- Lean `v4.33.1`, Mathlib `v4.33.1` (commit 0df444a3), already built in `.lake/`. Never run
  `lake update`, never edit `lakefile.toml` / `lake-manifest.json` / `lean-toolchain`.
- PATH: `export PATH=$HOME/.elan/bin:$PATH`.
- Check one file (dependencies must be built): `scripts/check.sh EG/Proof/Foo.lean [timeout]`.
  Build a module and its dependencies: `lake build EG.Proof.Foo`.
- The machine has 4 cores and 15 GB RAM shared by several agents: build only what you need,
  use `LEAN_NUM_THREADS=2` for single-file checks, and never start more than one `lake build`
  at a time yourself.
- Axioms of your declarations: `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Foo`.

## Searching Mathlib
- Source is in `.lake/packages/mathlib/Mathlib/`; use `grep -rn "theorem .*card_le" .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/`.
- Inside a proof, `exact?`, `apply?`, `rw?`, `simp?`, `aesop`, `omega`, `linarith`, `nlinarith`,
  `positivity`, `norm_num`, `decide` (small finite only), `grind` are available.
- Useful: `SimpleGraph`, `Subgraph`, `Walk` (`IsPath`, `IsTrail`, `IsCycle`, `toSubgraph`),
  `SimpleGraph.Connected`, `degree`, `sum_degrees_eq_twice_card_edges`, Hall's theorem
  `Finset.all_card_le_biUnion_card_iff_exists_injective`, `Real.logb`, `Real.log`,
  `Finset.sum_*`, `Finset.prod_*`, `Finset.card_*`.

## Module system (decided in P0; see STATE.md)
All files under `EG/` are Lean `module`s, so that a proof-only edit does not rebuild importers
(measured in P0: with modules only the edited file rebuilds; without, every importer does).
- Header: `module`, then `public import ...` lines, then the module docstring, then
  `@[expose] public section` in `EG/Defs/**` and `EG/Spec/**` (definition bodies must be visible
  downstream), `public section` in `EG/Lib/**` and `EG/Proof/**`.
- A definition in `Lib`/`Proof` that later files must unfold needs `@[expose]`; otherwise
  downstream `unfold`/`simp [foo]` fails. Theorems need nothing special.
- `EGTest/**` and `EGCheck/**` are ordinary (non-module) files; they may import modules.

## Conventions
- Namespace `EG`; files mirror the manuscript layers (PLAN §3 table). Tag every declaration that
  formalizes a manuscript statement with a docstring starting `[s3:lemL15p]` (manuscript label).
- Internal objects: `EG.Obj` (edge | cycle list), decomposition `EG.IsDecomp`, see
  `EG/Defs/Objects.lean`. Randomness: `EG.FinDist` (finite sample spaces, real weights);
  conclusions are deterministic existence statements.
- `EG.fnum F` ignores loops (`fnum F = f(F \ diagSet)`). In statements apply `fnum` only to
  loopless sets: `H.edges` for `H : FGraph V` (lemmas in `EG.Lib.Found.FGraphFnum`),
  `G.edgeFinset`, or add the hypothesis `∀ e ∈ F, ¬ e.IsDiag`. State "F decomposes" for a raw F
  (e.g. Fact EG0(b)) with `IsDecomp` plus that hypothesis.
- Graph layer: `EG.FGraph` (explicit `verts`/`edges` finsets), list paths in `EG.Defs.Walk`,
  `FGraph.IsExpander` (Def 11, log₂), `FGraph.IsPathConnected` (Def 7, real `ℓ t`, indexed
  families of pairs). Probability: `EG.FinDist` (`EG.Defs.Prob.FinDist`, API in `EG.Lib.Prob.*`).
  Read the design notes in `work/p1b/*.md` before writing new foundations.
- Galactic constants: never compute them; use eventualities (`∀ᶠ x in atTop, …`).
  Small absolute constants: `norm_num` / `nlinarith`.
- Prefer many small lemmas with clear statements over one huge proof. Keep files < 1500 lines.
- `set_option maxHeartbeats N in` (N ≤ 1000000) is allowed locally with a comment saying why.

## Reporting
Write results to the files your task names and return only a short status. Report honestly:
what is proved, what is `sorry`, what failed and why.
