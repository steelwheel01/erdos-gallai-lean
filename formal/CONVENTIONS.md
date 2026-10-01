# Conventions for statement authors (T0 encoding decisions; PLAN §7)

Collected from the P1 definition reviews (APPROVALS/reviews/*.md, 2026-09-26). Every Spec statement
must respect these; the statement reviewers check them.

## Objects and f
- `EG.fnum F` ignores loops. Apply it only to loopless sets (`H.edges` for `H : FGraph V`,
  `G.edgeFinset`), or add `∀ e ∈ F, ¬ e.IsDiag`. "F decomposes" for a raw `F` = `IsDecomp F D` plus
  that hypothesis (e.g. v6 Fact EG0(b)).
- For a Finset `F : Finset (Sym2 V)`, write `IsDecomp (F : Set (Sym2 V)) D`,
  `IsPathDecomp (F : Set (Sym2 V)) P`, `IsPathCycleDecomp (F : Set (Sym2 V)) P C`, not `↑F`:
  when the second argument's type is not yet known (e.g. under `∃ P C, …`) `↑F` fails with
  "expected `Set (Sym2 ?m)`" (checked, fix round 2 of work/p2d/small.md).
- `EG.Spec.MainInternal` locks only the existence of a constant `c`, not the explicit `c_EG`.
  Stage-α hypotheses (Lovász, Haxell, Euler) go on `EG.Proof.mainInternal`, never into `MainInternal`.
- Multigraphs (s5, s7) are not `Finset (Sym2 V)`; they need their own structure (`MGraph`, PLAN §3).

## Graphs (EG.Defs.Graph, Walk, Expander)
- `minDeg`/`maxDeg` are 0 on the empty graph: "δ(H) ≥ d > 0" needs `H.verts.Nonempty`.
- Use `edgesBetween A B` / `eBetween` only for disjoint `A`, `B` (all manuscript uses are disjoint).
- The one-vertex path `[v]` is a path for every `v`, and `ball i U W` contains `U ∩ W` even outside
  `V(H)`: statements must assume `U, W ⊆ H.verts` where the manuscript does.
- Ball radii are natural numbers: a real radius `r` (e.g. `log⁴ n`) is written `⌊r⌋₊` with `0 ≤ r`.
- `IsExpander ε s` is trivially true for `ε ≤ 0` and for `n ≤ 1`: uses of "δ(G) > s" need `0 < ε`
  and `2 ≤ |G|` (manuscript remark after s1:citDef11 is being corrected to say ε > 0 in v6).
- "O is a spanning (ε,s)-expander on Z": `O.verts = Z ∧ O.IsExpander ε s`.
- `IsPathConnected ℓ t` depends on `t` only through `⌊t⌋₊` and is trivial for `t < 1`; write integer
  multiplicities as `(k : ℝ)`. For index types outside `Type`, use `IsPathConnected.exists_paths`.
- Definitions accept arguments outside the manuscript's domain; keep the manuscript's inclusion
  hypotheses (e.g. `F ⊆ H.edges`, `U ⊆ H.verts`) in statements.
- `edgeComps` / `compEdges` / `IsNonBridge` / `IsPendant` (EG.Defs.Components) and `IsPathDecomp` /
  `IsPathCycleDecomp` (EG.Defs.PathDecomp) are for loopless edge sets only, as for `fnum`: a loop
  counts as a non-bridge, forms a one-edge (odd) component and counts in `degE`, and an `F`
  containing a loop has no path decomposition. Use `H.edges`, subsets of `G.edgeFinset`, or add
  `∀ e ∈ F, ¬ e.IsDiag`. "Non-bridge / pendant of that component" = the global predicate on `E`
  (`isNonBridge_compEdges_iff`, `isPendant_compEdges_iff`).
- Well-expanding sets are `FGraph.IsWellExpanding` (EG.Defs.Graph, neighbourhood in `G`, not
  `G − F`); `EG/Defs/Link/Star.lean` uses it and does not redefine it.

## Constants and Γ (EG.Defs.Constants, EG.Defs.Gamma.Core)
- Names: `EG.epsC : ℝ` (ε = 2^-5), `EG.sigmaC : ℕ` (σ = 100), `EG.Cp : ℕ` (C' = 103), `EG.Aexp : ℕ`
  (A = 105). Not `ε`/`σ`, and not the blueprint names `CpC`/`AexpC`.
- Γ1 items (a)–(e): `Gamma1a` … `Gamma1e`, `Gamma1Items μ`, `Gamma1core D`; Γ2(a): `Gamma2a D`
  (derived from `Gamma1core` by `Gamma1core.gamma2a`). `Gamma1core` is satisfiable
  (`EG.exists_gamma1core`, `EG.eventually_gamma1core`).

## Parameters of s3/s4 (EG.Defs.Link.Star, EG.Defs.Vortex, EG.Defs.Lend.COLTable)
- Short names recur across these namespaces (`Star.L`/`Vortex.L`, `Star.lam`/`COLTable.lam`,
  `Star.M` next to the run's `run.M`). Never `open` more than one of `EG.Star`, `EG.Vortex` and
  `EG.COLTable` in a Spec; write the qualified names.
- The vortex size predicates, η's and parameters take `N : ℕ` (N = |Z| is a vertex count): write
  `Vortex.TPVSize O.card`, not `TPVSize (O.card : ℝ)`. `N0Cond` quantifies over `N : ℕ` with
  `N0 ≤ (N : ℝ)` (TRIAGE §2.4).
- `COLTable.row i μ` is numbered 1…13 and is `True` (junk) for `i = 0` and `i ≥ 14`: always bound
  the row index by `1 ≤ i ∧ i ≤ 13`, or use `COLTable.col3`. A statement "∀ i, row i μ" or
  "∃ i, ¬ row i μ" without those bounds silently includes the junk rows.
- `Gamma1c` (Core) writes `1.6 * μ` while `COLTable.row 12` writes `8/5`; they are bridged by
  `COLTable.row12_iff_gamma1c` (μ > 0). Do not restate either with the other literal.
- Star parameters are junk outside `n ≥ 2`, `ρ ∈ (0,1]`, `ε' ∈ [2^{-7},1]`, `t ≥ 1`: s3 Specs carry
  these hypotheses. `Fin (Star.K n ε' ρ t)` colourings get `K_* ≠ 0` from `Star.K_ne_zero`.

## The s2 hierarchy (EG.Defs.HB; design note work/p2d/hb.md)
- Runs: Specs read `∀ Dstar (Γ-items), ∀ G run, run.Valid G Dstar → …`; `Run.Valid` contains no Γ.
  Rounds are 1-indexed ℕ, bounded by `run.IsRound l` (`1 ≤ l ≤ run.R`); offsets as `r + 2 ≤ l`.
- Argument shapes: ancestor data takes `Y : PartId` (`run.LY G (r, a)`, `run.ancVerts G Y`,
  `run.ancGraph G Y`, `run.ancEps G Y`, `run.ancS G Y`); choice-only objects take no `G`
  (`run.R`, `run.cycles l`, `run.cycEdges l`, `run.tree0 l`, `run.tauRun l q`, `run.pieceAddrs l`,
  `run.pieceOf l a`); everything else takes `G` first. Blueprint renames: `run.Mr` → `run.M`,
  `run.H Y` → `run.ancGraph G Y`, `run.allAncestors`/`ancestorSet` → `run.ancestors G`,
  `run.isStd Y` → `Y ∈ run.stdParts G`, `EG.HB.psi` → `EG.HB.psiPool`.
- `E(Cyc_l)` is `run.cycEdges l` (guarded), not `Round.cycEdges (run.choice l)` (unguarded).
- Read `run.tauRun l q` only at `q ∈ run.bigPieceAddrs G l`; per-address wrappers (`Z0`, `X0`,
  `guests`, `isLight`, `home`, …) only at addresses in `run.prePartAddrs G l`.

## Probability (EG.Defs.Prob.FinDist)
- FinDist is finitely supported: an untruncated geometric level law (P(lev ≥ j) = 2^{-j} for all j)
  cannot be expressed (proved: `no_geometric`). Vortex Specs (s4:lemTPV, s4:lemPV, s4:thmVXp) use
  the truncated law `min(lev, J)` with P(lev' = J) = 2^{-J}; checked lossless for U_j (j ≤ J) and
  W_j, Z_j, V_{j,c} (j < J). This matches manuscript v6 change R5.
- `IsRSubset` allows ρ = 0 (T16*'s Spec adds `0 < ρ`) and fixes only the law; "independent of other
  randomness" is a separate `IndepFun` clause.
- Colours are `Fin k` (0-based); named colour families (TPV's 3J+1 colours) need an explicit
  bijection or colour type.
- Non-uniform label laws (κ, JS labels, truncated levels) are built in Specs via `ofFintype` /
  `ofFinset`; reviewers must check their weights.

## Orientations (EG.Defs.Orient)
- `IsBalanced` quantifies over all vertices; the cluster "admissible orientation" (s6:defCluster)
  needs balance only at hubs, so those Specs must use `outDeg`/`inDeg` pointwise, not `IsBalanced`.
- `IsDirCycle` admits loops and 2-cycles for general arc sets; for subsets of an orientation every
  directed cycle has length ≥ 3 (proved).

## T0 record (encoding decisions with a manuscript-wording consequence; PLAN §7 class T0)
| ID | Where | Decision | Manuscript action (v6) |
|---|---|---|---|
| T0-def11-eps | s1:citDef11 remark | "δ(G) > s" proved with `0 < ε` | add "ε > 0" to the remark |
| T0-eg0-loop | v6 Fact EG0(b) | stated for loopless edge sets | say "edge set of a (simple) graph" |
| T0-cap-1 | s1:citLem25 | `BMLemma25Statement` adds `2 ≤ m`; the literal statement is false at m = 1 for large ε (Lean: `EG.bmLemma25_literal_false`); only use has m ≥ 2^40 | "Let ε ≥ 2^{-5} and m ≥ max(2, 2^{30}/ε²)" |
| T0-glob-input | s6:lemHCCglob ¶2 (`EG.Spec.HccGlobStatement`) | hypothesis at the input level: beads and all path edges of distinct systems pairwise disjoint (the literal hypothesis, "their beads together with their sets `F_j`", names HCC-P outputs; `F_j ⊆ E(𝒫_j)`, so this is stronger). It is what JS-LC Step 7 checks: "Their bead sets are pairwise disjoint ... Their path edges are pairwise disjoint ... Path edges are disjoint from beads". The conclusion adds "cycles of `G`", which Step 7 ("decomposes into at most `∑_𝒮 Φ(𝒮)` cycles") and J⁺ read (P2E review 1, R1) | optional: "their beads and their path edges are pairwise disjoint" |
| T0-stage3-det | s5:lemChild, s5:lemDemoted, s5:lemKRED (`EG.Spec.LemChildStatement`, `LemDemotedStatement`, `LemKREDStatement`); TRIAGE §2.8, §2.12 | Stage 3 is deterministic: the good events `𝒢_Z` (lemChild, `P ≥ 1/3`) and `𝒢^VX_Y` (lemDemoted, `P ≥ 1/2`) and "determined by the stage-1 outcome and these labels" are not stated; the conclusions are `∀ ω ∈ supp, ∀ admissible H_0 (resp. E), ∃ decomposition`. This is logically weaker than the TeX's "∃ stage-3 outcome ∀ H_0" (uniformity in `H_0` is lost). It suffices for all current consumers: MIX-C applies the per-`H_0` form at the final `H_0` of each part (s6b T0-mixc-stage3), and s7:lemOneOutcome's stage-3 part has no Lean content (OO-PROCEDURAL, `EG/Spec/Quot/OneOutcome.lean`). A consumer needing the uniform or causal form must add its own Spec | none |
| T0-kred-causality | s5:lemParent, s5:lemKRED (`LemParentStatement`, `LemKREDStatement`); TRIAGE §2.12 | The "depends only on" clauses are dropped: K-RED is pure existence for every family with `EG.Light.LentExtHyp`, lemParent for every arc system with `ArcHyp` (PAR-ARCS-INPUT); the round procedure is proof-internal. K-RED's itemization with `c^exact = 1 + 2·369 = 739` is not a Spec (it implies the stated `745` bound). `LemParentSumStatement` sums the per-round bound `14(J̄_l+1)n/(102 log₂λ_{l−2})²` in place of the existential `cap_l` | none |
