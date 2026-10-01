# Clean-room review of the P4B Specs — lens: vacuity and consumer form (model B)

Reviewed: the Spec files listed in `work/p2b/P4B.md` (new ones in full: `EG/Spec/Light/ParentSteps.lean`,
`EG/Spec/Light/ParentRun.lean`, `EG/Spec/Stage1/COLc.lean`, `EG/Spec/Stage1/COLa.lean`,
`EG/Spec/Found/EulerMulti.lean`, `EG/Spec/Link/T16s.lean`, `EG/Spec/HB/TowerBM.lean`,
`EG/Spec/HB/StructureLight.lean`, the reconstructed `EG/Spec/Light/Setting.lean`), the new Defs file
`EG/Defs/Probe/P4B/Trail.lean`, the nine stubs under `EG/Proof/**`, `EGTest/ProbeP4B.lean`, and the TeX
(v6.1): `s5.tex` lemParent Steps 0–9 and Claims, defStages, lemE1 (c), the setting paragraph (eqLY, eqZp);
`s3.tex` thmT16s, defCOL (ii)/(derived quantities), lemCOL statement and proof of (a), (c), Table COL-JV rows
4, 7, 9, 12; `s1.tex` citEuler (b) and the log convention (`s1:convGraphs`: all logarithms base 2);
`s2.tex` lemTower (a), (b) with its proof, propStructure (iv). No Lean file was edited. A scratch file was
compiled in the session scratchpad (`P4Bvac.lean`, rc = 0) for the vacuity probes recorded below.

Verdict: **approve**. Every new statement back-translates to the quoted TeX with the right quantifier order,
strictness, constants, base-2 logarithms and integer/real typing; no contradictory hypothesis set and no
trivially true conclusion was found; no Γ2(b),(c) hypothesis appears anywhere; `python3 -I scripts/lint.py`:
0 findings. One duplication with a Spec of another unit (minor, integrator's call) and a few cosmetic points.

## 1. Fidelity (back-translation next to the TeX)

Common: `L_Y = run.LY G Y = log₂|V(Y)|`, `λ_r = run.lam G r = log₂ d_r`, `M_l = run.M G l ∈ ℕ`,
`t_Y = Stage1.tY = ⌈λ_r^{1.6}⌉₊`, `N^{-k}` are `zpow`, `x^{1.6}` is `rpow`, `(A log λ)^{2A}` a natural power.

| Spec | Lean, in plain mathematics | TeX (quoted) | Verdict |
|---|---|---|---|
| `EulerMultiStatement` | finite nonempty edge index set `E` with endpoint map; any two edge-ends reachable in the loop-free adjacency graph; every vertex has even degree (loop = 2) ⇒ ∃ nonempty cyclic list of oriented edges, no edge twice, consecutive ends matching, edge set exactly `E` | "A connected graph (or multigraph) in which every vertex has even degree has a closed trail using every edge exactly once." | faithful; T0 `E ≠ ∅` (H3), isolated vertices dropped (equivalent) |
| `T16sStatement` | `X` fixed, `2^{-7} ≤ ε' ≤ 1`, `X` `(ε',s)`-expander, `0<ρ≤1`, `t ≥ 1` real, `W` with law `rsubset V(X) ρ`, `L² ≤ ρN`, `2^{135} t L^{28} ρ^{-5} ≤ s` ⇒ `P(X (2^{12}L^4,t)-path connected through W) ≥ 1 − 2^{86} t L^{19} ρ^{-3} N^{-3}` | statement of s3:thmT16s verbatim; items (a)–(c) are remarks | faithful (`N = X.card`, `L = log₂ N`); degenerate `N ∈ {0,1}` give `L = 0`, hypotheses trivial and conclusion trivially true (no pairs) — harmless |
| `COLaProbStatement` | Γ1, valid run, `D_* ≤ d_1`, any ancestor `Y`, any `D` with law `colLaw Y`: `P(¬COL(a)) ≤ N^{-2}/4` | proof of lemCOL (a): "the total failure probability of (a) is at most `2(2+k+k_own)N^{-5} ≤ … ≤ N^{-2}/4`" | faithful; the bound is proved for every round (`k = 0` for `r ≥ R−1`, `k_own` unread for standalone `Y`) |
| `COLcIndexStatement` | as above, `Y` light, `i ∈ I^U(Y)`, `W` `ρ`-random subset of `V(Y)` with `1/(12L^5) ≤ ρ`, `W ⟂ D`: `P(COL(a)(D) ∧ ¬ LU_i (2^{12}L^4, t_Y)-p.c. through W) ≤ 2^{86} t_Y L^{19} (12L^5)^3 N^{-3}` | "Condition on a stage-(i)/(ii) outcome in which (a) holds … apply Theorem s3:thmT16s … with `t := t_Y` … `ρ := ρ_{l,c,σ} ≥ 1/(12L^5)` … Each index fails with probability at most `2^{86}tL^{19}(12L^5)^3N^{-3}`" | faithful (integrated form of the conditional bound; `ρ^{-3} ≤ (12L^5)^3` as in the TeX); T16* hypotheses re-derived from COL(a) (`s = ancS/(8k) = s_r/(16k)`, `ε_Y = 2^{-6}`), row 4, `N/(12L^5) ≥ L²` |
| `COLcStatement` | `Y` light, `D` with law `colLaw Y`, family `Vs`, each `Vs·i` (`i ∈ I^U`) `ρ_i`-random in `V(Y)` with `ρ_i ≥ 1/(12L^5)`, `Vs ⟂ D` jointly: `P(¬COL(c)(D, Vs)) ≤ N^{-2}/2` | lemCOL (c) verbatim (quoted in the docstring) | faithful; "may be dependent across indices" = no independence across `i` assumed; `r ≥ R−1` vacuous as in the TeX |
| `TowerBMStatement` | Γ1(a)–(e), valid run, `D_* ≤ d_1`: `∀ 3 ≤ l ≤ R`, `M_l ≤ (A log₂ λ_{l−2})^{2A} ≤ λ_{l−2}^{1.6}`; `Σ_{l=1}^R 1/M_l ≤ 2/D_*` | "For `3 ≤ l ≤ R`: `M_l ≤ (A log λ_{l−2})^{2A} ≤ λ_{l−2}^{1.6}` … Moreover `Σ_{l≤R} 1/M_l ≤ 2/D_*`" | faithful; s2 proof uses propDegRec, Γ1(c) at `log λ_{l−2}`, lemLacunary + Γ1(a),(b): all inside `Gamma1core` |
| `StructureLightStatement` | RunHyp: distinct light parts of one round have disjoint vertex sets | "(iv) light parts of one round are pairwise vertex-disjoint" | faithful (stronger hypotheses than the TeX's `n ≥ N_0, d_1 ≥ D_*`; safe for a declared input); see duplication, §3 |
| `ArcClassEulerStatement` | arcs `A` with parents of ends in `Nd` ⇒ ∃ `T ⊆ A`, `|T| ≤ |Nd|−1`, ≤ `|Nd|` closed trails of the quotient, arcs `A \ T` used exactly once | Steps 2–3 (quoted) | faithful; `|T| ≤ |E(forest)| ≤ |Nd|−1`, components with an edge (incl. single loops) ≤ `|Nd|` |
| `TransitionClaimStatement` | closed quotient trail, arcs with two distinct ends, distinct arcs with disjoint end sets ⇒ every transition has distinct vertices with equal parent | Claim (transitions) with its proof inputs (Step 1, (F-d)) | faithful; `k = 1` covered (`rotate 1` of a singleton) |
| `VisitCapStatement` | pairwise arc-disjoint closed quotient trails, `cap ≥ 1` at transition nodes ⇒ closed trails with the same arcs (multiset), each inside one old trail, `vis_Y ≤ cap Y` for every `Y`, count `≤ |Ws| + Σ_Y tr_Y/cap_Y` | Step 4 (quoted) | faithful; I re-derived the split (blocks re-closed at the processed node, `m` transitions at `Y` per block, `tr_Y` invariant, no transitions created at unprocessed nodes) |
| `TransitionCountStatement` | as above, arcs with distinct ends, any `v`: #transitions containing `v` (with multiplicity) ≤ #arcs on the trails with an end `v` | Step 5, bullets 1–2 (quoted) | faithful; true even without the end-disjointness of the transition claim (injection transition ↦ arc end at `v`) |
| `ConnectorCycleStatement` | cyclic list of (arc, connector), each Nodup with ≥ 1 edge, connector `j` from last(arc `j`) to head(arc `j+1`), arcs vertex-disjoint, connector interiors pairwise disjoint and off all arcs, arc edges ∩ connector edges = ∅ ⇒ `a_1 C_1° ⋯ a_k C_k°` is a WF cycle (Nodup, ≥ 3 vertices) with edges = arc edges + connector edges | Claim (cycles) with inputs (1)–(4) and (F-c) | faithful; the 2-cycle is excluded exactly by the edge-disjointness hypothesis (EGTest shows the degenerate instance fails it) |
| `BundleEndCountStatement` | RunHyp, outcome in the support, `3 ≤ l ≤ R`, `ArcHyp`, phase `c`, vertex `v`: `Σ_{Z non-demoted light, round l} pathEndCount(phase-c arcs of Z) v ≤ M_l − 1` | "the number of arcs of `B_{l,c}` having `v` as an end … at most `|Z(v)|−1 ≤ M_l−1`" | faithful; derivable from `ArcSys` (ends in `Rt(Z) ⊆ Z`, `pathEndCount ≤ |Z|−1`), StructureLight, CapPrePart |
| `MlTyStatement` | RunHyp, `Y` light, `r+2 ≤ l ≤ R`: `M_l ≤ λ_{l−2}^{1.6}`, `λ_{l−2}^{1.6} ≤ λ_r^{1.6}`, `M_l ≤ t_Y`, `M_l − 1 < t_Y` (ℕ) | "`M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ ⌈λ_r^{1.6}⌉ = t_Y` … `M_l−1 < t_Y`" | faithful |
| `EtaHalvingStatement` | Γ1: `η` antitone on `[log₂D_*, ∞)`, `η(2^{x/A}) ≤ η(x)/2` for `x ≥ log₂D_*` | Step 9 claim (quoted); `η(x) = log₂(2A log₂(A log₂x))/(log₂x)²` | faithful; `etaCh` matches, and `epsChain D = 614/D + η(log₂D)/371` (`EG.Chain.epsK`) matches the lemma's `ε_ch` |
| `ParentBadProbStatement` | RunHyp, `Y` light: `P_{stage 1}(Y parent-bad) ≤ |Y|^{-2}/2` | lemE1 (c), first step (quoted) | faithful; `parentBad = ¬COLc(cOutAt Y, zones)`, so it is exactly `COLcStatement` applied with `Vs = zones` |
| `EqLYStatement`, `EqZpStatement` (reconstructed) | seven inequalities of eqLY with `R − r` real; `Σ_{Y ∋ v} L_Y^{-2} < 1/2` | setting paragraph (quoted) | faithful; identical to the s5 unit's back-translation in `work/p2s/s5.md` §"s5:eqLY"/"s5:eqZp", which now records the P4B version as the one in use (lines 8, 45–46, 80, 95) |

Points checked in detail: quantifier order in `COLc*` (∀ family, then probability; the family's `ρ i` is
deterministic, as the TeX's "`ρ_{l,c,σ}`"); strict `<` in eqZp and in `M_l − 1 < t_Y`; `1 ≤ t` real in T16*
vs `t_Y ∈ ℕ` cast at the consumer; `Real.logb 2` everywhere (`s1:convGraphs`: base 2); `(12L^5)^3` literal
as in the TeX and in `COLJVRow7Statement`; `Finset.Icc 1 run.R` for "`l ≤ R`"; `⌈·⌉₊` for `T^sl_Y`, `t_Y`.

## 2. Vacuity

- Hypothesis sets are jointly satisfiable: the abstract Step statements on the EGTest instances; in the
  scratch file additionally (i) `EulerMultiStatement` on a one-vertex multigraph with one loop (connected,
  `mdeg = 2`, trail `[(e, true)]`), (ii) Step 5 count on a single arc forming a quotient loop (transition
  `(1,0)`; each vertex: 1 ≤ 1), (iii) the regime `|A| ≤ |Nd| − 1` of `ArcClassEulerStatement`, where
  `T = A`, `Ws = []` satisfies the conclusion. (iii) is not a defect: the TeX also permits outputting every
  T-join arc as single edges, and the lemma's count uses only `|T| ≤ ν_l − 1`; trails are forced as soon as
  `|A| ≥ |Nd|`.
- Conclusions are not trivially true: `VisitCap` (4) forces genuine splitting whenever some `vis > cap`,
  and (2) forbids `Ws' = []`; `TransitionCount` is attained with equality (EGTest); `ConnectorCycle`
  requires ≥ 3 vertices and the exact edge multiset; the probability bounds are `< 1` for `N ≥ 2`.
- Run-level statements need Γ1 (galactic `D_*`: Γ1(c) fails at `μ = 2^8` and needs `μ ≳ 2^{12}`), but
  `Gamma1core` is satisfiable (`EG.exists_gamma1core`) and Γ1 in full is the GAMMA unit's
  `EG/Spec/Gamma/Sat.lean`; not a vacuity of these Specs.
- `T16sStatement` at `N ≤ 1`: hypotheses and conclusion both trivial (no pairs of distinct vertices); the
  statement is meant for large `N` and is not weakened by it.
- Numerics of Step 9 re-checked (python): `η` antitone on a grid `x_1 ∈ [2^8, 10^9]`; halving at
  `x_1 ∈ {256, 300, 1000, 5000}` holds with margin ≈ `2^{-480}`; Γ1(b) at `x_1 = 256` holds.

## 3. Consistency (reuse, duplication, hidden hypotheses)

- Γ2(b),(c): never assumed. Hypothesis bundles are `Gamma1`/`Gamma1core` + `Valid` + `D_* ≤ d_1` (s2/s3)
  or `RunHyp` (s5), as in the existing Specs of those layers.
- Reuse is correct: `COLcStatement` is imported unchanged by the s3b unit (`EG/Spec/Stage1/COL.lean`,
  `COLLemmaStatement := COLStatement ∧ COLcStatement`), whose joint clause has the same family hypotheses;
  `COLaProbStatement` and `COLcIndexStatement` are acknowledged there as proof-internal steps, and
  `COLStatement`'s joint bound `N^{-2}/2` for (a),(b),(e) is too weak to replace `COLaProbStatement`
  (P4B open question 3: the s3b unit chose not to export it, so the input stays until the s3 COL proof).
  `T16sStatement` is reused unchanged by `EG/Spec/Link/T16sForced.lean` (item (b), no overlap).
  `TowerBMStatement` is referenced by `EG/Spec/HB/Tower.lean` (`TowerBRestStatement` states the remaining
  clauses; no overlap). Consumer chain `T16s → COLcIndex → COLc → ParentBadProb → (LemE1 (c))` is
  well-typed: `Stage1.law` (`Ω = Outcome`), `map_cOutAt`, `indepFun_cOutAt_zone`, `LemZonesStatement`
  (ii) (`IsRSubset` of `fun ω => Zone G run ω.zone Y i` with `ρ_Y ≥ 1/(12L^5)`, for `r + 2 ≤ R`; for
  `r ≥ R−1`, `I^U(Y) = ∅` makes the hypothesis vacuous) and (iv) supply exactly the hypotheses of
  `COLcStatement`. The abstract chain `ArcClassEuler → VisitCap → TransitionClaim/TransitionCount →
  ConnectorCycle` hands over its data in the form the next statement takes (`IsClosedTrail (qEnds …)`,
  `trailEdges … Nodup`, `∀ p ∈ W', p ∈ W`), and `TransitionCount`'s LHS predicate is literally the
  multiplicity clause of `IsPathConnected` (`(P i).1 = v ∨ (P i).2 = v`), so Step 6 needs no re-counting.
- **Duplication (minor):** `StructureLightStatement` restates the first clause of the s2b unit's
  `StructureVertexStatement` (`EG/Spec/HB/Structure.lean`, propStructure (iv)), which holds under
  `run.Valid` alone (`∀ l, ∀ a ≠ b light pre-parts of round l, Disjoint (partVerts l a) (partVerts l b)`);
  `lightParts = parts.filter isLight` and `ancVerts = partVerts`, so `StructureLightStatement` follows
  from it. `Structure.lean` imports the P4B file and its docstring (line 45) records the relation. Two
  Specs for one clause is an integrator decision; the cheapest resolution is to turn the stub
  `EG.structureLight` into a two-line proof from `structureVertex` (one declared input fewer).
- The reconstructed `EG/Spec/Light/Setting.lean` is consistent with `work/p2s/s5.md` and with its
  consumers (`EGTest/Spec_s5.lean` per P4B); the s5 unit's note says it adopted the P4B version. The
  docstring's "must re-check" sentence can be retired once the s5 reviewer signs off (cosmetic).

## 4. Hygiene

`python3 -I scripts/lint.py`: 0 findings (development mode). Module headers (`module`, `public import`,
`@[expose] public section`) present in all Spec/Defs files; `sorry` only in the nine `[DECLARED INPUT]`
stubs, each with a docstring starting with the manuscript label; no forbidden tokens.

## 5. Issues

| # | Severity | Location | Description | Suggested fix |
|---|---|---|---|---|
| 1 | minor | `EG/Spec/HB/StructureLight.lean` (`StructureLightStatement`) vs `EG/Spec/HB/Structure.lean` (`StructureVertexStatement`, clause 1) | Same clause of propStructure (iv) stated twice, the P4B version with the stronger `RunHyp` | Integrator: keep one; or replace the stub `EG.structureLight` by a proof from `structureVertex` |
| 2 | cosmetic | `EG/Spec/Light/ParentRun.lean` (`EtaHalvingStatement`) | Takes `Gamma1` although only Γ1(a),(b) ⊂ `Gamma1core` are used; the analytic lemma would be reusable without the COL-JV table | If ever revised, weaken the hypothesis to `Gamma1core` (consumers have `RunHyp`, so nothing breaks either way) |
| 3 | cosmetic | `EG/Spec/Stage1/COLa.lean`, `COLc.lean` | Extra hypothesis `Dstar ≤ run.d G 1`, which the s3b unit's `COLStatement` omits as implied by `run.Valid` once an ancestor exists | None needed (weaker statement; matches `TowerBRoundStatement`); note for the integrator's uniformity pass |
| 4 | cosmetic | `EG/Spec/Link/T16s.lean` | `ρ ≤ 1` is stated twice (explicitly and inside `IsRSubset`) | None needed |
| 5 | cosmetic | `EG/Spec/Light/Setting.lean` docstring | "The s5 unit (or its reviewer) must re-check" — the s5 unit's `s5.md` already records the P4B version as adopted | Retire the sentence after the s5 reviewer confirms |

## 6. Math findings

None of class T1–T3. Re-derived at the statement level (independently of P4B.md): the Step 4 split
invariants (`tr_Y` unchanged, no transition created at an unprocessed node), the Step 5 injection
(occurrence of `v` ↦ arc end at `v`), the Step 7 length-≥3 argument, Step 9's `(ν−1)(M−1)+ν ≤ νM`,
`56·2·2.74 = 306.88`, `14/102² < 1/743`, `2/743 < 1/371`, the `η` derivative and halving, and the COL(c)
arithmetic (`N/(12L^5) ≥ λ^{98}/768 ≥ 4λ² ≥ L²`, row 7 with `|I^U| ≤ 12L³`).

T0 (encoding, recorded): `EulerMultiStatement` requires `E ≠ ∅` because `IsClosedTrail` excludes the
empty list (the TeX's "closed trail" on an edgeless connected graph would be the empty trail); every use
(lemParent Step 3, "every component … that has an edge") satisfies it. Optional manuscript wording: "with
at least one edge".
