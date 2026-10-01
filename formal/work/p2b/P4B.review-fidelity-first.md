# Clean-room review of the P4B Specs (probe P-4, part 2). Lens: fidelity first (model A)

Reviewer: clean-room Spec reviewer. I edited no Lean file. Sources: `work/p2b/P4B.md`, the Spec and Defs files it
lists, the TeX `proofs/manuscript/s5.tex` (lemChild, lemParent Steps 0 to 9, eqLY/eqZp, lemZones, defStages,
lemE1), `s3.tex` (thmT16s, lemCOL (a) to (c) and their proofs), `s2.tex` (lemTower), `s1.tex` (log base 2).

**Verdict: APPROVE.** Every new P4B Spec back-translates faithfully. None is vacuous or trivially true, and none
assumes Γ2(b),(c). Lint: `python3 -I scripts/lint.py` gives 0 findings. The remarks below are all cosmetic or
minor, and none blocks approval.

## Checks run
- Lint: 0 findings.
- Scratch file `/tmp/p4brev/Scratch.lean` (`lake env lean`, no errors). It covers:
  - the `k = 1` case: one arc `0–1` whose two ends have the same parent gives a loop of the quotient. It is
    `IsClosedTrail`, its only transition is `(1, 0)`, and the end count at `0` is 1.
  - a `k = 2` instance of `ConnectorCycleStatement`: arcs `[0,1]`, `[2,3]` and connectors `[1,2]`, `[3,0]`. The
    conclusion holds: the result is a 4-cycle whose edges are a permutation of the arc and connector edges.
- Read `EGTest/ProbeP4B.lean`. Its instances make the hypotheses of the abstract steps hold together.

## Per-Spec fidelity (back-translation, then comparison with the TeX)

### Defs `EG/Defs/Probe/P4B/Trail.lean` (new)
- `oSrc`/`oTgt`, `transitions`: `zipWith` of `W` with `W.rotate 1` gives exactly the TeX pairs
  `(v_j^+, v_{j+1}^-)`, indices mod k. For `k = 1` it gives `(v_1^+, v_1^-)` (checked).
- `IsClosedTrail`: the list is nonempty, the arcs are distinct, and consecutive arcs meet cyclically. This
  matches "cyclic sequence `(a_1..a_k)`, `k ≥ 1`, of distinct arcs … `par(v_j^+) = par(v_{j+1}^-)`" when used
  with `qEnds`.
- `mdeg` counts a loop twice, as in "a loop adds 2". `mAdj` is `fromRel`: it drops loops and multiplicities,
  which is correct for connectivity.
- `etaCh`: `log₂(2A log₂(A log₂ x))/(log₂ x)^2`, the same as the TeX's `η`.

### `ArcClassEulerStatement` (Steps 2–3): faithful
- Lean: take arcs `A` whose end-parents lie in `Nd`. Then there exist `T ⊆ A` with `|T| ≤ |Nd|−1` and at most
  `|Nd|` closed trails of the quotient that use `A \ T` exactly once and nothing else.
- TeX: `|𝒯_i| ≤ |E(𝓕_i)| ≤ ν_l − 1`, and "at most `ν_l` closed trails … use every edge of `UQ − 𝒯_i` exactly
  once".
- The statement is true in full generality: a forest has `≤ |Nd| − #comp` edges, and each component that has
  edges gives one Euler trail. `Nd = ∅` forces `A = ∅`.
- Cosmetic: "`𝒯_i ⊆ E(𝓕_i)`" (loop-free, lies in a forest) is not recorded. No consumer needs it.

### `TransitionClaimStatement`: faithful
- Lean: take a closed trail of the quotient whose arcs have distinct ends and pairwise disjoint end sets. Then
  every transition has `t.1 ≠ t.2` and `par t.1 = par t.2`.
- This matches the TeX proof: the `k ≥ 2` case uses distinct arcs of one class, and the `k = 1` case uses (F-d).
- The hypothesis (disjoint end sets) is weaker than the TeX's "vertex-disjoint", so the statement is stronger.
  "Vertices of its node `Y`" (membership) is left to the run level (H2). Cosmetic.

### `VisitCapStatement` (Step 4): faithful
- Lean: `Ws'` are closed trails, their arcs are a permutation of the arcs of `Ws`, and each `W'` is a subset of
  some `W` with the same orientations. Every node has `vis ≤ cap`, and
  `|Ws'| ≤ |Ws| + Σ_Y tr_Y / cap_Y`.
- The TeX construction satisfies each clause. A split adds `⌈vis/cap⌉ − 1 ≤ vis/cap` trails, and the total
  `Σ_W vis_Y = tr_Y` is invariant, so the sequential processing gives the bound.
- The `⊆ some W` clause is what carries the transition claim over to the blocks.

### `TransitionCountStatement` (Step 5, refutation target): faithful and true
- Lean: for every `v`, the number of transitions containing `v`, over all trails and with multiplicity, is at most
  the number of arcs used that have `v` as an end. This matches the TeX's "Counting" bullet.
- I re-derived it. The injection is: transition `j` goes to `W[j]` if `t.1 = v`, and to `W[j+1]` otherwise. A
  collision would force both ends of one arc to equal `v`, which the distinct-ends hypothesis rules out.
- Counting all nodes rather than only `par(v)` gives the same count, since `v` only occurs at `par(v)`.

### `ConnectorCycleStatement` (Step 7 Claim): faithful
- The hypotheses are (1) to (4) of the TeX proof plus the edge-disjointness that (F-c) supplies.
- The conclusion: the cycle is Nodup with `≥ 3` vertices, and its cyclic edges are a permutation of the arc and
  connector edges.
- The degenerate 2-cycle is excluded exactly by the edge-disjointness hypothesis, which is the TeX's "As `G` is
  simple, these are the same edge".

### `BundleEndCountStatement`: faithful
- Lean: under `RunHyp` and `ArcHyp`, `Σ_{Z ∈ childParts} pathEndCount(phase-c arcs of Z, v) ≤ M_l − 1` (in ℕ).
- TeX: "the number of arcs of `B_{l,c}` having `v` as an end … at most `|Z(v)|−1 ≤ M_l−1`".
- It is true via:
  - arcs lie in `H0 ⊆ E_l(Z)`, so their ends are in `Z` (StructureHY);
  - light parts of one round are disjoint (StructureLight);
  - the `ArcSys` bound is `≤ |Z|−1`;
  - CapPrePart gives `|Z| ≤ M_l`.

### `MlTyStatement`: faithful
- It states the four links `M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6}`, `M_l ≤ t_Y`, and `M_l − 1 < t_Y`, with
  `t_Y = ⌈λ_r^{1.6}⌉₊`.
- The range `r + 2 ≤ l ≤ R` is right (`l ≥ 3` follows from `r ≥ 1`). The logarithms are base 2, matching
  `s1.tex` l.730.

### `EtaHalvingStatement`: faithful and true
- The domain is `[log₂D_*, ∞)`. I re-derived both claims:
  - `x_1 = log₂x ≥ log₂log₂D_* ≥ 2^8` (Γ1(a)), `x_2 ≥ 14.7`, `x_3 ≥ 11.6`, so `d ln η/dx_1 < 0`;
  - `η(2^{x/A}) = A² log₂(2Ax_1)/x²`, and `2A²x_1² log₂(2Ax_1) ≤ 2^{2x_1}` by Γ1(b).
- Taking full `Gamma1` where only (a) and (b) are used is a weaker statement, so it is safe.

### `ParentBadProbStatement`: faithful
- Lean: `P_{stage1}(parentBad Y) ≤ |V(Y)|^{-2}/2` for every light `Y`, under `RunHyp`. This is the TeX's
  lemE1 (c) intermediate.
- `parentBad` is by definition `¬COLc` for the zone family, so it follows from COLc + lemZones (ii),(iv).

### `COLcIndexStatement`: faithful
- Lean: `P(COL(a) ∧ ¬ LU_i is (2^{12}L^4, t_Y)-PC through W) ≤ 2^{86} t_Y L^{19}(12L^5)^3 N^{-3}` for a
  `ρ`-random `W` (`ρ ≥ 1/(12L^5)`, and `ρ ≤ 1` via `IsRSubset`) that is independent of `D`.
- This is the TeX's "Condition … in which (a) holds … Each index fails with probability at most …". It is true
  by T16* applied conditionally on `D`, using `ρ^{-3} ≤ (12L^5)^3` and `ρ^{-5} ≤ (12L^5)^5` (row 4).

### `COLcStatement`: faithful
- It quotes lemCOL (c) verbatim. The quantifiers are `Y` light, then `D`, then the family and its `ρ_i`. The
  hypotheses are: `ρ_i`-random at each `i ∈ I^U`, `ρ_i ≥ 1/(12L^5)`, joint independence from `D`, and no
  independence across indices. The conclusion is `P(¬COLc) ≤ N^{-2}/2`.
- Minor T0: `μ.IndepFun D Vs` is over the whole `LentTag`-indexed family, not only `I^U(Y)`. This is harmless:
  extend any `I^U`-family by constants. The consumer's zone family satisfies it anyway (lemZones (iv)).
- The extra `D_* ≤ d_1` is part of the setting (documented in `COL.lean`).

### Declared inputs
- `EulerMultiStatement`: faithful. The graph is nonempty and connected in the sense that the ends of the edges
  are pairwise reachable, and all degrees are even with a loop counted twice. The conclusion is a closed trail
  using each edge exactly once.
- `T16sStatement`:
  - Faithful to all clauses: `ε' ∈ [2^{-7},1]`, `ρ ∈ (0,1]`, `t ≥ 1`, `ρN ≥ L^2`,
    `s ≥ 2^{135}tL^{28}ρ^{-5}`, probability `≥ 1 − 2^{86}tL^{19}ρ^{-3}N^{-3}`, `L = log₂N`.
  - Edge cases: `N ≤ 1` is trivially true. At `N = 2` the expander definition (the `|U| = 1` clause) forces
    `δ > s`, so the statement cannot be falsified with an edgeless graph.
- `COLaProbStatement`: faithful to the proof's `N^{-2}/4`. It is not implied by the lemma statement
  (`(a)∧(b)∧(e) ≥ 1 − N^{-2}/2`), so declaring it as an input is justified. It is stated for all ancestors.
- `TowerBMStatement`:
  - Faithful: `(A log₂λ_{l−2})^{2A}` with `A = 105`, for `3 ≤ l ≤ R`, and `Σ_{l=1}^R 1/M_l ≤ 2/D_*`.
  - It uses `Gamma1core`, as the other lemTower Specs do. Row 12 needs Γ1(c) at `μ = log₂λ_{l−2}`, which is
    available.
- `StructureLightStatement`: faithful. The disjointness of light parts in one round is stated under `RunHyp`,
  which is a stronger hypothesis and so a weaker statement.

### Reconstructed `EG/Spec/Light/Setting.lean` (s5 unit's file)
- The current content is faithful to eqLY (all seven links, including "`R − r ≤ L_Y/102`", with `R − r` real)
  and to eqZp (strict `< 1/2`, sum over the light parts `Y ∋ v`).

## Consistency
- Existing Specs are reused as P4B.md says:
  - s5: LemChild/LemParent*/Zones/Stages;
  - P4A: PV;
  - P2E: EulerTreeTJoin.
- No Defs were edited. The only new Defs are in `EG/Defs/Probe/P4B/`.
- Later units reuse the P4B Specs rather than duplicating them: `COLLemmaStatement := COLStatement ∧ COLcStatement`
  (s3), and `TowerBRestStatement` excludes `TowerBM`.
- `StructureVertexStatement` (s2 unit, `EG/Spec/HB/Structure.lean`, written after P4B) implies
  `StructureLightStatement`, and says so in its docstring. The stub `EG.structureLight` can therefore become a
  one-line derivation instead of a declared input.
- There are no Γ2(b),(c) hypotheses anywhere. The sets used are `Gamma1`/`Gamma1core`/`RunHyp` only.

## Remarks (none blocking)
1. (minor) Replace the declared input `structureLight` by a proof from `StructureVertexStatement` (+ `RunHyp →
   Valid`), so that there is one source for propStructure (iv).
2. (cosmetic, process) `work/p2s/s5.md` ("Concurrent-write incident") still describes a `Setting.lean` that has
   a `ZonesRhoStatement` and lacks the "`R − r ≤ L_Y/102`" conjunct. The current file has no `ZonesRho` and does
   have that conjunct, and `P4B.md` gives a contradictory account of who overwrote whom. The orchestrator should
   record the current file as authoritative and fix `s5.md`. The content itself is faithful.
3. (cosmetic, T0) `COLcStatement`/`COLStatement`: the independence is over the whole `LentTag` family. It could
   be recorded in the T0 table.
4. (cosmetic) `TransitionClaimStatement` omits "both vertices lie in `Y`", and `ArcClassEulerStatement` omits
   "`𝒯_i ⊆` spanning forest". Both are abstraction choices (H2) that no consumer needs.

## Math findings
None of class T1–T3. I re-derived the refutation targets and they hold: Step 5 (transition count ≤ arc ends
≤ `M_l − 1`), `M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ t_Y` (Γ1(c)), η monotonicity and halving (Γ1(a),(b)), the Step 9
constants (`56·2·2.74 ≤ 307`, `14/102² ≤ 1/743`, `2/743 ≤ 1/371`), and COL(c) (T16* per index + row 7 +
`N^{-2}/4` for (a)).
