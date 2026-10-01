# P2b probe unit P4B (probe P-4, part 2), stage 1: statements

Chain: lemChild (PV instance, (E1′)) → lemParent Steps 1–9 (quotient multigraph, T-join, Euler, trail surgery,
slots, multiplicity `M_l − 1 ≤ t_Y`, η halving) → COL(c) (T16* per U-index, joint independence). TRIAGE §4 row
P-4, second part. Manuscript v6.1 `proofs/manuscript/s5.tex` (lemChild, lemParent, lemE1 (c)), `s3.tex`
(lemCOL (c), thmT16s), `s1.tex` (citEuler), `s2.tex` (lemTower (b), propStructure). The manuscript is a
CANDIDATE proof, reviewed by AI only.

Refutation targets (TRIAGE §4): "Parent Step 5 `M_l − 1 ≤ t_Y`; COL(b)/(c) `t^JS` and `t_Y`". Hit by:
- `TransitionCountStatement` (Step 5: occurrences of `v` in transition pairs ≤ number of arc ends at `v`),
- `BundleEndCountStatement` (Step 5: every `v` is an end of ≤ `M_l − 1` arcs of a U-bundle),
- `MlTyStatement` (Step 5: `M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ t_Y`, so `M_l − 1 < t_Y`),
- `COLcIndexStatement`, `COLcStatement` (COL(c) at multiplicity `t_Y`), `ParentBadProbStatement` (its use on
  the zones). `COL(b)`/`t^JS` belongs to probe P-2 (JS-LC) and is not restated here.
No statement was found false (see "Math findings").

## Status (stage 1)

- All files below compile: `lake build` of every new Spec/Proof module; `scripts/check.sh EGTest/ProbeP4B.lean`
  rc=0, 0 errors, 0 warnings. `python3 -I scripts/lint.py`: 0 findings.
- No proofs yet except the fix-round derivation of `EG.structureLight`. `sorry` appears only in the 9 declared-input stubs listed below.
- About 1130 lines of Lean (Defs 105, Specs ~560, stubs ~200, test ~225).

## IMPORTANT problem (for the orchestrator): accidental overwrite of an s5-unit file

While this unit was running, the P2 s5 Spec unit (`work/p2s/s5.md`) wrote `EG/Spec/Light/*.lean` (untracked).
P4B first wrote a file of the same path `EG/Spec/Light/Setting.lean` (it did not exist when P4B listed `EG/Spec`)
and so **overwrote the s5 unit's `Setting.lean`**, which was untracked and cannot be recovered from git. P4B then
**reconstructed** it from the s5 unit's back-translation in `work/p2s/s5.md` (sections "s5:eqLY — `EqLYStatement`"
and "s5:eqZp — `EqZpStatement`"): same names, same argument order as the other s5 Specs
(`V [DecidableEq V] G N0 Dstar run`), `RunHyp`, the seven inequalities of eqLY with `R − r` a real difference
(including "`R − r ≤ L_Y/102`"), and the sum of eqZp over light parts containing `v` with `L_Y^(-2 : ℤ)`. The file's
module docstring says it was reconstructed. `EGTest/Spec_s5.lean` (s5 unit) compiles against it (rc=0, 0 errors).
**The s5 unit or its reviewer must re-check `EG/Spec/Light/Setting.lean` against its original.** No other file of
another unit was touched.

After this, P4B reused the s5 unit's Specs instead of writing its own for the lemmas themselves
(`LemChildStatement`, `LemParentStatement`, `LemParentSumStatement`, `LemParentAvailDisjointStatement`,
`LemParentLimitStatement`) and dropped its own drafts of these, of a lemHB Spec (covered by `StagesHBStatement`)
and of a ZonesRho Spec (covered by `LemZonesStatement` (ii)).

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Probe/P4B/Trail.lean` | `EG.Defs.Probe.P4B.Trail` | **NEW DEFS**: `EG.MTrail.{oSrc, oTgt, transitions, IsClosedTrail, qEnds, vis, trailEdges, mdeg, mVerts, mAdj}`, `EG.Light.etaCh` |
| `EG/Spec/Light/ParentSteps.lean` | `EG.Spec.Light.ParentSteps` | probe nodes (abstract): `ArcClassEulerStatement`, `TransitionClaimStatement`, `VisitCapStatement`, `TransitionCountStatement`, `ConnectorCycleStatement` |
| `EG/Spec/Light/ParentRun.lean` | `EG.Spec.Light.ParentRun` | probe nodes (run level): `BundleEndCountStatement`, `MlTyStatement`, `EtaHalvingStatement`, `ParentBadProbStatement` |
| `EG/Spec/Stage1/COLc.lean` | `EG.Spec.Stage1.COLc` | probe nodes: `COLcIndexStatement`, `COLcStatement` |
| `EG/Spec/Found/EulerMulti.lean` | `EG.Spec.Found.EulerMulti` | declared input `EulerMultiStatement` |
| `EG/Spec/Link/T16s.lean` | `EG.Spec.Link.T16s` | declared input `T16sStatement` |
| `EG/Spec/Stage1/COLa.lean` | `EG.Spec.Stage1.COLa` | declared input `COLaProbStatement` |
| `EG/Spec/HB/TowerBM.lean` | `EG.Spec.HB.TowerBM` | declared input `TowerBMStatement` |
| `EG/Spec/HB/StructureLight.lean` | `EG.Spec.HB.StructureLight` | declared input `StructureLightStatement` |
| `EG/Spec/Light/Setting.lean` | `EG.Spec.Light.Setting` | s5 unit's file, RECONSTRUCTED (see above): `EqLYStatement`, `EqZpStatement` |
| `EG/Proof/Found/EulerMulti.lean` | | stub `EG.eulerMulti` |
| `EG/Proof/Link/T16s.lean` | | stub `EG.t16s` |
| `EG/Proof/Stage1/COLa.lean` | | stub `EG.colaProb` |
| `EG/Proof/HB/TowerBM.lean` | | stub `EG.towerBM` |
| `EG/Proof/HB/StructureLight.lean` | | `EG.structureLight` **derived** (fix round) from `EG.structureVertex`; `EG.mem_lightParts_iff`, `EG.structureLight_of_structureVertex` (0 sorry) |
| `EG/Proof/HB/Structure.lean` | | stub `EG.structureVertex : StructureVertexStatement` (s2 unit's Spec; fix round) |
| `EG/Proof/Vortex/PV.lean` | | stub `EG.pvLemma : PVStatement` (P4A's Spec) |
| `EG/Proof/Light/Setting.lean` | | stub `EG.eqLY : EqLYStatement` (s5 unit's Spec) |
| `EG/Proof/Light/Stages.lean` | | stub `EG.stagesHB : StagesHBStatement` (s5 unit's Spec) |
| `EG/Proof/Light/Zones.lean` | | stub `EG.lemZones : LemZonesStatement` (s5 unit's Spec) |
| `EGTest/ProbeP4B.lean` | | non-vacuity checks |

Root imports for the orchestrator (I did not edit `EG.lean`/`EGTest.lean`): to `EG`: `EG.Defs.Probe.P4B.Trail`,
`EG.Spec.Light.ParentSteps`, `EG.Spec.Light.ParentRun`, `EG.Spec.Stage1.COLc`, `EG.Spec.Stage1.COLa`,
`EG.Spec.Found.EulerMulti`, `EG.Spec.Link.T16s`, `EG.Spec.HB.TowerBM`, `EG.Spec.HB.StructureLight`, and the ten
`EG.Proof.*` modules above (nine stubs incl. `EG.Proof.HB.Structure`, plus `EG.Proof.HB.StructureLight`); to `EGTest`: `EGTest.ProbeP4B`.

## Nodes: label → Lean name

All statements in namespace `EG.Spec`; planned proof names in namespace `EG`.

| Label | Role | Statement | Owner of Spec | Planned proof (stage 2) |
|---|---|---|---|---|
| s5:lemChild | probe | `LemChildStatement` | s5 unit (reused) | `EG.lemChild` |
| s5:lemParent Steps 2–3 (quotient, T-join, Euler) | probe | `ArcClassEulerStatement` | P4B | `EG.arcClassEuler` (uses `eulerTreeTJoin`, `eulerMulti`) |
| s5:lemParent Claim (transitions) | probe | `TransitionClaimStatement` | P4B | `EG.transitionClaim` |
| s5:lemParent Step 4 (visit capping, trail surgery) | probe | `VisitCapStatement` | P4B | `EG.visitCap` |
| s5:lemParent Step 5 (end count; **refutation target**) | probe | `TransitionCountStatement` | P4B | `EG.transitionCount` |
| s5:lemParent Step 5 + (F-a,c,d) (**refutation target**) | probe | `BundleEndCountStatement` | P4B | `EG.bundleEndCount` |
| s5:lemParent Step 5 comparison (**refutation target**) | probe | `MlTyStatement` | P4B | `EG.mlTy` |
| s5:lemParent Step 7 Claim (cycles) | probe | `ConnectorCycleStatement` | P4B | `EG.connectorCycle` |
| s5:lemParent Step 9 (η halving) | probe | `EtaHalvingStatement` | P4B | `EG.etaHalving` |
| s5:lemParent (lemma, (i)–(iii)) | probe | `LemParentStatement` | s5 unit (reused) | `EG.lemParent` (Steps 1, 5 slots, 6, 8 inline) |
| s5:lemParent (ii) sum | probe | `LemParentSumStatement` | s5 unit (reused) | `EG.lemParentSum` |
| s5:lemParent disjointness over `(l,c)` | probe | `LemParentAvailDisjointStatement` | s5 unit (reused) | `EG.lemParentAvailDisjoint` |
| s3:lemCOL (c), per U-index (T16*) | probe | `COLcIndexStatement` | P4B | `EG.colcIndex` |
| s3:lemCOL (c) | probe (**refutation target**) | `COLcStatement` | P4B | `EG.colc` |
| s5:lemE1 (c), proof step (joint independence) | probe | `ParentBadProbStatement` | P4B | `EG.parentBadProb` |
| s1:citEuler (b) | **declared input** | `EulerMultiStatement` | P4B | stub `EG.eulerMulti` |
| s1:citEuler (a) | declared input (reused) | `EulerTreeTJoinStatement` | P2E | stub `EG.eulerTreeTJoin` (exists) |
| s3:thmT16s | **declared input** | `T16sStatement` | P4B | stub `EG.t16s` |
| s3:lemCOL (a), failure bound | **declared input** | `COLaProbStatement` | P4B | stub `EG.colaProb` |
| s4:lemPV | **declared input** | `PVStatement` | P4A (reused) | stub `EG.pvLemma` (new) |
| s2:lemTower (b), `M_l` clauses | **declared input** | `TowerBMStatement` | P4B | stub `EG.towerBM` |
| s2:propStructure (iv), light parts | **declared input** (reused, fix round) | `StructureVertexStatement` (first clause; consumer form `StructureLightStatement`, derived) | s2 unit | stub `EG.structureVertex` (new); `EG.structureLight` proved from it |
| s5:eqLY | **declared input** (reused) | `EqLYStatement` | s5 unit | stub `EG.eqLY` (new) |
| s5:defStages claims | **declared input** (reused) | `StagesHBStatement` | s5 unit | stub `EG.stagesHB` (new) |
| s5:lemZones | **declared input** (reused) | `LemZonesStatement` | s5 unit | stub `EG.lemZones` (new) |
| s2:lemTower (a), (b) first sentence, (b) late | used (reused, stubs exist) | `TowerAStatement`, `TowerBRoundStatement`, `TowerBLateStatement` | P3B / P4A / P2J | existing stubs |
| s2:propStructure (iii); s2:lemCap (ii) | used (reused) | `StructureHYStatement`, `CapPrePartStatement` | P2J / Cap unit | existing |
| s3:lemCOLJV rows 4, 7, 8; (i) | used (P4A nodes / input) | `COLJVRow4/7/8Statement`, `COLJVCountStatement` | P4A | P4A stage 2 / stub `EG.colJVCount` |

## Declared inputs, with justification

1. **[s1:citEuler] (b)** `EulerMultiStatement` — stage-α standard fact (TRIAGE: "stage-α Euler hypothesis"). Used in
   Step 3 for the closed Euler trails of the even components of `UQ − 𝒯_i` (multigraph with loops). Item (a) is
   P2E's `EulerTreeTJoinStatement` (a spanning tree is simple; P2E review 2 confirmed it covers lemParent Step 3).
2. **[s3:thmT16s]** `T16sStatement` — s3's theorem (the task: "T16* if it is s3's"); applied once per U-index in
   COL(c). No Spec existed.
3. **[s3:lemCOL] (a), failure bound from the proof** `COLaProbStatement` (`P(¬COL(a)) ≤ N^{-2}/4`) — the proof of
   COL(c) adds it ("Together with the failure probability of (a)"); the lemma statement only bounds (a),(b),(e)
   jointly by `N^{-2}/2`, which is too weak (blueprint E1-COL-A-BOUND). Its proof (three L15⁺ applications,
   conditioning on the split) is the s3 COL unit's job.
4. **[s4:lemPV]** `PVStatement` (P4A's Spec, deterministic form) — lemChild instantiates it. P4A: "P4B declares it
   as an input (lemChild)". New stub `EG.pvLemma`.
5. **[s2:lemTower] (b), `M_l` clauses** `TowerBMStatement`: `M_l ≤ (A log λ_{l−2})^{2A} ≤ λ_{l−2}^{1.6}` (row 12;
   Step 5 and Step 9) and `Σ_{l≤R} 1/M_l ≤ 2/D_*` (Step 9). Not covered by `TowerBRound`/`TowerBLate`.
6. **[s2:propStructure] (iv)** `StructureLightStatement`: light parts of one round are pairwise vertex-disjoint
   ((F-c), Steps 1 and 5). Not covered by any existing Spec.
7. **[s5:eqLY]** (s5 unit's `EqLYStatement`) — Step 4 (`T^sl_Y ≥ (102 log₂λ_{l−2})^2`) and Step 9.
8. **[s5:defStages] claims** (s5 unit's `StagesHBStatement`) — lemChild's hypothesis check: `X_Z` a spanning
   `(2^{-6}, s_l/2)`-expander, `2vm ≤ s_l/2`, `A_Z` a Lemma-HB family (it subsumes propStructure (i) and s3:lemHB).
9. **[s5:lemZones]** (s5 unit's `LemZonesStatement`) — (ii) the zones are `ρ_Y`-random with `ρ_Y ≥ 1/(12L^5)`,
   (iv) jointly independent of the colourings; used by `ParentBadProbStatement`.

Used but not declared (proved by other units or already stubbed): TowerA/TowerBRound/TowerBLate, StructureHY,
CapPrePart (`|Z^0| ≤ M_l`, `deg_{E_l(Z)} ≤ M_l − 1`), COLJVRow4/7/8 (P4A nodes), COLJVCount (row 9, stubbed),
EulerTreeTJoin (stubbed). Lib lemmas used: `EG.Light.E1_childData`, `AY_spec`, `X_verts_of_isLight`,
`EG.Stage1.map_cOutAt`, `indepFun_cOutAt_zone`, `isRSubset_Zone`, `COLg_of_mem_supp_law`.
Not used: Lovász/Cor 22 (inside PV), Chernoff/Markov (lemE1 (a),(b) are not P4B nodes), lemLacunary (Step 9's
geometric sum is done inline as in the TeX; `EtaHalvingStatement` isolates the analytic part).

## Definitions used

- Locked: `EG.HB.Run.{Valid, R, lightParts, ancestors, ancVerts, X, E, LY, lam, M, s, P, d, nuAnc}`,
  `EG.Stage1.{Outcome, law, COLOut, colLaw, COLa, COLc, lentClass, LU, IU, tY, Tslot, Zone, zonePhase, rhoY,
  LentTag}`, `EG.Light.{demoted, parentBad, goodParents, childParts, ArcHyp, ArcSys, H0Adm, Arc, arcEdges,
  bundleEdges, lentUAvail, IsConnector, Jbar, childData, epsChain}`, `EG.Vortex.{PVHyp, PVData}` (P4A probe Defs),
  `EG.{FGraph, IsExpander, IsPathConnected, IsDecomp, Obj, cycleEdges, walkEdges, interior, pathEndCount, degE,
  RunHyp, Gamma1, Gamma1core, FinDist, IsRSubset, IndepFun}`, `EG.Aexp`, `EG.logStar`.
- **New Defs** `EG/Defs/Probe/P4B/Trail.lean` (no locked file has multigraphs or trails; blueprint
  PAR-MGRAPH-EULER recommends "finite index set I with an endpoint map" instead of a multigraph type):
  - `oSrc/oTgt ends (e,b)`: start/end of the oriented edge (`b = true`: `(ends e).1 → (ends e).2`);
  - `transitions ends W`: `zipWith (fun p q => (oTgt p, oSrc q)) W (W.rotate 1)` = the pairs `(v_j^+, v_{j+1}^-)`;
  - `IsClosedTrail ends W`: `W ≠ [] ∧ (W.map fst).Nodup ∧ ∀ t ∈ transitions ends W, t.1 = t.2`;
  - `qEnds par ends`: the quotient endpoint map `a ↦ (par v, par v')` (Step 2);
  - `vis par ends W Y`: number of transitions with `par t.1 = Y` (Step 4); `trailEdges Ws`: the arcs of a list
    of trails;
  - `mdeg E ends v`: multigraph degree, loop counted twice; `mVerts`; `mAdj` (`SimpleGraph.fromRel`);
  - `EG.Light.etaCh x = log₂(2A log₂(A log₂ x)) / (log₂ x)^2` (Step 9's `η`).
  Checks in EGTest: a closed trail of the quotient is exactly a TeX closed trail of oriented arcs (the transitions
  in `V` have equal parents, `IsClosedTrail (qEnds par ends) W`).

## Hazards / encoding decisions

- **H1 (reuse of the s5 unit's lemma Specs).** lemChild, lemParent (per round), its sum and the `(l,c)`
  disjointness are the s5 unit's Specs. Their encoding decisions carry over: deterministic lemChild (no good
  event, no `≥ 1/3`; TRIAGE §2.8 PV-DET-SPEC), arcs as input (`ArcHyp`, PAR-ARCS-INPUT), `cap_l` existential,
  "depends only on" dropped (T0, TRIAGE §2.12).
- **H2 (abstract step engines).** Steps 2–5 and 7 are stated for arbitrary index types, ends, parent maps and
  node sets, without the run. This is strictly more general than the lemma's use and is what the TeX proof uses
  (only (F-a)–(F-d)). The run-level link is `BundleEndCountStatement` and `MlTyStatement`.
- **H3 (Euler (b), T0).** Stated for a nonempty edge set (a closed trail has `k ≥ 1` edges), "connected" =
  the ends of the edges are pairwise reachable in the adjacency graph (isolated vertices dropped; equivalent).
  Loops count 2 in `mdeg`.
- **H4 (VisitCap bound).** The TeX's `cap_l ≤ Σ_{Y,c,i} tr_{c,i,Y}/T^sl_Y` is stated per list of trails as
  `|Ws'| ≤ |Ws| + Σ_Y tr_Y / cap_Y` (sum over the nodes of the transitions), with the extra clauses the later
  steps need: each final trail uses arcs of one initial trail with the same orientation (so vertex-disjointness
  within a class, hence the transition claim, is preserved), and the arcs are preserved as a multiset.
- **H5 (slots, Step 5).** The slot assignment ("pairwise distinct slots `σ ∈ [T^sl_Y]` … possible because
  `vis_Y(𝒲) ≤ T^sl_Y`") is an injection `Fin vis → Fin T` and has no node of its own; it is part of the
  `LemParentStatement` proof.
- **H6 (COL(c) per index).** The per-index failure is stated as `P(COL(a) ∧ ¬ path-connected_i) ≤
  2^{86} t_Y L^{19} (12L^5)^3 N^{-3}` — the TeX's "Condition on a stage-(i)/(ii) outcome in which (a) holds … Each
  index fails with probability at most …", with `ρ^{-3}` replaced by `(12L^5)^3` as in the TeX and in row 7
  (`COLJVRow7Statement`).
- **H7 (COL(c) joint independence).** `μ.IndepFun D Vs` for the whole family `Vs : Ω → LentTag → Finset V`; no
  independence across indices is assumed ("The family may be dependent across indices"). Stated for every light
  `Y`, including `r ≥ R − 1` (vacuous: `I^U(Y) = ∅`).
- **H8 (hypothesis bundles).** s5 nodes use `RunHyp` (s5 setting, as the s5 unit). s2/s3 statements use `Gamma1`
  (resp. `Gamma1core` for lemTower, as the existing TowerA/B/BLate Specs) + `Valid` + `D_* ≤ d_1`.
  `StructureLightStatement` uses `RunHyp` (the proposition assumes `n ≥ N_0`, `d_1 ≥ D_*`).
  `EtaHalvingStatement` takes `Gamma1` although only Γ1 (a), (b) are used (weaker statement, safe).
- **H9 (`M_l − 1` in ℕ).** `BundleEndCountStatement` bounds by `run.M G l - 1` (natural subtraction; `M_l ≥ 2^{40}`),
  `MlTyStatement` states both `M_l ≤ t_Y` and `M_l − 1 < t_Y` in ℕ.
- **H10 (not stated).** "The objects and `LentU` depend only on …" (T0, s5 unit); the joint probability of COL
  items (a),(b),(c),(e) (`1 − N^{-2}`; not a P4B node, (b) is P-2); lemE1 (c)'s final union bound (s5 unit's
  `LemE1Statement` (c)).

## Back-translation of every P4B Spec (plain mathematics next to the TeX)

### `EulerMultiStatement` [s1:citEuler] (b)
TeX: "A connected graph (or multigraph) in which every vertex has even degree has a closed trail using every edge
exactly once." Lean: for a finite nonempty set `E` of edges with endpoint map `ends` (loops, parallel edges allowed),
if any two ends of edges are joined by a walk and every vertex has even degree (loops counting 2), then there is a
nonempty cyclic list of oriented edges, no edge repeated, consecutive edges meeting (cyclically), whose edges are
exactly `E`.

### `T16sStatement` [s3:thmT16s]
TeX: "Let `X` be an `N`-vertex `(ε′,s)`-expander with `ε′ ∈ [2^{-7},1]` … `L := log N`. Let `ρ ∈ (0,1]` and `t ≥ 1`,
and let `V` be a `ρ`-random subset of `V(X)`. … Suppose that `ρN ≥ L^2` and `s ≥ 2^{135}tL^{28}ρ^{-5}`. Then, with
probability at least `1 − 2^{86}tL^{19}ρ^{-3}N^{-3}`, the graph `X` is `(2^{12}L^4,t)`-path connected through `V`."
Lean: for a graph `X`, reals `ε′ ∈ [2^{-7},1]`, `s`, `ρ ∈ (0,1]`, `t ≥ 1`, with `X` an `(ε′,s)`-expander, and any
random set `W` whose law is the `ρ`-random subset law of `V(X)`, if `L^2 ≤ ρN` and `2^{135}tL^{28}ρ^{-5} ≤ s`
(`N = |V(X)|`, `L = log₂N`), then `P(X is (2^{12}L^4, t)-path connected through W) ≥ 1 − 2^{86}tL^{19}ρ^{-3}N^{-3}`.

### `COLaProbStatement` [s3:lemCOL] (a), proof
TeX: "the total failure probability of (a) is at most `2(2+k+k_own)N^{-5} ≤ 2(2+λ^{3.3}+2λ)N^{-5} ≤ N^{-2}/4`."
Lean: under Γ1, for a valid run with `d_1 ≥ D_*`, every ancestor `Y` and every random variable `D` with law
`colLaw Y`: `P(COL(a) fails for D) ≤ |V(Y)|^{-2}/4`.

### `COLcIndexStatement` [s3:lemCOL] (c), per index
TeX: "Condition as in (b) [on a stage-(i)/(ii) outcome in which (a) holds]. The sets `V_{l,c,σ}` are independent of
the colouring. For a fixed index, apply Theorem s3:thmT16s … with `t := t_Y` … and `ρ := ρ_{l,c,σ} ≥ 1/(12L^5)`. …
Each index fails with probability at most `2^{86}tL^{19}(12L^5)^3N^{-3}`." Lean: under Γ1, valid run, `d_1 ≥ D_*`,
for a light part `Y`, a U-index `i ∈ I^U(Y)`, lending data `D` with law `colLaw Y`, and a `ρ`-random subset `W` of
`V(Y)` with `ρ ≥ 1/(12L_Y^5)` independent of `D`: `P(COL(a) holds for D and the lent class of i is not
(2^{12}L_Y^4, t_Y)-path connected through W) ≤ 2^{86} t_Y L_Y^{19} (12L_Y^5)^3 |V(Y)|^{-3}`.

### `COLcStatement` [s3:lemCOL] (c)
TeX: quoted in the module docstring ("Let `Y` be light. Let `(V_{l,c,σ})` be random subsets of `V(Y)`, independent
of the stage-1 lending data of `Y`, … `ρ_{l,c,σ} ≥ 1/(12L_Y^5)`. The family may be dependent across indices. Then,
with probability at least `1 − |V(Y)|^{-2}/2` …, every U-lent class … is `(2^{12}L_Y^4,t_Y)`-path connected through
`V_{l,c,σ}`"). Lean: under Γ1, valid run, `d_1 ≥ D_*`, for a light `Y`, lending data `D` with law `colLaw Y` and a
family `Vs` of random sets (indexed by lent tags) jointly independent of `D`, each `Vs_i` (`i ∈ I^U(Y)`) a
`ρ_i`-random subset of `V(Y)` with `ρ_i ≥ 1/(12L_Y^5)`: `P(some U-lent class of D is not (2^{12}L_Y^4, t_Y)-path
connected through its set) ≤ |V(Y)|^{-2}/2`.

### `TowerBMStatement` [s2:lemTower] (b)
TeX: "For `3 ≤ l ≤ R`: `M_l ≤ (A log λ_{l−2})^{2A} ≤ λ_{l−2}^{1.6}` … Moreover `Σ_{l≤R}1/M_l ≤ 2/D_*`." Lean: under
Γ1 (a)–(e), valid run, `d_1 ≥ D_*`: for `3 ≤ l ≤ R`, `M_l ≤ (105·log₂λ_{l−2})^{210} ≤ λ_{l−2}^{1.6}`; and
`Σ_{l=1}^{R} 1/M_l ≤ 2/D_*`.

### `StructureLightStatement` [s2:propStructure] (iv)
TeX: "light parts of one round are pairwise vertex-disjoint". Lean: under `RunHyp`, two distinct light parts of the
same round have disjoint vertex sets.

### `ArcClassEulerStatement` [s5:lemParent] Steps 2–3
TeX: quoted in the docstring (quotient multigraph, spanning forest, `𝒯_i` with `|𝒯_i| ≤ ν_l − 1`, "at most `ν_l`
closed trails …, which together use every edge of `UQ_{l,c,i} − 𝒯_i` exactly once"). Lean: for a finite set `A` of
arcs with ends `ends` and parents `par` of the ends lying in a node set `Nd`, there are `T ⊆ A` with
`|T| ≤ |Nd| − 1` and a list of at most `|Nd|` closed trails of the quotient multigraph (edge `a` joining
`par(v), par(v')`) such that every arc of `A \ T` is used by exactly one trail, once, and no other arc is used.

### `TransitionClaimStatement` [s5:lemParent] Claim (transitions)
TeX: "In every closed trail of this kind, every transition consists of two distinct vertices of its node `Y`."
Lean: for a closed trail `W` of the quotient multigraph whose arcs have two distinct ends and pairwise disjoint end
sets, every transition `(v_j^+, v_{j+1}^-)` has `v_j^+ ≠ v_{j+1}^-` and `par(v_j^+) = par(v_{j+1}^-)`.

### `VisitCapStatement` [s5:lemParent] Step 4
TeX: quoted in the docstring. Lean: for pairwise arc-disjoint closed trails `Ws` of the quotient and capacities
`cap ≥ 1` at the nodes of their transitions, there are closed trails `Ws'` of the quotient using the same arcs (as a
multiset), each consisting of oriented arcs of a single trail of `Ws`, with at most `cap Y` transitions at every node
`Y`, and `|Ws'| ≤ |Ws| + Σ_Y tr_Y/cap_Y` where `tr_Y` is the number of transitions of `Ws` at `Y`.

### `TransitionCountStatement` [s5:lemParent] Step 5 (refutation target)
TeX: "every arc end lies in at most one transition over all final trails … the number of pairs … containing `v`,
counted with multiplicity, is at most the number of arcs … having `v` as an end." Lean: for pairwise arc-disjoint
closed trails of the quotient whose arcs have two distinct ends, and every vertex `v`: the number of transitions
(over all trails, with multiplicity) containing `v` is at most the number of arcs used by the trails with an end
equal to `v`. EGTest shows equality on an instance.

### `BundleEndCountStatement` [s5:lemParent] Step 5 with (F-a), (F-c), (F-d) (refutation target)
TeX: "By (F-d) and (F-c), all of them are arcs of the unique round-`l` light part `Z(v)` containing `v`, and there are
at most `|Z(v)| − 1 ≤ M_l − 1` of them." Lean: under `RunHyp`, for a stage-1 outcome of positive weight, a round
`3 ≤ l ≤ R`, arc systems with `ArcHyp`, every phase `c` and vertex `v`: summed over the non-demoted light parts `Z` of
round `l`, the number of phase-`c` arcs of `Z` with an end at `v` is at most `M_l − 1`.

### `MlTyStatement` [s5:lemParent] Step 5, comparison (refutation target)
TeX: "`M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6} ≤ ⌈λ_r^{1.6}⌉ = t_Y` … So `v` lies in at most `M_l − 1 < t_Y` pairs." Lean:
under `RunHyp`, for a light part `Y` of round `r` and `r + 2 ≤ l ≤ R`: `M_l ≤ λ_{l−2}^{1.6}`,
`λ_{l−2}^{1.6} ≤ λ_r^{1.6}`, `M_l ≤ t_Y`, and `M_l − 1 < t_Y`.

### `ConnectorCycleStatement` [s5:lemParent] Step 7 Claim (cycles)
TeX: quoted in the docstring. Lean: for a nonempty list of pairs (arc `a_j` in traversal order, connector `𝒞_j`),
each a path with `≥ 1` edge, `𝒞_j` from the last vertex of `a_j` to the first vertex of `a_{j+1}` (cyclically), arcs
pairwise vertex-disjoint, connector interiors pairwise disjoint and disjoint from all arcs, and no arc edge equal to a
connector edge: the vertex list `a_1 𝒞_1° a_2 𝒞_2° ⋯ a_k 𝒞_k°` has no repetition and `≥ 3` vertices, and its cyclic
edges are exactly the arc edges and the connector edges (as a multiset).

### `EtaHalvingStatement` [s5:lemParent] Step 9
TeX: "We claim that `η` is non-increasing on `[log₂D_*, ∞)` and that `η(2^{x/A}) ≤ η(x)/2` there." Lean: under Γ1,
`η` is antitone on `[log₂D_*, ∞)` and `η(2^{x/105}) ≤ η(x)/2` for every `x ≥ log₂D_*`.

### `ParentBadProbStatement` [s5:lemE1] (c), proof
TeX: "… for every sublabel `(l,c,σ)` of `Y` the set `V_{l,c,σ} := Zone_{Y,l,c,σ}` contains each vertex of `Y`
independently with probability `ρ_Y ≥ 1/(12L_Y^5)`, independently of the colouring of `Y`. (The zones of `Y` are
dependent across indices …; Lemma s3:lemCOL(c) allows this.) So Lemma s3:lemCOL(c), applied with this family, gives
`P(Y parent-bad) ≤ |Y|^{-2}/2`." Lean: under `RunHyp`, for every light part `Y`,
`P_{stage 1}(Y is parent-bad) ≤ |V(Y)|^{-2}/2`.

(The back-translations of the reused Specs `LemChildStatement`, `LemParent*`, `EqLY/EqZp`, `StagesHB`, `LemZones` are
in `work/p2s/s5.md`; `PVStatement` in `work/p2b/P4A.md`.)

## Math findings

None of class T1–T3. Re-derived at the statement level:
- Step 5 chain: occurrences of `v` in slot multisets ≤ arc ends at `v` (injective map occurrence → arc end, using
  distinct arc ends; the `k = 1` case) ≤ `pathEndCount` over `Z(v)` ≤ `|Z(v)| − 1 ≤ M_l − 1` (CapPrePart) and
  `M_l ≤ λ_{l−2}^{1.6}` (row 12 ⇔ Γ1 (c) at `μ = log₂λ_{l−2}`: `2A log₂(Aμ) ≤ 1.6μ`) `≤ λ_r^{1.6} ≤ t_Y`. Note: row 12
  needs `μ` large (at `μ = 2^8`, `(Aμ)^{2A} ≈ 2^{3089} > 2^{409.6} = λ^{1.6}`); Γ1 (c) supplies it for every
  `μ ≥ log₂log₂D_*`, so the input must carry Γ1, as `TowerBMStatement` does.
- Transition claim after capping (new transition `(v_q^+, v_p^-)`: two distinct arcs of one class, or two ends of
  one arc), cycle claim (length `≥ 3` needs arc edges ≠ connector edges, (F-c)).
- Step 9: `(ν−1)(M−1) + ν ≤ νM`; `56·2·2.74 = 306.88`; `J̄+1 ≤ log₂log₂M_l ≤ log₂(2A log₂(A log₂λ_{l−2}))` so
  `cap_l ≤ (14/102²) n η(λ_{l−2})`; η halving via `2A²x₁² log₂(2Ax₁) ≤ 4A³x₁³ ≤ (2^{14}Ax₁³)² ≤ 2^{2x₁}` and
  `d ln η/dx₁ = 1/(x₃x₂x₁ ln²2) − 2/x₁ < 0` (`x₂ ≥ 14`, `x₃ ≥ 11`); `2^{x/A} ≥ log₂D_*` for `x ≥ log₂D_*`.
- COL(c): T16* hypotheses (`ε_Y = 2^{-6} ∈ [2^{-7},1]`, `s = s_r/(16k)` = `ancS/(8k_lend)`, row 4 with
  `ρ^{-5} ≤ (12L^5)^5`, `ρN ≥ N/(12L^5) ≥ L^2`), conditioning on (a), union with row 7, plus `N^{-2}/4` for (a).
- lemChild hypothesis check: `PVSize` from `N ≥ P_l/2 ≥ λ_l^{103}/2 ≥ (log₂D_*)^{103}/2 ≥ N_0` (Γ3, `N0Cond`); own
  classes from COL(a) (non-demoted) and COL(g) on the support (edge-disjointness through `ownIdx`); `s' ≥
  2^{145}L^{41}` from row 8(d); (E1′) from (E1) at `l = r(Z)` (`E1_childData`).

## Non-vacuity (`EGTest/ProbeP4B.lean`)
- Euler (b): triangle with a loop, even degrees (loop counted twice), a closed trail using every edge once.
- Steps 2–3: two arcs whose quotient is a 2-cycle; the closed trail, its transitions `(1,2)`, `(3,0)` (claim holds),
  the witness `T = ∅`, `Ws = [W]` of the conclusion; the end count is attained at `v = 1`.
- Step 4: a four-arc trail visiting node `0` twice; with capacity 1, the split into two re-closed blocks satisfies
  the closure, arc-permutation and `vis ≤ 1` clauses.
- Step 7: the 4-cycle from arc `0 1 2` and connector `2 3 0` (hypotheses and conclusion); the degenerate 2-cycle
  violates the edge-disjointness hypothesis.
- T16*: all hypotheses hold together (degenerate `N = 1`).
- Γ1 (a)–(e) satisfiable (`exists_gamma1core`); each stub elaborates against its Spec.
- **Not cheap:** every run-level statement (needs Γ1, i.e. astronomically large runs), as for P4A.

## Open questions
1. The s5 unit must re-check the reconstructed `EG/Spec/Light/Setting.lean` (see the problem section).
2. Ownership of the stubs `EG/Proof/Light/{Setting,Stages,Zones}.lean` and `EG/Proof/Vortex/PV.lean`: placed at
   the natural paths of the future proofs (P4A pattern); the owners replace them.
3. Should the s3 COL unit export `COLaProbStatement` as part of its lemCOL Spec (blueprint E1-COL-A-BOUND)?

## Fix round (Specs, reviews `P4B.review-fidelity-first.md` and `P4B.review-vacuity-and-consumer-form.md`)

Both items concern the same duplication and were verified: `StructureVertexStatement` (s2 unit,
`EG/Spec/HB/Structure.lean`) states its first clause under `run.Valid` alone; `RunHyp` contains `run.Valid`
(last conjunct), `run.lightParts G = (run.parts G).filter isLight` with `run.parts G` the pairs `(l, a)`,
`l ∈ [1,R]`, `a ∈ run.prePartAddrs G l`, and `run.ancVerts G Y = run.partVerts G Y.1 Y.2`; two distinct light
parts with the same round have distinct addresses. So `StructureLightStatement` follows (checked in Lean).

1. (minor) "`StructureLight` as a declared-input sorry duplicates a source for propStructure (iv)": **fixed**.
   `EG.structureLight` (`EG/Proof/HB/StructureLight.lean`) is now a proof: `EG.mem_lightParts_iff` (membership in
   `lightParts`) and `EG.structureLight_of_structureVertex : StructureVertexStatement → StructureLightStatement`
   (0 sorry, axiom scan clean), applied to the new declared-input stub `EG.structureVertex :
   StructureVertexStatement` in `EG/Proof/HB/Structure.lean` (natural path of the s2 unit's future proof, P4A
   pattern; the s2 unit owns it and replaces the stub). One source for propStructure (iv); the number of
   declared-input stubs stays 9 (`structureLight` out, `structureVertex` in).
2. (minor) "two Specs for one clause": **fixed** in the same way. `StructureLightStatement` is kept (it is the
   consumer form used by `BundleEndCount`/`LemParent` Step 1 and 5, and `EG/Spec/HB/Structure.lean` imports it);
   it is no longer a declared input but a corollary; its module docstring says so. Deleting it would break the
   s2 unit's file (import), which P4B must not edit.

Reported, not edited (s2 unit's file): the module docstring of `EG/Spec/HB/Structure.lean` (line 45) still calls
`StructureLightStatement` "the declared input … (unit P4B)"; it is now derived from `StructureVertexStatement`.

Checks: `lake build EG.Proof.HB.StructureLight` ok; `scripts/check.sh` rc=0, 0 errors on
`EG/Proof/HB/StructureLight.lean`, `EGTest/ProbeP4B.lean` (now also `example : StructureVertexStatement :=
structureVertex`) and `EGTest/Spec_s2b.lean`; axiom scan of `EG.Proof.HB.StructureLight`: `sorryAx` only in
`EG.structureVertex` (stub) and, through it, `EG.structureLight`; `python3 -I scripts/lint.py`: 0 findings.

## Proof round 1 (complete: every probe node proved, 0 sorry outside declared-input stubs)

Status: all 15 probe nodes of the unit are proved. `lake build` of all modules below: ok; `scripts/check.sh` rc=0,
0 errors, 0 sorry warnings on every new file; `python3 -I scripts/lint.py`: 0 findings; `scripts/Axioms.lean --prefix EG`
over the 12 proof modules: 0 violations; `sorryAx` reaches the new theorems only through declared-input stubs (see
below). About 3800 new lines of Lean.

### Proved nodes (name — file — inputs used)

| Node | Lean name | File | Declared inputs / other units' results used |
|---|---|---|---|
| s5:lemParent Claim (transitions) | `EG.transitionClaim` | `EG/Proof/Light/ParentSteps.lean` | none |
| s5:lemParent Step 5 end count (refutation target) | `EG.transitionCount` | same | none |
| s5:lemParent Step 4 (visit capping) | `EG.visitCap` | same (Lib `EG/Lib/Light/VisitCap.lean`) | none |
| s5:lemParent Step 7 Claim (cycles) | `EG.connectorCycle` | `EG/Proof/Light/ConnectorCycle.lean` | none |
| s5:lemParent Steps 2–3 | `EG.arcClassEuler` | `EG/Proof/Light/ArcClassEuler.lean` (Lib `EG/Lib/Light/Euler.lean`) | `eulerMulti` ([s1:citEuler] (b); since P3 proved by unit P3-s1) |
| s5:lemParent Step 5 comparison (refutation target) | `EG.mlTy` | `EG/Proof/Light/ParentRun.lean` | `towerBM`, `towerA` |
| s5:lemParent Step 5 + (F-a,c,d) (refutation target) | `EG.bundleEndCount` | same | `capPrePart`, `structureVertex` (via `structureLight`) |
| s5:lemParent Step 9 (η) | `EG.etaHalving` | `EG/Proof/Light/EtaHalving.lean` | none (Γ1 (a), (b)) |
| s3:lemCOL (c) per index (T16*) | `EG.colcIndex` | `EG/Proof/Stage1/COLc.lean` | `t16s`; P4A's `colJVRow4` |
| s3:lemCOL (c) (refutation target) | `EG.colc` | same | `colaProb`; P4A's `colJVRow7` |
| s5:lemE1 (c) proof step | `EG.parentBadProb` | `EG/Proof/Light/ParentBadProb.lean` | `colc`, `lemZones` |
| s5:lemParent (disjointness over `(l,c)`) | `EG.lemParentAvailDisjoint` | `EG/Proof/Light/ParentAvail.lean` | P2J's `structureHY` (proved) |
| s5:lemChild | `EG.lemChild` | `EG/Proof/Light/Child.lean` | `pvLemma`, `stagesHB`; P4A's `colJVRow8` |
| s5:lemParent (ii) sum | `EG.lemParentSum` | `EG/Proof/Light/ParentSum.lean` | `towerBM`, `towerA`, `towerBLate`, `capPrePart`; `etaHalving` |
| s5:lemParent (lemma) | `EG.lemParent` | `EG/Proof/Light/Parent.lean` (engine `EG/Proof/Light/ParentEngine.lean`) | `eqLY`, `towerA`, `capPrePart`, `structureVertex`, `structureHY`; `bundleEndCount`, `mlTy`, `lemParentAvailDisjoint`, `arcClassEuler`, `visitCap`, `transitionClaim`, `transitionCount`, `connectorCycle` |

Proof-internal (not Spec nodes): `EG.PEngine.engine` + `EG.PEngine.Hyp` (Lemma parent side for one round and one phase,
abstract; Steps 2–9), `EG.parent_phase` (its instantiation for one phase), helper namespaces `EG.ChildAux`,
`EG.COLcAux`, `EG.EtaAux`, `EG.ParentSumAux`, `EG.ParentAux`, `EG.ArcEulerAux`, `EG.ConnCyc`.

### New files (all modules; none edits a locked or foreign file)
Lib: `EG/Lib/Light/Trail.lean`, `EG/Lib/Light/VisitCap.lean`, `EG/Lib/Light/Euler.lean`, `EG/Lib/Light/ChainAux.lean`,
`EG/Lib/Light/ParentData.lean`. Proof: `EG/Proof/Light/{ParentSteps,ConnectorCycle,ParentRun,EtaHalving,ParentBadProb,
ParentAvail,Child,ParentSum,ArcClassEuler,ParentEngine,Parent}.lean`, `EG/Proof/Stage1/COLc.lean`.
Root imports for the orchestrator (not edited by me): the 12 `EG.Proof.*` modules above (they import the Lib files).

### Declared inputs actually used (sorry stubs reached)
Own stubs of stage 1: `EG.t16s` ([s3:thmT16s]), `EG.colaProb` ([s3:lemCOL] (a) bound), `EG.pvLemma` ([s4:lemPV]),
`EG.eqLY` ([s5:eqLY]), `EG.stagesHB` ([s5:defStages] claims), `EG.lemZones` ([s5:lemZones]). Stubs of other units /
P3 in progress (reached transitively at the time of the scan): `towerA`, `towerBLate`, `towerBM` (now implemented by
the tower unit, itself depending on `EG.Todo.TowerBRest`), `colJVCount` (via P4A's rows), `capPrePart`/`structureVertex`
chains (other units). Not used any more: `EG.eulerTreeTJoin` (the `T`-join is proved directly, see below).

### Deviations from the TeX route (all proofs of the same statements; no statement changed)
- Step 3 `T`-join: instead of a spanning forest and [s1:citEuler] (a), `EG.MTrail.exists_even_complement` takes `T ⊆ A`
  of minimal size with `A \ T` even; if `|T| ≥ |Nd|`, a pigeonhole on the `2^{|T|}` subsets of `T` (their odd-degree sets
  in `Nd \ {v_0}`, `2^{|Nd|−1}` values; handshake at `v_0`) gives a nonempty even `C ⊆ T`, and `T \ C` is smaller.
- Step 4: the "transitions at `Y`" of a trail are counted as its oriented arcs ending at `Y` (`vis` = countP over
  `map oTgt`, `EG.countP_transitions_node`); the split is "rotate, cut into segments ending at `Y`, chunk".
- Step 9 η monotonicity: no derivative; `f(x_1)=log₂(2A log₂(Ax_1))/x_1^2` is compared at `a ≤ b = at` via
  `log₂ t ≤ (3/2)(t−1)`.
- COL(c): the conditioning on the lending data is `IsRSubset.map_pair_eq_prod` + `prob_compProd_le_of_forall`; T16* is
  applied to the law `rsubset V(Y) ρ` itself.

### Math findings of round 1
None of class T1–T3; no step failed. Checked in Lean along the refutation targets: Step 5 `M_l − 1 < t_Y`
(`mlTy`, needs `λ_{l−2} > 0` from validity), the end count (`transitionCount` + `bundleEndCount`, bound `deg_{H_0(Z)}(v)
≤ M_l − 1` by [s2:lemCap] (ii)), COL(c) with `t_Y` (row 4 with `ρ^{-5} ≤ (12L^5)^5`, `ρN ≥ L^2` from
`N ≥ λ^{103}/2`, `L ≤ 2λ`, `λ ≥ 2^{256}`), the routing multiplicity per `(Y, σ)` (count over the whole family ≤ arcs
with end `v` ≤ `t_{par v}`).

### Notes for the orchestrator
- `EG/Proof/Todo/LemParent.lean` (P3 stub, not mine) still has `by sorry`; it can now be `EG.lemParent`
  (`EG/Proof/Light/Parent.lean`). `EG/Proof/Todo/{ArcClassEuler,VisitCap}.lean` already point to my proofs.
- Name clash fixed on my side: P3-s1's `EG/Lib/Found/EulerMulti.lean` defines `EG.MTrail.IsClosedTrail.rotate`; my
  lemma in `EG/Lib/Light/VisitCap.lean` is now `IsClosedTrail.rotate_closed`.
