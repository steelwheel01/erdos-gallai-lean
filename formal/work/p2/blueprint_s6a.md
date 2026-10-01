# P2-U formalization blueprint: chunk s6a (s6 routing engine: GATE, clusters, MED, EQ-LPT, PAR, HCC-P, union of systems; designations; Theorem CONC)

Manuscript: `proofs/manuscript/s6.tex` lines 1-333 (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s6a.json` (same content, one object per label, same field names as `nodes_s1.json`). Line numbers refer to `s6.tex`. Lean names in `code` that already exist were checked against `formal/EG/**` (EG.FGraph, EG.degE, EG.IsPathIn, EG.IsThrough, EG.walkEdges, EG.Obj, EG.IsDecomp, EG.IsOrientation, EG.outDeg, EG.inDeg, EG.IsBalanced, EG.IsDirCycle, EG.IsAcyclic, EG.cycleArcs, EG.Spec.GateStatement, EG.Spec.GatePreciseStatement, EG.gate, EG.gate_precise, EG.gate_with_cycles, and the Lib lemmas of `EG/Lib/Found/Orient.lean`: isOrientation_walkArcs, IsOrientation.union, IsOrientation.outDeg_add_inDeg, exists_cancel_dirCycles, exists_balanced_sdiff_acyclic, isAcyclic_of_potential, IsAcyclic.exists_potential, isDecomp_map_cycle_of_arcs, sum_outDeg_eq_card, sum_inDeg_eq_card). Names from other blueprints: `EG.HB.Run`, `run.Std/Z0/E/graph/DupStar/guests/anc/classed/ancVerts`, `POf`, `MOf`, `tauOf` (s2a); `EG.Gamma1core`, `EG.logStar` (s1). All other names are proposals. The unlabelled log* facts `(s6:eqTowerHalf)`, `(s6:eqTowerEnd)` (s6.tex:262-295) are treated under `s6:thmCONC`.

> **Note (P2-D [chain], 2026-09-26).** The `lean_shape` snippets for `s6:defCluster`, `s6:lemMED`,
> `s6:lemHCCP` and `s6:lemHCCglob` below predate the Defs. The shipped Defs differ: `EG.Chain.exc`
> (not `Cluster.exc`), real-valued `beadCount`, `pad_k1` restricted to `⋃ LayP_j`, `path_edisj` as
> `List.Pairwise` edge-disjointness, extra `bb_disj`, the path clause split into
> `path_G`/`path_ends`/`path_T`, field names `T_disj`/`parityClean`/`pp_disj`/`pb_disj`, and no
> `Phi0` accessor (use `∃ Φ`). See "Differences from the blueprint `lean_shape`" in section
> "Fix round 1" of `formal/work/p2d/chain.md` before writing a Spec.

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s6:lemGATE` | lemma | done: existing Spec GateStatement + GatePreciseStatement, proved | 0 | 1 | note (GATE-DONE) |
| `s6:defCluster` | definition | Defs (EG/Defs/Chain/Cluster.lean) | 150 | 2 | note (CL-ADMISSIBLE-LOCAL) |
| `s6:lemMED` | lemma | Spec MedStatement + MedExcStatement; Lib exists_admissible | 350 | 2 | note (MED-ONLY-EXISTENCE-USED) |
| `s6:lemEQLPT` | lemma | Defs IsGreedyLPT + Spec EqLptStatement | 250 | 2 | note (EQ-GREEDY-RELATION) |
| `s6:lemPAR` | lemma | Defs (edge-set components) + Spec ParStatement | 700 | 3 | risk (PAR-GRAPH-INFRA) |
| `s6:lemHCCP` | lemma | Defs HccpData/Valid + Spec HccpStatement | 1100 | 4 | risk (HCCP-FLAGGED-REDERIVED) |
| `s6:lemHCCglob` | lemma | Lib (concatenation) + Spec HccGlobStatement (input-level disjointness) | 120 | 1 | risk (GLOB-OUTPUT-LEVEL-HYP) |
| `s6:defDesign` | definition | Defs (EG/Defs/Chain/Design.lean) on the s2 run model | 300 | 3 | risk (DES-RUN-MODEL) |
| `s6:thmCONC` | theorem | Spec ConcI/ConcII/ConcIII; Lib log* + tower facts | 750 | 3 | risk (CONC-IMPLICIT-HYPS) |

Estimated new Lean for this chunk: **~3720 lines** (GATE is done: 0 new lines; the orientation Lib of P1b is reused). No **blocker** in this chunk: I re-derived every proof (GATE, MED (a),(b), EQ-LPT, PAR, all four steps of HCC-P including the k = 1 and k = 2 cases, the union lemma, CONC (i)-(iii) and the tower facts (eqTowerHalf)/(eqTowerEnd) with all numerical constants) and found no mathematical error. The risks are (1) the size of HCC-P and of the graph infrastructure for PAR (components/bridges/spanning trees of edge sets); (2) cross-chunk dependencies: `s6:defDesign` and `s6:thmCONC` sit on the s2 run model (not yet locked; s2a blocker HB-M-INTEGER) and must use the same hypothesis bundle as the s2 Specs; (3) one quantifier issue (HCCglob's output-level hypothesis), resolved by an input-level statement; (4) the log* real-analysis library for the tower facts. Consumers (JS-LC) use only existence from MED and EQ-LPT, and only the count/cycle part of HCC-P.

## 2. Cross-cutting decisions proposed for the integrator

- **Module layout (Chain layer, PLAN §3).** Protected Defs: `EG/Defs/Chain/Cluster.lean` (Cluster, beadCount, ParityClean, IsAdmissible, exc, load, medOrient), `EG/Defs/Chain/EqLpt.lean` (IsGreedyLPT, layerLoad), `EG/Defs/Components.lean` (edgeVerts, edgeGraph, edgeComps, compEdges, IsNonBridge, IsPendant; shared with defDesign 'giant', s5:lemParent forests), `EG/Defs/Chain/HCCP.lean` (HccpData, Valid and derived defs), `EG/Defs/Chain/Design.lean` (IsDesignation and the class data). Specs in `EG/Spec/Chain/{MED,EqLpt,PAR,HCCP,CONC}.lean` (`Gate.lean` exists). Lib: `EG/Lib/Found/LogStar.lean` (log* API, tower facts), `EG/Lib/Chain/Conc.lean` (shared τ- and d*-sums for CONC and CONC-L), IsDecomp concatenation lemma.
- **Clusters are G-free and indexed.** A `Cluster` carries its own loop-freeness and end-membership; `beads ⊆ G.edges` is a hypothesis of HCC-P. Layers are an index family `Fin N → Cluster V` with a layer map `Fin N → Fin k`, and HCC-P (D) is stated for distinct indices. Admissibility is hub-local (never `IsBalanced`).
- **HCC-P uniform in k.** One Spec with `succ j := (j+1) mod k` covers k = 1 (pad ≡ 0) exactly; the path families are lists (multiplicities), edge-disjointness is `Nodup` of concatenated `walkEdges`, first/last-vertex counts are `filter`-lengths. The length conclusion max(3,k) is unused downstream and may be split off.
- **HCCglob with input-level disjointness** (GLOB-OUTPUT-LEVEL-HYP): cross-system disjointness of beads ∪ path edges; this is exactly what JS-LC Step 7 verifies and it implies the manuscript's output-level condition.
- **Faithful Specs, existence corollaries for consumers.** MED(a) is stated for the concrete `medOrient`, EQ-LPT for every greedy placement (+ existence), PAR for every admissible choice (+ existence of an admissible edge); consumers (JS-LC, J+) should depend on Lib corollaries `Cluster.exists_admissible`, `exists_greedy`, so that their proofs do not unfold the median/greedy shape.
- **Designations.** `δ : ℕ → V → ℕ × List Bool` (round-indexed; ancestors = (round, pre-part address), the s2a identity convention), constrained only on classed ports; δ is a parameter fixed before any FinDist. Class data count ports (equivalent to counting edges at fixed h). The run model must give Std_l = ∅ and E_l = ∅ for l > R.
- **CONC hypothesis bundle.** CONC's Specs take the same hypotheses as the s2 Specs they apply (propOrigin, propOV, lemTower, lemLacunary): at least `Gamma1core D ∧ run.Valid G D`; add n ≥ N0 / d_1 ≥ D* only if those Specs have them. Decide once in P2-D; CONC-L, MIX-C and s7 inherit it.
- **Tower facts and log*.** Add `EG.logStar` (s1 blueprint CONV-LOGSTAR) with `logStar_le_iff_le_tower`, `logStar_eq_succ_logStar_log`, `logStar_le_one_add_log` (provided in `EG.Lib.Found.Log` as `logStar_le_iff_le_tower`, `logStar_of_one_lt`, `logStar_le_one_add_logb`); prove (eqTowerHalf)/(eqTowerEnd) once for the three functions a, b, c (c is used only by CONC-L) and reuse in CONC-L.
- **Dependency graph corrections (usesgen/msreport).** Undeclared uses found in proofs: s6:lemGATE uses s1:convGraphs; s6:lemPAR uses s1:convGraphs; s6:lemHCCP uses s1:defObject, s1:convGraphs; s6:lemHCCglob uses s1:defObject (and actually needs IsDecomp concatenation rather than s1:factAdd(b)); s6:defDesign uses s2:propStructure(iv); s6:thmCONC uses s2:defAncestors, s1:convGraphs, (s2:propStructure(iii)). Misattributed: the extractor assigns s1:condGamma and s2:lemTower to s6:defDesign — they belong to the log* facts, i.e. to s6:thmCONC and s6:thmCONCL.
- **Probe order (s1:remStatus(iv)(a)).** The engine lemmas themselves re-derive cleanly; the hot spot is their USE in s6:lemJSLC (joint routing multiplicities, (D) for systems, EQ-LPT with empty S_0). A P2b probe should formalize HCC-P and then the JS-LC Step 6/7 hypothesis checks early.

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| risk | `s6:lemPAR` | PAR-GRAPH-INFRA | Components, bridges, pendant edges and spanning trees of an EDGE SET are not in EG/Defs or EG/Lib. They must be built on FGraph.toSimpleGraph + Mathlib (ConnectedComponent, IsBridge, Connected.exists_isTree_le or an own spanning-tree construction), with transport lemmas between compEdges/degE and Mathlib degree/edge sets. The T-join lemma (s1:citEuler(a)) is planned as a Lib theorem for multigraph forests (s1 blueprint EUL-MULTI-USE); PAR needs the simple-graph instance on each component. Estimated ~400 lines of infrastructure before PAR proper; shared with s6:defDesign ('giant' components) and s5:lemParent. |
| risk | `s6:lemHCCP` | HCCP-FLAGGED-REDERIVED | s1:remStatus(iv)(a) names the routing engine (HCC-P, PAR, MED, EQ-LPT as used in JS-LC) as the single most likely error site. I re-derived HCC-P completely: Step 0 (\|P_j\| = Σ_{LayP_j} dm⁻ = Φ_j via MED(b), and = Σ_{LayP_{j+1}} dm⁺ = Φ_{j+1}); Step 1 (ports are sources/sinks of D_j, including k = 2 where LayP_{j+1} = LayP_{j−1} ≠ LayP_j, and k = 1 via X^out ∩ X^in = ∅; cancelled cycles lie in T_j, so returned edges ⊆ E(G[T_j])); Step 2 (balance at hubs, T-vertices and ports: exc + dm⁻ − dm⁺ = 0); Step 3 (Ψ ∈ (3j,3j+1) on layer j and (3j+1,3j+2) on T_j; every non-W arc increases Ψ, including direct port→port arcs of length-1 paths; \|W\| = \|P_{k−1}\| because the last arcs are distinct, end at ports, and are never cancelled); Step 4 (GATE; the block-crossing count gives length ≥ k). No error found in HCC-P itself. The residual risk lies in JS-LC's verification of (D) and (JC-P) (joint routing multiplicity ≤ 2M_l − 2 ≤ t, pair ends distinct, T-avoidance), which is outside this chunk. |
| risk | `s6:lemHCCP` | HCCP-EFFORT | Largest Lean item of the chunk: orient each path (EG.isOrientation_walkArcs), union of arc sets under edge-disjointness (IsOrientation.union), degree bookkeeping per vertex class (hub / port of layer j / T_j vertex) with in/out counts of D_j equal to first/last-vertex counts of the list P_j, cancellation (EG.exists_cancel_dirCycles), a piecewise real potential Ψ built from per-cluster topological numberings and per-T_j numberings, the count \|W\| = \|P_{k−1}\|, GATE, and the block-crossing length argument on a directed cycle. The Lib from P1b covers the orientation primitives; the counting of first/last vertices of a list of paths vs out/in-degrees of the union of their arcs is new (~250 lines). |
| risk | `s6:lemHCCglob` | GLOB-OUTPUT-LEVEL-HYP | Quantifier issue: part (2) assumes that 'the edge sets they decompose (their beads together with their sets F_j) are pairwise disjoint', but the F_j are OUTPUTS of HCC-P (existentially produced), so the hypothesis refers to objects that do not exist before the lemma is applied. Decision: state (2) with INPUT-level disjointness (beads and all path edges of distinct systems pairwise disjoint), which is exactly what JS-LC Step 7 verifies (bead sets disjoint by the joint-routing claim (b); path edges disjoint within (Y,l,j) by joint routing, across j by distinct classes, across Y by E(H_Y) ⊆ E_{r(Y)}(Y); paths vs beads by s2:propStructure(iii)) and implies the output-level condition because F_j ⊆ E(P_j). This is not a weakening for any consumer. |
| risk | `s6:defDesign` | DES-RUN-MODEL | Every quantity is defined on top of the s2 data model (pre-parts by (round, address), Std, D_l, anc, classed ports, E_l(Z), G_l, Dup*, guests, P, M). Design.lean cannot be written or locked before EG/Defs/HB/Run.lean (s2a: HB-DATAMODEL, HB-ADDRESS-IDENTITY, and the BLOCKER HB-M-INTEGER, which enters here through γ_l = ⌊P_{l−2}/M_l⌋ — harmless either way with Nat.floor, but the M_l type must be fixed first). The ancestor type (ℕ × List Bool, with light/standalone derived) is a cross-chunk type shared with s3:defCOL (classes per ancestor), s5, s6:defLending and s7 (H_{Y(u)}); it must be decided once. |
| risk | `s6:thmCONC` | CONC-IMPLICIT-HYPS | 'For every valid HB*^{τ+} run' hides hypotheses: the proof uses s2:lemTower(a),(c) (stated for valid runs with d_1 ≥ D*, under (Γ1),(Γ2)), s2:propOV(K1),(K3) and s2:propOrigin (whose proofs use s2:propStructure, stated for n ≥ N0 and d_1 ≥ D*), and the tower facts use (Γ1)(a),(b). The Lean Specs must carry exactly the hypothesis bundle of those s2 Specs (at least Gamma1core D ∧ run.Valid G D); if the s2 blueprint's Specs assume n ≥ N0, so must CONC, and then s6:thmCONCL/s6:thmMIXC/s7 must supply it. Mismatch across chunks would make CONC unprovable or unusable; decide the bundle once (P2-D). (When d_1 < D*, R = 0 and (ii),(iii) are trivial.) |
| risk | `s6:thmCONC` | CONC-TOWER-FACTS | (s6:eqTowerHalf) and (s6:eqTowerEnd) are proved in an unlabelled proof block before the theorem and need real analysis not yet in EG: a log* definition on ℝ with log* x ≤ k ↔ x ≤ T_k and log* x = 1 + log*(log x) for x > 1; log* x ≤ 1 + log x for x ≥ 1 (case x ≤ 4 by inspection, then induction); monotonicity of t ↦ (2 log t + 6)/t, (7 + 2 log t)/t, (2 log t + 5)/t^{1/2} on t ≥ 4; and (Γ1)(a),(b) at μ = log λ_{r+1}, log log D*, log D*. I re-derived every inequality (2^{y/(2A)} ≥ 2^{4+2v} = 16y², y(2y/A+6) ≤ 8y² ≤ 2^{y/A}, 2y^{1/2}(2y/A+5) ≤ 14y^{3/2} ≤ 2^{y/(2A)}, A(7+2 log y)/y ≤ 1/(2 log y) from y ≥ 2Av(7+2v), both cases of (eqTowerEnd) including t(2t+6) ≤ 2^t and t(2t+5)² ≤ 2^t, k* ≥ 6 from log log D* ≥ 2^8 ⇒ D* > T_5): all correct. The effort is the Lean real-analysis bookkeeping (~300 lines), shared with s6:thmCONCL. |
| note | `s6:lemGATE` | GATE-DONE | Statement and proof exist and were approved twice; nothing to do except lock/tag. The two conclusions are both needed: HCC-P Step 4 uses the precise form (each cycle is a directed cycle of F⃗ containing a W-arc) for its length claim. |
| note | `s6:lemGATE` | GATE-G-ONLY-FOR-CYCLES-OF-G | The hypothesis F ⊆ E(G) only serves 'cycles of G' (edges in G.edges) and looplessness; IsOrientation already forces F loopless and excludes antiparallel arcs (EG.IsOrientation.not_mem_swap), which is the formal content of 'G is simple, so no 2-cycles'. |
| note | `s6:lemGATE` | GATE-BALANCE-GLOBAL | IsBalanced quantifies over all vertices; this is right for GATE (the manuscript says 'at every vertex'). It must NOT be reused for cluster admissibility (balance at hubs only; CONVENTIONS). |
| note | `s6:defCluster` | CL-ADMISSIBLE-LOCAL | Admissibility requires balance at HUBS only; ports are unbalanced by design. Use pointwise outDeg/inDeg on K.hubs, never EG.IsBalanced (CONVENTIONS, 'Orientations'). |
| note | `s6:defCluster` | CL-ORIENT-IS-DATA | exc(u) and Φ(K) depend on the orientation, which the notation suppresses ('Φ(K)', 'exc(u)'). In Lean they take O as an argument, and HCC-P's 'each cluster with a fixed admissible orientation' is data (O : Fin N → Finset (V × V)). A port's exc is taken in the unique cluster containing it (HCC-P (D)). |
| note | `s6:defCluster` | CL-BEADCOUNT-HALF | b(K) contains deg/2, a half-integer for non-parity-clean hubs. It is only ever used for parity-clean clusters (MED(b), JS-LC Step 4 where b(K_C) = \|E(C)\|/2). Define with ℕ division and prove exactness under ParityClean (or under admissibility, which forces even hub degrees); a ℚ-valued definition is an alternative. |
| note | `s6:defCluster` | CL-G-FREE | The manuscript's B_K ⊆ E(G[A ∪ U]) mentions the input graph. Recommended: a G-free Cluster (loopless beads with ends in V(K)) plus an explicit hypothesis K.beads ⊆ G.edges in HCC-P. All consumer clusters (JS-LC components and cherries) have beads in E_l(Z) ⊆ E(G). |
| note | `s6:defCluster` | CL-MED-TOTAL | MED(≺) is defined in the manuscript only for parity-clean clusters ('u_1 ≺ … ≺ u_{2d}'). The Lean medOrient is total (median count rule 2·#{w ≼ u} ≤ deg); its properties are claimed only under ParityClean and rk injective on ports (s6:lemMED). |
| note | `s6:defCluster` | CL-IDENTITY | Layers are 'families of clusters'. Equal triples may occur (e.g. empty clusters); index clusters (Fin N → Cluster V) and state HCC-P (D) for distinct INDICES, not as a Finset of clusters. |
| note | `s6:lemMED` | MED-ONLY-EXISTENCE-USED | No consumer uses the median structure: JS-LC Step 4 only needs 'some admissible orientation exists' and then (b) (valid for every admissible orientation). Keep the faithful Spec on medOrient (MedStatement), and derive the Lib corollary exists_admissible for consumers; the consumer proofs must not depend on medOrient's shape. |
| note | `s6:lemMED` | MED-MEDIAN-COUNT | The Lean proof of 'exactly d in-arcs at a hub of degree 2d' is a counting argument on the rank-sorted neighbour list (#{w ∈ N(h) : rk w ≤ rk u} ranges over 1..2d bijectively); needs rk injective on ports and N_B(h) ⊆ ports. Moderate list/Finset bookkeeping (~150 lines). |
| note | `s6:lemMED` | MED-POT-UNUSED | The potential of (a) is used only to derive acyclicity; HCC-P Step 3 uses a topological numbering of the given admissible orientation instead (EG.IsAcyclic.exists_potential exists). Keep (a) as stated; no consumer needs the (0,1) range. |
| note | `s6:lemMED` | MED-INT-PARITY | exc is an integer; state parity as Even (exc − deg) in ℤ and \|exc\| via natAbs; Φ(K) uses Int.toNat of exc. Σ exc = 0 is an ℤ-sum over U_K (hubs contribute 0 by balance; the handshake lemmas EG.sum_outDeg_eq_card / sum_inDeg_eq_card exist). |
| note | `s6:lemMED` | MED-B-NEEDS-NO-HUBHUB | Φ ≤ b uses that every arc with tail at a port ends at a hub or at a port, and that every in-arc at a hub has its tail at a port; both need the cluster axiom 'no bead has both ends in A_K'. Also needs IsOrientation.outDeg_add_inDeg (exists) for \|exc\| ≤ deg and the parity claim. |
| note | `s6:lemEQLPT` | EQ-GREEDY-RELATION | 'Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists' is a nondeterministic rule (ties arbitrary). Formalize as a relation IsGreedyLPT and quantify over ALL greedy placements (faithful 'then'); add the existence conjunct (0), which the manuscript asserts in the proof ('So the rule is consistent') and which JS-LC needs to 'layer them by that lemma'. |
| note | `s6:lemEQLPT` | EQ-REAL-VS-NAT | Loads are reals ≥ 0 in the statement but natural numbers at every use (Φ(K_C) and unit cherry loads). State over ℝ (faithful) and cast at the use, or state for a LinearOrderedAddCommMonoid; do not state over ℕ only (that would be a weakening). |
| note | `s6:lemEQLPT` | EQ-INDEX-SHIFT | Items 1..m and layers 1..k become Fin m / Fin k (0-based); Φ_1 is Φ ⟨0,_⟩ (CONVENTIONS, [k] vs Fin k). |
| note | `s6:lemEQLPT` | EQ-USE-EMPTY-S0 | Cross-chunk (s6:lemJSLC Step 4): k_0 := min(K, max(1, ⌊ΣΦ/(2Φ_max)⌋)) divides by Φ_max, and EQ-LPT needs 1 ≤ k ≤ m. If R_Y has no non-giant component, S_0(Y,l) has m = 0 clusters and ΣΦ = Φ_max = 0; the text says 'S_0(Y,l) (if non-empty)' only in Step 6. The JS-LC Lean proof must case-split on S_0 = ∅ (trivial, but the literal formula is ill-defined there). Also 'k_0 ≤ number of clusters' needs Φ(K_C) ≥ 1 for every cluster (proved in JS-LC). |
| note | `s6:lemPAR` | PAR-SIDES-DISJOINT | The Spec must assume Disjoint V_a V_b (implicit in 'bipartite graph with sides V_a, V_b'); without it the lemma is false (V_a = V_b = {x,y,z}, E = {xy, yz}: one even component, J' = ∅, but no partition makes all degrees even in both S_a and S_b). In JS-LC the sides are class-a and class-b ports of Qs_Z, disjoint because each port has one class and a ≠ b. |
| note | `s6:lemPAR` | PAR-FORALL-CHOICE | 'for EVERY such choice' is load-bearing for s6:lemJplus ('this holds for every choice'); state the conclusion ∀ J' with IsParChoice, and the existence of an admissible edge per odd component as a separate conjunct (0). The J-interface must not depend on which admissible edge was chosen. |
| note | `s6:lemPAR` | PAR-DIRECT-PROOF-OPTION | Alternative that avoids spanning trees: prove 'a connected graph has a spanning subgraph with prescribed degree parities p iff Σ p is even' by induction on edges (or via paths between T-pairs, symmetric difference). Either route is acceptable; the Spec does not change. |
| note | `s6:lemPAR` | PAR-COUNT-USE | The bounds \|J'\| ≤ #odd ≤ \|V(E_ab)\|/2 feed only (eqJbound) of JS-LC, which the manuscript says is not used later; the parity partition is the load-bearing part. Keep the bounds (faithful; cheap). |
| note | `s6:lemPAR` | PAR-COMPONENT-ISOLATED | Mathlib components include singleton components of vertices outside edgeVerts E; edgeComps is taken over edgeVerts E only, and odd components automatically have ≥ 1 edge, hence ≥ 2 vertices of V(E_ab) (the counting step). |
| note | `s6:lemHCCP` | HCCP-K1-UNIFORM | The k = 1 special reading (paths from X^out to X^in, u ∈ X^out starts exactly exc(u)⁻ paths) is equivalent to the uniform reading with succ 0 = 0 and pad ≡ 0 (a first vertex u must have dm⁻(u) = exc(u)⁻ ≥ 1, i.e. u ∈ X^out; similarly for last vertices). State the Spec uniformly; the proof still needs X^out ∩ X^in = ∅ (automatic: exc(u) cannot be both < 0 and > 0). |
| note | `s6:lemHCCP` | HCCP-INDEXED-CLUSTERS | (D) is 'pairwise disjoint over all clusters of all layers'. With a Finset of clusters, a cluster occurring in two layers would be one element; index clusters by Fin N with a layer map and require disjointness for distinct indices (plus the cluster's own A ∩ U = ∅). pexc then reads the unique cluster containing u (by (D) the sum has ≤ 1 non-zero term). |
| note | `s6:lemHCCP` | HCCP-PATH-FAMILY-LIST | P_j is a family, not a set: use List (List V). 'Pairwise edge-disjoint' = Nodup of the concatenated walkEdges (also gives each path's own edges distinct, automatic for paths). Paths have ≥ 1 edge automatically (first and last vertices lie in disjoint sets), so the one-vertex-path caveat of EG.IsPathIn (CONVENTIONS) is harmless here, but keep the head/last membership conjuncts explicit. |
| note | `s6:lemHCCP` | HCCP-JCP-AS-DATA | (JC-P) says 'there is a family P_j'; conclusion (ii) refers to E(P_j). In the Spec the families are data of HccpData (universally quantified), not an existential hypothesis; this is the only faithful reading since F_j ⊆ E(P_j). |
| note | `s6:lemHCCP` | HCCP-P-REDUNDANT | (P) parity-clean follows from admissibility (hub balance forces even hub degree). Keep (P) as a field for fidelity; the proof never needs it separately. |
| note | `s6:lemHCCP` | HCCP-LENGTH-UNUSED | The conclusion 'each cycle has length ≥ max(3,k)' is used by no consumer (JS-LC, J+, MIX-C need only the count and that all objects are cycles). It costs ~150 lines (block-crossing argument). Keep it (faithful), but it may be split into a separate HccpLengthStatement so that consumers depend only on the count part. |
| note | `s6:lemHCCP` | HCCP-PAD-DOMAIN | pad is defined on ports only (values in ℤ_{≥0}); in Lean pad : V → ℕ with junk values off ports. The k = 1 condition 'pad ≡ 0' becomes ∀ u, pad u = 0 (the consumer passes pad := 0 when k = 1). |
| note | `s6:lemHCCP` | HCCP-SUCC-FIN | Indices mod k on Fin k: define succ j := ⟨(j+1) % k, _⟩ (or finRotate); JS-LC's 'junction j − 1' is the predecessor under the same map. For k = 2 the two neighbours coincide and the proof relies on succ j ≠ j (true for k ≥ 2). |
| note | `s6:lemHCCglob` | GLOB-NO-VERTEX-DISJ | Correct and important: HCC-P's proof uses (D) only through the potential Ψ of its own system; the union needs only edge-disjointness. The Spec must NOT add cross-system vertex conditions (JS-LC: vertices of systems of other pairs (Y',l) may lie in T_j(Y,l) and be interior path vertices). |
| note | `s6:lemHCCglob` | GLOB-FACTADD-MISCITE | The proof cites s1:factAdd(b) (a statement about f = the MINIMUM number of objects); what is needed and used is the concatenation of given decompositions (exact count Σ a_i). The Lean proof uses an IsDecomp-concatenation Lib lemma, not factAdd. |
| note | `s6:defDesign` | DES-CLASS-DEPENDS-ON-ROUND | The notation Y(u), Z_u, r(u) suppresses the round l; a vertex may be a classed port in several rounds with different classes. δ must be indexed by l (δ : ℕ → V → Anc), and every consumer must pass l. |
| note | `s6:defDesign` | DES-DELTA-TOTAL | δ is a total function in Lean; values off the classed ports of round l are junk and unconstrained. All definitions filter by classed ports first. Existence of a designation (s7:thmMainProof) follows from anc_l(u) ≠ ∅ for classed u (definition of F_Z) by Classical.choice; 'a fixed rule' is not needed. |
| note | `s6:defDesign` | DES-DETERMINISTIC | 'δ is any deterministic function of the run': in Lean δ is a parameter quantified BEFORE the stage-1 FinDist; consumers (s6:lemLost(i): 'the designation is deterministic, so Y is fixed'; s7:lemEXprime: weights ω_l = c^agg are independent of pool labels) then hold automatically. A formalization that lets δ depend on stage-1 data would break these. |
| note | `s6:defDesign` | DES-UNIQUE-Z | 'Every classed port lies in Q_Z for exactly one Z' is a lemma (from U_Z = Z^0 \ D_l and D_l = {v in ≥ 2 pre-parts}; s2:propStructure(iv)), not definitional. Avoid a function Z_u in Defs: use ∃ a ∈ Std, u ∈ classed a ∧ … (as in alphaY), and prove uniqueness in Lib. |
| note | `s6:defDesign` | DES-COUNT-EDGES-VS-PORTS | d_{Y,l}(h) counts EDGES hu; the Lean definition counts ports u. At fixed h, u ↦ s(h,u) is injective and each edge lies in at most one E_l(Z) (R5 assigns each edge once), so the two agree; document in the docstring and prove the equivalence lemma (needed by s7:lemEXprime's double counting Σ_h c^agg ≤ Σ_Z Σ_{u ∈ Q_Z} deg_{E_l(Z)}(u)). |
| note | `s6:defDesign` | DES-BEAD-CLAUSE-VACUOUS | In Bead_{Y,l} the clause 'h ∉ Q_Z or Y(h) ≠ Y' is always true: if h ∈ Q_Z with Y(h) = Y then both ends lie in V(Y) and hu ∈ E(G_l) with l > r(Y), contradicting s2:lemEL. Keep the literal clause (faithful); JS-LC Step 3 does not rely on it. |
| note | `s6:defDesign` | DES-L-RANGE | The quantities must vanish for l ≤ 2 (anc_l = ∅) and for l > R (the data model must give Std_l = ∅ and E_l(·) = ∅ beyond the last round; s2a's Run defines rounds by list index, so out-of-range rounds need an explicit convention). s6:thmCONC(ii) 'for every l' and the sums in (iii) depend on this. |
| note | `s6:defDesign` | DES-GAMMA-INDEX | γ_l uses P_{l−2}: for l ≥ 3 the ℕ-subtraction l − 2 ≥ 1 is fine; for l ≤ 2 the value is junk and unused. P and M are functions of d_{l−2}, d_l (s2a POf, MOf). |
| note | `s6:defDesign` | DES-ALPHA-LIGHT-ONLY | α_{Y,l} is defined for light Y only; the Lean definition is total (for standalone Y the guest set used is the pre-part's S_Y, which is meaningless but unused). Consumers (s6:thmCONCL) must only read it for light Y. |
| note | `s6:defDesign` | DES-CLASS-COUNTS-USE | c^agg_{h,l} is load-bearing downstream (s7:lemPay (a2), s7:lemEXprime); c_x(Z) and c_pp(u) enter only (eqJbound), which the manuscript says is not used later. c^agg ranges over ancestors of rounds ≤ l − 2 (a finite set); cAgg needs a Finset of all ancestors up to a round (run.ancestorsUpTo). |
| note | `s6:defDesign` | DES-EXTRACTOR-MISATTRIBUTION | ms_deps_v6.json lists s1:condGamma and s2:lemTower as undeclared references of this definition; they come from the log* facts (s6.tex:262-295), which usesgen attaches to the preceding environment. Attach them to s6:thmCONC / s6:thmCONCL instead (they are proof ingredients of both). |
| note | `s6:thmCONC` | CONC-ROUND-RANGE | (i) quantifies over l ≥ r + 1 but G_l exists only for l ≤ R + 1 (the procedure stops at R + 1); restrict to l ≤ R + 1 or define G_l for l > R + 1 in the data model (e.g. constant). (ii) 'for every l' and the sum in (iii) rely on m_{Y,l} = 0 for l ≤ r + 1 (anc_l requires r ≤ l − 2), for l ≤ 2, and for l > R (needs Std_l = ∅ beyond R in the data model; see DES-L-RANGE). |
| note | `s6:thmCONC` | CONC-SUM-INDEX | 'Σ over pairs (Y,l) with Y standalone' must be a finite sum over an explicit index set: Σ_{r ∈ [1,R]} Σ_{a ∈ Std r} Σ_{l ∈ [1,R]} (equivalently [max(3,r+2), R]). Ancestors are addresses, so distinct pre-parts with equal vertex sets are counted separately (as the manuscript intends: 'distinct ancestors of round r have distinct pre-parts'). |
| note | `s6:thmCONC` | CONC-SHARED-COMPUTATION | s6:thmCONCL(iv) reuses 'the computation in the proof of CONC(iii) verbatim' for ALL ancestors (light and standalone; the number of ancestors of round r is ≤ 1.37 n/P_r by (K1)) and the d*-injectivity argument. Formalize the two sums as Lib lemmas over an arbitrary per-round family of ancestors with a cardinality bound, and derive CONC(iii) and CONC-L(iv) from them; do not prove the chain twice. |
| note | `s6:thmCONC` | CONC-IV-META | (iv) is a meta-statement ('nothing used how δ chooses'); in Lean it is automatic because (ii),(iii) quantify over every δ with IsDesignation. No separate statement; mention in the docstring. |
| note | `s6:thmCONC` | CONC-NAT-SUB | τ_r − 1 is ℕ-subtraction; τ_r = ⌈128 s_r log² M_r⌉ ≥ 1, so no truncation occurs (keep a lemma 1 ≤ tauOf d). The real inequality (iii) needs casts; the constants 1.37·16/3 < 8, 2k+4 ≤ 8k/3 and 2k+3 ≤ 2.5k (k ≥ 6), 32·2.5 = 80 ≤ 100 are norm_num facts. |
| note | `s6:thmCONC` | CONC-LOG-JUNK | log log D* and log* D* are real expressions with Real.logb junk values for arguments ≤ 1; (Γ1) gives log log D* ≥ 2^8, so all logs are positive. The tower facts must be stated for d ≥ D* only (they are false for small d). |
| note | `s6:thmCONC` | CONC-II-SIMPLE | (ii) splits the edges counted in d_{Y,l}(h) into u ∉ Dup*_r (≤ τ_r − 1 by (i), since E_l(Z) ⊆ E(G_l) and u ∈ V(Y) = Y^0) and u ∈ Dup*_r (distinct ports u, counted by d*_{Y,l}); with the port-counting definition of classDeg (DES-COUNT-EDGES-VS-PORTS) this is a Finset.card_union_le split, no simplicity argument needed. |

## 4. Nodes

### `s6:lemGATE` — lemma: Lemma GATE (forward direction) (s6.tex:16)

- **Manuscript referee status:** x2; +RA
- **Formalization:** DONE: existing Spec EG.Spec.GateStatement and EG.Spec.GatePreciseStatement (EG/Spec/Chain/Gate.lean), proved with 0 sorry (EG.gate, EG.gate_precise, and EG.gate_with_cycles which returns both conclusions at once, EG/Proof/Chain/Gate.lean); two reviews APPROVE (formal/work/p1b/gate.review1.md, gate.review2.md)

**Statement (precise restatement).** Let G be the input graph (finite, simple). Let F ⊆ E(G) and let A (= F⃗) be an orientation of F: every edge of F receives exactly one direction, so A is a set of arcs (u,v), u ≠ v, whose underlying edges uv are exactly the edges of F, each once. Assume d⁺_A(v) = d⁻_A(v) for EVERY vertex v. Let W ⊆ A be a set of arcs such that A \ W contains no directed cycle (no cyclic vertex sequence c_0 … c_{p-1}, p ≥ 1, pairwise distinct, with all arcs c_i → c_{i+1 mod p} in A \ W). THEN there exist p ≤ |W| directed cycles C_1, …, C_p of A, each with pairwise distinct vertices and length ≥ 3, pairwise arc-disjoint, whose arc sets together are exactly A, each containing at least one arc of W. Consequently the underlying cycles of G form a decomposition (s1:defObject) of F into at most |W| cycles of G (no single edges).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| orientation of an edge set; arcs; d⁺, d⁻; balanced | IsOrientation F A (loop-free arcs, underlying edge in F, each edge exactly one arc); outDeg/inDeg; IsBalanced A := ∀ v, outDeg A v = inDeg A v | s6 preamble (s6.tex:12) | yes: EG.IsOrientation, EG.outDeg, EG.inDeg, EG.IsBalanced (EG/Defs/Orient.lean) |
| directed cycle; acyclic; A − W | IsDirCycle A c (non-empty, Nodup, all cycleArcs c ∈ A); IsAcyclic A := ∀ c, ¬ IsDirCycle A c; A − W = A \ W | s6 preamble | yes: EG.IsDirCycle, EG.IsAcyclic, EG.cycleArcs |
| object, decomposition | cycle (Nodup vertex list, ≥ 3 vertices) or single edge; edge lists partition the set | s1:defObject | yes: EG.Obj, EG.Obj.WF, EG.IsDecomp |

**deps_declared** (manuscript \deps): `s1:defObject`

**deps_from_proof:** s1:defObject, s1:convGraphs — The proof re-proves the balanced-digraph cycle decomposition (s1:citEuler(c) is NOT used). Simplicity of G (s1:convGraphs) excludes 2-cycles; formally this is IsOrientation's uniqueness clause (no antiparallel arcs).

**used_by:** s6:lemHCCP (Step 4, needs the precise form: every cycle contains a W-arc, for the length bound)

**randomness:** none (deterministic combinatorial lemma)

**lean_shape:**

```lean
-- EXISTS (EG/Spec/Chain/Gate.lean):
def EG.Spec.GateStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (F : Finset (Sym2 V)) (A W : Finset (V × V)),
    F ⊆ G.edges → EG.IsOrientation F A → EG.IsBalanced A → W ⊆ A → EG.IsAcyclic (A \ W) →
    ∃ D : List (EG.Obj V), EG.IsDecomp (F : Set (Sym2 V)) D ∧ D.length ≤ W.card ∧
      ∀ o ∈ D, (∃ c : List V, o = EG.Obj.cycle c) ∧ ∀ e ∈ o.edges, e ∈ G.edges
def EG.Spec.GatePreciseStatement : Prop := … ∃ cs : List (List V),
  (∀ c ∈ cs, EG.IsDirCycle A c ∧ 3 ≤ c.length ∧ (EG.Obj.cycle c).WF ∧ (∀ e ∈ EG.cycleEdges c, e ∈ G.edges) ∧
     (∃ w ∈ W, w ∈ EG.cycleArcs c)) ∧ (cs.flatMap EG.cycleArcs).Nodup ∧
  (∀ a, a ∈ cs.flatMap EG.cycleArcs ↔ a ∈ A) ∧ cs.length ≤ W.card
-- consumer form (EG/Proof/Chain/Gate.lean): EG.gate_with_cycles
```

**hazards:**

- **[note] GATE-DONE.** Statement and proof exist and were approved twice; nothing to do except lock/tag. The two conclusions are both needed: HCC-P Step 4 uses the precise form (each cycle is a directed cycle of F⃗ containing a W-arc) for its length claim.
- **[note] GATE-G-ONLY-FOR-CYCLES-OF-G.** The hypothesis F ⊆ E(G) only serves 'cycles of G' (edges in G.edges) and looplessness; IsOrientation already forces F loopless and excludes antiparallel arcs (EG.IsOrientation.not_mem_swap), which is the formal content of 'G is simple, so no 2-cycles'.
- **[note] GATE-BALANCE-GLOBAL.** IsBalanced quantifies over all vertices; this is right for GATE (the manuscript says 'at every vertex'). It must NOT be reused for cluster admissibility (balance at hubs only; CONVENTIONS).

**effort:** ~0 Lean lines, difficulty 1/5 (Done: Spec ~70 lines, proof ~130 lines, shared Lib EG/Lib/Found/Orient.lean ~1100 lines (also provides the HCC-P helpers: isOrientation_walkArcs, IsOrientation.union, exists_cancel_dirCycles, exists_balanced_sdiff_acyclic, isAcyclic_of_potential, IsAcyclic.exists_potential, isDecomp_map_cycle_of_arcs).).

### `s6:defCluster` — definition: clusters; bead count; parity-clean; admissible orientation; excess; load; median orientation MED(≺) (s6.tex:33)

- **Manuscript referee status:** x2
- **Formalization:** Defs: new protected file EG/Defs/Chain/Cluster.lean (Cluster structure, verts, beadCount, ParityClean, IsAdmissible, exc, load, medOrient)

**Statement (precise restatement).** A cluster K = (A_K, U_K, B_K): A_K (hubs) and U_K (ports) are DISJOINT finite vertex sets, V(K) := A_K ∪ U_K; B_K ⊆ E(G[A_K ∪ U_K]) (edges of the input graph G with both ends in V(K)) is the bead set, and NO bead has both ends in A_K. Bead count b(K) := Σ_{h ∈ A_K} deg_{B_K}(h)/2 + e(B_K[U_K]) (a half-integer in general, an integer when K is parity-clean). K is parity-clean iff deg_{B_K}(h) is even for every hub h. An admissible orientation of K is an orientation O of B_K (each bead exactly one direction) that is ACYCLIC and has d⁺_O(h) = d⁻_O(h) for every HUB h (no condition at ports). For such O and a port u: exc(u) := d⁺_O(u) − d⁻_O(u) ∈ ℤ, exc(u)⁺ := max(exc(u), 0), exc(u)⁻ := max(−exc(u), 0); the load Φ(K) := Σ_{u ∈ U_K} exc(u)⁺ (depends on O). For K parity-clean and a linear order ≺ on U_K, the median orientation MED(≺): at a hub h with B_K-neighbours u_1 ≺ … ≺ u_{2d} (all ports, since no bead joins two hubs; d ≥ 0) orient u_i → h for i ≤ d and h → u_i for i > d; orient each port–port bead uv with u ≺ v as u → v. Every bead is oriented exactly once.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| input graph G, E(G[S]) | finite simple graph; induced edge set | s1:convGraphs | yes: EG.FGraph, FGraph.induce (a cluster is better G-free: beads loopless with ends in A ∪ U, plus a hypothesis beads ⊆ G.edges where needed) |
| deg_B(v), e(B[U]) | number of beads at v; number of beads with both ends in U | s1:convGraphs(c) | yes: EG.degE; e(B[U]) = (B.filter (· ∈ U.sym2)).card |
| orientation, d⁺, d⁻, acyclic | as in GATE | s6 preamble | yes: EG.IsOrientation, EG.outDeg, EG.inDeg, EG.IsAcyclic |
| Cluster (structure) | hubs ports : Finset V; beads : Finset (Sym2 V); Disjoint hubs ports; ∀ e ∈ beads, ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ hubs ∪ ports; ∀ e ∈ beads, ∃ v ∈ e, v ∈ ports | s6:defCluster | no: new EG.Chain.Cluster |
| linear order ≺ on U_K | an injective rank rk : V → ℕ on U_K (u ≺ v iff rk u < rk v); every linear order of a finite set is of this form | s6:defCluster | no (represent by rk; MED depends only on the induced order) |
| MED(≺) as a Finset of arcs | ((V(K) ×ˢ V(K)).filter fun a => s(a.1,a.2) ∈ B ∧ ((a.1 ∈ U ∧ a.2 ∈ A ∧ 2·#{w ∈ N_B(a.2) : rk w ≤ rk a.1} ≤ deg_B(a.2)) ∨ (a.1 ∈ A ∧ a.2 ∈ U ∧ 2·#{w ∈ N_B(a.1) : rk w ≤ rk a.2} > deg_B(a.1)) ∨ (a.1 ∈ U ∧ a.2 ∈ U ∧ rk a.1 < rk a.2))) | s6:defCluster | no: EG.Chain.Cluster.medOrient (u_i has #{w ≼ u_i} = i, so i ≤ d ⟺ 2i ≤ 2d) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:convGraphs — Definition only. 'Every bead is oriented exactly once' is a claim (needs 'no hub–hub bead' and A ∩ U = ∅); it is part (a) of s6:lemMED in Lean (medOrient is an orientation of B_K).

**used_by:** s6:lemMED; s6:lemHCCP; s6:lemJSLC (Steps 4, 5: component clusters, cherries)

**randomness:** none

**lean_shape:**

```lean
-- EG/Defs/Chain/Cluster.lean (protected)
structure EG.Chain.Cluster (V : Type*) where
  hubs : Finset V
  ports : Finset V
  beads : Finset (Sym2 V)
  disjoint : Disjoint hubs ports
  loopless : ∀ e ∈ beads, ¬ e.IsDiag
  ends_mem : ∀ e ∈ beads, ∀ v ∈ e, v ∈ hubs ∪ ports
  no_hub_hub : ∀ e ∈ beads, ∃ v ∈ e, v ∈ ports
namespace EG.Chain.Cluster
variable [DecidableEq V] (K : Cluster V)
def verts : Finset V := K.hubs ∪ K.ports
def beadCount : ℕ := ∑ h ∈ K.hubs, EG.degE K.beads h / 2 + (K.beads.filter (· ∈ K.ports.sym2)).card
def ParityClean : Prop := ∀ h ∈ K.hubs, Even (EG.degE K.beads h)
structure IsAdmissible (O : Finset (V × V)) : Prop where
  orient : EG.IsOrientation K.beads O
  acyclic : EG.IsAcyclic O
  hub_bal : ∀ h ∈ K.hubs, EG.outDeg O h = EG.inDeg O h
def exc (O : Finset (V × V)) (u : V) : ℤ := (EG.outDeg O u : ℤ) - EG.inDeg O u
def load (O : Finset (V × V)) : ℕ := ∑ u ∈ K.ports, (exc O u).toNat
def medOrient (rk : V → ℕ) : Finset (V × V) := (K.verts ×ˢ K.verts).filter (fun a => s(a.1, a.2) ∈ K.beads ∧ medRule K rk a.1 a.2)
```

**hazards:**

- **[note] CL-ADMISSIBLE-LOCAL.** Admissibility requires balance at HUBS only; ports are unbalanced by design. Use pointwise outDeg/inDeg on K.hubs, never EG.IsBalanced (CONVENTIONS, 'Orientations').
- **[note] CL-ORIENT-IS-DATA.** exc(u) and Φ(K) depend on the orientation, which the notation suppresses ('Φ(K)', 'exc(u)'). In Lean they take O as an argument, and HCC-P's 'each cluster with a fixed admissible orientation' is data (O : Fin N → Finset (V × V)). A port's exc is taken in the unique cluster containing it (HCC-P (D)).
- **[note] CL-BEADCOUNT-HALF.** b(K) contains deg/2, a half-integer for non-parity-clean hubs. It is only ever used for parity-clean clusters (MED(b), JS-LC Step 4 where b(K_C) = |E(C)|/2). Define with ℕ division and prove exactness under ParityClean (or under admissibility, which forces even hub degrees); a ℚ-valued definition is an alternative.
- **[note] CL-G-FREE.** The manuscript's B_K ⊆ E(G[A ∪ U]) mentions the input graph. Recommended: a G-free Cluster (loopless beads with ends in V(K)) plus an explicit hypothesis K.beads ⊆ G.edges in HCC-P. All consumer clusters (JS-LC components and cherries) have beads in E_l(Z) ⊆ E(G).
- **[note] CL-MED-TOTAL.** MED(≺) is defined in the manuscript only for parity-clean clusters ('u_1 ≺ … ≺ u_{2d}'). The Lean medOrient is total (median count rule 2·#{w ≼ u} ≤ deg); its properties are claimed only under ParityClean and rk injective on ports (s6:lemMED).
- **[note] CL-IDENTITY.** Layers are 'families of clusters'. Equal triples may occur (e.g. empty clusters); index clusters (Fin N → Cluster V) and state HCC-P (D) for distinct INDICES, not as a Finset of clusters.

**effort:** ~150 Lean lines, difficulty 2/5 (Structure, 7 definitions, basic API (verts, exc as ℤ, beadCount exactness lemma, medRule decidability).).

### `s6:lemMED` — lemma: Lemma MED (s6.tex:56)

- **Manuscript referee status:** x2; +RA
- **Formalization:** Spec EG/Spec/Chain/MED.lean: MedStatement ((a), for medOrient) and MedExcStatement ((b), for EVERY admissible orientation); Lib corollary exists_admissible (all consumers need only existence)

**Statement (precise restatement).** Let K be a parity-clean cluster and ≺ a linear order on U_K (rk injective on U_K). (a) MED(≺) is an orientation of B_K (every bead exactly one arc, no loop), it is acyclic, and every hub h has d⁺(h) = d⁻(h) (= deg_{B_K}(h)/2); i.e. MED(≺) is admissible. Moreover there is pot : A_K ∪ U_K → (0,1) with pot(x) < pot(y) for every arc x → y of MED(≺). (b) For EVERY admissible orientation O of K (in particular MED(≺)) and every port u ∈ U_K: |exc(u)| ≤ deg_{B_K}(u) and exc(u) ≡ deg_{B_K}(u) (mod 2); moreover Σ_{u ∈ U_K} exc(u) = 0 and Φ(K) = Σ_u exc(u)⁺ ≤ b(K).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| Cluster, ParityClean, IsAdmissible, exc, load, beadCount, medOrient | see s6:defCluster | s6:defCluster | no: new (EG/Defs/Chain/Cluster.lean) |
| potential | pot : V → ℝ, 0 < pot v < 1 on V(K), strictly increasing along arcs | s6:lemMED(a) | Lib: EG.isAcyclic_of_potential (any LinearOrder) turns it into acyclicity |
| rk (rank realising ≺) | rk : V → ℕ injective on U_K; the manuscript uses rk : U → {1..\|U\|} and pot(u) = rk(u)/(\|U\|+1) | proof of (a) | no |

**deps_declared** (manuscript \deps): `s6:defCluster`

**deps_from_proof:** s6:defCluster — Nothing else. (a) uses: no hub–hub bead (neighbours of hubs are ports), parity-clean (2d neighbours), ranks distinct integers. (b) uses: orientation (each bead one arc: exc is a ±1 sum over deg(u) beads), hub balance (d⁻(h) = deg(h)/2), no hub–hub bead (every in-arc at a hub comes from a port), handshake Σ_v (d⁺−d⁻) = 0; acyclicity is NOT used in (b).

**used_by:** s6:lemHCCP (Step 0: Σ exc = 0 per cluster; Step 3 optionally (a)); s6:lemJSLC (Step 4: MED on component clusters, Φ ≤ b = |E(C)|/2, |exc| ≤ M_l − 1; Step 4 padding: Φ^raw_j = ½ Σ|exc|; joint-routing claim (a))

**randomness:** none

**lean_shape:**

```lean
open EG.Chain in
def EG.Spec.MedStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (K : Cluster V) (rk : V → ℕ), K.ParityClean → Set.InjOn rk K.ports →
    K.IsAdmissible (K.medOrient rk) ∧
    ∃ pot : V → ℝ, (∀ v ∈ K.verts, 0 < pot v ∧ pot v < 1) ∧ ∀ a ∈ K.medOrient rk, pot a.1 < pot a.2
def EG.Spec.MedExcStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (K : Cluster V) (O : Finset (V × V)), K.IsAdmissible O →
    (∀ u ∈ K.ports, (Cluster.exc O u).natAbs ≤ EG.degE K.beads u ∧ Even (Cluster.exc O u - EG.degE K.beads u)) ∧
    (∑ u ∈ K.ports, Cluster.exc O u = 0) ∧ K.load O ≤ K.beadCount
-- Lib: theorem Cluster.exists_admissible (K) (h : K.ParityClean) : ∃ O, K.IsAdmissible O
```

**hazards:**

- **[note] MED-ONLY-EXISTENCE-USED.** No consumer uses the median structure: JS-LC Step 4 only needs 'some admissible orientation exists' and then (b) (valid for every admissible orientation). Keep the faithful Spec on medOrient (MedStatement), and derive the Lib corollary exists_admissible for consumers; the consumer proofs must not depend on medOrient's shape.
- **[note] MED-MEDIAN-COUNT.** The Lean proof of 'exactly d in-arcs at a hub of degree 2d' is a counting argument on the rank-sorted neighbour list (#{w ∈ N(h) : rk w ≤ rk u} ranges over 1..2d bijectively); needs rk injective on ports and N_B(h) ⊆ ports. Moderate list/Finset bookkeeping (~150 lines).
- **[note] MED-POT-UNUSED.** The potential of (a) is used only to derive acyclicity; HCC-P Step 3 uses a topological numbering of the given admissible orientation instead (EG.IsAcyclic.exists_potential exists). Keep (a) as stated; no consumer needs the (0,1) range.
- **[note] MED-INT-PARITY.** exc is an integer; state parity as Even (exc − deg) in ℤ and |exc| via natAbs; Φ(K) uses Int.toNat of exc. Σ exc = 0 is an ℤ-sum over U_K (hubs contribute 0 by balance; the handshake lemmas EG.sum_outDeg_eq_card / sum_inDeg_eq_card exist).
- **[note] MED-B-NEEDS-NO-HUBHUB.** Φ ≤ b uses that every arc with tail at a port ends at a hub or at a port, and that every in-arc at a hub has its tail at a port; both need the cluster axiom 'no bead has both ends in A_K'. Also needs IsOrientation.outDeg_add_inDeg (exists) for |exc| ≤ deg and the parity claim.

**effort:** ~350 Lean lines, difficulty 2/5 ((a) ~220 (orientation property of medOrient ~80, median count ~100, potential ~40); (b) ~100; corollary ~20.).

### `s6:lemEQLPT` — lemma: Lemma EQ-LPT (greedy longest-processing-time placement) (s6.tex:90)

- **Manuscript referee status:** x2; +RA
- **Formalization:** Defs (IsGreedyLPT, layerLoad; EG/Defs/Chain/EqLpt.lean) + Spec EG/Spec/Chain/EqLpt.lean: EqLptStatement (existence of a greedy placement + properties of EVERY greedy placement)

**Statement (precise restatement).** Let m ≥ 1, reals Φ_1 ≥ Φ_2 ≥ … ≥ Φ_m ≥ 0 and an integer k with 1 ≤ k ≤ m. A greedy placement is a map σ : {1..m} → {1..k} such that, for every item i, with L^{<i}_j := Σ_{i' < i, σ(i') = j} Φ_{i'} (load of layer j before item i) and 'layer j empty before i' := no i' < i has σ(i') = j: (G1) L^{<i}_{σ(i)} ≤ L^{<i}_j for all j, and (G2) if some layer is empty before i, then σ(i) is empty before i. CLAIMS: (0) a greedy placement exists (the rule is consistent: an empty layer has load 0, which is minimum since all loads are ≥ 0); (1) for EVERY greedy placement σ, every layer receives at least one item, and with L_j := Σ_{σ(i)=j} Φ_i: max_j L_j − min_j L_j ≤ Φ_1.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| greedy placement (a relation, ties arbitrary) | IsGreedyLPT Φ σ as (G1) ∧ (G2) above | s6:lemEQLPT (statement text) | no: new EG.Chain.IsGreedyLPT |
| layer load | layerLoad Φ σ j := Σ_{i : σ i = j} Φ i | s6:lemEQLPT | no: new EG.Chain.layerLoad |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Self-contained. The ordering Φ_1 ≥ … is used only to know Φ_x ≤ Φ_1 for the last item x of a heaviest layer; the bound max − min ≤ max_i Φ_i holds for any order.

**used_by:** s6:lemJSLC (Step 4: component clusters, loads Φ(K_C) ∈ ℕ, k_0 layers; Step 5: cherries with unit loads, k_i layers)

**randomness:** none

**lean_shape:**

```lean
-- EG/Defs/Chain/EqLpt.lean
def EG.Chain.IsGreedyLPT {m k : ℕ} (Φ : Fin m → ℝ) (σ : Fin m → Fin k) : Prop :=
  ∀ i : Fin m,
    (∀ j, (∑ i' ∈ Finset.univ.filter (fun i' => i' < i ∧ σ i' = σ i), Φ i') ≤
          ∑ i' ∈ Finset.univ.filter (fun i' => i' < i ∧ σ i' = j), Φ i') ∧
    ((∃ j, ∀ i' < i, σ i' ≠ j) → ∀ i' < i, σ i' ≠ σ i)
def EG.Chain.layerLoad {m k : ℕ} (Φ : Fin m → ℝ) (σ : Fin m → Fin k) (j : Fin k) : ℝ :=
  ∑ i ∈ Finset.univ.filter (σ · = j), Φ i
def EG.Spec.EqLptStatement : Prop :=
  ∀ (m k : ℕ) (Φ : Fin m → ℝ) (h1 : 1 ≤ k) (hkm : k ≤ m), Antitone Φ → (∀ i, 0 ≤ Φ i) →
    (∃ σ : Fin m → Fin k, EG.Chain.IsGreedyLPT Φ σ) ∧
    ∀ σ : Fin m → Fin k, EG.Chain.IsGreedyLPT Φ σ → Function.Surjective σ ∧
      ∀ j j', EG.Chain.layerLoad Φ σ j - EG.Chain.layerLoad Φ σ j' ≤ Φ ⟨0, by omega⟩
```

**hazards:**

- **[note] EQ-GREEDY-RELATION.** 'Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists' is a nondeterministic rule (ties arbitrary). Formalize as a relation IsGreedyLPT and quantify over ALL greedy placements (faithful 'then'); add the existence conjunct (0), which the manuscript asserts in the proof ('So the rule is consistent') and which JS-LC needs to 'layer them by that lemma'.
- **[note] EQ-REAL-VS-NAT.** Loads are reals ≥ 0 in the statement but natural numbers at every use (Φ(K_C) and unit cherry loads). State over ℝ (faithful) and cast at the use, or state for a LinearOrderedAddCommMonoid; do not state over ℕ only (that would be a weakening).
- **[note] EQ-INDEX-SHIFT.** Items 1..m and layers 1..k become Fin m / Fin k (0-based); Φ_1 is Φ ⟨0,_⟩ (CONVENTIONS, [k] vs Fin k).
- **[note] EQ-USE-EMPTY-S0.** Cross-chunk (s6:lemJSLC Step 4): k_0 := min(K, max(1, ⌊ΣΦ/(2Φ_max)⌋)) divides by Φ_max, and EQ-LPT needs 1 ≤ k ≤ m. If R_Y has no non-giant component, S_0(Y,l) has m = 0 clusters and ΣΦ = Φ_max = 0; the text says 'S_0(Y,l) (if non-empty)' only in Step 6. The JS-LC Lean proof must case-split on S_0 = ∅ (trivial, but the literal formula is ill-defined there). Also 'k_0 ≤ number of clusters' needs Φ(K_C) ≥ 1 for every cluster (proved in JS-LC).

**effort:** ~250 Lean lines, difficulty 2/5 (Existence by recursion on i (choose an empty layer if any, else an argmin) ~90; surjectivity (first k items go to distinct empty layers) ~60; spread bound (last item of a heaviest layer; loads monotone in time) ~100.).

### `s6:lemPAR` — lemma: Lemma PAR (port–port parity) (s6.tex:105)

- **Manuscript referee status:** x2; +RA
- **Formalization:** Defs (edge-set components, bridges, pendant edges: new EG/Defs/Components.lean, shared with s6:defDesign 'giant' and s5/s7 forests) + Spec EG/Spec/Chain/PAR.lean: ParStatement

**Statement (precise restatement).** Let E_ab be a finite set of edges (loop-free) and V_a, V_b DISJOINT vertex sets such that every edge of E_ab has one end in V_a and the other in V_b. Let V(E_ab) be the set of ends of edges of E_ab, and consider the connected components of the graph (V(E_ab), E_ab); a component is odd if it has an odd number of edges. (0) Every odd component contains an edge that is a non-bridge of it (its removal leaves the component connected) or a pendant edge (an end of degree 1). (1) For EVERY set J' ⊆ E_ab that contains exactly one edge of each odd component, no edge of any even component, and only edges that are non-bridges or pendant edges of their components: |J'| ≤ #{odd components} ≤ |V(E_ab)|/2, and there is a partition E_ab \ J' = S_a ⊔ S_b such that deg_{S_a}(v) is even for every v ∈ V_b and deg_{S_b}(u) is even for every u ∈ V_a.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| V(E) (ends of an edge set) | E.biUnion of the two ends | s6:lemPAR | no: new EG.edgeVerts |
| components of an edge set; edges of a component; odd component | connected components of (FGraph.ofEdges (edgeVerts E) E).toSimpleGraph (Mathlib SimpleGraph.ConnectedComponent); compEdges C := edges with both ends in C | s6:lemPAR | no: new EG.edgeGraph, EG.edgeComps, EG.compEdges |
| bridge / non-bridge; pendant edge | Mathlib SimpleGraph.IsBridge on edgeGraph E (bridge of a component = bridge of the whole graph); pendant: ∃ v ∈ e, degE E v = 1 | s6:lemPAR | no: new EG.IsNonBridge, EG.IsPendant (via Mathlib IsBridge) |
| T-join in a spanning tree | for a connected graph H and T ⊆ V(H) with \|T\| even, every spanning tree contains J with odd J-degree exactly on T | s1:citEuler(a) | no: planned Lib (s1 blueprint: citEuler(a) as Lib theorem; PAR needs the SIMPLE-graph form on a component) |
| deg_S(v) | number of edges of S at v | s1:convGraphs(c) | yes: EG.degE |

**deps_declared** (manuscript \deps): `s1:citEuler`

**deps_from_proof:** s1:citEuler, s1:convGraphs — Uses only s1:citEuler(a) (T-join in a spanning tree of each even component) plus elementary facts: a component with a cycle has a non-bridge, a tree with an edge has a leaf; deleting a non-bridge keeps connectivity; deleting a pendant edge isolates one vertex.

**used_by:** s6:lemJSLC (Step 2a: per standalone part Z and pair {a,b} of classes; counting of PAR deletions for (eqJbound)); s6:lemJplus (J^par edges; 'for every choice')

**randomness:** none

**lean_shape:**

```lean
-- EG/Defs/Components.lean (new, protected)
def EG.edgeVerts (E : Finset (Sym2 V)) : Finset V := E.biUnion (fun e => e.toFinset)   -- via Sym2 → Finset
def EG.edgeGraph (E) : SimpleGraph V := (EG.FGraph.ofEdges (EG.edgeVerts E) E).toSimpleGraph
noncomputable def EG.edgeComps (E) : Finset (EG.edgeGraph E).ConnectedComponent :=
  (EG.edgeVerts E).image (EG.edgeGraph E).connectedComponentMk
def EG.compEdges (E) (C : (EG.edgeGraph E).ConnectedComponent) : Finset (Sym2 V) :=
  E.filter (fun e => ∀ v ∈ e, (EG.edgeGraph E).connectedComponentMk v = C)
def EG.IsNonBridge (E) (e : Sym2 V) : Prop := e ∈ E ∧ ¬ (EG.edgeGraph E).IsBridge e
def EG.IsPendant (E) (e : Sym2 V) : Prop := e ∈ E ∧ ∃ v ∈ e, EG.degE E v = 1
def EG.Chain.IsParChoice (E J' : Finset (Sym2 V)) : Prop :=
  J' ⊆ E ∧ (∀ C ∈ EG.edgeComps E, (J' ∩ EG.compEdges E C).card = if Odd (EG.compEdges E C).card then 1 else 0) ∧
  ∀ e ∈ J', EG.IsNonBridge E e ∨ EG.IsPendant E e
def EG.Spec.ParStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (E : Finset (Sym2 V)) (Va Vb : Finset V),
    Disjoint Va Vb → (∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) →
    (∀ C ∈ EG.edgeComps E, Odd (EG.compEdges E C).card → ∃ e ∈ EG.compEdges E C, EG.IsNonBridge E e ∨ EG.IsPendant E e) ∧
    ∀ J', EG.Chain.IsParChoice E J' →
      let odd := (EG.edgeComps E).filter (fun C => Odd (EG.compEdges E C).card)
      J'.card ≤ odd.card ∧ 2 * odd.card ≤ (EG.edgeVerts E).card ∧
      ∃ Sa Sb : Finset (Sym2 V), Disjoint Sa Sb ∧ Sa ∪ Sb = E \ J' ∧
        (∀ v ∈ Vb, Even (EG.degE Sa v)) ∧ ∀ u ∈ Va, Even (EG.degE Sb u)
```

**hazards:**

- **[risk] PAR-GRAPH-INFRA.** Components, bridges, pendant edges and spanning trees of an EDGE SET are not in EG/Defs or EG/Lib. They must be built on FGraph.toSimpleGraph + Mathlib (ConnectedComponent, IsBridge, Connected.exists_isTree_le or an own spanning-tree construction), with transport lemmas between compEdges/degE and Mathlib degree/edge sets. The T-join lemma (s1:citEuler(a)) is planned as a Lib theorem for multigraph forests (s1 blueprint EUL-MULTI-USE); PAR needs the simple-graph instance on each component. Estimated ~400 lines of infrastructure before PAR proper; shared with s6:defDesign ('giant' components) and s5:lemParent.
- **[note] PAR-SIDES-DISJOINT.** The Spec must assume Disjoint V_a V_b (implicit in 'bipartite graph with sides V_a, V_b'); without it the lemma is false (V_a = V_b = {x,y,z}, E = {xy, yz}: one even component, J' = ∅, but no partition makes all degrees even in both S_a and S_b). In JS-LC the sides are class-a and class-b ports of Qs_Z, disjoint because each port has one class and a ≠ b.
- **[note] PAR-FORALL-CHOICE.** 'for EVERY such choice' is load-bearing for s6:lemJplus ('this holds for every choice'); state the conclusion ∀ J' with IsParChoice, and the existence of an admissible edge per odd component as a separate conjunct (0). The J-interface must not depend on which admissible edge was chosen.
- **[note] PAR-DIRECT-PROOF-OPTION.** Alternative that avoids spanning trees: prove 'a connected graph has a spanning subgraph with prescribed degree parities p iff Σ p is even' by induction on edges (or via paths between T-pairs, symmetric difference). Either route is acceptable; the Spec does not change.
- **[note] PAR-COUNT-USE.** The bounds |J'| ≤ #odd ≤ |V(E_ab)|/2 feed only (eqJbound) of JS-LC, which the manuscript says is not used later; the parity partition is the load-bearing part. Keep the bounds (faithful; cheap).
- **[note] PAR-COMPONENT-ISOLATED.** Mathlib components include singleton components of vertices outside edgeVerts E; edgeComps is taken over edgeVerts E only, and odd components automatically have ≥ 1 edge, hence ≥ 2 vertices of V(E_ab) (the counting step).

**effort:** ~700 Lean lines, difficulty 3/5 (Defs/Components ~80; component/bridge/pendant API ~250; existence of admissible edge (cycle ⇒ non-bridge; tree ⇒ leaf) ~120; even components after deletion ~120; parity partition via T-join per component and gluing ~130.).

### `s6:lemHCCP` — lemma: Lemma HCC-P (layered hub-cluster chaining with path junctions) (s6.tex:140)

- **Manuscript referee status:** x2; +RA (flagged in s1:remStatus(iv)(a))
- **Formalization:** Defs (EG/Defs/Chain/HCCP.lean: HccpData, HccpData.Valid, derived layP, pexc, demMinus, demPlus, Phi, pathEdges, beads) + Spec EG/Spec/Chain/HCCP.lean: HccpStatement

**Statement (precise restatement).** Data: k ≥ 1; finitely many clusters K_i (i ∈ I) each with a FIXED admissible orientation O_i and a layer lay(i) ∈ {0..k−1}; LayP_j := ∪_{lay(i)=j} U_{K_i}; junction sets T_0..T_{k−1}; a padding pad : ∪_j LayP_j → ℤ_{≥0} with pad ≡ 0 if k = 1; for a port u (of the unique cluster containing it): dm⁻(u) := exc(u)⁻ + pad(u), dm⁺(u) := exc(u)⁺ + pad(u); padded loads Φ_j := Σ_{u ∈ LayP_j} dm⁺(u); indices mod k. Hypotheses: (D) the sets A_{K_i}, U_{K_i} (over all i, all layers) and T_0..T_{k−1} are pairwise disjoint; (P) every K_i is parity-clean; (JC-P) for each j a finite family P_j (a list; multiplicity counts) of paths of G such that: each path starts in LayP_j and ends in LayP_{j+1}, all its interior vertices lie in T_j; every u ∈ LayP_j is the first vertex of exactly dm⁻(u) paths of P_j and every v ∈ LayP_{j+1} is the last vertex of exactly dm⁺(v) paths of P_j (for k = 1 this is: paths from X^out = {exc < 0} to X^in = {exc > 0}, u starting exc(u)⁻ and v ending exc(v)⁺ of them — equivalent, since pad = 0); the paths of each P_j are pairwise edge-disjoint; the edge sets E(P_0), …, E(P_{k−1}) and all bead sets B_{K_i} are pairwise disjoint; beads are edges of G. Conclusions: (i) there is Φ with Φ_j = Φ = |P_j| for every j; (ii) there are F_j ⊆ E(P_j) with E(P_j) \ F_j ⊆ E(G[T_j]) such that (∪_i B_{K_i}) ∪ (∪_j F_j) has a decomposition into at most Φ cycles of G (no single edges), each of length ≥ max(3,k). The edges E(P_j) \ F_j ('returned') are not used.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| cluster, admissible orientation, exc, parity-clean | see s6:defCluster | s6:defCluster | no: new EG.Chain.Cluster (EG/Defs/Chain/Cluster.lean) |
| paths, interior, 'through T' | vertex lists, IsPathIn G.edges p, IsThrough T p, head?/getLast? | s1:convGraphs(d) | yes: EG.IsPathIn, EG.IsThrough, EG.interior, EG.walkEdges |
| E(G[T]) | edges with both ends in T | s1:convGraphs | yes: T.sym2 (Finset.sym2) / FGraph.induce |
| HCC-P system (all data bundled) | k, N, K : Fin N → Cluster V, O : Fin N → Finset (V × V), lay : Fin N → Fin k, T : Fin k → Finset V, pad : V → ℕ, P : Fin k → List (List V) | s6:lemHCCP | no: new EG.Chain.HccpData |
| LayP_j, dm±, Φ_j, E(P_j), succ mod k | layP j := (univ.filter (lay · = j)).biUnion (ports ∘ K); pexc u := Σ_i [u ∈ ports i] exc (O i) u; demMinus/demPlus via Int.toNat; succ j := ⟨(j+1) % k, _⟩ | s6:lemHCCP | no: new (derived defs of HccpData) |
| decomposition into cycles | IsDecomp of the union with objects Obj.cycle | s1:defObject | yes: EG.IsDecomp, EG.Obj |

**deps_declared** (manuscript \deps): `s6:lemGATE`, `s6:lemMED`, `s6:defCluster`

**deps_from_proof:** s6:lemMED, s6:lemGATE, s6:defCluster, s1:defObject, s1:convGraphs — Step 0 uses MED(b) (Σ_{U_K} exc = 0 for every admissible orientation). Step 3 uses a topological numbering of each acyclic admissible orientation and of D'_j[T_j] (Lib EG.IsAcyclic.exists_potential), MED(a) only optionally. Step 1 cancellation = Lib EG.exists_cancel_dirCycles. Step 4 = GATE precise form (EG.gate_with_cycles). Simplicity of G: bead sets of vertex-disjoint clusters are disjoint; edge-disjoint paths give an arc SET.

**used_by:** s6:lemHCCglob; s6:lemJSLC (Step 7, per system S_0(Y,l) and cherry classes S_i(Y,l)); s6:lemJplus ('HCC-P output consists of cycles only')

**randomness:** none

**lean_shape:**

```lean
-- EG/Defs/Chain/HCCP.lean
structure EG.Chain.HccpData (V : Type*) where
  k : ℕ
  N : ℕ
  K : Fin N → EG.Chain.Cluster V
  O : Fin N → Finset (V × V)
  lay : Fin N → Fin k
  T : Fin k → Finset V
  pad : V → ℕ
  P : Fin k → List (List V)
namespace EG.Chain.HccpData  -- variable [DecidableEq V] (S : HccpData V)
def succ (j : Fin S.k) : Fin S.k := ⟨(j.1 + 1) % S.k, Nat.mod_lt _ (Fin.pos j)⟩
def layP (j) : Finset V := (Finset.univ.filter (S.lay · = j)).biUnion (fun i => (S.K i).ports)
def pexc (u : V) : ℤ := ∑ i, if u ∈ (S.K i).ports then Cluster.exc (S.O i) u else 0
def demMinus (u) : ℕ := (-(S.pexc u)).toNat + S.pad u ;  def demPlus (u) : ℕ := (S.pexc u).toNat + S.pad u
def Phi (j) : ℕ := ∑ u ∈ S.layP j, S.demPlus u
def pathEdges (j) : Finset (Sym2 V) := ((S.P j).flatMap EG.walkEdges).toFinset
def beads : Finset (Sym2 V) := Finset.univ.biUnion (fun i => (S.K i).beads)
structure Valid (G : EG.FGraph V) : Prop where
  k_pos : 1 ≤ S.k
  pad_k1 : S.k = 1 → ∀ u, S.pad u = 0
  beads_G : ∀ i, (S.K i).beads ⊆ G.edges
  adm : ∀ i, (S.K i).IsAdmissible (S.O i)
  D_KK : ∀ i i', i ≠ i' → Disjoint (S.K i).verts (S.K i').verts
  D_KT : ∀ i j, Disjoint (S.K i).verts (S.T j)
  D_TT : ∀ j j', j ≠ j' → Disjoint (S.T j) (S.T j')
  P_clean : ∀ i, (S.K i).ParityClean
  path : ∀ j, ∀ p ∈ S.P j, EG.IsPathIn G.edges p ∧ EG.IsThrough (S.T j) p ∧
           (∃ u ∈ S.layP j, p.head? = some u) ∧ (∃ v ∈ S.layP (S.succ j), p.getLast? = some v)
  starts : ∀ j, ∀ u ∈ S.layP j, ((S.P j).filter (·.head? = some u)).length = S.demMinus u
  ends : ∀ j, ∀ v ∈ S.layP (S.succ j), ((S.P j).filter (·.getLast? = some v)).length = S.demPlus v
  edisj : ∀ j, ((S.P j).flatMap EG.walkEdges).Nodup
  pdisj : ∀ j j', j ≠ j' → Disjoint (S.pathEdges j) (S.pathEdges j')
  bdisj : ∀ j, Disjoint (S.pathEdges j) S.beads
-- EG/Spec/Chain/HCCP.lean
def EG.Spec.HccpStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (S : EG.Chain.HccpData V), S.Valid G →
    (∃ Φ : ℕ, ∀ j, S.Phi j = Φ ∧ (S.P j).length = Φ) ∧
    ∃ F : Fin S.k → Finset (Sym2 V), (∀ j, F j ⊆ S.pathEdges j) ∧ (∀ j, S.pathEdges j \ F j ⊆ (S.T j).sym2) ∧
      ∃ cs : List (List V), EG.IsDecomp ↑(S.beads ∪ Finset.univ.biUnion F) (cs.map EG.Obj.cycle) ∧
        (∀ j, cs.length ≤ S.Phi j) ∧ ∀ c ∈ cs, max 3 S.k ≤ c.length ∧ ∀ e ∈ EG.cycleEdges c, e ∈ G.edges
```

**hazards:**

- **[risk] HCCP-FLAGGED-REDERIVED.** s1:remStatus(iv)(a) names the routing engine (HCC-P, PAR, MED, EQ-LPT as used in JS-LC) as the single most likely error site. I re-derived HCC-P completely: Step 0 (|P_j| = Σ_{LayP_j} dm⁻ = Φ_j via MED(b), and = Σ_{LayP_{j+1}} dm⁺ = Φ_{j+1}); Step 1 (ports are sources/sinks of D_j, including k = 2 where LayP_{j+1} = LayP_{j−1} ≠ LayP_j, and k = 1 via X^out ∩ X^in = ∅; cancelled cycles lie in T_j, so returned edges ⊆ E(G[T_j])); Step 2 (balance at hubs, T-vertices and ports: exc + dm⁻ − dm⁺ = 0); Step 3 (Ψ ∈ (3j,3j+1) on layer j and (3j+1,3j+2) on T_j; every non-W arc increases Ψ, including direct port→port arcs of length-1 paths; |W| = |P_{k−1}| because the last arcs are distinct, end at ports, and are never cancelled); Step 4 (GATE; the block-crossing count gives length ≥ k). No error found in HCC-P itself. The residual risk lies in JS-LC's verification of (D) and (JC-P) (joint routing multiplicity ≤ 2M_l − 2 ≤ t, pair ends distinct, T-avoidance), which is outside this chunk.
- **[risk] HCCP-EFFORT.** Largest Lean item of the chunk: orient each path (EG.isOrientation_walkArcs), union of arc sets under edge-disjointness (IsOrientation.union), degree bookkeeping per vertex class (hub / port of layer j / T_j vertex) with in/out counts of D_j equal to first/last-vertex counts of the list P_j, cancellation (EG.exists_cancel_dirCycles), a piecewise real potential Ψ built from per-cluster topological numberings and per-T_j numberings, the count |W| = |P_{k−1}|, GATE, and the block-crossing length argument on a directed cycle. The Lib from P1b covers the orientation primitives; the counting of first/last vertices of a list of paths vs out/in-degrees of the union of their arcs is new (~250 lines).
- **[note] HCCP-K1-UNIFORM.** The k = 1 special reading (paths from X^out to X^in, u ∈ X^out starts exactly exc(u)⁻ paths) is equivalent to the uniform reading with succ 0 = 0 and pad ≡ 0 (a first vertex u must have dm⁻(u) = exc(u)⁻ ≥ 1, i.e. u ∈ X^out; similarly for last vertices). State the Spec uniformly; the proof still needs X^out ∩ X^in = ∅ (automatic: exc(u) cannot be both < 0 and > 0).
- **[note] HCCP-INDEXED-CLUSTERS.** (D) is 'pairwise disjoint over all clusters of all layers'. With a Finset of clusters, a cluster occurring in two layers would be one element; index clusters by Fin N with a layer map and require disjointness for distinct indices (plus the cluster's own A ∩ U = ∅). pexc then reads the unique cluster containing u (by (D) the sum has ≤ 1 non-zero term).
- **[note] HCCP-PATH-FAMILY-LIST.** P_j is a family, not a set: use List (List V). 'Pairwise edge-disjoint' = Nodup of the concatenated walkEdges (also gives each path's own edges distinct, automatic for paths). Paths have ≥ 1 edge automatically (first and last vertices lie in disjoint sets), so the one-vertex-path caveat of EG.IsPathIn (CONVENTIONS) is harmless here, but keep the head/last membership conjuncts explicit.
- **[note] HCCP-JCP-AS-DATA.** (JC-P) says 'there is a family P_j'; conclusion (ii) refers to E(P_j). In the Spec the families are data of HccpData (universally quantified), not an existential hypothesis; this is the only faithful reading since F_j ⊆ E(P_j).
- **[note] HCCP-P-REDUNDANT.** (P) parity-clean follows from admissibility (hub balance forces even hub degree). Keep (P) as a field for fidelity; the proof never needs it separately.
- **[note] HCCP-LENGTH-UNUSED.** The conclusion 'each cycle has length ≥ max(3,k)' is used by no consumer (JS-LC, J+, MIX-C need only the count and that all objects are cycles). It costs ~150 lines (block-crossing argument). Keep it (faithful), but it may be split into a separate HccpLengthStatement so that consumers depend only on the count part.
- **[note] HCCP-PAD-DOMAIN.** pad is defined on ports only (values in ℤ_{≥0}); in Lean pad : V → ℕ with junk values off ports. The k = 1 condition 'pad ≡ 0' becomes ∀ u, pad u = 0 (the consumer passes pad := 0 when k = 1).
- **[note] HCCP-SUCC-FIN.** Indices mod k on Fin k: define succ j := ⟨(j+1) % k, _⟩ (or finRotate); JS-LC's 'junction j − 1' is the predecessor under the same map. For k = 2 the two neighbours coincide and the proof relies on succ j ≠ j (true for k ≥ 2).

**effort:** ~1100 Lean lines, difficulty 4/5 (Defs ~120; Step 0 counting ~120; Step 1 (orient + cancel, source/sink facts) ~200; Step 2 balance ~200; Step 3 potential Ψ and |W| = Φ ~250; Step 4 GATE + length ~200. Reuses EG/Lib/Found/Orient.lean.).

### `s6:lemHCCglob` — lemma: Lemma (union of systems) (s6.tex:221)

- **Manuscript referee status:** x2; +RA (joint-routing form)
- **Formalization:** Lib lemma (part 1: concatenation of decompositions of pairwise disjoint edge sets) + Spec EG/Spec/Chain/HCCP.lean: HccGlobStatement (part 2, with INPUT-level cross-system edge-disjointness)

**Statement (precise restatement).** (1) Let E_1, …, E_q ⊆ E(G) be pairwise disjoint and let each E_i have a decomposition D_i into a_i objects. Then the concatenation of D_1, …, D_q is a decomposition of E_1 ∪ … ∪ E_q into Σ_i a_i objects. (2) Let S_1, …, S_q be HCC-P systems, each satisfying all hypotheses of s6:lemHCCP on its own data (its own k, layers, junction sets, padding, path families; (D), (P), (JC-P) only INSIDE the system), and suppose the edge sets they decompose, B(S_s) ∪ ∪_j F_j(S_s), are pairwise disjoint across s. Then the union of these edge sets decomposes into at most Σ_s Φ(S_s) cycles. No vertex-disjointness across systems is required: a vertex may be a hub, a port or a junction vertex in several systems.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| decomposition, objects | IsDecomp, Obj | s1:defObject | yes: EG.IsDecomp, EG.Obj |
| HCC-P system | HccpData + Valid | s6:lemHCCP | no: new EG.Chain.HccpData (see s6:lemHCCP) |
| all path edges of a system | allPathEdges S := univ.biUnion S.pathEdges | s6:lemHCCglob | no: new derived def |

**deps_declared** (manuscript \deps): `s1:factAdd`, `s6:lemHCCP`

**deps_from_proof:** s1:factAdd, s6:lemHCCP, s1:defObject — The proof cites Fact s1:factAdd(b), which is about f (the minimum); what is actually used is concatenation of decompositions (Lean: IsDecomp of a flatMap of pairwise edge-disjoint decompositions, a Lib lemma).

**used_by:** s6:lemJSLC (Step 7: all systems of all (Y,l) of round l)

**randomness:** none

**lean_shape:**

```lean
-- Lib (EG/Lib/Found/Fnum.lean or Decomp.lean)
theorem EG.IsDecomp.biUnion {q : ℕ} (E : Fin q → Finset (Sym2 V)) (D : Fin q → List (EG.Obj V))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (E i) (E i')) (hD : ∀ i, EG.IsDecomp ↑(E i) (D i)) :
    EG.IsDecomp ↑(Finset.univ.biUnion E) ((List.finRange q).flatMap D) ∧
    ((List.finRange q).flatMap D).length = ∑ i, (D i).length
-- Spec
def EG.Spec.HccGlobStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (q : ℕ) (S : Fin q → EG.Chain.HccpData V),
    (∀ s, (S s).Valid G) →
    (∀ s s', s ≠ s' → Disjoint ((S s).beads ∪ (S s).allPathEdges) ((S s').beads ∪ (S s').allPathEdges)) →
    ∃ F : (s : Fin q) → Fin (S s).k → Finset (Sym2 V),
      (∀ s j, F s j ⊆ (S s).pathEdges j ∧ (S s).pathEdges j \ F s j ⊆ ((S s).T j).sym2) ∧
      ∃ cs : List (List V),
        EG.IsDecomp ↑(Finset.univ.biUnion fun s => (S s).beads ∪ Finset.univ.biUnion (F s)) (cs.map EG.Obj.cycle) ∧
        cs.length ≤ ∑ s, (S s).Phi0      -- Phi0 := common padded load (Phi at index 0; 0 if k = 0)
-- SUPERSEDED (P2-D [chain] fix round 1): there is no `Phi0` accessor. Use the ∃-form
--   ∃ Φ : Fin q → ℕ, (∀ s j, (S s).Phi j = Φ s) ∧ ... ∧ cs.length ≤ ∑ s, Φ s
-- (Φ s is unique since k ≥ 1: EG.Chain.HccpData.eq_of_forall_Phi_eq).
```

**hazards:**

- **[risk] GLOB-OUTPUT-LEVEL-HYP.** Quantifier issue: part (2) assumes that 'the edge sets they decompose (their beads together with their sets F_j) are pairwise disjoint', but the F_j are OUTPUTS of HCC-P (existentially produced), so the hypothesis refers to objects that do not exist before the lemma is applied. Decision: state (2) with INPUT-level disjointness (beads and all path edges of distinct systems pairwise disjoint), which is exactly what JS-LC Step 7 verifies (bead sets disjoint by the joint-routing claim (b); path edges disjoint within (Y,l,j) by joint routing, across j by distinct classes, across Y by E(H_Y) ⊆ E_{r(Y)}(Y); paths vs beads by s2:propStructure(iii)) and implies the output-level condition because F_j ⊆ E(P_j). This is not a weakening for any consumer.
- **[note] GLOB-NO-VERTEX-DISJ.** Correct and important: HCC-P's proof uses (D) only through the potential Ψ of its own system; the union needs only edge-disjointness. The Spec must NOT add cross-system vertex conditions (JS-LC: vertices of systems of other pairs (Y',l) may lie in T_j(Y,l) and be interior path vertices).
- **[note] GLOB-FACTADD-MISCITE.** The proof cites s1:factAdd(b) (a statement about f = the MINIMUM number of objects); what is needed and used is the concatenation of given decompositions (exact count Σ a_i). The Lean proof uses an IsDecomp-concatenation Lib lemma, not factAdd.

**effort:** ~120 Lean lines, difficulty 1/5 (Concatenation lemma ~50 (list Nodup of flatMap under pairwise disjointness); part (2) from HccpStatement applied per system + concatenation ~70.).

### `s6:defDesign` — definition: designation and class data (V = ∅) (s6.tex:238)

- **Manuscript referee status:** x2
- **Formalization:** Defs: new protected file EG/Defs/Chain/Design.lean (IsDesignation, classedPorts, classDeg, mY, dStar, alphaY, Bead, gammaL, IsGiant, cAgg, cFresh, cPP) on top of the s2 run model EG/Defs/HB/Run.lean; plus Lib lemmas (unique Z_u, u ∈ V(Y(u)), r(Y(u)) ≤ l − 2, vanishing for l ≤ 2)

**Statement (precise restatement).** Fix a valid HB*^{τ+} run on G (rounds 1..R). A designation δ assigns to every round l ≥ 3, every standalone pre-part Z ∈ Std_l and every classed port u ∈ Q_Z an ancestor Y(u) = δ_l(u) ∈ anc_l(u) (its class); δ is an arbitrary function of the run only (not of any later randomness). Every classed port u of round l lies in Q_Z for exactly one Z =: Z_u ∈ Std_l, and u ∈ V(Y(u)), r(Y(u)) ≤ l − 2. For l ≥ 3, an ancestor Y of round r and a vertex h: d_{Y,l}(h) := #{edges hu ∈ E_l(Z) : Z ∈ Std_l, u ∈ Q_Z, Y(u) = Y} (= #{classed ports u of round l : Y(u) = Y, hu ∈ E_l(Z_u)}); m_{Y,l} := max_{h ∈ V(G)} d_{Y,l}(h); d*_{Y,l} := #{classed ports u of round l : Y(u) = Y, u ∈ Dup*_r}; for light Y: α_{Y,l} := max_{x ∈ S_Y} #{u ∈ V(Y) \ Dup*_r : u classed port of round l, Y(u) = Y, xu ∈ E_l(Z_u)} (0 if S_Y = ∅); Bead_{Y,l} := {hu ∈ E_l(Z) : Z ∈ Std_l, u ∈ Q_Z, Y(u) = Y, and (h ∉ Q_Z or Y(h) ≠ Y)} (an edge set); γ_l := ⌊P_{l−2}/M_l⌋; (Y,l) is giant iff some connected component of the graph Bead_{Y,l} has more than 2γ_l edges; c^agg_{h,l} := #{Y : d_{Y,l}(h) ≥ 1}; for Z ∈ Std_l and x ∈ F_Z: c_x(Z) := #{Y(u) : u ∈ Q_Z, xu ∈ E_l(Z)} (distinct classes); for u ∈ Q_Z: c_pp(u) := #{Y(v) : v ∈ Q_Z, uv ∈ E_l(Z)}. For l ≤ 2 there are no classed ports (anc_l = ∅) and all quantities are 0. All are deterministic functions of (run, δ).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| valid run; rounds; R | Run V, run.Valid G D, run.R | s2:defHBtp | no: planned EG/Defs/HB/Run.lean (s2a blueprint: EG.HB.Run, Run.Valid) |
| round-l pre-parts, Z^0, Std_l, S_Z, D_l, E_l(Z), G_l, Dup*_l | run.prePartAddrs G l, run.Z0 G l a, run.Std G l, run.guests G l a, run.D G l, run.E G l a, run.graph G l, run.DupStar G l (pre-parts identified by (round, address)) | s2:defHBtp (R3)-(R5) | no: planned (s2a) |
| ancestors, V(Y), r(Y), anc_l(x) | ancestor = (round r, pre-part address a) with V(Y) = run.ancVerts G r a (Y^0 \ S_Y if light, Y^0 if standalone); anc_l(x) = {(r,a) : r ≤ l − 2, x ∈ V(Y)} | s2:defAncestors | no: planned (s2a: run.anc G l x : Finset (ℕ × List Bool), run.ancVerts) |
| hubs A_Z, ports U_Z, fresh F_Z, classed Q_Z | Z^0 ∩ D_l; Z^0 \ D_l; {x ∈ U_Z : anc_l(x) = ∅}; U_Z \ F_Z | s2:defAncestors | no: planned (s2a: run.hubs/ports/fresh/classed) |
| P_l, M_l | P_l = ⌈λ_l^{C'}⌉, M_l = max(2^40, 2^16 t d log^4(t d)) (integer or real: s2a blocker HB-M-INTEGER) | s2:defHBtp (R2) | no: planned (s2a: POf, MOf) |
| designation δ | δ : ℕ → V → ℕ × List Bool with IsDesignation: ∀ l ≥ 3, ∀ a ∈ Std l, ∀ u ∈ classed l a, δ l u ∈ anc l u | s6:defDesign | no: new EG.Chain.IsDesignation |
| connected components of an edge set | as in s6:lemPAR (edgeComps, compEdges) | s6:lemPAR / new Defs/Components.lean | no: new (shared with PAR) |

**deps_declared** (manuscript \deps): `s2:defAncestors`, `s2:defHBtp`

**deps_from_proof:** s2:defAncestors, s2:defHBtp, s2:propStructure — The claim 'every classed port lies in Q_Z for exactly one Z (port sets of one round are disjoint)' is s2:propStructure(iv) (or directly: U_Z = Z^0 \ D_l and D_l = vertices in ≥ 2 pre-parts). The extractor (ms_deps_v6.json) attributes s1:condGamma and s2:lemTower to this node: those references belong to the unlabelled log* facts (s6.tex:262-295: (s6:eqTowerHalf), (s6:eqTowerEnd) and their proof), which are used by s6:thmCONC and s6:thmCONCL, not by the definition.

**used_by:** s6:thmCONC; s6:thmCONCL; s6:defLending; s6:lemLost; s6:lemJSLC; s6:lemJplus; s6:thmMIXC; s7:defCand; s7:lemPay (c^agg, d_{Y,l}); s7:lemEXprime (Σ_h c^agg ≤ 1.37 n M_l); s7:thmMainProof (existence of a designation)

**randomness:** none. δ is deterministic given the run; s6:lemLost and s7:lemEXprime rely on δ (and the weights c^agg) being independent of the stage-1 labels and pools: in Lean δ is a parameter fixed before any FinDist is formed.

**lean_shape:**

```lean
-- EG/Defs/Chain/Design.lean   (run : EG.HB.Run V) (G : EG.FGraph V); ancestors are (r, a) : ℕ × List Bool
abbrev EG.Chain.Anc := ℕ × List Bool
def EG.Chain.IsDesignation (run) (G) (δ : ℕ → V → Anc) : Prop :=
  ∀ l, 3 ≤ l → ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a, δ l u ∈ run.anc G l u
def classedPorts run G l : Finset V := (run.Std G l).biUnion (run.classed G l)
def classDeg run G δ (Y : Anc) l (h : V) : ℕ :=   -- d_{Y,l}(h), counted by ports u (G simple)
  ((run.Std G l).biUnion fun a => (run.classed G l a).filter fun u => δ l u = Y ∧ s(h, u) ∈ run.E G l a).card
def mY run G δ Y l : ℕ := G.verts.sup (classDeg run G δ Y l)
def dStar run G δ Y l : ℕ := ((classedPorts run G l).filter fun u => δ l u = Y ∧ u ∈ run.DupStar G Y.1).card
def alphaY run G δ Y l : ℕ := (run.guests G Y.1 Y.2).sup fun x =>
  ((run.ancVerts G Y.1 Y.2 \ run.DupStar G Y.1).filter fun u => δ l u = Y ∧
     ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ s(x, u) ∈ run.E G l a).card
def Bead run G δ Y l : Finset (Sym2 V) := (run.Std G l).biUnion fun a => (run.E G l a).filter fun e =>
  ∃ h u, e = s(h, u) ∧ u ∈ run.classed G l a ∧ δ l u = Y ∧ (h ∉ run.classed G l a ∨ δ l h ≠ Y)
def gammaL run G l : ℕ := ⌊(POf (run.d G (l - 2)) : ℝ) / MOf (run.d G l)⌋₊
def IsGiant run G δ Y l : Prop := ∃ C ∈ EG.edgeComps (Bead run G δ Y l), 2 * gammaL run G l < (EG.compEdges _ C).card
def cAgg run G δ (h : V) l : ℕ := ((run.ancestorsUpTo G (l - 2)).filter fun Y => 1 ≤ classDeg run G δ Y l h).card
def cFresh run G δ l a (x : V) : ℕ := (((run.classed G l a).filter fun u => s(x, u) ∈ run.E G l a).image (δ l)).card
def cPP run G δ l a (u : V) : ℕ := (((run.classed G l a).filter fun v => s(u, v) ∈ run.E G l a).image (δ l)).card
```

**hazards:**

- **[risk] DES-RUN-MODEL.** Every quantity is defined on top of the s2 data model (pre-parts by (round, address), Std, D_l, anc, classed ports, E_l(Z), G_l, Dup*, guests, P, M). Design.lean cannot be written or locked before EG/Defs/HB/Run.lean (s2a: HB-DATAMODEL, HB-ADDRESS-IDENTITY, and the BLOCKER HB-M-INTEGER, which enters here through γ_l = ⌊P_{l−2}/M_l⌋ — harmless either way with Nat.floor, but the M_l type must be fixed first). The ancestor type (ℕ × List Bool, with light/standalone derived) is a cross-chunk type shared with s3:defCOL (classes per ancestor), s5, s6:defLending and s7 (H_{Y(u)}); it must be decided once.
- **[note] DES-CLASS-DEPENDS-ON-ROUND.** The notation Y(u), Z_u, r(u) suppresses the round l; a vertex may be a classed port in several rounds with different classes. δ must be indexed by l (δ : ℕ → V → Anc), and every consumer must pass l.
- **[note] DES-DELTA-TOTAL.** δ is a total function in Lean; values off the classed ports of round l are junk and unconstrained. All definitions filter by classed ports first. Existence of a designation (s7:thmMainProof) follows from anc_l(u) ≠ ∅ for classed u (definition of F_Z) by Classical.choice; 'a fixed rule' is not needed.
- **[note] DES-DETERMINISTIC.** 'δ is any deterministic function of the run': in Lean δ is a parameter quantified BEFORE the stage-1 FinDist; consumers (s6:lemLost(i): 'the designation is deterministic, so Y is fixed'; s7:lemEXprime: weights ω_l = c^agg are independent of pool labels) then hold automatically. A formalization that lets δ depend on stage-1 data would break these.
- **[note] DES-UNIQUE-Z.** 'Every classed port lies in Q_Z for exactly one Z' is a lemma (from U_Z = Z^0 \ D_l and D_l = {v in ≥ 2 pre-parts}; s2:propStructure(iv)), not definitional. Avoid a function Z_u in Defs: use ∃ a ∈ Std, u ∈ classed a ∧ … (as in alphaY), and prove uniqueness in Lib.
- **[note] DES-COUNT-EDGES-VS-PORTS.** d_{Y,l}(h) counts EDGES hu; the Lean definition counts ports u. At fixed h, u ↦ s(h,u) is injective and each edge lies in at most one E_l(Z) (R5 assigns each edge once), so the two agree; document in the docstring and prove the equivalence lemma (needed by s7:lemEXprime's double counting Σ_h c^agg ≤ Σ_Z Σ_{u ∈ Q_Z} deg_{E_l(Z)}(u)).
- **[note] DES-BEAD-CLAUSE-VACUOUS.** In Bead_{Y,l} the clause 'h ∉ Q_Z or Y(h) ≠ Y' is always true: if h ∈ Q_Z with Y(h) = Y then both ends lie in V(Y) and hu ∈ E(G_l) with l > r(Y), contradicting s2:lemEL. Keep the literal clause (faithful); JS-LC Step 3 does not rely on it.
- **[note] DES-L-RANGE.** The quantities must vanish for l ≤ 2 (anc_l = ∅) and for l > R (the data model must give Std_l = ∅ and E_l(·) = ∅ beyond the last round; s2a's Run defines rounds by list index, so out-of-range rounds need an explicit convention). s6:thmCONC(ii) 'for every l' and the sums in (iii) depend on this.
- **[note] DES-GAMMA-INDEX.** γ_l uses P_{l−2}: for l ≥ 3 the ℕ-subtraction l − 2 ≥ 1 is fine; for l ≤ 2 the value is junk and unused. P and M are functions of d_{l−2}, d_l (s2a POf, MOf).
- **[note] DES-ALPHA-LIGHT-ONLY.** α_{Y,l} is defined for light Y only; the Lean definition is total (for standalone Y the guest set used is the pre-part's S_Y, which is meaningless but unused). Consumers (s6:thmCONCL) must only read it for light Y.
- **[note] DES-CLASS-COUNTS-USE.** c^agg_{h,l} is load-bearing downstream (s7:lemPay (a2), s7:lemEXprime); c_x(Z) and c_pp(u) enter only (eqJbound), which the manuscript says is not used later. c^agg ranges over ancestors of rounds ≤ l − 2 (a finite set); cAgg needs a Finset of all ancestors up to a round (run.ancestorsUpTo).
- **[note] DES-EXTRACTOR-MISATTRIBUTION.** ms_deps_v6.json lists s1:condGamma and s2:lemTower as undeclared references of this definition; they come from the log* facts (s6.tex:262-295), which usesgen attaches to the preceding environment. Attach them to s6:thmCONC / s6:thmCONCL instead (they are proof ingredients of both).

**effort:** ~300 Lean lines, difficulty 3/5 (~12 definitions (~120 lines) + Lib API (unique Z_u, u ∈ V(Y(u)), r(Y(u)) ≤ l − 2, vanishing for l ≤ 2 and l > R, edge-vs-port count, Bead clause vacuous via EL) ~180. Blocked on EG/Defs/HB/Run.lean.).

### `s6:thmCONC` — theorem: Theorem CONC (standalone ancestors) (s6.tex:297)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/Chain/CONC.lean: ConcIStatement, ConcIIStatement, ConcIIIStatement ((iv) is meta: no statement); Lib: log* API and the tower facts (s6:eqTowerHalf, s6:eqTowerEnd) in EG/Lib/Found/LogStar.lean; shared summation lemmas conc_tau_sum, conc_dstar_sum (reused by s6:thmCONCL(iv))

**Statement (precise restatement).** Constants: σ = 100, ε = 2^-5, C' = 103; log = log_2; log* x = least k ≥ 0 with log^[k] x ≤ 1. Standing hypotheses (implicit in 'every valid run'): D* satisfies (Γ1) (hence (Γ2)(a)); the run is a valid HB*^{τ+} run on G with n = |V(G)| (and whatever the s2 Specs of propOrigin/propOV/lemTower require, e.g. d_1 ≥ D*; n ≥ N0 only if those Specs require it). (i) For every round r ≤ R, every Y ∈ Std_r, every round l with r + 1 ≤ l (≤ R + 1) and every vertex h: #{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l)} ≤ τ_r − 1. (ii) For EVERY designation δ, every r, every Y ∈ Std_r and EVERY l: m_{Y,l} ≤ τ_r − 1 + d*_{Y,l}. (iii) For every designation δ: Σ_{r ≤ R} Σ_{Y ∈ Std_r} Σ_{l} m_{Y,l} ≤ 2^{σ+14} n log* D*/log D* + 100 ε n log* D*/(C' log log D*) (only l with max(3, r+2) ≤ l ≤ R contribute). (iv) (i)-(iii) hold for every designation, including designations mixing light and standalone classes (meta-statement; automatic from the universal quantification over δ). Auxiliary facts proved in the text before the theorem (s6.tex:262-295): with a(d) := (2 log* d + 2)/log d, b(d) := (2 log* d + 1)/log log d, c(d) := (2 log* d + 1)/(log d)^{1/2} for d ≥ D*: (eqTowerHalf) a(d_r) ≤ a(d_{r+1})/2, b(d_r) ≤ b(d_{r+1})/2, c(d_r) ≤ c(d_{r+1})/2 for r < R; (eqTowerEnd) a(d) ≤ (2k*+4)/log D*, b(d) ≤ (2k*+3)/log log D*, c(d) ≤ (2k*+3)/(log D*)^{1/2} for d ≥ D*, where k* := log* D* ≥ 6.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| valid run, Std_r, Y^0, Dup*_r, G_l, τ_r, P_r, d_r, λ_r, R | s2 run model (run.Std, run.Z0, run.DupStar, run.graph, tauOf (run.d G r), POf, run.d, run.R) | s2:defHBtp | no: planned EG/Defs/HB/Run.lean (s2a) |
| designation, m_{Y,l}, d*_{Y,l} | IsDesignation, mY, dStar | s6:defDesign | no: new EG/Defs/Chain/Design.lean |
| log*, tower T_k | logStar x := Nat.find (∃ k, log^[k] x ≤ 1) on reals; T_0 = 1, T_{k+1} = 2^{T_k}; lemma log* x ≤ k ↔ x ≤ T_k (x ≥ 1) | s1:convGraphs (s1.tex:518) | no: planned EG.logStar (s1 blueprint CONV-LOGSTAR) |
| a, b, c (tower functions) | towerA d := (2 logStar d + 2)/logb 2 d; towerB d := (2 logStar d + 1)/logb 2 (logb 2 d); towerC d := (2 logStar d + 1)/√(logb 2 d) | s6.tex:266-269 | no: new Lib (EG/Lib/Found/LogStar.lean) |
| (Γ1) core items (a),(b) | ∀ μ ≥ log log D*: μ ≥ 2^8 and 2^μ ≥ 2^14 A μ^3 | s1:condG1 | no: planned EG.Gamma1core (s1 blueprint) |
| constants σ, ε, C', A | 100, 2^-5, 103, 105 | s1:defConstants(i) | no: planned EG/Defs/Constants.lean |

**deps_declared** (manuscript \deps): `s2:propOrigin`, `s2:lemTower`, `s2:propOV`, `s2:lemLacunary`, `s6:defDesign`, `s2:defHBtp`, `s1:condG1`

**deps_from_proof:** s2:defHBtp, s2:defAncestors, s2:propOrigin, s2:lemTower, s2:propOV, s2:lemLacunary, s6:defDesign, s1:condG1, s1:convGraphs, s2:propStructure — (i): (R1),(R5) of s2:defHBtp (or s2:propStructure(iii)) for E(G_l) ⊆ E(G_{r+1}); s2:propOrigin(a) (standalone Y has no (α) edges) and (b) (≤ τ_r − 1 (β) edges). (ii): s6:defDesign (u ∈ V(Y(u)) = Y^0 for standalone Y, s2:defAncestors), simplicity of G (s1:convGraphs: distinct edges hu at fixed h have distinct u). (iii) τ-term: s2:lemTower(a) (R − r ≤ 2 log* d_r + 2), s2:propOV(K1) (|Std_r| ≤ 1.37 n/P_r), s2:lemTower(c) (τ_r/P_r ≤ 2^{σ+11}/λ_r), (eqTowerHalf) + s2:lemLacunary(i), (eqTowerEnd), k* ≥ 6; d*-term: injectivity u ↦ (Y(u), u), s2:propOV(K3) (Σ_Y |Y^0 ∩ Dup*_r| ≤ 16 ε n/log P_r), P_r = ⌈λ_r^{C'}⌉ (R2) so log P_r ≥ C' log λ_r, s2:lemTower(a) (R − r − 1 ≤ 2 log* d_r + 1). The tower facts use (Γ1)(a),(b) at μ ∈ {log λ_{r+1}, log log D*, log D*} and s2:lemTower(a) (λ_r ≥ d_{r+1}^{1/A}). Undeclared: s2:defAncestors, s1:convGraphs, (optionally) s2:propStructure(iii).

**used_by:** s6:thmCONCL (τ- and d*-term computations 'verbatim'; (ii) for standalone ancestors; GC-parts); s1:condGamma (Γ4 via ε_CONC, through s6:thmCONCL(iv))

**randomness:** none (deterministic, for every valid run and every designation)

**lean_shape:**

```lean
-- EG/Spec/Chain/CONC.lean   (hyp bundle H := Gamma1core D ∧ run.Valid G D ∧ <whatever s2:propOrigin/propOV/lemTower Specs require>)
def EG.Spec.ConcIStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (D : ℝ) (run : EG.HB.Run V), EG.Gamma1core D → run.Valid G D →
    ∀ r a, a ∈ run.Std G r → ∀ l, r + 1 ≤ l → l ≤ run.R + 1 → ∀ h : V,
      ((run.Z0 G r a \ run.DupStar G r).filter fun u => s(h, u) ∈ (run.graph G l).edges).card ≤ tauOf (run.d G r) - 1
def EG.Spec.ConcIIStatement : Prop := ∀ … (δ : ℕ → V → ℕ × List Bool), EG.Chain.IsDesignation run G δ →
    ∀ r a, a ∈ run.Std G r → ∀ l, EG.Chain.mY run G δ (r, a) l ≤ tauOf (run.d G r) - 1 + EG.Chain.dStar run G δ (r, a) l
def EG.Spec.ConcIIIStatement : Prop := ∀ … δ, EG.Chain.IsDesignation run G δ →
    (∑ r ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G r, ∑ l ∈ Finset.Icc 1 run.R, (EG.Chain.mY run G δ (r, a) l : ℝ)) ≤
      (2 : ℝ) ^ (EG.sigmaC + 14) * G.card * EG.logStar D / Real.logb 2 D +
      100 * EG.epsC * G.card * EG.logStar D / ((EG.Cp : ℝ) * Real.logb 2 (Real.logb 2 D))
-- Lib (EG/Lib/Found/LogStar.lean, EG/Lib/Chain/Conc.lean)
theorem towerA_half (hΓ : Gamma1core D) (hv : run.Valid G D) (hr : r < run.R) : towerA (d r) ≤ towerA (d (r+1)) / 2  -- same for B, C
theorem towerA_end (hΓ : Gamma1core D) (hd : D ≤ d) : towerA d ≤ (2 * logStar D + 4) / logb 2 D           -- same for B, C
theorem logStar_ge_six (hΓ : Gamma1core D) : 6 ≤ logStar D
theorem conc_tau_sum / conc_dstar_sum : generic sums over a family of ancestors with ≤ 1.37 n / P_r per round
```

**hazards:**

- **[risk] CONC-IMPLICIT-HYPS.** 'For every valid HB*^{τ+} run' hides hypotheses: the proof uses s2:lemTower(a),(c) (stated for valid runs with d_1 ≥ D*, under (Γ1),(Γ2)), s2:propOV(K1),(K3) and s2:propOrigin (whose proofs use s2:propStructure, stated for n ≥ N0 and d_1 ≥ D*), and the tower facts use (Γ1)(a),(b). The Lean Specs must carry exactly the hypothesis bundle of those s2 Specs (at least Gamma1core D ∧ run.Valid G D); if the s2 blueprint's Specs assume n ≥ N0, so must CONC, and then s6:thmCONCL/s6:thmMIXC/s7 must supply it. Mismatch across chunks would make CONC unprovable or unusable; decide the bundle once (P2-D). (When d_1 < D*, R = 0 and (ii),(iii) are trivial.)
- **[risk] CONC-TOWER-FACTS.** (s6:eqTowerHalf) and (s6:eqTowerEnd) are proved in an unlabelled proof block before the theorem and need real analysis not yet in EG: a log* definition on ℝ with log* x ≤ k ↔ x ≤ T_k and log* x = 1 + log*(log x) for x > 1; log* x ≤ 1 + log x for x ≥ 1 (case x ≤ 4 by inspection, then induction); monotonicity of t ↦ (2 log t + 6)/t, (7 + 2 log t)/t, (2 log t + 5)/t^{1/2} on t ≥ 4; and (Γ1)(a),(b) at μ = log λ_{r+1}, log log D*, log D*. I re-derived every inequality (2^{y/(2A)} ≥ 2^{4+2v} = 16y², y(2y/A+6) ≤ 8y² ≤ 2^{y/A}, 2y^{1/2}(2y/A+5) ≤ 14y^{3/2} ≤ 2^{y/(2A)}, A(7+2 log y)/y ≤ 1/(2 log y) from y ≥ 2Av(7+2v), both cases of (eqTowerEnd) including t(2t+6) ≤ 2^t and t(2t+5)² ≤ 2^t, k* ≥ 6 from log log D* ≥ 2^8 ⇒ D* > T_5): all correct. The effort is the Lean real-analysis bookkeeping (~300 lines), shared with s6:thmCONCL.
- **[note] CONC-ROUND-RANGE.** (i) quantifies over l ≥ r + 1 but G_l exists only for l ≤ R + 1 (the procedure stops at R + 1); restrict to l ≤ R + 1 or define G_l for l > R + 1 in the data model (e.g. constant). (ii) 'for every l' and the sum in (iii) rely on m_{Y,l} = 0 for l ≤ r + 1 (anc_l requires r ≤ l − 2), for l ≤ 2, and for l > R (needs Std_l = ∅ beyond R in the data model; see DES-L-RANGE).
- **[note] CONC-SUM-INDEX.** 'Σ over pairs (Y,l) with Y standalone' must be a finite sum over an explicit index set: Σ_{r ∈ [1,R]} Σ_{a ∈ Std r} Σ_{l ∈ [1,R]} (equivalently [max(3,r+2), R]). Ancestors are addresses, so distinct pre-parts with equal vertex sets are counted separately (as the manuscript intends: 'distinct ancestors of round r have distinct pre-parts').
- **[note] CONC-SHARED-COMPUTATION.** s6:thmCONCL(iv) reuses 'the computation in the proof of CONC(iii) verbatim' for ALL ancestors (light and standalone; the number of ancestors of round r is ≤ 1.37 n/P_r by (K1)) and the d*-injectivity argument. Formalize the two sums as Lib lemmas over an arbitrary per-round family of ancestors with a cardinality bound, and derive CONC(iii) and CONC-L(iv) from them; do not prove the chain twice.
- **[note] CONC-IV-META.** (iv) is a meta-statement ('nothing used how δ chooses'); in Lean it is automatic because (ii),(iii) quantify over every δ with IsDesignation. No separate statement; mention in the docstring.
- **[note] CONC-NAT-SUB.** τ_r − 1 is ℕ-subtraction; τ_r = ⌈128 s_r log² M_r⌉ ≥ 1, so no truncation occurs (keep a lemma 1 ≤ tauOf d). The real inequality (iii) needs casts; the constants 1.37·16/3 < 8, 2k+4 ≤ 8k/3 and 2k+3 ≤ 2.5k (k ≥ 6), 32·2.5 = 80 ≤ 100 are norm_num facts.
- **[note] CONC-LOG-JUNK.** log log D* and log* D* are real expressions with Real.logb junk values for arguments ≤ 1; (Γ1) gives log log D* ≥ 2^8, so all logs are positive. The tower facts must be stated for d ≥ D* only (they are false for small d).
- **[note] CONC-II-SIMPLE.** (ii) splits the edges counted in d_{Y,l}(h) into u ∉ Dup*_r (≤ τ_r − 1 by (i), since E_l(Z) ⊆ E(G_l) and u ∈ V(Y) = Y^0) and u ∈ Dup*_r (distinct ports u, counted by d*_{Y,l}); with the port-counting definition of classDeg (DES-COUNT-EDGES-VS-PORTS) this is a Finset.card_union_le split, no simplicity argument needed.

**effort:** ~750 Lean lines, difficulty 3/5 ((i) ~60 from propOrigin; (ii) ~80; (iii) τ-sum ~150, d*-sum ~150 (both as shared Lib lemmas); log* API + tower facts ~300 (shared with CONC-L); Spec ~40. Blocked on the s2 Specs (propOrigin, propOV, lemTower, lemLacunary) and the s2 run model.).
