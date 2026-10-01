# P2-U formalization blueprint: chunk s2a (s2: witnesses, tau-rules, SEP, thin cut, OV, Lemma 14^tau, the hierarchy HB*^{tau+}, ancestors, size cap, Lemma HS)

Manuscript: `proofs/manuscript/s2.tex` lines 1-708 (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s2a.json` (same content, one object per label, same field names as `nodes_s1.json`). Line numbers refer to `s2.tex`. Lean names in `code` that already exist were checked against `formal/EG/**` (EG.FGraph, EG.FGraph.IsExpander, EG.Obj, EG.cycleEdges, EG.degE, EG.Spec.CapStatement/CapUniformStatement/CapGraphStatement, EG.cap, EG.cap_graph); all other names are proposals. No node of this chunk involves randomness: a valid run is a deterministic object built from arbitrary choices, and 'any witnesses / orders' is universal quantification over `Run.Valid`.

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s2:defWitness` | definition | Defs (IsWitness, witN, witF0) + Spec | 120 | 1 | note (WIT-EPS-PARAM) |
| `s2:defTauRules` | definition | Defs (split constructors, tau-rule sets) + Spec (Facts, eqSplit) | 250 | 2 | note (TAU-DEFINE-BY-EQSPLIT) |
| `s2:lemSEP` | lemma | Defs (split trees, addresses, graft) + Spec | 900 | 3 | risk (SEP-TREE-INFRA) |
| `s2:lemThinCut` | lemma | Spec | 200 | 2 | note (THIN-CEIL-FORM) |
| `s2:lemOVgeneric` | lemma | Defs (IsS0Rec, DeltaGe, dupGe, cOV) + Spec | 500 | 3 | risk (OV-CONST-546) |
| `s2:lem14tau` | lemma | Defs (IsTauRun) + Spec in 6 parts | 750 | 3 | risk (LEM14-TERMINATION) |
| `s2:defHBtp` | definition | Defs (Run, RoundChoice, Run.Valid) + Run API | 1100 | 4 | blocker (HB-M-INTEGER) |
| `s2:defAncestors` | definition | Defs (in Run.lean) | 250 | 2 | risk (ANC-ROUND-OFFSET) |
| `s2:lemCap` | lemma | (i)+remark: existing Spec, proved; (ii): new CapRunStatement | 250 | 2 | risk (CAP-L25-CONST) |
| `s2:lemHS` | lemma | Spec | 150 | 2 | note (HS-NUMERIC) |

Estimated new Lean for this chunk: **~4470 lines** (s2:lemCap(i), its remark and graph step already exist: ~330 lines, not counted). One **blocker** (HB-M-INTEGER: M_l is a real in (R2) but an integer at its uses in s3/s6/s7) needs a manuscript decision before `EG/Defs/HB/Run.lean` is locked; the proposed fix (ceiling) was checked against every s2 inequality involving M_l and has ample slack. The mathematics of the ten statements was re-derived and found correct as stated (modulo the implicit hypotheses listed); the main risks are the size of the data model (split trees with addresses and grafting; the round recursion) and two thin numerical margins (OV/14^tau constant 5.46 needs log_2(4/3) >= 0.414508; lemCap(i) rests on the unproved constant 18 of B-M Lemma 25).

## 2. Cross-cutting decisions proposed for the integrator

- **M_l must be an integer (blocker HB-M-INTEGER).** Proposed manuscript change to (R2): M_l := ⌈max(2^40, 2^16 T_l log^4 T_l)⌉ ∈ ℕ, Λ_l := log_2 M_l. Uses that need it: [4M_l] colour sets and random bijections in s7 (K^HUB_l = 4M_l), K^JS_l = M_l^2 classes in s3:defCOL, 'M_l - 1 cherry systems' in s6:lemJSLC. s2 impact checked: lemCap(ii) unchanged; M_l <= d_l^2, M_l <= (A log λ_{l-2})^{2A}, M_{l-1} >= 2M_l, Σ1/M_l <= 2/D_*, P_{l-2}/2 >= M_l log^4 M_l keep large slack. Fallback without manuscript change: ceilings at each use (K^HUB := ⌈4M_l⌉, K^JS := ⌈M_l^2⌉) and a +M_l^-4 term in s6:lemLost(i).
- **Split trees (P2-D).** `EG.HB.STree V := BinaryTree (Finset V × Finset V)` (Mathlib `BinaryTree`, formerly `Tree`): `nil` = leaf, `node (U', N'') t₁ t₂`. Graphs are computed from the root graph (choices only, PLAN §3 decision 5) by the shared constructors `splitFst`/`splitSnd`/`splitDel` (the (eqSplit) forms), used by BOTH levels. Nodes are addressed by `List Bool` (false = first child); ancestors = prefixes; a total `graphAtD`; `leafAddrs`, `internalAddrs`, `dup`, `deleted`, `leafMass`, `DeltaGe`, `dupGe`, `graft`. Leaves, pieces, pre-parts and ancestors are identified by ADDRESS (SEP-LEAF-IDENTITY, HB-ADDRESS-IDENTITY): every s2-s7 Spec indexes parts by (round, address).
- **Witnesses and tau-rules.** `IsWitness H ε s U F` is literally the negated body of `IsExpander`; tau-rule sets are functions of `(H, U, N, τ)` (makes RT2-I7 definitional); `ε` is a parameter, instantiated at `2^(-5:ℤ)`. Validity predicates: `IsS0Rec`, `IsTauSplitTree`, `IsTauRun` (leaf ⇔ expander; internal ⇒ tau-rule split of a witness).
- **The run.** `Run V := List (RoundChoice V)` with `RoundChoice = {cycles, tree0, tauRun : List Bool → STree V, homeOrder}`; `Run.Valid G D_* run : Prop`; every round object is an `irreducible_def` of `(run, G, l)` with characterization lemmas. (R1) encoded as any maximal family of edge-disjoint long cycles (HB-R1-ENCODING). (R5)(3) uses the home order (HB-R5-ORDER, decision needed). Rounds are 1-indexed; write `r + 2 ≤ l` (ANC-ROUND-OFFSET). Valid never presupposes the hypotheses of Lemma 14^tau (no circularity; trees are finite by construction).
- **Termination.** 'For every choice of witnesses the recursion terminates' = (T1) strict size decrease at every tau-split under τ >= 128 s log^2 |H| + (T2) existence of a tau-run; 'for every choice' = ∀ trees with `IsTauRun` (LEM14-TERMINATION).
- **Constants.** Prove OV(a) in its sharp form (with c_OV = log_2(4/3)) and derive 3.42 (needs log_2(4/3) >= 12/29, 2^46 >= 3^29) and 5.46 (needs >= 17/41, 2^65 >= 3^41; 12/29 is NOT enough). All other constants (1.12, 1.21, 0.698, 127/128, 2/5, 1/10, log_2 11 >= 3.45) are small rational checks.
- **Γ hypotheses.** s2 statements in this chunk take only D_* >= 2^117 (lemCap(ii)); nothing here uses Γ1. (s1 blueprint decision: s2 statements take only the Γ items they cite.)
- **Modules.** Defs: `EG/Defs/HB/Witness.lean` (IsWitness, witN, witF0, split constructors, tau-rule sets), `EG/Defs/HB/SplitTree.lean` (STree API, IsS0Rec, IsTauSplitTree, IsTauRun, DeltaGe, dupGe, cOV), `EG/Defs/HB/Run.lean` (constants-as-functions, RoundChoice, Run, derived objects, ancestors, Valid). Specs: `EG/Spec/HB/{Witness, SplitTree, Overlap, Lemma14Tau, Cap, HS}.lean` (Cap.lean exists; add CapRunStatement).
- **Undeclared dependencies found in proofs** (for `usesgen`/msreport): s2:lemCap uses s2:lemSEP (node graphs ⊆ root) and s1:citDef11; s2:lemOVgeneric's instance remark uses s2:defTauRules; s2:defHBtp uses s2:defWitness, s2:defTauRules, s1:citDef11, s1:defObject. Declared but not logically used: s1:citLem14 (in OV, 14^tau, defHBtp: attribution), s1:defConstants (in defWitness), s2:lem14tau (in lemCap: conclusion pointer).

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| blocker | `s2:defHBtp` | HB-M-INTEGER | Definition-vs-use mismatch. (R2) defines M_l := max(2^40, 2^16 T log^4 T) with T = d_l log^2 d_l, an irrational REAL in general. Downstream uses need an INTEGER: s7 (s7.tex:183-184, 270, 280-297, 518) uses the colour set [4M_l] = [K^HUB_l] with uniformly random bijections [4M_l] → [4M_l] and 3-subsets of [4M_l]; s3:defCOL (s3.tex:1045, 1072) uses K^JS_l := M_l^2 as the NUMBER of JS classes (0 <= j < K^JS_l) and the probability K^JS_l rho_l = M_l^-2; s6:lemJSLC counts 'M_l - 1 cherry systems' and pads with ⌈(M_l-1)/2⌉. A Lean statement of (R2) must choose. Proposed manuscript decision: M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ (a natural number), with Lambda_l := log_2 M_l of that integer. Checked impact in s2: lemCap(ii) (\|Q\| <= 2^16 T log^4 T <= M_l) unaffected; propDegRec M_l <= d_l^2 (2^20 x^6 2^x + 1 <= 2^{2x}, huge slack); lemTower(b) M_l <= (A log lambda_{l-2})^{2A}, M_{l-1} >= 2M_l, Σ 1/M_l <= 2/D_*, P_{l-2}/2 >= M_l log^4 M_l all have factor-level slack; K^JS_l rho_l = M_l^-2 then holds exactly. Alternative (no manuscript change): keep M_l real and put ceilings at every use (K^HUB_l := ⌈4M_l⌉, K^JS_l := ⌈M_l^2⌉), which changes K^JS rho_l to <= M_l^-2 + M_l^-4 in s6:lemLost(i) (absorbed by the slack of 2\|V(Y)\|^-2). Either way the choice must be made before EG/Defs/HB/Run.lean is locked. |
| risk | `s2:lemSEP` | SEP-TREE-INFRA | Split trees with addresses, prefix order, 'deepest ancestor containing h', 'path child', lowest common ancestor (propOV(K3)) and grafting (the two-level recursion) are new foundations with no Mathlib counterpart beyond BinaryTree. Every counting lemma of s2 (SEP, thin cut, OV, 14^tau, propOV, propDegRec, propOrigin) and s6:thmCONCL rests on them. This is the main P2-D data-model decision for s2 (not a manuscript decision): recommend BinaryTree (Finset V × Finset V) + List Bool addresses + a total graphAtD, with a library of 'induction along an address' lemmas. Estimated 400 lines before SEP itself. |
| risk | `s2:lemSEP` | SEP-LEAF-IDENTITY | 'Distinct leaf nodes are distinct leaves even if their vertex sets coincide' forces leaves (hence pieces, pre-parts, ancestors) to be identified by ADDRESS, never by vertex set or graph. Dup counts leaf addresses. If any later Spec quantifies over 'pre-parts' as a Finset of vertex sets or FGraphs, D_l, home, S_Z and all counts (K1)-(K3) change meaning. All s2-s7 Specs must index parts by (round, address). |
| risk | `s2:lemOVgeneric` | OV-CONST-546 | Constants: 1 + 1/c_OV = 3.4094... <= 3.42 needs log_2(4/3) >= 1/2.42 = 0.41322 (e.g. 12/29: 2^46 >= 3^29). But lem14tau(b)'s 5.46 = 1.6(1 + 1/c_OV) needs log_2(4/3) >= 0.414508; the bound 12/29 = 0.41379 gives 1.6(1 + 29/12) = 5.4667 > 5.46 and FAILS. Use 17/41 (2^65 >= 3^41, i.e. 3.689e19 >= 3.647e19). So (a) must be proved in its sharp first form (with c_OV) and both constants derived from it; proving only the '3.42' form would make lem14tau(b) and propOV(K2) unprovable as stated. (The true value 5.4555 has 0.08% slack.) |
| risk | `s2:lem14tau` | LEM14-TERMINATION | 'The recursion terminates ... for every choice of witnesses' is a statement about a nondeterministic procedure. Lean: (T1) strict size decrease at every tau-split under tau >= 128 s log^2 \|H\| (needs U' ≠ ∅, i.e. tau > s, AND V\(U'∪N'') ≠ ∅, i.e. the 0.698 bound), (T2) existence of a tau-run (strong induction on \|H\|), and 'for every choice' = the global conclusions hold for EVERY t with IsTauRun. With only tau > s (the defTauRules requirement) a split can have U'∪N'' = V, child 1 = H, and the procedure can loop; so Run.Valid in s2:defHBtp must not presuppose termination (trees are finite by construction) and propExists must use T1/T2 with lemCap's bound tau_l >= 128 s_l log^2 \|Q\|. |
| risk | `s2:lem14tau` | LEM14-CONST-546 | (b)'s 5.46 needs 1.6(1 + 1/c_OV) <= 5.46, i.e. log_2(4/3) >= 0.414508 (true value 0.415037; slack 0.13%). The rational bound 12/29 that suffices for OV's 3.42 is not enough (gives 5.4667). See OV-CONST-546; use 17/41 (2^65 >= 3^41). Similarly 1/(1 - 5.472 eps) <= 1/(1 - 5.5 eps) = 1.20755 <= 1.21. |
| risk | `s2:defHBtp` | HB-R5-ORDER | (R5)(3) assigns an edge 'to the first such pre-part' without naming the order ((R5)(2) says 'in the home order'). Proposed decision: the home order (the only order on pre-parts that the run fixes). Downstream uses of E_l(Z) for standalone Z (s4 TPV input, s6 beads/J-edges, lemCap degree bound, propStructure(iii) partition) use only: both ends in Z^0, disjointness across parts, E(X^0_Z) ⊆ E_l(Z); any deterministic choice works, but the Lean definition needs one. Alternative: make the step-(3) choice an extra field of RoundChoice (then 'valid run' quantifies over it). |
| risk | `s2:defHBtp` | HB-ADDRESS-IDENTITY | Pieces, pre-parts, parts and ancestors must be identified by (round, address in T_l), never by vertex set: 'distinct pre-parts are counted separately even if their vertex sets coincide', home(v) ≠ Z and S_Z compare pre-parts, and (K1)-(K3), mu_r, dup_r count leaves. Every s2-s7 Spec must index parts by addresses (e.g. Z ∈ run.Std G l : Finset (List Bool)). Two pre-parts with equal vertex sets are possible in principle (then the second has S_Z = Z^0 and is standalone by (L1)); a vertex-set encoding would merge them. |
| risk | `s2:defHBtp` | HB-DATAMODEL | Everything of round l (G_l, pieces, pre-parts, D_l, home, S_Z, light/Std, E_l(Z), G_{l+1}) is a function of (G, run, l) defined by recursion through all earlier rounds; Valid threads D_* <= d_l for l <= R and d_{R+1} < D_*. This is the largest definition of the project and all of s3-s7 read it. Needs: irreducible_def for every derived object, characterization lemmas (e.g. E_l(Z) edges lie in partVerts, (graph (l+1)).edges = passed edges, pre-part ↔ tau-run leaf inside a piece), and non-vacuity tests (a small G with R = 1 where every rule fires). Estimate 500 lines of definitions + 600 lines of API; P2-D must fix it before any s3-s7 Spec is written. |
| risk | `s2:defHBtp` | HB-GRAFT | The two-level recursion is t0_l with tau-runs grafted at big pieces. propOV applies OV to the grafted tree (first-level splits c = 1, second-level c = 1.6), propOrigin compares Dup of a tau-run with Dup*_l and needs 'u ∉ Dup*_l ⇒ unique piece', lemCap needs 'pre-part ⊆ its piece'. The graft API must give: addresses of the graft = a ++ b; graphs at a ++ b = graphs of the grafted tree at b rooted at Q_a; leaves, internal nodes, labels, Dup correspondences. Without this, three s2 propositions have no clean proof path. |
| risk | `s2:defHBtp` | HB-STOPRULE | Definition-vs-use: 'A node is a leaf iff its graph is an (eps,0)-expander': the direction 'internal ⇒ not an expander' follows from the witness required at internal nodes (s2:defWitness W0); Valid must require 'leaf ⇒ expander' explicitly (lemCap uses that pieces are (eps,0)-expanders; propStructure(i) that pre-parts are (eps,s_l)-expanders). Leaves of size < P_l that are not tau-run roots are pieces; no stopping condition at s_l for them. If Run.Valid is locked without 'leaf ⇒ (eps,0)-expander' (first level) and 'leaf ⇒ (eps,s_l)-expander' (tau-runs), lemCap(ii) and propStructure(i) become unprovable and a Tier-1 definition change is needed later. |
| risk | `s2:defAncestors` | ANC-ROUND-OFFSET | 'r(Y) <= l - 2' with ℕ subtraction, and 'anc_l = ∅ for l <= 2', silently depend on rounds being 1-indexed: with 0-indexed rounds (List index) round 0 would satisfy r <= l - 2 = 0 at l = 1, 2 and F_Z would change (fresh ports at rounds 1-2 would become classed), breaking (K4), s6:defDesign and the 338n fresh-port charge. Write the condition as r + 2 <= l with 1 <= r and add a test (anc G l x = ∅ for l ≤ 2). |
| risk | `s2:lemCap` | CAP-L25-CONST | (i) has razor-thin margins that are already machine-checked (18432·1.37317^4 = 65534.45 <= 65536; at log T = 117: 43.661 vs 43.481), but they rest on the constant 18 of the explicit B-M Lemma 25 (18432 = 18·2^10), whose Lean proof (EG.bmLemma25) is still sorry (s1 hazard L25-CONST18). If that proof only reaches a constant C > 18, (i) fails at T = 2^117. Mitigation that needs no change to M_l: for any C < 64, χ(B) >= C·2^10·T holds for B = 2^16 T log^4 T once log T >= x_0(C) (log B = log T (1 + o(1))), and T >= D_* is galactic; so Gamma2(a) would become an eventuality 'D_* >= 2^{x_0(C)}' (R6 style). For C >= 64 the factor 2^16 in (R2) must grow. |
| risk | `s2:lemCap` | CAP-GAMMA-EXPLICIT | Implicit hypothesis. (ii) says 'in every round l <= R of a valid run' with no hypothesis on D_*, but the proof needs D_* >= 2^117 (Gamma2(a)): with small D_* a piece can exceed M_l. The Spec must carry 2^117 <= Dstar (not the whole Gamma bundle; s1 blueprint decision: s2 statements take only the Gamma items they cite). |
| note | `s2:defWitness` | WIT-EPS-PARAM | The manuscript fixes eps = 2^-5 for all of s2 ('Throughout, eps = 2^-5'). The definition and the Fact are eps-independent; the Lean definition must take eps as a parameter (lem14tau, the OV instance and (R3) instantiate eps = 2^(-5:ℤ)). For eps <= 0 there is no witness (EG.FGraph.isExpander_of_nonpos), consistent with the manuscript. |
| note | `s2:defWitness` | WIT-M2-FREE | 'Then m >= 2' needs no hypothesis: \|U\| >= 1 and \|U\| <= 2m/3 give m >= 3/2. With Lean's x/0 = 0, m <= 1 also has no witness (the expansion inequality reads \|N\| < 0). Consistent with EG.FGraph.isExpander_of_card_le_one. |
| note | `s2:defWitness` | WIT-FACT-GENERAL | Fact (i),(ii) hold for every U ⊆ V(H), F ⊆ E(H); state them without the witness hypothesis (reused in s2:defTauRules(c) and nowhere does the proof need the expansion inequality). N ∩ U = ∅ is free (EG.FGraph.disjoint_nbrSet). |
| note | `s2:defWitness` | WIT-HYP-ORDER | Keep the conjuncts of IsWitness literally the negated body of IsExpander (same real casts, 2*card/3, logb 2 card ^ 2) so that WitnessIffStatement is push_neg plus reordering; a mismatch here (e.g. natural-number division 2*m/3) would silently change the definition. |
| note | `s2:defTauRules` | TAU-DEFINE-BY-EQSPLIT | The manuscript defines G_2 := H - U' - E(G_1) - F'' and then derives (eqSplit). In Lean define the children by the (eqSplit) forms (splitFst/splitSnd), shared with every split recursion (the s = 0 level uses the same constructor), and prove the literal forms as TauEqSplitStatement. Otherwise SEP, OV and the two-level recursion would need transport lemmas between two constructions. |
| note | `s2:defTauRules` | TAU-SIGNATURE-UN | Fact (c) (RT2-I7) is automatic if the tau-rule functions take (H,U,N,tau) and the witness-level split is obtained by N := witN H U F. Do not define them from F (then (c) becomes a lemma about F_0 = witF0 and must be proved). |
| note | `s2:defTauRules` | TAU-TAU-GT-S-UNUSED | tau > s only makes the rules 'defined' in the manuscript; no Fact uses it. The Lean functions are total for every real tau; for tau <= 0 they degenerate (H_out = U, U' = ∅) and termination fails (see LEM14-TERMINATION). Validity predicates (IsTauRun) carry the tau hypothesis, not the definitions. |
| note | `s2:defTauRules` | TAU-IMPLICIT-SUBSETS | U' ⊆ V(H) and N'' ⊆ V(H) are not stated in the manuscript but are needed for the split to be a SEP split (SEP requires U'_nu, N''_nu ⊆ V(H_nu)) and, in Lean, because FGraph.induce intersects with verts: without N'' ⊆ V the identity \|nu_1\| = \|U'\| + \|N''\| fails. Include them in TauFactAStatement. |
| note | `s2:defTauRules` | TAU-REALCOMPARE | deg_{F_0}(v) >= tau compares a natural number with a real; write τ ≤ ((degE F0 v : ℕ) : ℝ). In all applications tau = tau_l ∈ ℕ (ceiling in (R2)), and deg < tau ⟺ deg <= tau - 1, which is the form used in s2:lemThinCut. |
| note | `s2:lemSEP` | SEP-INCLUSION-HYP | U'_nu, N''_nu ⊆ V(H_nu) is part of the definition and must be in STree.WF: Lean's induce intersects with verts, so without it \|nu_1\| + \|nu_2\| = \|nu\| + \|N''_nu\| and the leaf-mass identity fail. |
| note | `s2:lemSEP` | SEP-MONO-IMPLICIT | The monotonicity (0') 'vertex sets shrink downwards / node graphs are subgraphs of the root' is used without citation in lemCap(ii) (piece ⊆ G'_l), propStructure(i) (X^0_Z ⊆ G'_l[Z^0]), propOV(K3), propOrigin; include it in the SEP Spec (SEPmono). |
| note | `s2:lemSEP` | SEP-I-FIRST-NODE | (i)'s phrase 'nu is the first node on the path of nodes having xy as an edge at which this happens' is formalized as: e ∈ E(H_mu) for every prefix mu of nu and e is not an edge of either child of nu. The count form '#leaves-with-e + #nodes-deleting-e = 1' captures 'exactly one of the two, exactly once'. |
| note | `s2:lemSEP` | SEP-III-DEEPEST | 'the deepest ancestor of L_u in which h lies' is well defined because the ancestors containing h form a prefix-closed chain (by (0')); in Lean define it as the longest prefix of L_u with h ∈ V(H_prefix), or quantify over any prefix with that maximality property (as in the Spec sketch) to avoid a definition. |
| note | `s2:lemThinCut` | THIN-CEIL-FORM | State the bound as the real inequality (count : ℝ) < τ; it is equivalent to count <= ⌈τ⌉ - 1 for τ > 0, and to count <= τ - 1 for integer τ (τ_r ∈ ℕ by the ceiling in (R2), which is the form propOrigin(b) and s6:thmCONCL(i) use). |
| note | `s2:lemThinCut` | THIN-UNUSED-HYPS | s_nu < tau and the witness inequality are not used; the Lean proof should go through a lemma assuming only that each split is a tau-rule split of some (U,N) (U ⊆ V(H_nu), N ⊆ V(H_nu)\U). This also covers the s = 0 first level of the two-level recursion (tau-rules at s = 0 are idle), so thin cut may be applied to the whole two-level recursion if convenient. |
| note | `s2:lemThinCut` | THIN-MOREOVER-IS-SEP | The 'Moreover' sentence is SEP(i)+(ii) and needs no tau-rules; put it in the SEP layer (ThinCutEdgeStatement holds for every split recursion). |
| note | `s2:lemThinCut` | THIN-H-ANY | 'every vertex h' ranges over all of V (h ∉ V(H_0) gives count 0); the proof's reduction 'h lies in the root' is a case split, not a hypothesis. |
| note | `s2:lemOVgeneric` | OV-A-PROOF-ROUTE | The manuscript's (a) charges (nu,u) to leaf copies, orders the charging ancestors into a chain and compares a sum with an integral. Recommended Lean route (no integrals, no chains): structural induction with the potential Phi_M(x) := [x >= M]·(1/log^2 M + 1/(c_OV log M) - 1/(c_OV log x)); claim: charges in the subtree of nu <= Σ_{leaf copies below nu} Phi_M(\|nu\|). Key facts: Phi_M(x) - Phi_M(3x/4) = 1/(log x · log(3x/4)) >= 1/log^2 x when 3x/4 >= M; Phi_M(x) >= 1/log^2 M >= 1/log^2 x when M <= x; at least \|U'_nu\| leaf copies lie below nu_1 (each u ∈ U'_nu lies in a leaf below nu_1, SEP(0)). |
| note | `s2:lemOVgeneric` | OV-INSTANCE-EPS | The instance needs eps <= 1/8 (for \|nu_1\| < (1+eps)(2/3)m <= 3m/4, using log m >= 1) and 1/(1 - 3.42 eps) <= 1.12, i.e. eps <= 0.031329; eps = 2^-5 = 0.03125 is just inside (1.11966). State the instance at eps = 2^(-5:ℤ) only. |
| note | `s2:lemOVgeneric` | OV-BM-COMMENTARY | 'This is exactly the recursion in the proof of B-M Lemma 14 with s = 0' is commentary; nothing downstream needs a Lean statement about B-M's recursion (declared dep s1:citLem14 is not logical). The tau-rules-at-s=0 identification IS worth stating (last conjunct of OVInstanceStatement) because it lets thin cut apply to the two-level recursion. |
| note | `s2:lemOVgeneric` | OV-NATSUB | (b)'s consequence 'Σ\|L\| - \|⋃V(L)\| <= Delta' must be stated additively (Σ <= \|⋃\| + Delta) to avoid ℕ truncated subtraction; M is real, \|nu\| >= M is a real comparison (M = P_r ∈ ℕ and M = 2 in applications). |
| note | `s2:lemOVgeneric` | OV-N0-POS | n_0 >= 1 is not needed (S = 0 when n_0 = 0); omit or keep, harmless. |
| note | `s2:lem14tau` | LEM14-S-GE-1 | s >= 1 is essential: at s = 0 the hypothesis allows tau = 0, then H_out = {v ∈ U : deg >= 0} = U, U' = ∅, n_2 = m (no progress). s = s_l = ⌈Λ_l^100⌉ >= 40^100 in applications. Take s : ℕ with 1 ≤ s (IsExpander gets (s : ℝ)). |
| note | `s2:lem14tau` | LEM14-IND-HYP | The inductions (deletions, leaf sizes) are over the tree with the claim for a subtree rooted at a node of size m; the hypothesis tau >= 128 s log^2 m is inherited because node sizes are <= n_0 and log is monotone on [1, ∞) (internal nodes have m >= 2). Children have sizes n_1, n_2 >= 1 (U' ≠ ∅; n_2 >= m/3), so log n_i >= 0 — needed for 2 + log n_i > 0 and for (8). |
| note | `s2:lem14tau` | LEM14-BM-BOUND-UNUSED | The B-M leaf-size bound 2n_0 - 2n_0/(2 + log n_0) (and inequality (9), 7L^2 - 3.6L - 3.2 >= 0) is not used anywhere downstream (propOV and propDegRec use (b) via OV on the composite tree, and the deletion bound). Keep it as a separate Spec conjunct/lemma so it can be deprioritized (PLAN R7 'not used' policy) without touching the used parts. |
| note | `s2:lem14tau` | LEM14-SMALL-NUMERICS | Small absolute constants to be checked by norm_num/nlinarith: 1/128 = eps/4; (1 + 3/64)(2/3) = 0.69792 <= 0.698; log_2 0.698 < -2/5 (0.698^5 = 0.1657 <= 1/4); 6 eps/log m <= 6/32 < 3/5; 3 eps = 3/32 < 1/10; 1.5·128/127 < 1.52 <= 1.6. All margins are comfortable except 0.698 (margin 1e-4 relative, still exact in ℚ). |
| note | `s2:lem14tau` | LEM14-DUP-SCOPE | Dup in (c),(d) is the Dup of THIS tau-run. In s2:defHBtp the tau-run is grafted into the two-level recursion and s2:propOrigin uses Y^0 \ Dup*_r ⊆ Y^0 \ Dup(tau-run); the graft API must provide: leaves of the graft below the piece address a ↔ leaves of the tau-run at a, with equal graphs, so Dup(tau-run) ⊆ Dup*_l. |
| note | `s2:defHBtp` | HB-R1-ENCODING | 'Delete the lexicographically first long cycle for a fixed vertex order, repeatedly' (PLAN decision 7: fixed rules become existentials). Encode Cyc_l as ANY list of pairwise edge-disjoint well-formed cycles of G_l of length >= T_l whose removal leaves no cycle of length >= T_l. This enlarges the set of valid runs (every greedy sequence qualifies), so every '∀ valid run' statement becomes stronger; the consumers (propStructure(iii): Σ\|Cyc_l\| <= n; s5/s7 treat long cycles as objects) use only edge-disjointness, length >= T_l and the absence of long cycles in G'_l. Existence is the greedy argument (propExists). |
| note | `s2:defHBtp` | HB-VALID-NO-TERMINATION | No circularity: Run.Valid does not require the hypotheses of Lemma 14^tau (tau_l >= 128 s_l log^2 \|Q\|); trees are finite by construction. Those hypotheses are consequences (lemCap(ii), needs D_* >= 2^117) used only to apply 14^tau and to prove existence (propExists). |
| note | `s2:defHBtp` | HB-L2-GRAPH | (L2) counts neighbours in G'_l[Z^0] (a supergraph of X^0_Z), (GC) in X^0_Z. Keep both graphs; replacing G'_l[Z^0] by X^0_Z in (L2) would enlarge the set of light pre-parts and change Std_l. HS is applied through X^0_Z ⊆ G'_l[Z^0] (propStructure(i)). |
| note | `s2:defHBtp` | HB-PART-OVERLOAD | The letter Z denotes a pre-part (address), Z^0, the light part's vertex set Z^0\S_Z, and the part itself; E_l(Z) belongs to the light part if Z is light. Lean: one address a, with partVerts l a := if light then Z0\guests else Z0; E l a indexed by the address. |
| note | `s2:defHBtp` | HB-REAL-NAT | Types: d_l, lambda_l, T_l, Lambda_l ∈ ℝ; s_l, P_l, tau_l, theta^GC ∈ ℕ (ceilings); s_l/2 in (L2) is real (s_l may be odd); \|S_Z\| <= \|Z^0\|/2 as 2\|S_Z\| <= \|Z^0\| in ℕ; lambda_l^{-1/2} via Real.rpow (lambda_l > 1 under Gamma). d_l uses n = \|V(G)\| (isolated vertices count). |
| note | `s2:defHBtp` | HB-DEGENERATE-N | n = 0: Lean gives d_1 = 0 (x/0 = 0), so the run stops at once iff D_* > 0 (true under Gamma). Rounds are 1-indexed; avoid ℕ-subtraction l - 1 in the list index by a helper 'round l' with 1 <= l. |
| note | `s2:defHBtp` | HB-EMBEDDED-CLAIMS | The definition's text contains claims that are lemmas, not definitions: (R5)(1) 'no edge is assigned twice' (SEP(i) on T_l), (R3) 'X^0_Z is a (2^-5,s_l)-expander' (stopping rule), '(R3) equivalently' (pre-parts = big leaves of T_l = big tau-run leaves), 'Std_l contains the GC-parts ...'. Put them in the Run API with proofs; step1 of assign must be defined so that it is well defined even without the disjointness (e.g. via find? on the home order). |
| note | `s2:defHBtp` | HB-MMAX-INACTIVE | Under Gamma2(a) (T_l >= 2^117) the max in M_l is never 2^40 for l <= R (2^16 T log^4 T >= 2^133). Gamma2(b)'s phrase 'including rounds with M_l = 2^40' is vacuous. Harmless. |
| note | `s2:defHBtp` | HB-DSTAR-PARAM | D_* enters the definition only through the stop rule; the Gamma conditions are hypotheses of the lemmas (e.g. lemCap(ii): D_* >= 2^117), never of Valid. Order of constants (s1:remOrder): D_* is fixed before G, so Specs read ∀ D_* (hyps) ∀ G ∀ run, run.Valid G D_* → ... . |
| note | `s2:defAncestors` | ANC-J0-INFTY | j_0(x) has no 'infinity if none' clause (j_1 has). All uses (propParentless(i)) have x in a pre-part; define both in WithTop ℕ (or ℕ∞) so the definitions are total. |
| note | `s2:defAncestors` | ANC-BIJECTION | 'Every ancestor corresponds to a distinct pre-part' is an injection in the text; with ancestors indexed by pre-part addresses it is a bijection by definition, so #ancestors of round r = #pre-parts of round r and mult_r(w) <= mu_r(w) is immediate (propOV (F11)). |
| note | `s2:defAncestors` | ANC-SY-REAL | s_Y = s_r/2 for light Y is real (s_r ∈ ℕ may be odd); IsExpander takes ℝ, fine. eps_Y and s_Y are the parameters of propStructure(i) ('H_Y is an (eps_Y,s_Y)-expander, min degree > s_Y'). |
| note | `s2:defAncestors` | ANC-STD-ONLY | Hubs/ports/fresh/classed are defined only for Z ∈ Std_l; Lean defs are total over addresses, and statements carry a ∈ run.Std G l. For l <= 2 all ports are fresh (anc empty); s6:defLending sets Q*_Z = ∅ there. |
| note | `s2:defAncestors` | ANC-DUP-POSPART | dup_r = Σ_w (mu_r(w) - 1)^+ over w ∈ V(G); ℕ truncated subtraction implements (·)^+ exactly. Do not confuse with Dup (SEP), Dup*_l (defHBtp) or dup_{>=M}(v) (OV) — four different objects with similar names. |
| note | `s2:lemCap` | CAP-RUN-API | (ii) needs three Run-API facts not stated in the manuscript: the piece graph is a subgraph of G'_l (SEP 0'), every pre-part is a tau-run leaf below a piece and Z^0 ⊆ V(Q) (graft API), and every edge of E_l(Z) has both ends in partVerts ⊆ Z^0 ((R5), also propStructure(iii)). A cycle of the piece graph is a cycle of G'_l because list cycles are edge sets (monotonicity of '∀ e ∈ cycleEdges c, e ∈ E'). |
| note | `s2:lemCap` | CAP-M-CEIL | With the proposed M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ (HB-M-INTEGER) the proof is unchanged (monotone); with M_l ∈ ℕ the degree bound becomes deg <= M_l - 1 in ℕ, as used in s6:lemJSLC/lemJplus ('each receives at most M_l - 1 charges'). |
| note | `s2:lemCap` | CAP-DEPENDS-SORRY | Until EG.bmLemma25 is proved, CapRunStatement's proof depends on sorryAx through EG.cap_graph; the ratchet should track it as downstream of s1:citLem25. |
| note | `s2:lemHS` | HS-NUMERIC | (log z'/log z)^2 >= 1/2 from z' >= z/2, z >= 11: the manuscript's route (log_2 11 >= 2 + √2 = 3.4142) involves √2. Lean route: a := log_2 z >= log_2 11 >= 3.45 (11^20 >= 2^69), log_2 z' >= a - 1 > 0, and (a-1)^2 >= a^2/2 ⟺ (a-2)^2 >= 2, true as 1.45^2 = 2.1025. Exact, norm_num/nlinarith. |
| note | `s2:lemHS` | HS-CARD | \|X - W\| = z - \|W\| needs W ⊆ V(X) (deleteVerts = induce (verts \ W)); the expansion parameter of the conclusion must be written with this card (Def 11 uses log of the graph's own card). U ranges over subsets of V(X)\W, F' over subsets of E(X - W); the proof's F := F' ∪ E_X(U,W) needs E_X(U,W) ⊆ E(X) and \|E_X(U,W)\| <= s_W\|U\| (sum over u ∈ U of \|N_X(u) ∩ W\|). |
| note | `s2:lemHS` | HS-APPLICATION-GRAPH | In propStructure(i) the hypothesis comes from (L2), which bounds neighbours in G'_l[Z^0] ⊇ X^0_Z; the transfer needs nbrs monotonicity under ≤ (existing API: nbrSet_mono / deg_mono) and X^0_Z ≤ G'_l[Z^0] (SEP 0' + edges inside Z^0). Also z = \|Z^0\| >= P_l >= 11 needs Gamma (lambda_l large). |

## 4. Nodes

### `s2:defWitness` — definition (with a proved Fact): witness and its minimal part (s2.tex:34)

- **Manuscript referee status:** x2+RT
- **Formalization:** Defs (EG/Defs/HB/Witness.lean: IsWitness, witN, witF0) + Spec for the Fact and for 'not an expander iff a witness exists' (EG/Spec/HB/Witness.lean)

**Statement (precise restatement).** Global: log = log_2, |H| = |V(H)|; in s2 eps = 2^-5, but nothing here depends on the value of eps, so the Lean definition takes eps : R as a parameter. Let s >= 0 (real) and H a finite simple graph with m := |V(H)|. (W) A WITNESS at H with parameter s is a pair (U,F) with U ⊆ V(H), F ⊆ E(H), 1 <= |U| <= 2m/3, |F| <= s|U| and |N_{H-F}(U)| < eps|U|/log^2 m, where N_{H-F}(U) = set of vertices of V(H)\U having an (H-F)-neighbour in U. (W0) H is NOT an (eps,s)-expander (s1:citDef11) IFF there EXISTS a witness at H with parameter s (this is literally the negation of Def 11). (W1) If a witness exists then m >= 2 (1 <= |U| <= 2m/3 forces m >= 3/2). For a witness put N := N_{H-F}(U) (so N ⊆ V(H)\U) and F_0 := E_H(U, V(H)\(U ∪ N)). FACT: (i) F_0 ⊆ F; (ii) N_{H-F_0}(U) = N; (iii) (U,F_0) is again a witness at H with parameter s, with the same N. (Parts (i),(ii) hold for EVERY U ⊆ V(H) and F ⊆ E(H), without the size and expansion inequalities; (iii) uses |F_0| <= |F| <= s|U|.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| FGraph, card, nbrSet (N_H(U)), deleteEdges (H-F), edgesBetween (E_H(A,B)) | finite simple graph with explicit vertex/edge finsets and the operations of s1:convGraphs(c) | s1:convGraphs | yes: EG.FGraph, EG.FGraph.card/nbrSet/deleteEdges/edgesBetween (EG/Defs/Graph.lean) |
| (eps,s)-expander | for all U ⊆ V, F ⊆ E, 1<=\|U\|<=2n/3, \|F\|<=s\|U\|: eps\|U\|/log_2^2 n <= \|N_{G-F}(U)\| | s1:citDef11 | yes: EG.FGraph.IsExpander G eps s (EG/Defs/Expander.lean) |
| IsWitness H eps s U F | the six conditions of (W), in the same order and form as the hypotheses of IsExpander, so that ¬IsExpander ↔ ∃ U F, IsWitness is `push_neg` | s2:defWitness | no: new EG.HB.IsWitness |
| witN H U F | (H.deleteEdges F).nbrSet U  (= N) | s2:defWitness | no: new EG.HB.witN (abbreviation) |
| witF0 H U N | H.edgesBetween U (H.verts \ (U ∪ N))  (= F_0; takes N, not F, so that s2:defTauRules(c) is definitional) | s2:defWitness | no: new EG.HB.witF0 |

**deps_declared** (manuscript \deps): s1:citDef11, s1:defConstants

**deps_from_proof:** s1:citDef11, s1:convGraphs

**deps_notes:** s1:defConstants only fixes eps = 2^-5 (not used in the Fact's proof; ms_deps flags it unreferenced). s1:convGraphs(c) supplies N_H(U), H-F, E_H(A,B).

**used_by:** s2:defTauRules; s2:lemOVgeneric; s2:lem14tau; s2:propExists; s2:defHBtp (implicitly: both levels of (R3) use witnesses)

**randomness:** none

**lean_shape:**

```lean
namespace EG.HB
variable {V : Type*} [DecidableEq V]
/-- [s2:defWitness] -/
def IsWitness (H : FGraph V) (ε s : ℝ) (U : Finset V) (F : Finset (Sym2 V)) : Prop :=
  U ⊆ H.verts ∧ F ⊆ H.edges ∧ 1 ≤ U.card ∧ (U.card : ℝ) ≤ 2 * (H.card : ℝ) / 3 ∧
  (F.card : ℝ) ≤ s * U.card ∧
  ((((H.deleteEdges F).nbrSet U).card : ℕ) : ℝ) < ε * U.card / Real.logb 2 H.card ^ 2
abbrev witN (H : FGraph V) (U : Finset V) (F : Finset (Sym2 V)) : Finset V := (H.deleteEdges F).nbrSet U
def witF0 (H : FGraph V) (U N : Finset V) : Finset (Sym2 V) := H.edgesBetween U (H.verts \ (U ∪ N))
-- Spec (EG/Spec/HB/Witness.lean)
def WitnessIffStatement : Prop := ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (ε s : ℝ),
  ¬ H.IsExpander ε s ↔ ∃ U F, IsWitness H ε s U F
def WitnessCardStatement : Prop := ∀ V [DecidableEq V] (H : FGraph V) ε s U F, IsWitness H ε s U F → 2 ≤ H.card
def WitnessFactStatement : Prop := ∀ V [DecidableEq V] (H : FGraph V) (U : Finset V) (F : Finset (Sym2 V)),
  U ⊆ H.verts → F ⊆ H.edges →
    witF0 H U (witN H U F) ⊆ F ∧ witN H U (witF0 H U (witN H U F)) = witN H U F
def WitnessMinimalStatement : Prop := ∀ V [DecidableEq V] (H : FGraph V) ε s U F,
  IsWitness H ε s U F → IsWitness H ε s U (witF0 H U (witN H U F))
```

**hazards:**

- **[note] WIT-EPS-PARAM.** The manuscript fixes eps = 2^-5 for all of s2 ('Throughout, eps = 2^-5'). The definition and the Fact are eps-independent; the Lean definition must take eps as a parameter (lem14tau, the OV instance and (R3) instantiate eps = 2^(-5:ℤ)). For eps <= 0 there is no witness (EG.FGraph.isExpander_of_nonpos), consistent with the manuscript.
- **[note] WIT-M2-FREE.** 'Then m >= 2' needs no hypothesis: |U| >= 1 and |U| <= 2m/3 give m >= 3/2. With Lean's x/0 = 0, m <= 1 also has no witness (the expansion inequality reads |N| < 0). Consistent with EG.FGraph.isExpander_of_card_le_one.
- **[note] WIT-FACT-GENERAL.** Fact (i),(ii) hold for every U ⊆ V(H), F ⊆ E(H); state them without the witness hypothesis (reused in s2:defTauRules(c) and nowhere does the proof need the expansion inequality). N ∩ U = ∅ is free (EG.FGraph.disjoint_nbrSet).
- **[note] WIT-HYP-ORDER.** Keep the conjuncts of IsWitness literally the negated body of IsExpander (same real casts, 2*card/3, logb 2 card ^ 2) so that WitnessIffStatement is push_neg plus reordering; a mismatch here (e.g. natural-number division 2*m/3) would silently change the definition.

**effort:** ~120 Lean lines, difficulty 1/5 (Defs ~25 lines; Fact and iff ~90 lines (Finset filter reasoning).)

### `s2:defTauRules` — definition (with proved Facts (a)-(c) and equation s2:eqSplit): the tau-rules and the split (s2.tex:64)

- **Manuscript referee status:** x2+RT
- **Formalization:** Defs (EG/Defs/HB/Witness.lean: generic split splitFst/splitSnd/splitDel shared with s2:lemSEP; tau-rule sets as functions of (H,U,N,tau)) + Spec for Facts (a),(b) and eqSplit

**Statement (precise restatement).** Data: H with V := V(H), m := |V|; s >= 0; a witness (U,F) at H with parameter s (s2:defWitness); N := N_{H-F}(U); F_0 := E_H(U, V\(U∪N)); a real tau > s. tau-rules: (1) H_out := {v ∈ U : deg_{F_0}(v) >= tau}; U' := U\H_out; N' := N ∪ H_out. (2) F_1 := E_H(U', V\(U'∪N')); H_in := {x ∈ V\(U'∪N') : deg_{F_1}(x) >= tau}; N'' := N' ∪ H_in; F'' := E_H(U', V\(U'∪N'')). Split: G_1 := H[U'∪N''] - F''; G_2 := H - U' - E(G_1) - F''; the deleted set is F''. (eqSplit) G_1 = H[U'∪N''] and G_2 = H[V\U'] - E(H[N'']) (equal as graphs: same vertex set, same edge set). Facts: (a) U'∩N'' = ∅; U'∪N' = U∪N; F'' ⊆ F_1 ⊆ F_0 ⊆ F. (b) E(H) = E(G_1) ⊔ E(G_2) ⊔ F'' (pairwise disjoint, union E(H)); V(G_1) = U'∪N''; V(G_2) = V\U'; v ∈ U' ⇒ v ∈ V(G_1)\V(G_2); v ∈ N'' ⇒ v ∈ V(G_1)∩V(G_2); v ∈ V\(U'∪N'') ⇒ v ∈ V(G_2)\V(G_1). (c) H_out, U', N', F_1, H_in, N'', F'', G_1, G_2 are functions of (H, U, N, tau) alone (they are defined from F_0, which is a function of (U,N)); every witness (U,F) gives the same split as its minimal part (U,F_0). Implicit facts used later (not stated): U' ⊆ U ⊆ V and N'' ⊆ V (so the split has the SEP form with U', N'' ⊆ V(H) disjoint); every edge of F'' has exactly one end in U' and the other in V\(U'∪N''); every edge of F_0 (resp. F_1) has exactly one end in U (resp. U') and the other outside U∪N; |N''| = |N| + |H_out| + |H_in| (the three sets are pairwise disjoint).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| IsWitness, witN, witF0 | see s2:defWitness | s2:defWitness | no (new, s2:defWitness) |
| degE F v (deg_F(v)), induce (H[U]), deleteVerts (H-U), deleteEdges (H-F), edgesBetween | s1:convGraphs(c) | s1:convGraphs | yes: EG.degE, EG.FGraph.induce/deleteVerts/deleteEdges/edgesBetween |
| splitFst H U' N'' / splitSnd H U' N'' / splitDel H U' N'' | H.induce (U'∪N'') / (H.induce (H.verts\U')).deleteEdges (H.induce N'').edges / H.edgesBetween U' (H.verts\(U'∪N'')) -- the canonical (eqSplit) forms, shared by every split recursion | s2:eqSplit, s2:lemSEP | no: new EG.HB.splitFst/splitSnd/splitDel |
| tauHout, tauU1 (U'), tauN1 (N'), tauF1, tauHin, tauN2 (N''), tauF2 (F'') | the sets of rules (1),(2) as functions of (H : FGraph V) (U N : Finset V) (τ : ℝ); the comparison deg >= tau is ((degE _ v : ℕ) : ℝ) >= τ | s2:defTauRules | no: new |

**deps_declared** (manuscript \deps): s2:defWitness

**deps_from_proof:** s2:defWitness, s1:convGraphs

**deps_notes:** The proof of (a) uses Fact F_0 ⊆ F of s2:defWitness; (b) uses only U'∩N'' = ∅ and eqSplit (so it is the generic split lemma, reused verbatim by s2:lemSEP(0)); (c) uses Fact (ii) of s2:defWitness. tau > s is never used in the Facts.

**used_by:** s2:lemSEP; s2:lemThinCut; s2:lem14tau; s2:lemOVgeneric (remark: tau-split at s = 0 is idle; undeclared)

**randomness:** none

**lean_shape:**

```lean
-- generic split (EG/Defs/HB/Witness.lean or SplitTree.lean)
def splitFst (H : FGraph V) (U' N'' : Finset V) : FGraph V := H.induce (U' ∪ N'')
def splitSnd (H : FGraph V) (U' N'' : Finset V) : FGraph V := (H.induce (H.verts \ U')).deleteEdges (H.induce N'').edges
def splitDel (H : FGraph V) (U' N'' : Finset V) : Finset (Sym2 V) := H.edgesBetween U' (H.verts \ (U' ∪ N''))
-- tau-rules, as functions of (H, U, N, τ): Fact (c) is then definitional
def tauHout (H) (U N) (τ : ℝ) := U.filter (fun v => τ ≤ (degE (witF0 H U N) v : ℝ))
def tauU1 H U N τ := U \ tauHout H U N τ ;  def tauN1 H U N τ := N ∪ tauHout H U N τ
def tauF1 H U N τ := H.edgesBetween (tauU1 H U N τ) (H.verts \ (tauU1 H U N τ ∪ tauN1 H U N τ))
def tauHin H U N τ := (H.verts \ (tauU1 H U N τ ∪ tauN1 H U N τ)).filter (fun x => τ ≤ (degE (tauF1 H U N τ) x : ℝ))
def tauN2 H U N τ := tauN1 H U N τ ∪ tauHin H U N τ
def tauF2 H U N τ := splitDel H (tauU1 H U N τ) (tauN2 H U N τ)
-- Spec
def SplitPartitionStatement : Prop := ∀ V [DecidableEq V] (H : FGraph V) (U' N'' : Finset V), U' ⊆ H.verts → N'' ⊆ H.verts → Disjoint U' N'' →
  Disjoint (splitFst H U' N'').edges (splitSnd H U' N'').edges ∧ Disjoint (splitFst H U' N'').edges (splitDel H U' N'') ∧
  Disjoint (splitSnd H U' N'').edges (splitDel H U' N'') ∧
  (splitFst H U' N'').edges ∪ (splitSnd H U' N'').edges ∪ splitDel H U' N'' = H.edges ∧
  (splitFst H U' N'').verts = U' ∪ N'' ∧ (splitSnd H U' N'').verts = H.verts \ U'
def TauFactAStatement : Prop := ∀ V [DecidableEq V] (H : FGraph V) ε s U F (τ : ℝ), IsWitness H ε s U F →
  let N := witN H U F; Disjoint (tauU1 H U N τ) (tauN2 H U N τ) ∧ tauU1 H U N τ ∪ tauN1 H U N τ = U ∪ N ∧
  tauF2 H U N τ ⊆ tauF1 H U N τ ∧ tauF1 H U N τ ⊆ witF0 H U N ∧ witF0 H U N ⊆ F ∧ tauU1 H U N τ ⊆ H.verts ∧ tauN2 H U N τ ⊆ H.verts
def TauEqSplitStatement : Prop := -- literal G_1, G_2 of the manuscript equal the canonical ones
  ∀ ..., (H.induce (U1 ∪ N2)).deleteEdges F2 = splitFst H U1 N2 ∧
         ((H.deleteVerts U1).deleteEdges (H.induce (U1 ∪ N2)).edges).deleteEdges F2 = splitSnd H U1 N2
```

**hazards:**

- **[note] TAU-DEFINE-BY-EQSPLIT.** The manuscript defines G_2 := H - U' - E(G_1) - F'' and then derives (eqSplit). In Lean define the children by the (eqSplit) forms (splitFst/splitSnd), shared with every split recursion (the s = 0 level uses the same constructor), and prove the literal forms as TauEqSplitStatement. Otherwise SEP, OV and the two-level recursion would need transport lemmas between two constructions.
- **[note] TAU-SIGNATURE-UN.** Fact (c) (RT2-I7) is automatic if the tau-rule functions take (H,U,N,tau) and the witness-level split is obtained by N := witN H U F. Do not define them from F (then (c) becomes a lemma about F_0 = witF0 and must be proved).
- **[note] TAU-TAU-GT-S-UNUSED.** tau > s only makes the rules 'defined' in the manuscript; no Fact uses it. The Lean functions are total for every real tau; for tau <= 0 they degenerate (H_out = U, U' = ∅) and termination fails (see LEM14-TERMINATION). Validity predicates (IsTauRun) carry the tau hypothesis, not the definitions.
- **[note] TAU-IMPLICIT-SUBSETS.** U' ⊆ V(H) and N'' ⊆ V(H) are not stated in the manuscript but are needed for the split to be a SEP split (SEP requires U'_nu, N''_nu ⊆ V(H_nu)) and, in Lean, because FGraph.induce intersects with verts: without N'' ⊆ V the identity |nu_1| = |U'| + |N''| fails. Include them in TauFactAStatement.
- **[note] TAU-REALCOMPARE.** deg_{F_0}(v) >= tau compares a natural number with a real; write τ ≤ ((degE F0 v : ℕ) : ℝ). In all applications tau = tau_l ∈ ℕ (ceiling in (R2)), and deg < tau ⟺ deg <= tau - 1, which is the form used in s2:lemThinCut.

**effort:** ~250 Lean lines, difficulty 2/5 (Generic split partition lemma ~100 lines (Sym2/Finset case analysis), Fact (a) ~60, eqSplit ~60.)

### `s2:lemSEP` — lemma (contains the definition of a split recursion): Lemma SEP (s2.tex:128)

- **Manuscript referee status:** x2+RT
- **Formalization:** Defs (EG/Defs/HB/SplitTree.lean: split trees, node addresses, graphs at nodes, leaves, Dup, deleted edges, graft) + Spec EG/Spec/HB/SplitTree.lean (SEP (0)-(iii) and monotonicity)

**Statement (precise restatement).** DEFINITION. A split recursion on a finite simple graph H_0 is a finite rooted full binary tree t (every internal node nu has an ordered pair of children nu_1, nu_2) whose nodes carry graphs H_nu with H_root = H_0 such that at every internal node nu there are sets U'_nu, N''_nu ⊆ V(H_nu) with U'_nu ∩ N''_nu = ∅ and H_{nu_1} = H_nu[U'_nu ∪ N''_nu], H_{nu_2} = H_nu[V(H_nu)\U'_nu] - E(H_nu[N''_nu]); deleted set F''_nu := E_{H_nu}(U'_nu, V(H_nu)\(U'_nu ∪ N''_nu)). |nu| := |V(H_nu)|; v lies in nu iff v ∈ V(H_nu); leaves = leaf NODES (positions; two leaves with equal vertex sets are distinct); deleted edge = element of ⋃_{nu internal} F''_nu; Dup := {v : v lies in at least two distinct leaf nodes}. For u ∉ Dup lying in some leaf, L_u := that leaf. CONCLUSIONS (for every split recursion): (0) at every internal nu: E(H_nu) = E(H_{nu_1}) ⊔ E(H_{nu_2}) ⊔ F''_nu (pairwise disjoint); v ∈ U'_nu lies in nu_1 only; v ∈ N''_nu lies in both children; v ∈ V(H_nu)\(U'∪N'') lies in nu_2 only; |nu_1| + |nu_2| = |nu| + |N''_nu|. Every vertex of a node nu lies in at least one leaf of the subtree of nu. Σ_{leaves L} |L| = |H_0| + Σ_{nu internal} |N''_nu|. (0', implicit, used by s2:lemCap, s2:propStructure(i),(iii), s2:propDegRec, s2:propOV) for mu in the subtree of nu: V(H_mu) ⊆ V(H_nu) and E(H_mu) ⊆ E(H_nu); in particular every node graph is a subgraph of H_0. (i) for every edge e = xy ∈ E(H_0): #{leaves L : e ∈ E(H_L)} + #{internal nu : e ∈ F''_nu} = 1. If e ∈ E(H_L) then x,y ∈ V(H_L). If e ∈ F''_nu then x,y ∈ V(H_nu), one of x,y lies in U'_nu and the other in V(H_nu)\(U'_nu ∪ N''_nu) (each goes to exactly one child, and to different children), e ∈ E(H_mu) for every ancestor mu of nu (nu included) and e ∉ E(H_{nu_1}) ∪ E(H_{nu_2}). (ii) for every u ∈ V(H_0)\Dup: there is exactly one leaf L_u with u ∈ V(H_{L_u}); {nu : u lies in nu} = {ancestors of L_u} (L_u included); u ∉ N''_nu for every internal ancestor nu of L_u. (iii) for u ∈ V(H_0)\Dup and h ∈ V(H_0)\V(H_{L_u}), let nu* be the deepest ancestor of L_u in which h lies (it exists: the root; it is internal since h ∉ V(H_{L_u})). Then for every u' ∈ V(H_{L_u})\Dup, every deleted edge hu' lies in F''_{nu*}.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| split tree t (choices only) | Mathlib BinaryTree (Finset V × Finset V): nil = leaf, node (U',N'') t1 t2 = internal node with its two sets; the graphs are COMPUTED from H_0 (PLAN §3 decision 5) | s2:lemSEP | no: new EG.HB.STree := BinaryTree (Finset V × Finset V) (Mathlib/Data/Tree/Basic.lean; renamed from Tree in this Mathlib) or a custom inductive |
| addresses, prefix/ancestor, subtreeAt, labelAt | a : List Bool (false = first child); ancestor = prefix (List.IsPrefix); nodeAddrs/leafAddrs/internalAddrs : Finset (List Bool) | s2:lemSEP ('ancestors', 'deepest ancestor', 'below', 'path child') | no: new |
| graphAt t H0 a | H_a, computed by folding splitFst/splitSnd along a (total version graphAtD returns H0 for invalid a) | s2:lemSEP | no: new |
| STree.WF t H0 | for every internal a: U'_a ⊆ V(H_a), N''_a ⊆ V(H_a), Disjoint U'_a N''_a | s2:lemSEP | no: new |
| leaf mass, dup set, deleted set | leafMass = Σ_{a ∈ leafAddrs} \|H_a\|; dup = {v ∈ V(H0) : 2 <= #{a ∈ leafAddrs : v ∈ V(H_a)}}; deleted = ⋃_{a ∈ internalAddrs} splitDel H_a U'_a N''_a | s2:lemSEP | no: new |
| graft t f | replace the leaf at address a by f a (needed for the two-level recursion of s2:defHBtp); addresses of the result = a ++ b | s2:defHBtp (R3), used by propOV, propOrigin | no: new |
| splitFst/splitSnd/splitDel | see s2:defTauRules | s2:eqSplit | no (new, s2:defTauRules) |

**deps_declared** (manuscript \deps): s2:defTauRules

**deps_from_proof:** s2:defTauRules

**deps_notes:** Only the generic part of Fact (b) of s2:defTauRules (partition for any disjoint U', N'' ⊆ V) is used; in Lean this is SplitPartitionStatement. Everything else is tree induction.

**used_by:** s2:lemThinCut; s2:lemOVgeneric; s2:lem14tau; s2:defHBtp; s2:propStructure; s2:propOV; s2:propDegRec; s2:propOrigin; s6:thmCONCL; s2:lemCap (implicitly, (0'))

**randomness:** none

**lean_shape:**

```lean
abbrev STree (V : Type*) := BinaryTree (Finset V × Finset V)   -- nil = leaf; node (U', N'') t₁ t₂
def STree.graphAtD : STree V → FGraph V → List Bool → FGraph V            -- H_a (total)
def STree.nodeAddrs / leafAddrs / internalAddrs : STree V → Finset (List Bool)
def STree.labelAt : STree V → List Bool → Option (Finset V × Finset V)    -- (U'_a, N''_a)
def STree.WF (t : STree V) (H : FGraph V) : Prop :=
  ∀ a ∈ t.internalAddrs, ∀ p, t.labelAt a = some p → p.1 ⊆ (t.graphAtD H a).verts ∧ p.2 ⊆ (t.graphAtD H a).verts ∧ Disjoint p.1 p.2
def STree.leafMass (t) (H) : ℕ := ∑ a ∈ t.leafAddrs, (t.graphAtD H a).card
def STree.dup (t) (H) : Finset V := H.verts.filter (fun v => 2 ≤ (t.leafAddrs.filter (fun a => v ∈ (t.graphAtD H a).verts)).card)
def STree.deleted (t) (H) : Finset (Sym2 V) := t.internalAddrs.biUnion (fun a => splitDel (t.graphAtD H a) (U' a) (N'' a))
def STree.graft : STree V → (List Bool → STree V) → STree V
-- Spec (each ∀ V [DecidableEq V] (H : FGraph V) (t : STree V), t.WF H → …)
SEP0 : (∀ a ∈ internalAddrs, partition + vertex placement + |H_{a++[f]}| + |H_{a++[t]}| = |H_a| + |N''_a|) ∧
       (∀ a ∈ nodeAddrs, ∀ v ∈ (graphAtD H a).verts, ∃ b ∈ leafAddrs, a <+: b ∧ v ∈ (graphAtD H b).verts) ∧
       t.leafMass H = H.card + ∑ a ∈ internalAddrs, (N'' a).card
SEPmono : ∀ a b ∈ nodeAddrs, a <+: b → graphAtD H b ≤ graphAtD H a
SEPi : ∀ e ∈ H.edges, (leafAddrs.filter (e ∈ (graphAtD H ·).edges)).card + (internalAddrs.filter (e ∈ splitDel …)).card = 1 ∧
      ∀ a ∈ internalAddrs, e ∈ splitDel … → (∀ b, b <+: a → e ∈ (graphAtD H b).edges) ∧ e ∉ (child graphs).edges ∧ (ends: one in U'_a, other in V(H_a)\(U'_a ∪ N''_a))
SEPii : ∀ u ∈ H.verts, u ∉ t.dup H → ∃! L ∈ leafAddrs, u ∈ V(H_L) ∧ (∀ a ∈ nodeAddrs, u ∈ V(H_a) ↔ a <+: L) ∧ ∀ a ∈ internalAddrs, a <+: L → u ∉ N'' a
SEPiii : ∀ u h L, (u ∉ dup, L = leaf of u) → h ∈ H.verts → h ∉ V(H_L) → ∀ ν*, (ν* deepest prefix of L with h ∈ V(H_ν*)) →
        ∀ u' ∈ V(H_L) \ dup, s(h,u') ∈ t.deleted H → s(h,u') ∈ splitDel (H_ν*) (U' ν*) (N'' ν*)
```

**hazards:**

- **[risk] SEP-TREE-INFRA.** Split trees with addresses, prefix order, 'deepest ancestor containing h', 'path child', lowest common ancestor (propOV(K3)) and grafting (the two-level recursion) are new foundations with no Mathlib counterpart beyond BinaryTree. Every counting lemma of s2 (SEP, thin cut, OV, 14^tau, propOV, propDegRec, propOrigin) and s6:thmCONCL rests on them. This is the main P2-D data-model decision for s2 (not a manuscript decision): recommend BinaryTree (Finset V × Finset V) + List Bool addresses + a total graphAtD, with a library of 'induction along an address' lemmas. Estimated 400 lines before SEP itself.
- **[risk] SEP-LEAF-IDENTITY.** 'Distinct leaf nodes are distinct leaves even if their vertex sets coincide' forces leaves (hence pieces, pre-parts, ancestors) to be identified by ADDRESS, never by vertex set or graph. Dup counts leaf addresses. If any later Spec quantifies over 'pre-parts' as a Finset of vertex sets or FGraphs, D_l, home, S_Z and all counts (K1)-(K3) change meaning. All s2-s7 Specs must index parts by (round, address).
- **[note] SEP-INCLUSION-HYP.** U'_nu, N''_nu ⊆ V(H_nu) is part of the definition and must be in STree.WF: Lean's induce intersects with verts, so without it |nu_1| + |nu_2| = |nu| + |N''_nu| and the leaf-mass identity fail.
- **[note] SEP-MONO-IMPLICIT.** The monotonicity (0') 'vertex sets shrink downwards / node graphs are subgraphs of the root' is used without citation in lemCap(ii) (piece ⊆ G'_l), propStructure(i) (X^0_Z ⊆ G'_l[Z^0]), propOV(K3), propOrigin; include it in the SEP Spec (SEPmono).
- **[note] SEP-I-FIRST-NODE.** (i)'s phrase 'nu is the first node on the path of nodes having xy as an edge at which this happens' is formalized as: e ∈ E(H_mu) for every prefix mu of nu and e is not an edge of either child of nu. The count form '#leaves-with-e + #nodes-deleting-e = 1' captures 'exactly one of the two, exactly once'.
- **[note] SEP-III-DEEPEST.** 'the deepest ancestor of L_u in which h lies' is well defined because the ancestors containing h form a prefix-closed chain (by (0')); in Lean define it as the longest prefix of L_u with h ∈ V(H_prefix), or quantify over any prefix with that maximality property (as in the Spec sketch) to avoid a definition.

**effort:** ~900 Lean lines, difficulty 3/5 (Tree/address/graft infrastructure ~400 lines; SEP (0),(0'),(i),(ii),(iii) ~500 lines (all by structural induction).)

### `s2:lemThinCut` — lemma: thin cut (s2.tex:213)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/SplitTree.lean (ThinCutStatement), proved from SEP; recommended to prove a stronger form that assumes only 'every split is a tau-rule split of some (U,N) with U ⊆ V, N ⊆ V\U'

**Statement (precise restatement).** Let tau > 0 (real), H_0 a graph and t a split recursion on H_0 (s2:lemSEP) in which EVERY split is produced by the tau-rules at threshold tau: for every internal node nu there EXIST s_nu ∈ R with s_nu < tau and a witness (U_nu, F_nu) at H_nu with parameter s_nu (s2:defWitness, eps = 2^-5) such that U'_nu, N''_nu are the sets U', N'' of the tau-rules applied to (H_nu, U_nu, N_nu := N_{H_nu - F_nu}(U_nu), tau). Dup and 'deleted edge' as in SEP. Then FOR EVERY leaf L and EVERY vertex h: #{u ∈ V(H_L)\Dup : hu is a deleted edge} <= ⌈tau⌉ - 1 (equivalently: the count is < tau), which is tau - 1 when tau is an integer; and the count is 0 if h ∈ V(H_L). MOREOVER, for u ∈ V(H_0)\Dup, every edge of H_0 at u is either deleted or an edge of the unique leaf L_u containing u. (The count is over vertices u; u ↦ hu is injective, so it equals the number of such deleted edges.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| split recursion, leaves, Dup, deleted edges | s2:lemSEP | s2:lemSEP | no (new, s2:lemSEP) |
| tau-rules (H_out, U', N', F_1, H_in, N'', F'') | s2:defTauRules | s2:defTauRules | no (new, s2:defTauRules) |
| IsTauSplitTree eps tau t H0 | t.WF H0 ∧ every internal node's label is the tau-rule output of some witness (U,F) with some parameter s < tau | s2:lemThinCut hypothesis | no: new |

**deps_declared** (manuscript \deps): s2:lemSEP, s2:defTauRules

**deps_from_proof:** s2:lemSEP, s2:defTauRules

**deps_notes:** SEP (i) (deleted edges split their ends between the children), (ii) (u ∉ Dup lies exactly on the ancestors of L), (iii) (all relevant deletions happen at nu*); defTauRules: definitions of H_out, H_in and Fact (a) (F'' ⊆ F_1 ⊆ F_0, N' ⊆ N''), eqSplit (V(G_1) = U'∪N'', V(G_2) = V\U'). The witness inequality and s_nu < tau are NOT used (the proof says so).

**used_by:** s2:lem14tau (c),(d); s2:propOrigin (b); s6:thmCONCL (via propOrigin)

**randomness:** none

**lean_shape:**

```lean
def IsTauSplitTree (ε τ : ℝ) (t : STree V) (H₀ : FGraph V) : Prop :=
  t.WF H₀ ∧ ∀ a ∈ t.internalAddrs, ∃ (s : ℝ) (U : Finset V) (F : Finset (Sym2 V)), s < τ ∧
    IsWitness (t.graphAtD H₀ a) ε s U F ∧
    t.labelAt a = some (tauU1 (t.graphAtD H₀ a) U (witN _ U F) τ, tauN2 (t.graphAtD H₀ a) U (witN _ U F) τ)
def ThinCutStatement : Prop := ∀ (V : Type u) [DecidableEq V] (H₀ : FGraph V) (t : STree V) (τ : ℝ),
  0 < τ → IsTauSplitTree EG.epsC τ t H₀ → ∀ L ∈ t.leafAddrs, ∀ h : V,
    ((((t.graphAtD H₀ L).verts \ t.dup H₀).filter (fun u => s(h, u) ∈ t.deleted H₀)).card : ℝ) < τ ∧
    (h ∈ (t.graphAtD H₀ L).verts → (((t.graphAtD H₀ L).verts \ t.dup H₀).filter (fun u => s(h, u) ∈ t.deleted H₀)) = ∅)
def ThinCutEdgeStatement : Prop := ∀ V … H₀ t, t.WF H₀ → ∀ u ∈ H₀.verts, u ∉ t.dup H₀ → ∀ e ∈ H₀.edges, u ∈ e →
    e ∈ t.deleted H₀ ∨ ∃ L ∈ t.leafAddrs, u ∈ (t.graphAtD H₀ L).verts ∧ e ∈ (t.graphAtD H₀ L).edges
-- stronger Lib form: replace the witness by any (U, N) with U ⊆ V(H_a), N ⊆ V(H_a) \ U
```

**hazards:**

- **[note] THIN-CEIL-FORM.** State the bound as the real inequality (count : ℝ) < τ; it is equivalent to count <= ⌈τ⌉ - 1 for τ > 0, and to count <= τ - 1 for integer τ (τ_r ∈ ℕ by the ceiling in (R2), which is the form propOrigin(b) and s6:thmCONCL(i) use).
- **[note] THIN-UNUSED-HYPS.** s_nu < tau and the witness inequality are not used; the Lean proof should go through a lemma assuming only that each split is a tau-rule split of some (U,N) (U ⊆ V(H_nu), N ⊆ V(H_nu)\U). This also covers the s = 0 first level of the two-level recursion (tau-rules at s = 0 are idle), so thin cut may be applied to the whole two-level recursion if convenient.
- **[note] THIN-MOREOVER-IS-SEP.** The 'Moreover' sentence is SEP(i)+(ii) and needs no tau-rules; put it in the SEP layer (ThinCutEdgeStatement holds for every split recursion).
- **[note] THIN-H-ANY.** 'every vertex h' ranges over all of V (h ∉ V(H_0) gives count 0); the proof's reduction 'h lies in the root' is a case split, not a hypothesis.

**effort:** ~200 Lean lines, difficulty 2/5 (Given SEP(ii),(iii): two cases (path child first/second), each a Finset card bound via degE of F_1 or F_0 and F'' ⊆ F_1 ⊆ F_0.)

### `s2:lemOVgeneric` — lemma (with the instance c = 1 and the definition of an s=0 recursion): generic overlap bound, Lemma OV (s2.tex:271)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/Overlap.lean (OVStatement, OVInstanceStatement); Defs IsS0Rec, DeltaGe, dupGe, cOV in EG/Defs/HB/SplitTree.lean

**Statement (precise restatement).** Let eps > 0 (manuscript: eps = 2^-5), c > 0 with 3.42 c eps < 1, and c_OV := log_2(4/3). Let t be a split recursion on H_0 with n_0 := |V(H_0)| >= 1 such that at EVERY internal node nu, with m := |nu|: (H1) m >= 2; (H2) |nu_1| <= 3m/4; (H3) |N''_nu| <= c eps |U'_nu| / log_2^2 m. Let S := Σ_{leaves L} |L|. For real M >= 2 let Delta_{>=M} := Σ_{internal nu, |nu| >= M} |N''_nu| and, for a vertex v, dup_{>=M}(v) := #{internal nu : |nu| >= M, v ∈ N''_nu} (so Σ_v dup_{>=M}(v) = Delta_{>=M}). Then: (a) Delta_{>=M} <= c eps (1/log^2 M + 1/(c_OV log M)) S <= 3.42 c eps S / log M; (b) for every v: #{leaves L : |L| >= M, v ∈ V(L)} <= 1 + dup_{>=M}(v); hence Σ_{L : |L| >= M} |L| <= |⋃_{L : |L| >= M} V(L)| + Delta_{>=M}; (c) S <= n_0 / (1 - 3.42 c eps). INSTANCE c = 1. An s=0 recursion is a split recursion in which every internal nu carries a witness (U_nu, F_nu) at H_nu with parameter 0 and U'_nu = U_nu, N''_nu = N_{H_nu}(U_nu). For every s=0 recursion: F_nu = ∅; H_{nu_1} = H_nu[U_nu ∪ N_nu], H_{nu_2} = H_nu[V\U_nu] - E(H_nu[N_nu]); the deleted sets are empty; the split equals the tau-rule split at s = 0 for every tau > 0; the hypotheses (H1)-(H3) hold with c = 1 (|nu_1| < (1+eps)(2/3)m <= 3m/4 needs eps <= 1/8); hence (eps = 2^-5) S <= n_0/(1 - 3.42 eps) <= 1.12 n_0. (Remarks, no content: this is the recursion of the proof of B-M Lemma 14 at s = 0; OV is applied with c = 1.6 to the recursion of Lemma 14^tau and to the two-level recursion of a round.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| split recursion, \|nu\|, U'_nu, N''_nu, children, leaves | s2:lemSEP | s2:lemSEP | no (new, s2:lemSEP) |
| S = leafMass | Σ over leaf addresses of \|H_a\| | s2:lemOVgeneric | no (new, s2:lemSEP) |
| Delta_{>=M}, dup_{>=M}(v) | sum of \|N''_a\| (resp. count of a with v ∈ N''_a) over internal addresses a with (\|H_a\| : ℝ) >= M | s2:lemOVgeneric | no: new EG.HB.STree.DeltaGe, EG.HB.STree.dupGe (M : ℝ) |
| c_OV | Real.logb 2 (4/3) | s2:lemOVgeneric | no: new EG.HB.cOV |
| OVHyp eps c t H0 | t.WF H0 ∧ ∀ internal a: 2 <= \|H_a\| ∧ \|H_{a++[false]}\| <= 3/4 \|H_a\| ∧ \|N''_a\| <= c eps \|U'_a\| / logb 2 \|H_a\| ^ 2 | s2:lemOVgeneric hypotheses | no: new |
| IsS0Rec eps t H0 | t.WF H0 ∧ ∀ internal a, ∃ U F, IsWitness H_a eps 0 U F ∧ labelAt a = some (U, H_a.nbrSet U) | s2:lemOVgeneric 'Instance c = 1' | no: new EG.HB.IsS0Rec |

**deps_declared** (manuscript \deps): s2:lemSEP, s2:defWitness, s1:citLem14

**deps_from_proof:** s2:lemSEP, s2:defWitness, s2:defTauRules

**deps_notes:** SEP(0): vertices of U' go only to nu_1, every vertex of a node lies in a leaf below, leaf-mass identity, v in both children iff v ∈ N''; vertex sets shrink downwards (0'). s2:defWitness: at s = 0, |F| <= 0 forces F = ∅, |N| < eps|U|/log^2 m, m >= 2. s2:defTauRules only for the remark 'also the tau-split at s = 0' (undeclared; needed if thin cut is applied to the whole two-level recursion). s1:citLem14 is commentary only (identification with B-M's recursion), not a logical dependency.

**used_by:** s2:lem14tau (b); s2:defHBtp (R3) (s=0 recursion); s2:propOV; s2:propDegRec; s2:propExists; s2:propOrigin; s2:remTauConstants

**randomness:** none

**lean_shape:**

```lean
def cOV : ℝ := Real.logb 2 (4 / 3)
def STree.DeltaGe (t : STree V) (H : FGraph V) (M : ℝ) : ℕ :=
  ∑ a ∈ t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ)), (N'' t a).card
def STree.dupGe (t) (H) (M : ℝ) (v : V) : ℕ :=
  (t.internalAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ) ∧ v ∈ N'' t a)).card
def OVHyp (ε c : ℝ) (t : STree V) (H : FGraph V) : Prop := t.WF H ∧ ∀ a ∈ t.internalAddrs,
  2 ≤ (t.graphAtD H a).card ∧ ((t.graphAtD H (a ++ [false])).card : ℝ) ≤ 3 / 4 * (t.graphAtD H a).card ∧
  ((N'' t a).card : ℝ) ≤ c * ε * (U' t a).card / Real.logb 2 (t.graphAtD H a).card ^ 2
def OVStatement : Prop := ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (t : STree V) (ε c : ℝ),
  0 < ε → 0 < c → 3.42 * c * ε < 1 → OVHyp ε c t H →
  (∀ M : ℝ, 2 ≤ M → (t.DeltaGe H M : ℝ) ≤ c * ε * (1 / Real.logb 2 M ^ 2 + 1 / (cOV * Real.logb 2 M)) * t.leafMass H ∧
                    (t.DeltaGe H M : ℝ) ≤ 3.42 * c * ε * t.leafMass H / Real.logb 2 M) ∧
  (∀ M : ℝ, 2 ≤ M → ∀ v, (t.leafAddrs.filter (fun a => M ≤ ((t.graphAtD H a).card : ℝ) ∧ v ∈ (t.graphAtD H a).verts)).card ≤ 1 + t.dupGe H M v) ∧
  (∀ M : ℝ, 2 ≤ M → ∑ a ∈ bigLeaves M, (t.graphAtD H a).card ≤ (bigLeaves M).biUnion (verts ∘ graphAtD) |>.card + t.DeltaGe H M) ∧
  (t.leafMass H : ℝ) ≤ H.card / (1 - 3.42 * c * ε)
def IsS0Rec (ε : ℝ) (t : STree V) (H : FGraph V) : Prop := t.WF H ∧ ∀ a ∈ t.internalAddrs,
  ∃ U F, IsWitness (t.graphAtD H a) ε 0 U F ∧ t.labelAt a = some (U, (t.graphAtD H a).nbrSet U)
def OVInstanceStatement : Prop := ∀ V [DecidableEq V] (H : FGraph V) (t : STree V), IsS0Rec EG.epsC t H →
  OVHyp EG.epsC 1 t H ∧ t.deleted H = ∅ ∧ (t.leafMass H : ℝ) ≤ 1.12 * H.card ∧
  (∀ τ > 0, IsTauSplitTree EG.epsC τ t H)   -- the 'tau-rules are idle at s = 0' remark
```

**hazards:**

- **[risk] OV-CONST-546.** Constants: 1 + 1/c_OV = 3.4094... <= 3.42 needs log_2(4/3) >= 1/2.42 = 0.41322 (e.g. 12/29: 2^46 >= 3^29). But lem14tau(b)'s 5.46 = 1.6(1 + 1/c_OV) needs log_2(4/3) >= 0.414508; the bound 12/29 = 0.41379 gives 1.6(1 + 29/12) = 5.4667 > 5.46 and FAILS. Use 17/41 (2^65 >= 3^41, i.e. 3.689e19 >= 3.647e19). So (a) must be proved in its sharp first form (with c_OV) and both constants derived from it; proving only the '3.42' form would make lem14tau(b) and propOV(K2) unprovable as stated. (The true value 5.4555 has 0.08% slack.)
- **[note] OV-A-PROOF-ROUTE.** The manuscript's (a) charges (nu,u) to leaf copies, orders the charging ancestors into a chain and compares a sum with an integral. Recommended Lean route (no integrals, no chains): structural induction with the potential Phi_M(x) := [x >= M]·(1/log^2 M + 1/(c_OV log M) - 1/(c_OV log x)); claim: charges in the subtree of nu <= Σ_{leaf copies below nu} Phi_M(|nu|). Key facts: Phi_M(x) - Phi_M(3x/4) = 1/(log x · log(3x/4)) >= 1/log^2 x when 3x/4 >= M; Phi_M(x) >= 1/log^2 M >= 1/log^2 x when M <= x; at least |U'_nu| leaf copies lie below nu_1 (each u ∈ U'_nu lies in a leaf below nu_1, SEP(0)).
- **[note] OV-INSTANCE-EPS.** The instance needs eps <= 1/8 (for |nu_1| < (1+eps)(2/3)m <= 3m/4, using log m >= 1) and 1/(1 - 3.42 eps) <= 1.12, i.e. eps <= 0.031329; eps = 2^-5 = 0.03125 is just inside (1.11966). State the instance at eps = 2^(-5:ℤ) only.
- **[note] OV-BM-COMMENTARY.** 'This is exactly the recursion in the proof of B-M Lemma 14 with s = 0' is commentary; nothing downstream needs a Lean statement about B-M's recursion (declared dep s1:citLem14 is not logical). The tau-rules-at-s=0 identification IS worth stating (last conjunct of OVInstanceStatement) because it lets thin cut apply to the two-level recursion.
- **[note] OV-NATSUB.** (b)'s consequence 'Σ|L| - |⋃V(L)| <= Delta' must be stated additively (Σ <= |⋃| + Delta) to avoid ℕ truncated subtraction; M is real, |nu| >= M is a real comparison (M = P_r ∈ ℕ and M = 2 in applications).
- **[note] OV-N0-POS.** n_0 >= 1 is not needed (S = 0 when n_0 = 0); omit or keep, harmless.

**effort:** ~500 Lean lines, difficulty 3/5 ((a) ~200 (potential induction + log inequalities), (b) ~100, (c) ~40, instance ~100, constants ~60 (rational bounds on log_2(4/3) via 2^65 >= 3^41).)

### `s2:lem14tau` — lemma (contains the definition of the tau-run): Lemma 14^tau (s2.tex:369)

- **Manuscript referee status:** x2+RT (two deep audits, with simulations)
- **Formalization:** Defs IsTauRun (EG/Defs/HB/SplitTree.lean); Spec EG/Spec/HB/Lemma14Tau.lean split into (a-split) local inequalities, (a-term) termination/existence, (a-del) deletion bound, (a-BM) B-M leaf-size bound, (b) OV at 1.6 eps, (c),(d) thin cut

**Statement (precise restatement).** Let eps := 2^-5, H_0 a finite simple graph, n_0 := |V(H_0)|, s ∈ ℕ with s >= 1, and tau ∈ R with tau >= 128 s log_2^2 n_0. A tau-RUN of H_0 with parameters (s,tau) is ANY split recursion t on H_0 such that (stop) a node nu is a leaf IFF H_nu is an (eps,s)-expander, and (split) at every internal nu there is a witness (U,F) at H_nu with parameter s (s2:defWitness) such that (U'_nu, N''_nu) are the tau-rule sets for (H_nu, U, N_{H_nu - F}(U), tau) (s2:defTauRules). Dup := vertices lying in >= 2 leaves. Then for EVERY tau-run t (i.e. for every choice of witnesses): (a-split) at every internal nu, with m := |nu| (so 2 <= m <= n_0) and the notation of s2:defTauRules: |H_out| + |H_in| <= |F_0|/tau <= s|U|/tau <= |U|/(128 log^2 m); |N''| < 1.25 eps|U|/log^2 m (< 1.5 eps|U|/log^2 m); |U'| >= (127/128)|U| > 0; U ⊆ U' ∪ N''; n_1 := |U' ∪ N''| <= 0.698 m < 3m/4; n_2 := m - |U'| < m. (a-term) the recursion terminates: formally, (T1) every tau-rule split of a graph H with 2 <= |H| <= n_0 by a witness with parameter s has 1 <= n_1 < |H| and 1 <= n_2 < |H|; (T2) for every H_0 (and every rule choosing a witness at each non-expander) a finite tau-run exists. (a-del) |⋃_nu F''_nu| <= 4 s n_0 log_2 n_0. (a-part) every edge of H_0 is deleted exactly once or lies in exactly one leaf (SEP(i)); every leaf graph is an (eps,s)-expander. (a-BM) S := Σ_L |L| <= 2 n_0 - 2 n_0/(2 + log_2 n_0). (b) at every internal nu: |N''_nu| <= 1.6 eps |U'_nu|/log^2 m, U'_nu goes only to nu_1, |nu_1| <= 3m/4; hence (s2:lemOVgeneric, c = 1.6) S <= n_0/(1 - 5.5 eps) <= 1.21 n_0 and, for every real M >= 2, Delta_{>=M} <= 5.46 eps S / log_2 M. (c) for every leaf L and every vertex h: #{u ∈ V(L)\Dup : hu deleted} <= ⌈tau⌉ - 1 (< tau), and = 0 if h ∈ V(L). (d) if u ∈ V(H_0)\Dup, every edge of H_0 at u is deleted or lies in the unique leaf containing u. (n_0 <= 1: the root is an expander, t = leaf, everything is trivial.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| IsTauRun eps s tau t H0 | t.WF H0 ∧ (∀ a ∈ nodeAddrs, a ∈ leafAddrs ↔ (graphAtD H0 a).IsExpander eps s) ∧ ∀ internal a, ∃ U F, IsWitness H_a eps s U F ∧ labelAt a = some (tauU1 H_a U (witN H_a U F) tau, tauN2 H_a U (witN H_a U F) tau) | s2:lem14tau | no: new EG.HB.IsTauRun |
| IsExpander | s1:citDef11 | s1:citDef11 | yes: EG.FGraph.IsExpander |
| witness, tau-rules, split recursion, Dup, deleted, leafMass, DeltaGe | s2:defWitness, s2:defTauRules, s2:lemSEP, s2:lemOVgeneric | s2 | no (new, earlier s2 nodes) |

**deps_declared** (manuscript \deps): s1:citLem14, s1:citDef11, s2:defTauRules, s2:lemThinCut, s2:lemOVgeneric, s2:lemSEP, s2:defWitness

**deps_from_proof:** s2:defWitness, s2:defTauRules, s2:lemSEP, s2:lemOVgeneric, s2:lemThinCut, s1:citDef11

**deps_notes:** defWitness: F_0 ⊆ F, |F| <= s|U|, |N| < eps|U|/log^2 m, m >= 2. defTauRules: Facts (a),(b), eqSplit, and the degree counting of F_0, F_1 (each edge of F_0 has exactly one end in U; each edge of F_1 exactly one end outside U∪N). SEP: (0),(i) (partition, leaf-mass identity). OV: (a),(c) at c = 1.6. Thin cut: (c),(d). s1:citDef11: the stopping rule (definitional; ms_deps flags it unreferenced). s1:citLem14 is attribution: the proof re-derives B-M's (8),(9) in full; no logical use of the cited statement.

**used_by:** s2:defHBtp (R3); s2:lemCap (ii) (conclusion pointer); s2:propStructure (i); s2:propOV; s2:propDegRec (a); s2:propExists; s2:remTauConstants

**randomness:** none ('any witnesses' = universally quantified over all trees satisfying IsTauRun)

**lean_shape:**

```lean
def IsTauRun (ε : ℝ) (s : ℕ) (τ : ℝ) (t : STree V) (H₀ : FGraph V) : Prop :=
  t.WF H₀ ∧ (∀ a ∈ t.nodeAddrs, a ∈ t.leafAddrs ↔ (t.graphAtD H₀ a).IsExpander ε s) ∧
  ∀ a ∈ t.internalAddrs, ∃ U F, IsWitness (t.graphAtD H₀ a) ε s U F ∧
    t.labelAt a = some (tauU1 (t.graphAtD H₀ a) U (witN _ U F) τ, tauN2 (t.graphAtD H₀ a) U (witN _ U F) τ)
-- (a-split): one split, no tree
def L14SplitStatement : Prop := ∀ V [DecidableEq V] (H : FGraph V) (s : ℕ) (τ : ℝ) U F, 1 ≤ s → 2 ≤ H.card →
  128 * s * Real.logb 2 H.card ^ 2 ≤ τ → IsWitness H (2^(-5:ℤ)) s U F → let N := witN H U F;
  ((tauHout H U N τ).card + (tauHin H U N τ).card : ℝ) ≤ U.card / (128 * Real.logb 2 H.card ^ 2) ∧
  ((tauN2 H U N τ).card : ℝ) < 1.25 * 2^(-5:ℤ) * U.card / Real.logb 2 H.card ^ 2 ∧
  (127 / 128 : ℝ) * U.card ≤ (tauU1 H U N τ).card ∧ U ⊆ tauU1 H U N τ ∪ tauN2 H U N τ ∧
  ((tauU1 H U N τ ∪ tauN2 H U N τ).card : ℝ) ≤ 0.698 * H.card ∧ (tauU1 H U N τ).Nonempty
-- (a-term)
def L14ExistsStatement : Prop := ∀ V [DecidableEq V] (H₀ : FGraph V) (s : ℕ) (τ : ℝ), 1 ≤ s →
  128 * s * Real.logb 2 H₀.card ^ 2 ≤ τ → ∃ t, IsTauRun (2^(-5:ℤ)) s τ t H₀
-- (a-del),(a-BM),(b),(c),(d): for every τ-run
def L14GlobalStatement : Prop := ∀ V [DecidableEq V] (H₀ : FGraph V) (s : ℕ) (τ : ℝ) (t : STree V), 1 ≤ s →
  128 * s * Real.logb 2 H₀.card ^ 2 ≤ τ → IsTauRun (2^(-5:ℤ)) s τ t H₀ →
  ((t.deleted H₀).card : ℝ) ≤ 4 * s * H₀.card * Real.logb 2 H₀.card ∧
  (∀ a ∈ t.leafAddrs, (t.graphAtD H₀ a).IsExpander (2^(-5:ℤ)) s) ∧
  (t.leafMass H₀ : ℝ) ≤ 2 * H₀.card - 2 * H₀.card / (2 + Real.logb 2 H₀.card) ∧   -- (a-BM), unused downstream
  OVHyp (2^(-5:ℤ)) 1.6 t H₀ ∧ (t.leafMass H₀ : ℝ) ≤ 1.21 * H₀.card ∧
  (∀ M : ℝ, 2 ≤ M → (t.DeltaGe H₀ M : ℝ) ≤ 5.46 * 2^(-5:ℤ) * t.leafMass H₀ / Real.logb 2 M) ∧
  IsTauSplitTree (2^(-5:ℤ)) τ t H₀      -- then (c),(d) are ThinCutStatement / ThinCutEdgeStatement
```

**hazards:**

- **[risk] LEM14-TERMINATION.** 'The recursion terminates ... for every choice of witnesses' is a statement about a nondeterministic procedure. Lean: (T1) strict size decrease at every tau-split under tau >= 128 s log^2 |H| (needs U' ≠ ∅, i.e. tau > s, AND V\(U'∪N'') ≠ ∅, i.e. the 0.698 bound), (T2) existence of a tau-run (strong induction on |H|), and 'for every choice' = the global conclusions hold for EVERY t with IsTauRun. With only tau > s (the defTauRules requirement) a split can have U'∪N'' = V, child 1 = H, and the procedure can loop; so Run.Valid in s2:defHBtp must not presuppose termination (trees are finite by construction) and propExists must use T1/T2 with lemCap's bound tau_l >= 128 s_l log^2 |Q|.
- **[risk] LEM14-CONST-546.** (b)'s 5.46 needs 1.6(1 + 1/c_OV) <= 5.46, i.e. log_2(4/3) >= 0.414508 (true value 0.415037; slack 0.13%). The rational bound 12/29 that suffices for OV's 3.42 is not enough (gives 5.4667). See OV-CONST-546; use 17/41 (2^65 >= 3^41). Similarly 1/(1 - 5.472 eps) <= 1/(1 - 5.5 eps) = 1.20755 <= 1.21.
- **[note] LEM14-S-GE-1.** s >= 1 is essential: at s = 0 the hypothesis allows tau = 0, then H_out = {v ∈ U : deg >= 0} = U, U' = ∅, n_2 = m (no progress). s = s_l = ⌈Λ_l^100⌉ >= 40^100 in applications. Take s : ℕ with 1 ≤ s (IsExpander gets (s : ℝ)).
- **[note] LEM14-IND-HYP.** The inductions (deletions, leaf sizes) are over the tree with the claim for a subtree rooted at a node of size m; the hypothesis tau >= 128 s log^2 m is inherited because node sizes are <= n_0 and log is monotone on [1, ∞) (internal nodes have m >= 2). Children have sizes n_1, n_2 >= 1 (U' ≠ ∅; n_2 >= m/3), so log n_i >= 0 — needed for 2 + log n_i > 0 and for (8).
- **[note] LEM14-BM-BOUND-UNUSED.** The B-M leaf-size bound 2n_0 - 2n_0/(2 + log n_0) (and inequality (9), 7L^2 - 3.6L - 3.2 >= 0) is not used anywhere downstream (propOV and propDegRec use (b) via OV on the composite tree, and the deletion bound). Keep it as a separate Spec conjunct/lemma so it can be deprioritized (PLAN R7 'not used' policy) without touching the used parts.
- **[note] LEM14-SMALL-NUMERICS.** Small absolute constants to be checked by norm_num/nlinarith: 1/128 = eps/4; (1 + 3/64)(2/3) = 0.69792 <= 0.698; log_2 0.698 < -2/5 (0.698^5 = 0.1657 <= 1/4); 6 eps/log m <= 6/32 < 3/5; 3 eps = 3/32 < 1/10; 1.5·128/127 < 1.52 <= 1.6. All margins are comfortable except 0.698 (margin 1e-4 relative, still exact in ℚ).
- **[note] LEM14-DUP-SCOPE.** Dup in (c),(d) is the Dup of THIS tau-run. In s2:defHBtp the tau-run is grafted into the two-level recursion and s2:propOrigin uses Y^0 \ Dup*_r ⊆ Y^0 \ Dup(tau-run); the graft API must provide: leaves of the graft below the piece address a ↔ leaves of the tau-run at a, with equal graphs, so Dup(tau-run) ⊆ Dup*_l.

**effort:** ~750 Lean lines, difficulty 3/5 ((a-split) ~200 (degree double counting via Finset.sum over edges with exactly one end in U), (a-term) ~100, (a-del) ~150, (a-BM) ~150 (optional), (b) ~80, (c),(d) ~30 (from thin cut).)

### `s2:defHBtp` — definition: the hierarchy HB*^{tau+} (rules (R0)-(R5), (GC); valid runs) (s2.tex:496)

- **Manuscript referee status:** x2+RT
- **Formalization:** Defs EG/Defs/HB/Run.lean (constants-as-functions, RoundChoice, Run, derived objects as irreducible_def, Run.Valid) + a Run API (characterization lemmas, EG/Lib/HB/RunBasic.lean). No Spec of its own; every s2-s7 Spec about runs quantifies over (G, D_*, run) with run.Valid G D_*.

**Statement (precise restatement).** INPUT: a finite simple graph G, V(G), n := |V(G)|; constants eps = 2^-5, sigma = 100, C' = 103 (A = 105 is not used by the definition); a real D_* (its conditions (Gamma) are not needed to state the definition). Rounds l = 1, 2, ... (1-indexed); G_1 := G; every G_l, G'_l has vertex set V(G). (R0) d_l := 2|E(G_l)|/n ∈ R. If d_l < D_*: STOP, E_0 := E(G_l), R := l - 1. Otherwise lambda_l := log_2 d_l. (R1) t^HB_l := log_2^2 d_l, T_l := t^HB_l d_l. Repeatedly delete a cycle of length >= T_l (the lexicographically first for a fixed vertex order) until none remains; Cyc_l := the deleted cycles; G'_l := the remainder. So: the cycles of Cyc_l are pairwise edge-disjoint cycles of G_l, each of length >= T_l, E(G'_l) = E(G_l) \ ⋃ E(C), and G'_l has NO cycle of length >= T_l. (R2) M_l := max(2^40, 2^16 T_l log_2^4 T_l) [a REAL; see hazard HB-M-INTEGER]; Lambda_l := log_2 M_l; s_l := ⌈Lambda_l^100⌉ ∈ ℕ; P_l := ⌈lambda_l^103⌉ ∈ ℕ; tau_l := ⌈128 s_l log_2^2 M_l⌉ ∈ ℕ. (R3) FIRST LEVEL: an s=0 recursion t0_l on G'_l (s2:lemOVgeneric: every internal node carries a witness (U,F) with parameter 0, U' = U, N'' = N_H(U)) such that a node is a leaf IFF its graph is an (eps,0)-expander; its leaves (addresses a, graphs Q_a) are the s=0 PIECES of round l. SECOND LEVEL: for every piece a with |Q_a| >= P_l, a tau-run tR_{l,a} of Q_a with parameters (s_l, tau_l) (s2:lem14tau; any witnesses). The TWO-LEVEL RECURSION T_l is t0_l with tR_{l,a} grafted at every piece a with |Q_a| >= P_l (a split recursion on G'_l). Its leaves: the pieces with |Q| < P_l and the leaves of the tau-runs. Round-l PRE-PARTS := leaves of T_l with >= P_l vertices (= leaves of tau-runs with >= P_l vertices); a pre-part is named by its ADDRESS Z; Z^0 := its vertex set; X^0_Z := its leaf graph (a graph on Z^0). Dup*_l := {v : v lies in >= 2 leaves of T_l (any size)}. (R4) D_l := {v : v lies in >= 2 round-l pre-parts}. A HOME ORDER is a linear order of the round-l pre-parts (addresses). For v in some pre-part, home_l(v) := the first pre-part (in the home order) containing v. S_Z := {v ∈ Z^0 ∩ D_l : home_l(v) ≠ Z} (guests). Z is LIGHT iff (L1) |S_Z| <= |Z^0|/2; (L2) every u ∈ Z^0 has at most s_l/2 neighbours in S_Z in the graph G'_l[Z^0]; (GC) no x ∈ S_Z has >= theta^GC_l(Z^0) := ⌈|Z^0| lambda_l^{-1/2}⌉ neighbours in Z^0\S_Z in X^0_Z. Otherwise Z is STANDALONE; a pre-part satisfying (L1),(L2) but not (GC) is a GC-part (standalone). A light Z gives the LIGHT PART with vertex set Z^0\S_Z and graph X_Z := X^0_Z - S_Z. Std_l := set of standalone pre-parts (contains the GC-parts and those failing (L1) or (L2)). (R5) Each edge e of G'_l is assigned in this order: (1) if e ∈ E(X_Z) for a light Z, to (the light part) Z; if e ∈ E(X^0_Z) for a standalone Z, to Z [at most one Z, since the X^0_Z are edge-disjoint by SEP(i)]; (2) else, if both ends lie in the light part of some light Z, to the first such Z in the home order; (3) else, if both ends lie in Z^0 for some standalone Z, to 'the first such pre-part' [order unspecified; see HB-R5-ORDER]; (4) else e passes down: E(G_{l+1}) := the set of these edges. E_l(Z) := edges assigned at round l to Z. NAMING: pre-parts are leaves (distinct even if vertex sets coincide); for light Z the letter Z also denotes the vertex set Z^0\S_Z; a round-l PART is a light part or a standalone pre-part. A VALID HB*^{tau+} RUN is an execution with ANY witnesses in both levels of (R3), ANY vertex order in (R1) and ANY home orders in (R4); R is finite (s2:propExists). At s = 0 the tau-rules are idle, so the first level is B-M's recursion unchanged.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| constants eps, sigma, C' | 2^-5, 100, 103 | s1:defConstants(i) | no: EG/Defs/Constants.lean proposed by the s1 blueprint (EG.epsC, EG.sigmaC, EG.Cp) |
| round parameters as functions of d | lamOf d = logb 2 d; TOf d = logb 2 d ^ 2 * d; MOf d (see HB-M-INTEGER); LamOf d = logb 2 (MOf d); sOf d = ⌈LamOf d ^ 100⌉₊; POf d = ⌈lamOf d ^ 103⌉₊; tauOf d = ⌈128 * sOf d * logb 2 (MOf d) ^ 2⌉₊; thetaGC d z = ⌈z * lamOf d ^ (-(1/2))⌉₊ | (R0)-(R2), (GC) | no: new EG.HB.lamOf/TOf/MOf/LamOf/sOf/POf/tauOf/thetaGC |
| cycle, cycle length | EG.Obj.cycle c with WF (Nodup, length >= 3), edges EG.cycleEdges c, length c.length (as in the existing CapGraphStatement) | s1:defObject, (R1) | yes: EG.Obj, EG.cycleEdges |
| s=0 recursion, stop-at-expanders, tau-run, graft, leaves, Dup | IsS0Rec (s2:lemOVgeneric), IsTauRun (s2:lem14tau), STree.graft/leafAddrs/dup (s2:lemSEP) | s2:lemOVgeneric, s2:lem14tau, s2:lemSEP | no (new, earlier s2 nodes) |
| RoundChoice / Run (choices only) | per round: cycles : List (List V); tree0 : STree V; tauRun : List Bool → STree V; homeOrder : List (List Bool). Run := List RoundChoice (R = length) | s2:defHBtp | no: new EG.HB.RoundChoice, EG.HB.Run (PLAN §3 decision 5) |
| derived round objects | graph l (G_l), graph' l (G'_l), d l, twoLevel l, pieceAddrs l, piece l a, prePartAddrs l, Z0 l a, X0 l a, DupStar l, D l, home l v : Option address, guests l a (S_Z), isLight/isGCPart l a, Std l, partVerts l a, X l a, assign l e : Option address, E l a (E_l(Z)), E0, R | (R0)-(R5) | no: new, irreducible_def + characterization lemmas |
| Run.Valid G Dstar run | for l = 1..R: Dstar <= d l ∧ cycles valid ∧ IsS0Rec eps (tree0 l) (graph' l) ∧ leaves of tree0 l are exactly the (eps,0)-expander nodes ∧ ∀ piece a with POf (d l) <= \|Q_a\|: IsTauRun eps (sOf (d l)) (tauOf (d l)) (tauRun l a) (Q_a) ∧ homeOrder l is a Nodup list with toFinset = prePartAddrs l; and d (R+1) < Dstar | 'valid HB*^{tau+} run' | no: new |

**deps_declared** (manuscript \deps): s1:citLem14, s2:lem14tau, s1:defConstants, s2:lemOVgeneric, s2:lemSEP

**deps_from_proof:** s1:defConstants, s2:lemOVgeneric, s2:lem14tau, s2:lemSEP, s2:defWitness, s2:defTauRules, s1:citDef11, s1:defObject

**deps_notes:** A definition; 'deps_from_proof' lists what the definition's text needs: the s=0 recursion (OV), the tau-run (14^tau), split recursions and grafting (SEP), witnesses/tau-rules/expanders (undeclared but used through OV and 14^tau), cycles (s1:defObject). The parenthetical claim in (R5)(1) ('no edge assigned twice') is SEP(i); '(2^-5,s_l)-expander by s2:lem14tau' is the stopping rule; the (R3) 'equivalently' is trivial. s1:citLem14 is commentary.

**used_by:** s2:defAncestors; s2:lemCap; s2:propStructure; s2:lemEL; s2:propOV; s2:propDegRec; s2:propExists; s2:lemTower; s2:lemGC; s2:propOrigin; s2:propParentless; s2:remTauConstants; s3 (all ancestor-based statements); s5; s6:defDesign; s6:thmCONC; s6:thmCONCL; s6:lemJSLC; s6:lemJplus; s6:thmMIXC; s7:lemUHsplit; s1:condGamma (pointer)

**randomness:** none: the run is deterministic given its choices; 'any witnesses / vertex order / home orders' is universal quantification over Run.Valid. Std_l is deterministic (the random demotions of s5 are not part of the run).

**lean_shape:**

```lean
-- EG/Defs/HB/Run.lean (sketch; all derived defs are irreducible_def with characterization lemmas)
def lamOf (d : ℝ) : ℝ := Real.logb 2 d
def TOf (d : ℝ) : ℝ := Real.logb 2 d ^ 2 * d                                   -- t^HB_l d_l
def MOf (d : ℝ) : ℕ := ⌈max (2 ^ 40) (2 ^ 16 * TOf d * Real.logb 2 (TOf d) ^ 4)⌉₊ -- DECISION HB-M-INTEGER (else ℝ)
def sOf (d : ℝ) : ℕ := ⌈Real.logb 2 (MOf d) ^ 100⌉₊
def POf (d : ℝ) : ℕ := ⌈lamOf d ^ 103⌉₊
def tauOf (d : ℝ) : ℕ := ⌈128 * (sOf d : ℝ) * Real.logb 2 (MOf d) ^ 2⌉₊
def thetaGC (d : ℝ) (z : ℕ) : ℕ := ⌈(z : ℝ) * lamOf d ^ (-(1 / 2 : ℝ))⌉₊
structure RoundChoice (V : Type*) where
  cycles : List (List V)            -- (R1)
  tree0 : STree V                   -- (R3) first level on G'_l
  tauRun : List Bool → STree V      -- (R3) second level, read only at pieces with |Q| ≥ P_l
  homeOrder : List (List Bool)      -- (R4) order of pre-part addresses of twoLevel
structure Run (V : Type*) where
  rounds : List (RoundChoice V)     -- R := rounds.length; round l ↔ rounds[l-1]
namespace Run  -- (G : FGraph V) fixed; rounds 1-indexed
def graph : Run V → FGraph V → ℕ → FGraph V          -- G_l (verts = G.verts), by recursion on l
def d (run) (G) (l) : ℝ := 2 * ((run.graph G l).edges.card : ℝ) / G.card
def graph' run G l := (run.graph G l).deleteEdges ((cycles l).flatMap cycleEdges).toFinset
def twoLevel run G l : STree V := (tree0 l).graft (fun a => if POf (d l) ≤ (piece l a).card then tauRun l a else .nil)
def prePartAddrs run G l : Finset (List Bool) := (twoLevel l).leafAddrs.filter (fun a => POf (d l) ≤ (X0 l a).card)
def X0 run G l a := (twoLevel l).graphAtD (graph' l) a ; def Z0 run G l a := (X0 l a).verts
def DupStar run G l := (twoLevel l).dup (graph' l)
def D run G l : Finset V := G.verts.filter (fun v => 2 ≤ ((prePartAddrs l).filter (v ∈ Z0 l ·)).card)
def home run G l v : Option (List Bool) := (homeOrder l).find? (fun a => a ∈ prePartAddrs l ∧ v ∈ Z0 l a)
def guests run G l a : Finset V := (Z0 l a ∩ D l).filter (fun v => home l v ≠ some a)
def isLight run G l a : Prop := 2 * (guests l a).card ≤ (Z0 l a).card ∧
  (∀ u ∈ Z0 l a, ((((graph' l).induce (Z0 l a)).nbrs u ∩ guests l a).card : ℝ) ≤ sOf (d l) / 2) ∧
  (∀ x ∈ guests l a, (X0 l a).eBetween {x} (Z0 l a \ guests l a) < thetaGC (d l) (Z0 l a).card)
def Std run G l := (prePartAddrs l).filter (¬ isLight l ·)
def partVerts run G l a := if isLight l a then Z0 l a \ guests l a else Z0 l a
def X run G l a := (X0 l a).deleteVerts (guests l a)
def assign run G l (e : Sym2 V) : Option (List Bool) :=   -- (R5) steps (1),(2),(3); none = passes down
  step1 l e <|> (homeOrder l).find? (fun a => isLight l a ∧ e ∈ (partVerts l a).sym2)
           <|> (homeOrder l).find? (fun a => a ∈ Std l ∧ e ∈ (Z0 l a).sym2)
def E run G l a : Finset (Sym2 V) := (graph' l).edges.filter (assign l · = some a)    -- E_l(Z)
-- graph (l+1) := FGraph.ofEdges G.verts ((graph' l).edges.filter (assign l · = none))
def R (run) : ℕ := run.rounds.length ;  def E0 run G := (run.graph G (run.R + 1)).edges
def Valid (G : FGraph V) (Dstar : ℝ) (run : Run V) : Prop :=
  (∀ l ∈ Finset.Icc 1 run.R, Dstar ≤ run.d G l ∧ CyclesValid l ∧ IsS0Rec eps (tree0 l) (graph' l) ∧
     (∀ a ∈ (tree0 l).leafAddrs, ((tree0 l).graphAtD (graph' l) a).IsExpander eps 0) ∧
     (∀ a ∈ (tree0 l).leafAddrs, POf (d l) ≤ (piece l a).card → IsTauRun eps (sOf (d l)) (tauOf (d l)) (tauRun l a) (piece l a)) ∧
     (homeOrder l).Nodup ∧ (homeOrder l).toFinset = prePartAddrs l) ∧
  run.d G (run.R + 1) < Dstar
-- CyclesValid l: ∀ c ∈ cycles l, (Obj.cycle c).WF ∧ (∀ e ∈ cycleEdges c, e ∈ (graph l).edges) ∧ TOf (d l) ≤ c.length;
--   ((cycles l).flatMap cycleEdges).Nodup; and ∀ c, (Obj.cycle c).WF → (∀ e ∈ cycleEdges c, e ∈ (graph' l).edges) → (c.length : ℝ) < TOf (d l)
```

**hazards:**

- **[blocker] HB-M-INTEGER.** Definition-vs-use mismatch. (R2) defines M_l := max(2^40, 2^16 T log^4 T) with T = d_l log^2 d_l, an irrational REAL in general. Downstream uses need an INTEGER: s7 (s7.tex:183-184, 270, 280-297, 518) uses the colour set [4M_l] = [K^HUB_l] with uniformly random bijections [4M_l] → [4M_l] and 3-subsets of [4M_l]; s3:defCOL (s3.tex:1045, 1072) uses K^JS_l := M_l^2 as the NUMBER of JS classes (0 <= j < K^JS_l) and the probability K^JS_l rho_l = M_l^-2; s6:lemJSLC counts 'M_l - 1 cherry systems' and pads with ⌈(M_l-1)/2⌉. A Lean statement of (R2) must choose. Proposed manuscript decision: M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ (a natural number), with Lambda_l := log_2 M_l of that integer. Checked impact in s2: lemCap(ii) (|Q| <= 2^16 T log^4 T <= M_l) unaffected; propDegRec M_l <= d_l^2 (2^20 x^6 2^x + 1 <= 2^{2x}, huge slack); lemTower(b) M_l <= (A log lambda_{l-2})^{2A}, M_{l-1} >= 2M_l, Σ 1/M_l <= 2/D_*, P_{l-2}/2 >= M_l log^4 M_l all have factor-level slack; K^JS_l rho_l = M_l^-2 then holds exactly. Alternative (no manuscript change): keep M_l real and put ceilings at every use (K^HUB_l := ⌈4M_l⌉, K^JS_l := ⌈M_l^2⌉), which changes K^JS rho_l to <= M_l^-2 + M_l^-4 in s6:lemLost(i) (absorbed by the slack of 2|V(Y)|^-2). Either way the choice must be made before EG/Defs/HB/Run.lean is locked.
- **[risk] HB-R5-ORDER.** (R5)(3) assigns an edge 'to the first such pre-part' without naming the order ((R5)(2) says 'in the home order'). Proposed decision: the home order (the only order on pre-parts that the run fixes). Downstream uses of E_l(Z) for standalone Z (s4 TPV input, s6 beads/J-edges, lemCap degree bound, propStructure(iii) partition) use only: both ends in Z^0, disjointness across parts, E(X^0_Z) ⊆ E_l(Z); any deterministic choice works, but the Lean definition needs one. Alternative: make the step-(3) choice an extra field of RoundChoice (then 'valid run' quantifies over it).
- **[risk] HB-ADDRESS-IDENTITY.** Pieces, pre-parts, parts and ancestors must be identified by (round, address in T_l), never by vertex set: 'distinct pre-parts are counted separately even if their vertex sets coincide', home(v) ≠ Z and S_Z compare pre-parts, and (K1)-(K3), mu_r, dup_r count leaves. Every s2-s7 Spec must index parts by addresses (e.g. Z ∈ run.Std G l : Finset (List Bool)). Two pre-parts with equal vertex sets are possible in principle (then the second has S_Z = Z^0 and is standalone by (L1)); a vertex-set encoding would merge them.
- **[risk] HB-DATAMODEL.** Everything of round l (G_l, pieces, pre-parts, D_l, home, S_Z, light/Std, E_l(Z), G_{l+1}) is a function of (G, run, l) defined by recursion through all earlier rounds; Valid threads D_* <= d_l for l <= R and d_{R+1} < D_*. This is the largest definition of the project and all of s3-s7 read it. Needs: irreducible_def for every derived object, characterization lemmas (e.g. E_l(Z) edges lie in partVerts, (graph (l+1)).edges = passed edges, pre-part ↔ tau-run leaf inside a piece), and non-vacuity tests (a small G with R = 1 where every rule fires). Estimate 500 lines of definitions + 600 lines of API; P2-D must fix it before any s3-s7 Spec is written.
- **[risk] HB-GRAFT.** The two-level recursion is t0_l with tau-runs grafted at big pieces. propOV applies OV to the grafted tree (first-level splits c = 1, second-level c = 1.6), propOrigin compares Dup of a tau-run with Dup*_l and needs 'u ∉ Dup*_l ⇒ unique piece', lemCap needs 'pre-part ⊆ its piece'. The graft API must give: addresses of the graft = a ++ b; graphs at a ++ b = graphs of the grafted tree at b rooted at Q_a; leaves, internal nodes, labels, Dup correspondences. Without this, three s2 propositions have no clean proof path.
- **[risk] HB-STOPRULE.** Definition-vs-use: 'A node is a leaf iff its graph is an (eps,0)-expander': the direction 'internal ⇒ not an expander' follows from the witness required at internal nodes (s2:defWitness W0); Valid must require 'leaf ⇒ expander' explicitly (lemCap uses that pieces are (eps,0)-expanders; propStructure(i) that pre-parts are (eps,s_l)-expanders). Leaves of size < P_l that are not tau-run roots are pieces; no stopping condition at s_l for them. If Run.Valid is locked without 'leaf ⇒ (eps,0)-expander' (first level) and 'leaf ⇒ (eps,s_l)-expander' (tau-runs), lemCap(ii) and propStructure(i) become unprovable and a Tier-1 definition change is needed later.
- **[note] HB-R1-ENCODING.** 'Delete the lexicographically first long cycle for a fixed vertex order, repeatedly' (PLAN decision 7: fixed rules become existentials). Encode Cyc_l as ANY list of pairwise edge-disjoint well-formed cycles of G_l of length >= T_l whose removal leaves no cycle of length >= T_l. This enlarges the set of valid runs (every greedy sequence qualifies), so every '∀ valid run' statement becomes stronger; the consumers (propStructure(iii): Σ|Cyc_l| <= n; s5/s7 treat long cycles as objects) use only edge-disjointness, length >= T_l and the absence of long cycles in G'_l. Existence is the greedy argument (propExists).
- **[note] HB-VALID-NO-TERMINATION.** No circularity: Run.Valid does not require the hypotheses of Lemma 14^tau (tau_l >= 128 s_l log^2 |Q|); trees are finite by construction. Those hypotheses are consequences (lemCap(ii), needs D_* >= 2^117) used only to apply 14^tau and to prove existence (propExists).
- **[note] HB-L2-GRAPH.** (L2) counts neighbours in G'_l[Z^0] (a supergraph of X^0_Z), (GC) in X^0_Z. Keep both graphs; replacing G'_l[Z^0] by X^0_Z in (L2) would enlarge the set of light pre-parts and change Std_l. HS is applied through X^0_Z ⊆ G'_l[Z^0] (propStructure(i)).
- **[note] HB-PART-OVERLOAD.** The letter Z denotes a pre-part (address), Z^0, the light part's vertex set Z^0\S_Z, and the part itself; E_l(Z) belongs to the light part if Z is light. Lean: one address a, with partVerts l a := if light then Z0\guests else Z0; E l a indexed by the address.
- **[note] HB-REAL-NAT.** Types: d_l, lambda_l, T_l, Lambda_l ∈ ℝ; s_l, P_l, tau_l, theta^GC ∈ ℕ (ceilings); s_l/2 in (L2) is real (s_l may be odd); |S_Z| <= |Z^0|/2 as 2|S_Z| <= |Z^0| in ℕ; lambda_l^{-1/2} via Real.rpow (lambda_l > 1 under Gamma). d_l uses n = |V(G)| (isolated vertices count).
- **[note] HB-DEGENERATE-N.** n = 0: Lean gives d_1 = 0 (x/0 = 0), so the run stops at once iff D_* > 0 (true under Gamma). Rounds are 1-indexed; avoid ℕ-subtraction l - 1 in the list index by a helper 'round l' with 1 <= l.
- **[note] HB-EMBEDDED-CLAIMS.** The definition's text contains claims that are lemmas, not definitions: (R5)(1) 'no edge is assigned twice' (SEP(i) on T_l), (R3) 'X^0_Z is a (2^-5,s_l)-expander' (stopping rule), '(R3) equivalently' (pre-parts = big leaves of T_l = big tau-run leaves), 'Std_l contains the GC-parts ...'. Put them in the Run API with proofs; step1 of assign must be defined so that it is well defined even without the disjointness (e.g. via find? on the home order).
- **[note] HB-MMAX-INACTIVE.** Under Gamma2(a) (T_l >= 2^117) the max in M_l is never 2^40 for l <= R (2^16 T log^4 T >= 2^133). Gamma2(b)'s phrase 'including rounds with M_l = 2^40' is vacuous. Harmless.
- **[note] HB-DSTAR-PARAM.** D_* enters the definition only through the stop rule; the Gamma conditions are hypotheses of the lemmas (e.g. lemCap(ii): D_* >= 2^117), never of Valid. Order of constants (s1:remOrder): D_* is fixed before G, so Specs read ∀ D_* (hyps) ∀ G ∀ run, run.Valid G D_* → ... .

**effort:** ~1100 Lean lines, difficulty 4/5 (Definitions ~500 (recursion over rounds, graft, assignment), API ~600 (characterizations, partition of E(G'_l), pre-part/piece correspondence, non-vacuity tests). The hard part is the design, not the proofs.)

### `s2:defAncestors` — definition: ancestors, typing, multiplicities (s2.tex:587)

- **Manuscript referee status:** x2
- **Formalization:** Defs EG/Defs/HB/Run.lean (ancestor data as functions of (run, r, address); anc, hubs, ports, fresh, classed, mu, dup, mult, j0, j1)

**Statement (precise restatement).** Fix a valid run (G, D_*, R). For every round r ∈ [1,R] and every round-r pre-part Y there is EXACTLY ONE ancestor of round r attached to Y (so ancestors of round r are in bijection with round-r pre-parts): if Y is light, the light part: V(Y) := Y^0\S_Y, H_Y := X_Y = X^0_Y - S_Y, eps_Y := 2^-6, s_Y := s_r/2 (real); if Y ∈ Std_r (GC-parts included): V(Y) := Y^0, H_Y := X^0_Y, eps_Y := 2^-5, s_Y := s_r. r(Y) := r; L_Y := log_2 |V(Y)|; V(Y) ⊆ Y^0. For l >= 3 and a vertex x: anc_l(x) := {ancestors Y : r(Y) <= l - 2, x ∈ V(Y)}; anc_l(x) := ∅ for l <= 2 (equivalently, for all l: {Y : r(Y) + 2 <= l, x ∈ V(Y)}, since rounds start at 1). For Z ∈ Std_l: hubs A_Z := Z^0 ∩ D_l; ports U_Z := Z^0\D_l; fresh ports F_Z := {x ∈ U_Z : anc_l(x) = ∅} (all ports are fresh for l <= 2); classed ports Q_Z := U_Z\F_Z. For a round r and a vertex w: mu_r(w) := #{round-r pre-parts Z : w ∈ Z^0} (so D_r = {w : mu_r(w) >= 2}); dup_r := Σ_{w ∈ V(G)} (mu_r(w) - 1)^+; mult_r(w) := #{ancestors Y of round r : w ∈ V(Y)}. j_0(x) := the first round r ∈ [1,R] in which x lies in a pre-part [no value is specified if there is none; take ∞]; j_1(x) := the first round in which x lies in a light part (∞ if none).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| pre-parts, light/standalone, S_Z, X^0_Z, X_Z, D_l, s_r, Std_l | s2:defHBtp | s2:defHBtp | no (new, s2:defHBtp) |
| ancestor (r, a) | a pair (round r ∈ [1,R], a ∈ prePartAddrs r); its type is isLight r a | s2:defAncestors | no: new (use ℕ × List Bool, or a structure Anc) |
| ancVerts r a, ancGraph r a, ancEps r a, ancS r a, LY r a | V(Y) = partVerts r a; H_Y = if light then X r a else X0 r a; eps_Y ∈ {2^-6, 2^-5}; s_Y ∈ {s_r/2, s_r} (ℝ); L_Y = logb 2 \|V(Y)\| | s2:defAncestors | no: new |
| anc l x | Finset (ℕ × List Bool) of (r, a) with 1 <= r, r + 2 <= l, a ∈ prePartAddrs r, x ∈ ancVerts r a | s2:defAncestors | no: new EG.HB.Run.anc |
| hubs, ports, fresh, classed | Z0 l a ∩ D l; Z0 l a \ D l; (ports l a).filter (anc l · = ∅); ports \ fresh | s2:defAncestors | no: new |
| mu r w, dup r, mult r w | #{a ∈ prePartAddrs r : w ∈ Z0 r a}; Σ_{w ∈ G.verts} (mu r w - 1) (ℕ truncated subtraction = (·)^+); #{a ∈ prePartAddrs r : w ∈ ancVerts r a} | s2:defAncestors | no: new |
| j0 x, j1 x | WithTop ℕ (or ℕ∞): least r ∈ [1,R] with x in a pre-part (resp. light part) of round r, ⊤ if none | s2:defAncestors | no: new |

**deps_declared** (manuscript \deps): s2:defHBtp

**deps_from_proof:** s2:defHBtp

**deps_notes:** A definition. The sentence 'Every ancestor corresponds to a distinct pre-part Y^0 ⊇ V(Y)' is a (trivial) claim; in Lean it is definitional because ancestors are indexed by pre-part addresses.

**used_by:** s2:propStructure; s2:lemEL; s2:propOV; s2:lemTower; s2:lemGC; s2:propParentless; s3:defCOL; s3:lemCOLJV; s3:lemCOL; s5:defZones; s5:defStages; s6:defDesign (designation Y(u) ∈ anc_l(u)); s6:defLending (A_Z, F_Z, Q_Z); s7 (mult_r, ancestors of pooled vertices)

**randomness:** none

**lean_shape:**

```lean
namespace EG.HB.Run
def ancVerts (run : Run V) (G : FGraph V) (r : ℕ) (a : List Bool) : Finset V := run.partVerts G r a
def ancGraph run G r a : FGraph V := if run.isLight G r a then run.X G r a else run.X0 G r a
def ancEps run G r a : ℝ := if run.isLight G r a then 2 ^ (-6 : ℤ) else 2 ^ (-5 : ℤ)
def ancS run G r a : ℝ := if run.isLight G r a then (sOf (run.d G r) : ℝ) / 2 else sOf (run.d G r)
def LY run G r a : ℝ := Real.logb 2 (run.ancVerts G r a).card
def ancestors run G (r : ℕ) : Finset (List Bool) := run.prePartAddrs G r      -- bijection with pre-parts
def anc run G (l : ℕ) (x : V) : Finset (ℕ × List Bool) :=
  ((Finset.Icc 1 run.R).filter (fun r => r + 2 ≤ l)).sigma-like biUnion (fun r => ((run.prePartAddrs G r).filter (x ∈ run.ancVerts G r ·)).image (r, ·))
def hubs run G l a := run.Z0 G l a ∩ run.D G l
def ports run G l a := run.Z0 G l a \ run.D G l
def fresh run G l a := (run.ports G l a).filter (fun x => run.anc G l x = ∅)
def classed run G l a := run.ports G l a \ run.fresh G l a
def mu run G r (w : V) : ℕ := ((run.prePartAddrs G r).filter (w ∈ run.Z0 G r ·)).card
def dup run G r : ℕ := ∑ w ∈ G.verts, (run.mu G r w - 1)
def mult run G r (w : V) : ℕ := ((run.prePartAddrs G r).filter (w ∈ run.ancVerts G r ·)).card
def j0 run G (x : V) : WithTop ℕ := -- least r ∈ Icc 1 R with ∃ a ∈ prePartAddrs r, x ∈ Z0 r a, else ⊤
def j1 run G (x : V) : WithTop ℕ := -- least r with ∃ a, isLight r a ∧ x ∈ partVerts r a, else ⊤
-- sanity lemmas (API): D r = G.verts.filter (2 ≤ mu r ·); mult r w ≤ mu r w; anc l x = ∅ for l ≤ 2
```

**hazards:**

- **[risk] ANC-ROUND-OFFSET.** 'r(Y) <= l - 2' with ℕ subtraction, and 'anc_l = ∅ for l <= 2', silently depend on rounds being 1-indexed: with 0-indexed rounds (List index) round 0 would satisfy r <= l - 2 = 0 at l = 1, 2 and F_Z would change (fresh ports at rounds 1-2 would become classed), breaking (K4), s6:defDesign and the 338n fresh-port charge. Write the condition as r + 2 <= l with 1 <= r and add a test (anc G l x = ∅ for l ≤ 2).
- **[note] ANC-J0-INFTY.** j_0(x) has no 'infinity if none' clause (j_1 has). All uses (propParentless(i)) have x in a pre-part; define both in WithTop ℕ (or ℕ∞) so the definitions are total.
- **[note] ANC-BIJECTION.** 'Every ancestor corresponds to a distinct pre-part' is an injection in the text; with ancestors indexed by pre-part addresses it is a bijection by definition, so #ancestors of round r = #pre-parts of round r and mult_r(w) <= mu_r(w) is immediate (propOV (F11)).
- **[note] ANC-SY-REAL.** s_Y = s_r/2 for light Y is real (s_r ∈ ℕ may be odd); IsExpander takes ℝ, fine. eps_Y and s_Y are the parameters of propStructure(i) ('H_Y is an (eps_Y,s_Y)-expander, min degree > s_Y').
- **[note] ANC-STD-ONLY.** Hubs/ports/fresh/classed are defined only for Z ∈ Std_l; Lean defs are total over addresses, and statements carry a ∈ run.Std G l. For l <= 2 all ports are fresh (anc empty); s6:defLending sets Q*_Z = ∅ there.
- **[note] ANC-DUP-POSPART.** dup_r = Σ_w (mu_r(w) - 1)^+ over w ∈ V(G); ℕ truncated subtraction implements (·)^+ exactly. Do not confuse with Dup (SEP), Dup*_l (defHBtp) or dup_{>=M}(v) (OV) — four different objects with similar names.

**effort:** ~250 Lean lines, difficulty 2/5 (Definitions ~120; basic API (D_r via mu, mult <= mu, anc_l = ∅ for l <= 2, fresh ↔ j_0 characterization is propParentless, not here) ~130.)

### `s2:lemCap` — lemma: Lemma-25 size cap (fact F2) (s2.tex:622)

- **Manuscript referee status:** x2+RT
- **Formalization:** (i) and the remark: EXISTING Spec EG.Spec.CapStatement, EG.Spec.CapUniformStatement, proved sorry-free (EG.cap, EG.cap_uniform, EG.cap_remark_counterexample); graph step: existing EG.Spec.CapGraphStatement (EG.cap_graph, depends on the sorry'd EG.bmLemma25). (ii): new Spec EG/Spec/HB/Cap.lean CapRunStatement over valid runs.

**Statement (precise restatement).** (i) For all reals m, T: m >= 2^40, T >= 2^117 and m < 18432 T log_2^4 m imply m <= 2^16 T log_2^4 T. (Remark, not used: (i) is false for T = 2^20, m = 2^55; uniform form: for all T >= 1, m < 18432 T log^4 m implies m <= max(2^40, 2^16 T (log T + 40)^4).) (ii) HYPOTHESIS (Gamma2(a), implicit in 'valid run' + s1:defConstants(iii)): D_* >= 2^117. For every valid run and every round l ∈ [1,R]: every s=0 piece Q of round l has |Q| <= M_l; hence every round-l pre-part Z has |Z^0| <= M_l; for every round-l part Z (light part or standalone pre-part) and every vertex v, deg_{E_l(Z)}(v) <= M_l - 1; and tau_l >= 128 s_l log_2^2 |Q| for every piece Q, so the hypotheses of s2:lem14tau (H_0 = graph of Q, n_0 = |Q|, s = s_l >= 1, tau = tau_l) hold for every piece with |Q| >= P_l. Proof of (ii): T := t^HB_l d_l = d_l log^2 d_l >= 2^117 (d_l >= D_* >= 2^117); if |Q| >= 2^40, the piece graph is a (2^-5,0)-expander (stopping rule), so by s1:citLem25 (eps = 2^-5, m >= 2^40 = 2^30/eps^2, m >= 2) it has a cycle of length >= m/(18432 log^4 m); this cycle is a cycle of G'_l (piece ⊆ G'_l), so its length is < T by (R1); (i) gives m <= 2^16 T log^4 T <= M_l. Pre-parts are tau-run leaves inside a piece; E_l(Z) edges have both ends in V(Z) ⊆ Z^0 (R5).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| valid run, pieces, pre-parts, parts, E_l(Z), M_l, s_l, tau_l, P_l, t^HB_l, d_l | s2:defHBtp | s2:defHBtp | no (new, s2:defHBtp) |
| cycle of a graph, length | (EG.Obj.cycle c).WF ∧ cycleEdges c ⊆ E; length c.length | s1:defObject | yes (as in CapGraphStatement) |
| degE | number of edges of an edge set at v | s1:convGraphs(c) | yes: EG.degE |

**deps_declared** (manuscript \deps): s1:citLem25, s1:condG2, s2:defHBtp, s2:lem14tau

**deps_from_proof:** s1:citLem25, s1:condG2, s2:defHBtp, s2:lemSEP, s1:citDef11

**deps_notes:** ms_deps_v6.json records s1:condGamma (the enclosing environment of the \namedlabel s1:condG2); only Gamma2(a) (D_* >= 2^117) is used. s2:lemSEP (0') (node graphs are subgraphs of the root; a pre-part lies inside its piece) is used but not declared. s2:lem14tau appears only in the conclusion ('so Lemma 14^tau applies'), not in the proof. s1:citLem25 is used in its T0-corrected form (m >= max(2, 2^30/eps^2)).

**used_by:** s2:propStructure (ii); s2:propDegRec; s2:propExists; s2:lemTower; s2:propOrigin; s2:propParentless; s6:lemJSLC; s6:lemJplus; s7:lemEXprime; s1:remBMused/condGamma (pointers)

**randomness:** none

**lean_shape:**

```lean
-- existing (EG/Spec/HB/Cap.lean): CapStatement, CapUniformStatement, CapGraphStatement
def CapRunStatement : Prop := ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : HB.Run V),
  2 ^ 117 ≤ Dstar → run.Valid G Dstar → ∀ l ∈ Finset.Icc 1 run.R,
    (∀ a ∈ run.pieceAddrs G l, ((run.piece G l a).card : ℝ) ≤ HB.MOf (run.d G l)) ∧
    (∀ a ∈ run.prePartAddrs G l, ((run.Z0 G l a).card : ℝ) ≤ HB.MOf (run.d G l)) ∧
    (∀ a ∈ run.prePartAddrs G l, ∀ v : V, (EG.degE (run.E G l a) v : ℝ) ≤ HB.MOf (run.d G l) - 1) ∧
    (∀ a ∈ run.pieceAddrs G l, 128 * (HB.sOf (run.d G l) : ℝ) * Real.logb 2 (run.piece G l a).card ^ 2 ≤ HB.tauOf (run.d G l))
-- proof: cap_graph (existing) applied to the piece graph with T := TOf (d l), plus the Run API
```

**hazards:**

- **[risk] CAP-L25-CONST.** (i) has razor-thin margins that are already machine-checked (18432·1.37317^4 = 65534.45 <= 65536; at log T = 117: 43.661 vs 43.481), but they rest on the constant 18 of the explicit B-M Lemma 25 (18432 = 18·2^10), whose Lean proof (EG.bmLemma25) is still sorry (s1 hazard L25-CONST18). If that proof only reaches a constant C > 18, (i) fails at T = 2^117. Mitigation that needs no change to M_l: for any C < 64, χ(B) >= C·2^10·T holds for B = 2^16 T log^4 T once log T >= x_0(C) (log B = log T (1 + o(1))), and T >= D_* is galactic; so Gamma2(a) would become an eventuality 'D_* >= 2^{x_0(C)}' (R6 style). For C >= 64 the factor 2^16 in (R2) must grow.
- **[risk] CAP-GAMMA-EXPLICIT.** Implicit hypothesis. (ii) says 'in every round l <= R of a valid run' with no hypothesis on D_*, but the proof needs D_* >= 2^117 (Gamma2(a)): with small D_* a piece can exceed M_l. The Spec must carry 2^117 <= Dstar (not the whole Gamma bundle; s1 blueprint decision: s2 statements take only the Gamma items they cite).
- **[note] CAP-RUN-API.** (ii) needs three Run-API facts not stated in the manuscript: the piece graph is a subgraph of G'_l (SEP 0'), every pre-part is a tau-run leaf below a piece and Z^0 ⊆ V(Q) (graft API), and every edge of E_l(Z) has both ends in partVerts ⊆ Z^0 ((R5), also propStructure(iii)). A cycle of the piece graph is a cycle of G'_l because list cycles are edge sets (monotonicity of '∀ e ∈ cycleEdges c, e ∈ E').
- **[note] CAP-M-CEIL.** With the proposed M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ (HB-M-INTEGER) the proof is unchanged (monotone); with M_l ∈ ℕ the degree bound becomes deg <= M_l - 1 in ℕ, as used in s6:lemJSLC/lemJplus ('each receives at most M_l - 1 charges').
- **[note] CAP-DEPENDS-SORRY.** Until EG.bmLemma25 is proved, CapRunStatement's proof depends on sorryAx through EG.cap_graph; the ratchet should track it as downstream of s1:citLem25.

**effort:** ~250 Lean lines, difficulty 2/5 ((i), remark and graph step exist (~330 lines, done in P1b). (ii) ~250 lines given the Run/graft API.)

### `s2:lemHS` — lemma: Lemma HS (deleting a thin set keeps expansion) (s2.tex:676)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/HS.lean (HSStatement, HSCorStatement); pure graph lemma, independent of the hierarchy

**Statement (precise restatement).** Let eps' > 0 and s >= 0 be reals, X a finite simple graph with z := |V(X)| >= 11 that is an (eps',s)-expander, W ⊆ V(X) with |W| <= z/2, and s_W a real with s_W <= s such that every u ∈ V(X)\W has at most s_W neighbours in W in X (|N_X(u) ∩ W| <= s_W). Put z' := z - |W| = |V(X)\W|. Then X - W := X[V(X)\W] is an (eps'(log_2 z'/log_2 z)^2, s - s_W)-expander (on its z' vertices; the log in Def 11 is log_2 z'), and eps'(log_2 z'/log_2 z)^2 >= eps'/2. In particular, if X is a (2^-5, s)-expander and s_W = s/2, then X - W is a (2^-6, s/2)-expander with vertex set V(X)\W (this gives the light X_Z). (s_W >= 0 is forced: V(X)\W ≠ ∅ since z' >= z/2 > 0.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| IsExpander, deleteVerts, nbrs, nbrSet, deleteEdges, edgesBetween | s1:citDef11, s1:convGraphs | s1 | yes: EG.FGraph.IsExpander, deleteVerts, nbrs, nbrSet, deleteEdges, edgesBetween |
| IsExpander.mono (smaller eps) | an (eps_a,s)-expander is an (eps_b,s)-expander for eps_b <= eps_a | s2:lemHS last sentence (= s3:lemMonotone(i)) | yes: EG.FGraph.IsExpander.mono |

**deps_declared** (manuscript \deps): s1:citDef11

**deps_from_proof:** s1:citDef11, s1:convGraphs

**deps_notes:** The proof applies Def 11 to X with F := F' ∪ E_X(U,W) and uses monotonicity in eps (stated inline; in Lean EG.FGraph.IsExpander.mono).

**used_by:** s2:propStructure (i) (light X_Z is a (2^-6, s_l/2)-expander)

**randomness:** none

**lean_shape:**

```lean
def HSStatement : Prop := ∀ (V : Type u) [DecidableEq V] (X : FGraph V) (W : Finset V) (ε' s sW : ℝ),
  0 < ε' → 0 ≤ s → sW ≤ s → 11 ≤ X.card → W ⊆ X.verts → (W.card : ℝ) ≤ X.card / 2 →
  (∀ u ∈ X.verts \ W, ((X.nbrs u ∩ W).card : ℝ) ≤ sW) → X.IsExpander ε' s →
  (X.deleteVerts W).IsExpander (ε' * (Real.logb 2 ((X.card : ℝ) - W.card) / Real.logb 2 X.card) ^ 2) (s - sW) ∧
  ε' / 2 ≤ ε' * (Real.logb 2 ((X.card : ℝ) - W.card) / Real.logb 2 X.card) ^ 2
def HSCorStatement : Prop := ∀ (V : Type u) [DecidableEq V] (X : FGraph V) (W : Finset V) (s : ℝ),
  0 ≤ s → 11 ≤ X.card → W ⊆ X.verts → (W.card : ℝ) ≤ X.card / 2 →
  (∀ u ∈ X.verts \ W, ((X.nbrs u ∩ W).card : ℝ) ≤ s / 2) → X.IsExpander EG.epsC s →
  (X.deleteVerts W).verts = X.verts \ W ∧ (X.deleteVerts W).IsExpander (2 ^ (-6 : ℤ)) (s / 2)
```

**hazards:**

- **[note] HS-NUMERIC.** (log z'/log z)^2 >= 1/2 from z' >= z/2, z >= 11: the manuscript's route (log_2 11 >= 2 + √2 = 3.4142) involves √2. Lean route: a := log_2 z >= log_2 11 >= 3.45 (11^20 >= 2^69), log_2 z' >= a - 1 > 0, and (a-1)^2 >= a^2/2 ⟺ (a-2)^2 >= 2, true as 1.45^2 = 2.1025. Exact, norm_num/nlinarith.
- **[note] HS-CARD.** |X - W| = z - |W| needs W ⊆ V(X) (deleteVerts = induce (verts \ W)); the expansion parameter of the conclusion must be written with this card (Def 11 uses log of the graph's own card). U ranges over subsets of V(X)\W, F' over subsets of E(X - W); the proof's F := F' ∪ E_X(U,W) needs E_X(U,W) ⊆ E(X) and |E_X(U,W)| <= s_W|U| (sum over u ∈ U of |N_X(u) ∩ W|).
- **[note] HS-APPLICATION-GRAPH.** In propStructure(i) the hypothesis comes from (L2), which bounds neighbours in G'_l[Z^0] ⊇ X^0_Z; the transfer needs nbrs monotonicity under ≤ (existing API: nbrSet_mono / deg_mono) and X^0_Z ≤ G'_l[Z^0] (SEP 0' + edges inside Z^0). Also z = |Z^0| >= P_l >= 11 needs Gamma (lambda_l large).

**effort:** ~150 Lean lines, difficulty 2/5 (Neighbourhood identity N_{X-F}(U) = N_{(X-W)-F'}(U) ~60 lines, card bound for E_X(U,W) ~30, log numerics ~40, corollary ~20.)
