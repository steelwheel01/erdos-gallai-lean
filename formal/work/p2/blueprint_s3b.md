# P2-U formalization blueprint: chunk s3b (s3: Lemma 9_rho, Theorem 16*, Lemma HB, the lending colouring COL-JV, the COL-JV table, Lemma COL)

Manuscript: `proofs/manuscript/s3.tex` lines 690-1587 (v6 working copy of 2026-09-26 09:14, which carries uncommitted G0/integration edits relative to commit d6f3c49: HB title, "not needed below" in the HB proof, row 8(b) "not used" note, lemCOL(e) wording, Haxell class names; none changes a statement of this chunk). A CANDIDATE proof, AI-reviewed only. Machine-readable twin: `formal/work/p2/nodes_s3b.json` (same content, same field names as `nodes_s1.json`, `nodes_s2a.json`, `nodes_s3a.json`). Line numbers refer to the working copy of `s3.tex`. Existing Lean names were checked against `formal/EG/**` (EG.FGraph, IsExpander(.lt_deg), IsPathConnected(.exists_paths, .mono), EG.ball (+ ball_mono_edges/left), EG.FGraph.colourClass, EG.FinDist.{pi, prod, map, uniform, bernoulli, dirac, ofFinset, cond, randColouring, rsubset, IsRSubset, IndepFun, iIndepFun}, IsRSubset.{cond_of_indepFun, chernoff_card_lower_half, subset_ae}, map_snd_cond_prod_fst, prob_prod_snd, map_selectSet_randColouring, EG.l15p, l15p_of_map_eq, l15p_prod_fst); all other names are proposals. The (eqStar) names EG.Star.* are those proposed by the s3a blueprint; the run/ancestor names EG.HB.Run.* those of the s2a blueprint.

The chunk's labels are s3:lemL9rho, s3:thmT16s, s3:lemHB, s3:defCOL, s3:lemCOLJV, s3:lemCOLJVev, s3:lemCOL. One SUPPORTING node is added: `s3:tabCOLJV` (the COL-JV table), because s1:condG1(f), s3:lemCOLJV, s3:lemCOLJVev and s7:lemGammaSat all refer to its formulas and no chunk list owns it.

## 1. Summary

| label | kind | formalization | new Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s3:lemL9rho` | lemma | Spec EG/Spec/Link/L9rho.lean (L9rhoStatement) + proof EG/Proof/Link/L9rho.lean. The proof  | 650 | 3 | risk (L9-HAXELL-UNIVERSE) |
| `s3:thmT16s` | theorem | Spec EG/Spec/Link/T16s.lean (T16sStatement, 'every rho-random subset' form over an arbitra | 450 | 3 | risk (T16-STEP1-PRODUCT) |
| `s3:lemHB` | lemma | Spec EG/Spec/Link/HB.lean (HBStatement) + proof EG/Proof/Link/HB.lean (Mathlib Hall: Finse | 320 | 3 | risk (HB-UNREVIEWED) |
| `s3:defCOL` | definition | Defs EG/Defs/Lend/COL.lean (index tags and index Finsets, per-edge and label laws, outcome | 750 | 4 | blocker (COL-M-INTEGER) |
| `s3:tabCOLJV` | table (supporting node, not in the chunk list) | Defs EG/Defs/Lend/COLTable.lean: EG.COLTable.{lam, Mbar, kbar, row : Fin 13 → ℝ → Prop, co | 120 | 1 | risk (TAB-NO-OWNER) |
| `s3:lemCOLJV` | lemma | Spec EG/Spec/Lend/COLJV.lean (COLJVStatement: per-ancestor part (i), rows 3-10 in precise  | 750 | 3 | risk (COLJV-N0-IMPLICIT) |
| `s3:lemCOLJVev` | lemma | Spec EG/Spec/Lend/COLJVev.lean (COLJVevStatement) + proof EG/Proof/Lend/COLJVev.lean. Pure | 450 | 2 | note (EV-GAMMASAT-SHAPE) |
| `s3:lemCOL` | lemma | Event predicates EG.Lend.{COLa, COLb, COLc, COLe, COLg} in EG/Defs/Lend/COL.lean (they are | 800 | 4 | risk (COL-CONDITIONAL-L15) |

Estimated new Lean for this chunk: **~4290 lines** (excluding the stage-alpha Haxell theorem, B-M Prop 8 (s1, ~600), (eqStar)/L15p/P18s (s3a) and the s2 run API). **One blocker, inherited:** COL-M-INTEGER (= s2a HB-M-INTEGER): K^JS_l := M_l^2 is a class COUNT, so M_l must be an integer (or ceilings inserted) before the lending data can be defined. Every statement was re-derived, including all 13 table rows (column 2 from column 3, and the column-4 triples), the Hall argument of Lemma HB and the Haxell argument of Lemma 9_rho (both v6 rewrites with one AI review): no mathematical error was found. The main risks are (1) data-model decisions for the stage-1 lending data (empty lent-index family, own labels for standalone parts, colourings of the random edge sets Lend_Y/Own_Y), (2) conditional applications of L15p and T16* inside Lemma COL, (3) implicit hypotheses (n >= N_0 through propStructure), (4) the universe of the stage-alpha Haxell hypothesis, (5) the informal column 2 of the table, and (6) the consumer-exclusivity rule COL(g), which is a design constraint on s4-s6 rather than a lemma.

## 2. Cross-cutting decisions proposed for the integrator

- **Ownership.** This chunk owns `EG/Defs/Lend/COLTable.lean` (the table: `EG.COLTable.{lam, Mbar, kbar, row, col3, triple, TypeE, v0}`) and `EG/Defs/Lend/COL.lean` (the stage-1 lending data and the event predicates `COLa/COLb/COLc/COLe/COLg`), and the Specs `EG/Spec/Link/{L9rho, T16s, HB}.lean`, `EG/Spec/Lend/{COLJV, COLJVev, COL}.lean`. s1's `Gamma1` item (f) must be `EG.COLTable.col3` (the s1 blueprint calls it `EG.S3.COLJVcol3`: rename or alias), so that G1(f), COLJV and COLJVev (hence s7:lemGammaSat) talk about one formula.
- **Decide M_l ∈ ℕ first (blocker COL-M-INTEGER).** Recommended (as s2a): M_l := ⌈max(2^40, 2^16 T log^4 T)⌉₊. Then K^JS_l = M_l^2 : ℕ, ρ_l = M_l^-4, t^JS_l = 2M_l + 2 : ℕ, and K^JS_l ρ_l = M_l^-2 exactly. Only (B6) needs a one-line adaptation (COLJV-B6-CEILING).
- **Stage-1 lending data model (s3:defCOL).** Per ancestor Y = (r, a): per-edge labels on the FIXED edge set E(H_Y): `(bit : Bool, idx : Option LentTag, own : Fin (kown Y))`, with `idx` uniform on `lentIdx Y` (dirac `none` if empty, i.e. r >= R-1) and `kown := 4⌊log2(L_Y/8)⌋₊ + 1` defined for every Y (unused for standalone Y); JS labels `Option ℕ` on the sites {(l, y) : r+2 <= l <= R, y ∈ V(Y)}; `colLaw Y` the product. Classes are `colourClass` of H_Y (spanning on V(Y)). This resolves s3a hazard L15-RANDOM-EDGESET: L15p applies slice-wise given the bits. The global stage-1 space is a product over ancestors (and zones, pools): fix it once in P2-D with named projections.
- **Random-set statements in "arbitrary finite space" form.** T16* quantifies over (Ω, μ, R) with `μ.IsRSubset R X.verts ρ` and `0 < ρ` (as L17*, P18*(ii) in s3a). Lemma COL quantifies over (Ω, μ, D) with `μ.map D = colLaw Y`, and for (c) over a family `Vs` with JOINT independence `μ.IndepFun D Vs`. Universe: Ω : Type u.
- **Stage alpha.** L9rho, T16*, Lemma COL (and every s4-s7 consumer of T16*) are proved from `EG.Spec.HaxellStatement` (and `BMProp8Statement` until B-M Prop 8 is proved) passed as hypotheses of the PROOF terms; the Specs are hypothesis-free. HaxellStatement must be universe-polymorphic (`α : Type u`) or L9rho needs a transport to `Fin N` (L9-HAXELL-UNIVERSE); lock the q^2-form (nonempty X', |Z| < q^2|X'|), which is exactly what L9rho verifies (L9-HAXELL-FORM).
- **Run context.** The COL Specs need Gamma1, `run.Valid`, and (unless s2:propStructure drops it) `N_0 <= |V(G)|`; recommend one bundled `RunCtx` hypothesis used uniformly by all s3-s7 run-based Specs (COLJV-N0-IMPLICIT).
- **Column 2 of the table is informal**: lemCOLJV(ii) must assert the precise requirements C1-C13 listed in node s3:tabCOLJV (row 3 with all three L15p levels; rows 4-7 in the exact form lemCOL applies T16*); these predicates (`EG.Lend.COLReq*`) are what s5/s6/s7 consume.
- **Export what consumers take from proofs.** s5:lemE1(b) re-enters the proof of Lemma COL for the bound P(COL(a) fails) <= 2(2 + k_lend + k_own)N^-5: export it in the COL Spec. s5:defStages and s6:defLending need the COL(a)/COL(b) events as named predicates of the outcome.
- **COL(g) exclusivity** is a design rule: s3 proves only partition facts; s5:lemParent, s6:lemJSLC, s6:defJconsumer, s6:consOrder must restrict each consumer's input to its class by construction and prove exclusivity there.
- **Undeclared / non-logical dependencies (for usesgen/msreport).** Attribution only: s1:citLem9 (L9rho), s1:citThm16 (T16*). Genuine but undeclared: s3:eqStar in L9rho, T16*; s3:tabCOLJV in lemCOLJV, lemCOL; s2:defHBtp in defCOL, lemCOLJV. Declared but not logical: s3:propP13s, s3:lemL17s in T16* (only via P18s); s3:lemL15p, s3:thmT16s in lemCOLJV (formulation only). Forward references: s6:consOrder and s3:lemCOL in defCOL; s3:lemCOLJVev in the table caption.

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| blocker | `s3:defCOL` | COL-M-INTEGER | (Inherited from s2a HB-M-INTEGER; decision needed before EG/Defs/Lend/COL.lean.) K^JS_l := M_l^2 is used as the NUMBER of JS classes (0 <= j < K^JS_l) and the label law needs K^JS_l·rho_l = M_l^-2 exactly; with (R2) M_l = max(2^40, 2^16 T log^4 T) a real number this is ill-typed. Proposed decision (as s2a): M_l := ceil(max(2^40, 2^16 T log^4 T)) ∈ ℕ. Impact here: none on the table rows except (B6) Λ_r <= λ+6μ+20 (see COLJV-B6-CEILING). Alternative (K^JS_l := ceil(M_l^2)) changes (i)'s \|I_JS\| <= (4/3)M^2 to <= (4/3)M^2 + (R - r - 1) and s6:lemLost's K^JS rho = M^-2 to <= M^-2 + M^-4. |
| risk | `s3:lemL9rho` | L9-HAXELL-UNIVERSE | The s1 blueprint's HaxellStatement quantifies over α : Type (universe 0), but the hypergraph here lives on ι ⊕ Sym2 V with V : Type u (all s3 Specs are universe-polymorphic in V). Either lock HaxellStatement universe-polymorphically (α : Type u, HaxellStatement.{u}; recommended, it is a stage-alpha hypothesis on proof terms only) or transport the finite hypergraph to Fin N (Fintype.equivFin of the support subtype, ~100 lines). Must be decided before HaxellStatement is locked; otherwise L9rho (and T16*, and everything using it) can only be proved for V : Type. |
| risk | `s3:lemL9rho` | L9-HAXELL-FORM | (Inherited s1 HAX-TRUTH.) Stage-alpha trusted hypothesis whose factor 2q-1 has not been checked against [Hax95]. This proof verifies the STRONGER premise \|Z\| < h^2 \|I\| for nonempty I (the manuscript notes the slack), so lock the q^2-form (nonempty X', \|Z\| < q^2 \|X'\|), which is implied by every quoted form; then L9rho does not depend on the unchecked factor. If the (2q-1)(\|X'\|-1) form is locked instead, avoid ℕ-subtraction at X' = ∅ (HAX-NATSUB) and add the 5-line implication (2h-1)(\|I\|-1) <= h^2(\|I\|-1) < h^2\|I\|. |
| risk | `s3:lemL9rho` | L9-UNREVIEWED | Claim and final step are v6 (R3) text with one AI review only (G0). Re-derived in full here: \|I\| <= 2t\|I'\| (multiplicities) and \|I'\| <= n/2; t_0 := ceil(\|I'\|/(2M_*)) satisfies 1 <= t_0, 2t_0-1 <= \|I'\| (M_* >= 3 because 2.1/rho >= 2.1), 4t_0-2 <= n/M_*+2 <= \|W\|, t_0 <= n; \|F\| < h^2\|I\| <= 16(ell_*L)^2·2t\|I'\| <= 64 M_* t t_0 (ell_*L)^2 <= sbar_* t_0 (M_* <= 3.1/rho, (ell_*L)^2 <= 2^20 L^8, 64·3.1 = 198.4 <= 2^8); Prop 8 on G-F with ell_* <= 2^10 L^3 <= n (n >= 2^30); (2h-1)(\|I\|-1) <= h^2(\|I\|-1) < h^2\|I\|; matching gives e_i with e_i ∩ A = {i}, hence distinct and disjoint. No error found; still the least-reviewed part of T16*. |
| risk | `s3:thmT16s` | T16-STEP1-PRODUCT | 'Colour E(X) with K_* colours, uniformly and independently of V' and 'condition on a colouring ...; V is still rho-random' hide the whole product/conditioning construction: Omega' := (randColouring ↥X.edges K_*).prod mu; L15p on the first factor (EG.l15p_prod_fst exists); for each colouring c with all classes expanders, the conditional law of R is rsubset (map_snd_cond_prod_fst); P18s(ii) for each of the K_* classes (the class graphs are colourClass X c i with the same verts, so the (eqStar) parameters coincide); union bound; P(bad) <= P(c bad) + max_{c good} P(bad \| c) (prob_compProd_le_of_forall-style slicing); transfer of the R-only event back to mu (prob_prod_snd). K_* needs a NeZero instance (ceil of a positive real). All ingredients exist; ~200 lines of plumbing. |
| risk | `s3:lemHB` | HB-UNREVIEWED | v6 (R4) proof with one AI review. Re-derived in full: (1) SDR ⇒ sets: at most d(w)-m arrows of w use spare slots of w, so >= m use load slots of their head, and injectivity bounds #{w : u ∈ A(w)} by b; (2) the union in Hall's condition is b\|R\| + Σ_{w∈S}(d(w)-m) (slots of distinct vertices are distinct); (3) S', \|N(w) \ R\| <= m-1 on S'; U := S' or a ceil(\|S'\|/2)-subset (<= ceil(N/2) <= 2N/3 for N >= 2); F := {wu : w ∈ U, u ∉ R}, \|F\| <= (m-1)\|U\| <= s\|U\|; an edge vw ∉ F with w ∈ U and v ∉ U forces v ∈ R; so N_{X-F}(U) ⊆ R and b\|R\| >= b ε'\|U\|/L^2 >= m\|S'\| >= LHS. Correct. The 'd(w)-m > m' remark is 'not needed' in the working copy; only d(w) >= m is needed (spare-slot count as ℕ subtraction). |
| risk | `s3:defCOL` | COL-EMPTY-INDEX | The 'formal' sentence 'every edge e of H_Y carries three independent uniform random variables (a fair bit, a lent index and an own label)' is ill-defined when k_lend(Y) = 0 (r >= R-1: uniform on the empty set; FinDist.uniform needs Nonempty) and for standalone Y (J_Y and k_own are defined only for light Y). Lean decision: lent index ∈ Option LentTag with idxLaw = dirac none when lentIdx Y = ∅; own label ∈ Fin (kown Y) with kown := 4⌊log2(L_Y/8)⌋₊ + 1 >= 1 defined for EVERY ancestor (an unused, independent label for standalone Y). Neither changes any law that the manuscript uses. Suggested wording: 'a lent index (if r <= R-2) and an own label (if Y is light)'. |
| risk | `s3:defCOL` | COL-RANDOM-EDGESET | (= s3a L15-RANDOM-EDGESET, resolved by this data model.) Lend_Y and Own_Y are random; L15p colours a FIXED edge Finset. With per-edge labels on the fixed E(H_Y), the needed API lemma is: conditional on the bit vector β (positive probability), the law of (fun e : ↥(Lend β).edges => idx e) is randColouring ↥(Lend β).edges k_lend transported along ↥(lentIdx Y) ≃ Fin k_lend (and the own labels on Own β likewise with Fin kown), and the classes are the colourClass of Lend β. Ingredients exist (map_selectSet_randColouring, l15p_of_map_eq, cond lemmas) but restriction of a pi to a random sub-index-set given the bits is new (~150 lines). |
| risk | `s3:defCOL` | COL-CONSUMERS-NOT-A-PROPERTY | The paragraph 'Consumers (property COL(g))' is a DESIGN RULE for the constructions of s4-s6 (which device may read which class), plus forward claims about s6:consOrder objects (Lent(Y) = ∅ for r >= R-1, Erem(Y) = E_r(Y), H_0(Y) = E_r(Y)). It is not a property of the random data and cannot be a lemma of s3. Its s3 content is only the partition facts (s3:lemCOL(g)). Exclusivity must be built into the Lean constructions of s5:lemParent, s6:lemJSLC, s6:defJconsumer, s6:consOrder (each consumer's input restricted to its class) and proved there; downstream independence arguments (s5:lemE1, s6:lemLost, s7:lemCand, s7:lemLift) silently rely on it. Undeclared forward dependency on s6:consOrder. |
| risk | `s3:tabCOLJV` | TAB-NO-OWNER | The table label is in no chunk list, yet s1:condG1(f), s3:lemCOLJV, s3:lemCOLJVev and s7:lemGammaSat all refer to it. It must be ONE Defs constant (proposed here, EG.COLTable.col3), locked together with Gamma1; otherwise G1(f) and COLJVev(iii) could refer to different formulas and s7:lemGammaSat would prove the wrong eventuality. msreport should list s3:tabCOLJV as a node (ms_deps already has it as a declared dep of COLJVev). |
| risk | `s3:tabCOLJV` | TAB-COL2-INFORMAL | Column 2 is informal ('T16* failures over I_JS(Y) sum to at most \|V(Y)\|^-2/4', 'own devices', 'Lemma 15+, lent level' — the two other levels of row 3 appear only in the proof). s3:lemCOLJV(ii) must assert the precise inequalities C1-C13 listed in the statement; in particular row 3 must include ALL three levels (s_Y >= 80 L_Y; s_r/8 >= 40 k_own L_Y for light Y; s_Y/4 >= 40 k_lend L_Y), else s3:lemCOL(a) and s5:lemE1(b) lack hypotheses. Rows 1 and 12 duplicate s2:lemTower(c),(b): keep one source. |
| risk | `s3:lemCOLJV` | COLJV-N0-IMPLICIT | The proof uses s2:propStructure ((B4) via (iv); H_Y's parameters) and s2:lemTower, whose proof uses propStructure; propStructure is stated only 'for every valid run on G with n >= N_0 and d_1 >= D_*'. lemCOLJV (and lemCOL) assume only G1. The written proof of propStructure does not appear to use n >= N_0, so either the s2 Spec of propStructure (and lemTower) drops n >= N_0 (preferred; verify lemCap/lem14tau), or every COL Spec adds N_0 <= \|V(G)\| (all consumers have it, e.g. s6:consOrder). d_1 >= D_* is automatic once an ancestor exists (R >= 1). Decide in P2-D with a bundled run context. |
| risk | `s3:lemCOLJV` | COLJV-COL2-PRECISION | (= TAB-COL2-INFORMAL.) The Lean (ii) must state the column-2 requirements in exactly the form lemCOL and s5/s7 apply them (C1-C13). Rows 4-7 carry the T16*/L15p hypotheses and failure sums: e.g. row 5 dominates T16*'s hypothesis for every l ∈ [r+2, R] only via t^JS_l <= 3M and ρ_l^-5 = M_l^20 <= M^20, which lemCOL(b) must then re-derive — better to state row 5 per l in the Spec. |
| risk | `s3:lemCOLJV` | COLJV-UNREVIEWED | (ii) restated in v6 (R6 + integration), one AI review. Every row re-derived here: row 1 (τ_r <= 128 s_r Λ^2 + 1 <= 257Λ^102, θ^GC >= λ^102.5, (B6)); row 3 (λ^100/8 >= 80λk̄ ⇔ λ^99 >= 640k̄; other levels λ^100/2 >= 160λ, λ^100/8 >= 160λ^2); row 4 (2^135·2λ^1.6·(2λ)^28·12^5(2λ)^25 = 2^189·12^5 λ^54.6, s >= λ^100/(16k̄) ⇒ need λ^45.4 >= 2^193 12^5 k̄ ⇐ row 4 col 3 + row 9); row 5 (λ^100 >= 3·2^167 k̄ M̄^21 λ^28); row 6 (2^107 λ^19 M^15 N^-3 <= N^-2/4 ⇐ λ^84 >= 2^110 M̄^15 with N >= λ^103/2); row 7 (12^4 2^124 λ^38.6 N^-3); row 8 (a)-(d) incl. s' >= λ^99/32; rows 9-13; (i) (4(L^2+1)L <= 12L^3, geometric sum (4/3)M^2, 2log* d_r + 2 <= μ <= 12L^3, 24(2λ)^3 = 192λ^3). No error found. |
| risk | `s3:lemCOL` | COL-CONDITIONAL-L15 | (a)'s second and third L15p applications are CONDITIONAL on the Own/Lend split: 'Condition on stage (i) with Lend_Y such an expander. Stage (ii) is then a uniform k-colouring of Lend_Y'. In Lean: for each bit vector β with Lend(β) (resp. Own(β)) an expander, the restricted index (own) labels have law randColouring ↥(Lend β).edges k (Fin kown) up to ↥lentIdx ≃ Fin k (COL-RANDOM-EDGESET), L15p slice-wise, and P(¬a) <= P(split bad) + Σ_β P(bits = β)·P(classes bad \| β) <= 4N^-5 + 2kN^-5 + 2k_own N^-5. ~250 lines; mathematically fine. |
| risk | `s3:lemCOL` | COL-CONDITIONAL-T16 | (b), (c) apply T16* to a class that is an expander only on (a), conditionally on the colouring: needs 'T_j(Y,l) (labels) resp. Vs_i independent of the colouring ⇒ still ρ-random under the conditional law given the colouring' (IsRSubset.cond_of_indepFun exists) and P(a ∧ ¬b) <= max over colourings c ∈ (a) of P(¬b \| c). For (c) the hypothesis must be JOINT independence IndepFun μ D Vs (conditioning on the colouring, a function of D, needs the whole family independent of D — per-index independence is not enough); the consumer s5:lemE1(c) must prove this joint form for the zones (functions of the choices/sublabels, an independent stage-1 factor: s5:lemZones(iv)). |
| risk | `s3:lemCOL` | COL-N0-IMPLICIT | (= COLJV-N0-IMPLICIT.) s2:propStructure(i) (H_Y an (ε_Y, s_Y)-expander with H_Y.verts = V(Y)) and (iv) are stated under n >= N_0 and d_1 >= D_*; lemCOL assumes only G1. Decide globally (drop N_0 from propStructure, or add it to every COL Spec). |
| note | `s3:lemL9rho` | L9-PATH-FINSET | Y_i must be a Finset (hyperedges are Finsets). There is no Mathlib 'all paths of length <= h' Finset for list paths; build it as a filter of the finite set of lists over G.verts of length <= h+1 (e.g. Finset.biUnion over lengths of List.Vector/Fintype.piFinset images). The bound \|hyperedge ∩ B\| = \|E(P)\| <= h needs walkEdges nodup for paths (Lib) and pathLength = number of edges. ~80 lines. |
| note | `s3:lemL9rho` | L9-MATCHING-EXTRACTION | From the matching M: for each i pick e_i ∈ M with inl i ∈ e_i; e_i = hyperedge(k, Q) for some k, Q (membership in the image), and inl i ∈ e_i forces k = i; choose Q_i by Classical.choose. Distinct indices give distinct e_i (their A-parts differ), hence disjoint, hence edge-disjoint Q_i. Repeated pairs get distinct paths automatically (indexing by i). |
| note | `s3:lemL9rho` | L9-PROP8-INTERFACE | BMProp8Statement (s1 blueprint) takes x y : Fin (2t-1) → V with Sum.elim x y injective, the ball hypothesis for all U ⊆ V(G) with \|U\| = t, and gives a path of real length <= 4 ell log2 n. The proof must: enumerate 2t_0-1 indices of I' (Finset.exists_subset_card_eq + equivFin), derive the Prop 8 hypothesis on G-F from the L9rho hypothesis (\|F\| < sbar t_0 = sbar \|U\|, F ⊆ E(G)), and convert the real length bound to <= h by Nat.le_floor. G-F has the same vertex set, so log n is unchanged. |
| note | `s3:lemL9rho` | L9-NUMERICS | Needs 2^10 (log2 n)^3 <= n for n >= 2^30 (so ell_* <= n, a Prop 8 hypothesis) — a small real-analysis lemma (~40 lines); n/M_* <= rho n/2.1 and rho n/2 - rho n/2.1 = rho n/42 >= 2 (write 2.1 = 21/10); M_* <= 2.1/rho + 1 <= 3.1/rho. All exact rationals. |
| note | `s3:lemL9rho` | L9-HYP-INCLUSIONS | Keep U ⊆ V(G), F ⊆ E(G) and W ⊆ V(G) in the Spec (CONVENTIONS: the one-vertex path puts U ∩ W into the ball even outside V(H)). The hypothesis form matches what T16* Step 4 provides (P18s(ii) quantifies nonempty U ⊆ V, F ⊆ E). |
| note | `s3:lemL9rho` | L9-DEPS | Attribution-only \deps edge s1:citLem9 (no Lean node); undeclared s3:eqStar; Aharoni-Haxell not used. msreport should mark these. |
| note | `s3:thmT16s` | T16-AE-SUBSET | IsRSubset gives R ω ⊆ V(X) only for ω in the support (IsRSubset.subset_ae); L9rho needs W ⊆ V(G). The good event must be intersected with the support (or the probability computed as a sum over the support). |
| note | `s3:thmT16s` | T16-S5-FORM | Use (S5) in the exact rational form of the s3a StarFactsStatement (K_* <= (6·2^81+1) t L^19/rho^3; 2K_*(theta_*+1) <= 2(6·2^81+1)(2^46+1) t L^28/rho^5) and compare with 2^135 and 2^86 by norm_num: 2(6·2^81+1)(2^46+1) <= 2^135 and 3(6·2^81+1)+1 <= 2^86 (margins ~2^4.4 and ~2^0.8). Never state the rpow constants 2^83.6, 2^130.6. |
| note | `s3:thmT16s` | T16-STEP0-NO-RPOW | Step 0 derives N >= 2^30, rho N >= 84 and e^(-rho N/8) <= N^-3 via (b) with rpow L^5.6 N^(4/5). All three follow without rpow from rho^5 N > rho^5 s >= 2^135 t L^28 (N > s since delta(X) > s): rho N >= rho^5 N > 2^135 L^28 >= 2^135, and rho N/8 >= 3 ln N = 3 L ln 2 as 2^135 L^28 >= 24 L for L >= 1. Recommend omitting (b) from the Spec (no consumer); if kept, a separate rpow lemma. |
| note | `s3:thmT16s` | T16-C-META | Item (c) says 'The proof uses only s >= 2K_*(theta_*+1)'. As written this is inaccurate: the Step 0 paragraph uses the full hypothesis s >= 2^135 t L^28 rho^-5 (to get N > 2^135, rho N >= 84, N >= 2^30 and e^(-rho N/8) <= N^-3). A variant assuming only s >= 2K_*(theta_*+1) is plausible (2K_*(theta_*+1) >= ~2^120 t L^28 rho^-5 would still force these) but is not written. No consumer uses (c); do not formalize it. Suggested manuscript wording: 'Apart from Step 0, the proof uses only ...'. |
| note | `s3:thmT16s` | T16-RHO-POS | IsRSubset allows rho = 0; the Spec adds 0 < rho (CONVENTIONS). The hypothesis rho N >= L^2 is unused in the proof (implied by the others for N >= 2) but kept for faithfulness; t is real (s4 passes t = 2^10 L^8). |
| note | `s3:thmT16s` | T16-DEGENERATE-N | For N ∈ {0, 1}: Lean's logb 2 N = 0, so the bound reads 1 - 0 <= prob; the event holds at every ω because no pair of distinct vertices exists (every admissible family has an empty index type). Needs a small Lib lemma (IsPathConnected of a graph with < 2 vertices). |
| note | `s3:thmT16s` | T16-STEP4-PIGEONHOLE | Some class i has \|F ∩ E(X_i)\| <= \|F\|/K_*: Σ_i \|F ∩ E(X_i)\| = \|F\| because the colour classes partition E(X) (disjoint_colourClass_edges + cover), then an averaging lemma. F ∩ E(X_i) ⊆ E(X_i) as P18s(ii) requires; X_i - (F ∩ E(X_i)) has edge set ⊆ E(X) \ F, so EG.ball_mono_edges gives the inclusion of balls. K_* >= sbar_*/mu_* from (S5). |
| note | `s3:thmT16s` | T16-STAGE-ALPHA | Through L9rho the proof depends on the stage-alpha Haxell hypothesis (and on BMProp8 until it is proved); the Spec is hypothesis-free, the proof term EG.t16s takes them as arguments; every consumer proof (lemCOL, s4) inherits them until stage beta. |
| note | `s3:thmT16s` | T16-DEPS | Declared s3:propP13s and s3:lemL17s are indirect (via s3:lemP18s); s1:citThm16 undeclared attribution; s3:eqStar undeclared. Universe: Ω : Type u (as in the s3a Specs); lemCOL's stage-1 space and s4's spaces are built from V and live in Type u. |
| note | `s3:lemHB` | HB-PLAN-MISMATCH | PLAN §2 R4 describes 'm rounds of Mathlib's Hall theorem on V × [ceil(2L^2/eps')]' with b' <= b + m. The v6 manuscript instead makes ONE Hall application with load and spare slots and gets exactly b. Formalize the manuscript version: s5:defStages needs b = ceil(2^7 L_Y^2 m) = b_Y exactly and s4 needs b <= b_vortex = ceil(2^8 L^2 m); a b+m variant would change these constants. |
| note | `s3:lemHB` | HB-HALL-ENCODING | Mathlib Hall is stated for t : ι → Finset α with ι a Fintype (use the subtype of the arrow Finset) and gives f injective with f a ∈ t a. Slot encoding α := V × ℕ × Bool; computing \|⋃_{a∈E} T(a)\| = b\|R\| + Σ_{w∈S}(d(w)-m) needs a disjoint-union bookkeeping lemma (~80 lines). |
| note | `s3:lemHB` | HB-EPS-UNUSED | The proof uses only 0 < eps' (min degree, expansion); eps' <= 1 and eps' >= 2^-7 are unused (2^-7 enters b's value at call sites). Keep both for faithfulness. |
| note | `s3:lemHB` | HB-FIXED-RULE | Consumers need A as a function of X ('the lexicographically first such family'): EG.hbSets via Classical.choose (PLAN decision 7); only its properties are used downstream. |
| note | `s3:lemHB` | HB-NBRS-VERTS | EG.FGraph.nbrs filters X.verts, so A(w) ⊆ V(X) automatically; the multiplicity count is over w ∈ V(X) (A w for w ∉ V(X) is junk and excluded). |
| note | `s3:defCOL` | COL-TY-CLAIM | 't_Y >= M_l for every r+2 <= l <= R' is a lemma needing G1 through s2:lemTower(a),(b) (M_l <= λ_{l-2}^1.6 <= λ_r^1.6), not part of the definition; put it in the COL API (used by s5:lemParent 'Comparison with t_Y'). t_Y := ⌈λ_r^(8/5)⌉₊ (rpow; λ_r > 0 under G1). |
| note | `s3:defCOL` | COL-LABEL-LAW | The JS-label law is a non-uniform law built with ofFinset/ofFintype; statement reviewers must check its weights (CONVENTIONS). Nonnegativity of 1 - M_l^-2 needs M_l >= 1. API: T_j(Y,l) is rho_l-random (isRSubset_selectSet on the indicators {lab(l,y) = some j}_y, independent across y by the pi structure), T_j ∩ T_j' = ∅ for j ≠ j', and the labels are independent of the colouring (prod structure: indepFun_fst_snd). |
| note | `s3:defCOL` | COL-ANCESTOR-INDEX | Ancestors must be indexed by (round, pre-part address) (s2a HB-ADDRESS-IDENTITY). The global space is a FinDist.pi over the Finset of ancestors; edge-disjointness of the H_Y (propStructure(iii)) is not needed for the definition, only for consumers that look at a fixed edge e of G across ancestors. |
| note | `s3:defCOL` | COL-NAMED-OWN-CLASSES | Own labels Fin (4J_Y + 1) must be matched with the names R_{j,c} (0 <= j < J_Y, c ∈ [4]) and M used in s4:lemPV / s5:lemChild; fix the bijection (R_{j,c} ↔ 4j + c, M ↔ 4J_Y) in the Defs, and make s4:lemPV's J := ⌊log2(L/8)⌋ the same term as J_Y (CONVENTIONS: named colour families need an explicit bijection). |
| note | `s3:defCOL` | COL-ZERO-BASED | c ∈ [4] → Fin 4, sigma ∈ [T^sl_Y] → 0-based σ < Tslot, j already 0-based; rounds stay 1-based ℕ with r + 2 <= l <= R (never ℕ-subtract). |
| note | `s3:defCOL` | COL-PY-DOMAIN | p_Y := 1/(2 k_lend) is junk (0 in Lean) for k_lend = 0; every statement about p_Y assumes r <= R-2. 'p_Y is the probability that a fixed edge lies in LJV_{Y,l}' is an API lemma (1/2 · 1/k_lend) used by s7:lemCand. |
| note | `s3:defCOL` | COL-STAGE-GROUPING | s7:defSchedule lists (1a) colourings and (1c) JS labels as separate independent stage-1 families; defCOL bundles both per ancestor. Equivalent (all independent), but P2-D must fix ONE product structure with named projections so that s5/s6/s7 Specs state independence uniformly (IndepFun of projections). |
| note | `s3:defCOL` | COL-EMBEDDED-FACTS | 'The graphs H_Y are pairwise edge-disjoint' (propStructure(iii)) and 'the label distribution is well defined because K^JS_l rho_l = M_l^-2 <= 1' are lemmas, not definitions; the five 'Consequently' bullets are API lemmas of colLaw. |
| note | `s3:tabCOLJV` | TAB-DECIMALS | Exponents 102.5, 42.1, 64.4, 3.3, 1.6, 1/2 and triples 0.5, 42.1, 64.4, 0.3, 1.6 must be exact rationals (205/2, 421/10, 322/5, 33/10, 8/5, 1/2, 3/10) and real powers Real.rpow of λ = 2^μ > 0. The s1 blueprint writes G1(c) as '2*105*logb 2 (105*μ) <= 1.6*μ' — use 8/5 there too (row 12 = G1(c) after taking log2). |
| note | `s3:tabCOLJV` | TAB-COUNT | 18 column-3 inequalities: two in row 1 (strict main form + crude form), five in row 8, one elsewhere — as G1(f) says. Row 13 is G* (G1(e)) and row 12 is G1(c) (after log2). |
| note | `s3:tabCOLJV` | TAB-COL4-NOT-ASSERTED | Column-4 triples define cruder inequalities that are NOT part of G1 and need not hold at a given μ >= log log D_*; only s3:lemCOLJVev may use them. |
| note | `s3:lemCOLJV` | COLJV-B6-CEILING | (B6) Λ_r <= λ + 6μ + 20 is derived for the real M_r of (R2) (log T = λ + 2μ <= 2λ, log log T <= μ + 1). If M_l becomes an integer ceiling (COL-M-INTEGER), log2⌈x⌉ <= log2 x + 2^-39 for x >= 2^40, absorbed by the slack in 4 log2(λ + 2μ) <= 4(μ + 1) (since λ + 2μ <= 1.01λ); the Lean proof must include this. |
| note | `s3:lemCOLJV` | COLJV-GAMMA-TRANSFER | Needs the s1 transfer lemma 'Gamma1 D → D <= d → items hold at μ = log2 log2 d' (s1 GAM-RAY) with λ_r = log2 d_r > 0 and μ_r = log2 λ_r >= log2 log2 D_* (monotonicity of logb for d_r >= D_* > 2); also at λ_{l-2} (l - 2 >= 1 is a round). |
| note | `s3:lemCOLJV` | COLJV-RPOW | λ^3.3, λ^1.6, λ^-4, λ^102.5, λ^42.1, λ^64.4 are Real.rpow; identities λ^a = 2^(aμ) via Real.rpow_logb / rpow_mul (λ > 0). A small shared 'λ-power' Lib (also for COLJVev) avoids repeated rewriting. |
| note | `s3:lemCOLJV` | COLJV-ROW-SCOPE | Rows 1, 3, 8 hold for r ∈ {R-1, R} too. Row 8's inequalities are proved for all ancestors (they use only s_r and L_Y <= 2λ); (a),(b) are consumed only for standalone Y, (c),(d) only for light Y; k_own must be defined for every Y (COL-EMPTY-INDEX). |
| note | `s3:lemCOLJV` | COLJV-JV-COUNT | RT2-I10: \|I_JV\| = R - r - 1 <= 2log* d_r + 1 (not an absolute constant); the display's '+2' is a harmless weakening. log* must be the Found.Log definition used by s2:lemTower(a),(d). |
| note | `s3:lemCOLJV` | COLJV-B2 | (B2) needs M_{l+1} <= M_l/2 (lemTower(b): M_{l-1} >= 2M_l) and M = M_{r+2} <= M̄(μ_r) (lemTower(b) at l = r + 2 >= 3, r >= 1). \|I_JS\| = Σ_{l=r+2}^R M_l^2 <= M^2 Σ 4^-i = (4/3)M^2: a geometric-sum Lib lemma over Finset.Icc. |
| note | `s3:lemCOLJV` | COLJV-DEPS | Declared s3:lemL15p, s3:thmT16s are not logical dependencies (formulation only); s3:lemCOLJVev is a forward ref in the caption; s2:defHBtp and s3:tabCOLJV are undeclared. |
| note | `s3:lemCOLJVev` | EV-GAMMASAT-SHAPE | s7:lemGammaSat needs: for all sufficiently large D_*, (f) holds on the WHOLE ray μ >= log2 log2 D_*. This follows from (iii) as ∃ μ_0 ∀ μ >= μ_0 (Filter.eventually_atTop) plus log2 log2 D → ∞. State (iii) with ∀ᶠ in atTop (or ∃ μ₀); the conjunction over the 13 rows is Filter.eventually_all over Fin 13. |
| note | `s3:lemCOLJVev` | EV-ROW1 | Row 1 is strict: the proof gives φ >= (0.5μ - 112) + 1 > 0. It needs 6μ + 20 <= 2^μ for REAL μ >= 6 (manuscript: derivative argument). Lean route: 2^μ >= 2^⌊μ⌋ and 2^k >= 6k + 26 for integers k >= 6 (tight at k = 6: 64 >= 62), or convexity of rpow. Crude form μ > 222 from 0.5μ >= 112. |
| note | `s3:lemCOLJVev` | EV-LOG-CONSTANTS | log2 257 < 9, log2 640 < 10, 5 log2 12 < 18, 4 log2 12 < 15, log2 3 < 2: rewrite as 257 < 2^9 etc. via Real.logb_lt_iff_lt_rpow and norm_num. k̄ <= 2^9 λ^3 M̄^2 uses x + y <= 2xy for x, y >= 1 (λ >= 1, Aμ >= 1). |
| note | `s3:lemCOLJVev` | EV-I-PROOF | (i) uses log2 v < v for v >= 1 (from 2^v >= 1 + v; Mathlib: Real.add_one_le_exp or Bernoulli for rpow) and the quadratic in v = sqrt μ with Real.sqrt; v_0 is well defined since c^2 + a(b + c log2 105) >= 0. ~80 lines. |
| note | `s3:lemCOLJVev` | EV-TRIPLES-EXACT | Triples copied exactly (s3:tabCOLJV); each row's φ lower bound re-derived: 1: 0.5μ - 111; 2: 103μ - 26A log; 3: 96μ - 19 - 4A log; 4: 42.1μ - 211; 5: 69μ - 178 - 46A log; 6: 84μ - 110 - 30A log; 7: 64.4μ - 142; 8: E := 58μ - 194 - log(Aμ) with the five differences (E, E + 4μ + 7, E + 4μ + 3, >= E, 93μ - 13 > 0); 9: 0.3μ - 9 - 4A log; 10: μ - 10 - 4A log; 11: 95μ - 13 - 24A log; 12: 1.6μ - 2A log; 13: 36μ - 240 - 46A log. All correct. |
| note | `s3:lemCOLJVev` | EV-NOT-G1 | Type-(E) inequalities are not part of G1 and may fail at some μ >= loglog D_* although G1 holds; no Spec may use them as hypotheses (only COLJVev and s7:lemGammaSat). |
| note | `s3:lemCOL` | COL-EXPORT-A-BOUND | s5:lemE1(b) re-derives P(COL(a) fails) <= 2(2 + k_lend + k_own)\|Y\|^-5 by re-entering the PROOF of lemCOL ('COL(a) is the conclusion of three applications of Lemma 15+ in the proof of Lemma COL'). The COL Spec should export this bound (as in lean_shape), so s5 does not duplicate the conditional-L15 plumbing. s6:defLending likewise needs COL(a), COL(b) as named predicates (COLa, COLb). |
| note | `s3:lemCOL` | COL-EVENT-NAMES | s5:defStages lists COL(a) for light Y as: Own_Y, Lend_Y (2^-6, s_r/8)-expanders, lent classes (2^-6, s_r/(16k)), own classes (2^-6, s_r/(16k_own)). COLa is defined with ε_Y, s_Y and must unfold to exactly this for light Y (ε_Y = 2^-6, s_Y = s_r/2 real) and to (2^-5, s_r/4), (2^-5, s_r/(8k)) for standalone Y (s6:thmMIXC uses Own_Z (2^-5, s_l/4)). 'On V(Y)' = spanning: colourClass keeps H_Y.verts = V(Y). |
| note | `s3:lemCOL` | COL-E-DETERMINISTIC | (e) is deterministic (row 8) plus restatements valid 'on (a)'; COLe should contain only the inequalities (s6.tex:803 uses that they do not depend on the colouring). Row 8(b) (VX+ for standalone parts) is marked 'not used' in the working copy; keeping it is harmless. |
| note | `s3:lemCOL` | COL-G-MEANING | (g) in Lean = partition facts: Own_Y, Lend_Y partition E(H_Y); own classes pairwise edge-disjoint with union Own_Y; for r <= R-2 lent classes (i ∈ lentIdx Y) pairwise edge-disjoint with union Lend_Y (every lend edge has idx = some i with i ∈ lentIdx: true on the support of idxLaw only — state COLg on the support or build idx with values in the subtype); for r >= R-1 idx = none. The consumer-exclusivity part is not a property of the data (COL-CONSUMERS-NOT-A-PROPERTY). |
| note | `s3:lemCOL` | COL-B-CHECK | (b)'s T16* hypotheses re-checked: ε_Y ∈ [2^-7, 1]; s = s_Y/(8k) >= 2^135 t^JS_l L^28 ρ_l^-5 by row 5 (t^JS_l <= 3M, ρ_l^-5 = M_l^20 <= M^20); ρ_l N >= L^2 by row 2 at λ_r (M̄^13 <= λ^103 ⇒ M̄^4 <= λ^31.7) and N >= λ^103/2: ρ_l N >= λ^71/2 >= 4λ^2 >= L^2; failure sum over (l, j) ∈ I_JS(Y) <= N^-2/4 by row 6. |
| note | `s3:lemCOL` | COL-C-CHECK | (c)'s T16* hypotheses re-checked: class is (2^-6, s_r/(16k)) on (a); s_r/(16k) >= 2^135 t_Y L^28 (12L^5)^5 by row 4 with row 9; ρN >= N/(12L^5) >= λ^103/(24(2λ)^5) >= L^2; failure per index <= 2^86 t_Y L^19 (12L^5)^3 N^-3, union over I_U by row 7. The ρ_{l,c,σ} must be deterministic (IsRSubset with fixed ρ); ρ <= 1 is part of IsRSubset; t_Y >= 1. |
| note | `s3:lemCOL` | COL-PROB-ACCOUNTING | P(¬a) <= 2(2 + k + k_own)N^-5 <= 2(2 + λ^3.3 + 2λ)N^-5 <= N^-2/4 (k <= λ^3.3 row 9, k_own <= L <= 2λ, N^3 >= λ^309/8); P(a ∧ ¬b) <= N^-2/4; P(a ∧ ¬c) <= N^-2/4; so P(a∧b∧e) >= 1 - N^-2/2, P(c) >= 1 - N^-2/2, P(a∧b∧c∧e) >= 1 - 3N^-2/4 >= 1 - N^-2. For standalone Y there is no stage-(iii) application (over-count harmless). |
| note | `s3:lemCOL` | COL-JOINT-ROUTING | (b)'s joint routing of several systems at junction j needs the multiplicity of the SUM multiset <= t^JS_l (s3a MON-JOINT-MULT); that is s6:lemJSLC's obligation, not lemCOL's. |

## 4. Nodes

### `s3:lemL9rho` — lemma: Lemma 9_rho: multiset linking from ball expansion (s3.tex:692)

- **Manuscript referee status:** x2+RT for the statement; claim and final step re-proved via Haxell's theorem in v6 (R3): one clean-room AI review (G0, 2026-09-26)
- **Formalization:** Spec EG/Spec/Link/L9rho.lean (L9rhoStatement) + proof EG/Proof/Link/L9rho.lean. The proof is stage alpha: it takes EG.Spec.HaxellStatement (and EG.Spec.BMProp8Statement until B-M Prop 8 is proved) as explicit hypotheses of the proof term; the Spec itself is hypothesis-free.

**Statement (precise restatement).** Let V be a vertex type, G a finite simple graph with n := |V(G)| >= 2^30, L := log2 n. Let t >= 1 and 0 < rho <= 1 be reals. Let ell_* := floor(2^10 L^3) (a natural number), sbar_* := 2^28 t L^8 / rho (real) and M_* := ceil(2.1/rho) (a natural number) be the parameters of (eqStar). Let W be a subset of V(G) with |W| >= rho n/2 and rho n >= 84. Then: (A) |W| >= n/M_* + 2 (real inequality). (B) IF for every nonempty U subset of V(G) and every F subset of E(G) with |F| <= sbar_* |U| we have |B^{ell_*}_{G-F}(U,W)| > |W|/2 (ball of radius ell_* in the graph G-F, i.e. V(G) with edges E(G) minus F, consisting of the vertices of W reachable from U by a path of length <= ell_* whose interior lies in W), THEN G is (2^12 L^4, t)-path connected through W in the multiset sense of Def 7: for every finite index type iota and every family P : iota -> V x V of pairs of distinct vertices of G in which every vertex is an entry of at most t indices (counted with multiplicity), there are paths Q_i (i in iota), Q_i an (P i).1-(P i).2 path of G of length <= 2^12 L^4 with all interior vertices in W, pairwise edge-disjoint for distinct indices (endpoints unrestricted). Proof-internal objects: h := floor(4 ell_* L) >= 1; Y_i := the finite set of x_i y_i-paths of G of length <= h with interior in W; for nonempty I subset of the index set, I' a maximal subfamily of pairwise vertex-disjoint pairs, t_0 := ceil(|I'|/(2 M_*)); the claim 'for every nonempty I and every F subset of E(G) with |F| < h^2 |I| there are j in I and P in Y_j with E(P) disjoint from F'; the hypergraph H on iota disjoint-union E(G) with edges {i} cup E(P), P in Y_i, to which Haxell's theorem is applied with q := h.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| finite simple graph, G - F, \|G\| | EG.FGraph (verts, edges), deleteEdges F, card = \|verts\| | s1:convGraphs | yes: EG/Defs/Graph.lean |
| ball B^i_H(U,W) | vertices of W reachable from U by a path through W of length <= i (start need not be in W) | s1:convGraphs(d), s1:citNotation | yes: EG.ball (EG/Defs/Walk.lean); ball_mono_edges, ball_mono_left in EG/Lib/Found/Graph.lean |
| (ell,t)-path connected through W, multiset form | Def 7 with indexed families iota -> V x V, one path per index, pairwise edge-disjoint | s1:citDef7, s3:remMultiset | yes: EG.FGraph.IsPathConnected (EG/Defs/Expander.lean) |
| ell_*, sbar_*, M_* | ell n := floor(2^10 L^3); sbar n rho t := 2^28 t L^8/rho; M rho := ceil(21/10/rho) | s3:eqStar | no: EG.Star.ell / EG.Star.sbar / EG.Star.M proposed by the s3a blueprint (EG/Defs/Link/Star.lean) |
| h, Y_i (bounded paths through W) | h := floor(4 ell_* L); Y_i := Finset of lists p with IsPathBetween G.edges x_i y_i p, IsThrough W p, pathLength p <= h | proof of s3:lemL9rho | no: new Lib EG.pathFinset (a Finset of bounded-length paths; needs a finite enumeration of lists over G.verts) |
| maximal vertex-disjoint subfamily I', counting \|I\| <= 2t\|I'\|, \|I'\| <= n/2 | I' subset I, pairs of I' pairwise vertex-disjoint, every pair of I meets a vertex covered by I' | s3:remMultiset | no: Lib proposed by the s3a blueprint (EG/Lib/Link/Multiset.lean) |
| hypergraph, A-saturating matching (Haxell) | Finset (Finset alpha), A, B disjoint, \|e cap A\| = 1, \|e cap B\| <= q; matching = pairwise disjoint edges covering A | s1:citHaxell | no: inline in EG.Spec.HaxellStatement (s1 blueprint, stage-alpha hypothesis) |
| B-M Proposition 8 | one pair out of 2t-1 vertex-disjoint pairs is joined by a path through W of length <= 4 ell log n, if all t-sets have balls > \|W\|/2 | s1:citProp8 | no: EG.Spec.BMProp8Statement (s1 blueprint) |

**deps_declared** (manuscript \deps): s1:citLem9, s1:citProp8, s1:citHaxell, s1:citDef7, s3:remMultiset

**deps_from_proof:** s3:eqStar, s1:citProp8, s1:citHaxell, s1:citDef7, s3:remMultiset, s1:convGraphs

**deps_notes:** s1:citLem9 is attribution only (B-M Lemma 9 has no Lean node, s1 blueprint L9-NOLEAN). s3:eqStar (ell_*, sbar_*, M_*, (S1): ell_* <= 2^10 L^3) is used but undeclared (namedlabel). B-M Theorem 6 (Aharoni-Haxell) is not used. The claim is proved from Prop 8; the matching from Haxell; the counting step from remMultiset.

**used_by:** s3:thmT16s (Step 4, with G := X, W := V); s7.tex:1591 (remark on slack; no logical use)

**randomness:** none (deterministic lemma).

**lean_shape:**

```lean
-- EG/Spec/Link/L9rho.lean
def EG.Spec.L9rhoStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (W : Finset V) (ρ t : ℝ),
    2 ^ 30 ≤ G.card → 0 < ρ → ρ ≤ 1 → 1 ≤ t → W ⊆ G.verts →
    ρ * G.card / 2 ≤ W.card → 84 ≤ ρ * G.card →
    ((G.card : ℝ) / (EG.Star.M ρ : ℝ) + 2 ≤ W.card) ∧
    ((∀ U : Finset V, U ⊆ G.verts → U.Nonempty → ∀ F : Finset (Sym2 V), F ⊆ G.edges →
        (F.card : ℝ) ≤ EG.Star.sbar G.card ρ t * U.card →
        (W.card : ℝ) / 2 < ((EG.ball (G.deleteEdges F) (EG.Star.ell G.card) U W).card : ℝ)) →
      G.IsPathConnected (2 ^ 12 * Real.logb 2 G.card ^ 4) t W)
-- EG/Proof/Link/L9rho.lean (stage alpha)
theorem EG.l9rho (hHax : EG.Spec.HaxellStatement.{u}) (hP8 : EG.Spec.BMProp8Statement.{u}) :
    EG.Spec.L9rhoStatement.{u}
-- proof-internal Lib (proposed):
-- EG.pathFinset (E : Finset (Sym2 V)) (S : Finset V) (x y : V) (W : Finset V) (h : ℕ) : Finset (List V)
-- claim: ∀ I : Finset ι, I.Nonempty → ∀ Z ⊆ G.edges, Z.card < h ^ 2 * I.card →
--          ∃ j ∈ I, ∃ p ∈ Y j, Disjoint (walkEdges p).toFinset Z
-- hyperedge i p := insert (Sum.inl i) ((walkEdges p).toFinset.map ⟨Sum.inr, Sum.inr_injective⟩)
```

**hazards:**

- **[risk] L9-HAXELL-UNIVERSE.** The s1 blueprint's HaxellStatement quantifies over α : Type (universe 0), but the hypergraph here lives on ι ⊕ Sym2 V with V : Type u (all s3 Specs are universe-polymorphic in V). Either lock HaxellStatement universe-polymorphically (α : Type u, HaxellStatement.{u}; recommended, it is a stage-alpha hypothesis on proof terms only) or transport the finite hypergraph to Fin N (Fintype.equivFin of the support subtype, ~100 lines). Must be decided before HaxellStatement is locked; otherwise L9rho (and T16*, and everything using it) can only be proved for V : Type.
- **[risk] L9-HAXELL-FORM.** (Inherited s1 HAX-TRUTH.) Stage-alpha trusted hypothesis whose factor 2q-1 has not been checked against [Hax95]. This proof verifies the STRONGER premise |Z| < h^2 |I| for nonempty I (the manuscript notes the slack), so lock the q^2-form (nonempty X', |Z| < q^2 |X'|), which is implied by every quoted form; then L9rho does not depend on the unchecked factor. If the (2q-1)(|X'|-1) form is locked instead, avoid ℕ-subtraction at X' = ∅ (HAX-NATSUB) and add the 5-line implication (2h-1)(|I|-1) <= h^2(|I|-1) < h^2|I|.
- **[risk] L9-UNREVIEWED.** Claim and final step are v6 (R3) text with one AI review only (G0). Re-derived in full here: |I| <= 2t|I'| (multiplicities) and |I'| <= n/2; t_0 := ceil(|I'|/(2M_*)) satisfies 1 <= t_0, 2t_0-1 <= |I'| (M_* >= 3 because 2.1/rho >= 2.1), 4t_0-2 <= n/M_*+2 <= |W|, t_0 <= n; |F| < h^2|I| <= 16(ell_*L)^2·2t|I'| <= 64 M_* t t_0 (ell_*L)^2 <= sbar_* t_0 (M_* <= 3.1/rho, (ell_*L)^2 <= 2^20 L^8, 64·3.1 = 198.4 <= 2^8); Prop 8 on G-F with ell_* <= 2^10 L^3 <= n (n >= 2^30); (2h-1)(|I|-1) <= h^2(|I|-1) < h^2|I|; matching gives e_i with e_i ∩ A = {i}, hence distinct and disjoint. No error found; still the least-reviewed part of T16*.
- **[note] L9-PATH-FINSET.** Y_i must be a Finset (hyperedges are Finsets). There is no Mathlib 'all paths of length <= h' Finset for list paths; build it as a filter of the finite set of lists over G.verts of length <= h+1 (e.g. Finset.biUnion over lengths of List.Vector/Fintype.piFinset images). The bound |hyperedge ∩ B| = |E(P)| <= h needs walkEdges nodup for paths (Lib) and pathLength = number of edges. ~80 lines.
- **[note] L9-MATCHING-EXTRACTION.** From the matching M: for each i pick e_i ∈ M with inl i ∈ e_i; e_i = hyperedge(k, Q) for some k, Q (membership in the image), and inl i ∈ e_i forces k = i; choose Q_i by Classical.choose. Distinct indices give distinct e_i (their A-parts differ), hence disjoint, hence edge-disjoint Q_i. Repeated pairs get distinct paths automatically (indexing by i).
- **[note] L9-PROP8-INTERFACE.** BMProp8Statement (s1 blueprint) takes x y : Fin (2t-1) → V with Sum.elim x y injective, the ball hypothesis for all U ⊆ V(G) with |U| = t, and gives a path of real length <= 4 ell log2 n. The proof must: enumerate 2t_0-1 indices of I' (Finset.exists_subset_card_eq + equivFin), derive the Prop 8 hypothesis on G-F from the L9rho hypothesis (|F| < sbar t_0 = sbar |U|, F ⊆ E(G)), and convert the real length bound to <= h by Nat.le_floor. G-F has the same vertex set, so log n is unchanged.
- **[note] L9-NUMERICS.** Needs 2^10 (log2 n)^3 <= n for n >= 2^30 (so ell_* <= n, a Prop 8 hypothesis) — a small real-analysis lemma (~40 lines); n/M_* <= rho n/2.1 and rho n/2 - rho n/2.1 = rho n/42 >= 2 (write 2.1 = 21/10); M_* <= 2.1/rho + 1 <= 3.1/rho. All exact rationals.
- **[note] L9-HYP-INCLUSIONS.** Keep U ⊆ V(G), F ⊆ E(G) and W ⊆ V(G) in the Spec (CONVENTIONS: the one-vertex path puts U ∩ W into the ball even outside V(H)). The hypothesis form matches what T16* Step 4 provides (P18s(ii) quantifies nonempty U ⊆ V, F ⊆ E).
- **[note] L9-DEPS.** Attribution-only \deps edge s1:citLem9 (no Lean node); undeclared s3:eqStar; Aharoni-Haxell not used. msreport should mark these.

**effort:** ~650 new Lean lines, difficulty 3/5 (Spec ~30; part (A) ~40; claim ~250 (remMultiset counting, t_0 bounds, choosing 2t_0-1 pairs, Prop 8 application); path Finset + hypergraph + Haxell application + extraction ~250; numerics ~80. Excludes Prop 8 (s1, ~600) and Haxell (stage alpha).)

### `s3:thmT16s` — theorem: Theorem 16*: linking through random sets; for-all multiset form (s3.tex:792)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/Link/T16s.lean (T16sStatement, 'every rho-random subset' form over an arbitrary finite space) + proof EG/Proof/Link/T16s.lean (stage alpha through L9rho: the proof term takes HaxellStatement, and BMProp8Statement until proved). Optional separate lemma for (b); (c) is not formalized.

**Statement (precise restatement).** Let X be a finite simple graph with N := |V(X)|, an (eps', s)-expander (Def 11) with 2^-7 <= eps' <= 1, L := log2 N; let 0 < rho <= 1 and t >= 1 be reals. Let (Omega, mu) be a finite probability space and R : Omega -> Finset V a rho-random subset of V(X) (IsRSubset: law = rsubset V(X) rho); X is deterministic (if X was produced at random, the consumer conditions on it and R must be independent of that randomness). Suppose rho N >= L^2 and s >= 2^135 t L^28 rho^-5. Then mu(X is (2^12 L^4, t)-path connected through R) >= 1 - 2^86 t L^19 rho^-3 N^-3. The event is the for-all multiset form of Def 7 (every admissible indexed family of pairs, endpoints anywhere), so the multiset may be chosen after R (s3:lemMonotone(iii)). (a) 2^86 is absolute; no lower bound on N (for N <= 1 the event is certain). (b) If N >= 2 then rho N > 2^27 L^5.6 N^(4/5) (because N > s); in particular rho N >= L^2 is implied. (c) (meta-claim) the requirement on s is linear in t, uniform in rho; 'the proof uses only s >= 2K_*(theta_*+1) <= 2^130.6 t L^28 rho^-5'. Proof: N >= 2 gives delta(X) > s so N > s >= 2^135, rho N >= 84, N >= 2^30; Step 1 colour E(X) uniformly with K_* colours independently of R (L15p: every class an (eps', s/(2K_*))-expander w.p. >= 1 - 2K_* N^-5, s/(2K_*) >= theta_*+1); Step 2 conditional on a good colouring, P18s(ii) per class, union over K_* classes (>= 1 - K_* N^-6); Step 3 Chernoff |R| >= rho N/2 (>= 1 - e^(-rho N/8)); Step 4 pigeonhole: some class carries <= |F|/K_* <= mu_*|U| edges of F, ball monotonicity, then L9rho; Step 5 failure <= 3K_* N^-5 + N^-3 <= 2^86 t L^19 rho^-3 N^-3, the colouring being auxiliary.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| (eps,s)-expander | Def 11 with log2 \|X\| | s1:citDef11 | yes: EG.FGraph.IsExpander; IsExpander.lt_deg (delta > s for eps > 0, \|X\| >= 2) |
| rho-random subset | law of R equals rsubset V(X) rho | s3 conventions | yes: EG.FinDist.IsRSubset; cond_of_indepFun, chernoff_card_lower_half, subset_ae |
| (ell,t)-path connected through R | Def 7 multiset form | s1:citDef7 | yes: EG.FGraph.IsPathConnected |
| K_*, theta_*, mu_*, sbar_*, ell_* and facts (S5) | (eqStar) with n := N | s3:eqStar | no: EG.Star.* and EG.Spec.StarFactsStatement (s3a blueprint) |
| uniform K-colouring of E(X), colour classes | randColouring ↥X.edges K; colourClass X c i | s3:lemL15p | yes: EG.FinDist.randColouring, EG.FGraph.colourClass, EG.l15p_prod_fst |
| product space colouring x (Omega, mu), conditioning on the colouring | (randColouring).prod mu; map_snd_cond_prod_fst | proof, Steps 1-2 | yes: FinDist.prod, map_snd_cond_prod_fst, prob_prod_snd (EG/Lib/Prob/Basic.lean) |

**deps_declared** (manuscript \deps): s3:lemL15p, s3:propP13s, s3:lemL17s, s3:lemP18s, s3:lemL9rho, s3:lemMonotone, s1:citDef11, s1:citChernoff

**deps_from_proof:** s3:eqStar, s3:lemL15p, s3:lemP18s, s3:lemL9rho, s3:lemMonotone, s1:citDef11, s1:citChernoff

**deps_notes:** s3:propP13s and s3:lemL17s are used only through s3:lemP18s (and in the commentary of (b),(c)); s3:eqStar ((S5): K_* >= sbar/mu_*, K_* <= (6·2^81+1) t L^19 rho^-3, 2K_*(theta_*+1) <= ..., 40K_*L <= 2K_*(theta_*+1)) is used but undeclared; s1:citThm16 is an undeclared attribution (ms_deps: undeclared_backward). Ball monotonicity in Step 4 is EG.ball_mono_edges (Lib), not s3:lemMonotone. lemMonotone(iii) is used in the statement and Step 5 (event depends only on (X, R)).

**used_by:** s3:lemCOLJV (rows 4-7 formulate its hypotheses and failure bounds); s3:lemCOL (b), (c) (conditional on the stage-1 colouring); s4:lemTPV (G2) (X := R_{j,c}, rho := 1/L, t := 2^10 L^8, then observation (MC)); s4:lemPV (G2); s4:thmVXp (G2)

**randomness:** Spec: an arbitrary finite probability space (Omega, mu) carrying R with IsRSubset R V(X) rho; X deterministic. Proof: Omega' := (randColouring ↥X.edges K_*).prod mu (colouring independent of R); Step 2 conditions on the colouring c (positive probability) — R is still rho-random under the conditional law (map_snd_cond_prod_fst / IsRSubset.cond_of_indepFun); the final event depends on R only, so its probability on Omega' equals that on mu (prob_prod_snd). Consumers: s3:lemCOL conditions on the whole stage-1 colouring of Y and applies T16* to the conditional law of T_j(Y,l) or of a zone; s4 applies it to an auxiliary (1/L)-random set V' and transfers by (MC).

**lean_shape:**

```lean
-- EG/Spec/Link/T16s.lean
def EG.Spec.T16sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : EG.FGraph V) (ε' s ρ t : ℝ) (Ω : Type u) (μ : EG.FinDist Ω)
    (R : Ω → Finset V),
    X.IsExpander ε' s → 2 ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 → 1 ≤ t →
    μ.IsRSubset R X.verts ρ →
    Real.logb 2 X.card ^ 2 ≤ ρ * X.card →
    2 ^ 135 * t * Real.logb 2 X.card ^ 28 / ρ ^ 5 ≤ s →
    1 - 2 ^ 86 * t * Real.logb 2 X.card ^ 19 / ρ ^ 3 * (X.card : ℝ) ^ (-3 : ℤ) ≤
      μ.prob {ω | X.IsPathConnected (2 ^ 12 * Real.logb 2 X.card ^ 4) t (R ω)}
-- EG/Proof/Link/T16s.lean
theorem EG.t16s (hHax : EG.Spec.HaxellStatement.{u}) (hP8 : EG.Spec.BMProp8Statement.{u}) :
    EG.Spec.T16sStatement.{u}
-- optional, (b) (no consumer):
-- theorem EG.t16s_forced ... (hN : 2 ≤ X.card) :
--   2 ^ 27 * Real.logb 2 X.card ^ (28/5 : ℝ) * (X.card : ℝ) ^ (4/5 : ℝ) < ρ * X.card
```

**hazards:**

- **[risk] T16-STEP1-PRODUCT.** 'Colour E(X) with K_* colours, uniformly and independently of V' and 'condition on a colouring ...; V is still rho-random' hide the whole product/conditioning construction: Omega' := (randColouring ↥X.edges K_*).prod mu; L15p on the first factor (EG.l15p_prod_fst exists); for each colouring c with all classes expanders, the conditional law of R is rsubset (map_snd_cond_prod_fst); P18s(ii) for each of the K_* classes (the class graphs are colourClass X c i with the same verts, so the (eqStar) parameters coincide); union bound; P(bad) <= P(c bad) + max_{c good} P(bad | c) (prob_compProd_le_of_forall-style slicing); transfer of the R-only event back to mu (prob_prod_snd). K_* needs a NeZero instance (ceil of a positive real). All ingredients exist; ~200 lines of plumbing.
- **[note] T16-AE-SUBSET.** IsRSubset gives R ω ⊆ V(X) only for ω in the support (IsRSubset.subset_ae); L9rho needs W ⊆ V(G). The good event must be intersected with the support (or the probability computed as a sum over the support).
- **[note] T16-S5-FORM.** Use (S5) in the exact rational form of the s3a StarFactsStatement (K_* <= (6·2^81+1) t L^19/rho^3; 2K_*(theta_*+1) <= 2(6·2^81+1)(2^46+1) t L^28/rho^5) and compare with 2^135 and 2^86 by norm_num: 2(6·2^81+1)(2^46+1) <= 2^135 and 3(6·2^81+1)+1 <= 2^86 (margins ~2^4.4 and ~2^0.8). Never state the rpow constants 2^83.6, 2^130.6.
- **[note] T16-STEP0-NO-RPOW.** Step 0 derives N >= 2^30, rho N >= 84 and e^(-rho N/8) <= N^-3 via (b) with rpow L^5.6 N^(4/5). All three follow without rpow from rho^5 N > rho^5 s >= 2^135 t L^28 (N > s since delta(X) > s): rho N >= rho^5 N > 2^135 L^28 >= 2^135, and rho N/8 >= 3 ln N = 3 L ln 2 as 2^135 L^28 >= 24 L for L >= 1. Recommend omitting (b) from the Spec (no consumer); if kept, a separate rpow lemma.
- **[note] T16-C-META.** Item (c) says 'The proof uses only s >= 2K_*(theta_*+1)'. As written this is inaccurate: the Step 0 paragraph uses the full hypothesis s >= 2^135 t L^28 rho^-5 (to get N > 2^135, rho N >= 84, N >= 2^30 and e^(-rho N/8) <= N^-3). A variant assuming only s >= 2K_*(theta_*+1) is plausible (2K_*(theta_*+1) >= ~2^120 t L^28 rho^-5 would still force these) but is not written. No consumer uses (c); do not formalize it. Suggested manuscript wording: 'Apart from Step 0, the proof uses only ...'.
- **[note] T16-RHO-POS.** IsRSubset allows rho = 0; the Spec adds 0 < rho (CONVENTIONS). The hypothesis rho N >= L^2 is unused in the proof (implied by the others for N >= 2) but kept for faithfulness; t is real (s4 passes t = 2^10 L^8).
- **[note] T16-DEGENERATE-N.** For N ∈ {0, 1}: Lean's logb 2 N = 0, so the bound reads 1 - 0 <= prob; the event holds at every ω because no pair of distinct vertices exists (every admissible family has an empty index type). Needs a small Lib lemma (IsPathConnected of a graph with < 2 vertices).
- **[note] T16-STEP4-PIGEONHOLE.** Some class i has |F ∩ E(X_i)| <= |F|/K_*: Σ_i |F ∩ E(X_i)| = |F| because the colour classes partition E(X) (disjoint_colourClass_edges + cover), then an averaging lemma. F ∩ E(X_i) ⊆ E(X_i) as P18s(ii) requires; X_i - (F ∩ E(X_i)) has edge set ⊆ E(X) \ F, so EG.ball_mono_edges gives the inclusion of balls. K_* >= sbar_*/mu_* from (S5).
- **[note] T16-STAGE-ALPHA.** Through L9rho the proof depends on the stage-alpha Haxell hypothesis (and on BMProp8 until it is proved); the Spec is hypothesis-free, the proof term EG.t16s takes them as arguments; every consumer proof (lemCOL, s4) inherits them until stage beta.
- **[note] T16-DEPS.** Declared s3:propP13s and s3:lemL17s are indirect (via s3:lemP18s); s1:citThm16 undeclared attribution; s3:eqStar undeclared. Universe: Ω : Type u (as in the s3a Specs); lemCOL's stage-1 space and s4's spaces are built from V and live in Type u.

**effort:** ~450 new Lean lines, difficulty 3/5 (Spec ~30; N <= 1 case ~20; Step 0 numerics ~60; Steps 1-2 product/conditioning/union ~200; Step 3 Chernoff ~30; Step 4 pigeonhole + L9rho application ~70; Step 5 arithmetic ~40.)

### `s3:lemHB` — lemma: Lemma HB: candidate sets of bounded multiplicity (the name HB is historical); Hall argument (s3.tex:904)

- **Manuscript referee status:** x2+RT for the statement; re-proved via Hall's theorem in v6 (R4): one clean-room AI review (G0, 2026-09-26)
- **Formalization:** Spec EG/Spec/Link/HB.lean (HBStatement) + proof EG/Proof/Link/HB.lean (Mathlib Hall: Finset.all_card_le_biUnion_card_iff_exists_injective); a Lib wrapper EG.hbSets defined by Classical.choose for consumers.

**Statement (precise restatement).** Let X be a finite simple graph with N := |V(X)| >= 2, an (eps', s)-expander with 2^-7 <= eps' <= 1, L := log2 N. Let m be a natural number with m >= 1 and 2m <= s (s real), and b := ceil(2 m L^2/eps') (a natural number). Then there is a map A assigning to every vertex w of X a set A(w) ⊆ N_X(w) with |A(w)| = m, such that every vertex u lies in at most b of the sets A(w), w ∈ V(X) (i.e. #{w ∈ V(X) : u ∈ A(w)} <= b). (At eps' = 2^-5, 2^-6, 2^-7: b = ceil(64 L^2 m), ceil(128 L^2 m), ceil(256 L^2 m).) Proof: SDR (Hall) of the ordered edge pairs (w,u) into load slots (u, j), j ∈ [b], and spare slots (w, i), i ∈ [d(w) - m]; at least m pairs of each w land in load slots, which gives A(w) and the multiplicity bound. Hall's condition via S' := {w : d(w) - |E_w| <= m-1}, U ⊆ S' with 1 <= |U| <= 2N/3 and |U| >= |S'|/2, F := E(U, V \ R), expansion gives b|R| >= m|S'|.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| (eps,s)-expander; delta(X) > s | Def 11; min degree remark | s1:citDef11 | yes: EG.FGraph.IsExpander, IsExpander.lt_deg |
| N_X(w), d_X(w) | X.nbrs w = verts.filter (Adj w); deg = card | s1:convGraphs(c) | yes: EG.FGraph.nbrs, EG.FGraph.deg |
| ordered edge pairs vec E(X), slots, T(a) | arrows (w,u) with s(w,u) ∈ E(X); load slots (u,j,1), j < b; spare slots (w,i,2), i < d(w)-m | proof of s3:lemHB | no: proof-internal (Finset (V × V), slots as V × ℕ × Bool) |
| Hall's theorem | SDR exists iff \|⋃_{a∈J'} T(a)\| >= \|J'\| for all J' | s1:citHall | yes: Mathlib Finset.all_card_le_biUnion_card_iff_exists_injective |

**deps_declared** (manuscript \deps): s1:citHall, s1:citDef11

**deps_from_proof:** s1:citHall, s1:citDef11

**deps_notes:** Exact. Def 11 is used twice: the min-degree remark (d(w) > s >= 2m, needed so that d(w) - m >= 0 spare slots exist) and the expansion of U with F.

**used_by:** s4:lemTPV (X := O, eps' := eps_O >= 2^-7, m := ceil(L^6); b <= ceil(2^8 L^2 m)); s4:lemPV (eps' = 2^-6, m = ceil(L^6)); s4:thmVXp (eps' = eps_O >= 2^-7, m = ceil(L^3)); s5:defStages (X_Y, eps' = 2^-6, m = ceil(L_Y^6), b = ceil(2^7 L_Y^2 m) = b_Y; family fixed by a rule); s5:lemE1 (a) (the fixed sets A_Y(w))

**randomness:** none (deterministic). Consumers fix one family 'by a fixed rule' (lexicographically first) so that it is a function of the graph: Classical.choose on the Spec's existential.

**lean_shape:**

```lean
-- EG/Spec/Link/HB.lean
def EG.Spec.HBStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : EG.FGraph V) (ε' s : ℝ) (m : ℕ),
    X.IsExpander ε' s → 2 ≤ X.card → 2 ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 1 ≤ m → 2 * (m : ℝ) ≤ s →
    ∃ A : V → Finset V,
      (∀ w ∈ X.verts, A w ⊆ X.nbrs w ∧ (A w).card = m) ∧
      ∀ u : V, (X.verts.filter (fun w => u ∈ A w)).card ≤
        ⌈2 * (m : ℝ) * Real.logb 2 X.card ^ 2 / ε'⌉₊
-- Lib: noncomputable def EG.hbSets (X) (ε' s m) (h : hyps) : V → Finset V := Classical.choose (EG.hb ... )
```

**hazards:**

- **[risk] HB-UNREVIEWED.** v6 (R4) proof with one AI review. Re-derived in full: (1) SDR ⇒ sets: at most d(w)-m arrows of w use spare slots of w, so >= m use load slots of their head, and injectivity bounds #{w : u ∈ A(w)} by b; (2) the union in Hall's condition is b|R| + Σ_{w∈S}(d(w)-m) (slots of distinct vertices are distinct); (3) S', |N(w) \ R| <= m-1 on S'; U := S' or a ceil(|S'|/2)-subset (<= ceil(N/2) <= 2N/3 for N >= 2); F := {wu : w ∈ U, u ∉ R}, |F| <= (m-1)|U| <= s|U|; an edge vw ∉ F with w ∈ U and v ∉ U forces v ∈ R; so N_{X-F}(U) ⊆ R and b|R| >= b ε'|U|/L^2 >= m|S'| >= LHS. Correct. The 'd(w)-m > m' remark is 'not needed' in the working copy; only d(w) >= m is needed (spare-slot count as ℕ subtraction).
- **[note] HB-PLAN-MISMATCH.** PLAN §2 R4 describes 'm rounds of Mathlib's Hall theorem on V × [ceil(2L^2/eps')]' with b' <= b + m. The v6 manuscript instead makes ONE Hall application with load and spare slots and gets exactly b. Formalize the manuscript version: s5:defStages needs b = ceil(2^7 L_Y^2 m) = b_Y exactly and s4 needs b <= b_vortex = ceil(2^8 L^2 m); a b+m variant would change these constants.
- **[note] HB-HALL-ENCODING.** Mathlib Hall is stated for t : ι → Finset α with ι a Fintype (use the subtype of the arrow Finset) and gives f injective with f a ∈ t a. Slot encoding α := V × ℕ × Bool; computing |⋃_{a∈E} T(a)| = b|R| + Σ_{w∈S}(d(w)-m) needs a disjoint-union bookkeeping lemma (~80 lines).
- **[note] HB-EPS-UNUSED.** The proof uses only 0 < eps' (min degree, expansion); eps' <= 1 and eps' >= 2^-7 are unused (2^-7 enters b's value at call sites). Keep both for faithfulness.
- **[note] HB-FIXED-RULE.** Consumers need A as a function of X ('the lexicographically first such family'): EG.hbSets via Classical.choose (PLAN decision 7); only its properties are used downstream.
- **[note] HB-NBRS-VERTS.** EG.FGraph.nbrs filters X.verts, so A(w) ⊆ V(X) automatically; the multiplicity count is over w ∈ V(X) (A w for w ∉ V(X) is junk and excluded).

**effort:** ~320 new Lean lines, difficulty 3/5 (Spec ~25; SDR ⇒ sets ~70; union count ~80; S', U, F and expansion ~120; wrapper ~25.)

### `s3:defCOL` — definition: stage-1 lending data: the two-stage colouring COL-JV and the JS labels (s3.tex:1035)

- **Manuscript referee status:** x2; t_Y changed by CR1-PV: x1
- **Formalization:** Defs EG/Defs/Lend/COL.lean (index tags and index Finsets, per-edge and label laws, outcome type, law colLaw, classes, derived quantities) + API EG/Lib/Lend/COL.lean (marginal laws and independence facts, restricted-colouring law given the split, T_j rho_l-random, partition facts, p_Y, t_Y >= M_l). No Spec of its own; locked through the Specs of s3:lemCOL, s5, s6, s7 that mention it. Must be fixed in P2-D together with the s2 run data model.

**Statement (precise restatement).** Fix a valid HB*tau+ run on G (rounds 1..R). For every ancestor Y of round r (s2:defAncestors: V(Y), H_Y a graph with vertex set V(Y), eps_Y, s_Y, L_Y = log2|V(Y)|, type light/standalone), the following random data are drawn, independently across ancestors. (i) Own/Lend split: every edge of H_Y independently lies in Own_Y or Lend_Y with probability 1/2 each (graphs on V(Y)). (ii) Lent classes: index families I_U(Y) := {(l,c,sigma) : r+2 <= l <= R, c ∈ [4], sigma ∈ [T^sl_Y]} with T^sl_Y := ceil(L_Y^2) if Y is light, empty if standalone; I_JS(Y) := {(l,j) : r+2 <= l <= R, 0 <= j < K^JS_l} with K^JS_l := M_l^2; I_JV(Y) := {l : r+2 <= l <= R}; tagged (pairwise disjoint); k_lend(Y) := |I_U| + |I_JS| + |I_JV|. If r <= R-2, every edge of Lend_Y independently receives an index uniform on the tagged union; the edges with index (l,c,sigma) form LU_{Y,l,c,sigma}, with (l,j) form LJS_{Y,l,j}, with l form LJV_{Y,l} (graphs on V(Y)). If r >= R-1, the families are empty, k_lend = 0, Lend_Y has no classes. (iii) Own classes (light Y only): J_Y := floor(log2(L_Y/8)), k_own := 4J_Y + 1; every edge of Own_Y independently receives one of k_own labels uniformly: own classes R_{j,c} (0 <= j < J_Y, c ∈ [4]) and M (graphs on V(Y)); standalone: Own_Y not subdivided. (iv) JS labels: for every r+2 <= l <= R and y ∈ V(Y) independently, lab_{Y,l}(y) ∈ {*} ∪ {0,..,K^JS_l - 1} with P(= j) = rho_l := M_l^-4 for each j and P(= *) = 1 - M_l^-2; T_j(Y,l) := {y : lab_{Y,l}(y) = j}. Formal model: each edge of H_Y carries three independent uniform variables (fair bit, lent index, own label); labels independent of all edge variables. Consequences: colours of distinct edges independent; ancestors independent; labels independent of colours; given Lend_Y, stage (ii) is a uniform k_lend-colouring of Lend_Y, given Own_Y stage (iii) a uniform k_own-colouring; for fixed (l,j), T_j(Y,l) is a rho_l-random subset of V(Y) independent of the colouring, and the T_j(Y,l), 0 <= j < K^JS_l, are pairwise disjoint. Derived: p_Y := 1/(2 k_lend(Y)) (k_lend >= 1) = P(fixed edge of H_Y ∈ LJV_{Y,l}); t^JS_l := 2M_l + 2; for light Y of round r, t_Y := ceil(lambda_r^1.6) (U-multiplicity parameter), with t_Y >= M_l for r+2 <= l <= R (claim). Consumers (COL(g), a design rule): Own_Y (+ own classes) only Y's own device (TPV if standalone; P-vortex, or VX+ if demoted, if light); LU_{Y,l,c,sigma} only the Theorem-U chaining of bundle B_{l,c} in slot sigma; LJS_{Y,l,j} only the JS-LC systems of (Y,l) at junction j; LJV_{Y,l} only the round-l J-consumer; unused lent edges are junk for Y's own device; for r >= R-1 all of Lend_Y is junk (Lent(Y) = ∅, Erem(Y) = E_r(Y), H_0(Y) = E_r(Y), per s6:consOrder). After the definition: the H_Y of all ancestors are pairwise edge-disjoint (propStructure(iii)); the label law is well defined as K^JS_l rho_l = M_l^-2 <= 1.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| valid run, R, rounds, d_r, lambda_r = log2 d_r, M_l, s_r | s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T log^4 T) (see blocker COL-M-INTEGER) | s2:defHBtp | no: EG.HB.Run, run.d, lamOf, MOf, sOf, run.R (s2a blueprint, P2-D) |
| ancestor Y = (r, a), V(Y), H_Y, eps_Y, s_Y, L_Y, light/standalone | one ancestor per round-r pre-part address a; H_Y = X_Y (light) or X^0_Y (standalone) | s2:defAncestors | no: EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/isLight (s2a blueprint) |
| lent index tags and families I_U, I_JS, I_JV; k_lend | inductive LentTag \| U (l : ℕ) (c : Fin 4) (σ : ℕ) \| JS (l j : ℕ) \| JV (l : ℕ); lentIdx Y : Finset LentTag = IU ∪ IJS ∪ IJV (disjoint by constructor); klend := card | s3:defCOL(ii) | no: new EG.Lend.LentTag, IU, IJS, IJV, lentIdx, klend |
| T^sl_Y, K^JS_l, rho_l, t^JS_l, t_Y, p_Y | ⌈L_Y^2⌉₊; M_l^2; (M_l : ℝ)^-4; 2M_l + 2; ⌈lambda_r^(8/5)⌉₊; 1/(2 klend) | s3:defCOL | no: new EG.Lend.Tslot, KJS, rhoJS, tauJS, tY, pY |
| J_Y, k_own, own-label names | J_Y := ⌊log2(L_Y/8)⌋₊ ; kown := 4 J_Y + 1 (defined for every Y); R_{j,c} ↔ label 4j + c, M ↔ label 4J_Y | s3:defCOL(iii), s4:lemPV | no: new EG.Lend.JY, kown, ownR, ownM |
| per-edge law and JS-label law | edgeLaw Y := bernoulli(1/2) ⊗ idxLaw Y ⊗ uniform (Fin kown); idxLaw Y := (uniform ↥(lentIdx Y)).map (some ∘ val) if nonempty, else dirac none; jsLabelLaw l on Option ℕ: some j (j < KJS l) weight M_l^-4, none weight 1 - M_l^-2 | s3:defCOL (formal paragraph), (iv) | no: new; built from EG.FinDist.bernoulli/uniform/dirac/map/ofFinset |
| outcome type and law | COLOut Y := (↥(H_Y).edges → Bool × Option LentTag × Fin (kown Y)) × (JSSite Y → Option ℕ), JSSite Y := {(l, y) : r+2 <= l <= R, y ∈ V(Y)}; colLaw Y := (pi edgeLaw).prod (pi jsLabelLaw) | s3:defCOL | no: new EG.Lend.COLOut, colLaw |
| Own_Y, Lend_Y, lent classes, own classes, T_j(Y,l) | colourClass H_Y (bit ·) false/true; colourClass H_Y (fun e => (bit e, idx e)) (true, some i); colourClass H_Y (fun e => (bit e, own e)) (false, o); V(Y).filter (lab (l,y) = some j) | s3:defCOL | partly: EG.FGraph.colourClass (EG/Lib/Found/ColourClass.lean), EG.FinDist.selectSet |
| stage-1 space (product over ancestors, with zones (1b) and pools (1d)) | pi over the Finset of ancestors of colLaw, times the s5/s7 factors | s7:defSchedule (1a)-(1d) | no: EG/Defs/Lend/Stage1.lean (PLAN §3 'Stage1'), P2-D |
| consumers (own devices, Theorem-U chaining, U-bundles B_{l,c}, JS-LC systems, J-consumer, Lent(Y), Erem(Y), H_0(Y), E_r(Y)) | forward references | s4, s5:lemParent, s6:lemJSLC, s6:defJconsumer, s6:consOrder | no (later chunks) |

**deps_declared** (manuscript \deps): s2:defAncestors, s2:propStructure, s2:lemTower

**deps_from_proof:** s2:defHBtp, s2:defAncestors, s2:lemTower, s2:propStructure, s1:condG1, s6:consOrder, s3:lemCOL

**deps_notes:** The definition proper needs only s2:defHBtp (R, lambda_r, M_l) and s2:defAncestors. The embedded claims need: s2:lemTower(a),(b) + s1:condG1 (t_Y >= M_l); s2:propStructure(iii) (edge-disjointness of the H_Y, sentence after the definition); s6:consOrder (forward: Lent(Y), Erem(Y), H_0(Y) in 'Consumers'); s3:lemCOL(c) (forward: role of t_Y). s2:defHBtp is undeclared; s6:consOrder and s3:lemCOL are forward references (ms_deps: forward_refs).

**used_by:** s3:lemCOLJV; s3:lemCOL; s5:defZones; s5:lemZones; s5:defStages; s5:lemE1; s5:lemChild; s5:lemParent; s5:lemKRED; s6:defLending; s6:lemLost; s6:lemJSLC; s6:lemJplus; s6:defJconsumer; s6:consOrder; s6:lemLent; s6:thmMIXC; s7:defPool; s7:defCand; s7:lemCand; s7:defSchedule; s7:lemLift

**randomness:** Per ancestor Y: sample space COLOut Y with law colLaw Y = (product over e ∈ E(H_Y) of Bernoulli(1/2) × idxLaw Y × Uniform(Fin kown)) × (product over (l, y), r+2 <= l <= R, y ∈ V(Y), of jsLabelLaw l). Globally: product over all ancestors (independent), one factor of the stage-1 space (s7:defSchedule: (1a) colourings, (1c) JS labels; (1b) zones and (1d) pools are further independent factors). Nothing is conditioned on in the definition. Consumers condition on: the split bits (L15p for stages (ii),(iii): s3:lemCOL(a), s5:lemE1(b)); the whole colouring of Y (T16* for T_j(Y,l) in s3:lemCOL(b), for zones in (c)); a stage-1 outcome (s5, s6: statuses as deterministic functions).

**lean_shape:**

```lean
-- EG/Defs/Lend/COL.lean  (Y = (r, a) an ancestor of the valid run `run` on `G`; all defs total)
inductive EG.Lend.LentTag | U (l : ℕ) (c : Fin 4) (σ : ℕ) | JS (l j : ℕ) | JV (l : ℕ)
noncomputable def EG.Lend.Tslot (run G Y) : ℕ := ⌈run.LY G Y.1 Y.2 ^ 2⌉₊
def EG.Lend.KJS (run G) (l : ℕ) : ℕ := run.M G l ^ 2                      -- needs M_l : ℕ (blocker COL-M-INTEGER)
noncomputable def EG.Lend.rhoJS (run G) (l : ℕ) : ℝ := ((run.M G l : ℕ) : ℝ)⁻¹ ^ 4
def EG.Lend.tauJS (run G) (l : ℕ) : ℕ := 2 * run.M G l + 2
def EG.Lend.lateRounds (run) (r : ℕ) : Finset ℕ := Finset.Icc (r + 2) run.R
def EG.Lend.IU (run G Y) : Finset LentTag := if run.isLight G Y.1 Y.2 then
    (lateRounds run Y.1).biUnion (fun l => Finset.univ.biUnion (fun c : Fin 4 => (Finset.range (Tslot run G Y)).image (LentTag.U l c))) else ∅
def EG.Lend.IJS (run G Y) : Finset LentTag := (lateRounds run Y.1).biUnion (fun l => (Finset.range (KJS run G l)).image (LentTag.JS l))
def EG.Lend.IJV (run G Y) : Finset LentTag := (lateRounds run Y.1).image LentTag.JV
def EG.Lend.lentIdx (run G Y) : Finset LentTag := IU run G Y ∪ IJS run G Y ∪ IJV run G Y
def EG.Lend.klend (run G Y) : ℕ := (lentIdx run G Y).card
noncomputable def EG.Lend.JY (run G Y) : ℕ := ⌊Real.logb 2 (run.LY G Y.1 Y.2 / 8)⌋₊
def EG.Lend.kown (run G Y) : ℕ := 4 * JY run G Y + 1                         -- defined for every Y (≥ 1)
noncomputable def EG.Lend.pY (run G Y) : ℝ := 1 / (2 * (klend run G Y : ℝ))
noncomputable def EG.Lend.tY (run G Y) : ℕ := ⌈run.lam G Y.1 ^ (8 / 5 : ℝ)⌉₊
-- laws
noncomputable def EG.Lend.idxLaw (run G Y) : FinDist (Option LentTag) :=
  if h : (lentIdx run G Y).Nonempty then (FinDist.uniform ↥(lentIdx run G Y)).map (fun i => some i.1) else FinDist.dirac none
noncomputable def EG.Lend.edgeLaw (run G Y) : FinDist (Bool × Option LentTag × Fin (kown run G Y)) :=
  (FinDist.bernoulli (1/2) _ _).prod ((idxLaw run G Y).prod (FinDist.uniform _))
noncomputable def EG.Lend.jsLabelLaw (run G) (l : ℕ) : FinDist (Option ℕ) :=   -- some j (j < KJS l): M_l^-4 each; none: 1 - M_l^-2
  FinDist.ofFinset (insert none ((Finset.range (KJS run G l)).image some)) (fun o => if o = none then 1 - (run.M G l : ℝ)⁻¹ ^ 2 else (run.M G l : ℝ)⁻¹ ^ 4) _ _ _
def EG.Lend.JSSite (run G Y) : Finset (ℕ × V) := (lateRounds run Y.1) ×ˢ run.ancVerts G Y.1 Y.2
def EG.Lend.COLOut (run G Y) : Type _ := (↥(run.ancGraph G Y.1 Y.2).edges → Bool × Option LentTag × Fin (kown run G Y)) × (↥(JSSite run G Y) → Option ℕ)
noncomputable def EG.Lend.colLaw (run G Y) : FinDist (COLOut run G Y) :=
  (FinDist.pi fun _ => edgeLaw run G Y).prod (FinDist.pi fun s => jsLabelLaw run G s.1.1)
-- classes (all spanning on V(Y) = (run.ancGraph G Y.1 Y.2).verts)
def EG.Lend.Own  (ω : COLOut run G Y) : FGraph V := (run.ancGraph G Y.1 Y.2).colourClass (fun e => (ω.1 e).1) false
def EG.Lend.Lend (ω) : FGraph V := (run.ancGraph G Y.1 Y.2).colourClass (fun e => (ω.1 e).1) true
def EG.Lend.lentClass (ω) (i : LentTag) : FGraph V := (run.ancGraph G Y.1 Y.2).colourClass (fun e => ((ω.1 e).1, (ω.1 e).2.1)) (true, some i)
def EG.Lend.ownClass (ω) (o : Fin (kown run G Y)) : FGraph V := (run.ancGraph G Y.1 Y.2).colourClass (fun e => ((ω.1 e).1, (ω.1 e).2.2)) (false, o)
def EG.Lend.T (ω) (l j : ℕ) : Finset V := (run.ancVerts G Y.1 Y.2).filter (fun y => ∃ h : (l, y) ∈ JSSite run G Y, ω.2 ⟨(l, y), h⟩ = some j)
-- LU Y l c σ := lentClass (U l c σ); LJS Y l j := lentClass (JS l j); LJV Y l := lentClass (JV l)
-- Stage1 (P2-D): FinDist.pi over ancestors of colLaw, times zones (s5:defZones) and pools (s7:defPool)
```

**hazards:**

- **[blocker] COL-M-INTEGER.** (Inherited from s2a HB-M-INTEGER; decision needed before EG/Defs/Lend/COL.lean.) K^JS_l := M_l^2 is used as the NUMBER of JS classes (0 <= j < K^JS_l) and the label law needs K^JS_l·rho_l = M_l^-2 exactly; with (R2) M_l = max(2^40, 2^16 T log^4 T) a real number this is ill-typed. Proposed decision (as s2a): M_l := ceil(max(2^40, 2^16 T log^4 T)) ∈ ℕ. Impact here: none on the table rows except (B6) Λ_r <= λ+6μ+20 (see COLJV-B6-CEILING). Alternative (K^JS_l := ceil(M_l^2)) changes (i)'s |I_JS| <= (4/3)M^2 to <= (4/3)M^2 + (R - r - 1) and s6:lemLost's K^JS rho = M^-2 to <= M^-2 + M^-4.
- **[risk] COL-EMPTY-INDEX.** The 'formal' sentence 'every edge e of H_Y carries three independent uniform random variables (a fair bit, a lent index and an own label)' is ill-defined when k_lend(Y) = 0 (r >= R-1: uniform on the empty set; FinDist.uniform needs Nonempty) and for standalone Y (J_Y and k_own are defined only for light Y). Lean decision: lent index ∈ Option LentTag with idxLaw = dirac none when lentIdx Y = ∅; own label ∈ Fin (kown Y) with kown := 4⌊log2(L_Y/8)⌋₊ + 1 >= 1 defined for EVERY ancestor (an unused, independent label for standalone Y). Neither changes any law that the manuscript uses. Suggested wording: 'a lent index (if r <= R-2) and an own label (if Y is light)'.
- **[risk] COL-RANDOM-EDGESET.** (= s3a L15-RANDOM-EDGESET, resolved by this data model.) Lend_Y and Own_Y are random; L15p colours a FIXED edge Finset. With per-edge labels on the fixed E(H_Y), the needed API lemma is: conditional on the bit vector β (positive probability), the law of (fun e : ↥(Lend β).edges => idx e) is randColouring ↥(Lend β).edges k_lend transported along ↥(lentIdx Y) ≃ Fin k_lend (and the own labels on Own β likewise with Fin kown), and the classes are the colourClass of Lend β. Ingredients exist (map_selectSet_randColouring, l15p_of_map_eq, cond lemmas) but restriction of a pi to a random sub-index-set given the bits is new (~150 lines).
- **[risk] COL-CONSUMERS-NOT-A-PROPERTY.** The paragraph 'Consumers (property COL(g))' is a DESIGN RULE for the constructions of s4-s6 (which device may read which class), plus forward claims about s6:consOrder objects (Lent(Y) = ∅ for r >= R-1, Erem(Y) = E_r(Y), H_0(Y) = E_r(Y)). It is not a property of the random data and cannot be a lemma of s3. Its s3 content is only the partition facts (s3:lemCOL(g)). Exclusivity must be built into the Lean constructions of s5:lemParent, s6:lemJSLC, s6:defJconsumer, s6:consOrder (each consumer's input restricted to its class) and proved there; downstream independence arguments (s5:lemE1, s6:lemLost, s7:lemCand, s7:lemLift) silently rely on it. Undeclared forward dependency on s6:consOrder.
- **[note] COL-TY-CLAIM.** 't_Y >= M_l for every r+2 <= l <= R' is a lemma needing G1 through s2:lemTower(a),(b) (M_l <= λ_{l-2}^1.6 <= λ_r^1.6), not part of the definition; put it in the COL API (used by s5:lemParent 'Comparison with t_Y'). t_Y := ⌈λ_r^(8/5)⌉₊ (rpow; λ_r > 0 under G1).
- **[note] COL-LABEL-LAW.** The JS-label law is a non-uniform law built with ofFinset/ofFintype; statement reviewers must check its weights (CONVENTIONS). Nonnegativity of 1 - M_l^-2 needs M_l >= 1. API: T_j(Y,l) is rho_l-random (isRSubset_selectSet on the indicators {lab(l,y) = some j}_y, independent across y by the pi structure), T_j ∩ T_j' = ∅ for j ≠ j', and the labels are independent of the colouring (prod structure: indepFun_fst_snd).
- **[note] COL-ANCESTOR-INDEX.** Ancestors must be indexed by (round, pre-part address) (s2a HB-ADDRESS-IDENTITY). The global space is a FinDist.pi over the Finset of ancestors; edge-disjointness of the H_Y (propStructure(iii)) is not needed for the definition, only for consumers that look at a fixed edge e of G across ancestors.
- **[note] COL-NAMED-OWN-CLASSES.** Own labels Fin (4J_Y + 1) must be matched with the names R_{j,c} (0 <= j < J_Y, c ∈ [4]) and M used in s4:lemPV / s5:lemChild; fix the bijection (R_{j,c} ↔ 4j + c, M ↔ 4J_Y) in the Defs, and make s4:lemPV's J := ⌊log2(L/8)⌋ the same term as J_Y (CONVENTIONS: named colour families need an explicit bijection).
- **[note] COL-ZERO-BASED.** c ∈ [4] → Fin 4, sigma ∈ [T^sl_Y] → 0-based σ < Tslot, j already 0-based; rounds stay 1-based ℕ with r + 2 <= l <= R (never ℕ-subtract).
- **[note] COL-PY-DOMAIN.** p_Y := 1/(2 k_lend) is junk (0 in Lean) for k_lend = 0; every statement about p_Y assumes r <= R-2. 'p_Y is the probability that a fixed edge lies in LJV_{Y,l}' is an API lemma (1/2 · 1/k_lend) used by s7:lemCand.
- **[note] COL-STAGE-GROUPING.** s7:defSchedule lists (1a) colourings and (1c) JS labels as separate independent stage-1 families; defCOL bundles both per ancestor. Equivalent (all independent), but P2-D must fix ONE product structure with named projections so that s5/s6/s7 Specs state independence uniformly (IndepFun of projections).
- **[note] COL-EMBEDDED-FACTS.** 'The graphs H_Y are pairwise edge-disjoint' (propStructure(iii)) and 'the label distribution is well defined because K^JS_l rho_l = M_l^-2 <= 1' are lemmas, not definitions; the five 'Consequently' bullets are API lemmas of colLaw.

**effort:** ~750 new Lean lines, difficulty 4/5 (Defs ~300 (tags, index Finsets, laws, outcome type, classes, derived quantities, Stage1 hook); API ~450 (marginals and independence, restricted colouring given the split, T_j rho-random and disjoint, p_Y, partition facts, t_Y >= M_l, product over ancestors).)

### `s3:tabCOLJV` — table (supporting node, not in the chunk list): the COL-JV table (s3.tex:1137)

- **Manuscript referee status:** part of s3:lemCOLJV (x2, rows 4 and 7 x1; R6: one clean-room AI review); no separate referee row
- **Formalization:** Defs EG/Defs/Lend/COLTable.lean: EG.COLTable.{lam, Mbar, kbar, row : Fin 13 → ℝ → Prop, col3, triple, TypeE, v0}. Owned by this chunk; s1's Gamma1 (item (f): EG.S3.COLJVcol3 in the s1 blueprint — rename to EG.COLTable.col3 or alias) must use THIS constant.

**Statement (precise restatement).** 13 rows; column 2 = requirement (use), column 3 = sufficient inequality in the real μ (18 inequalities: two in row 1, five in row 8, one in each other row), column 4 = triples (a_i, b_i, c_i) for the type-(E) inequalities of s3:lemCOLJVev. λ := λ_r and μ := log2 λ, except rows 2, 11, 12 where λ := λ_{l-2}, 3 <= l <= R. Column 3 (G1(f)); λ := 2^μ, M̄ := (Aμ)^{2A}, k̄ := 192λ^3 + (4/3)M̄^2, A = 105:
 R1: λ^{102.5} > 257(λ + 6μ + 20)^{102} and λ^{1/2} > 2^{111};  R2: λ^{103} >= M̄^{13};  R3: λ^{99} >= 640 k̄;  R4: λ^{42.1} >= 2^{193}·12^5;
 R5: λ^{72} >= 3·2^{167} k̄ M̄^{21};  R6: λ^{84} >= 2^{110} M̄^{15};  R7: λ^{64.4} >= 2^{127}·12^4;
 R8: λ^{58} >= 2^{194}; λ^{62} >= 2^{186}(μ+1); λ^{62} >= 2^{190}(μ+1); λ^{58} >= 2^{191}; λ^{99} >= 64((2λ)^6 + 1);
 R9: k̄ <= λ^{3.3};  R10: 2k̄ <= λ^4;  R11: λ^{95} >= 2^{13} M̄^{12};  R12: M̄ <= λ^{1.6};  R13: λ^{36} >= 2^{240}(Aμ)^{46A}.
Column 4 triples (a,b,c): (0.5,112,0), (103,0,26A), (96,19,4A), (42.1,211,0), (69,178,46A), (84,110,30A), (64.4,142,0), (58,194,1), (0.3,9,4A), (1,10,4A), (95,13,24A), (1.6,0,2A), (36,240,46A).
Column 2 (precise forms to be asserted by s3:lemCOLJV(ii); N := |V(Y)|, L := L_Y, k := k_lend(Y), M := M_{r+2}):
 C1: every round-r pre-part Z: τ_r < θ^GC_r(Z^0);  C2: 3 <= l <= R: M_l^{13} <= P_{l-2};
 C3: 80L <= s_Y; light: 40 k_own L <= s_r/8; r <= R-2: 40 k L <= s_Y/4;
 C4: light, r <= R-2: 2^{135} t_Y L^{28} (12L^5)^5 <= s_Y/(8k);  C5: r <= R-2: 2^{135}(3M) L^{28} M^{20} <= s_Y/(8k);
 C6: r <= R-2: Σ_{(l,j)∈I_JS(Y)} 2^{86} t^JS_l L^{19} ρ_l^{-3} N^{-3} <= N^{-2}/4;  C7: light, r <= R-2: Σ_{I_U(Y)} 2^{86} t_Y L^{19}(12L^5)^3 N^{-3} <= N^{-2}/4;
 C8: 2^{150}L^{42} <= s_r/4; 2^{146}L^{38} log L <= s_r/4; 2^{151}L^{38} log L <= s_r/2; 2^{145}L^{41} <= s_r/(16k_own); 2⌈L^6⌉ <= s_r/(16k_own);
 C9: k <= λ_r^{3.3};  C10: r <= R-2: λ_r^{-4} <= p_Y;  C11: 3 <= l <= R: 2^{10}M_l^{10} <= λ_{l-2}^{95}/(8M_l^2);  C12: M_l <= λ_{l-2}^{1.6};  C13: G* at μ = log2 λ_r.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| λ(μ), M̄(μ), k̄(μ) | (2:ℝ)^μ; (105 μ)^210; 192 λ^3 + 4/3 M̄^2 | table caption | no: new EG.COLTable.lam/Mbar/kbar |
| row i μ, col3 μ | the column-3 inequalities of row i (list above), with exact rational exponents (205/2, 421/10, 322/5, 33/10, 8/5, 1/2) as Real.rpow of λ | table column 3; s1:condG1(f) | no: new EG.COLTable.row, EG.COLTable.col3 |
| triples, TypeE, v0 | triple : Fin 13 → ℝ × ℝ × ℝ (column 4); TypeE a b c μ := 0 <= aμ - b - c log2(105μ); v0 := (c + sqrt(c^2 + a(b + c log2 105)))/a | table column 4; s3:lemCOLJVev | no: new |
| column-2 requirements C1-C13 | precise inequalities listed above, stated per round/ancestor | table column 2 (informal) + proof of s3:lemCOLJV | no: new EG.Lend.COLReq* predicates (s3:lemCOLJV) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none

**deps_notes:** A table, not a statement. Referenced by s1:condG1(f) (forward), s3:lemCOLJV, s3:lemCOLJVev (declared dep), s3:lemCOL, s5:lemE1, s5:lemParent, s5:lemDemoted, s7:lemCand, s7:lemWellDef, s7:lemGammaSat.

**used_by:** s1:condG1 (item (f): column 3); s3:lemCOLJV; s3:lemCOLJVev; s3:lemCOL; s5:lemE1; s5:lemParent (row 12); s5:lemDemoted (row 8(c)); s7:lemCand (rows 10, 11); s7:lemWellDef (row 11); s7:lemGammaSat

**randomness:** none.

**lean_shape:**

```lean
-- EG/Defs/Lend/COLTable.lean
namespace EG.COLTable
noncomputable def lam (μ : ℝ) : ℝ := (2 : ℝ) ^ μ
noncomputable def Mbar (μ : ℝ) : ℝ := (105 * μ) ^ (210 : ℕ)
noncomputable def kbar (μ : ℝ) : ℝ := 192 * lam μ ^ 3 + 4 / 3 * Mbar μ ^ 2
noncomputable def row : Fin 13 → ℝ → Prop
  | 0, μ => 257 * (lam μ + 6 * μ + 20) ^ (102 : ℕ) < lam μ ^ (205 / 2 : ℝ) ∧ (2 : ℝ) ^ 111 < lam μ ^ (1 / 2 : ℝ)
  | 1, μ => Mbar μ ^ 13 ≤ lam μ ^ (103 : ℕ)
  | 2, μ => 640 * kbar μ ≤ lam μ ^ (99 : ℕ)
  | 3, μ => (2 : ℝ) ^ 193 * 12 ^ 5 ≤ lam μ ^ (421 / 10 : ℝ)
  | 4, μ => 3 * 2 ^ 167 * kbar μ * Mbar μ ^ 21 ≤ lam μ ^ (72 : ℕ)
  | 5, μ => (2 : ℝ) ^ 110 * Mbar μ ^ 15 ≤ lam μ ^ (84 : ℕ)
  | 6, μ => (2 : ℝ) ^ 127 * 12 ^ 4 ≤ lam μ ^ (322 / 5 : ℝ)
  | 7, μ => (2 : ℝ) ^ 194 ≤ lam μ ^ (58 : ℕ) ∧ 2 ^ 186 * (μ + 1) ≤ lam μ ^ (62 : ℕ) ∧ 2 ^ 190 * (μ + 1) ≤ lam μ ^ (62 : ℕ) ∧
             (2 : ℝ) ^ 191 ≤ lam μ ^ (58 : ℕ) ∧ 64 * ((2 * lam μ) ^ 6 + 1) ≤ lam μ ^ (99 : ℕ)
  | 8, μ => kbar μ ≤ lam μ ^ (33 / 10 : ℝ)
  | 9, μ => 2 * kbar μ ≤ lam μ ^ (4 : ℕ)
  | 10, μ => (2 : ℝ) ^ 13 * Mbar μ ^ 12 ≤ lam μ ^ (95 : ℕ)
  | 11, μ => Mbar μ ≤ lam μ ^ (8 / 5 : ℝ)
  | 12, μ => (2 : ℝ) ^ 240 * (105 * μ) ^ (46 * 105) ≤ lam μ ^ (36 : ℕ)
def col3 (μ : ℝ) : Prop := ∀ i, row i μ
def triple : Fin 13 → ℝ × ℝ × ℝ := ![(1/2, 112, 0), (103, 0, 26*105), (96, 19, 4*105), (421/10, 211, 0), (69, 178, 46*105),
  (84, 110, 30*105), (322/5, 142, 0), (58, 194, 1), (3/10, 9, 4*105), (1, 10, 4*105), (95, 13, 24*105), (8/5, 0, 2*105), (36, 240, 46*105)]
noncomputable def TypeE (a b c μ : ℝ) : Prop := 0 ≤ a * μ - b - c * Real.logb 2 (105 * μ)
noncomputable def v0 (a b c : ℝ) : ℝ := (c + Real.sqrt (c ^ 2 + a * (b + c * Real.logb 2 105))) / a
end EG.COLTable
```

**hazards:**

- **[risk] TAB-NO-OWNER.** The table label is in no chunk list, yet s1:condG1(f), s3:lemCOLJV, s3:lemCOLJVev and s7:lemGammaSat all refer to it. It must be ONE Defs constant (proposed here, EG.COLTable.col3), locked together with Gamma1; otherwise G1(f) and COLJVev(iii) could refer to different formulas and s7:lemGammaSat would prove the wrong eventuality. msreport should list s3:tabCOLJV as a node (ms_deps already has it as a declared dep of COLJVev).
- **[risk] TAB-COL2-INFORMAL.** Column 2 is informal ('T16* failures over I_JS(Y) sum to at most |V(Y)|^-2/4', 'own devices', 'Lemma 15+, lent level' — the two other levels of row 3 appear only in the proof). s3:lemCOLJV(ii) must assert the precise inequalities C1-C13 listed in the statement; in particular row 3 must include ALL three levels (s_Y >= 80 L_Y; s_r/8 >= 40 k_own L_Y for light Y; s_Y/4 >= 40 k_lend L_Y), else s3:lemCOL(a) and s5:lemE1(b) lack hypotheses. Rows 1 and 12 duplicate s2:lemTower(c),(b): keep one source.
- **[note] TAB-DECIMALS.** Exponents 102.5, 42.1, 64.4, 3.3, 1.6, 1/2 and triples 0.5, 42.1, 64.4, 0.3, 1.6 must be exact rationals (205/2, 421/10, 322/5, 33/10, 8/5, 1/2, 3/10) and real powers Real.rpow of λ = 2^μ > 0. The s1 blueprint writes G1(c) as '2*105*logb 2 (105*μ) <= 1.6*μ' — use 8/5 there too (row 12 = G1(c) after taking log2).
- **[note] TAB-COUNT.** 18 column-3 inequalities: two in row 1 (strict main form + crude form), five in row 8, one elsewhere — as G1(f) says. Row 13 is G* (G1(e)) and row 12 is G1(c) (after log2).
- **[note] TAB-COL4-NOT-ASSERTED.** Column-4 triples define cruder inequalities that are NOT part of G1 and need not hold at a given μ >= log log D_*; only s3:lemCOLJVev may use them.

**effort:** ~120 new Lean lines, difficulty 1/5 (Definitions ~70; simp/unfold lemmas and a 'row i μ at μ = log2 λ' rewriting kit ~50.)

### `s3:lemCOLJV` — lemma: the COL-JV table (RT2-I10) (s3.tex:1179)

- **Manuscript referee status:** x2 (table recomputed three times independently); rows 4, 7 changed by CR1-PV: x1; R6: one clean-room AI review (G0, 2026-09-26); (ii) restated at every μ >= loglog D_* in v6 (integration): one clean-room AI review (G0)
- **Formalization:** Spec EG/Spec/Lend/COLJV.lean (COLJVStatement: per-ancestor part (i), rows 3-10 in precise column-2 form; COLJVRoundStatement: rows 1, 2, 11, 12, 13 and col3 at λ_r, λ_{l-2}) + proof EG/Proof/Lend/COLJV.lean with the standing bounds (B1)-(B7) as Lib lemmas (EG/Lib/Lend/Standing.lean), shared with s3:lemCOL.

**Statement (precise restatement).** Assume G1 (D_* > 2 and items (a)-(f) for every real μ >= log2 log2 D_*). Let (G, D_*, run) be a valid run, Y an ancestor of round r <= R, λ := λ_r, μ := log2 λ; if r <= R-2, M := M_{r+2}. (i) If r >= R-1 then k_lend(Y) = 0. If r <= R-2: |I_U(Y)| <= 12 L_Y^3, |I_JS(Y)| <= (4/3)M^2, |I_JV(Y)| = R - r - 1 <= 2 log* d_r + 1; hence k_lend(Y) <= 12L_Y^3 + (4/3)M^2 + 2log* d_r + 2 <= 24 L_Y^3 + (4/3)M^2 <= k̄(μ) <= λ^3.3 and p_Y >= λ^-4. (The JV family is not bounded by an absolute constant; '+16' must not be used.) (ii) Every column-2 requirement and every column-3 inequality of the table holds (column 4 excluded): column 3 at every μ >= log2 log2 D_* by G1(f), in particular at μ = log2 λ_r and, for rows 2, 11, 12, at μ = log2 λ_{l-2} (3 <= l <= R); at the λ of the caption column 3 implies column 2 (row 4 together with row 9). Scope: rows 1, 3, 8 for every r <= R (row 1 for every round-r pre-part; rows 3, 8 for every ancestor of round r; the lent level of row 3 void for r >= R-1); rows 4-7 and 10 for r <= R-2; row 9 for every r (trivial if k_lend = 0); rows 2, 11, 12 for 3 <= l <= R; row 13 = G*. Precise column-2 forms: see s3:tabCOLJV (C1-C13). Proof: standing bounds (B1) L_Y <= log M_r <= 2λ; (B2) M_l <= M <= M̄, M_{l+1} <= M_l/2, M_l <= (A log λ_{l-2})^{2A}; (B3) s_r >= λ^100, s_r <= 2Λ_r^100, s_Y >= s_r/2; (B4) |V(Y)| >= P_r/2 >= λ^103/2; (B5) R - r <= 2log* d_r + 2 <= μ; (B6) Λ_r <= λ + 6μ + 20; (B7) t^JS_l <= 3M, ρ_l^-1 <= M^4; then row-by-row monotone substitution.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| G1 (Gamma1) | D_* > 2 ∧ ∀ μ >= log2 log2 D_*, items (a)-(e) ∧ col3 μ | s1:condGamma | no: EG.Gamma1 (s1 blueprint) with item (f) = EG.COLTable.col3 |
| run quantities d_r, λ_r, Λ_r = log2 M_r, M_l, P_l, s_r, τ_r, θ^GC_r, R, log* | s2:defHBtp (R0)-(R2), (GC); log* from Found.Log | s2:defHBtp, s2:lemTower | no: s2a blueprint (EG.HB.Run.*, lamOf, MOf, sOf, POf, tauOf, thetaGC); logStar (Found.Log) |
| ancestor data V(Y), s_Y, L_Y, isLight | s2:defAncestors | s2:defAncestors | no: s2a blueprint |
| I_U, I_JS, I_JV, k_lend, p_Y, t_Y, t^JS_l, ρ_l, k_own | s3:defCOL | s3:defCOL | no: EG.Lend.* (this chunk) |
| table constants and rows; column-2 predicates | EG.COLTable.*; EG.Lend.COLReq3..COLReq10 (C3-C10) | s3:tabCOLJV | no: this chunk |

**deps_declared** (manuscript \deps): s1:condG1, s1:condGstar, s2:lemTower, s3:defCOL, s2:defAncestors, s2:propStructure, s3:lemL15p, s3:thmT16s

**deps_from_proof:** s1:condG1, s1:condGstar, s2:lemTower, s2:propStructure, s2:defAncestors, s2:defHBtp, s3:defCOL, s3:tabCOLJV

**deps_notes:** s2:lemTower: (a) λ_r >= λ_{l-2} and R - r <= 2log* d_r + 2; (b) M_r <= d_r^2, L_Y <= log M_r <= 2λ_r, λ^100 <= s_r <= 2Λ^100, M_l <= (A log λ_{l-2})^{2A} <= λ_{l-2}^1.6, P_{l-2} >= M_l^13, M_{l-1} >= 2M_l; (c) τ_r <= 2^111 λ^102 (row 1 crude); (d) 2^{2log* d_r+2} <= λ_r. s2:propStructure(iv): |Y| >= |Y^0|/2 >= P_r/2 (B4). s2:defHBtp (undeclared): definitions of τ_r, θ^GC, M_r, Λ_r, P_r. s3:lemL15p and s3:thmT16s are referenced only to FORMULATE rows 3-7 (their hypotheses and failure bounds), not used as results. s3:lemCOLJVev is a forward reference in the caption (no dependence). s3:tabCOLJV undeclared.

**used_by:** s3:lemCOL (standing bounds; rows 2-9); s5:lemE1 (b) (row 3; (i) k_lend <= λ^3.3); s5:lemParent (row 12 via lemTower); s5:lemDemoted (row 8(c)); s6:thmMIXC (row 8(a) via lemCOL(e)); s7:lemCand (row 10 p_Y >= λ^-4; row 11 H^cd_l >= 2^10 M_l^10); s7:lemWellDef (row 11); s1:condG2 (b),(c) (remark)

**randomness:** none (deterministic).

**lean_shape:**

```lean
-- EG/Spec/Lend/COLJV.lean   (Y = (r, a); N := |V(Y)|, L := L_Y, λ := λ_r, μ := log2 λ, M := M_{r+2})
def EG.Spec.COLJVStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (Dstar : ℝ) (run : EG.HB.Run V),
    EG.Gamma1 Dstar → run.Valid G Dstar →      -- (+ EG.N0 ≤ G.card if s2:propStructure keeps it: COLJV-N0-IMPLICIT)
    ∀ Y ∈ run.ancestorSet G,
      (run.R ≤ Y.1 + 1 → EG.Lend.klend run G Y = 0) ∧
      (Y.1 + 2 ≤ run.R →
         ((EG.Lend.IU run G Y).card : ℝ) ≤ 12 * run.LY G Y.1 Y.2 ^ 3 ∧
         ((EG.Lend.IJS run G Y).card : ℝ) ≤ 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 ∧
         (EG.Lend.IJV run G Y).card = run.R - Y.1 - 1 ∧
         run.R - Y.1 - 1 ≤ 2 * EG.logStar (run.d G Y.1) + 1 ∧
         (EG.Lend.klend run G Y : ℝ) ≤ 24 * run.LY G Y.1 Y.2 ^ 3 + 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 ∧
         24 * run.LY G Y.1 Y.2 ^ 3 + 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 ≤ EG.COLTable.kbar (Real.logb 2 (run.lam G Y.1)) ∧
         run.lam G Y.1 ^ (-4 : ℝ) ≤ EG.Lend.pY run G Y) ∧
      (EG.Lend.klend run G Y : ℝ) ≤ run.lam G Y.1 ^ (33 / 10 : ℝ) ∧            -- row 9
      EG.COLTable.col3 (Real.logb 2 (run.lam G Y.1)) ∧                       -- column 3 at μ_r
      EG.Lend.COLReq3 run G Y ∧ EG.Lend.COLReq8 run G Y ∧                    -- C3 (three levels), C8 (five)
      (Y.1 + 2 ≤ run.R → EG.Lend.COLReq5 run G Y ∧ EG.Lend.COLReq6 run G Y ∧
         (run.isLight G Y.1 Y.2 → EG.Lend.COLReq4 run G Y ∧ EG.Lend.COLReq7 run G Y))
def EG.Spec.COLJVRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (Dstar : ℝ) (run : EG.HB.Run V),
    EG.Gamma1 Dstar → run.Valid G Dstar →
    (∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r,
        (EG.HB.tauOf (run.d G r) : ℝ) < EG.HB.thetaGC (run.d G r) (run.Z0 G r a).card) ∧            -- C1
    (∀ l ∈ Finset.Icc 3 run.R,
        (run.M G l) ^ 13 ≤ EG.HB.POf (run.d G (l - 2)) ∧                                              -- C2
        2 ^ 10 * (run.M G l : ℝ) ^ 10 ≤ run.lam G (l - 2) ^ 95 / (8 * (run.M G l : ℝ) ^ 2) ∧            -- C11
        (run.M G l : ℝ) ≤ run.lam G (l - 2) ^ (8 / 5 : ℝ) ∧                                           -- C12
        EG.COLTable.col3 (Real.logb 2 (run.lam G (l - 2))))
-- COLReq4 run G Y := 2^135 * tY * L^28 * (12 * L^5)^5 ≤ ancS / (8 * klend)
-- COLReq6 run G Y := ∑ i ∈ IJS, 2^86 * tauJS l(i) * L^19 * rhoJS l(i)⁻¹ ^ 3 * N^(-3:ℤ) ≤ N^(-2:ℤ) / 4   (etc., C3-C10)
```

**hazards:**

- **[risk] COLJV-N0-IMPLICIT.** The proof uses s2:propStructure ((B4) via (iv); H_Y's parameters) and s2:lemTower, whose proof uses propStructure; propStructure is stated only 'for every valid run on G with n >= N_0 and d_1 >= D_*'. lemCOLJV (and lemCOL) assume only G1. The written proof of propStructure does not appear to use n >= N_0, so either the s2 Spec of propStructure (and lemTower) drops n >= N_0 (preferred; verify lemCap/lem14tau), or every COL Spec adds N_0 <= |V(G)| (all consumers have it, e.g. s6:consOrder). d_1 >= D_* is automatic once an ancestor exists (R >= 1). Decide in P2-D with a bundled run context.
- **[risk] COLJV-COL2-PRECISION.** (= TAB-COL2-INFORMAL.) The Lean (ii) must state the column-2 requirements in exactly the form lemCOL and s5/s7 apply them (C1-C13). Rows 4-7 carry the T16*/L15p hypotheses and failure sums: e.g. row 5 dominates T16*'s hypothesis for every l ∈ [r+2, R] only via t^JS_l <= 3M and ρ_l^-5 = M_l^20 <= M^20, which lemCOL(b) must then re-derive — better to state row 5 per l in the Spec.
- **[risk] COLJV-UNREVIEWED.** (ii) restated in v6 (R6 + integration), one AI review. Every row re-derived here: row 1 (τ_r <= 128 s_r Λ^2 + 1 <= 257Λ^102, θ^GC >= λ^102.5, (B6)); row 3 (λ^100/8 >= 80λk̄ ⇔ λ^99 >= 640k̄; other levels λ^100/2 >= 160λ, λ^100/8 >= 160λ^2); row 4 (2^135·2λ^1.6·(2λ)^28·12^5(2λ)^25 = 2^189·12^5 λ^54.6, s >= λ^100/(16k̄) ⇒ need λ^45.4 >= 2^193 12^5 k̄ ⇐ row 4 col 3 + row 9); row 5 (λ^100 >= 3·2^167 k̄ M̄^21 λ^28); row 6 (2^107 λ^19 M^15 N^-3 <= N^-2/4 ⇐ λ^84 >= 2^110 M̄^15 with N >= λ^103/2); row 7 (12^4 2^124 λ^38.6 N^-3); row 8 (a)-(d) incl. s' >= λ^99/32; rows 9-13; (i) (4(L^2+1)L <= 12L^3, geometric sum (4/3)M^2, 2log* d_r + 2 <= μ <= 12L^3, 24(2λ)^3 = 192λ^3). No error found.
- **[note] COLJV-B6-CEILING.** (B6) Λ_r <= λ + 6μ + 20 is derived for the real M_r of (R2) (log T = λ + 2μ <= 2λ, log log T <= μ + 1). If M_l becomes an integer ceiling (COL-M-INTEGER), log2⌈x⌉ <= log2 x + 2^-39 for x >= 2^40, absorbed by the slack in 4 log2(λ + 2μ) <= 4(μ + 1) (since λ + 2μ <= 1.01λ); the Lean proof must include this.
- **[note] COLJV-GAMMA-TRANSFER.** Needs the s1 transfer lemma 'Gamma1 D → D <= d → items hold at μ = log2 log2 d' (s1 GAM-RAY) with λ_r = log2 d_r > 0 and μ_r = log2 λ_r >= log2 log2 D_* (monotonicity of logb for d_r >= D_* > 2); also at λ_{l-2} (l - 2 >= 1 is a round).
- **[note] COLJV-RPOW.** λ^3.3, λ^1.6, λ^-4, λ^102.5, λ^42.1, λ^64.4 are Real.rpow; identities λ^a = 2^(aμ) via Real.rpow_logb / rpow_mul (λ > 0). A small shared 'λ-power' Lib (also for COLJVev) avoids repeated rewriting.
- **[note] COLJV-ROW-SCOPE.** Rows 1, 3, 8 hold for r ∈ {R-1, R} too. Row 8's inequalities are proved for all ancestors (they use only s_r and L_Y <= 2λ); (a),(b) are consumed only for standalone Y, (c),(d) only for light Y; k_own must be defined for every Y (COL-EMPTY-INDEX).
- **[note] COLJV-JV-COUNT.** RT2-I10: |I_JV| = R - r - 1 <= 2log* d_r + 1 (not an absolute constant); the display's '+2' is a harmless weakening. log* must be the Found.Log definition used by s2:lemTower(a),(d).
- **[note] COLJV-B2.** (B2) needs M_{l+1} <= M_l/2 (lemTower(b): M_{l-1} >= 2M_l) and M = M_{r+2} <= M̄(μ_r) (lemTower(b) at l = r + 2 >= 3, r >= 1). |I_JS| = Σ_{l=r+2}^R M_l^2 <= M^2 Σ 4^-i = (4/3)M^2: a geometric-sum Lib lemma over Finset.Icc.
- **[note] COLJV-DEPS.** Declared s3:lemL15p, s3:thmT16s are not logical dependencies (formulation only); s3:lemCOLJVev is a forward ref in the caption; s2:defHBtp and s3:tabCOLJV are undeclared.

**effort:** ~750 new Lean lines, difficulty 3/5 (Standing bounds (B1)-(B7) ~220 (given the s2 API); (i) counting ~150; column 2 from column 3, rows 1-13, with rpow algebra ~330; Specs ~50.)

### `s3:lemCOLJVev` — lemma: eventual form of the COL-JV table (s3.tex:1344)

- **Manuscript referee status:** new; R6: one clean-room AI review (G0, 2026-09-26)
- **Formalization:** Spec EG/Spec/Lend/COLJVev.lean (COLJVevStatement) + proof EG/Proof/Lend/COLJVev.lean. Pure real analysis on the definitions of EG/Defs/Lend/COLTable.lean.

**Statement (precise restatement).** A := 105, log = log2. An inequality in the real variable μ is of type (E) if it reads aμ - b - c log(Aμ) >= 0 with reals a > 0, b, c >= 0. (i) A type-(E) inequality holds for every μ >= max{1, v_0^2}, where v_0 := (c + (c^2 + a(b + c log A))^(1/2))/a. (ii) Let μ >= 6 be real, λ := 2^μ, M̄ := (Aμ)^{2A}, k̄ := 192λ^3 + (4/3)M̄^2; let 1 <= i <= 13 and (a_i, b_i, c_i) the column-4 triple of row i. If a_iμ - b_i - c_i log(Aμ) >= 0 then every column-3 inequality of row i holds at λ. (iii) Consequently, for each row, every column-3 inequality holds at λ = 2^μ for all sufficiently large real μ (explicit threshold max{6, v_0^2}, never evaluated). No hypothesis; no graph, run or condition on D_*.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| table rows, triples, TypeE, v0, M̄, k̄ | see s3:tabCOLJV | s3:tabCOLJV | no: EG.COLTable.* (this chunk) |
| log2, sqrt, rpow, eventually atTop | Real.logb 2, Real.sqrt, Real.rpow, Filter.Eventually _ Filter.atTop | Mathlib | yes (Mathlib) |

**deps_declared** (manuscript \deps): s3:tabCOLJV

**deps_from_proof:** s3:tabCOLJV

**deps_notes:** Only the definitions of the table. Elementary facts: 2^v >= 1 + v for v >= 1 (so log2 v < v), the quadratic root, 6μ + 20 <= 2^μ for μ >= 6, log2 257 < 9, log2 640 < 10, 5 log2 12 < 18, 4 log2 12 < 15, log2 3 < 2, x + y <= 2xy for x, y >= 1.

**used_by:** s7:lemGammaSat ((i) for G1 items (a)-(e); (iii) for item (f)); s3:tabCOLJV caption / s3:lemCOLJV (commentary only)

**randomness:** none.

**lean_shape:**

```lean
-- EG/Spec/Lend/COLJVev.lean
def EG.Spec.COLJVevStatement : Prop :=
  (∀ a b c μ : ℝ, 0 < a → 0 ≤ b → 0 ≤ c → max 1 (EG.COLTable.v0 a b c ^ 2) ≤ μ → EG.COLTable.TypeE a b c μ) ∧
  (∀ μ : ℝ, 6 ≤ μ → ∀ i : Fin 13,
      EG.COLTable.TypeE (EG.COLTable.triple i).1 (EG.COLTable.triple i).2.1 (EG.COLTable.triple i).2.2 μ →
      EG.COLTable.row i μ) ∧
  (∀ i : Fin 13, ∀ᶠ μ in Filter.atTop, EG.COLTable.row i μ) ∧
  (∀ᶠ μ in Filter.atTop, EG.COLTable.col3 μ)
```

**hazards:**

- **[note] EV-GAMMASAT-SHAPE.** s7:lemGammaSat needs: for all sufficiently large D_*, (f) holds on the WHOLE ray μ >= log2 log2 D_*. This follows from (iii) as ∃ μ_0 ∀ μ >= μ_0 (Filter.eventually_atTop) plus log2 log2 D → ∞. State (iii) with ∀ᶠ in atTop (or ∃ μ₀); the conjunction over the 13 rows is Filter.eventually_all over Fin 13.
- **[note] EV-ROW1.** Row 1 is strict: the proof gives φ >= (0.5μ - 112) + 1 > 0. It needs 6μ + 20 <= 2^μ for REAL μ >= 6 (manuscript: derivative argument). Lean route: 2^μ >= 2^⌊μ⌋ and 2^k >= 6k + 26 for integers k >= 6 (tight at k = 6: 64 >= 62), or convexity of rpow. Crude form μ > 222 from 0.5μ >= 112.
- **[note] EV-LOG-CONSTANTS.** log2 257 < 9, log2 640 < 10, 5 log2 12 < 18, 4 log2 12 < 15, log2 3 < 2: rewrite as 257 < 2^9 etc. via Real.logb_lt_iff_lt_rpow and norm_num. k̄ <= 2^9 λ^3 M̄^2 uses x + y <= 2xy for x, y >= 1 (λ >= 1, Aμ >= 1).
- **[note] EV-I-PROOF.** (i) uses log2 v < v for v >= 1 (from 2^v >= 1 + v; Mathlib: Real.add_one_le_exp or Bernoulli for rpow) and the quadratic in v = sqrt μ with Real.sqrt; v_0 is well defined since c^2 + a(b + c log2 105) >= 0. ~80 lines.
- **[note] EV-TRIPLES-EXACT.** Triples copied exactly (s3:tabCOLJV); each row's φ lower bound re-derived: 1: 0.5μ - 111; 2: 103μ - 26A log; 3: 96μ - 19 - 4A log; 4: 42.1μ - 211; 5: 69μ - 178 - 46A log; 6: 84μ - 110 - 30A log; 7: 64.4μ - 142; 8: E := 58μ - 194 - log(Aμ) with the five differences (E, E + 4μ + 7, E + 4μ + 3, >= E, 93μ - 13 > 0); 9: 0.3μ - 9 - 4A log; 10: μ - 10 - 4A log; 11: 95μ - 13 - 24A log; 12: 1.6μ - 2A log; 13: 36μ - 240 - 46A log. All correct.
- **[note] EV-NOT-G1.** Type-(E) inequalities are not part of G1 and may fail at some μ >= loglog D_* although G1 holds; no Spec may use them as hypotheses (only COLJVev and s7:lemGammaSat).

**effort:** ~450 new Lean lines, difficulty 2/5 ((i) ~80; shared bounds (log k̄, log M̄, 6μ+20 <= 2^μ, log constants) ~100; 13 rows ~20 each ~260; (iii) ~20.)

### `s3:lemCOL` — lemma: Lemma COL (s3.tex:1440)

- **Manuscript referee status:** x2; (c) changed by CR1-PV: x1; step (b) (ρ_l N >= L^2) changed in v6 (integration, R6): one clean-room AI review (G0, 2026-09-26)
- **Formalization:** Event predicates EG.Lend.{COLa, COLb, COLc, COLe, COLg} in EG/Defs/Lend/COL.lean (they are read by s5:defStages and s6:defLending) + Spec EG/Spec/Lend/COL.lean (COLStatement) + proof EG/Proof/Lend/COL.lean (stage alpha through T16*).

**Statement (precise restatement).** Assume G1. Let (G, D_*, run) be a valid run and Y an ancestor of round r with the stage-1 lending data of s3:defCOL; N := |V(Y)|, L := L_Y, k := k_lend(Y), λ := λ_r. If r >= R-1 then k = 0 and every statement about lent classes is vacuous. (a) Own_Y and Lend_Y are (ε_Y, s_Y/4)-expanders on V(Y); every lent class (graph on V(Y)) is an (ε_Y, s_Y/(8k))-expander; if Y is light, every own class R_{j,c}, M (graph on V(Y)) is a (2^-6, s_r/(16k_own))-expander. (b) For all r+2 <= l <= R and 0 <= j < K^JS_l: LJS_{Y,l,j} is (2^12 L^4, t^JS_l)-path connected through T_j(Y,l) (hence, by Monotone(iii), joint routing of any union multiset with multiplicities <= t^JS_l). (c) Let Y be light. Let (V_{l,c,σ})_{(l,c,σ) ∈ I_U(Y)} be random subsets of V(Y), (jointly) independent of the stage-1 lending data of Y, each a ρ_{l,c,σ}-random subset of V(Y) with (deterministic) ρ_{l,c,σ} >= 1/(12L^5); arbitrary dependence across indices. Then with probability >= 1 - N^-2/2 over the lending data and the sets, every LU_{Y,l,c,σ} is (2^12 L^4, t_Y)-path connected through V_{l,c,σ}, t_Y = ⌈λ_r^1.6⌉. (e) Deterministic thresholds: standalone Y: s_Y/4 >= 2^150 L^42 and s_Y/4 >= 2^146 L^38 log L (so on (a) Own_Y is a spanning (2^-5, s_r/4)-expander meeting the TPV and VX+ thresholds; the VX+ one is not used); light Y: s_r/2 >= 2^151 L^38 log L (VX+ threshold at 2^-6 on H_Y = X_Y, a (2^-6, s_r/2)-expander), and s' := s_r/(16k_own) >= 2^145 L^41 and 2⌈L^6⌉ <= s' (own classes on (a)). (g) Always: the own classes partition Own_Y; if r <= R-2 the lent classes are pairwise edge-disjoint and partition Lend_Y; if r >= R-1, Lend_Y has no classes and is all junk. (Consumer exclusivity: design rule.) Probabilities: (a), (b), (e) hold simultaneously with probability >= 1 - N^-2/2 over the lending data of Y; for every family as in (c), (a), (b), (c), (e) hold simultaneously with probability >= 1 - N^-2. Proof accounting: P(¬a) <= 2(2 + k + k_own)N^-5 <= N^-2/4; P(a ∧ ¬b) <= N^-2/4 (row 6); P(a ∧ ¬c) <= N^-2/4 (row 7).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| stage-1 lending data and its law; classes; T_j(Y,l) | s3:defCOL | s3:defCOL | no: EG.Lend.* (this chunk) |
| H_Y spanning (ε_Y, s_Y)-expander on V(Y) | propStructure(i); H_Y.verts = V(Y) | s2:propStructure, s2:defAncestors | no: s2 API |
| expander, path connectivity | Def 11, Def 7 | s1:citDef11, s1:citDef7 | yes: IsExpander, IsPathConnected |
| rho-random subset, independence | IsRSubset; IndepFun (joint) | s3 conventions | yes: EG.FinDist.IsRSubset, IndepFun, IsRSubset.cond_of_indepFun |
| event predicates COLa/COLb/COLc/COLe/COLg | (a), (b), (c), (e), (g) as predicates of an outcome ω : COLOut Y (and of the set family for COLc) | s3:lemCOL; used by s5:defStages, s6:defLending | no: new EG.Lend.COLa etc. |

**deps_declared** (manuscript \deps): s3:defCOL, s3:lemL15p, s3:thmT16s, s3:lemMonotone, s3:lemCOLJV, s2:lemTower, s2:propStructure, s2:defAncestors, s1:condG1

**deps_from_proof:** s3:defCOL, s3:lemL15p, s3:thmT16s, s3:lemMonotone, s3:lemCOLJV, s3:tabCOLJV, s2:lemTower, s2:propStructure, s2:defAncestors, s1:condG1

**deps_notes:** Exact up to s3:tabCOLJV (the rows are cited by number). Rows used: 2 (ρ_l N >= L^2 at λ_r), 3 (all three L15p levels), 4 (with 9), 5, 6, 7, 8 ((e)), 9 (k <= λ^3.3). Standing bounds (B1)-(B7) are taken from the proof of lemCOLJV (should be Lib lemmas). s2:propStructure(i) (H_Y an (ε_Y, s_Y)-expander on V(Y)); s2:lemTower(b) (s_r >= λ^100, L <= 2λ). Monotone(iii) only for the last sentence of (b). s1:condG1 via COLJV.

**used_by:** s5:defStages ('demoted' uses the COL(a) events); s5:lemE1 ((b) re-derives the COL(a) failure bound from inside this proof; (c) applies COL(c) with the zones); s5:lemChild ((a): own classes); s6:defLending (lend-bad: a COL(a) or COL(b) event fails); s6:lemLost (P(lend-bad) via (a),(b)); s6:lemJSLC (d) ((b) path connectivity of LJS through T_j); s6:thmMIXC ((a), (e) for O_Z = Own_Z); s1:condG2 (c) (remark); s7:lemGammaSat (remark)

**randomness:** (a), (b), (e): over the stage-1 lending data of Y only — law colLaw Y (s3:defCOL); the Spec quantifies over any finite (Ω, μ) and D : Ω → COLOut Y with μ.map D = colLaw Y (so it applies on the global stage-1 space). (c): over a joint space (Ω, μ) carrying D (law colLaw Y) and the family Vs : Ω → (LentTag → Finset V) with IndepFun μ D Vs (the whole family independent of the whole lending data of Y) and each Vs_i ρ_i-random in V(Y). Conditioning in the proof: on the split bits (stage (ii) and (iii) are uniform colourings of Lend_Y resp. Own_Y given the bits; L15p applied slice-wise on the event 'Lend_Y (Own_Y) is an expander'); on the whole colouring (T_j(Y,l) and V_{l,c,σ} stay ρ-random: labels / sets independent of the colouring; T16* applied to the fixed class).

**lean_shape:**

```lean
-- EG/Defs/Lend/COL.lean (event predicates; ω : COLOut run G Y, Y = (r, a))
def EG.Lend.COLa (run G Y) (ω) : Prop :=
  (Own ω).IsExpander (run.ancEps G Y.1 Y.2) (run.ancS G Y.1 Y.2 / 4) ∧ (Lend ω).IsExpander (run.ancEps ..) (run.ancS .. / 4) ∧
  (∀ i ∈ lentIdx run G Y, (lentClass ω i).IsExpander (run.ancEps ..) (run.ancS .. / (8 * klend run G Y))) ∧
  (run.isLight G Y.1 Y.2 → ∀ o, (ownClass ω o).IsExpander (2 ^ (-6 : ℤ)) (EG.HB.sOf (run.d G Y.1) / (16 * kown run G Y)))
def EG.Lend.COLb (run G Y) (ω) : Prop := ∀ l ∈ Finset.Icc (Y.1 + 2) run.R, ∀ j < KJS run G l,
  (lentClass ω (.JS l j)).IsPathConnected (2 ^ 12 * run.LY G Y.1 Y.2 ^ 4) (tauJS run G l) (T ω l j)
def EG.Lend.COLc (run G Y) (ω) (Vs : LentTag → Finset V) : Prop := ∀ i ∈ IU run G Y,
  (lentClass ω i).IsPathConnected (2 ^ 12 * run.LY G Y.1 Y.2 ^ 4) (tY run G Y) (Vs i)
def EG.Lend.COLe (run G Y) : Prop := ...   -- the row-8 inequalities by type (deterministic)
def EG.Lend.COLg (run G Y) (ω) : Prop := ... -- partition facts
-- EG/Spec/Lend/COL.lean
def EG.Spec.COLStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (Dstar : ℝ) (run : EG.HB.Run V),
    EG.Gamma1 Dstar → run.Valid G Dstar →          -- (+ N0 ≤ G.card: COL-N0-IMPLICIT)
    ∀ Y ∈ run.ancestorSet G,
      let N : ℝ := (run.ancVerts G Y.1 Y.2).card; let L := run.LY G Y.1 Y.2
      EG.Lend.COLe run G Y ∧ (∀ ω, EG.Lend.COLg run G Y ω) ∧
      (∀ (Ω : Type u) (μ : EG.FinDist Ω) (D : Ω → EG.Lend.COLOut run G Y), μ.map D = EG.Lend.colLaw run G Y →
         μ.prob {ω | ¬ EG.Lend.COLa run G Y (D ω)} ≤
           2 * (2 + EG.Lend.klend run G Y + EG.Lend.kown run G Y) * N ^ (-5 : ℤ) ∧          -- exported for s5:lemE1(b)
         1 - N ^ (-2 : ℤ) / 2 ≤ μ.prob {ω | EG.Lend.COLa run G Y (D ω) ∧ EG.Lend.COLb run G Y (D ω)}) ∧
      (run.isLight G Y.1 Y.2 →
       ∀ (Ω : Type u) (μ : EG.FinDist Ω) (D : Ω → EG.Lend.COLOut run G Y)
         (Vs : Ω → EG.Lend.LentTag → Finset V) (ρ : EG.Lend.LentTag → ℝ),
         μ.map D = EG.Lend.colLaw run G Y → μ.IndepFun D Vs →
         (∀ i ∈ EG.Lend.IU run G Y, 1 / (12 * L ^ 5) ≤ ρ i ∧ μ.IsRSubset (fun ω => Vs ω i) (run.ancVerts G Y.1 Y.2) (ρ i)) →
         1 - N ^ (-2 : ℤ) / 2 ≤ μ.prob {ω | EG.Lend.COLc run G Y (D ω) (Vs ω)} ∧
         1 - N ^ (-2 : ℤ) ≤ μ.prob {ω | EG.Lend.COLa run G Y (D ω) ∧ EG.Lend.COLb run G Y (D ω) ∧
                                         EG.Lend.COLc run G Y (D ω) (Vs ω)})
theorem EG.lemCOL (hHax : EG.Spec.HaxellStatement.{u}) (hP8 : EG.Spec.BMProp8Statement.{u}) : EG.Spec.COLStatement.{u}
```

**hazards:**

- **[risk] COL-CONDITIONAL-L15.** (a)'s second and third L15p applications are CONDITIONAL on the Own/Lend split: 'Condition on stage (i) with Lend_Y such an expander. Stage (ii) is then a uniform k-colouring of Lend_Y'. In Lean: for each bit vector β with Lend(β) (resp. Own(β)) an expander, the restricted index (own) labels have law randColouring ↥(Lend β).edges k (Fin kown) up to ↥lentIdx ≃ Fin k (COL-RANDOM-EDGESET), L15p slice-wise, and P(¬a) <= P(split bad) + Σ_β P(bits = β)·P(classes bad | β) <= 4N^-5 + 2kN^-5 + 2k_own N^-5. ~250 lines; mathematically fine.
- **[risk] COL-CONDITIONAL-T16.** (b), (c) apply T16* to a class that is an expander only on (a), conditionally on the colouring: needs 'T_j(Y,l) (labels) resp. Vs_i independent of the colouring ⇒ still ρ-random under the conditional law given the colouring' (IsRSubset.cond_of_indepFun exists) and P(a ∧ ¬b) <= max over colourings c ∈ (a) of P(¬b | c). For (c) the hypothesis must be JOINT independence IndepFun μ D Vs (conditioning on the colouring, a function of D, needs the whole family independent of D — per-index independence is not enough); the consumer s5:lemE1(c) must prove this joint form for the zones (functions of the choices/sublabels, an independent stage-1 factor: s5:lemZones(iv)).
- **[risk] COL-N0-IMPLICIT.** (= COLJV-N0-IMPLICIT.) s2:propStructure(i) (H_Y an (ε_Y, s_Y)-expander with H_Y.verts = V(Y)) and (iv) are stated under n >= N_0 and d_1 >= D_*; lemCOL assumes only G1. Decide globally (drop N_0 from propStructure, or add it to every COL Spec).
- **[note] COL-EXPORT-A-BOUND.** s5:lemE1(b) re-derives P(COL(a) fails) <= 2(2 + k_lend + k_own)|Y|^-5 by re-entering the PROOF of lemCOL ('COL(a) is the conclusion of three applications of Lemma 15+ in the proof of Lemma COL'). The COL Spec should export this bound (as in lean_shape), so s5 does not duplicate the conditional-L15 plumbing. s6:defLending likewise needs COL(a), COL(b) as named predicates (COLa, COLb).
- **[note] COL-EVENT-NAMES.** s5:defStages lists COL(a) for light Y as: Own_Y, Lend_Y (2^-6, s_r/8)-expanders, lent classes (2^-6, s_r/(16k)), own classes (2^-6, s_r/(16k_own)). COLa is defined with ε_Y, s_Y and must unfold to exactly this for light Y (ε_Y = 2^-6, s_Y = s_r/2 real) and to (2^-5, s_r/4), (2^-5, s_r/(8k)) for standalone Y (s6:thmMIXC uses Own_Z (2^-5, s_l/4)). 'On V(Y)' = spanning: colourClass keeps H_Y.verts = V(Y).
- **[note] COL-E-DETERMINISTIC.** (e) is deterministic (row 8) plus restatements valid 'on (a)'; COLe should contain only the inequalities (s6.tex:803 uses that they do not depend on the colouring). Row 8(b) (VX+ for standalone parts) is marked 'not used' in the working copy; keeping it is harmless.
- **[note] COL-G-MEANING.** (g) in Lean = partition facts: Own_Y, Lend_Y partition E(H_Y); own classes pairwise edge-disjoint with union Own_Y; for r <= R-2 lent classes (i ∈ lentIdx Y) pairwise edge-disjoint with union Lend_Y (every lend edge has idx = some i with i ∈ lentIdx: true on the support of idxLaw only — state COLg on the support or build idx with values in the subtype); for r >= R-1 idx = none. The consumer-exclusivity part is not a property of the data (COL-CONSUMERS-NOT-A-PROPERTY).
- **[note] COL-B-CHECK.** (b)'s T16* hypotheses re-checked: ε_Y ∈ [2^-7, 1]; s = s_Y/(8k) >= 2^135 t^JS_l L^28 ρ_l^-5 by row 5 (t^JS_l <= 3M, ρ_l^-5 = M_l^20 <= M^20); ρ_l N >= L^2 by row 2 at λ_r (M̄^13 <= λ^103 ⇒ M̄^4 <= λ^31.7) and N >= λ^103/2: ρ_l N >= λ^71/2 >= 4λ^2 >= L^2; failure sum over (l, j) ∈ I_JS(Y) <= N^-2/4 by row 6.
- **[note] COL-C-CHECK.** (c)'s T16* hypotheses re-checked: class is (2^-6, s_r/(16k)) on (a); s_r/(16k) >= 2^135 t_Y L^28 (12L^5)^5 by row 4 with row 9; ρN >= N/(12L^5) >= λ^103/(24(2λ)^5) >= L^2; failure per index <= 2^86 t_Y L^19 (12L^5)^3 N^-3, union over I_U by row 7. The ρ_{l,c,σ} must be deterministic (IsRSubset with fixed ρ); ρ <= 1 is part of IsRSubset; t_Y >= 1.
- **[note] COL-PROB-ACCOUNTING.** P(¬a) <= 2(2 + k + k_own)N^-5 <= 2(2 + λ^3.3 + 2λ)N^-5 <= N^-2/4 (k <= λ^3.3 row 9, k_own <= L <= 2λ, N^3 >= λ^309/8); P(a ∧ ¬b) <= N^-2/4; P(a ∧ ¬c) <= N^-2/4; so P(a∧b∧e) >= 1 - N^-2/2, P(c) >= 1 - N^-2/2, P(a∧b∧c∧e) >= 1 - 3N^-2/4 >= 1 - N^-2. For standalone Y there is no stage-(iii) application (over-count harmless).
- **[note] COL-JOINT-ROUTING.** (b)'s joint routing of several systems at junction j needs the multiplicity of the SUM multiset <= t^JS_l (s3a MON-JOINT-MULT); that is s6:lemJSLC's obligation, not lemCOL's.

**effort:** ~800 new Lean lines, difficulty 4/5 (Event predicates + Spec ~140; (a) three conditional L15p applications + accounting ~250; (b) conditional T16* + union ~150; (c) joint-independence conditioning + union ~150; (e), (g) ~70; numerics ~40.)

