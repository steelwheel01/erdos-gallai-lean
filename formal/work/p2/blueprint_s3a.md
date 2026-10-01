# P2-U formalization blueprint: chunk s3a (s3: monotonicity, Lemma 15^+, multisets, the T16^* parameters, Prop 13^*, Lemma 17^*, Prop 18^*/Lemma 19^*)

Manuscript: `proofs/manuscript/s3.tex` lines 1-688 (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s3a.json` (same content, one object per node, same field names as `nodes_s1.json` / `nodes_s2a.json`). Line numbers refer to `s3.tex`. Lean names that already exist were checked against `formal/EG/**` (EG.FGraph.IsExpander, IsPathConnected, EG.ball, EG.FinDist.{pi, rsubset, IsRSubset, iIndepFun, randColouring, selectSet}, Lib: IsExpander.of_le/mono/lt_deg, IsPathConnected.mono/exists_paths/exists_paths_sigma, ball_mono_*, the Chernoff family, EG.Spec.L15pStatement and its proof EG.l15p); all other names are proposals.

The chunk's labels are s3:lemMonotone, s3:lemL15p, s3:remMultiset, s3:propP13s, s3:lemL17s, s3:lemP18s. One SUPPORTING node is added: `s3:eqStar` (the parameter block (eqStar) with the facts (S1)-(S6), namedlabels s3:eqS1..s3:eqS6), because P13^*'s use, L17^*, P18^*, L9_rho and T16^* are all stated 'with the parameters of (eqStar)' and no chunk list owns it.

## 1. Summary

| label | kind | formalization | new Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s3:lemMonotone` | lemma | Lib (already proved, sorry-free, in EG/Lib/Found/Graph.lean: IsExpander.of_le, IsExpander. | 60 | 1 | note (MON-EXISTING) |
| `s3:lemL15p` | lemma | DONE: Spec EG.Spec.L15pStatement (EG/Spec/Link/L15.lean) and complete sorry-free proof EG. | 0 | 2 | risk (L15-RANDOM-EDGESET) |
| `s3:remMultiset` | remark | No Spec. The multiset reading is definitional in EG.FGraph.IsPathConnected (indexed famili | 60 | 1 | note (MS-BUILTIN) |
| `s3:eqStar` | equation block with six proved facts | Defs EG/Defs/Link/Star.lean (the parameter functions; IsWellExpanding is `EG.FGraph.IsWellExpanding` in EG/Defs/Graph.lean, not redefined here) + Spec EG/Spec/Link | 740 | 3 | risk (STAR-NO-LABEL-OWNER) |
| `s3:propP13s` | proposition | Spec EG/Spec/Link/P13s.lean (P13sStatement) + proof EG/Proof/Link/P13s.lean | 750 | 3 | risk (P13-STAR-ENCODING) |
| `s3:lemL17s` | lemma | Spec EG/Spec/Link/L17s.lean (L17sStatement, in the 'every rho-random subset' form) + proof | 1700 | 4 | risk (L17-LAYER-SPACE) |
| `s3:lemP18s` | lemma | Spec EG/Spec/Link/P18s.lean (P18sStatement with conjuncts (i), (ii)) + proof EG/Proof/Link | 700 | 3 | note (P18-THETA-PLUS-ONE) |

Estimated new Lean for this chunk: **~4010 lines** (Lemma 15^+ is already stated and proved, 416 + 106 lines, and the monotonicity lemmas already exist in EG/Lib/Found/Graph.lean; not counted; B-M Prop 12 and Lemma BBD are counted in the s1 blueprint). **No blocker** was found: every statement was re-derived (including all numerical constants) and is correct as stated, modulo the implicit hypotheses listed. The risks are infrastructure, not mathematics: the layered sample space of Lemma 17^* with prefix conditioning, the union law (S2) of independent random subsets, the transport of a rho-random set's indicator vector to the product Bernoulli space required by Lemma BBD, the encoding of 'stars' and 'bipartite subgraph' in P13^*, the missing owner of (eqStar), and (consumer-side) colourings of random edge sets in s3:lemCOL. Case (b) of Lemma 17^* (v6 R2) has no referee yet; I re-checked it and found no error.

## 2. Cross-cutting decisions proposed for the integrator

- **(eqStar) gets its own Defs file and two Specs (owned by this chunk).** `EG/Defs/Link/Star.lean`: `EG.Star.{L, ell, g, q, p, d, lam, Delta, sigma, theta, mu, sbar, M, K}` as functions of `(n : ℕ) (ε' ρ t : ℝ)` (ℕ-valued where the manuscript says 'integer'), p_* by the explicit rpow closed form. `EG.FGraph.IsWellExpanding` already exists in `EG/Defs/Graph.lean` (P2-D small); Star.lean uses it and does not redefine it. `EG/Spec/Link/Star.lean`: `StarFactsStatement` ((S1),(S3)-(S6), numeric part of (S2), the P13^* hypothesis check) and `StarUnionLawStatement` (the law part of (S2)). All s3 Specs (L17^*, P18^*, L9_rho, T16^*) must use these constants, never inline copies. msreport should treat `s3:eqStar` and `s3:eqS1..eqS6` as nodes (ms_deps currently lists none of them).
- **Random-set statements are in 'every rho-random subset' form.** L17^* and P18^*(ii) quantify over an arbitrary finite space `(Ω, μ)` and `R : Ω → Finset V` with `μ.IsRSubset R G.verts ρ` (the manuscript's final sentence of L17^*); the layered space V_1..V_ell is proof-internal. Reason: T16^* has V on a product with an independent colouring, and conditions on the colouring (IsRSubset.cond_of_indepFun). Universe: `Ω : Type u` (same as V) suffices for every current consumer.
- **Quantifier placement.** L17^*: ∀ U F, prob(bad) ≤ exp(-7|U|L) (per pair). P18^*(ii): prob(∀ U F, good) ≥ 1 - n^{-6} (quantifiers inside the event). Monotone(iii): deterministic ∀ over multisets; consumers apply it pointwise at each outcome.
- **Encodings for P13^*.** (a) centre Finset C ⊆ W + leaf map `lv : V → Finset V` (card lambda, ⊆ V(G)\W, (G-F)-adjacent, `PairwiseDisjoint` on C); (b) `X : Finset V`, `H : FGraph V` with `H ≤ G.deleteEdges F`, `H.verts = W ∪ X`, `H.edges ⊆ G.edgesBetween W X`, degree conditions via `H.deg`. Lib consequences for L17^*: `H.nbrs x ⊆ W`, `∑ w ∈ W, H.deg w = d * X.card`.
- **New probability infrastructure (EG/Lib/Prob):** (1) union law of independent random subsets (for (S2)); (2) prefix conditioning on `pi` over `Fin ℓ` (event depending on a prefix block and one further coordinate); (3) `IsRSubset.map_indicator_eq_pi` (indicator vector of a rho-random set on W ⊆ S is product Bernoulli), shared with the s1 BBD transport corollary; (4) a marginalization wrapper for events that are functions of (X, V) (Monotone(iii)). Each ~40-250 lines; (2) and (1) are the largest.
- **Greedy constructions become maximal objects.** P13^*'s greedy bipartite graph and maximal star family, and P18^*(i)'s maximal U', are formalized via `Finset.exists_max_image` / `Finset.exists_maximal`; only the maximality consequences are used (proof-level deviation, statements unchanged).
- **Constants.** All constants are small and exact (norm_num, plus Real.exp_one_gt_d9 / Real.log_two_lt_d9 / gt_d9). Thin margins: 0.00243 vs 1/412 (0.1%), 0.09/4.2 vs 1/47 (0.7%), 7/ln 2 >= 10.09 (0.09%), 2^19/28200 = 18.59 vs 18 (3%), S5 log2 margins 0.015. (S5)'s 2^83.6 / 2^130.6 should be stated as the exact rational products (T16^* compares them with 2^86, 2^135).
- **Undeclared / non-logical dependencies (for usesgen/msreport).** Attribution-only \deps: s1:citProp13 (P13^*), s1:citLem17 (L17^*), s1:citProp18 and s1:citLem19 (P18^*), s1:citLem9 (remMultiset). Genuine but undeclared: s3:eqStar/(S1)-(S6) in L17^*, P18^*, L9_rho, T16^*; s1:citDef11 in L17^* (hypothesis passed to P13^*); s3:remMultiset in s6:lemJSLC. Declared but only indirect: T16^* → P13^*, T16^* → L17^* (both only through P18^*).
- **Consumer-side decision flagged here (affects s3b, s5):** colourings of a random edge set (Lend_Y, Own_Y) must be encoded as labels on a FIXED ambient edge set, so that L15^+ (stated for `randColouring X.edges k` with X fixed) applies slice-wise (hazard L15-RANDOM-EDGESET).

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| risk | `s3:lemL15p` | L15-RANDOM-EDGESET | (Consumer-side, decides whether L15p is usable as stated.) The Spec colours the edge finset of a FIXED X (type ↥X.edges). In s3:lemCOL / s5:lemE1 the second and third colourings are applied to Lend_Y and Own_Y, which are themselves random (outputs of the first k = 2 colouring): the index type ↥(Lend_Y ω).edges depends on ω, which a single FinDist cannot have. The consumer Specs (s3b) must colour a FIXED ambient edge set (E(X_Y), or the vertex-pair set) with independent uniform labels and define the classes of Lend_Y by restriction; then L15p applies slice-wise (for each value of the first stage the restricted colouring has law randColouring (Lend_Y).edges k, via map_selectSet_randColouring / l15p_of_map_eq). This is a data-model decision for s3:defCOL (not a manuscript error); if it is not made, L15p's Spec cannot be instantiated there. |
| risk | `s3:eqStar` | STAR-NO-LABEL-OWNER | The parameter block (eqStar) and (S1)-(S6) are not a labelled environment of any chunk list, yet s3:propP13s (via its use), s3:lemL17s, s3:lemP18s, s3:lemL9rho and s3:thmT16s are stated 'with the parameters of (eqStar)'. If no one owns EG/Defs/Link/Star.lean before the s3 Specs are locked, each Spec will inline its own (possibly different) copy of p_*, Delta_*, theta_* ... Proposed: this chunk owns the Defs file and the two Specs; msreport should know the namedlabels s3:eqStar, s3:eqS1..s3:eqS6 as nodes. |
| risk | `s3:eqStar` | STAR-S2-UNIONLAW | (S2)'s last claim is new FinDist infrastructure: the union of independent layers with element probabilities p_i is an independent random subset with element probability 1 - Π(1-p_i). Nothing in EG/Lib/Prob (Named, Indep) covers unions of random sets; the proof must regroup the product over (layers × elements) into a product over elements of products over layers (pi swap / Fintype.piFinset reindexing, or via the elementwise characterization isRSubset_iff + iIndepFun of the layers). Needed by s3:lemL17s only. ~200 lines; the elementwise route through isRSubset_iff is recommended. |
| risk | `s3:propP13s` | P13-STAR-ENCODING | 'vertex-disjoint stars, each with exactly lambda leaves, centre in W, leaves in V(G)\W' and 'bipartite subgraph with sides W and X' have no EG definition; the Spec's encoding fixes what s3:lemL17s can extract. Proposed encoding (above): (a) centre Finset C ⊆ W + leaf map lv with card, inclusion, (G-F)-adjacency and PairwiseDisjoint on C (vertex-disjointness then follows because centres ∈ W and leaves ∉ W); (b) FGraph H with H ≤ G - F, V(H) = W ∪ X, E(H) ⊆ E_G(W,X). L17s needs from (a): leaves of stars with centre in V_i lie in A_i(W) and distinct centres have disjoint leaf sets (\|A_i(W)\| >= lambda·\|C ∩ V_i\|); from (b): N_H(x) ⊆ W, \|N_H(x)\| = d, Σ_{w∈W} deg_H(w) = d\|X\|, deg_H(w) <= Delta. All derivable from the proposed encoding; if H were encoded only by an edge set, or the degree of x counted in G - F instead of H, case (b) of L17s would not go through. Decide before locking. |
| risk | `s3:lemL17s` | L17-LAYER-SPACE | The proof lives on the ell_*-fold product (ell_* = ⌊2^10 L^3⌋ depends on n) and conditions twice on prefixes ('the set B_i is determined by U, F, V_1..V_{i-1}, so it is independent of V_i..V_ell' — a 'clearly' that hides the Fubini/independence argument). EG/Lib/Prob has compProd/prod slicing (prob_compProd_le_of_forall) and iIndepFun_pi_of_dependsOn, but no ready lemma for 'event depending on coordinates < i and on coordinate i of a pi over Fin ell'. Needed: (1) B_i as a function of (fun j : {j // j < i} => V_j) only (a dependsOn lemma for reach), (2) the split pi ≅ (prefix block) × (coordinate i) × (rest) at the level of laws, (3) the slice bound. Estimated 250 lines of new probability plumbing; the main technical risk of this node. |
| risk | `s3:lemL17s` | L17-BBD-TRANSPORT | (= s1 hazard BBD-TRANSPORT, instantiated here.) BBD is stated on pi (Bernoulli p_k) over a coordinate type; Z is a function of the indicator vector (1{w ∈ V_i})_{w ∈ W} of a p_*-random V_i (itself one coordinate of the layered space, after conditioning). Needed: IsRSubset V_i V(G) p and W ⊆ V(G) ⇒ law of ω ↦ (w : ↥W) ↦ decide (w ∈ V_i ω) is pi (fun _ => bernoulli p) (not in Lib; map_selectSet_pi_rsubset / isRSubset_iff go the other way), then E Z and P(Z <= E Z - a) transported by prob_map/expect_map. Also 'differ in coordinate k ⇒ \|ΔΨ\| <= deg_H(w_k)' must be proved for Ψ(y) = #{x ∈ X : ∃ w ∈ N_H(x), y_w = 1} (Function.update form). |
| risk | `s3:lemL17s` | L17-UNREVIEWED-CASE-B | Case (b) of Step 2 (BBD application) is new in v6 (R2) and has 'no referee yet' in s1:tabDAG. Re-derived here: c_k = deg_H(w_k) <= Delta_* = b; Σ p(1-p)c_k^2 <= p Delta Σ_w deg_H(w) = p d Delta \|X\| <= 2 Delta \|X\| = beta (S6: p d <= 2), beta > 0; a = 0.3\|X\|; exponent 0.09\|X\|^2/(2(2Delta\|X\| + 0.1 Delta\|X\|)) = 0.09\|X\|/(4.2 Delta) >= \|X\|/(47 Delta) (0.021428 > 0.021277); E Z >= (1 - e^{-1})\|X\| >= 0.63\|X\| since P(N_H(x) ∩ V_i = ∅) = (1-p)^d <= e^{-pd} <= e^{-1}; exponents: p <= 0.11 ⇒ 2^19/(94·300) = 18.59 >= 18; p > 0.11 ⇒ Delta < 1075, 2^19/(94·1075) = 5.19 >= 5, 5 ell^2 >= 18. No error found; severity 'risk' only because this step has no independent review and its margins are thin (0.7% in 0.09/4.2 vs 1/47; 3% in 18.59 vs 18). |
| risk | `s3:lemL17s` | L17-S2-DEPENDENCY | The transfer 'V_1 ∪ ... ∪ V_ell is rho-random' (S2) is the bridge between the proof's layered space and the Spec's arbitrary rho-random R. Without StarUnionLawStatement (new infrastructure, hazard STAR-S2-UNIONLAW) the Spec form cannot be derived; do not work around it by stating L17s only for the layered space (P18s/T16* need the IsRSubset form because V lives on a product with the colouring). |
| note | `s3:lemMonotone` | MON-EXISTING | (i), (ii), (iii)(b),(c) are already proved sorry-free in EG/Lib/Found/Graph.lean (IsExpander.of_le, IsExpander.mono, IsPathConnected.mono, exists_paths, exists_paths_sigma). Remaining work: tag the declarations with [s3:lemMonotone], add the traceability Spec and the map-equality lemma. The Lean (ii) is slightly stronger than the manuscript (no V' ⊆ V(G) needed). |
| note | `s3:lemMonotone` | MON-ADAPTIVE-READING | 'P may be chosen after X and V are revealed, as an arbitrary function of them and of any further randomness (adaptively)' is sound only because Def 7 is a universally quantified property of (X,V): consumers must use it POINTWISE (fix ω in the event, then apply exists_paths to the multiset P(ω)), never as a probability statement whose event mentions P. In Lean this is automatic; statement reviewers of s4/s5/s6 Specs must check that no Spec quantifies 'with probability ... for the multiset P(ω)' in a way that re-introduces P into the event. |
| note | `s3:lemMonotone` | MON-MARGINAL | The probabilistic content consumers actually need (T16* Step 5: 'the random colouring of Step 1, which is auxiliary, does not affect the event, which depends only on (X,V)'; s4:lemTPV '(G2) depends only on the classes and the sets') is marginalization: probability of an event that is a function of (X,V) equals its probability under the law of (X,V). Lean: prob_map + map_fst_prod/map_snd_prod/map_fst_compProd (exist). Provide the one-line wrapper lemma above so consumer proofs do not repeat it. |
| note | `s3:lemMonotone` | MON-JOINT-MULT | Joint routing needs the multiplicity of each vertex in the SUM multiset (Σ_k over the q multisets) to be <= t (exists_paths_sigma). Consumers (s3:lemCOL, s4 TPV/PV, s6:lemJSLC) must bound this sum; bounding each P_k separately by t is not enough. |
| note | `s3:lemMonotone` | MON-UPWARD | s4 (lemTPV/PV/VX+) uses (ii) with G = G', ell = ell', t = t' only as 'the event is closed upwards in V' (monotone-comparison coupling of v6 R5): IsPathConnected.mono with hle := le_rfl, hV := rfl. No additional lemma needed. |
| note | `s3:lemL15p` | L15-DONE | Statement locked-candidate and proof complete (0 sorry, status/STATUS.md: EG.Proof.Link.L15 30 constants, 0 using sorry). Nothing to do for this node except tagging/lock. |
| note | `s3:lemL15p` | L15-K-NEZERO | k : ℕ with [NeZero k]. Consumers with k = K_* = ⌈6 s̄ θ L²/ε'⌉₊ or k_lend(Y) (possibly 0 when r >= R-1: then there are no lent classes and L15p must not be invoked) must supply the instance from a positivity proof (haveI : NeZero k := ⟨by positivity/omega⟩). |
| note | `s3:lemL15p` | L15-FIN-COLOURS | Colours are Fin k (0-based) in place of [k]; named colour families (s4 TPV's 3J+1 colours) need an explicit equivalence with Fin k (CONVENTIONS). |
| note | `s3:lemL15p` | L15-PER-CLASS-VS-ALL | The per-colour bound 1 - 2N^{-5} and the all-colours bound 1 - 2kN^{-5} are different statements; both are in the Spec. s5:lemE1 sums per-class failures over 2 + k_lend + k_own classes of three different colourings — use the per-class conjunct. |
| note | `s3:remMultiset` | MS-BUILTIN | Def 7's multiset reading (RT2-I14) is built into EG.FGraph.IsPathConnected: indices are occurrences, the multiplicity bound counts indices, one path per index, pairwise edge-disjoint for distinct indices. Endpoints are only required to be in V(G) (unrestricted w.r.t. W), interior in W. Matches items (1),(2),(5) exactly; no Spec needed. |
| note | `s3:remMultiset` | MS-ORDERED-PAIRS | Lean pairs are ordered (V × V). Because (P i).1 ≠ (P i).2, the Lean count #{i \| (P i).1 = v ∨ (P i).2 = v} equals the manuscript's occurrence count of v; reversal of a path handles orientation (IsPathBetween.reverse). |
| note | `s3:remMultiset` | MS-COUNTING-HYP | The counting step needs only 'every pair of I has an endpoint covered by I'' (the consequence of maximality), not maximality itself; state the Lib lemma that way (maximality → cover is a separate 5-line lemma). The multiplicity hypothesis may be restricted to I (a fortiori from the global bound). |
| note | `s3:remMultiset` | MS-CITLEM9-COMMENTARY | Items (3) and (4) are phrased as claims about B-M's proof of Lemma 9; B-M Lemma 9 has no Lean declaration (s1 blueprint L9-NOLEAN) and is not used. Mark the \deps edge to s1:citLem9 as attribution-only for msreport; the logical content is re-proved inside s3:lemL9rho. |
| note | `s3:remMultiset` | MS-UNDECLARED-USE | s6:lemJSLC uses this remark without \deps (usesgen will add the edge from the \ref). |
| note | `s3:eqStar` | STAR-PSTAR-IMPLICIT | p_* is defined implicitly ('given by (1-p)^{ell-1} = (1-rho)/(1-0.9rho)'). Lean: explicit closed form p := 1 - b^(1/(ell-1)) with b := (1-rho)/(1-0.9rho) ∈ [0,1) (Real.rpow; ell - 1 >= 1023 > 0). Then (1-p)^(ell-1) = b by Real.rpow_natCast and rpow_mul (b >= 0); rho = 1 gives b = 0, 0^(positive) = 0, p = 1, consistent. Uniqueness is never used downstream; existence + the defining equation suffice. Faithful. |
| note | `s3:eqStar` | STAR-TYPES | ell_*, d_*, lambda_*, Delta_*, M_*, K_* ∈ ℕ (Nat.floor/Nat.ceil of positive reals; the ceilings are of strictly positive arguments under the domain hypotheses). g_*, q_*, p_*, sigma_*, theta_*, mu_*, sbar_* ∈ ℝ. In EG.ball the radius ell_* : ℕ is used directly (no ⌊·⌋₊ needed). '0.9', '2.1', '8.34', '2.34', '0.11' must be written as exact rationals (9/10, 21/10, 834/100, ...). |
| note | `s3:eqStar` | STAR-DOMAIN | The definitions are total; every fact needs n >= 2 (L >= 1), 2^-7 <= eps' <= 1, 0 < rho <= 1, and (S5) additionally 1 <= t. For n < 2, L <= 0 and ell_* = 0 (then p's exponent 1/(0-1) = -1 is junk); no statement may use the parameters without n >= 2. |
| note | `s3:eqStar` | STAR-S5-RPOW | (S5)'s 2^{83.6} and 2^{130.6} are real powers used only by s3:thmT16s (to reach its 2^86 and 2^135). Proposed Lean form: keep the exact rational products (6·2^81+1) and 2(6·2^81+1)(2^46+1) in StarFactsStatement (as above) and let T16*'s proof compare with 2^86 / 2^135 by norm_num (3(6·2^81+1)+1 <= 2^86 and 2(6·2^81+1)(2^46+1) <= 2^131 <= 2^135). The log2 margins are 0.015 (2^83.6) and 0.015 (2^130.6); the crude bound K <= 2^84 tL^19rho^-3 would give 2K(theta+1) <= 2^132, still < 2^135. Nothing breaks, but do not state the rpow forms. |
| note | `s3:eqStar` | STAR-PARAM-ORDER | The parameters are functions of n = \|V(graph at hand)\|, eps', rho, t. In T16* each colour class X_i has the same n and eps', so its parameters are the same terms (definitional, since X_i.card = X.card is rfl for restrictEdges). No constant is chosen out of order. |
| note | `s3:eqStar` | STAR-S3-MARGINS | (S3): 25/3 <= 8.34, 7/3 <= 2.34 (exact); p <= 0.11 ⇒ 8.34/p <= 0.92/p^2 (needs p <= 0.11031) and 2.34 <= 0.03/p^2 (needs p <= 0.11323), total 2.95 <= 3; p <= 1 ⇒ 12.68 <= 13. (S4): 8(6+7+1) = 112, 11200 <= 2^19. (S5): 6·2^67·2^14 = 6·2^81. All exact rational arithmetic (norm_num) once the ceilings are replaced by x <= ⌈x⌉₊ < x + 1. |
| note | `s3:propP13s` | P13-GREEDY-VS-MAXIMAL | The manuscript builds H greedily over an ordering v_1..v_{r'} of V(G)\W and uses 'degrees in H_{i-1} are at most final degrees'. Recommended Lean proof: take (X, E_H) of MAXIMUM \|X\| among valid configurations (X ⊆ V\W, each x ∈ X has exactly d H-neighbours in W that are (G-F)-neighbours, all H-degrees in W <= Delta); if some v ∉ W ∪ X had d (G-F)-neighbours in U = W\Bl (final degree < Delta) it could be added, contradicting maximality. Same for the star family (max \|C\|). Proof-level deviation only; avoids list recursion. |
| note | `s3:propP13s` | P13-PROP12-FIRST | P13s cannot be proved before B-M Prop 12 has a Spec (s1 blueprint: EG.Spec.BMProp12Statement with EG.FGraph.nbrSetDeg). nbrSetDeg must be a single Defs constant shared by both Specs (s1 hazard P12-NEWDEF). Prop 12 is applied with d real = (d_* : ℝ) and needs U ⊆ V(G), F ⊆ E(G) (kept in both Specs). |
| note | `s3:propP13s` | P13-EPS-LOWER-UNUSED | 2^-7 <= eps' is not used in the proof (only 0 < eps' <= 1, via sigma >= 24L^2/eps' >= 24 and Delta - lambda > 0). Keep it in the Spec for faithfulness; the proof will not use the hypothesis (linter: unused variable is fine in a Spec). |
| note | `s3:propP13s` | P13-REAL-COUNTS | \|C\| >= \|W\|/sigma and \|X\| >= eps'\|W\|/(2L^2) are real comparisons with natural cardinalities; Delta - lambda is a real difference (Delta >= lambda so ℕ subtraction would also be safe, but write it in ℝ). The derived inequalities \|Sat\| < eps'\|W\|/(8L^2), \|Bl\| < eps'\|W\|/(6L^2) <= \|W\|/6, \|U\| >= 5\|W\|/6 and the Case-1 contradiction 39 lambda < 1 are linear arithmetic once \|Cen\| < \|W\|/sigma is available (strict: from the failure of (a) with \|C\| maximal). |
| note | `s3:propP13s` | P13-CASE-ANALYSIS | Checked in full: (P13a) N_{G-F}(W\Cen) ⊆ Cen ∪ Lvs ∪ ⋃_{w ∈ W\Cen}(N(w) \ (W ∪ Lvs)) gives \|.\| < (1+lambda)\|W\|/sigma + (lambda-1)\|W\|; Sat double count (Delta-lambda)\|Sat\| <= e_H(Sat, X∩Lvs) <= d\|Lvs\| < d lambda \|W\|/sigma; Case 1: N_{G-F}(U) ⊆ N_{G-F}(W\Cen) ∪ Sat; Case 2: N_{G-F,d}(U) \ Bl ⊆ X. No gap found. |
| note | `s3:lemL17s` | L17-STATEMENT-FORM | Decision: the Spec is the manuscript's final sentence ('the same bound holds for every rho-random subset V of V(G)'), quantified over an arbitrary finite probability space (Ω, μ) and R with μ.IsRSubset R G.verts rho. The layers are proof-internal. Consumers: s3:lemP18s(ii) (then T16* on the product space colouring × V, with V conditionally rho-random given the colouring: IsRSubset.cond_of_indepFun exists). Universe: Ω : Type u (same as V) suffices for T16*; a separate universe parameter is harmless if the lock tool supports Spec.{u,w}. |
| note | `s3:lemL17s` | L17-QUANTIFIERS | Order: ∀ U, F (fixed, deterministic) then the probability bound for that pair. This is exactly what P18s's union bound over pairs (U', F') needs. It is NOT 'with probability ... for all U, F' (that is P18s(ii)). U = ∅ is well-expanding (0 >= 0) and the bound is 1 (prob_le_one). |
| note | `s3:lemL17s` | L17-INCLUSIONS | U ⊆ V(G) (B_0 = U must consist of vertices; otherwise the one-vertex path [u] puts u ∉ V(G) into the ball, CONVENTIONS) and F ⊆ E(G) (needed by P13s → Prop 12 for \|F ∪ F'\| <= s\|U\| inside E(G)) are hypotheses of the manuscript and must stay in the Spec. The random set R ω ⊆ V(G) holds almost surely (IsRSubset.subset_ae); the proof must work on the support (0 < μ.w ω). |
| note | `s3:lemL17s` | L17-REACH-NOT-BALL | B_i (reach set) has its END vertex unrestricted and interior in V_1 ∪ .. ∪ V_{i-1}, whereas EG.ball requires the end in W. Define a separate Lib notion (reach) with (O1)-(O3); (O1)'s 'v does not lie on the path, since otherwise an initial segment would put v into B_i' needs a list lemma: a prefix (List.take) of a path through W is a path through W from the same start, of smaller length (IsPathIn of a prefix; interior of prefix ⊆ interior ∪ {last}). |
| note | `s3:lemL17s` | L17-NUMERICS | Constants to verify by norm_num with Real.exp/Real.log bounds (Real.exp_one_gt_d9, Real.log_two_lt_d9/gt_d9): n > theta >= 2^19 ell^2 L^3 ⇒ rho n > 2^39, 7uL <= 2^{-36} rho n; 0.1·2^19/192 >= 273; 1 - e^{-1} >= 0.63; 0.09/4.2 > 1/47; 2^19/28200 >= 18; 13/0.0121 < 1075; L^3 e^{-11L} <= e^{-11} for L >= 1 (from 3 ln L <= 3(L-1) <= 11(L-1)); 2^10 e^{-11} <= 0.02; ln(1+g) >= g - g^2/2 >= 15g/16 for 0 <= g <= 1/8; (ell-1)g > L - 2^{-9} (needs eps' >= 2^-7); (15/16)(L - 2^{-9}) >= L ln 2 for L >= 1; 0.0081·0.6/2 = 0.00243 >= 1/412; 0.0027 >= 1/412; 1/412 - 1/413 >= 2^{-36}; 2e^{-2^39/413} <= 0.01; 0.02 + 0.01 <= 1. Margins: 0.1% (0.00243 vs 1/412), 0.7% (1/47), otherwise >= 3%. All exact rationals or single exp/log facts. |
| note | `s3:lemL17s` | L17-STEP5-MIXED | Step 5 combines a conditional bound (given V_1..V_{ell-1} with \|B_ell\| >= 2n/3, V_ell is 0.9rho-random, mean >= 0.6 rho n; ChernoffGen(a) with the mean LOWER bound mu = 0.6 rho n, delta = 0.09) with an unconditional one (\|V\| ~ Bin(n, rho), upper tail delta = 0.09). The final bound is P(∪E_i^c) + P(E, \|B_ell\| >= 2n/3, \|B_ell ∩ V_ell\| < 0.546 rho n) + P(\|V\| > 1.09 rho n) <= 0.02e^{-7uL} + 0.01e^{-7uL}. Lean: three events and prob_biUnion_le; the middle one via the prefix-conditioning lemma of L17-LAYER-SPACE. |
| note | `s3:lemL17s` | L17-P13-CHOICE | Within the claim, W and F are fixed and P13s gives a disjunction with existential witnesses; choose them with Classical.choose (deterministic in W). The claim must be proved for EVERY fixed W (⊇ B_1, \|W\| <= 2n/3), not for the random B_i, and then applied slice-wise — this is what makes the case split legitimate. |
| note | `s3:lemL17s` | L17-EPS-USE | eps' >= 2^-7 is used in Step 4 (g_* >= 2^{-10}L^{-2}) and passed to P13s; eps' <= 1 in Step 0 (theta >= 2^19 ell^2 L^3/rho^2), g_* <= 1/8, and P13s. s_1 >= 8 d lambda >= 48 gives \|F\| <= u <= \|W\| <= s_1\|W\|/4. |
| note | `s3:lemP18s` | P18-THETA-PLUS-ONE | The hypothesis s_1 >= theta_* + 1 (RT2-I12) is necessary for the proof ((i): \|F\| <= Σ a_v < (theta+1)\|U\| needs to be <= s_1\|U\|). T16* supplies s/(2K_*) >= theta_* + 1. Keep exactly this form. |
| note | `s3:lemP18s` | P18-I-MAXIMAL | (i) takes U' ⊆ U maximal (inclusion) with \|N_G(U')\| >= theta\|U'\|; Lean: Finset.exists_maximal on U.powerset.filter (∅ qualifies). The identity \|N(U' ∪ {v})\| = \|N(U')\| - 1{v ∈ N(U')} + a_v (a_v = # neighbours of v outside U' ∪ N(U')) needs a small Finset lemma; only the inequality \|N(U' ∪ {v})\| >= \|N(U')\| - 1 + a_v is used (to get a_v < theta + 1) together with \|N(U' ∪ {v})\| >= \|N(U')\| - 1 (to get \|N(U')\| < theta(\|U'\|+1) + 1). Then N_{G-F}(U) ⊆ N_G(U') for F := E_G(U\U', V(G) \ (U' ∪ N(U'))), expansion, and the case U' = ∅ contradiction. The general-theta Lib lemma is cleaner than instantiating theta_* early. |
| note | `s3:lemP18s` | P18-EG-COUNT | The manuscript bounds #{F' ⊆ E(G) : \|F'\| <= u} <= Σ_{f<=u} e_G^f <= 2e_G^u using e_G >= 2, which it derives from the min-degree remark (delta(G) > s_1 >= 1, needs eps' > 0 and n >= 2: IsExpander.lt_deg). Simpler Lean route with no e_G >= 2: Σ_{f<=u} C(e_G, f) <= (e_G + 1)^u <= n^{2u} (e_G <= n^2/2, so e_G + 1 <= n^2 for n >= 2), and #U' of size u <= C(n,u) <= n^u; total n^{3u} per size as in the manuscript. |
| note | `s3:lemP18s` | P18-UNIONBOUND-SUM | Per pair failure <= e^{-7uL} = n^{-7u/ln 2} <= n^{-10.09u} (7/ln 2 = 10.0989; needs ln 2 <= 0.69375, Real.log_two_lt_d9). Σ_{u>=1} n^{3u} n^{-10.09u} <= n^{-7.09}/(1 - n^{-7.09}) <= n^{-6} for n >= 2 (n^{-1.09} <= 1 - n^{-7.09}). Lean: sum over nonempty subsets U' of V(G) grouped by card, or reuse the exact binomial trick of EG.L15.sum_powerset_erase_pow_le ((1 + n^{-7})^n - 1 style). Also the union bound must range over the finite family of pairs; the complement event implies the deterministic conclusion for all (U, F). |
| note | `s3:lemP18s` | P18-DETERMINISTIC-CASES | Case \|U\| <= 2n/3, \|F\| <= 2mu_*\|U\|: (i) gives U' with \|U'\| >= eps'\|U\|/(3theta L^2) = 2mu_*\|U\| >= \|F\|, so (U', F) is in the union-bound family (U' ≠ ∅ from \|U'\| > 0); ball_mono_left. Case \|U\| > 2n/3: choose Ū ⊆ U with \|Ū\| = ⌈n/2⌉ = (n+1)/2 (ℕ division), which satisfies 3\|Ū\| <= 2n for n >= 2 (omega) and \|Ū\| <= \|U\| (Finset.exists_subset_card_eq); \|F\| <= mu n <= 2mu\|Ū\|. The manuscript's 'check n <= 5 directly' is replaced by the ℕ fact. |
| note | `s3:lemP18s` | P18-SINGLE-EVENT | (ii) is 'with probability >= 1 - n^{-6}, for all U, F' — the quantifiers are INSIDE the event (contrast L17s). T16* Step 4 applies it pointwise to U and F ∩ E(X_i) for the class i with few F-edges; F ranges over subsets of E(G) (for the class graph X_i: E(X_i)). |
| note | `s3:lemP18s` | P18-L17-HYP | L17s needs s_1 >= 8 d_* lambda_*: from (S4) theta_* >= 112p^-2 >= 8 d_* lambda_*, so s_1 >= theta_* + 1 suffices. Also theta_* >= 1 (from (S4)/(S1)) is used in (i). Both come from StarFactsStatement. |

## 4. Nodes

### `s3:lemMonotone` — lemma: monotonicity and the for-all property (s3.tex:49)

- **Manuscript referee status:** x2+RT
- **Formalization:** Lib (already proved, sorry-free, in EG/Lib/Found/Graph.lean: IsExpander.of_le, IsExpander.mono, IsPathConnected.mono, IsPathConnected.exists_paths, IsPathConnected.exists_paths_sigma) + a thin traceability Spec EG/Spec/Link/Monotone.lean (MonotoneStatement) + one new Lib lemma for the probabilistic reading of (iii) (event determined by the law of (X,V))

**Statement (precise restatement).** (i) Let eps', s be reals, H and H' finite simple graphs with V(H') = V(H) and E(H) ⊆ E(H'). If H is an (eps',s)-expander (s1:citDef11) then H' is an (eps',s)-expander. Moreover, for all reals eps'' <= eps' and s' <= s, every (eps',s)-expander is an (eps'',s')-expander (no sign conditions are needed). (ii) Let G ⊆ G' be graphs with V(G) = V(G'), let V ⊆ V' (⊆ V(G); the Lean form does not need this), reals ell <= ell' and t' <= t. If G is (ell,t)-path connected through V (s1:citDef7, multiset form) then G' is (ell',t')-path connected through V'. (iii) (a) '(ell,t)-path connected through V' is a predicate of the pair (X,V) (and ell,t) only. (b) On this event, for EVERY finite multiset P of pairs of distinct vertices of X in which every vertex lies in at most t pairs (counted with multiplicity), there are pairwise edge-disjoint paths of X, one per occurrence, joining the pair, of length <= ell, with all interior vertices in V; P may be any function of (X,V) and of further randomness (the property is a universally quantified statement, applied pointwise at each outcome). (c) Joint routing: for finitely many multisets P_1..P_q such that every vertex lies in at most t pairs of the sum P_1+...+P_q (multiplicities ADDED over k), one application gives pairwise edge-disjoint paths for all pairs of all P_k simultaneously. Probabilistic reading used downstream (T16* Step 5, s4 TPV/PV/VX+, s5:lemParent Step 6, s6:lemJSLC(d)): if (X,V) is a random pair on a finite space, the probability of the event {X is (ell,t)-path connected through V} depends only on the law of (X,V); in particular auxiliary independent randomness (a colouring) can be integrated out.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| (eps,s)-expander | Def 11 of B-M on FGraph with log = log_2 of \|G\| | s1:citDef11 | yes: EG.FGraph.IsExpander (EG/Defs/Expander.lean) |
| (ell,t)-path connected through W (multiset form) | Def 7 of B-M; indexed families P : ι → V × V over a Fintype ι, multiplicity = number of indices having v as an entry, one path per index, pairwise edge-disjoint | s1:citDef7, s1:convGraphs(e), s3:remMultiset | yes: EG.FGraph.IsPathConnected (EG/Defs/Expander.lean) |
| subgraph with the same vertex set | H ≤ H' (FGraph partial order: verts ⊆ and edges ⊆) together with H.verts = H'.verts | s1:convGraphs | yes: FGraph PartialOrder instance (EG/Defs/Graph.lean) |
| paths through W, path length, edge-disjointness | IsPathBetween E x y p, IsThrough W p, pathLength p, walkEdges p Disjoint | s1:convGraphs(d) | yes: EG/Defs/Walk.lean |
| law of a random pair / pushforward | FinDist.map, prob_map, prob_prod_snd, prob_compProd_fst | PLAN §3 decision 3 | yes: EG/Defs/Prob/FinDist.lean, EG/Lib/Prob/Basic.lean |

**deps_declared** (manuscript \deps): s1:citDef7, s1:citDef11

**deps_from_proof:** s1:citDef11; s1:citDef7; s1:convGraphs

**deps_notes:** Proof of (i) uses only Def 11 (with F ∩ E(H) and nbrSet monotonicity under ≤); (ii),(iii) only Def 7. s1:convGraphs(c),(d) supply H-F, Nbr, paths through V. Declared deps are exact.

**used_by:** s3:thmT16s (Step 5: the colouring is auxiliary; statement: P chosen after V); s3:lemCOL (joint routing, s3.tex:1449, 1549); s4:lemTPV ((ii) 'closed upwards', (iii) event depends only on classes and sets); s4:lemPV; s4:thmVXp; s5:lemParent (Step 6: multiset formed after the stage-1 outcome); s6:lemJSLC ((d): multiset chosen after stage 1)

**randomness:** none in the lemma itself. (iii) is a deterministic statement; its probabilistic use: for any FinDist μ on Ω and random X : Ω → FGraph V, W : Ω → Finset V, μ.prob {ω | (X ω).IsPathConnected ℓ t (W ω)} = (μ.map (fun ω => (X ω, W ω))).prob {xw | xw.1.IsPathConnected ℓ t xw.2} (prob_map), so it is unchanged by adjoining independent coordinates (prob_prod_fst / prob_prod_snd / prob_compProd_fst).

**lean_shape:**

```lean
-- EXISTING (EG/Lib/Found/Graph.lean), tag each with docstring [s3:lemMonotone]:
theorem EG.FGraph.IsExpander.of_le (hG : G.IsExpander ε s) (hle : G ≤ H) (hV : G.verts = H.verts) : H.IsExpander ε s
theorem EG.FGraph.IsExpander.mono (hG : G.IsExpander ε s) (hε : ε' ≤ ε) (hs : s' ≤ s) : G.IsExpander ε' s'
theorem EG.FGraph.IsPathConnected.mono (hG : G.IsPathConnected ℓ t W) (hle : G ≤ G') (hV : G.verts = G'.verts)
    (hW : W ⊆ W') (hℓ : ℓ ≤ ℓ') (ht : t' ≤ t) : G'.IsPathConnected ℓ' t' W'
theorem EG.FGraph.IsPathConnected.exists_paths  -- (iii)(b), index type in any universe
theorem EG.FGraph.IsPathConnected.exists_paths_sigma  -- (iii)(c) joint routing, multiplicity = Σ_k
-- NEW Lib lemma (EG/Lib/Prob/Basic.lean or Link): probabilistic reading of (iii)(a)
theorem EG.FinDist.prob_isPathConnected_eq_of_map_eq {Ω Ω' : Type*} (μ : FinDist Ω) (μ' : FinDist Ω')
    (X : Ω → FGraph V) (W : Ω → Finset V) (X' : Ω' → FGraph V) (W' : Ω' → Finset V)
    (h : μ.map (fun ω => (X ω, W ω)) = μ'.map (fun ω => (X' ω, W' ω))) :
    μ.prob {ω | (X ω).IsPathConnected ℓ t (W ω)} = μ'.prob {ω | (X' ω).IsPathConnected ℓ t (W' ω)}
-- Traceability Spec (EG/Spec/Link/Monotone.lean); proved by the lemmas above:
def EG.Spec.MonotoneStatement : Prop := ∀ (V : Type u) [DecidableEq V],
  (∀ (H H' : FGraph V) (ε s : ℝ), H ≤ H' → H.verts = H'.verts → H.IsExpander ε s → H'.IsExpander ε s) ∧
  (∀ (H : FGraph V) (ε s ε'' s' : ℝ), ε'' ≤ ε → s' ≤ s → H.IsExpander ε s → H.IsExpander ε'' s') ∧
  (∀ (G G' : FGraph V) (W W' : Finset V) (ℓ ℓ' t t' : ℝ), G ≤ G' → G.verts = G'.verts → W ⊆ W' → ℓ ≤ ℓ' → t' ≤ t →
     G.IsPathConnected ℓ t W → G'.IsPathConnected ℓ' t' W') ∧
  (∀ (G : FGraph V) (W : Finset V) (ℓ t : ℝ) (κ : Type) [Fintype κ] (ι : κ → Type) [∀ k, Fintype (ι k)]
     (P : ∀ k, ι k → V × V), G.IsPathConnected ℓ t W →
     (∀ k i, (P k i).1 ∈ G.verts ∧ (P k i).2 ∈ G.verts ∧ (P k i).1 ≠ (P k i).2) →
     (∀ v, ((∑ k, (Finset.univ.filter (fun i => (P k i).1 = v ∨ (P k i).2 = v)).card : ℕ) : ℝ) ≤ t) →
     ∃ Q : ∀ k, ι k → List V, (∀ k i, IsPathBetween G.edges (P k i).1 (P k i).2 (Q k i) ∧ IsThrough W (Q k i) ∧
        (pathLength (Q k i) : ℝ) ≤ ℓ) ∧ ∀ k i k' j, (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ → (walkEdges (Q k i)).Disjoint (walkEdges (Q k' j)))
```

**hazards:**

- **[note] MON-EXISTING.** (i), (ii), (iii)(b),(c) are already proved sorry-free in EG/Lib/Found/Graph.lean (IsExpander.of_le, IsExpander.mono, IsPathConnected.mono, exists_paths, exists_paths_sigma). Remaining work: tag the declarations with [s3:lemMonotone], add the traceability Spec and the map-equality lemma. The Lean (ii) is slightly stronger than the manuscript (no V' ⊆ V(G) needed).
- **[note] MON-ADAPTIVE-READING.** 'P may be chosen after X and V are revealed, as an arbitrary function of them and of any further randomness (adaptively)' is sound only because Def 7 is a universally quantified property of (X,V): consumers must use it POINTWISE (fix ω in the event, then apply exists_paths to the multiset P(ω)), never as a probability statement whose event mentions P. In Lean this is automatic; statement reviewers of s4/s5/s6 Specs must check that no Spec quantifies 'with probability ... for the multiset P(ω)' in a way that re-introduces P into the event.
- **[note] MON-MARGINAL.** The probabilistic content consumers actually need (T16* Step 5: 'the random colouring of Step 1, which is auxiliary, does not affect the event, which depends only on (X,V)'; s4:lemTPV '(G2) depends only on the classes and the sets') is marginalization: probability of an event that is a function of (X,V) equals its probability under the law of (X,V). Lean: prob_map + map_fst_prod/map_snd_prod/map_fst_compProd (exist). Provide the one-line wrapper lemma above so consumer proofs do not repeat it.
- **[note] MON-JOINT-MULT.** Joint routing needs the multiplicity of each vertex in the SUM multiset (Σ_k over the q multisets) to be <= t (exists_paths_sigma). Consumers (s3:lemCOL, s4 TPV/PV, s6:lemJSLC) must bound this sum; bounding each P_k separately by t is not enough.
- **[note] MON-UPWARD.** s4 (lemTPV/PV/VX+) uses (ii) with G = G', ell = ell', t = t' only as 'the event is closed upwards in V' (monotone-comparison coupling of v6 R5): IsPathConnected.mono with hle := le_rfl, hV := rfl. No additional lemma needed.

**effort:** ~60 new Lean lines, difficulty 1/5 (Already proved: ~120 lines in EG/Lib/Found/Graph.lean (not counted). New: traceability Spec ~35 lines + proof ~10, map-equality wrapper ~15.)

### `s3:lemL15p` — lemma: Lemma 15^+: random splitting without loss (s3.tex:102)

- **Manuscript referee status:** x2+RT
- **Formalization:** DONE: Spec EG.Spec.L15pStatement (EG/Spec/Link/L15.lean) and complete sorry-free proof EG.l15p (EG/Proof/Link/L15.lean, 416 lines), plus consumer corollaries EG.exists_colouring_forall_isExpander, EG.l15p_of_map_eq, EG.l15p_prod_fst; shared def EG.FGraph.colourClass (EG/Lib/Found/ColourClass.lean)

**Statement (precise restatement).** Let X be a finite simple graph with N := |V(X)| vertices, eps' real with 0 < eps' <= 1, s real, L := log_2 N, k >= 1 an integer with s >= 40kL, and X an (eps',s)-expander. Colour every edge of X independently and uniformly with a colour from [k] (sample space: uniform product on [k]^{E(X)}). For i ∈ [k] let X_i := (V(X), {e ∈ E(X) : colour(e) = i}) (spanning colour class). Then (1) for each i ∈ [k], P(X_i is an (eps', s/(2k))-expander) >= 1 - 2N^{-5}; (2) P(all k classes are (eps', s/(2k))-expanders) >= 1 - 2kN^{-5}. No size condition on N (N <= 1: every graph is an expander; N = 0: N^{-5} read as 0 in Lean, statement still true).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| (eps,s)-expander | Def 11 | s1:citDef11 | yes: EG.FGraph.IsExpander |
| uniform random k-colouring of E(X) | FinDist.randColouring ↥X.edges k = pi (uniform (Fin k)) over the edge finset; colours Fin k = {0..k-1} | s3:lemL15p | yes: EG.FinDist.randColouring (EG/Defs/Prob/FinDist.lean) |
| colour class X_i | X.restrictEdges (selectSet X.edges (fun e => decide (c e = i))) — vertex set V(X), edges of colour i; named EG.FGraph.colourClass X c i in Lib (rfl) | s3:lemL15p | yes: EG.FGraph.restrictEdges, EG.FinDist.selectSet; Lib EG.FGraph.colourClass |
| Binomial / Chernoff lower tail delta = 1/2 | P(Z < mu/2) <= exp(-mu/8) for a colour count | s1:citChernoff | yes: EG.FinDist.chernoff_randColouring_lower_half (EG/Lib/Prob/Chernoff.lean) |

**deps_declared** (manuscript \deps): s1:citDef11, s1:citChernoff

**deps_from_proof:** s1:citDef11; s1:citChernoff; s1:convGraphs

**deps_notes:** Exact. s1:convGraphs(c) for e_X(A,B), N_{H-F}(U). The Lean proof replaces the manuscript's N^{2u}N^{-7.2u} sum by the exact binomial count Σ_{∅≠U⊆V(X)} N^{-6|U|} = (1+N^{-6})^N - 1 <= 2N^{-5} with the cruder e^{-5uL} <= N^{-7u} (proof-level deviation only).

**used_by:** s3:thmT16s (Step 1, k = K_*); s3:lemCOLJV (row 3 hypotheses s >= 40kL); s3:lemCOL (three applications: k = 2, k = k_lend(Y), k = k_own); s4:lemTPV (k = 3J+1 named colours); s4:thmVXp; s5:lemE1 (COL(a) conditional on the split); s1:citLem15 / s1:remBMused / s1:defConstants (mentions only)

**randomness:** Sample space: randColouring ↥X.edges k (uniform on (↥X.edges → Fin k)), X fixed. No conditioning in the lemma. Consumers: (T16*) colouring independent of the random set V — product space, handled by l15p_prod_fst; (s3:lemCOL, s5:lemE1) second-stage colourings uniform GIVEN the first split, i.e. the colouring law is a kernel of the first stage — handled by l15p_of_map_eq applied slice-wise (prob_compProd_le_of_forall).

**lean_shape:**

```lean
-- EXISTING, locked candidate (EG/Spec/Link/L15.lean):
def EG.Spec.L15pStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : EG.FGraph V) (ε' s : ℝ) (k : ℕ) [NeZero k],
    0 < ε' → ε' ≤ 1 → 40 * (k : ℝ) * Real.logb 2 (X.card : ℝ) ≤ s → X.IsExpander ε' s →
    (∀ i : Fin k, 1 - 2 * (X.card : ℝ) ^ (-5 : ℤ) ≤ (EG.FinDist.randColouring X.edges k).prob
        {c | (X.restrictEdges (EG.FinDist.selectSet X.edges fun e => decide (c e = i))).IsExpander ε' (s / (2 * (k : ℝ)))}) ∧
    1 - 2 * (k : ℝ) * (X.card : ℝ) ^ (-5 : ℤ) ≤ (EG.FinDist.randColouring X.edges k).prob
        {c | ∀ i : Fin k, (X.restrictEdges (EG.FinDist.selectSet X.edges fun e => decide (c e = i))).IsExpander ε' (s / (2 * (k : ℝ)))}
-- EXISTING proof: theorem EG.l15p : EG.Spec.L15pStatement.{u}
-- EXISTING consumer corollaries: EG.exists_colouring_forall_isExpander, EG.l15p_of_map_eq (any μ, c : Ω → (↥X.edges → Fin k)
--   with μ.map c = randColouring), EG.l15p_prod_fst (colouring as first factor of a product).
```

**hazards:**

- **[risk] L15-RANDOM-EDGESET.** (Consumer-side, decides whether L15p is usable as stated.) The Spec colours the edge finset of a FIXED X (type ↥X.edges). In s3:lemCOL / s5:lemE1 the second and third colourings are applied to Lend_Y and Own_Y, which are themselves random (outputs of the first k = 2 colouring): the index type ↥(Lend_Y ω).edges depends on ω, which a single FinDist cannot have. The consumer Specs (s3b) must colour a FIXED ambient edge set (E(X_Y), or the vertex-pair set) with independent uniform labels and define the classes of Lend_Y by restriction; then L15p applies slice-wise (for each value of the first stage the restricted colouring has law randColouring (Lend_Y).edges k, via map_selectSet_randColouring / l15p_of_map_eq). This is a data-model decision for s3:defCOL (not a manuscript error); if it is not made, L15p's Spec cannot be instantiated there.
- **[note] L15-DONE.** Statement locked-candidate and proof complete (0 sorry, status/STATUS.md: EG.Proof.Link.L15 30 constants, 0 using sorry). Nothing to do for this node except tagging/lock.
- **[note] L15-K-NEZERO.** k : ℕ with [NeZero k]. Consumers with k = K_* = ⌈6 s̄ θ L²/ε'⌉₊ or k_lend(Y) (possibly 0 when r >= R-1: then there are no lent classes and L15p must not be invoked) must supply the instance from a positivity proof (haveI : NeZero k := ⟨by positivity/omega⟩).
- **[note] L15-FIN-COLOURS.** Colours are Fin k (0-based) in place of [k]; named colour families (s4 TPV's 3J+1 colours) need an explicit equivalence with Fin k (CONVENTIONS).
- **[note] L15-PER-CLASS-VS-ALL.** The per-colour bound 1 - 2N^{-5} and the all-colours bound 1 - 2kN^{-5} are different statements; both are in the Spec. s5:lemE1 sums per-class failures over 2 + k_lend + k_own classes of three different colourings — use the per-class conjunct.

**effort:** ~0 new Lean lines, difficulty 2/5 (Done: Spec 60 + proof 416 + ColourClass 106 lines already in the repository.)

### `s3:remMultiset` — remark: multisets (RT2-I14) (s3.tex:175)

- **Manuscript referee status:** -- (no referee column; fixes RT2-I14)
- **Formalization:** No Spec. The multiset reading is definitional in EG.FGraph.IsPathConnected (indexed families). One Lib lemma for the counting step (used by s3:lemL9rho): EG/Lib/Link/Multiset.lean (or EG/Lib/Found/Graph.lean)

**Statement (precise restatement).** Content: (1) In Def 7 (s1:citDef7) the collection P is a MULTISET of pairs of distinct vertices: repeated pairs each need their own path (the paths for different occurrences are pairwise edge-disjoint); the endpoints are arbitrary vertices of the graph (need not lie in V); only interior vertices must lie in V. (2) 'every vertex lies in at most t pairs' counts occurrences. (3) [claim about B-M's proof of Lemma 9; commentary] (4) Counting step: let P = (x_i,y_i)_{i ∈ [r]} be a family of pairs of distinct vertices in which every vertex lies in at most t pairs (with multiplicity), I ⊆ [r], and I' ⊆ I a maximal subfamily of pairwise vertex-disjoint pairs; then |I| <= 2t|I'| (every pair of I meets one of the 2|I'| vertices covered by I', each of which lies in at most t pairs of I). (5) All path-connectivity statements of the manuscript are in this multiset sense.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| multiset of pairs | indexed family P : ι → V × V over a Fintype ι with (P i).1 ≠ (P i).2; occurrence count of v = #{i \| (P i).1 = v ∨ (P i).2 = v} | s1:citDef7, s1:convGraphs(e) | yes: built into EG.FGraph.IsPathConnected |
| vertex-disjoint subfamily | I' ⊆ I with {(P i).1,(P i).2} ∩ {(P j).1,(P j).2} = ∅ for distinct i,j ∈ I'; maximal: every i ∈ I has an endpoint in ⋃_{j∈I'} {(P j).1,(P j).2} | s3:remMultiset, s3:lemL9rho | no: stated inline in the Lib lemma (proof-internal notion) |

**deps_declared** (manuscript \deps): s1:citDef7, s1:citLem9

**deps_from_proof:** s1:citDef7; s1:convGraphs

**deps_notes:** s1:citLem9 is referenced only for commentary on B-M's proof (B-M Lemma 9 is not used; s3:lemL9rho re-proves it). No logical dependency on s1:citLem9. s6:lemJSLC cites this remark without declaring it (ms_deps report: undeclared).

**used_by:** s3:lemL9rho (counting step |I| <= 2t|I'|; repeated pairs get distinct hyperedges); s6:lemJSLC (d) (undeclared); every Spec using IsPathConnected (interpretation)

**randomness:** none

**lean_shape:**

```lean
-- Lib (EG/Lib/Link/Multiset.lean): the counting step, stated with the weakest hypothesis the proof uses
theorem EG.card_le_two_mul_of_cover {ι : Type*} [DecidableEq V] (P : ι → V × V) (I I' : Finset ι) (t : ℝ)
    (hmult : ∀ v, ((I.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤ t)
    (hcover : ∀ i ∈ I, (P i).1 ∈ I'.biUnion (fun j => {(P j).1, (P j).2}) ∨ (P i).2 ∈ I'.biUnion (fun j => {(P j).1, (P j).2})) :
    (I.card : ℝ) ≤ 2 * t * I'.card
-- (sketch: I ⊆ ⋃_{v ∈ cover} {i ∈ I | v endpoint of P i}; |cover| ≤ 2|I'|; each fibre ≤ t)
-- plus existence of a maximal vertex-disjoint I' ⊆ I (Finset.exists_maximal on the filter of I.powerset),
-- and |I'| ≤ n/2 when all endpoints lie in V(G) and pairs of I' are vertex-disjoint (2|I'| distinct vertices).
```

**hazards:**

- **[note] MS-BUILTIN.** Def 7's multiset reading (RT2-I14) is built into EG.FGraph.IsPathConnected: indices are occurrences, the multiplicity bound counts indices, one path per index, pairwise edge-disjoint for distinct indices. Endpoints are only required to be in V(G) (unrestricted w.r.t. W), interior in W. Matches items (1),(2),(5) exactly; no Spec needed.
- **[note] MS-ORDERED-PAIRS.** Lean pairs are ordered (V × V). Because (P i).1 ≠ (P i).2, the Lean count #{i | (P i).1 = v ∨ (P i).2 = v} equals the manuscript's occurrence count of v; reversal of a path handles orientation (IsPathBetween.reverse).
- **[note] MS-COUNTING-HYP.** The counting step needs only 'every pair of I has an endpoint covered by I'' (the consequence of maximality), not maximality itself; state the Lib lemma that way (maximality → cover is a separate 5-line lemma). The multiplicity hypothesis may be restricted to I (a fortiori from the global bound).
- **[note] MS-CITLEM9-COMMENTARY.** Items (3) and (4) are phrased as claims about B-M's proof of Lemma 9; B-M Lemma 9 has no Lean declaration (s1 blueprint L9-NOLEAN) and is not used. Mark the \deps edge to s1:citLem9 as attribution-only for msreport; the logical content is re-proved inside s3:lemL9rho.
- **[note] MS-UNDECLARED-USE.** s6:lemJSLC uses this remark without \deps (usesgen will add the edge from the \ref).

**effort:** ~60 new Lean lines, difficulty 1/5 (Counting lemma ~35 lines, maximal-subfamily existence and |I'| <= n/2 ~25 lines. Could be placed with s3:lemL9rho.)

### `s3:eqStar` — equation block with six proved facts (S1)-(S6) (namedlabels s3:eqS1..s3:eqS6); SUPPORTING NODE, not in the chunk's label list but a definition every node of this chunk after remMultiset depends on: local parameters of Theorem 16^* and facts (S1)-(S6) (s3.tex:227)

- **Manuscript referee status:** part of the T16* material (x2+RT); no separate referee row
- **Formalization:** Defs EG/Defs/Link/Star.lean (the parameter functions; IsWellExpanding is `EG.FGraph.IsWellExpanding` in EG/Defs/Graph.lean, not redefined here) + Spec EG/Spec/Link/Star.lean (StarFactsStatement = (S1),(S3),(S4),(S5),(S6) + the P13* hypothesis check; StarUnionLawStatement = (S2) law identity)

**Statement (precise restatement).** Inputs: n >= 2 (vertices of the graph at hand), L := log_2 n, eps' ∈ [2^-7, 1], rho ∈ (0,1], t >= 1. Definitions (eqStar): ell_* := ⌊2^10 L^3⌋ ∈ ℕ; g_* := eps'/(8L^2); q_* := 0.9 rho; p_* ∈ (0,1] the unique solution of (1-p)^{ell_*-1} = (1-rho)/(1-0.9rho); d_* := ⌈1/p_*⌉; lambda_* := ⌈6/p_*⌉; Delta_* := lambda_* + ⌈d_* lambda_*/3⌉; sigma_* := 24L^2/eps'; theta_* := 2^19 ell_*^2 L^3/(eps' rho^2); mu_* := eps'/(6 theta_* L^2); sbar_* := 2^28 t L^8/rho; M_* := ⌈2.1/rho⌉; K_* := ⌈6 sbar_* theta_* L^2/eps'⌉ (ell,d,lambda,Delta,M,K integers). Write p := p_*. (S1) 2^10L^3 - 1 < ell_* <= 2^10L^3 and ell_* >= 2^10. (S2) p_* exists, is unique, p_* >= 0.1 rho/ell_* (so p^-2 <= 100 ell^2 rho^-2); if V_1..V_ell are independent random subsets of a finite S, V_i p-random for i < ell and V_ell q-random, then V_1 ∪ ... ∪ V_ell is a rho-random subset of S. (S3) Delta_* <= 2p^-2 + 8.34p^-1 + 2.34; hence Delta_* <= 3p^-2 if p <= 0.11 and Delta_* <= 13p^-2 for all p ∈ (0,1]. (S4) 8 d_* lambda_* <= 112 p^-2 <= theta_*, and theta_* <= 2^39 L^9/(eps' rho^2) <= 2^46 L^9 rho^-2. (S5) K_* >= sbar_*/mu_*; K_* <= (6·2^81+1) t L^19 rho^-3 <= 2^83.6 t L^19 rho^-3; 2K_*(theta_*+1) <= 2^130.6 t L^28 rho^-5; 40 K_* L <= 2K_*(theta_*+1). (S6) sigma_* >= 24, lambda_* p >= 6, 1 <= d_* p <= 1 + p <= 2. P13* check: sigma_* = 24L^2/eps' and Delta_* - lambda_* = ⌈d_*lambda_*/3⌉ >= d_*lambda_*/3 = 8 d_* lambda_* L^2/(eps' sigma_*).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| ell_*, g_*, q_*, p_*, d_*, lambda_*, Delta_*, sigma_*, theta_*, mu_*, sbar_*, M_*, K_* | functions of (n : ℕ) (ε' ρ t : ℝ) as in (eqStar), with L := Real.logb 2 n; ℕ-valued ones via Nat.floor / Nat.ceil; p_* by the explicit closed form 1 - ((1-ρ)/(1-(9/10)ρ))^(1/(ell_*-1)) (Real.rpow) | s3:eqStar (s3.tex:227-237) | no: new EG.Star.* in EG/Defs/Link/Star.lean |
| well-expanding set | U ⊆ V(G) with \|N_G(U)\| >= theta_*\|U\| (N_G in G, not G-F) | s3:lemL17s (statement), used in s3:lemP18s | yes: EG.FGraph.IsWellExpanding G θ U (EG/Defs/Graph.lean, P2-D small; do not redefine in Star.lean) |
| rho-random subset / independence of layers | IsRSubset, iIndepFun | s3 conventions | yes: EG.FinDist.IsRSubset, EG.FinDist.iIndepFun |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:convGraphs

**deps_notes:** No \deps line (equation block). (S2)'s last claim is the only probabilistic fact; all others are real arithmetic.

**used_by:** s3:propP13s (hypotheses are satisfied by the eqStar values); s3:lemL17s ((S1),(S2),(S3),(S6), and (S4) via s1 >= 8dλ); s3:lemP18s ((S4): theta >= 8dλ, theta >= 1); s3:lemL9rho (ell_*, sbar_*, M_*, (S1)); s3:thmT16s ((S5))

**randomness:** (S2) only: product of ell_* independent random subsets of S (FinDist.pi over Fin ell_* of rsubset S p_i), pushed forward by the union map; claim: the pushforward equals rsubset S rho.

**lean_shape:**

```lean
namespace EG.Star   -- EG/Defs/Link/Star.lean
noncomputable def L (n : ℕ) : ℝ := Real.logb 2 n
noncomputable def ell (n : ℕ) : ℕ := ⌊(2:ℝ) ^ 10 * L n ^ 3⌋₊
noncomputable def g (n : ℕ) (ε' : ℝ) : ℝ := ε' / (8 * L n ^ 2)
noncomputable def q (ρ : ℝ) : ℝ := 9 / 10 * ρ
noncomputable def p (n : ℕ) (ρ : ℝ) : ℝ := 1 - ((1 - ρ) / (1 - 9 / 10 * ρ)) ^ ((1 : ℝ) / ((ell n : ℝ) - 1))
noncomputable def d (n : ℕ) (ρ : ℝ) : ℕ := ⌈1 / p n ρ⌉₊
noncomputable def lam (n : ℕ) (ρ : ℝ) : ℕ := ⌈6 / p n ρ⌉₊
noncomputable def Delta (n : ℕ) (ρ : ℝ) : ℕ := lam n ρ + ⌈((d n ρ * lam n ρ : ℕ) : ℝ) / 3⌉₊
noncomputable def sigma (n : ℕ) (ε' : ℝ) : ℝ := 24 * L n ^ 2 / ε'
noncomputable def theta (n : ℕ) (ε' ρ : ℝ) : ℝ := 2 ^ 19 * (ell n : ℝ) ^ 2 * L n ^ 3 / (ε' * ρ ^ 2)
noncomputable def mu (n : ℕ) (ε' ρ : ℝ) : ℝ := ε' / (6 * theta n ε' ρ * L n ^ 2)
noncomputable def sbar (n : ℕ) (ρ t : ℝ) : ℝ := 2 ^ 28 * t * L n ^ 8 / ρ
noncomputable def M (ρ : ℝ) : ℕ := ⌈(21 / 10 : ℝ) / ρ⌉₊
noncomputable def K (n : ℕ) (ε' ρ t : ℝ) : ℕ := ⌈6 * sbar n ρ t * theta n ε' ρ * L n ^ 2 / ε'⌉₊
end EG.Star
-- EXISTS in EG/Defs/Graph.lean (P2-D small); shown for reference only, do not redefine:
-- def EG.FGraph.IsWellExpanding (G : FGraph V) (θ : ℝ) (U : Finset V) : Prop := θ * U.card ≤ ((G.nbrSet U).card : ℝ)
-- Spec (EG/Spec/Link/Star.lean)
def EG.Spec.StarFactsStatement : Prop := ∀ (n : ℕ) (ε' ρ t : ℝ), 2 ≤ n → 2 ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 → 1 ≤ t →
  let L := Star.L n; let p := Star.p n ρ
  -- S1
  ((2:ℝ)^10 * L^3 - 1 < Star.ell n ∧ (Star.ell n : ℝ) ≤ 2^10 * L^3 ∧ 2^10 ≤ Star.ell n) ∧
  -- S2 (numeric part)
  (0 < p ∧ p ≤ 1 ∧ (1 - p) ^ (Star.ell n - 1) = (1 - ρ) / (1 - 9/10*ρ) ∧ 1/10 * ρ / Star.ell n ≤ p) ∧
  -- S3
  ((Star.Delta n ρ : ℝ) ≤ 2 * p⁻¹^2 + 8.34 * p⁻¹ + 2.34 ∧ (p ≤ 0.11 → (Star.Delta n ρ : ℝ) ≤ 3 * p⁻¹^2) ∧ (Star.Delta n ρ : ℝ) ≤ 13 * p⁻¹^2) ∧
  -- S4
  (((8 * Star.d n ρ * Star.lam n ρ : ℕ) : ℝ) ≤ 112 * p⁻¹^2 ∧ 112 * p⁻¹^2 ≤ Star.theta n ε' ρ ∧ Star.theta n ε' ρ ≤ 2^39 * L^9 / (ε' * ρ^2) ∧ 2^39 * L^9 / (ε' * ρ^2) ≤ 2^46 * L^9 / ρ^2) ∧
  -- S5 (integer-exponent form, see hazard STAR-S5-RPOW)
  (Star.sbar n ρ t / Star.mu n ε' ρ ≤ Star.K n ε' ρ t ∧ (Star.K n ε' ρ t : ℝ) ≤ (6 * 2^81 + 1) * t * L^19 / ρ^3 ∧
    2 * Star.K n ε' ρ t * (Star.theta n ε' ρ + 1) ≤ 2 * (6 * 2^81 + 1) * (2^46 + 1) * t * L^28 / ρ^5 ∧ 40 * Star.K n ε' ρ t * L ≤ 2 * Star.K n ε' ρ t * (Star.theta n ε' ρ + 1)) ∧
  -- S6
  (24 ≤ Star.sigma n ε' ∧ 6 ≤ Star.lam n ρ * p ∧ 1 ≤ Star.d n ρ * p ∧ Star.d n ρ * p ≤ 1 + p ∧ 1 + p ≤ 2) ∧
  -- P13* hypotheses
  (Star.sigma n ε' = 24 * L^2 / ε' ∧ Star.lam n ρ ≤ Star.Delta n ρ ∧ 1 ≤ Star.d n ρ ∧ 1 ≤ Star.lam n ρ ∧
    8 * Star.d n ρ * Star.lam n ρ * L^2 / (ε' * Star.sigma n ε') ≤ (Star.Delta n ρ : ℝ) - Star.lam n ρ)
-- S2 law identity (no proof terms: layer laws via IsRSubset)
def EG.Spec.StarUnionLawStatement : Prop := ∀ (α : Type u) [DecidableEq α] (Ω : Type u) (μ : FinDist Ω) (S : Finset α)
  (n : ℕ) (ρ : ℝ) (Vs : Ω → Fin (Star.ell n) → Finset α), 2 ≤ n → 0 < ρ → ρ ≤ 1 →
  μ.iIndepFun (fun i ω => Vs ω i) →
  (∀ i : Fin (Star.ell n), μ.IsRSubset (fun ω => Vs ω i) S (if (i : ℕ) + 1 < Star.ell n then Star.p n ρ else Star.q ρ)) →
  μ.IsRSubset (fun ω => Finset.univ.biUnion (Vs ω)) S ρ
```

**hazards:**

- **[risk] STAR-NO-LABEL-OWNER.** The parameter block (eqStar) and (S1)-(S6) are not a labelled environment of any chunk list, yet s3:propP13s (via its use), s3:lemL17s, s3:lemP18s, s3:lemL9rho and s3:thmT16s are stated 'with the parameters of (eqStar)'. If no one owns EG/Defs/Link/Star.lean before the s3 Specs are locked, each Spec will inline its own (possibly different) copy of p_*, Delta_*, theta_* ... Proposed: this chunk owns the Defs file and the two Specs; msreport should know the namedlabels s3:eqStar, s3:eqS1..s3:eqS6 as nodes.
- **[risk] STAR-S2-UNIONLAW.** (S2)'s last claim is new FinDist infrastructure: the union of independent layers with element probabilities p_i is an independent random subset with element probability 1 - Π(1-p_i). Nothing in EG/Lib/Prob (Named, Indep) covers unions of random sets; the proof must regroup the product over (layers × elements) into a product over elements of products over layers (pi swap / Fintype.piFinset reindexing, or via the elementwise characterization isRSubset_iff + iIndepFun of the layers). Needed by s3:lemL17s only. ~200 lines; the elementwise route through isRSubset_iff is recommended.
- **[note] STAR-PSTAR-IMPLICIT.** p_* is defined implicitly ('given by (1-p)^{ell-1} = (1-rho)/(1-0.9rho)'). Lean: explicit closed form p := 1 - b^(1/(ell-1)) with b := (1-rho)/(1-0.9rho) ∈ [0,1) (Real.rpow; ell - 1 >= 1023 > 0). Then (1-p)^(ell-1) = b by Real.rpow_natCast and rpow_mul (b >= 0); rho = 1 gives b = 0, 0^(positive) = 0, p = 1, consistent. Uniqueness is never used downstream; existence + the defining equation suffice. Faithful.
- **[note] STAR-TYPES.** ell_*, d_*, lambda_*, Delta_*, M_*, K_* ∈ ℕ (Nat.floor/Nat.ceil of positive reals; the ceilings are of strictly positive arguments under the domain hypotheses). g_*, q_*, p_*, sigma_*, theta_*, mu_*, sbar_* ∈ ℝ. In EG.ball the radius ell_* : ℕ is used directly (no ⌊·⌋₊ needed). '0.9', '2.1', '8.34', '2.34', '0.11' must be written as exact rationals (9/10, 21/10, 834/100, ...).
- **[note] STAR-DOMAIN.** The definitions are total; every fact needs n >= 2 (L >= 1), 2^-7 <= eps' <= 1, 0 < rho <= 1, and (S5) additionally 1 <= t. For n < 2, L <= 0 and ell_* = 0 (then p's exponent 1/(0-1) = -1 is junk); no statement may use the parameters without n >= 2.
- **[note] STAR-S5-RPOW.** (S5)'s 2^{83.6} and 2^{130.6} are real powers used only by s3:thmT16s (to reach its 2^86 and 2^135). Proposed Lean form: keep the exact rational products (6·2^81+1) and 2(6·2^81+1)(2^46+1) in StarFactsStatement (as above) and let T16*'s proof compare with 2^86 / 2^135 by norm_num (3(6·2^81+1)+1 <= 2^86 and 2(6·2^81+1)(2^46+1) <= 2^131 <= 2^135). The log2 margins are 0.015 (2^83.6) and 0.015 (2^130.6); the crude bound K <= 2^84 tL^19rho^-3 would give 2K(theta+1) <= 2^132, still < 2^135. Nothing breaks, but do not state the rpow forms.
- **[note] STAR-PARAM-ORDER.** The parameters are functions of n = |V(graph at hand)|, eps', rho, t. In T16* each colour class X_i has the same n and eps', so its parameters are the same terms (definitional, since X_i.card = X.card is rfl for restrictEdges). No constant is chosen out of order.
- **[note] STAR-S3-MARGINS.** (S3): 25/3 <= 8.34, 7/3 <= 2.34 (exact); p <= 0.11 ⇒ 8.34/p <= 0.92/p^2 (needs p <= 0.11031) and 2.34 <= 0.03/p^2 (needs p <= 0.11323), total 2.95 <= 3; p <= 1 ⇒ 12.68 <= 13. (S4): 8(6+7+1) = 112, 11200 <= 2^19. (S5): 6·2^67·2^14 = 6·2^81. All exact rational arithmetic (norm_num) once the ceilings are replaced by x <= ⌈x⌉₊ < x + 1.

**effort:** ~740 new Lean lines, difficulty 3/5 (Defs ~70 lines; StarFacts ~450 lines (rpow for p_*, Bernoulli's inequality (one_add_mul_le_pow), ceil/floor bookkeeping, rational numerics); StarUnionLaw ~200 lines (new random-set infrastructure); P13* hypothesis check ~20.)

### `s3:propP13s` — proposition: Proposition 13^*: stars or bipartite (s3.tex:286)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/Link/P13s.lean (P13sStatement) + proof EG/Proof/Link/P13s.lean; depends on the Spec of s1:citProp12 (EG.Spec.BMProp12Statement with the shared Defs constant EG.FGraph.nbrSetDeg)

**Statement (precise restatement).** Let G be a finite simple graph with n := |V(G)| >= 2, L := log_2 n, reals eps', s_1 with 2^-7 <= eps' <= 1 and G an (eps',s_1)-expander. Let W ⊆ V(G) with 1 <= |W| <= 2n/3 and F ⊆ E(G) with |F| <= s_1|W|/4. Let sigma > 0 be real and lambda, d, Delta natural numbers with lambda >= 1, d >= 1, Delta >= lambda, such that sigma >= 24L^2/eps', Delta - lambda >= 8 d lambda L^2/(eps' sigma), s_1 >= 8 d lambda. Then (a) OR (b): (a) there are a set C ⊆ W of centres with |C| >= |W|/sigma and, for each c ∈ C, a leaf set Lv(c) ⊆ V(G) \ W with |Lv(c)| = lambda, every leaf adjacent to c in G - F, and the Lv(c) (c ∈ C) pairwise disjoint (the stars are vertex-disjoint: centres are distinct elements of W, leaves lie outside W); (b) there are X ⊆ V(G) \ W and a graph H ⊆ G - F with V(H) = W ∪ X whose edges all join W to X (bipartite with sides W, X), such that |X| >= eps'|W|/(2L^2), deg_H(x) = d for every x ∈ X, and deg_H(w) <= Delta for every w ∈ W. (The hypothesis 2^-7 <= eps' is not used by the proof; only 0 < eps' <= 1 and L >= 1.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| (eps,s)-expander | Def 11 | s1:citDef11 | yes: EG.FGraph.IsExpander |
| N_{G-F,d}(U) | vertices of V(G)\U with at least d neighbours in U in G - F | s1:citProp12 (defined again in the proof of s3:propP13s) | no: new EG.FGraph.nbrSetDeg H U d (shared with the s1:citProp12 Spec; must be ONE Defs constant) |
| B-M Proposition 12 | G (eps,s)-expander, U ⊆ V(G), 1 <= \|U\| <= 2n/3, F ⊆ E(G), \|F\| <= s\|U\|/2, 0 < d <= s ⇒ \|N_{G-F}(U)\| >= s\|U\|/(2d) or \|N_{G-F,d}(U)\| >= eps\|U\|/log^2 n | s1:citProp12 | no: EG.Spec.BMProp12Statement (s1 blueprint; Lean-proved, not yet written) |
| vertex-disjoint stars with centre in W and lambda leaves outside W | encoded as (C : Finset V, lv : V → Finset V) as in (a) | s3:propP13s | no: inline existential in the Spec (no new Defs constant) |
| bipartite subgraph with sides W and X | H : FGraph V, H ≤ G.deleteEdges F, H.verts = W ∪ X, H.edges ⊆ G.edgesBetween W X | s3:propP13s | no: inline existential; uses EG.FGraph.deleteEdges, edgesBetween, deg, ≤ |

**deps_declared** (manuscript \deps): s1:citProp12, s1:citProp13, s1:citDef11

**deps_from_proof:** s1:citProp12; s1:citDef11; s1:convGraphs

**deps_notes:** The only logical input is B-M Prop 12 (applied once, to U := W \ Bl). s1:citDef11 is the definition of the hypothesis (ms_deps flags it 'declared but unreferenced'; it is a genuine definitional dependency). s1:citProp13 is attribution (proof structure) only. Not used: 2^-7 <= eps'.

**used_by:** s3:lemL17s (Step 2, with the eqStar values and W = B_i); s3:thmT16s (declared in \deps; not used logically — only through s3:lemL17s)

**randomness:** none (deterministic; in s3:lemL17s it is applied to a W that is fixed by conditioning on V_1..V_{i-1}).

**lean_shape:**

```lean
def EG.Spec.P13sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (ε' s₁ σ : ℝ) (lam d Δ : ℕ) (W : Finset V) (F : Finset (Sym2 V)),
    G.IsExpander ε' s₁ → 2 ≤ G.card → 2 ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 →
    W ⊆ G.verts → 1 ≤ W.card → (W.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 →
    F ⊆ G.edges → (F.card : ℝ) ≤ s₁ * W.card / 4 →
    0 < σ → 1 ≤ lam → 1 ≤ d → lam ≤ Δ →
    24 * Real.logb 2 G.card ^ 2 / ε' ≤ σ →
    8 * (d : ℝ) * lam * Real.logb 2 G.card ^ 2 / (ε' * σ) ≤ (Δ : ℝ) - lam →
    8 * (d : ℝ) * lam ≤ s₁ →
    (∃ (C : Finset V) (lv : V → Finset V), C ⊆ W ∧ (W.card : ℝ) / σ ≤ C.card ∧
        (∀ c ∈ C, (lv c).card = lam ∧ lv c ⊆ G.verts \ W ∧ ∀ x ∈ lv c, (G.deleteEdges F).Adj c x) ∧
        (C : Set V).PairwiseDisjoint lv) ∨
    (∃ (X : Finset V) (H : EG.FGraph V), X ⊆ G.verts \ W ∧ H ≤ G.deleteEdges F ∧ H.verts = W ∪ X ∧
        H.edges ⊆ G.edgesBetween W X ∧ ε' * W.card / (2 * Real.logb 2 G.card ^ 2) ≤ X.card ∧
        (∀ x ∈ X, H.deg x = d) ∧ (∀ w ∈ W, H.deg w ≤ Δ))
-- Lib consequences for the consumer (EG/Lib/Link/P13s.lean): in case (b), ∀ x ∈ X, H.nbrs x ⊆ W;
--   ∑ w ∈ W, H.deg w = d * X.card (double counting over H.edges ⊆ edgesBetween W X).
```

**hazards:**

- **[risk] P13-STAR-ENCODING.** 'vertex-disjoint stars, each with exactly lambda leaves, centre in W, leaves in V(G)\W' and 'bipartite subgraph with sides W and X' have no EG definition; the Spec's encoding fixes what s3:lemL17s can extract. Proposed encoding (above): (a) centre Finset C ⊆ W + leaf map lv with card, inclusion, (G-F)-adjacency and PairwiseDisjoint on C (vertex-disjointness then follows because centres ∈ W and leaves ∉ W); (b) FGraph H with H ≤ G - F, V(H) = W ∪ X, E(H) ⊆ E_G(W,X). L17s needs from (a): leaves of stars with centre in V_i lie in A_i(W) and distinct centres have disjoint leaf sets (|A_i(W)| >= lambda·|C ∩ V_i|); from (b): N_H(x) ⊆ W, |N_H(x)| = d, Σ_{w∈W} deg_H(w) = d|X|, deg_H(w) <= Delta. All derivable from the proposed encoding; if H were encoded only by an edge set, or the degree of x counted in G - F instead of H, case (b) of L17s would not go through. Decide before locking.
- **[note] P13-GREEDY-VS-MAXIMAL.** The manuscript builds H greedily over an ordering v_1..v_{r'} of V(G)\W and uses 'degrees in H_{i-1} are at most final degrees'. Recommended Lean proof: take (X, E_H) of MAXIMUM |X| among valid configurations (X ⊆ V\W, each x ∈ X has exactly d H-neighbours in W that are (G-F)-neighbours, all H-degrees in W <= Delta); if some v ∉ W ∪ X had d (G-F)-neighbours in U = W\Bl (final degree < Delta) it could be added, contradicting maximality. Same for the star family (max |C|). Proof-level deviation only; avoids list recursion.
- **[note] P13-PROP12-FIRST.** P13s cannot be proved before B-M Prop 12 has a Spec (s1 blueprint: EG.Spec.BMProp12Statement with EG.FGraph.nbrSetDeg). nbrSetDeg must be a single Defs constant shared by both Specs (s1 hazard P12-NEWDEF). Prop 12 is applied with d real = (d_* : ℝ) and needs U ⊆ V(G), F ⊆ E(G) (kept in both Specs).
- **[note] P13-EPS-LOWER-UNUSED.** 2^-7 <= eps' is not used in the proof (only 0 < eps' <= 1, via sigma >= 24L^2/eps' >= 24 and Delta - lambda > 0). Keep it in the Spec for faithfulness; the proof will not use the hypothesis (linter: unused variable is fine in a Spec).
- **[note] P13-REAL-COUNTS.** |C| >= |W|/sigma and |X| >= eps'|W|/(2L^2) are real comparisons with natural cardinalities; Delta - lambda is a real difference (Delta >= lambda so ℕ subtraction would also be safe, but write it in ℝ). The derived inequalities |Sat| < eps'|W|/(8L^2), |Bl| < eps'|W|/(6L^2) <= |W|/6, |U| >= 5|W|/6 and the Case-1 contradiction 39 lambda < 1 are linear arithmetic once |Cen| < |W|/sigma is available (strict: from the failure of (a) with |C| maximal).
- **[note] P13-CASE-ANALYSIS.** Checked in full: (P13a) N_{G-F}(W\Cen) ⊆ Cen ∪ Lvs ∪ ⋃_{w ∈ W\Cen}(N(w) \ (W ∪ Lvs)) gives |.| < (1+lambda)|W|/sigma + (lambda-1)|W|; Sat double count (Delta-lambda)|Sat| <= e_H(Sat, X∩Lvs) <= d|Lvs| < d lambda |W|/sigma; Case 1: N_{G-F}(U) ⊆ N_{G-F}(W\Cen) ∪ Sat; Case 2: N_{G-F,d}(U) \ Bl ⊆ X. No gap found.

**effort:** ~750 new Lean lines, difficulty 3/5 (Spec ~35; maximal star family + (P13a) ~200; maximal bipartite configuration + construction of the FGraph H ~250; Sat/Bl counting ~120; Prop 12 application and both cases ~150. Excludes BMProp12 (~150, counted in s1).)

### `s3:lemL17s` — lemma: Lemma 17^*: sprinkling at density rho (s3.tex:402)

- **Manuscript referee status:** x2+RT; case (b) re-proved via Lemma BBD in v6 (R2): no referee yet
- **Formalization:** Spec EG/Spec/Link/L17s.lean (L17sStatement, in the 'every rho-random subset' form) + proof EG/Proof/Link/L17s.lean; Lib lemmas: the layered space and prefix-conditioning (EG/Lib/Prob/Layers.lean), IsRSubset indicator-vector law (for BBD), the claim (eqL17claim) as a standalone lemma

**Statement (precise restatement).** Let G be a finite simple graph with n := |V(G)| >= 2, L := log_2 n, 2^-7 <= eps' <= 1, s_1 real with G an (eps',s_1)-expander, 0 < rho <= 1, the parameters of (eqStar) for (n, eps', rho) (t plays no role), and assume s_1 >= 8 d_* lambda_*. Call U ⊆ V(G) well-expanding if |N_G(U)| >= theta_*|U|. Then for every rho-random subset V of V(G) (on any finite probability space), every well-expanding U ⊆ V(G) and every F ⊆ E(G) with |F| <= |U|: P(|B^{ell_*}_{G-F}(U,V)| <= |V|/2) <= exp(-7|U|L) (natural exponential, L = log_2 n). (The manuscript states it first for V := V_1 ∪ ... ∪ V_{ell_*} with independent V_i, p_*-random for i < ell_* and q_*-random for i = ell_*, then transfers to every rho-random V because the event is a function of V and the law of the union is that of a rho-random set by (S2). The quantifier order is: for all U, F, the probability bound holds; U = ∅ is trivial.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| parameters ell_*, g_*, p_*, q_*, d_*, lambda_*, Delta_*, sigma_*, theta_* | (eqStar) | s3:eqStar | no: new EG.Star.* (this chunk, EG/Defs/Link/Star.lean) |
| well-expanding | \|N_G(U)\| >= theta_*\|U\| (neighbourhood in G, not in G-F) | s3:lemL17s | yes: EG.FGraph.IsWellExpanding (EG/Defs/Graph.lean) |
| ball B^i_H(U,W) | vertices of W reachable from U by a path through W of length <= i | s1:convGraphs(d) | yes: EG.ball (EG/Defs/Walk.lean); radius ell_* : ℕ |
| rho-random subset | law of V equals rsubset V(G) rho | s3 conventions | yes: EG.FinDist.IsRSubset |
| layers V_1..V_ell and reach sets B_i | Ω_L := Fin ell_* → Finset V with law pi (i ↦ rsubset V(G) (p_* or q_*)); B_i := {v ∈ V(G) : ∃ u ∈ U, path in G-F from u to v of length <= i with interior in V_1 ∪ .. ∪ V_{i-1}} (end unrestricted; NOT EG.ball) | proof of s3:lemL17s (Step 1) | no: proof-internal (Lib) EG.Link.reach (H : FGraph V) (i : ℕ) (U W : Finset V) := H.verts.filter (∃ u ∈ U, ∃ p, IsPathBetween H.edges u v p ∧ IsThrough W p ∧ pathLength p ≤ i) |
| A_i(W) | {v ∈ N_{G-F}(W) : v has a (G-F)-neighbour in W ∩ V_i} | proof of s3:lemL17s (Step 2) | no: proof-internal |
| Prop 13^* | stars or bipartite | s3:propP13s | no: EG.Spec.P13sStatement (this chunk) |
| Lemma BBD | Bernstein bound for bounded differences on a product of Bernoulli coordinates | s1:lemBBD | no: EG.Spec.BBDStatement (s1 blueprint) |
| Chernoff (binomial, Poisson-binomial with mean bounds) | lower tail delta = 1/2; lower tail with mu <= E, delta = 0.09; upper tail delta = 0.09 | s1:citChernoff, s1:citChernoffGen(a) | yes: IsRSubset.chernoff_card_inter_lower_half / _lower, IsRSubset.chernoff_card_upper (EG/Lib/Prob/Chernoff.lean) |

**deps_declared** (manuscript \deps): s3:propP13s, s1:citLem17, s1:lemBBD, s1:citChernoff, s1:citChernoffGen

**deps_from_proof:** s3:propP13s; s1:lemBBD; s1:citChernoff; s1:citChernoffGen; s3:eqStar ((S1),(S2),(S3),(S6); (S4) implicitly: s_1 >= 8dλ >= 48); s1:citDef11 (the expander hypothesis is passed to P13s); s1:convGraphs (balls, N_{G-F})

**deps_notes:** s1:citLem17 is attribution (proof structure) only. (S1),(S2),(S3),(S6) are cited as \ref's to namedlabels s3:eqS1..eqS6, which ms_deps does not list as nodes (see s3:eqStar). BBD enters only in case (b) of Step 2; Chernoff (binomial) in case (a); ChernoffGen(a) in Step 5.

**used_by:** s3:lemP18s (ii) (union bound over well-expanding pairs); s3:thmT16s (declared; used only via s3:lemP18s, and (c) cites the p_* > 0.11 regime)

**randomness:** Statement: an arbitrary finite probability space (μ : FinDist Ω) and a random set R : Ω → Finset V with μ.IsRSubset R G.verts rho; the event {ω | |ball (G-F) ell_* U (R ω)| <= |R ω|/2} is a function of R ω only. Proof: the layered space Ω_L := Fin ell_* → Finset V with law pi (i ↦ rsubset V(G) p_i), p_i = p_* for i < ell_* - 1 (0-based) and q_* = 0.9 rho for the last layer; V := ⋃_i V_i is rho-random by (S2) (StarUnionLawStatement), so μ.prob(event ∘ R) = (rsubset).prob(event) = (layer law).prob(event ∘ union) (prob_map). Conditioning: Step 3 conditions on the prefix (V_1..V_{i-1}), which fixes W = B_i; V_i is still p_*-random (independence of coordinates of pi). Step 5 conditions on (V_1..V_{ell-1}), which fixes B_ell; V_ell is still q_*-random; the event {|V| > 1.09 rho n} is unconditional (V rho-random). Inside the claim (eqL17claim) the only randomness is one p_*-random set V_i with W, F, U fixed: case (a) Binomial(|Cen|, p_*) = |Cen ∩ V_i|; case (b) Z = Ψ((1{w ∈ V_i})_{w ∈ W}) with independent Bernoulli(p_*) coordinates (BBD).

**lean_shape:**

```lean
def EG.Spec.L17sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (ε' s₁ ρ : ℝ) (Ω : Type u) (μ : EG.FinDist Ω) (R : Ω → Finset V),
    G.IsExpander ε' s₁ → 2 ≤ G.card → 2 ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    8 * ((EG.Star.d G.card ρ * EG.Star.lam G.card ρ : ℕ) : ℝ) ≤ s₁ →
    μ.IsRSubset R G.verts ρ →
    ∀ (U : Finset V) (F : Finset (Sym2 V)), U ⊆ G.verts → F ⊆ G.edges → F.card ≤ U.card →
      G.IsWellExpanding (EG.Star.theta G.card ε' ρ) U →
      μ.prob {ω | ((EG.ball (G.deleteEdges F) (EG.Star.ell G.card) U (R ω)).card : ℝ) ≤ ((R ω).card : ℝ) / 2}
        ≤ Real.exp (-(7 * (U.card : ℝ) * Real.logb 2 G.card))
-- Proof-internal Lib (EG/Lib/Link/L17.lean, EG/Lib/Prob/Layers.lean):
--  * reach H i U W, reach_zero (= U), reach_one (= U ∪ nbrSet), reach_mono, (O1) nbr of reach i with a neighbour in reach i ∩ W_i ∈ reach (i+1) W',
--    (O2) reach ell (⋃_{j<ell} V_j) ∩ V_ell ⊆ ball, (O3) θ|U| ≤ |reach 1| (from |F| ≤ |U| and well-expansion);
--  * claim (eqL17claim): ∀ W ⊇ reach₁, W ⊆ V(G), |W| ≤ 2n/3, ∀ (μ', V_i) with IsRSubset V_i V(G) p_*,
--      μ'.prob {|A_i(W, V_i)| < g_*|W|} ≤ exp(-18|U|L);
--  * prefix conditioning on pi over Fin ell: an event {ω | E (prefix ω) (ω i)} with ∀ prefix, prob_{ω i}(E prefix ·) ≤ c has prob ≤ c
--    (from iIndepFun_pi_of_dependsOn + indepFun_iff_map_eq_prod + prob_compProd_le_of_forall / prob_prod);
--  * IsRSubset.map_indicator_eq_pi: IsRSubset V S p, W ⊆ S ⇒ μ.map (fun ω (w : W) => decide (↑w ∈ V ω)) = pi (fun _ => bernoulli p _ _).
```

**hazards:**

- **[risk] L17-LAYER-SPACE.** The proof lives on the ell_*-fold product (ell_* = ⌊2^10 L^3⌋ depends on n) and conditions twice on prefixes ('the set B_i is determined by U, F, V_1..V_{i-1}, so it is independent of V_i..V_ell' — a 'clearly' that hides the Fubini/independence argument). EG/Lib/Prob has compProd/prod slicing (prob_compProd_le_of_forall) and iIndepFun_pi_of_dependsOn, but no ready lemma for 'event depending on coordinates < i and on coordinate i of a pi over Fin ell'. Needed: (1) B_i as a function of (fun j : {j // j < i} => V_j) only (a dependsOn lemma for reach), (2) the split pi ≅ (prefix block) × (coordinate i) × (rest) at the level of laws, (3) the slice bound. Estimated 250 lines of new probability plumbing; the main technical risk of this node.
- **[risk] L17-BBD-TRANSPORT.** (= s1 hazard BBD-TRANSPORT, instantiated here.) BBD is stated on pi (Bernoulli p_k) over a coordinate type; Z is a function of the indicator vector (1{w ∈ V_i})_{w ∈ W} of a p_*-random V_i (itself one coordinate of the layered space, after conditioning). Needed: IsRSubset V_i V(G) p and W ⊆ V(G) ⇒ law of ω ↦ (w : ↥W) ↦ decide (w ∈ V_i ω) is pi (fun _ => bernoulli p) (not in Lib; map_selectSet_pi_rsubset / isRSubset_iff go the other way), then E Z and P(Z <= E Z - a) transported by prob_map/expect_map. Also 'differ in coordinate k ⇒ |ΔΨ| <= deg_H(w_k)' must be proved for Ψ(y) = #{x ∈ X : ∃ w ∈ N_H(x), y_w = 1} (Function.update form).
- **[risk] L17-UNREVIEWED-CASE-B.** Case (b) of Step 2 (BBD application) is new in v6 (R2) and has 'no referee yet' in s1:tabDAG. Re-derived here: c_k = deg_H(w_k) <= Delta_* = b; Σ p(1-p)c_k^2 <= p Delta Σ_w deg_H(w) = p d Delta |X| <= 2 Delta |X| = beta (S6: p d <= 2), beta > 0; a = 0.3|X|; exponent 0.09|X|^2/(2(2Delta|X| + 0.1 Delta|X|)) = 0.09|X|/(4.2 Delta) >= |X|/(47 Delta) (0.021428 > 0.021277); E Z >= (1 - e^{-1})|X| >= 0.63|X| since P(N_H(x) ∩ V_i = ∅) = (1-p)^d <= e^{-pd} <= e^{-1}; exponents: p <= 0.11 ⇒ 2^19/(94·300) = 18.59 >= 18; p > 0.11 ⇒ Delta < 1075, 2^19/(94·1075) = 5.19 >= 5, 5 ell^2 >= 18. No error found; severity 'risk' only because this step has no independent review and its margins are thin (0.7% in 0.09/4.2 vs 1/47; 3% in 18.59 vs 18).
- **[risk] L17-S2-DEPENDENCY.** The transfer 'V_1 ∪ ... ∪ V_ell is rho-random' (S2) is the bridge between the proof's layered space and the Spec's arbitrary rho-random R. Without StarUnionLawStatement (new infrastructure, hazard STAR-S2-UNIONLAW) the Spec form cannot be derived; do not work around it by stating L17s only for the layered space (P18s/T16* need the IsRSubset form because V lives on a product with the colouring).
- **[note] L17-STATEMENT-FORM.** Decision: the Spec is the manuscript's final sentence ('the same bound holds for every rho-random subset V of V(G)'), quantified over an arbitrary finite probability space (Ω, μ) and R with μ.IsRSubset R G.verts rho. The layers are proof-internal. Consumers: s3:lemP18s(ii) (then T16* on the product space colouring × V, with V conditionally rho-random given the colouring: IsRSubset.cond_of_indepFun exists). Universe: Ω : Type u (same as V) suffices for T16*; a separate universe parameter is harmless if the lock tool supports Spec.{u,w}.
- **[note] L17-QUANTIFIERS.** Order: ∀ U, F (fixed, deterministic) then the probability bound for that pair. This is exactly what P18s's union bound over pairs (U', F') needs. It is NOT 'with probability ... for all U, F' (that is P18s(ii)). U = ∅ is well-expanding (0 >= 0) and the bound is 1 (prob_le_one).
- **[note] L17-INCLUSIONS.** U ⊆ V(G) (B_0 = U must consist of vertices; otherwise the one-vertex path [u] puts u ∉ V(G) into the ball, CONVENTIONS) and F ⊆ E(G) (needed by P13s → Prop 12 for |F ∪ F'| <= s|U| inside E(G)) are hypotheses of the manuscript and must stay in the Spec. The random set R ω ⊆ V(G) holds almost surely (IsRSubset.subset_ae); the proof must work on the support (0 < μ.w ω).
- **[note] L17-REACH-NOT-BALL.** B_i (reach set) has its END vertex unrestricted and interior in V_1 ∪ .. ∪ V_{i-1}, whereas EG.ball requires the end in W. Define a separate Lib notion (reach) with (O1)-(O3); (O1)'s 'v does not lie on the path, since otherwise an initial segment would put v into B_i' needs a list lemma: a prefix (List.take) of a path through W is a path through W from the same start, of smaller length (IsPathIn of a prefix; interior of prefix ⊆ interior ∪ {last}).
- **[note] L17-NUMERICS.** Constants to verify by norm_num with Real.exp/Real.log bounds (Real.exp_one_gt_d9, Real.log_two_lt_d9/gt_d9): n > theta >= 2^19 ell^2 L^3 ⇒ rho n > 2^39, 7uL <= 2^{-36} rho n; 0.1·2^19/192 >= 273; 1 - e^{-1} >= 0.63; 0.09/4.2 > 1/47; 2^19/28200 >= 18; 13/0.0121 < 1075; L^3 e^{-11L} <= e^{-11} for L >= 1 (from 3 ln L <= 3(L-1) <= 11(L-1)); 2^10 e^{-11} <= 0.02; ln(1+g) >= g - g^2/2 >= 15g/16 for 0 <= g <= 1/8; (ell-1)g > L - 2^{-9} (needs eps' >= 2^-7); (15/16)(L - 2^{-9}) >= L ln 2 for L >= 1; 0.0081·0.6/2 = 0.00243 >= 1/412; 0.0027 >= 1/412; 1/412 - 1/413 >= 2^{-36}; 2e^{-2^39/413} <= 0.01; 0.02 + 0.01 <= 1. Margins: 0.1% (0.00243 vs 1/412), 0.7% (1/47), otherwise >= 3%. All exact rationals or single exp/log facts.
- **[note] L17-STEP5-MIXED.** Step 5 combines a conditional bound (given V_1..V_{ell-1} with |B_ell| >= 2n/3, V_ell is 0.9rho-random, mean >= 0.6 rho n; ChernoffGen(a) with the mean LOWER bound mu = 0.6 rho n, delta = 0.09) with an unconditional one (|V| ~ Bin(n, rho), upper tail delta = 0.09). The final bound is P(∪E_i^c) + P(E, |B_ell| >= 2n/3, |B_ell ∩ V_ell| < 0.546 rho n) + P(|V| > 1.09 rho n) <= 0.02e^{-7uL} + 0.01e^{-7uL}. Lean: three events and prob_biUnion_le; the middle one via the prefix-conditioning lemma of L17-LAYER-SPACE.
- **[note] L17-P13-CHOICE.** Within the claim, W and F are fixed and P13s gives a disjunction with existential witnesses; choose them with Classical.choose (deterministic in W). The claim must be proved for EVERY fixed W (⊇ B_1, |W| <= 2n/3), not for the random B_i, and then applied slice-wise — this is what makes the case split legitimate.
- **[note] L17-EPS-USE.** eps' >= 2^-7 is used in Step 4 (g_* >= 2^{-10}L^{-2}) and passed to P13s; eps' <= 1 in Step 0 (theta >= 2^19 ell^2 L^3/rho^2), g_* <= 1/8, and P13s. s_1 >= 8 d lambda >= 48 gives |F| <= u <= |W| <= s_1|W|/4.

**effort:** ~1700 new Lean lines, difficulty 4/5 (Spec ~25; reach sets + (O1)-(O3) ~250; claim case (a) ~150; claim case (b) incl. BBD transport, Ψ bounded differences, E Z ~350; layered space, prefix conditioning, Steps 3 and 5 ~450; Step 4 growth ~120; Step 0 + numerics ~200; transfer to arbitrary rho-random R via (S2) ~80; assembly ~80. Excludes StarUnionLaw (counted in s3:eqStar) and BBD itself (s1).)

### `s3:lemP18s` — lemma: Proposition 18^* and Lemma 19^* (s3.tex:595)

- **Manuscript referee status:** x2+RT (fixes RT2-I12: s_1 >= theta_* + 1)
- **Formalization:** Spec EG/Spec/Link/P18s.lean (P18sStatement with conjuncts (i), (ii)) + proof EG/Proof/Link/P18s.lean; (i) via a general Lib lemma for any real theta >= 1

**Statement (precise restatement).** Let G be a finite simple graph with n := |V(G)| >= 2, L := log_2 n, 2^-7 <= eps' <= 1, s_1 real, G an (eps',s_1)-expander, 0 < rho <= 1, parameters (eqStar) for (n, eps', rho), and assume s_1 >= theta_* + 1 (not merely theta_*). (i) (Prop 18^*) For every U ⊆ V(G) with 1 <= |U| <= 2n/3 there is U' ⊆ U with |N_G(U')| >= theta_*|U'| (well-expanding) and |U'| >= eps'|U|/(3 theta_* L^2) (in particular U' ≠ ∅). (ii) (Lemma 19^*) For every rho-random subset V of V(G) (any finite probability space): with probability at least 1 - n^{-6}, the following single event holds: for EVERY nonempty U ⊆ V(G) and EVERY F ⊆ E(G) with |F| <= mu_*|U|, |B^{ell_*}_{G-F}(U,V)| > |V|/2.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| parameters theta_*, mu_*, ell_* and (S4) | (eqStar) | s3:eqStar | no: new EG.Star.* (this chunk) |
| well-expanding | \|N_G(U')\| >= theta_*\|U'\| | s3:lemL17s | yes: EG.FGraph.IsWellExpanding (EG/Defs/Graph.lean) |
| (eps,s)-expander and its min-degree remark | Def 11; remark: delta(G) > s for eps > 0, n >= 2 | s1:citDef11 | yes: EG.FGraph.IsExpander, IsExpander.lt_deg / lt_minDeg (Lib) |
| ball, ball monotone in U | EG.ball; ball_mono_left | s1:convGraphs(d) | yes: EG.ball, EG.ball_mono_left (Lib) |
| rho-random subset | IsRSubset | s3 conventions | yes |

**deps_declared** (manuscript \deps): s1:citProp18, s1:citLem19, s3:lemL17s, s1:citDef11

**deps_from_proof:** s3:lemL17s; s1:citDef11 (expansion in (i); min-degree remark for e_G >= 2 in (ii)); s3:eqStar ((S4): theta >= 8 d lambda, theta >= 1); s1:convGraphs (ball monotonicity)

**deps_notes:** s1:citProp18 and s1:citLem19 are attribution (proof structure) only; the RT2-I12 correction (theta + 1) is built into the hypothesis. (S4) is cited as \ref to a namedlabel (not in ms_deps nodes).

**used_by:** s3:thmT16s (Step 2: applied to each colour class X_i with s_1 = s/(2K_*), union bound over i)

**randomness:** (i) none. (ii) V : Ω → Finset V with μ.IsRSubset V G.verts rho on an arbitrary finite space (μ : FinDist Ω); the event is a function of V only; the proof is a union bound of L17s's per-pair failure probabilities over the finite family {(U', F') : U' ⊆ V(G) nonempty well-expanding, F' ⊆ E(G), |F'| <= |U'|}, then a deterministic consequence on the complement. No conditioning. In T16* the same statement is applied under the conditional law given the colouring (V independent of the colouring).

**lean_shape:**

```lean
def EG.Spec.P18sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (ε' s₁ ρ : ℝ),
    G.IsExpander ε' s₁ → 2 ≤ G.card → 2 ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    EG.Star.theta G.card ε' ρ + 1 ≤ s₁ →
    -- (i) Proposition 18*
    (∀ U : Finset V, U ⊆ G.verts → 1 ≤ U.card → (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 →
      ∃ U' ⊆ U, G.IsWellExpanding (EG.Star.theta G.card ε' ρ) U' ∧
        ε' * U.card / (3 * EG.Star.theta G.card ε' ρ * Real.logb 2 G.card ^ 2) ≤ U'.card) ∧
    -- (ii) Lemma 19*
    (∀ (Ω : Type u) (μ : EG.FinDist Ω) (R : Ω → Finset V), μ.IsRSubset R G.verts ρ →
      1 - (G.card : ℝ) ^ (-6 : ℤ) ≤ μ.prob {ω | ∀ U : Finset V, U ⊆ G.verts → U.Nonempty →
        ∀ F : Finset (Sym2 V), F ⊆ G.edges → (F.card : ℝ) ≤ EG.Star.mu G.card ε' ρ * U.card →
          ((R ω).card : ℝ) / 2 < (EG.ball (G.deleteEdges F) (EG.Star.ell G.card) U (R ω)).card})
-- Lib (general form of (i)): ∀ θ ≥ 1, s₁ ≥ θ + 1, 0 < ε' ≤ 1, 2 ≤ n: ∃ U' ⊆ U, θ|U'| ≤ |N_G(U')| ∧ ε'|U|/(3θL²) ≤ |U'|.
```

**hazards:**

- **[note] P18-THETA-PLUS-ONE.** The hypothesis s_1 >= theta_* + 1 (RT2-I12) is necessary for the proof ((i): |F| <= Σ a_v < (theta+1)|U| needs to be <= s_1|U|). T16* supplies s/(2K_*) >= theta_* + 1. Keep exactly this form.
- **[note] P18-I-MAXIMAL.** (i) takes U' ⊆ U maximal (inclusion) with |N_G(U')| >= theta|U'|; Lean: Finset.exists_maximal on U.powerset.filter (∅ qualifies). The identity |N(U' ∪ {v})| = |N(U')| - 1{v ∈ N(U')} + a_v (a_v = # neighbours of v outside U' ∪ N(U')) needs a small Finset lemma; only the inequality |N(U' ∪ {v})| >= |N(U')| - 1 + a_v is used (to get a_v < theta + 1) together with |N(U' ∪ {v})| >= |N(U')| - 1 (to get |N(U')| < theta(|U'|+1) + 1). Then N_{G-F}(U) ⊆ N_G(U') for F := E_G(U\U', V(G) \ (U' ∪ N(U'))), expansion, and the case U' = ∅ contradiction. The general-theta Lib lemma is cleaner than instantiating theta_* early.
- **[note] P18-EG-COUNT.** The manuscript bounds #{F' ⊆ E(G) : |F'| <= u} <= Σ_{f<=u} e_G^f <= 2e_G^u using e_G >= 2, which it derives from the min-degree remark (delta(G) > s_1 >= 1, needs eps' > 0 and n >= 2: IsExpander.lt_deg). Simpler Lean route with no e_G >= 2: Σ_{f<=u} C(e_G, f) <= (e_G + 1)^u <= n^{2u} (e_G <= n^2/2, so e_G + 1 <= n^2 for n >= 2), and #U' of size u <= C(n,u) <= n^u; total n^{3u} per size as in the manuscript.
- **[note] P18-UNIONBOUND-SUM.** Per pair failure <= e^{-7uL} = n^{-7u/ln 2} <= n^{-10.09u} (7/ln 2 = 10.0989; needs ln 2 <= 0.69375, Real.log_two_lt_d9). Σ_{u>=1} n^{3u} n^{-10.09u} <= n^{-7.09}/(1 - n^{-7.09}) <= n^{-6} for n >= 2 (n^{-1.09} <= 1 - n^{-7.09}). Lean: sum over nonempty subsets U' of V(G) grouped by card, or reuse the exact binomial trick of EG.L15.sum_powerset_erase_pow_le ((1 + n^{-7})^n - 1 style). Also the union bound must range over the finite family of pairs; the complement event implies the deterministic conclusion for all (U, F).
- **[note] P18-DETERMINISTIC-CASES.** Case |U| <= 2n/3, |F| <= 2mu_*|U|: (i) gives U' with |U'| >= eps'|U|/(3theta L^2) = 2mu_*|U| >= |F|, so (U', F) is in the union-bound family (U' ≠ ∅ from |U'| > 0); ball_mono_left. Case |U| > 2n/3: choose Ū ⊆ U with |Ū| = ⌈n/2⌉ = (n+1)/2 (ℕ division), which satisfies 3|Ū| <= 2n for n >= 2 (omega) and |Ū| <= |U| (Finset.exists_subset_card_eq); |F| <= mu n <= 2mu|Ū|. The manuscript's 'check n <= 5 directly' is replaced by the ℕ fact.
- **[note] P18-SINGLE-EVENT.** (ii) is 'with probability >= 1 - n^{-6}, for all U, F' — the quantifiers are INSIDE the event (contrast L17s). T16* Step 4 applies it pointwise to U and F ∩ E(X_i) for the class i with few F-edges; F ranges over subsets of E(G) (for the class graph X_i: E(X_i)).
- **[note] P18-L17-HYP.** L17s needs s_1 >= 8 d_* lambda_*: from (S4) theta_* >= 112p^-2 >= 8 d_* lambda_*, so s_1 >= theta_* + 1 suffices. Also theta_* >= 1 (from (S4)/(S1)) is used in (i). Both come from StarFactsStatement.

**effort:** ~700 new Lean lines, difficulty 3/5 (Spec ~30; (i) general Lib lemma ~220 (maximal subset, neighbourhood identity, F construction, expansion, U' = ∅ case); (ii) counting pairs ~180, union bound sum ~150, deterministic consequence ~120.)
