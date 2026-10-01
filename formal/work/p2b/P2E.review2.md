# P2E, stage 1 (Specs): clean-room review, round 2

Reviewer: a clean-room statement reviewer, round 2 (after fix round 1). I did not edit any Lean
file. Scratch checks are in the session scratchpad (`Scratch2.lean`, outside the repository;
compiles with 0 errors under `lake env lean`).

The proof under formalization is a CANDIDATE proof of the Erdős–Gallai cycle decomposition
conjecture, reviewed only by AI. Nothing below says the conjecture is solved.

**Verdict: approve.** Every Spec and both new Defs items back-translate to the TeX with the two
recorded T0 deviations (HCCglob, CONVENTIONS row `T0-glob-input`) and nothing else. The fix-round-1
actions R1–R6 are in place and correct. No declared input hides a probe node. Lint is clean. The
remarks below are cosmetic or hand-offs; none requires a statement change.

## 0. What I read and ran

- Manuscript v6.1: `s6.tex:16–237` (GATE, defCluster, MED, EQ-LPT, PAR, HCC-P, HCCglob),
  `s6.tex:443–615` (JS-LC, Steps 1–8 and the joint-routing claim), `s1.tex:1489–1500`
  (citEuler), and `s5.tex:252` (the other use of citEuler (a)).
- Files of the unit: `EG/Spec/Chain/{MED,EqLpt,PAR,HCCP,EngineMult}.lean`,
  `EG/Spec/Found/EulerTreeTJoin.lean`, `EG/Proof/Found/EulerTreeTJoin.lean` (stub),
  `EG/Proof/Chain/{HCCUnion,EngineMult,EngineMultTJS}.lean`, `EG/Defs/Probe/P2E/Par.lean`,
  `EGTest/ProbeP2E.lean`; the notes `work/p2b/P2E.md` (incl. "Fix round 1") and `P2E.review1.md`.
- Locked Defs read in full: `EG/Defs/Chain/{Cluster,EqLpt,HCCP}.lean`, `EG/Defs/Components.lean`,
  `EG/Defs/Orient.lean`; the relevant parts of `Graph.lean` (`degE`, `induce`, `restrictEdges`,
  `toSimpleGraph`), `Walk.lean`, `Objects.lean`; the Lib `EG/Lib/Chain/HCCP.lean`
  (`pexc_eq`, `layP_disjoint`, `jcp_iff_jcpOne`) and the lemma list of `EG/Lib/Found/Components.lean`.
- Context: `blueprint_s6a.md` §3 and the MED/EQ-LPT/PAR/HCC-P/HCCglob nodes, `nodes_s6a.json`
  labels, TRIAGE §4 row P-2, `work/p2d/chain.md`, CONVENTIONS (T0 table incl. `T0-glob-input`).
- Ran: `python3 -I scripts/lint.py` (0 findings); `scripts/check.sh EGTest/ProbeP2E.lean`
  (rc=0, 0 errors, 0 sorry); olean freshness of all 13 modules of the unit (all newer than their
  sources, so the author's `lake build`s are current); my scratch file (below).

## 1. Fidelity: back-translation of every Spec and Defs item next to the TeX

### `MedStatement` [s6:lemMED] (a)
TeX: "Let 𝒦 be a parity-clean cluster and ≺ a linear order on U_𝒦. (a) MED(≺) is an admissible
orientation. There is a function pot : A_𝒦 ∪ U_𝒦 → (0,1) that strictly increases along every arc
of MED(≺)."

Lean: for every type V, cluster K, rank rk : V → ℕ with K parity-clean and rk injective on U_K:
`K.medOrient rk` is admissible (an orientation of B_K, acyclic, d⁺ = d⁻ at every hub), and some
pot : V → ℝ has 0 < pot < 1 on V(𝒦) = A ∪ U and pot(x) < pot(y) on every arc (x, y) of `medOrient`.

Checked against the Defs: `medOrient rk` keeps the pairs (x, y) ∈ V(𝒦)² with xy ∈ B and
`medRule`: port x → hub y iff 2·#{w ∈ N_B(y) : rk w ≤ rk x} ≤ |N_B(y)|; hub x → port y iff
|N_B(x)| < 2·#{w ∈ N_B(x) : rk w ≤ rk y}; port x → port y iff rk x < rk y. With no hub–hub bead
(`no_hub_hub`) the neighbours of a hub are ports, so with rk injective on ports the count is the
position i of u_i and the rule is "u_i → h for i ≤ d, h → u_i for i > d" (|N_B(h)| = 2d by parity).
Every linear order of the finite set U_𝒦 is induced by such an rk; rk is never read at hubs.
pot is constrained only on V(𝒦), and all arcs lie in V(𝒦)². **Faithful.**

### `MedExcStatement` [s6:lemMED] (b)
TeX: "(b) For every admissible orientation of 𝒦, in particular for MED(≺), and every port u:
|exc(u)| ≤ deg_{B_𝒦}(u) and exc(u) ≡ deg_{B_𝒦}(u) (mod 2). Moreover ∑_{u∈U_𝒦} exc(u) = 0 and
Φ(𝒦) ≤ b(𝒦)."

Lean: for every parity-clean K and every admissible O: ∀ u ∈ U_K, |exc_O(u)| ≤ deg_B(u) (in ℤ) and
Even(exc_O(u) − deg_B(u)); ∑_{U_K} exc_O = 0 (in ℤ); (load K O : ℝ) ≤ beadCount K, where
beadCount = ∑_h deg_B(h)/2 + |B[U]| is real as in the TeX. The quantifier "for every admissible
orientation" is kept; "parity-clean" is kept (implied by admissibility, so no restriction).
**Faithful.** The parity conjunct is independent of the bound (scratch V6).

### `EqLptExistsStatement`, `EqLptStatement` [s6:lemEQLPT]
TeX: "Let Φ_1 ≥ Φ_2 ≥ … ≥ Φ_m ≥ 0 be loads of m items, and let 1 ≤ k ≤ m. Place the items in the
order 1, …, m into k initially empty layers. Each item goes to a layer of currently minimum load,
and to an empty layer whenever one exists. Then all k layers are non-empty, and the final layer
loads satisfy max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1." Proof: "So the rule is consistent".

Lean: m, k ∈ ℕ, Φ : Fin m → ℝ, 1 ≤ k ≤ m, `Antitone Φ` (= Φ_1 ≥ … ≥ Φ_m), Φ ≥ 0.
- Exists: some σ : Fin m → Fin k with `IsGreedyLPT Φ σ`, i.e. (G1) each item's layer has minimum
  load among all layers counting the earlier items only, and (G2) it is an empty layer (no earlier
  item) whenever one exists.
- Statement: every such σ is surjective, and Φ^lay_j − Φ^lay_{j'} ≤ Φ_0 (= Φ_1) for all j, j'
  (equivalent to max − min ≤ Φ_1 because k ≥ 1).

Ties are arbitrary, so the relation form with "for every greedy placement" is the faithful
reading; the existence conjunct is what the proof asserts and what JS-LC needs. Loads are real
as in the TeX. **Faithful.** Scratch V4: a non-greedy placement violates the spread bound
(loads 3, 2, 1 into 0, 0, 1 gives 5 − 1 = 4 > 3), so the conclusion is not vacuous; V7: for
m = k = 2 with unit loads the identity placement is greedy.

### `ParExistsStatement`, `ParStatement` [s6:lemPAR]; new Defs `oddComps`, `IsParChoice`
TeX: quoted in full in `EG/Spec/Chain/PAR.lean`, matching `s6.tex:105–110`.

Lean, hypotheses: E : Finset (Sym2 V); Va, Vb disjoint; every e ∈ E is s(a, b) with a ∈ Va,
b ∈ Vb (so E is loopless and bipartite with sides Va, Vb; the disjointness is implicit in
"sides" and necessary, PAR-SIDES-DISJOINT).
- `oddComps E` = the components of (V(E), E) (`edgeComps E`: Mathlib components of
  `fromEdgeSet E` meeting V(E)) with an odd number of edges (`compEdges`).
- `IsParChoice E J'`: J' ⊆ E; for every component C of (V(E), E), |J' ∩ E(C)| = 1 if C is odd
  and 0 otherwise; every edge of J' is a non-bridge of E (Mathlib `¬ IsBridge`, i.e. its ends stay
  connected after deleting it) or has an end of E-degree 1. Since every edge of E is in exactly
  one `compEdges`, J' is exactly "one chosen edge per odd component, nothing else"; the
  non-bridge and pendant predicates of the component equal the global ones
  (`isNonBridge_compEdges_iff`, `isPendant_compEdges_iff`, CONVENTIONS).
- Exists: every odd component contains such an edge, and some J' is an admissible choice.
- Statement: for every admissible J': |J'| ≤ #odd; #odd ≤ |V(E)|/2 in ℝ; there are disjoint
  Sa, Sb with Sa ∪ Sb = E ∖ J', deg_{Sa}(v) even for all v ∈ Vb and deg_{Sb}(u) even for all
  u ∈ Va.

**Faithful.** The new Defs file is minimal, correctly placed (`EG/Defs/Probe/P2E/`, module,
`@[expose] public section`), and its docstrings quote the TeX. Scratch V1: `IsParChoice E01 ∅`
is false for the single odd edge 01, so the choice predicate is not trivially satisfied
(`EGTest/ProbeP2E.lean` shows it is satisfiable on the same instance).

### `HccpStatement` [s6:lemHCCP]
Hypotheses: the locked `HccpData.Valid`, which I compared clause by clause with (D), (P), (JC-P)
(k ≥ 1; admissible orientations; B_𝒦 ⊆ E(G); T_j pairwise disjoint; pad ≡ 0 on ⋃ LayP_j if
k = 1; (D) across clusters and cluster/junction; (P); paths of G with head in LayP_j, last in
LayP_{j+1}, interior in T_j; first/last counts dem⁻/dem⁺ with multiplicity; pairwise
edge-disjoint; E(𝒫_j) pairwise disjoint, disjoint from all B_𝒦, B_𝒦 pairwise disjoint).
The uniform k = 1 reading is equivalent to the explicit one (`jcp_iff_jcpOne`).

Conclusion in Lean: ∃ Φ ∈ ℕ with (i) Φ_j = Φ and |𝒫_j| = Φ for all j; (ii) ∃ F_j ⊆ E(𝒫_j) with
E(𝒫_j) ∖ F_j ⊆ E(G[T_j]) (`(G.induce (S.T j)).edges` = edges of G with both ends in T_j), and a
list D with `IsDecomp (beads ∪ ⋃ F_j) D`, |D| ≤ Φ, every object a cycle c (Nodup, ≥ 3 by `WF`)
with max(3, k) ≤ |c| and all its edges in E(G). TeX (i), (ii) verbatim, including the length
bound. **Faithful.**

### `HccUnionStatement` [s6:lemHCCglob] ¶1 (proved, `EG.hccUnion`)
Literal: E_i ⊆ E(G) pairwise disjoint, each with a decomposition D_i ⇒ some D' decomposes ⋃ E_i
with |D'| = ∑ |D_i|. **Faithful**; the proof (concatenation, `isDecomp_finset_biUnion`) is right.

### `HccGlobStatement` [s6:lemHCCglob] ¶2
Lean: q systems, each valid for the same G, with (beads_s ∪ allPathEdges_s) disjoint from
(beads_{s'} ∪ allPathEdges_{s'}) for s ≠ s'. Then: common loads Φ_s; sets F_{s,j} as in
HCC-P (ii); a decomposition of ⋃_s (beads_s ∪ ⋃_j F_{s,j}) into ≤ ∑_s Φ_s objects, all cycles
of G. No cross-system vertex condition (the bowtie test shares a port).

Two deviations, both recorded as T0 in CONVENTIONS (`T0-glob-input`) after round 1: the
input-level disjointness hypothesis (stronger than the literal one, which names the outputs
F_j; it is exactly what JS-LC Step 7 checks, `s6.tex:588–594`) and the extra "cycles of G"
conjunct (what Step 7 reads: "decomposes into at most ∑_𝒮 Φ(𝒮) cycles"). The only manuscript
consumers of HCCglob are JS-LC Step 7 and the remark at `s6.tex:562` (grep of s1–s7). **Accepted.**

### `HccpEndMultStatement` (refutation target, engine part)
Lean: for a valid system S, junction j, vertex u: (1) #{p ∈ 𝒫_j : head p = u ∨ last p = u} ≤
max(dem⁻(u), dem⁺(u)); (2) that max = |exc(u)| + pad(u); (3) u ∈ U_{𝒦_i} ⇒ |exc(u)| ≤ deg_{B_{𝒦_i}}(u).

It encodes JS-LC Step 4 ("Both are at most |exc(u)| + pad(u)"), claim (c) ("at a fixed junction
a port occurs in at most max(dem⁻, dem⁺) pairs of each system containing it. Centres occur in no
pair") and MED(b) as used in Step 4. Reading junction-j pairs as (first, last) of the paths of
𝒫_j is right: pairs have distinct vertices, so a path has two distinct ends. I re-checked truth:
k ≥ 2: a port of LayP_j is a head of exactly dem⁻ paths and never a last vertex
(`layP_disjoint`, `succ_ne_self`); a port of LayP_{j+1} symmetrically; other vertices are no
path end (`path_ends`). k = 1: pad = 0, one of exc⁻, exc⁺ is 0, heads + lasts ≤ |exc|.
(3): `pexc_eq` and `IsOrientation` give |d⁺ − d⁻| ≤ d⁺ + d⁻ = deg_B. Scratch V2 confirms (2) is
an identity for all S, u (as the docstring says); scratch V3 shows (1) is not (it fails for a
non-valid system), so the Spec is not trivial. **Faithful as a proof-internal target.**

### `JsMultNumStatement` (refutation target, numeric part; proved) and `EngineMultTJS`
For M ≥ 2 in ℕ: ⌈(M−1)/2⌉ ≤ ⌈M/2⌉ ≤ M − 1; 2(M−1) = 2M−2; max(2M−2, (M−1)+⌈M/2⌉) = 2M−2;
2M−2 < 2M+2. The claim proof's "For M_l ≥ 2" is the hypothesis. `EG.tJS_eq_two_mul_add_two`
(`Stage1.tJS G run l = 2 * run.M G l + 2`, `rfl`, matches `EG/Defs/Stage1/COL.lean:97`) and
`EG.jsMult_lt_tJS` bridge the literal to t^JS_l (round-1 R3, done). **Faithful.** Scratch V5:
at M = 1 the maximum is 1 ≠ 0 (the T1 wording point, unchanged).

### `EulerTreeTJoinStatement` [s1:citEuler] (a) (declared input)
TeX (`s1.tex:1491`): "Let H be a connected graph and T ⊆ V(H) with |T| even. Every spanning tree S
of H contains a T-join, i.e. a set J ⊆ E(S) such that the vertices of odd J-degree are exactly
the vertices of T."

Lean: H : FGraph V connected on V(H) (Reachable in `toSimpleGraph`), T ⊆ V(H), |T| even;
S ⊆ E(H) with (V(H), S) (= `restrictEdges S`, edge set exactly S) connected on V(H) and
`IsAcyclic`; then ∃ J ⊆ S, ∀ v, Odd(deg_J v) ↔ v ∈ T. Vertices outside V(H) have J-degree 0 and
are not in T, so the "for every v" is consistent. **Faithful**; the standard true fact.

## 2. Vacuity
- Hypotheses of every Spec are satisfied on the instances of `EGTest/ProbeP2E.lean` (re-checked
  by `check.sh`: 0 errors, 0 sorry): MED on K5 and a cherry with a non-MED admissible
  orientation; EQ-LPT with loads 3, 2, 1 and k = 2; PAR on the path 0123 and `IsParChoice` on a
  real odd component; HCC-P on S1 (k = 1) and S2 (k = 2); HCCglob on two systems sharing a
  vertex; Euler on a single edge.
- Conclusions are not trivial: scratch V1 (a wrong PAR choice is rejected), V3 (the path-end
  bound needs `Valid`), V4 (the spread bound fails for a non-greedy placement), V6 (the parity
  conjunct of MED(b) is independent of the bound). The only identity conjunct is (2) of
  `HccpEndMultStatement`, kept on purpose and documented.
- No contradictory hypotheses: `Antitone` + `Φ ≥ 0` + `1 ≤ k ≤ m`, `Disjoint Va Vb` + the edge
  condition, `Valid`, and the Euler hypotheses are all satisfiable as above.

## 3. Declared inputs
- Only `s1:citEuler` (a), stub `EG.eulerTreeTJoin` (the single `sorry` of the unit; grep of all
  unit files). It is really used by the PAR proof (`s6.tex:130`) and stated as in the TeX.
- Nothing the probe must prove is among the inputs: MED, EQ-LPT (+existence), PAR (+existence),
  HCC-P and HCCglob ¶2 are Specs with proofs pending; HCCglob ¶1 is proved; GATE is proved
  already; `s1:factAdd` is replaced by the proved Lib concatenation lemma; citEuler (c) is
  re-proved by GATE. Spanning-tree existence (used implicitly by the PAR proof) is Lib work from
  Mathlib (`SimpleGraph.Connected.exists_isTree_le`), not an input.
- Canonical form (round-1 R5): the only other manuscript use of citEuler (a) is `s5:lemParent`
  Step 3 (`s5.tex:252`), "applied to a spanning tree of each component" of a loop-free spanning
  forest. A spanning tree is a simple graph, so `EulerTreeTJoinStatement` (with H := that tree)
  covers that use as well; no multigraph form of (a) is needed. I confirm the Spec as canonical.

## 4. Hygiene
- `python3 -I scripts/lint.py`: 0 findings. No forbidden tokens.
- All files are modules with the right headers (`@[expose] public section` in Spec/Defs,
  `public section` in Proof). No locked Defs/Spec file was edited; `EG/Defs/Probe/P2E/Par.lean`
  is the one new Defs file and is listed in the status.
- The 13 oleans of the unit are newer than their sources; `check.sh` on the test file passes.
- Docstrings start with manuscript labels; the two proof-internal targets use the pseudo-label
  `[s6:lemJSLC:proof-claim-c]` (round-1 R4), which no script parses.
- Fix round 1 verified: R1 (CONVENTIONS row `T0-glob-input` present, docstring cites it and
  Step 7), R2 (scope paragraph in the `EngineMult` module docstring), R3 (`EngineMultTJS.lean`,
  proved, no sorry), R4 (labels), R5 (canonical note; see §3), R6 (no change, correctly).

## 5. Remarks (none blocking)
**R2-1 (cosmetic).** `IsParChoice`'s first conjunct `J' ⊆ E` is implied by the third
(`IsNonBridge`/`IsPendant` require `e ∈ E`). Harmless; it makes the shape explicit.

**R2-2 (cosmetic, hand-off).** `HccpStatement` keeps the length conclusion `max 3 S.k ≤ |c|`.
I agree with round 1: keep it in the Spec; a count-only corollary for consumers may live in
Lib/Proof, never as a replacement Spec.

**R2-3 (hand-off to P-2 part 2, unchanged from round 1 R2).** The aggregated claim (c) (sum over
all systems of (Y,l), 𝒮_0/cherry exclusivity, ≤ M_l − 1 cherry systems per port with demand ≤ 2,
pad ≤ ⌈(M_l−1)/2⌉) must get its own JS-LC-level Spec in part 2, proved from
`HccpEndMultStatement`, `JsMultNumStatement` and `EG.jsMult_lt_tJS`. The module docstring
records this.

**R2-4 (info for stage 2).** `EqLptExistsStatement` and `ParExistsStatement` carry the full
lemma hypotheses although existence needs fewer; not a weakening (the consumer has them all).

## 6. Math findings
- **No error found** in the engine lemmas. I re-derived: MED (a) (pot(h) = (rk(u_d)+½)/(|U|+1)
  ∈ (0,1); hub in/out-degree d each) and (b) (Φ ≤ ∑_{ports} d⁺ = #{port→hub arcs} + e(B[U]) =
  ∑_h d⁻(h) + e(B[U]) = b, using "no hub–hub bead"); EQ-LPT; PAR (existence of the edge; the
  count; even components after deleting a non-bridge or a pendant edge, including the
  single-edge component; the parity prescription with ∑ p ≡ |E(C′)| ≡ 0 and the T-join);
  HCC-P Steps 0–4 for k = 1, k = 2 (LayP_{j+1} = LayP_{j−1} ≠ LayP_j) and k ≥ 3 (ports are
  sources/sinks of D_j so cancellation touches no port arc; balance at hubs, T-vertices and
  ports; Ψ with blocks [3j, 3j+3); |W| = |𝒫_{k−1}| since last arcs are distinct, end at ports and
  are never cancelled; the block-crossing count ≥ k−1 plus the W-arc); HCCglob.
- **Engine part of JS-LC claim (c), re-derived; no error.** Per system and junction a port is
  in ≤ max(dem⁻, dem⁺) ≤ |exc| + pad pairs; |exc| ≤ deg_{R_Y}(u) ≤ M_l − 1 (Lemma Cap(ii));
  pad ≤ ⌈(M_l−1)/2⌉ because Π_j ≤ Φ^raw_j = ½∑_{LayP_j}|exc| ≤ ½(M_l−1)|LayP_j| and Φ^raw_j ≥ Π_j
  from k_0 ≤ ΣΦ/(2Φ_max); a port is in 𝒮_0 or in ≤ M_l − 1 cherry systems (one cherry per
  class, distinct edges at u), each with demand ≤ 2; so ≤ max(2M_l−2, (M_l−1)+⌈M_l/2⌉) = 2M_l−2 <
  2M_l+2 = t^JS_l for M_l ≥ 2.
- **T1 (confirmed, harmless).** Claim (c) states "= 2M_l − 2" without "M_l ≥ 2"; at M_l = 1 the
  maximum is 1 (scratch V5). The claim's proof says "For M_l ≥ 2" and M_l ≥ 2^40 by (R2).
- **T0 (recorded).** HCCglob ¶2 input-level hypothesis and "cycles" conjunct (`T0-glob-input`).
- **Hazard for part 2 (not this unit).** EQ-USE-EMPTY-S0: with 𝒮_0 = ∅ the formula for k_0
  divides by Φ_max = 0 and EQ-LPT needs m ≥ 1; JS-LC's Lean proof must case-split.
