# P2E, stage 1 (Specs): clean-room review, round 1

Reviewer: a clean-room statement reviewer, round 1. I did not edit any Lean file. Scratch checks are in `/tmp/p2erev/Scratch.lean`, outside the repository.

The proof under formalization is a CANDIDATE proof of the Erdős–Gallai cycle decomposition conjecture, reviewed only by AI. Nothing below says the conjecture is solved.

**Verdict: approve.** There is no fidelity defect in any Spec or in the new Defs. The remarks below are minor or cosmetic. One remark (R2, on the refutation target) is a to-do for P-2 part 2.

## 0. What I read

- The manuscript v6.1: `s6.tex:1–237` (GATE, defCluster, MED, EQ-LPT, PAR, HCC-P, HCCglob), `s6.tex:443–615` (JS-LC Steps 1–8 and the joint-routing claim), and `s1.tex:1489` (citEuler).
- The Specs:
  - `EG/Spec/Chain/{MED,EqLpt,PAR,HCCP,EngineMult}.lean`;
  - `EG/Spec/Found/EulerTreeTJoin.lean`;
  - the stub `EG/Proof/Found/EulerTreeTJoin.lean`;
  - the proved `EG/Proof/Chain/{HCCUnion,EngineMult}.lean`;
  - the NEW Defs file `EG/Defs/Probe/P2E/Par.lean`.
- The locked Defs used:
  - `Chain/Cluster`, `Chain/EqLpt`, `Chain/HCCP`;
  - `Components`, `Orient`, `Objects`, `Walk`;
  - `Graph` (`FGraph`, `induce`, `restrictEdges`, `toSimpleGraph`, `degE`).
- The context: `blueprint_s6a.md` §3 (hazard index), TRIAGE §4 row P-2, and `EGTest/ProbeP2E.lean`.

## 1. Fidelity: each Spec in plain words, next to the TeX

### `MedStatement` [s6:lemMED] (a)
TeX: "Let 𝒦 be a parity-clean cluster and ≺ a linear order on U_𝒦. (a) MED(≺) is an admissible orientation. There is a function pot : A_𝒦 ∪ U_𝒦 → (0,1) that strictly increases along every arc of MED(≺)."

Lean, in plain words: take any type V, cluster K and rank rk : V → ℕ, with K parity-clean and rk injective on U_K. Then:
- `medOrient rk` is an orientation of B_K, it is acyclic, and it has d⁺ = d⁻ at every hub;
- some pot : V → ℝ has 0 < pot < 1 on A_K ∪ U_K and pot(x) < pot(y) for every arc (x, y) of `medOrient rk`.

I checked the Defs side of `medOrient`:
- `medPos` is #{w ∈ N_B(h) : rk w ≤ rk u};
- the arc u→h holds iff 2·pos ≤ deg(h);
- the arc h→u holds iff deg(h) < 2·pos;
- a port–port bead is oriented upwards in rk.

With rk injective on the ports and N_B(h) ⊆ ports (no hub–hub bead), this is exactly "u_i → h for i ≤ d, h → u_i for i > d". Every linear order of the finite set U_𝒦 is induced by such an rk. Every arc lies in V(𝒦) × V(𝒦), so pot needs to be constrained only on V(𝒦).

**Faithful.**

### `MedExcStatement` [s6:lemMED] (b)
TeX: "(b) For every admissible orientation of 𝒦, in particular for MED(≺), and every port u: |exc(u)| ≤ deg_{B_𝒦}(u) and exc(u) ≡ deg_{B_𝒦}(u) (mod 2). Moreover ∑_{u∈U_𝒦} exc(u) = 0 and Φ(𝒦) ≤ b(𝒦)."

Lean, in plain words: for every parity-clean K and every admissible O:
- ∀ u ∈ U_K, |exc_O(u)| ≤ deg_B(u) in ℤ, and exc_O(u) − deg_B(u) is even;
- ∑_{U_K} exc_O = 0;
- (load K O : ℝ) ≤ beadCount K.

Here b(𝒦) is the real ∑_h deg/2 + |B[U]|, as in the TeX. The quantifier "for every admissible orientation" is kept.

**Faithful.**

### `EqLptExistsStatement`, `EqLptStatement` [s6:lemEQLPT]
TeX: "Let Φ_1 ≥ … ≥ Φ_m ≥ 0 … 1 ≤ k ≤ m … Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists … Then all k layers are non-empty, and … max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1." Proof: "So the rule is consistent".

Lean, in plain words: take m, k ∈ ℕ and a real Φ : Fin m → ℝ with 1 ≤ k ≤ m, Φ antitone and Φ ≥ 0.
- (Exists) Some σ : Fin m → Fin k satisfies `IsGreedyLPT`.
- (Statement) Every σ satisfying `IsGreedyLPT` is surjective and has layerLoad j − layerLoad j' ≤ Φ_0 for all j, j'.

`IsGreedyLPT` (G1) puts each item in a layer whose load, counting only earlier items, is minimum. (G2) puts it in an empty layer whenever one exists, where "empty" counts earlier items, not load. So a zero-load item still makes its layer non-empty, which is the TeX meaning of "empty".

The loads are real, as in the TeX. The pairwise-difference form is equivalent to max − min, since k ≥ 1. The statement quantifies over every greedy placement, which is the faithful reading because ties are arbitrary.

A scratch check (`/tmp/p2erev/Scratch.lean`, compiles) shows the relation is not trivial: with m = k = 2 and unit loads, "both items into layer 0" is not greedy.

**Faithful.**

### `ParExistsStatement`, `ParStatement` [s6:lemPAR]; the new Defs `oddComps`, `IsParChoice`
TeX: quoted in the Spec file; the quotation matches `s6.tex:105`.

Lean, in plain words: take E a Finset of edges and Va, Vb disjoint, with every e ∈ E of the form s(a, b), a ∈ Va, b ∈ Vb.
- (Exists) Every odd component C of (V(E), E) has an edge of E(C) that is a non-bridge of E or has an end of E-degree 1. Also, some J' satisfies `IsParChoice E J'`.
- (Statement) For every J' with `IsParChoice E J'`:
  - |J'| ≤ #odd;
  - #odd ≤ |V(E)|/2, in ℝ;
  - there are disjoint Sa, Sb with Sa ∪ Sb = E ∖ J', deg_{Sa}(v) even for every v ∈ Vb, and deg_{Sb}(u) even for every u ∈ Va.

`IsParChoice E J'` requires:
- J' ⊆ E;
- for every component C of (V(E), E), |J' ∩ E(C)| = 1 if |E(C)| is odd and 0 otherwise;
- every edge of J' is a non-bridge of E or a pendant edge of E.

This is "one chosen edge in each odd component, a non-bridge or pendant edge of that component, J' = the set of chosen edges":
- every edge of E lies in some `compEdges E C` with C ∈ `edgeComps E`, so J' has no stray edges;
- the non-bridge and pendant predicates of the component equal the global ones, since a bridge is a property of its component and the degree in a component equals the degree in E.

`oddComps` is `edgeComps` filtered by odd `compEdges`, and it excludes the isolated Mathlib components outside V(E).

The disjointness of the sides is necessary and implicit in "bipartite with sides V_a, V_b" (PAR-SIDES-DISJOINT). "For *every* such choice" is kept (PAR-FORALL-CHOICE). The partition may have empty parts, which is standard.

**Faithful.** The new Defs file is well placed (`EG/Defs/Probe/P2E/`, module, `@[expose] public section`), minimal and correct.

### `HccpStatement` [s6:lemHCCP]
The hypotheses are the locked `HccpData.Valid`. I compared it clause by clause with (D), (P) and (JC-P). Every clause is present.
- The uniform k = 1 reading is justified by `jcp_iff_jcpOne`.
- One-vertex paths cannot occur:
  - for k ≥ 2, `layP j` and `layP (succ j)` are disjoint;
  - for k = 1, such a path would need exc⁻ ≥ 1 and exc⁺ ≥ 1 with pad = 0.

  So the `IsPathIn` caveat is harmless.

Conclusion in Lean, in plain words: there is Φ ∈ ℕ such that:
- (i) Φ_j = Φ and |𝒫_j| = Φ for every j;
- (ii) there is F_j ⊆ E(𝒫_j) with E(𝒫_j) ∖ F_j ⊆ E(G[T_j]), and a list D with `IsDecomp (beads ∪ ⋃F_j) D`;
- |D| ≤ Φ;
- every object of D is a cycle c (Nodup, ≥ 3 vertices, by `IsDecomp`'s WF) with max(3, k) ≤ |c| and E(c) ⊆ E(G).

This matches TeX (i) and (ii), including the length bound, which the author rightly kept (H3). Splitting the length bound into its own Spec would be acceptable only if `HccpStatement` itself stays whole.

**Faithful.**

### `HccUnionStatement` [s6:lemHCCglob] ¶1
Literal: E_i ⊆ E(G), pairwise disjoint, `IsDecomp (E i) (D i)` ⇒ ∃ D' with `IsDecomp (⋃E_i) D'` and |D'| = ∑|D_i|. **Faithful.** It is proved by `hccUnion`, whose proof I checked.

### `HccGlobStatement` [s6:lemHCCglob] ¶2
Lean, in plain words: take q systems, each valid for the same G, with beads_s ∪ allPathEdges_s disjoint from beads_{s'} ∪ allPathEdges_{s'} for s ≠ s'. Then:
- there are Φ_s with Φ_{s,j} = Φ_s;
- there are F_{s,j} as in HCC-P (ii);
- there is D decomposing ⋃_s(beads_s ∪ ⋃_j F_{s,j}), with |D| ≤ ∑_s Φ_s and all objects cycles of G.

No vertex condition across systems is assumed; the bowtie test shares port 0. See R1 for the two T0 deviations. I **accept** them.

### `HccpEndMultStatement` (refutation target, engine part)
Lean, in plain words: for a valid system S, a junction j and any vertex u:
- #{p ∈ 𝒫_j : head p = u or last p = u} ≤ max(dem⁻(u), dem⁺(u));
- max(dem⁻(u), dem⁺(u)) = |pexc u| + pad u;
- if u ∈ U_{𝒦_i}, then |pexc u| ≤ deg_{B_{𝒦_i}}(u).

I checked that it is true:
- k ≥ 2: a port of layer j is only a head at junction j (by `path_ends` and `D_KK`, since `succ j ≠ j`);
- k = 1: pad = 0 and at most one of exc⁻, exc⁺ is non-zero, so heads + lasts ≤ exc⁻ + exc⁺ = |exc|;
- non-ports occur in no path end;
- `pexc` reads the unique cluster, by `D_KK`, and IsOrientation gives |exc| ≤ out + in = deg_B.

It encodes JS-LC "at a fixed junction a port occurs in at most max(dem⁻, dem⁺) pairs of each system containing it. Centres occur in no pair" together with Step 4's "|exc(u)| ≤ deg_{B_𝒦}(u)", reading pairs as (first, last) path ends.

**Faithful as a proof-internal target.** Note that its second conjunct is an identity.

### `JsMultNumStatement` (refutation target, numeric part)
For every M ≥ 2:
- ⌈(M−1)/2⌉ ≤ ⌈M/2⌉ ≤ M − 1;
- 2(M−1) = 2M − 2;
- max(2M − 2, (M−1) + ⌈M/2⌉) = 2M − 2;
- 2M − 2 < 2M + 2.

This is claim (c)'s arithmetic, with the claim proof's "For M_l ≥ 2" made a hypothesis. **Faithful.** It is proved, and I checked the ceiling helpers.

### `EulerTreeTJoinStatement` [s1:citEuler] (a) (declared input)
TeX (`s1.tex:1491`): "Let H be a connected graph and T ⊆ V(H) with |T| even. Every spanning tree S of H contains a T-join, i.e. a set J ⊆ E(S) such that the vertices of odd J-degree are exactly the vertices of T."

Lean, in plain words:
- H is connected on V(H), T ⊆ V(H), and |T| is even;
- S ⊆ E(H), with (V(H), S) connected on V(H) and acyclic;
- then ∃ J ⊆ S with ∀ v, deg_J(v) odd ↔ v ∈ T.

**Faithful.** It is the standard, true fact.

## 2. Vacuity
- Every Spec's hypotheses are satisfied in `EGTest/ProbeP2E.lean`:
  - MED: K5, and the cherry with a non-MED admissible orientation;
  - EQ-LPT: loads 3, 2, 1 with k = 2;
  - PAR: the path 0123;
  - `IsParChoice`: on a real odd component with a pendant edge;
  - HCC-P: S1 (k = 1) and S2 (k = 2);
  - HCCglob: two systems sharing a vertex;
  - Euler: on a single edge.
- None of the conclusions is trivial, except the identity conjunct noted above for `HccpEndMultStatement`.
- Scratch checks (`/tmp/p2erev/Scratch.lean`, compiles with 0 errors):
  - `IsGreedyLPT` rejects a non-greedy placement;
  - at M = 1 the claim-(c) maximum is 1 ≠ 2M − 2 = 0, which confirms the T1 wording point (§4).

## 3. Declared inputs
- The only input is s1:citEuler (a). It is really used: `s6.tex` PAR proof, "By Cited result s1:citEuler, a spanning tree of the connected graph C′ contains a T-join". It is stated as in the TeX.
- No probe node is hidden among the inputs:
  - MED, EQ-LPT, PAR, HCC-P and HCCglob are all probe Specs with proofs pending;
  - GATE is already proved;
  - s1:factAdd is replaced by the proved Lib lemma `isDecomp_finset_biUnion`.
- The list is minimal.

## 4. Hygiene
- `python3 -I scripts/lint.py`: 0 findings.
- All files are modules, with the right section headers.
- The only `sorry` is the DECLARED INPUT stub `EG.eulerTreeTJoin`.
- Docstrings start with the manuscript labels and quote the TeX.

## 5. Remarks

**R1 (minor, T0; accept): HccGlob.**
(a) The input-level disjointness hypothesis is formally *stronger* than the literal TeX hypothesis, since F ⊆ E(𝒫). So the Spec is weaker than a literal reading. The literal TeX hypothesis quantifies over outputs of HCC-P and is not well-formed as a hypothesis. Its only sensible literal reading ("for the F_j produced, if they are disjoint …") is `HccUnionStatement` applied to per-system `HccpStatement` outputs, which the formalization also provides.
I checked JS-LC Step 7 (`s6.tex:580ff`). It verifies exactly the input-level condition:
- bead sets are disjoint;
- path edges are disjoint "within one (Y,l) and one j … for different j … for different Y ≠ Y′";
- "Path edges are disjoint from beads".

So no consumer loses anything.
(b) The extra "cycles of G" conjunct in the conclusion is a strengthening, and it is true, since the decomposition is the concatenation of HCC-P outputs. It is what Step 7 and J⁺ read ("decomposes into at most ∑Φ(𝒮) cycles"; "HCC-P output consists of cycles only").
Suggestion: record this as a T0 row in CONVENTIONS ("T0-glob-input").

**R2 (minor; to-do for part 2): the refutation target is hit only per system.** The load-bearing claim (c), "every vertex lies in at most 2M_l − 2 ≤ t pairs of 𝔓_j(Y,l)", aggregates over all systems of (Y,l). The aggregation needs three facts:
- the S₀/cherry exclusivity;
- ≤ M_l − 1 cherry systems per port, each with demand ≤ 2;
- Step 4's padding spread pad ≤ ⌈(M_l − 1)/2⌉, from Φ^raw_j = ½∑|exc| ≤ ½(M_l − 1)|LayP_j|.

None of these is a Spec in this unit. `HccpEndMultStatement` follows from `Valid` + MED(b) alone. Part 2 of P-2 must state the aggregated bound as its own Spec, e.g. a JS-LC-level `JointMultStatement`, so that the target is really hit. I re-derived the aggregation by hand and found no error (§6).

**R3 (cosmetic).** `JsMultNumStatement` writes t as the literal `2 * M + 2`, not `EG.Stage1.tJS`, which depends on the run. This is fine. Part 2 should link it with a one-line lemma `tJS = 2 * run.M G l + 2`, which is true by `rfl`.

**R4 (cosmetic).** `HccpEndMultStatement` and `JsMultNumStatement` carry docstrings tagged `[s6:lemJSLC]` although they are proof-internal facts, not the lemma. Tools that map labels to statements should not mistake them for the JS-LC Spec. A prefix such as `[s6:lemJSLC:proof]` would disambiguate.

**R5 (cosmetic).** `EulerTreeTJoinStatement` is the first Lean statement of s1:citEuler (a). EUL-MULTI-USE (TRIAGE) plans a multigraph form in Lib. The integrator should make this Spec the canonical (a), or bridge the two, so that the input is not declared twice.

**R6 (cosmetic).** `EqLptExistsStatement` keeps `Antitone`, `k ≤ m` and `Φ ≥ 0`, which existence does not need (H6). This is harmless: the consumer has all three. It is not a weakening.

## 6. Math findings
- **T1 (already noted by the author; I confirm it).** JS-LC claim (c) states "max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2" without "M_l ≥ 2". At M_l = 1 the left side is 1 (checked in Lean). The claim proof says "For M_l ≥ 2", and M_l ≥ 2^40 holds by (R2). This is harmless wording.
- **T0 (HccGlob ¶2).** The hypothesis refers to the outputs F_j. The input-level reading is the one JS-LC checks (R1).
- **No error found in the following re-derivations.**
  - MED (a) and (b): the hub potential (rk(u_d) + ½)/(|U| + 1) ∈ (0,1) because rk(u_d) ≤ |U| − 1; and Φ ≤ ∑d⁺(ports) = b.
  - EQ-LPT.
  - PAR: existence of the edge; the count; the even components after deletion; the parity prescription with ∑p ≡ |E(C′)| ≡ 0.
  - HCC-P: Step 0, Step 1 for k = 1, k = 2 and k ≥ 3, the balance of Step 2, Ψ and |W| = Φ, and the block-crossing bound ≥ k.
  - HCCglob.
  - The engine part of JS-LC claim (c), including the pad spread and the cherry demand ≤ 2 = |exc| + pad with pad ≤ 1.
