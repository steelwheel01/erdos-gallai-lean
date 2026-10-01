# P2E: probe P-2, part 1 (the s6a routing engine). Stage 1: the statements

Unit P2E, stage 1: the Specs, the declared-input stubs and the non-vacuity tests. The proofs come in stage 2; this stage proves only two trivial statements. The proof being formalized is a CANDIDATE proof of the Erdős–Gallai cycle decomposition conjecture. It has been reviewed only by AI, so nothing here says the conjecture is solved.

Sources:
- the manuscript v6.1 `proofs/manuscript/s6.tex`, lines 16–237 and 443–600 (JS-LC, for the refutation target), and `s1.tex:1489` (s1:citEuler);
- `work/p2/blueprint_s6a.md` and `nodes_s6a.json`;
- `work/p2/TRIAGE.md` §4, row P-2;
- `work/p2d/chain.md`.

## 1. Status

| file | content | state |
|---|---|---|
| `EG/Spec/Chain/MED.lean` | `MedStatement`, `MedExcStatement` | compiles |
| `EG/Spec/Chain/EqLpt.lean` | `EqLptExistsStatement`, `EqLptStatement` | compiles |
| `EG/Spec/Chain/PAR.lean` | `ParExistsStatement`, `ParStatement` | compiles |
| `EG/Spec/Chain/HCCP.lean` | `HccpStatement`, `HccUnionStatement`, `HccGlobStatement` | compiles |
| `EG/Spec/Chain/EngineMult.lean` | `HccpEndMultStatement`, `JsMultNumStatement` (the refutation target) | compiles |
| `EG/Spec/Found/EulerTreeTJoin.lean` | `EulerTreeTJoinStatement` (declared input) | compiles |
| `EG/Proof/Found/EulerTreeTJoin.lean` | `EG.eulerTreeTJoin` (DECLARED INPUT stub, `sorry`) | compiles, 1 sorry (allowed) |
| `EG/Proof/Chain/HCCUnion.lean` | `EG.hccUnion : HccUnionStatement` | **proved** (trivial: Lib `isDecomp_finset_biUnion`) |
| `EG/Proof/Chain/EngineMult.lean` | `EG.jsMultNum : JsMultNumStatement`, ceiling helpers | **proved** (numeric) |
| `EG/Proof/Chain/EngineMultTJS.lean` | `EG.tJS_eq_two_mul_add_two`, `EG.jsMult_lt_tJS` (bridge to `Stage1.tJS`; fix round 1) | **proved** |
| `EG/Defs/Probe/P2E/Par.lean` | NEW Defs: `EG.Chain.oddComps`, `EG.Chain.IsParChoice` | compiles |
| `EGTest/ProbeP2E.lean` | non-vacuity tests | compiles, 0 sorry |

Checks run:
- `lake build` on each module above;
- `scripts/check.sh EGTest/ProbeP2E.lean`: 0 errors and 0 sorry;
- `python3 -I scripts/lint.py`: 0 findings;
- the axiom scan of `EG.Proof.Chain.EngineMult`, `EG.Proof.Chain.HCCUnion` and `EG.Proof.Found.EulerTreeTJoin` (448 constants): the only `sorryAx` is `EG.eulerTreeTJoin`, the declared input.

## 2. Nodes: manuscript label → Lean

| label | Lean statement | proof (stage 2) | notes |
|---|---|---|---|
| `s6:lemMED` (a) | `EG.Spec.MedStatement` | todo | for the concrete `K.medOrient rk` |
| `s6:lemMED` (b) | `EG.Spec.MedExcStatement` | todo | for every admissible `O` |
| `s6:lemEQLPT` | `EG.Spec.EqLptStatement` | todo | for every greedy placement |
| `s6:lemEQLPT` (existence: "the rule is consistent") | `EG.Spec.EqLptExistsStatement` | todo | |
| `s6:lemPAR` | `EG.Spec.ParStatement` | todo | for every admissible choice `J'` |
| `s6:lemPAR` (existence: "such an edge exists") | `EG.Spec.ParExistsStatement` | todo | the edge, and hence a choice `J'` |
| `s6:lemHCCP` | `EG.Spec.HccpStatement` | todo | (i) and (ii), including the length bound `max(3,k)` |
| `s6:lemHCCglob` ¶1 | `EG.Spec.HccUnionStatement` | **done** (`EG.hccUnion`) | |
| `s6:lemHCCglob` ¶2 | `EG.Spec.HccGlobStatement` | todo | input-level disjointness (TRIAGE) |
| refutation target (JS-LC Step 4, claim (c), engine part) | `EG.Spec.HccpEndMultStatement` | todo | uses MED(b) and (D) |
| refutation target (JS-LC claim (c), numeric part) | `EG.Spec.JsMultNumStatement` | **done** (`EG.jsMultNum`) | |
| `s6:lemGATE` | existing `EG.Spec.GateStatement` / `GatePreciseStatement` | done before this unit | used by HCC-P |

## 3. Declared inputs

| label | Spec | stub | why |
|---|---|---|---|
| `s1:citEuler` (a) | `EG.Spec.EulerTreeTJoinStatement` (`EG/Spec/Found/EulerTreeTJoin.lean`) | `EG.eulerTreeTJoin` (`EG/Proof/Found/EulerTreeTJoin.lean`) | Cited by the proof of PAR (s6.tex:130, "By Cited result s1:citEuler, a spanning tree of the connected graph `C'` contains a `T`-join"). It is a stage-α cited result (standard). No Lean statement of it existed. |

Kept out of the list, on purpose:
- **`s1:factAdd`**, cited by HCCglob. Its list form is already proved in `EG.Lib.Found.Fnum` (`isDecomp_finset_biUnion`, `exists_isDecomp_biUnion`), so it needs no declaration.
- **`s6:lemGATE`**, used by HCC-P. It is already proved (`EG.gate`, `EG.gate_precise`, `EG.gate_with_cycles`).
- **MED**, used by HCC-P Step 0 and by the engine multiplicity bound. It is a probe node.
- **`s1:citEuler` (c)** (balanced digraphs). GATE re-proves it.

Stage 2 may also prove PAR without the input (blueprint PAR-DIRECT-PROOF-OPTION: build the parity subgraph by induction). The stub then becomes unused and can be dropped.

## 4. Defs used, and the new Defs file

Locked Defs used:
- `EG.Defs.Chain.Cluster`: `Cluster`, `exc`, `excPos`, `excNeg`, `verts`, `beadCount`, `ParityClean`, `IsAdmissible`, `load`, `medOrient`;
- `EG.Defs.Chain.EqLpt`: `IsGreedyLPT`, `layerLoad`;
- `EG.Defs.Chain.HCCP`: `HccpData`, `Valid`, `layP`, `pexc`, `demMinus`, `demPlus`, `Phi`, `pathEdges`, `allPathEdges`, `beads`, `succ`;
- `EG.Defs.Components`: `edgeVerts`, `edgeGraph`, `edgeComps`, `compEdges`, `IsNonBridge`, `IsPendant`;
- `EG.Defs.Orient`, through Cluster;
- `EG.Defs.Graph`: `FGraph`, `degE`, `induce`, `restrictEdges`, `toSimpleGraph`;
- `EG.Defs.Objects`: `Obj`, `IsDecomp`, `cycleEdges`.

**New Defs file** `EG/Defs/Probe/P2E/Par.lean` (module, `@[expose] public section`). The integrator flagged these two predicates as missing in `work/p2d/chain.md` ("Not in this task; flagged for the integrator").
- `EG.Chain.oddComps E`: the components of `(V(E), E)` with an odd number of edges.
- `EG.Chain.IsParChoice E J'`: three conditions.
  - `J' ⊆ E`.
  - Every component `C` of `(V(E), E)` satisfies `|J' ∩ E(C)| = 1` if `C` is odd, and `0` otherwise.
  - Every edge of `J'` is a non-bridge or a pendant edge.

  Every edge of `E` lies in `compEdges` of a component in `edgeComps E`, so `J'` has no edge outside the odd components. "Non-bridge / pendant of that component" is the global predicate, by `isNonBridge_compEdges_iff` and `isPendant_compEdges_iff` (CONVENTIONS).

P-2 part 2 (Lemma J⁺, J^par edges "for every choice") needs `IsParChoice` too, which is why it is a Defs file and not a Spec-local definition.

## 5. Back-translation: each Spec next to its TeX

### `MedStatement` [s6:lemMED] (a)
TeX: "Let `𝒦` be a parity-clean cluster and `≺` a linear order on `U_𝒦`. (a) `MED(≺)` is an admissible orientation. There is a function `pot : A_𝒦 ∪ U_𝒦 → (0,1)` that strictly increases along every arc of `MED(≺)`."

Lean, in plain words: for every type `V`, cluster `K` and `rk : V → ℕ`, if `K` is parity-clean and `rk` is injective on the ports, then:
- `medOrient rk` is an admissible orientation of `K` (an orientation of the beads, acyclic, with `d⁺ = d⁻` at every hub);
- some real function `pot` takes values in `(0,1)` on `V(𝒦)` and satisfies `pot(x) < pot(y)` for every arc `x → y` of `medOrient rk`.

Faithfulness:
- The linear orders of the finite set `U_𝒦` are exactly the orders induced by ranks that are injective on `U_𝒦`, and `medOrient` reads `rk` only through the comparisons `≤` and `<`.
- `pot` is defined on all of `V`, but only its values on `V(𝒦)` are constrained. Every arc has both ends in `V(𝒦)`.

### `MedExcStatement` [s6:lemMED] (b)
TeX: "(b) For every admissible orientation of `𝒦`, in particular for `MED(≺)`, and every port `u`: `|exc(u)| ≤ deg_{B_𝒦}(u)` and `exc(u) ≡ deg_{B_𝒦}(u) (mod 2)`. Moreover `∑_{u∈U_𝒦} exc(u) = 0` and `Φ(𝒦) ≤ b(𝒦)`."

Lean, in plain words: for every parity-clean cluster `K` and every admissible orientation `O` of it:
- every port `u` has `|exc(u)| ≤ deg_B(u)` (in ℤ), and `exc(u) − deg_B(u)` is even;
- the sum of `exc` over the ports is `0`;
- the load `Φ(𝒦) = ∑ exc⁺ ∈ ℕ`, cast to ℝ, is at most the real bead count `b(𝒦)`.

The standing hypothesis "parity-clean" is kept; admissibility implies it anyway.

### `EqLptExistsStatement` / `EqLptStatement` [s6:lemEQLPT]
TeX: "Let `Φ_1 ≥ … ≥ Φ_m ≥ 0` be loads of `m` items, and let `1 ≤ k ≤ m`. Place the items in the order `1, …, m` into `k` initially empty layers. Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists. Then all `k` layers are non-empty, and the final layer loads satisfy `max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1`." Proof: "So the rule is consistent".

Lean, in plain words: for `m, k ∈ ℕ` and real loads `Φ : Fin m → ℝ` with `1 ≤ k ≤ m`, `Φ` non-increasing and nonnegative:
- **(Exists)** some placement `σ : Fin m → Fin k` satisfies the greedy relation. The relation says: each item goes to a layer of minimum load before it, and to a layer that is empty before it whenever one exists.
- **(Statement)** every greedy placement `σ` is surjective (every layer is used), and any two final layer loads differ by at most `Φ_1` (index 0).

Faithfulness:
- "Place ... greedy" is non-deterministic (ties are arbitrary), so the Lean form is a relation, and the lemma holds for every placement satisfying it.
- `max − min ≤ Φ_1` is equivalent to "all pairwise differences are `≤ Φ_1`", since `k ≥ 1`.

### `ParExistsStatement` / `ParStatement` [s6:lemPAR]
TeX: quoted in full in `EG/Spec/Chain/PAR.lean`.

Lean, in plain words: let `E` be a finite edge set and `V_a`, `V_b` disjoint vertex sets such that every edge of `E` is `ab` with `a ∈ V_a` and `b ∈ V_b`.
- **(Exists)** Every odd component of `(V(E), E)` contains an edge of `E` that is a non-bridge or a pendant edge. Consequently some `J'` is an admissible choice.
- **(Statement)** For every admissible choice `J'`, three things hold.
  - `|J'| ≤` #odd components.
  - #odd components `≤ |V(E)|/2`, in ℝ.
  - There are disjoint `S_a`, `S_b` with `S_a ∪ S_b = E ∖ J'`, every vertex of `V_b` having even `S_a`-degree and every vertex of `V_a` having even `S_b`-degree.

Faithfulness:
- "Bipartite graph with sides `V_a, V_b`" is the disjointness of the sides plus the edge condition. Without disjointness the lemma is false (PAR-SIDES-DISJOINT).
- The existence statement carries the lemma's bipartite hypotheses unchanged.

### `HccpStatement` [s6:lemHCCP]
TeX: the data and (D), (P), (JC-P) are quoted field by field in `EG.Chain.HccpData.Valid`. The conclusions: "(i) all `Φ_j` are equal to a common value `Φ`, and `Φ = |𝒫_j|` for every `j`; (ii) there are sets `F_j ⊆ E(𝒫_j)` with `E(𝒫_j) ∖ F_j ⊆ E(G[T_j])` such that `⋃_𝒦 B_𝒦 ∪ ⋃_j F_j` decomposes into at most `Φ` cycles of `G`, each of length at least `max(3,k)`."

Lean, in plain words: for every graph `G` and every HCC-P system `S` valid for `G`, there is `Φ ∈ ℕ` with the following properties.
- `Φ_j = Φ` and `|𝒫_j| = Φ` for every `j`.
- There are `F_j` with `F_j ⊆ E(𝒫_j)` and `E(𝒫_j) ∖ F_j ⊆ E(G[T_j])`.
- There is a list `D` of objects decomposing `beads ∪ ⋃_j F_j`, with `|D| ≤ Φ`. Every object is a cycle `c` with `|c| ≥ max(3, k)` and all its edges in `E(G)`.

Faithfulness:
- The `k = 1` reading is uniform: `succ 0 = 0` and `pad ≡ 0`. It is equivalent to the manuscript's explicit `k = 1` reading (`jcp_iff_jcpOne`).
- The families `𝒫_j` are data. This is the only faithful reading, since (ii) mentions `E(𝒫_j)`.

### `HccUnionStatement` [s6:lemHCCglob] ¶1 (proved)
TeX: "Let `E_1, …, E_q ⊆ E(G)` be pairwise disjoint, and suppose each `E_i` decomposes into `a_i` objects. Then `E_1 ∪ ⋯ ∪ E_q` decomposes into `∑_i a_i` objects."

Lean, in plain words: take edge sets `E_i ⊆ E(G)`, pairwise disjoint, each with a decomposition `D_i`. Then some `D'` decomposes `⋃ E_i` and has exactly `∑ |D_i|` objects. The Lean statement is literal.

### `HccGlobStatement` [s6:lemHCCglob] ¶2
TeX: "In particular, suppose several systems satisfy the hypotheses of Lemma HCC-P separately, each with its own layers, junction sets and path families, and the edge sets they decompose (their beads together with their sets `F_j`) are pairwise disjoint. Then the union of these edge sets decomposes into at most the sum of their values `Φ`. No vertex-disjointness across systems is needed ..."

Lean, in plain words: let `q` systems each be valid for `G`, such that the beads and all path edges of two distinct systems are disjoint. Then:
- there are common loads `Φ_s`;
- there are sets `F_{s,j}` as in HCC-P (ii), for every system;
- the union over `s` of `beads_s ∪ ⋃_j F_{s,j}` has a decomposition into at most `∑_s Φ_s` objects, all of them cycles of `G`.

Two differences from the TeX, both T0:
1. **Input-level disjointness** (TRIAGE decision, GLOB-OUTPUT-LEVEL-HYP). The TeX hypothesis refers to the `F_j`, which are outputs. Since `F_j ⊆ E(𝒫_j)`, the input-level hypothesis implies the TeX one. It is exactly what JS-LC Step 7 checks: bead sets disjoint, path edges disjoint within `(Y,l,j)`, across `j` and across `Y`, and path edges disjoint from beads.
2. **"cycles" in the conclusion.** The TeX says only "decomposes into at most ...". The consumer, JS-LC Step 7, reads "the union decomposes into at most `∑_𝒮 Φ(𝒮)` cycles", and J⁺ says "HCC-P output consists of cycles only". The extra conjunct is a strengthening, and it holds because the decomposition is the concatenation of the HCC-P outputs.

No cross-system vertex condition is assumed. The bowtie test shares the port `0` between two systems.

### `HccpEndMultStatement` (refutation target, engine part)
TeX (JS-LC Step 4): "A port `u` of layer `j` has demand `dem⁻(u)` at junction `j` and `dem⁺(u)` at junction `j−1`. Both are at most `|exc(u)| + pad(u)`." Claim (c) proof: "So at a fixed junction a port occurs in at most `max(dem⁻, dem⁺)` pairs of each system containing it. Centres occur in no pair." Step 4: "`|exc(u)| ≤ M_l − 1`", via MED(b) `|exc(u)| ≤ deg_{B_𝒦}(u)`.

Lean, in plain words: for every valid system `S`, every junction `j` and every vertex `u`:
- the number of paths of `𝒫_j` whose first or last vertex is `u` is at most `max(dem⁻(u), dem⁺(u))`;
- that maximum is `|exc(u)| + pad(u)`;
- if `u` is a port of cluster `𝒦_i`, then `|exc(u)| ≤ deg_{B_{𝒦_i}}(u)`.

In the HCC-P encoding, the junction-`j` pairs of a system are the (first, last) vertex pairs of the paths of `𝒫_j`.

### `JsMultNumStatement` (refutation target, numeric part; proved)
TeX (claim (c)): "Every vertex lies in at most `max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 ≤ t` pairs ... For `M_l ≥ 2`, `⌈M_l/2⌉ ≤ M_l − 1`, so both are at most `2M_l − 2 < t = 2M_l + 2`". Step 4 adds "`pad(u) ≤ ⌈(M_l − 1)/2⌉ ≤ ⌈M_l/2⌉`".

Lean, in plain words: for `M ∈ ℕ` with `M ≥ 2`:
- `⌈(M−1)/2⌉ ≤ ⌈M/2⌉ ≤ M − 1`;
- `2(M−1) = 2M−2`;
- `max(2M−2, (M−1) + ⌈M/2⌉) = 2M−2`;
- `2M−2 < 2M+2`.

`t^JS_l = 2M_l + 2` is `EG.Stage1.tJS`.

### `EulerTreeTJoinStatement` [s1:citEuler] (a) (declared input)
TeX: "Let `H` be a connected graph and `T ⊆ V(H)` with `|T|` even. Every spanning tree `S` of `H` contains a `T`-join, i.e. a set `J ⊆ E(S)` such that the vertices of odd `J`-degree are exactly the vertices of `T`."

Lean, in plain words: let `H` be a finite simple graph (`FGraph`) in which any two vertices of `V(H)` are joined by a walk, let `T ⊆ V(H)` have even size, and let `S ⊆ E(H)` be such that `(V(H), S)` is connected on `V(H)` and acyclic. Then some `J ⊆ S` has `deg_J(v)` odd iff `v ∈ T`, for every vertex `v`.

The empty `H` is allowed; it is trivial there.

## 6. Refutation target, and how the probe hits it

TRIAGE §4 names two refutation targets for P-2:
- "two J^hub edges of one class at one hub in one round (J1 aggregated)", which is JS-LC/J⁺ work for part 2;
- this task's target: "the engine's multiplicity bounds feeding JS-LC (joint multiplicity `≤ 2M_l − 2 ≤ t^JS`)".

This unit splits the second target into an engine part and a numeric part.
1. **Engine part** (`HccpEndMultStatement`, to be proved in stage 2 from `Valid`, `pexc_eq` and MED(b)). Per system and per junction, a vertex is an end of at most `|exc| + pad` paths, and `|exc| ≤ deg_B`. This is the only place where the engine's multiplicities enter claim (c).
2. **Numeric part** (`JsMultNumStatement`, proved). It gives `max(2M−2, (M−1) + ⌈M/2⌉) = 2M−2 < 2M+2` for `M ≥ 2`.

The remaining JS-LC-level step is the aggregation over the systems of `(Y,l)`:
- a port is in `𝒮_0` or in cherry systems, never in both;
- it lies in at most `M_l − 1` cherry systems;
- its demand is `≤ 2` per cherry system.

That step belongs to part 2 of P-2. It uses `|exc| ≤ deg_{R_Y}(u) ≤ M_l − 1` and `pad ≤ ⌈(M_l−1)/2⌉` or `pad ≤ 1`.

I re-derived claim (c) and found no error. The equality `max(…) = 2M_l − 2` in the claim needs `M_l ≥ 2`: at `M_l = 1` the maximum is `1 > 0`, though still `≤ t`. It holds because `M_l ≥ 2^40` by (R2), and the claim's proof says "For `M_l ≥ 2`". This is a harmless wording point (T1, no action needed).

## 7. Non-vacuity (`EGTest/ProbeP2E.lean`)

- **MED.** `K5` (from `EGTest.Chain`) is parity-clean, and `v ↦ v` is injective on its ports. The conclusion holds on it:
  - `medOrient = O5` is admissible;
  - (b) holds on `O5`: the port bounds, the zero sum, and `Φ = 2 ≤ b = 3`.
- **A cherry** (JS-LC Step 5): the orientation `1 → 0 → 2` is admissible, with `exc = +1` and `−1` and load 1.
- **EQ-LPT.** Loads `3,2,1`, `k = 2`: the loads are antitone and nonnegative, and a greedy placement exists (`σ3`). `σ3` is surjective.
- **PAR.**
  - The hypotheses hold on the path `0 1 2 3` with sides `{0,2}`, `{1,3}`.
  - `IsParChoice ∅ ∅` holds.
  - `IsParChoice {01} {01}` holds for a single odd component with a pendant edge; this proof reasons about components.
- **HCC-P.**
  - `S1` (`k = 1`) and `S2` (`k = 2`) are valid (from `EGTest.Chain`), and conclusion (i) holds on `S1`.
  - `HccpEndMultStatement`'s conclusion holds on `S1` at the port `1`.
- **HCCglob.** Two valid systems on a bowtie share the port `0`, and the input-level disjointness holds for them. This checks that the hypothesis does not force vertex-disjointness.
- **`HccUnionStatement`** and **`JsMultNumStatement`** at `M = 2^40` are both used.
- **Euler (a).** The hypotheses hold on the single edge `01`, with `T = {0,1}` and `S = {01}`.

## 8. Hazards and open questions

- **H1 (T0, TRIAGE decision): HCCglob input-level hypothesis.** See §5. It is not a weakening for the only consumer, JS-LC Step 7. A reviewer should confirm that the added "cycles" conjunct is acceptable. The alternative is to drop it and let JS-LC use HCC-P per system plus `hccUnion`.
- **H2: `HccUnionStatement` keeps `E_i ⊆ E(G)`**, although the proof does not need it. It is literal.
- **H3: the HCC-P length conclusion `max(3,k)`** is used by no consumer (HCCP-LENGTH-UNUSED). It is kept in `HccpStatement` for faithfulness, at a cost of about 150 lines in stage 2. Alternative: split it into its own Spec and let consumers depend on a count-only Spec. That needs a decision, because a count-only Spec alone would be weaker than the TeX.
- **H4: PAR without Euler.** Stage 2 may prove the parity partition directly and drop the declared input.
- **H5: `Par.lean` is a new Defs file.** It needs integrator review and a lock before P-2 part 2 (J⁺) uses `IsParChoice`.
- **H6: EQ-LPT existence under the full lemma hypotheses.** `EqLptExistsStatement` keeps `Antitone`, `k ≤ m` and `Φ ≥ 0`, although existence needs only `k ≥ 1` and `Φ ≥ 0`. The JS-LC consumer has all of them: it sorts the clusters by load, and `k_0 ≤ #clusters`.
- **H7 (JS-LC, for part 2): EQ-USE-EMPTY-S0.** When `𝒮_0 = ∅`, `m = 0` and EQ-LPT does not apply. JS-LC must case-split.
- **Open question: stage-2 order.** Proposed order:
  1. MED(b), which HCC-P Step 0 and the engine multiplicity bound need;
  2. `HccpEndMultStatement`;
  3. EQ-LPT;
  4. MED(a);
  5. HCC-P;
  6. HCCglob ¶2;
  7. PAR, the most infrastructure.

## 9. Math findings

No error found in the engine lemmas (MED, EQ-LPT, PAR, HCC-P, HCCglob) or in the engine part of JS-LC claim (c). The only items are the T0 encodings (H1) and the harmless T1 wording point in §6.

## Fix round 1

Review: `work/p2b/P2E.review1.md` (verdict: approve; six remarks). I checked each remark against the TeX and the files. Results:

| # | remark | verdict | action |
|---|---|---|---|
| R1 (minor) | `HccGlobStatement`: input-level disjointness is stronger than the literal hypothesis; the "cycles of `G`" conjunct is extra | **valid, accepted as T0** | Checked against `s6.tex:588–594`. Step 7 verifies exactly the input-level condition: bead sets pairwise disjoint, path edges pairwise disjoint (within `(Y,l,j)`, across `j`, across `Y`), and path edges disjoint from beads. It reads "decomposes into at most `∑_𝒮 Φ(𝒮)` cycles". **Fixed:** new row `T0-glob-input` at the end of the CONVENTIONS T0 table, which quotes Step 7, and the `HccGlobStatement` docstring now cites that row and the Step 7 quotation. The statement is unchanged. |
| R2 (minor) | the refutation target is hit only per system and per junction; the aggregated claim (c) has no Spec | **valid; deferred to part 2** (it cannot be stated in part 1) | The aggregated bound quantifies over all systems of `(Y,l)`. It needs `𝒮_0`/cherry exclusivity, `≤ M_l − 1` cherry systems per port with demand `≤ 2`, and Step 4's pad bound. These are JS-LC-level data (systems of `(Y,l)`, padding choice), and part 2 models them. **Fixed in this unit:** the `EngineMult` Spec module docstring now states the scope and the hand-off. **Hand-off to P-2 part 2:** add a JS-LC-level Spec for "every vertex lies in at most `2M_l − 2 ≤ t^JS_l` pairs of `𝔓_j(Y,l)`", and prove it from `HccpEndMultStatement`, `JsMultNumStatement` and `EG.jsMult_lt_tJS`. The observation that the second conjunct of `HccpEndMultStatement` is an identity is correct: `max((−x)⁺, x⁺) = |x|`. I kept it on purpose, since it ties the demand bound to the TeX's `|exc(u)| + pad(u)`, and the docstring says so. |
| R3 (cosmetic) | `JsMultNumStatement` writes `t` as the literal `2M + 2` | **valid; fixed now** (the review suggested part 2) | New file `EG/Proof/Chain/EngineMultTJS.lean` with two results. `EG.tJS_eq_two_mul_add_two`: `Stage1.tJS G run l = 2 * run.M G l + 2`, by `rfl`. `EG.jsMult_lt_tJS`: for `M_l ≥ 2`, `max(2M_l − 2, (M_l − 1) + ⌈M_l/2⌉) = 2M_l − 2 < tJS G run l`. It compiles, and its axiom scan (764 constants) finds 0 `sorryAx`. It sits in its own file so that the engine files do not import the Stage1 and HB stack. |
| R4 (cosmetic) | the `[s6:lemJSLC]` tags on proof-internal facts | **valid; fixed** | The docstrings of `HccpEndMultStatement` and `JsMultNumStatement`, and of `EG.jsMultNum`, now start with `[s6:lemJSLC:proof-claim-c]` and say they are proof-internal facts, not the lemma. No script parses labels (checked `scripts/`). |
| R5 (cosmetic) | `EulerTreeTJoinStatement` vs the planned Lib form (EUL-MULTI-USE) | **partly an issue** | TRIAGE EUL-MULTI-USE plans a multigraph form of citEuler **(b)**, not (a). Part (a) is applied only to spanning trees, which are simple. So a double declaration of (a) is not currently planned. **Fixed:** the Spec's module docstring marks it as the canonical s1:citEuler (a) and asks that any later Lib form of (a) be bridged to it. **Integrator:** confirm that it is canonical. |
| R6 (cosmetic) | `EqLptExistsStatement` keeps the extra hypotheses | **not an issue** | The extra hypotheses are harmless and not a weakening (H6); the consumer has all of them. No change. |

No statement changed in this round. Only docstrings changed, the CONVENTIONS row was added, and the bridge file is new.

Checks after the fixes:
- `lake build` of `EG.Spec.Chain.{EngineMult,HCCP}`, `EG.Spec.Found.EulerTreeTJoin`, `EG.Proof.Chain.{EngineMultTJS,HCCUnion}` and `EG.Proof.Found.EulerTreeTJoin` succeeds. The one `sorry` is the DECLARED INPUT stub `EG.eulerTreeTJoin`.
- `scripts/check.sh` on `EGTest/ProbeP2E.lean` and on `EG/Proof/Chain/EngineMultTJS.lean`: 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.

New file for the integrator's root list: `EG/Proof/Chain/EngineMultTJS.lean` (module `EG.Proof.Chain.EngineMultTJS`). Edited shared file: `CONVENTIONS.md`, one appended T0 row.

## Fix round 2

Review: `work/p2b/P2E.review2.md` (verdict: approve; four remarks, none needing a statement change). I checked each remark against the TeX and the files.

| # | remark | verdict | action |
|---|---|---|---|
| 1 (cosmetic) | `IsParChoice`: the conjunct `J' ⊆ E` is implied by the third conjunct | **valid (redundancy confirmed); no semantic change** | `EG.IsNonBridge E e` is `e ∈ E ∧ ¬ IsBridge` and `EG.IsPendant E e` is `e ∈ E ∧ ∃ v ∈ e, degE E v = 1` (`EG/Defs/Components.lean:91–97`), so the conjunct is redundant. **Fixed:** the `IsParChoice` docstring in `EG/Defs/Probe/P2E/Par.lean` (this unit's own probe Defs file) now records the redundancy. The definition is unchanged; I kept the conjunct because it makes the shape explicit. |
| 2 (cosmetic) | the HCC-P length conclusion `max 3 S.k ≤ c.length` has no consumer but is in the TeX | **not an issue; stays** | `s6:lemHCCP` (ii) states the length bound, so dropping it would weaken the Spec. **Fixed (docstring only):** the module docstring of `EG/Spec/Chain/HCCP.lean` now says the bound stays, and that any count-only form must be a Lib/Proof corollary of `HccpStatement`, never a replacement Spec. `HccpStatement` is unchanged. |
| 3 (minor) | the refutation target is hit per system and per junction only; aggregated JS-LC claim (c) has no Spec | **valid; hand-off to P-2 part 2** (as in round 1, R2) | The aggregated bound needs JS-LC-level data (the systems of `(Y,l)`, `𝒮_0`/cherry exclusivity, `≤ M_l − 1` cherry systems per port with demand `≤ 2`, pad `≤ ⌈(M_l−1)/2⌉`). Part 1 does not model these. **Fixed (docstring only):** the `EG/Spec/Chain/EngineMult.lean` module docstring now names all three ingredients, `HccpEndMultStatement`, `JsMultNumStatement` and `EG.jsMult_lt_tJS`. **Hand-off to part 2 (open):** add a JS-LC-level aggregated multiplicity Spec ("every vertex lies in at most `2M_l − 2 ≤ t^JS_l` pairs of `𝔓_j(Y,l)`") and prove it from these three. |
| 4 (cosmetic) | `EulerTreeTJoinStatement` is canonical for s1:citEuler (a) | **confirmed** | Grepped all manuscript uses of `s1:citEuler`: `s6.tex:130` (PAR) and `s5.tex:252` (s5:lemParent Step 3, "applied to a spanning tree of each component" of a loop-free spanning forest; the multigraph remark there concerns the Euler-trail part (b)). A spanning tree is simple, so the Spec covers both uses of (a). **Fixed (docstring only):** the Spec module docstring records this confirmation. **Integrator:** record `EulerTreeTJoinStatement` as the canonical s1:citEuler (a) and bridge any later Lib form of (a) to it. |

No statement or definition changed in this round; only docstrings changed, in 4 files: `EG/Defs/Probe/P2E/Par.lean`, `EG/Spec/Chain/HCCP.lean`, `EG/Spec/Chain/EngineMult.lean` and `EG/Spec/Found/EulerTreeTJoin.lean`.

Checks after the fixes:
- `lake build` of `EG.Spec.Chain.{PAR,HCCP,EngineMult}`, `EG.Spec.Found.EulerTreeTJoin`, `EG.Proof.Found.EulerTreeTJoin` and `EG.Proof.Chain.{EngineMult,HCCUnion,EngineMultTJS}` succeeds. The only `sorry` is the DECLARED INPUT stub `EG.eulerTreeTJoin`.
- `scripts/check.sh` on `EGTest/ProbeP2E.lean` and on `EG/Proof/Chain/EngineMultTJS.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.

Re-verification (fix round 2, second pass). All four fixes are present in the files. Remark 1 was re-checked against `EG/Defs/Components.lean`. Remark 4 was re-checked against `s5.tex:252`: a spanning tree of the loopy multigraph `UQ_{l,c,i}` has neither loops nor parallel edges, so `H :=` the tree is an `FGraph`. The same build, `check.sh` (rc=0, 0 errors, 0 sorry) and lint (0 findings) were re-run and pass. Remark 3 remains open as the part-2 hand-off; the aggregated JS-LC multiplicity is not in this unit's files.

## Proof round 1

Stage 3 (proofs), round 1. Progress log, updated as each node is finished.

| label | Lean theorem | file | state |
|---|---|---|---|
| `s6:lemMED` (a) | `EG.med : MedStatement` | `EG/Proof/Chain/MED.lean` (Lib: `EG/Lib/Chain/MedOrient.lean`) | **proved** |
| `s6:lemMED` (b) | `EG.medExc : MedExcStatement` | `EG/Proof/Chain/MED.lean` (Lib: `EG/Lib/Chain/MedExc.lean`) | **proved** |
| refutation target, engine part | `EG.hccpEndMult : HccpEndMultStatement` | `EG/Proof/Chain/HccpEndMult.lean` (Lib: `EG/Lib/Chain/HccpEnds.lean`) | **proved** |
| `s6:lemEQLPT` (existence) | `EG.eqLptExists : EqLptExistsStatement` | `EG/Proof/Chain/EqLpt.lean` (Lib: `EG/Lib/Chain/EqLptProof.lean`) | **proved** |
| `s6:lemEQLPT` | `EG.eqLpt : EqLptStatement` | `EG/Proof/Chain/EqLpt.lean` | **proved** |
| `s6:lemHCCP` | `EG.hccp : HccpStatement` | `EG/Proof/Chain/HCCP.lean` (Lib: `EG/Lib/Chain/{HccpPaths,HccpAux,HccpPot}.lean`) | **proved** (incl. the length bound `max(3,k)`) |
| `s6:lemHCCglob` ¶2 | `EG.hccGlob : HccGlobStatement` | `EG/Proof/Chain/HCCGlob.lean` | **proved** |
| `s6:lemPAR` (existence) | `EG.parExists : ParExistsStatement` | `EG/Proof/Chain/PAR.lean` (Lib: `EG/Lib/Chain/ParExist.lean`) | **proved** |
| `s6:lemPAR` | `EG.par : ParStatement` | `EG/Proof/Chain/PAR.lean` (Lib: `EG/Lib/Chain/{ParTJoin,ParComp,ParMain}.lean`) | **proved**, without the declared input |

Already proved in stage 1: `EG.hccUnion` (`s6:lemHCCglob` ¶1), `EG.jsMultNum` (numeric part of the
refutation target), `EG.jsMult_lt_tJS` (bridge to `Stage1.tJS`). `s6:lemGATE` was proved before
this unit (`EG.gate_with_cycles` is used by HCC-P Step 4).

**Every probe node of this unit is proved with 0 sorry. Nothing remains open in part 1.**

### How the proofs follow the manuscript

- **MED (a)** (`EG/Lib/Chain/MedOrient.lean`). "Every bead is oriented exactly once": for a bead
  `xy`, exactly one of `medRule x y`, `medRule y x` holds (a hub–port bead by the position rule, a
  port–port bead by the rank, using injectivity of `rk` on the ports). Hub balance: the positions
  `medPos` of the `2d` neighbours of a hub are exactly `1, …, 2d` (injective, values in
  `[1, 2d]`), so `d` of them are `≤ d`. The potential is the manuscript's: `(rk(u)+1)/(M+2)` on
  ports, `(rk(u_d)+1+1/2)/(M+2)` on hubs (`u_d` = the in-neighbour of largest rank, `0` if none).
- **MED (b)** (`EG/Lib/Chain/MedExc.lean`). `d⁺ + d⁻ = deg_B` gives the bound and the parity; the
  handshake `∑_{V(𝒦)} (d⁺ − d⁻) = 0` plus hub balance gives `∑_{U} exc = 0`; `Φ ≤ ∑_U d⁺ =
  #{port→hub arcs} + e(B[U]) = ∑_A d⁻ + e(B[U]) = b(𝒦)`.
- **EQ-LPT** (`EG/Lib/Chain/EqLptProof.lean`). Existence: a greedy placement is built item by item
  (the rule for item `i` reads only the items before `i`); an empty layer has load `0`, which is
  minimum because loads are `≥ 0`. Surjectivity: if some layer stayed empty, the rule would send
  every item to a layer empty before it, so `σ` would be injective into the other `k − 1` layers,
  contradicting `k ≤ m`. Balance: the manuscript's last-item argument, for any two layers.
- **HCC-P** (`EG/Lib/Chain/{HccpPaths,HccpAux,HccpPot}.lean`, `EG/Proof/Chain/HCCP.lean`).
  Step 0 via `|𝒫_j| = ∑_{LayP_j} dem⁻` and `= ∑_{LayP_{j+1}} dem⁺`, with `∑ exc⁻ = ∑ exc⁺` from
  MED (b). Step 1: `D_j` orients `E(𝒫_j)`; per-path counting gives
  `d⁺_{D_j}(v) + #last(v) = #paths through v = d⁻_{D_j}(v) + #first(v)`, so a vertex outside `T_j`
  is a source or a sink (for `k ≥ 2` by disjoint layers, for `k = 1` because `exc⁻` and `exc⁺`
  are not both positive and `pad = 0`), and the balanced cancelled set `R_j` lies inside `T_j`
  (`EG.exists_balanced_sdiff_acyclic`). Step 2: the excess of `F⃗` at `v` is
  `exc(v) + [v port](dem⁻(v) − dem⁺(v)) = 0` (the `dem⁺` sum is reindexed along the bijection
  `succ`). Step 3: `Ψ` as in the manuscript (topological numberings from
  `EG.IsAcyclic.exists_potential`), `𝒲` = arcs of `D'_{k−1}` into `LayP_0`, and
  `|𝒲| ≤ ∑_{LayP_0} d⁻_{D_{k−1}} ≤ ∑_{LayP_0} dem⁺ = Φ`. Step 4: GATE, and the length bound by
  telescoping the block index around each cycle (`EG.le_length_of_blocks`).
- **HCCglob ¶2** (`EG/Proof/Chain/HCCGlob.lean`): HCC-P per system plus the concatenation lemma
  `EG.isDecomp_finset_biUnion`; the edge sets are disjoint because `F_{s,j} ⊆ E(𝒫_{s,j})`.
- **PAR** (`EG/Lib/Chain/{ParExist,ParComp,ParTJoin,ParMain}.lean`). Existence: a maximal-path
  argument (extend a path at its first vertex `x`; if `deg(x) = 1` the first edge is pendant,
  else a second neighbour on the path closes a cycle through the first edge, which is then a
  non-bridge). The count: `J'` meets each odd component once and nothing else; odd components
  have two vertices each in disjoint `compVerts`. Even components after deletion
  (`EG.Chain.even_card_compPrime`): the three cases of the manuscript (no chosen edge; non-bridge;
  pendant, where a path of `E` between two vertices `≠ u` never passes through the leaf `u`, by
  `IsTrail.even_countP_edges_iff`). The partition: `S_a` is a `T`-join of `E ∖ J'` for
  `T = {u ∈ V_a : deg_{E∖J'}(u) odd}`, `S_b` the rest.

### Declared input no longer used

The proof of PAR does not use `EG.eulerTreeTJoin` (s1:citEuler (a)). The `T`-join is built by
induction on `|T|` as a symmetric difference of paths (`EG.exists_tJoin`, `EG/Lib/Chain/ParTJoin.lean`),
using only that every component of `E ∖ J'` contains an even number of vertices of `T`. So the
probe needs **no declared input**. The stub files `EG/Spec/Found/EulerTreeTJoin.lean` and
`EG/Proof/Found/EulerTreeTJoin.lean` (stage 1) are left in place, unused; s5:lemParent Step 3 still
cites s1:citEuler (a), so the integrator may keep the Spec as the canonical statement. It could now
be proved from `EG.exists_tJoin` (a spanning tree is connected), but that is outside this unit.

### Refutation target (engine multiplicities feeding JS-LC)

Hit and proved: `EG.hccpEndMult` (per system and junction, a vertex is an end of at most
`max(dem⁻, dem⁺) = |exc| + pad` paths, and `|exc(u)| ≤ deg_{B_𝒦}(u)` via MED (b)), with
`EG.jsMultNum` and `EG.jsMult_lt_tJS` (`max(2M−2, (M−1)+⌈M/2⌉) = 2M−2 < t^JS = 2M+2` for
`M ≥ 2`). No counterexample and no gap found. The aggregation over the systems of `(Y,l)` stays
the part-2 hand-off recorded in the fix rounds.

### Math findings of this round

None that affects a statement. Minor remarks (T1 at most, no action needed):
- HCC-P Step 3 says `|𝒲| = |𝒫_{k−1}| = Φ`; only `|𝒲| ≤ Φ` is needed and proved (equality also holds
  since last arcs are never cancelled, but it is not used).
- The PAR proof's citation of s1:citEuler can be replaced by the elementary path argument above.

### Checks (proof round 1)

- `lake build EG.Proof.Chain.{MED,EqLpt,HccpEndMult,HCCP,HCCGlob,PAR}`: success.
- `scripts/check.sh` on each new file: 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Chain.{MED,EqLpt,HccpEndMult,HCCP,HCCGlob,PAR,EngineMult,HCCUnion}`:
  1242 constants inspected, **0 use `sorryAx`**, 0 violations.

### New files (for the integrator's root list)

Lib: `EG/Lib/Chain/{MedExc,MedOrient,HccpEnds,EqLptProof,HccpPaths,HccpAux,HccpPot,ParTJoin,ParComp,ParMain,ParExist}.lean`.
Proof: `EG/Proof/Chain/{MED,EqLpt,HccpEndMult,HCCP,HCCGlob,PAR}.lean`.
No Defs, Spec, root or test file was changed.

### Re-verification (proof round 1, second pass, 2026-09-29)

Re-ran on the current tree: `lake build` of `EG.Proof.Chain.{MED,EqLpt,HccpEndMult,HCCP,HCCGlob,PAR,EngineMult,HCCUnion,EngineMultTJS}`
succeeds (2089 jobs; only unused-simp-arg linter warnings in `HccpPaths.lean`); `python3 -I scripts/lint.py`: 0 findings;
axiom scan of those modules plus `EG.Proof.Found.EulerTreeTJoin`: 1744 constants, 1 `sorryAx` = the unused
DECLARED INPUT stub `EG.eulerTreeTJoin`, 0 violations; `git status` shows no change under `EG/Spec` or `EG/Defs`.
No new work was needed; the table above is current.

### Re-verification (proof round 1, third pass, 2026-09-30)

Re-ran on the current tree (HEAD `506e5f0`): `lake build` of `EG.Proof.Chain.{MED,EqLpt,HccpEndMult,HCCP,HCCGlob,PAR,EngineMult,HCCUnion,EngineMultTJS}`
and `EG.Proof.Found.EulerTreeTJoin` succeeds (2111 jobs; only unused-simp-arg linter warnings); `python3 -I scripts/lint.py`: 0 findings;
axiom scan of those modules: 1744 constants, 1 `sorryAx` = the unused DECLARED INPUT stub `EG.eulerTreeTJoin`, 0 violations;
`git diff HEAD -- EG/Spec EG/Defs` is empty. No new work was needed; the table above is current.
