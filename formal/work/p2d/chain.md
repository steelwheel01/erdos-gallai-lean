# P2-D [chain]: routing-engine data (s6:defCluster, s6:lemMED, s6:lemEQLPT, s6:lemHCCP): design note

Status: all files compile with 0 errors, 0 warnings and 0 `sorry`. The lint is clean on all seven
files. The axiom scan (`scripts/Axioms.lean --prefix EG EG.Lib.Chain.HCCP EG.Lib.Chain.EqLpt`,
which covers all six EG modules) inspects 651 constants and finds 0 violations and 0 `sorryAx`.
Manuscript: `proofs/manuscript/s6.tex` v6.1, lines 12–219.

These are the Defs items 21–23 of TRIAGE §3. They use only `EG.Defs.Graph`, `Walk` and `Orient`
(not `Components`). They do not mention `M_l`, so the M-INTEGER lock gate does not affect them.

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Chain/Cluster.lean` | `EG.Defs.Chain.Cluster` | `Cluster`, `exc`, `excPos`, `excNeg`, `Cluster.verts`, `portBeads`, `beadCount`, `ParityClean`, `IsAdmissible`, `load`, `beadNbrs`, `medPos`, `medRule`, `medOrient` |
| `EG/Defs/Chain/EqLpt.lean` | `EG.Defs.Chain.EqLpt` | `loadBefore`, `EmptyBefore`, `IsGreedyLPT`, `layerLoad` |
| `EG/Defs/Chain/HCCP.lean` | `EG.Defs.Chain.HCCP` | `HccpData` (data), `succ`, `layP`, `pexc`, `demMinus`, `demPlus`, `Phi`, `xOut`, `xIn`, `pathEdges`, `allPathEdges`, `beads`, `Valid` (hypotheses) |
| `EG/Lib/Chain/Cluster.lean` | `EG.Lib.Chain.Cluster` | API lemmas (listed below) |
| `EG/Lib/Chain/EqLpt.lean` | `EG.Lib.Chain.EqLpt` | API lemmas |
| `EG/Lib/Chain/HCCP.lean` | `EG.Lib.Chain.HCCP` | API lemmas, `JcpUniform`, `JcpOne`, and `jcp_iff_jcpOne` (the k = 1 equivalence) |
| `EGTest/Chain.lean` | `EGTest.Chain` | unit tests, non-vacuity of `Valid` for k = 1 and k = 2, negative tests |

All names live in the namespace `EG.Chain`.

Root imports for the orchestrator to add (I did not edit `EG.lean` or `EGTest.lean`):
- to `EG`: `EG.Defs.Chain.Cluster`, `EG.Defs.Chain.EqLpt`, `EG.Defs.Chain.HCCP`, `EG.Lib.Chain.Cluster`, `EG.Lib.Chain.EqLpt`, `EG.Lib.Chain.HCCP`;
- to `EGTest`: `EGTest.Chain`.

## Definitions, with the manuscript text

### `EG/Defs/Chain/Cluster.lean` (s6:defCluster, s6.tex:33–54)

**`structure Cluster (V)`.** Fields: `hubs ports : Finset V`, `beads : Finset (Sym2 V)`, and four axioms: `disjoint`, `loopless`, `ends_mem`, `no_hub_hub`.

> "A *cluster* is a triple 𝒦=(A_𝒦,U_𝒦,B_𝒦) with the following parts. A_𝒦 (the *hubs* of 𝒦) and U_𝒦 (the *ports* of 𝒦) are disjoint vertex sets. Put V(𝒦):=A_𝒦∪U_𝒦. B_𝒦⊆E(G[A_𝒦∪U_𝒦]) is the set of *beads*. No bead has both ends in A_𝒦."

- `disjoint : Disjoint hubs ports`.
- `no_hub_hub : ∀ e ∈ beads, ¬ ∀ v ∈ e, v ∈ hubs`. This is the literal "no bead has both ends in A". The Lib lemma `exists_port_of_mem_beads` gives the form "some end is a port".
- **Decision (G-free cluster; TRIAGE §2.9, blueprint CL-G-FREE).** The clause "B ⊆ E(G[A ∪ U])" is split in two:
  - the G-free part is in the structure: `loopless` (G is simple) and `ends_mem` (both ends lie in A ∪ U);
  - `B ⊆ E(G)` is a hypothesis wherever G matters (`HccpData.Valid.beads_G`).

  Every consumer cluster (JS-LC components and cherries) has beads in E_l(Z) ⊆ E(G).
- `@[ext]` on hubs, ports and beads.

**`exc O u : ℤ := outDeg O u − inDeg O u`, `excPos O u := (exc O u).toNat`, `excNeg O u := (−exc O u).toNat`.**

> "Given an admissible orientation, put for every port u: exc(u):=d⁺(u)−d⁻(u), exc(u)⁺:=max(exc(u),0), exc(u)⁻:=max(−exc(u),0)"

- **Decision (CL-ORIENT-IS-DATA).** The orientation is an explicit argument, because the manuscript suppresses it in the notation.
- The functions are total: defined at every vertex and for every arc set.
- `excPos` and `excNeg` are in ℕ. `excPos_cast` and `excNeg_cast` state that their casts to ℤ are `max(±exc, 0)`.

**`Cluster.verts := hubs ∪ ports`** ("Put V(𝒦):=A_𝒦∪U_𝒦").

**`Cluster.portBeads := beads.filter (· ∈ ports.sym2)`**: the set B_𝒦[U_𝒦], whose cardinality is e(B_𝒦[U_𝒦]).

**`Cluster.beadCount : ℝ := ∑_{h∈hubs} (deg_B h : ℝ)/2 + |portBeads|`.**

> "The *bead count* is b(𝒦):=∑_{h∈A_𝒦}deg_{B_𝒦}(h)/2+e(B_𝒦[U_𝒦])."

- **Decision (CL-BEADCOUNT-HALF).** b(𝒦) is real-valued. With ℕ division it would differ from the text for clusters that are not parity-clean.
- `beadCount_eq_natCast` shows that it is a natural number for parity-clean clusters.
- Test: the cluster `Kodd` has b = 3/2.

**`Cluster.ParityClean := ∀ h ∈ hubs, Even (degE beads h)`**, with a `Decidable` instance.

> "The cluster 𝒦 is *parity-clean* if every hub has even B_𝒦-degree."

**`Cluster.IsAdmissible O`.** A structure with the fields `orient : IsOrientation beads O`, `acyclic : IsAcyclic O` and `hub_bal : ∀ h ∈ hubs, outDeg O h = inDeg O h`.

> "An *admissible orientation* of 𝒦 is an acyclic orientation of B_𝒦 in which every hub h has d⁺(h)=d⁻(h)."

- Balance is required at the hubs only, so `IsBalanced` is not used (CONVENTIONS). The test shows that `O5` is admissible but not `IsBalanced`.

**`Cluster.load O : ℕ := ∑_{u∈ports} excPos O u`.**

> "define the *load* Φ(𝒦):=∑_{u∈U_𝒦}exc(u)⁺"

- The value is an integer, because each exc(u)⁺ is. `load_cast` gives the ℤ form ∑ max(exc, 0).

**`Cluster.beadNbrs h := verts.filter (s(h,·) ∈ beads)`, `medPos rk h u := #{w ∈ beadNbrs h : rk w ≤ rk u}`, `medRule`, `medOrient rk := (verts ×ˢ verts).filter (s(a.1,a.2) ∈ beads ∧ medRule rk a.1 a.2)`.**

> "Let 𝒦 be parity-clean and let ≺ be a linear order on U_𝒦. The *median orientation* MED(≺) orients B_𝒦 as follows. At a hub h with B_𝒦-neighbours u_1≺u_2≺…≺u_{2d}, it orients u_i→h for i≤d and h→u_i for i>d. These neighbours are ports, since no bead joins two hubs. A port–port bead uv with u≺v is oriented u→v (≺-upwards)."

- The linear order ≺ is a rank `rk : V → ℕ`, with u ≺ v iff rk u < rk v. Statements about MED assume `Set.InjOn rk ports`. Every linear order of a finite set arises this way.
- For u = u_i we have `medPos rk h u = i`. The conditions "i ≤ d" and "i > d" become `2·medPos ≤ #beadNbrs` and `#beadNbrs < 2·medPos`, since 2d = #neighbours = deg_B(h) by `card_beadNbrs`.
- `medRule x y` has three disjuncts: (port x, hub y, 2i ≤ 2d), (hub x, port y, 2i > 2d), and (ports x and y, rk x < rk y).
- **Decision (CL-MED-TOTAL).** `medOrient` is total. The manuscript defines MED only for parity-clean clusters and linear orders, and Lemma MED is stated under those hypotheses.
- "Every bead is oriented exactly once" is a claim of the manuscript, not a definition. It is MED(a) and belongs to the MED Spec.
- `mem_medOrient` drops the `verts ×ˢ verts` guard, which is automatic because both ends of a bead are in `verts`.
- Test: for the cluster `K5`, `medOrient` gives exactly `{1→0, 0→2, 3→4, 1→3}` (by `decide`).

### `EG/Defs/Chain/EqLpt.lean` (s6:lemEQLPT, s6.tex:90–93)

> "Let Φ_1≥Φ_2≥…≥Φ_m≥0 be loads of m items, and let 1≤k≤m. Place the items in the order 1,2,…,m into k initially empty layers. Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists ("greedy longest-processing-time placement"). Then all k layers are non-empty, and the final layer loads satisfy max_jΦ^lay_j−min_jΦ^lay_j≤Φ_1."

- **`loadBefore Φ σ i j := ∑_{i' < i, σ i' = j} Φ i'`**: the load of layer j just before item i is placed.
- **`EmptyBefore σ i j := ∀ i' < i, σ i' ≠ j`**: layer j is empty just before item i is placed.
- **`IsGreedyLPT Φ σ := ∀ i, (∀ j, loadBefore Φ σ i (σ i) ≤ loadBefore Φ σ i j) ∧ ((∃ j, EmptyBefore σ i j) → EmptyBefore σ i (σ i))`.** The first conjunct is "a layer of currently minimum load" (G1). The second is "to an empty layer whenever one exists" (G2).
- **`layerLoad Φ σ j := ∑_{σ i = j} Φ i`**: the final layer load Φ^lay_j.
- **Decision (EQ-GREEDY-RELATION).** Ties are arbitrary, so greedy placement is a relation, and the lemma quantifies over every placement that satisfies it.
  - Existence, "So the rule is consistent", is a claim of the lemma, so it belongs in the Spec.
  - Items and layers are `Fin m` and `Fin k`, 0-based, so Φ_1 is `Φ 0`.
  - Loads are real (EQ-REAL-VS-NAT). At the uses (Φ(K_C) and unit cherry loads) they are cast from ℕ.
- Tests: the loads 3,2,1 placed into 2 layers as 0,1,1 form a greedy placement with final loads 3 and 3. The placement 0,0,1 is not greedy, because it violates (G2).

### `EG/Defs/Chain/HCCP.lean` (s6:lemHCCP, s6.tex:140–168)

**`structure HccpData (V)`.** Fields: `k N : ℕ`, `K : Fin N → Cluster V`, `O : Fin N → Finset (V×V)`, `lay : Fin N → Fin k`, `T : Fin k → Finset V`, `pad : V → ℕ` and `P : Fin k → List (List V)`.

> "Let k≥1, and suppose the following data are given. *Layers* 𝒦_0,…,𝒦_{k−1}: finite families of clusters, each cluster with a fixed admissible orientation. Put LayP_j:=⋃_{𝒦∈𝒦_j}U_𝒦. *Junction sets* T_0,…,T_{k−1}: pairwise disjoint vertex sets. A *padding* pad:⋃_jLayP_j→ℤ_{≥0}, with pad≡0 if k=1."

- **Decision (CL-IDENTITY, HCCP-INDEXED-CLUSTERS).** The layers form one indexed family of clusters with a layer map, and (D) is stated for distinct indices. A family may repeat a cluster, for example an empty one.
- **Decision (HCCP-JCP-AS-DATA).** The path families 𝒫_j are data, because conclusion (ii) refers to E(𝒫_j). "For each j there is a family 𝒫_j" becomes "for the given families".
- **Decision (HCCP-PAD-DOMAIN).** `pad : V → ℕ`, and its values off the ports are never read.

Derived definitions:
- **`succ j := ⟨(j+1) % k, _⟩`**: "Indices of layers and junction sets are taken modulo k".
- **`layP j := ⋃_{lay i = j} ports(K i)`**: LayP_j.
- **`pexc u := ∑_i [u ∈ ports(K i)] exc (O i) u`**: exc(u) of a port u in its cluster's orientation. Under (D) the sum has at most one term, and `pexc_eq` shows that pexc u = exc (O i) u for a port u of K i.
- **`demMinus u := (−pexc u).toNat + pad u`, `demPlus u := (pexc u).toNat + pad u`**: "Define the demands dem⁻(u):=exc(u)⁻+pad(u) and dem⁺(u):=exc(u)⁺+pad(u)".
- **`Phi j := ∑_{u∈layP j} demPlus u`**: "the padded loads Φ_j:=∑_{u∈LayP_j}dem⁺(u)".
- **`xOut j`, `xIn j`**: "For k=1 put X^out:={u∈LayP_0:exc(u)<0} and X^in:={u∈LayP_0:exc(u)>0}". They are defined for every layer j and used for k = 1.
- **`pathEdges j := (P j).flatMap walkEdges`**, as a Finset: E(𝒫_j).
- **`allPathEdges`**: the union of all E(𝒫_j), for the input-level form of HCCglob (GLOB-OUTPUT-LEVEL-HYP).
- **`beads`**: ⋃_𝒦 B_𝒦.

**`structure HccpData.Valid S G`.** It has one field per hypothesis, and each field's docstring quotes its clause.

> "(D) the sets A_𝒦 and U_𝒦 (over all clusters of all layers) and T_0,…,T_{k−1} are pairwise disjoint; (P) every cluster is parity-clean; (JC-P) for each j there is a family 𝒫_j of pairwise edge-disjoint paths of G with the following properties. Each path runs from a vertex of LayP_j to a vertex of LayP_{j+1}; for k=1, from X^out to X^in. All interior vertices of each path lie in T_j. Every u∈LayP_j is the first vertex of exactly dem⁻(u) paths of 𝒫_j, and every v∈LayP_{j+1} is the last vertex of exactly dem⁺(v) paths of 𝒫_j. For k=1 this reads: u∈X^out starts exactly exc(u)⁻ paths and v∈X^in ends exactly exc(v)⁺ paths. The edge sets E(𝒫_0),…,E(𝒫_{k−1}) and all bead sets B_𝒦 are pairwise disjoint."

| field | clause |
|---|---|
| `k_pos : 1 ≤ k` | "Let k ≥ 1" |
| `adm : ∀ i, (K i).IsAdmissible (O i)` | "each cluster with a fixed admissible orientation" |
| `beads_G : ∀ i, (K i).beads ⊆ G.edges` | "B_𝒦 ⊆ E(G[A_𝒦 ∪ U_𝒦])" (G part) |
| `T_disj` | "Junction sets … pairwise disjoint" / (D) |
| `pad_k1 : k = 1 → ∀ j, ∀ u ∈ layP j, pad u = 0` | "pad ≡ 0 if k = 1", on its domain ⋃ LayP_j |
| `D_KK : i ≠ i' → Disjoint (K i).verts (K i').verts` | (D) between clusters; within one cluster it is `Cluster.disjoint` |
| `D_KT : Disjoint (K i).verts (T j)` | (D) between clusters and junction sets |
| `parityClean` | (P) |
| `path_G : IsPathIn G.edges p` | "paths of G" |
| `path_ends` | "runs from a vertex of LayP_j to a vertex of LayP_{j+1}" (`head?`/`getLast?`) |
| `path_T : IsThrough (T j) p` | "All interior vertices of each path lie in T_j" |
| `starts`, `ends` | the two counts, as `List.countP` (multiplicities) |
| `path_edisj : (P j).Pairwise (walkEdges · ).Disjoint` | "pairwise edge-disjoint paths" (distinct list positions) |
| `pp_disj`, `pb_disj`, `bb_disj` | "E(𝒫_0),…,E(𝒫_{k−1}) and all bead sets B_𝒦 are pairwise disjoint" (path–path, path–bead, bead–bead) |

Decisions:
- **k = 1 (HCCP-K1-UNIFORM).** `Valid` uses the uniform reading, with `succ 0 = 0` and pad ≡ 0: paths from LayP_0 to LayP_0 with counts dem∓. `jcp_iff_jcpOne` (Lib) proves, for k = 1 and pad = 0 on LayP_0, that this is **equivalent** to the manuscript's explicit k = 1 reading. That reading is the Lib predicate `JcpOne`: paths from X^out to X^in, u ∈ X^out starts exactly exc(u)⁻ paths, and v ∈ X^in ends exactly exc(v)⁺. So nothing is weakened or strengthened.
- **"Pairwise edge-disjoint".** This is `List.Pairwise` over list positions, the literal reading. `Valid.nodup_flatMap_walkEdges` converts it to "each edge of E(𝒫_j) is on exactly one path".
- **`bb_disj` is kept literally**, although (D) implies it. Keeping an implied hypothesis does not weaken the lemma.
- **(P) is kept literally**, although admissibility implies it (`Cluster.IsAdmissible.parityClean`; HCCP-P-REDUNDANT).
- **(D) for hubs and ports of one cluster** is `Cluster.disjoint`. The sets `A_𝒦 ∪ U_𝒦` of distinct indices are disjoint; this is equivalent to the four pairwise conditions between {A_i, U_i} and {A_i', U_i'}.
- **One-vertex paths** (the caveat on `IsPathIn`) cannot occur in a valid system. For k ≥ 2 the first and last vertices lie in disjoint layers (`layP_disjoint`). For k = 1, exc cannot be both < 0 and > 0 (see the `JcpOne` direction). The `head?`/`getLast?` membership conjuncts are explicit.

## Lib API (`EG/Lib/Chain/*.lean`)
- **Cluster.**
  - `excPos_cast`, `excNeg_cast`, `exc_eq_excPos_sub_excNeg`, `excPos_eq_zero_or_excNeg_eq_zero`.
  - `Cluster.mem_verts`, `hubs_subset_verts`, `ports_subset_verts`, `not_mem_ports_of_mem_hubs`, `mem_verts_of_mem_beads`, `exists_port_of_mem_beads`.
  - `mem_portBeads`, `mem_beadNbrs`, `card_beadNbrs` (#B-neighbours = deg_B).
  - `IsAdmissible.parityClean`, `beadCount_eq_natCast` (under ParityClean), `load_cast`, `mem_medOrient`.
- **EqLpt.** `emptyBefore_of_forall_le`, `loadBefore_of_forall_le` (before the first item), `sum_layerLoad` (Σ_j Φ^lay_j = Σ_i Φ_i), `layerLoad_nonneg`.
- **HCCP.**
  - `succ_val`, `succ_eq_self` (k = 1), `succ_ne_self` (k ≥ 2).
  - `mem_layP`, `ports_subset_layP`, `layP_disjoint` (under (D)), `pexc_eq` (under (D)).
  - `mem_pathEdges`, `mem_allPathEdges`, `mem_beads`.
  - `Valid.nodup_flatMap_walkEdges`, `JcpUniform`, `JcpOne`, `Valid.jcpUniform`, `jcp_iff_jcpOne`.

## Tests (`EGTest/Chain.lean`)
- **Cluster `K5` on `Fin 5`.** Hub 0, ports 1–4, beads 01, 02, 34, 13.
  - Checked by `decide`: `medOrient` equals the hand-computed arc set; `beadNbrs`, `portBeads`, `ParityClean`.
  - Excesses: exc = (2, −1, 0, −1) on ports 1–4, with sum 0. Load Φ = 2 and bead count b = 3, so Φ ≤ b as MED(b) predicts.
  - `O5` is admissible (orientation, potential, hub balance) but not `IsBalanced`.
- **Cluster `Kodd`.** Its hub has 3 neighbours. It is not parity-clean, has no admissible orientation, and b = 3/2.
- **No hub–hub bead.** No cluster has a bead joining two hubs.
- **EQ-LPT.** A greedy placement, a non-greedy one, and final loads.
- **HCC-P, k = 1: a triangle.** One hubless cluster with bead 0→1, T_0 = {2}, and the path 1 2 0.
  - `Valid` holds; Φ = 1 = |𝒫_0|; X^out = {1}, X^in = {0}; and `JcpOne` follows through `jcp_iff_jcpOne`.
  - Negative test: the reversed path makes the system invalid.
- **HCC-P, k = 2: a 4-cycle.** Two layers and direct port–port paths.
  - `Valid` holds; Φ_0 = Φ_1 = 1; `succ 1 = 0`.
  - Negative test: pad ≡ 1 breaks the demands.

## Not in this task; flagged for the integrator
- **PAR (s6:lemPAR).** Its definitions are the edge-set components of `EG/Defs/Components.lean` (TRIAGE item 5), which another task wrote. The predicate for an admissible choice J′ is not in any Defs file; the blueprint proposes `EG.Chain.IsParChoice`. The blueprint's text reads: "one edge of each odd component, none of each even component, each a non-bridge or pendant edge of its component".
  - It is a statement-shape predicate, so it can go in the PAR Spec file.
  - If s6:lemJplus needs it too, it could go in a small `EG/Defs/Chain/Par.lean` on top of `Components`.

  I did not create that file, because it is outside this task's file list.
- **The MED, EQ-LPT and HCC-P statements** (`MedStatement`, `MedExcStatement`, `EqLptStatement`, `HccpStatement`, `HccGlobStatement`) are Spec work. The Defs above match the blueprint's `lean_shape` sketches, with these differences:
  - `Cluster.exc` becomes `EG.Chain.exc`, since it does not depend on the cluster;
  - `beadCount` is real;
  - `pad_k1` is restricted to its domain;
  - `path_edisj` is `Pairwise`;
  - `Valid` adds `bb_disj`;
  - the (JC-P) path clause is split into `path_G`/`path_ends`/`path_T`.

  In the HCC-P Spec, "decomposes into at most Φ cycles" should read Φ as `S.Phi j` for any j (all are equal by (i)), or as `(S.P j).length`.

## Fix round 1 (review `work/p2d/chain.review1.md`, verdict APPROVE; 2 minor, 4 cosmetic)

After the fixes, everything compiles with 0 errors, 0 warnings and 0 `sorry`:
- `lake build EG.Lib.Chain.HCCP EG.Lib.Chain.EqLpt` (which rebuilds all three Defs files);
- `scripts/check.sh EGTest/Chain.lean`.

Lint is 0 findings. The axiom scan (`--prefix EG EG.Lib.Chain.HCCP EG.Lib.Chain.EqLpt`) inspects 666 constants and finds 0 violations and 0 `sorryAx`. No definition body or `Valid` field changed; the Defs edits are docstrings only.

| issue | verdict | action |
|---|---|---|
| **M1** no Lib bridge from padded load to cluster loads | valid | Added to `EG/Lib/Chain/HCCP.lean`, all under (D) = `D_KK`: `sum_layP` (a sum over `LayP_j` splits over the clusters of layer j, by `Finset.sum_biUnion`), `sum_ports_demPlus`, `sum_ports_demMinus`, `Phi_eq_sum_load_add_pad` (`S.Phi j = ∑_{lay i = j} (K i).load (O i) + ∑_{u∈layP j} pad u`), `sum_demMinus_eq` (`∑_{layP j} demMinus = ∑_{lay i = j} ∑_{ports} excNeg (O i) + ∑_{layP j} pad`), and the `Valid.`-versions of the last two. The step `∑ dem⁻ = Φ_j` needs `∑_{U} exc = 0`, which is Lemma MED(b), a manuscript lemma; it is deliberately not proved here (Spec/proof work). Tests: `S2` layer 0 (load 1, pad 0), and the `sum_demMinus_eq` instance. |
| **M2** no accessor for the common load Φ(𝒮) | valid (usability) | **Decision: no new Defs accessor; use the ∃-form.** HCCglob is stated as `∃ Φ : Fin q → ℕ, (∀ s j, (S s).Phi j = Φ s) ∧ … ∧ cs.length ≤ ∑ s, Φ s`. Reason: it adds no locked surface, and it is exactly the manuscript's "the common value Φ", which is determined because `Valid.k_pos` gives k ≥ 1. The Lib lemma `eq_of_forall_Phi_eq` (the common value is unique for k ≥ 1) supports it. The blueprint_s6a HccGlob sketch is annotated as SUPERSEDED, and a test shows both the ∃-form and uniqueness on `S2`. |
| **C1** Cluster/Valid do not require A, U, T_j ⊆ V(G) | valid | The `Cluster` docstring now records the generalization next to CL-G-FREE. It is harmless: all conclusions concern edges only, and the ends of beads and path edges lie in V(G) via `beads_G`/`path_G`. |
| **C2** numerals on `Fin S.k` | valid | Usage note added to the `EG.Defs.Chain.HCCP` module docstring: use `(0 : Fin 2)`, compare via `.val … := rfl`, and use indices at type `Fin S.k` inside `univ.filter (S.lay · = j)`. The last point was found while writing the new tests: with `(0 : Fin 2)` the `DecidablePred` instance is not found, so the tests use `S2j0 : Fin S2.k := ⟨0, by decide⟩`. The note also points to the ∃-form for Φ. |
| **C3** auxiliary defs untagged | valid | Tags added: `[s6:lemHCCP]` on `succ`, `pathEdges`, `allPathEdges`, `beads`; `[s6:lemEQLPT]` on `loadBefore`, `EmptyBefore`; `[s6:defCluster]` on `medPos`, `medRule`. Every top-level declaration docstring in `EG/Defs/Chain/*.lean` now starts with a manuscript label. |
| **C4** blueprint snippets outdated | valid | A note at the top of `work/p2/blueprint_s6a.md` lists the differences and points here, and the `Phi0` line of the HccGlob sketch is marked SUPERSEDED. The JSON twin `nodes_s6a.json` was not edited. TRIAGE was left untouched because it is binding and integrator-owned. |

### Differences from the blueprint `lean_shape` (for Spec authors)
- `EG.Chain.exc O u`, not `Cluster.exc`: it depends only on the orientation. `excPos`/`excNeg` are in ℕ.
- `Cluster.beadCount : ℝ`, not ℕ. MED(b)'s "Φ(𝒦) ≤ b(𝒦)" reads `(K.load O : ℝ) ≤ K.beadCount`.
- `Cluster.no_hub_hub : ∀ e ∈ beads, ¬ ∀ v ∈ e, v ∈ hubs`. The "some end is a port" form is the Lib lemma `exists_port_of_mem_beads`.
- `Valid.pad_k1 : S.k = 1 → ∀ j, ∀ u ∈ S.layP j, S.pad u = 0`, restricted to the domain of pad.
- `Valid.path_edisj : ∀ j, (S.P j).Pairwise (fun p q => (walkEdges p).Disjoint (walkEdges q))`. The Nodup form is `Valid.nodup_flatMap_walkEdges`.
- The path clause is split into `path_G`, `path_ends` and `path_T`. `starts`/`ends` use `List.countP`, not `filter … length`.
- The field names are `T_disj` (blueprint `D_TT`), `parityClean` (`P_clean`), `pp_disj` (`pdisj`), and `pb_disj : ∀ j i, Disjoint (S.pathEdges j) (S.K i).beads` (per cluster, not against `S.beads`). There is an extra field `bb_disj`.
- There is no `Phi0`; use `∃ Φ` (M2 above). `allPathEdges` exists for the input-level HCCglob hypothesis.
