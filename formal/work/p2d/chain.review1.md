# Clean-room definition review, round 1: [chain] (s6 routing-engine data)

Reviewer: clean-room definition reviewer, round 1 (2026-09-26).

Files reviewed (not edited):
- `EG/Defs/Chain/Cluster.lean`, `EG/Defs/Chain/EqLpt.lean`, `EG/Defs/Chain/HCCP.lean`;
- `EG/Lib/Chain/{Cluster,EqLpt,HCCP}.lean`;
- `EGTest/Chain.lean`;
- the design note `work/p2d/chain.md`.

Manuscript: `proofs/manuscript/s6.tex` v6.1.
- Lines 12–54: the preamble and s6:defCluster.
- Lines 56–101: s6:lemMED and s6:lemEQLPT.
- Lines 140–219: s6:lemHCCP and its proof.
- Lines 221–232: s6:lemHCCglob.
- Lines 443–612: s6:lemJSLC, the only consumer of the engine.

Blueprints: `work/p2/blueprint_s6a.md` (the nodes above) and `work/p2/blueprint_s6b.md` (the JS-LC node).

**Verdict: APPROVE.**
- I found no major issue.
- There are 2 minor issues (usability: Lib lemmas that JS-LC and the HCCglob Spec will want).
- There are 4 cosmetic issues.
- Every definition back-translates to the quoted manuscript text.
- Every Spec in the blueprints can be stated with these definitions. That covers MED(a), MED(b), EQ-LPT (existence and ∀-greedy), HCC-P (i) and (ii), HCCglob with input-level disjointness, and the uses inside JS-LC Steps 4–7.
- `HccpData.Valid` is non-vacuous in a richer configuration than the shipped tests: hubs, padding, non-empty junction interiors, and k = 2 and k = 3 (see §4).

Lint: `python3 scripts/lint.py` gives 0 findings.

## 1. Cluster.lean (s6:defCluster)

**`Cluster` (structure).**
- Back-translation: a cluster is a triple (A, U, B) with the following properties:
  - A ∩ U = ∅;
  - every b ∈ B is a non-loop with both ends in A ∪ U;
  - no b ∈ B has both ends in A.
- Manuscript: "A_𝒦 … and U_𝒦 … are disjoint vertex sets … B_𝒦 ⊆ E(G[A_𝒦∪U_𝒦]) … No bead has both ends in A_𝒦."
- Faithful under the documented G-free split (CL-G-FREE). The only G-dependent part, B ⊆ E(G), is `Valid.beads_G`. MED is G-free in the manuscript as well: its proof never uses G.
- `no_hub_hub` is the literal negation, `¬ ∀ v ∈ e, v ∈ hubs`. It is equivalent to the blueprint's `∃ v ∈ e, v ∈ ports`, given `ends_mem` (Lib `exists_port_of_mem_beads`).
- See cosmetic C1 for one further generalization.

**`exc`, `excPos`, `excNeg`.**
- These are d⁺ − d⁻ in ℤ, (exc)⁺ in ℕ and (−exc)⁺ in ℕ.
- They agree with "exc(u):=d⁺(u)−d⁻(u), exc(u)⁺:=max(exc(u),0), exc(u)⁻:=max(−exc(u),0)". The Lib lemmas `excPos_cast` and `excNeg_cast` give the max-form.
- Moving `exc` from `Cluster.exc` (blueprint) to `EG.Chain.exc` is correct: it depends on O only.

**`verts`, `portBeads`.**
- `portBeads` = `beads.filter (· ∈ ports.sym2)`, and its card is e(B[U]).
- `Finset.sym2` also contains diagonals, but beads are loopless, so this is exact.

**`beadCount : ℝ`.**
- The definition Σ_{h∈A} deg_B(h)/2 + e(B[U]) is literal.
- The real value is more faithful than the blueprint's ℕ division, which would floor ½-integers. It is a natural number under ParityClean (`beadCount_eq_natCast`), and the test `Kodd` gives b = 3/2.
- MED(b)'s "Φ(𝒦) ≤ b(𝒦)" is stated as `(K.load O : ℝ) ≤ K.beadCount`. JS-LC Step 4's "b(𝒦_C) = |E(C)|/2" is stateable.

**`ParityClean`.** Literal. Decidable.

**`IsAdmissible O`.**
- `IsOrientation beads O ∧ IsAcyclic O ∧ ∀ h ∈ hubs, outDeg = inDeg`.
- Manuscript: "an acyclic orientation of B_𝒦 in which every hub h has d⁺(h)=d⁻(h)".
- Balance is at hubs only, and `IsBalanced` is not used, as CONVENTIONS requires. The test shows `O5` is admissible but not `IsBalanced`.
- The arcs of O automatically lie in V(𝒦) × V(𝒦), because `IsOrientation.mem` and `ends_mem` force it.

**`load`.** Σ_{u∈U} exc(u)⁺, as in the manuscript.

**`beadNbrs`, `medPos`, `medRule`, `medOrient`.**
- Back-translation. With `rk` injective on U, and for a hub h (all of whose B-neighbours are ports, by `no_hub_hub`), `medPos rk h u_i = i`. So:
  - `2·medPos ≤ #N(h)` ⇔ i ≤ d, and case 1 is "u_i → h for i ≤ d";
  - `#N(h) < 2·medPos` ⇔ i > d, and case 2 is "h → u_i for i > d";
  - case 3 is "port–port bead uv with u ≺ v is oriented u → v".
- Every linear order of the finite set U is realised by some ℕ-rank injective on U, and conversely. So quantifying over `rk` with `Set.InjOn rk K.ports` is exactly "every linear order ≺ on U_𝒦".
- Totality (CL-MED-TOTAL) is harmless: the MED Spec carries ParityClean and InjOn.
- Checked by scratch tests:
  - a hub of degree 4 with the reversed rank gives exactly {4→0, 3→0, 0→2, 0→1}, i.e. the two lowest-rank neighbours inward;
  - the shipped `K5` test passes.

## 2. EqLpt.lean (s6:lemEQLPT)

**`loadBefore`, `EmptyBefore`, `IsGreedyLPT`, `layerLoad`.**
- Back-translation. σ places item i so that:
  - (G1) layer σ(i) has minimum load among all layers just before i;
  - (G2) if some layer is empty just before i, then σ(i) is empty just before i.
- Manuscript: "Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists."
- "Empty" means "has received no item" (`EmptyBefore`), not "has load 0". That matters when some Φ_i = 0, and it is right. The scratch test rejects placing a load-0 item on the non-empty load-1 layer while another layer is empty.
- With nonnegative loads, (G1) and (G2) are compatible, and existence is a Spec conjunct, as the blueprint requires.
- The relation encoding (EQ-GREEDY-RELATION) matches "ties arbitrary", and the Spec quantifies over every greedy σ.
- Index types `Fin m`, `Fin k` and real loads (EQ-REAL-VS-NAT) are as the blueprint recommends. The JS-LC uses cast ℕ loads (Φ(𝒦_C), unit cherry loads) and compose σ with a sorting of the clusters. That is expressible.

## 3. HCCP.lean (s6:lemHCCP)

**Data (`HccpData`).** The fields are k, N, `K : Fin N → Cluster V`, `O`, `lay : Fin N → Fin k`, `T : Fin k → Finset V`, `pad : V → ℕ` and `P : Fin k → List (List V)`. They cover every datum of the lemma:
- the layers, as an indexed family with a layer map (CL-IDENTITY);
- the fixed orientations;
- the junction sets;
- the padding;
- the path families.

The families are data (HCCP-JCP-AS-DATA), which is needed because conclusion (ii) mentions E(𝒫_j). Index types are right for every use:
- JS-LC builds `T j := T_j(Y,l)` for j < k ≤ K^JS;
- `lay` comes from EQ-LPT's σ;
- `P j` comes from the joint-routing family, via `List.ofFn`.

**Derived definitions.**
- `succ` is (j+1) mod k: "Indices … are taken modulo k". A scratch test confirms the wrap at k = 3.
- `layP` is LayP_j.
- `pexc` is exc(u) in the unique cluster containing u. It is unique under `D_KK`, and `pexc_eq` proves it.
- `demMinus` and `demPlus` are exc⁻ + pad and exc⁺ + pad.
- `Phi` is Σ_{LayP_j} dem⁺.
- `xOut` and `xIn` are X^out and X^in.
- `pathEdges` is E(𝒫_j), `allPathEdges` is ⋃_j E(𝒫_j), and `beads` is ⋃ B_𝒦.

All are literal.

**Hypotheses (`Valid`).** I compared each field with the manuscript clause:

| Manuscript clause | Lean field(s) |
|---|---|
| "k≥1" | `k_pos` |
| "each cluster with a fixed admissible orientation" | `adm` |
| B ⊆ E(G) | `beads_G` |
| "Junction sets … pairwise disjoint" | `T_disj` |
| "pad≡0 if k=1" | `pad_k1`, on the domain ⋃LayP_j. Restricting it to the domain is faithful (pad is only defined there) and is the more general hypothesis. |
| (D) | `Cluster.disjoint` + `D_KK` + `D_KT` + `T_disj`. This is complete for the family {A_i, U_i}_i ∪ {T_j}_j. |
| (P) | `parityClean` |
| "paths of G" | `path_G` |
| "runs from LayP_j to LayP_{j+1}" | `path_ends` |
| "interior vertices … in T_j" | `path_T` |
| the two exact counts | `starts` and `ends`, as `countP`, i.e. with multiplicity |
| "pairwise edge-disjoint" | `path_edisj`, over list positions. This is the literal family reading: duplicated paths are correctly forbidden. |
| "E(𝒫_0),…,E(𝒫_{k−1}) and all bead sets pairwise disjoint" | `pp_disj`, `pb_disj`, `bb_disj`. All three kinds of pair are covered. |

- I found no hypothesis that is stronger than the manuscript. The family reading of (D) for distinct indices forbids repeating a non-empty cluster in two layers. That is required: with such a repeat, Step 1's source/sink facts fail. JS-LC never does it.
- **k = 1.** The uniform reading is equivalent to the manuscript's explicit k = 1 reading. `jcp_iff_jcpOne` is a proof of the equivalence, not merely a claim; I read it and it uses `pad_k1` for the pad = 0 premise. One-vertex paths are excluded in all cases: by disjoint layers for k ≥ 2, and because exc cannot be both < 0 and > 0 for k = 1.
- **Soundness sanity check.** I re-ran Steps 0–4 of the manuscript proof against the Lean hypotheses and found no gap:
  - direct port→port paths of length 1 are covered by `pb_disj` and by the W-arc argument;
  - a path edge can never touch a hub, by `path_T` + `D_KT` and because endpoints are ports;
  - the union of the arc sets is an arc set, by `path_edisj`, `pp_disj` and `pb_disj`.

  So the eventual HCC-P Spec on this bundle is not false for a formal reason.

**Downstream stateability.**
- HCC-P (i): `∃ Φ, ∀ j, S.Phi j = Φ ∧ (S.P j).length = Φ`.
- HCC-P (ii): `F j ⊆ S.pathEdges j`, `S.pathEdges j \ F j ⊆ (S.T j).sym2`, and IsDecomp of `S.beads ∪ ⋃ F`, with `max 3 S.k ≤ c.length`.
- HCCglob with input-level disjointness: `(S s).beads ∪ (S s).allPathEdges`.
- JS-LC Steps 4–7: MED on components, EQ-LPT layering, padding ≤ ⌈M/2⌉, cherries, and the (D), (P) and (JC-P) checks of Step 7.

All of these are expressible. The JS-LC Spec (blueprint_s6b) does not mention these definitions at all; they are proof-internal there.

## 4. Non-vacuity (scratch tests, `/tmp/chainrev/T1.lean`, compiles with 0 errors)

- **k = 2 with a hub, padding and junction interiors.** `Valid` holds (`S_valid`, all fields checked by `decide`/`fin_cases`), with Φ_0 = Φ_1 = 2 = |𝒫_0| = |𝒫_1|. The system:
  - layer 0 is hub 0 with ports 1, 2 and beads 01, 02, oriented 1→0→2;
  - layer 1 is the bead 3→4;
  - pad(2) = pad(4) = 1;
  - 𝒫_0 = [2 5 3], [2 6 4] with T_0 = {5,6};
  - 𝒫_1 = [4 7 1], [4 8 2] with T_1 = {7,8}.
- **k = 3.** A 6-cycle of three one-bead clusters, with `succ 2 = 0`. The path-end conditions hold, and they fail for the reversed direction (paths from layer j to layer j−1).
- **k = 1 with pad ≠ 0 on a port.** Rejected by `pad_k1`.
- **MED.**
  - The hub-degree-4 median split is as computed in §1.
  - `medOrient` is total on the non-parity-clean `Kodd`, and also with a non-injective rank.
- **EQ-LPT.** (G2) rejects a load-0 item placed on a non-empty layer while an empty layer exists.

## 5. Issues

**M1 (minor, usability, Lib). No Lib bridge between the padded load and the cluster loads.**
- JS-LC Step 4 ("Φ^raw_j = … Σ Φ(𝒦_C)", "Π_j units of padding … all padded loads equal Φ*") and HCC-P Step 0 both need one of the identities below. A Lib lemma under `D_KK` would be the natural home. The lemma would be:

  `S.Phi j = ∑ i with S.lay i = j, (S.K i).load (S.O i) + ∑ u ∈ S.layP j, S.pad u`

  or, equivalently, `∑_{u∈layP j} demPlus u` split as a disjoint biUnion over the clusters of layer j.
- The same holds for `∑ demMinus` (with MED(b)'s Σ exc = 0).
- It is not a Defs defect. It belongs in `EG/Lib/Chain/HCCP.lean` before probe P-2 starts on JS-LC.

**M2 (minor, usability). There is no accessor for the common load Φ(𝒮) of a system.**
- The HCCglob Spec sketch in blueprint_s6a uses `(S s).Phi0`, which does not exist. `S.Phi ⟨0, _⟩` needs `k_pos` inside the statement.
- Options:
  - state HCCglob with `∃ Φ : Fin q → ℕ, (∀ s j, (S s).Phi j = Φ s) ∧ cs.length ≤ ∑ s, Φ s`, which needs no new definition;
  - or add a Lib/Defs `HccpData.load0 : ℕ := if h : 0 < S.k then S.Phi ⟨0, h⟩ else 0`.
- The Spec author must pick one. Adding the accessor now is cheap, if it is wanted in Defs before the lock.

**C1 (cosmetic, docstring). The G-free `Cluster` does not require A ∪ U ⊆ V(G), and `Valid` does not require T_j ⊆ V(G).**
- "Vertex sets" in the manuscript implicitly means subsets of V(G). The Lean hypotheses are therefore slightly more general.
- This is harmless: the HCC-P conclusions concern edges only, and paths with an edge automatically have their vertices in V(G).
- Mention it in the `Cluster` docstring next to CL-G-FREE.

**C2 (cosmetic, usability). Numerals and `decide` on `Fin S.k` for a concrete `S`.**
- `S.Phi 0` fails, because there is no `OfNat (Fin S.k) 0`. One needs `(0 : Fin 2)`.
- `decide` cannot decide `S3.succ 2 = 0` at type `Fin S3.k`; `.val … = … := rfl` works.
- The shipped tests already use ascriptions. A one-line note in the HCCP module docstring would save test and probe writers time.

**C3 (cosmetic). Auxiliary definitions lack a manuscript-label tag.**
- The untagged definitions are `loadBefore`, `EmptyBefore`, `succ`, `pathEdges`, `allPathEdges`, `beads`, `medPos` and `medRule`.
- They are helpers, but `succ` ("Indices … modulo k") and `pathEdges` (E(𝒫_j)) quote manuscript text and could carry `[s6:lemHCCP]`, for consistency with the AGENTS.md tagging rule.

**C4 (cosmetic). The design note lists "Differences from the blueprint lean_shape".**
- They are: `exc` namespace, real `beadCount`, `pad_k1` domain, `Pairwise` edge-disjointness, the extra `bb_disj`, and the split path clause.
- The MED/HCC-P Spec authors must use `EG.Chain.exc` (not `Cluster.exc`) and a real-valued `beadCount`. The blueprint snippets are outdated there.
- A pointer in blueprint_s6a (or in TRIAGE §2.9) would prevent a failed first Spec draft.

## 6. Summary for the integrator

The three Defs files are faithful, total and usable. Lock them after round 2. Before P-2 reaches JS-LC:
- add the M1 Lib lemmas;
- decide M2 (the ∃-form in the HCCglob Spec is sufficient).
