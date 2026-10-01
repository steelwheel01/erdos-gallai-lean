# Clean-room definition review, round 2: [chain] (s6 routing-engine data)

Reviewer: clean-room definition reviewer, round 2 (2026-09-26). Independent of round 1
(`chain.review1.md`), which I read only after forming my own back-translations; I also checked
that the round-1 fixes landed.

Files reviewed (not edited):
- `EG/Defs/Chain/Cluster.lean`, `EG/Defs/Chain/EqLpt.lean`, `EG/Defs/Chain/HCCP.lean` (to be locked);
- `EG/Lib/Chain/{Cluster,EqLpt,HCCP}.lean`, `EGTest/Chain.lean`, design note `work/p2d/chain.md`.

Manuscript: `proofs/manuscript/s6.tex` v6.1 — preamble (l. 12–17), s6:defCluster (33–54),
s6:lemMED (56–88), s6:lemEQLPT (90–103), s6:lemHCCP (140–219), s6:lemHCCglob (221–232),
and the consumer s6:lemJSLC (443–612, Steps 4–7). Blueprints `blueprint_s6a.md` (nodes
defCluster, lemMED, lemEQLPT, lemPAR, lemHCCP, lemHCCglob) and `blueprint_s6b.md` (JS-LC node);
TRIAGE §2.9 and §3 items 21–23.

Checks run (read-only):
- `python3 scripts/lint.py`: 0 findings.
- `scripts/check.sh EGTest/Chain.lean`: 0 errors, 0 sorry.
- `scripts/Axioms.lean --prefix EG EG.Lib.Chain.HCCP EG.Lib.Chain.EqLpt`: 666 constants, 0 violations, 0 sorryAx.
- Own scratch file (scratchpad `R2.lean`, 0 errors): see §5.

**Verdict: APPROVE (lock the three Defs files).**
- No major issue: every definition back-translates to the quoted manuscript text; no field is
  missing and no index type is wrong for any downstream use listed in the blueprints (§4).
- No minor issue in the Defs. Four cosmetic items (§6), all in Lib/tests/integration, none of
  which touches a definition body or a `Valid` field.
- The round-1 fixes (M1 Lib bridge, M2 ∃-form for Φ, C1–C4) are in place and correct.

## 1. `Cluster.lean` (s6:defCluster)

| Lean | back-translation | manuscript (s6.tex:33–54) | verdict |
|---|---|---|---|
| `structure Cluster`: `hubs ports : Finset V`, `beads : Finset (Sym2 V)`, `disjoint`, `loopless`, `ends_mem`, `no_hub_hub` | (A, U, B) with A ∩ U = ∅; every bead a non-loop with both ends in A ∪ U; no bead with both ends in A | "A_𝒦 … and U_𝒦 … are disjoint vertex sets. … B_𝒦 ⊆ E(G[A_𝒦∪U_𝒦]) … No bead has both ends in A_𝒦." | faithful under the G-free split (TRIAGE §2.9; `B ⊆ E(G)` is `Valid.beads_G`). `no_hub_hub` is the literal negation; with `ends_mem` it is equivalent to "some end is a port" (Lib `exists_port_of_mem_beads`). |
| `exc O u : ℤ := d⁺ − d⁻`; `excPos := (exc).toNat`; `excNeg := (−exc).toNat` | exc, exc⁺ = max(exc,0), exc⁻ = max(−exc,0) | "exc(u):=d⁺(u)−d⁻(u), exc(u)⁺:=max(exc(u),0), exc(u)⁻:=max(−exc(u),0)" | faithful (`excPos_cast`, `excNeg_cast`). Orientation explicit (CL-ORIENT-IS-DATA); `EG.Chain.exc` rather than `Cluster.exc` is right, it does not depend on 𝒦. |
| `verts := hubs ∪ ports` | V(𝒦) | "Put V(𝒦):=A_𝒦∪U_𝒦" | faithful |
| `portBeads := beads.filter (· ∈ ports.sym2)`; `beadCount : ℝ := Σ_{h∈hubs} deg_B(h)/2 + #portBeads` | b(𝒦) as a real | "b(𝒦):=∑_{h∈A_𝒦}deg_{B_𝒦}(h)/2+e(B_𝒦[U_𝒦])" | faithful. `Finset.sym2` contains diagonals, but beads are loopless, so `portBeads` is exactly B[U]. ℝ is the right choice (ℕ-division would floor for non-parity-clean 𝒦; test `Kodd` gives 3/2); `beadCount_eq_natCast` gives the ℕ form under ParityClean. |
| `ParityClean := ∀ h ∈ hubs, Even (degE beads h)` | every hub has even B-degree | "parity-clean if every hub has even B_𝒦-degree" | faithful, decidable |
| `IsAdmissible O`: `IsOrientation beads O`, `IsAcyclic O`, `∀ h ∈ hubs, outDeg = inDeg` | acyclic orientation of B, balanced at hubs | "an acyclic orientation of B_𝒦 in which every hub h has d⁺(h)=d⁻(h)" | faithful; hub-local balance, `IsBalanced` not used (CONVENTIONS). Arcs automatically lie in V(𝒦)² (`IsOrientation.mem` + `ends_mem`). |
| `load O : ℕ := Σ_{u∈ports} excPos O u` | Φ(𝒦) | "Φ(𝒦):=∑_{u∈U_𝒦}exc(u)⁺" | faithful (`load_cast`) |
| `beadNbrs h`, `medPos rk h u := #{w ∈ N_B(h) : rk w ≤ rk u}`, `medRule`, `medOrient rk` | see below | "At a hub h with B_𝒦-neighbours u_1≺…≺u_{2d}, it orients u_i→h for i≤d and h→u_i for i>d … A port–port bead uv with u≺v is oriented u→v" | faithful; see below |

**MED back-translation.** ≺ is the order `rk u < rk v` for a rank `rk : V → ℕ` injective on U
(every linear order of a finite set arises this way, and conversely). For a hub h all
B-neighbours are ports (`no_hub_hub`), so with `rk` injective on U the neighbour u_i has
`medPos rk h u_i = i` (1-based, u_i counts itself). Hence:
- case 1 `(x ∈ U ∧ y ∈ A ∧ 2·medPos y x ≤ #N(y))` is "u_i → h for i ≤ d" (2d = #N(h) = deg_B(h) by `card_beadNbrs`);
- case 2 `(x ∈ A ∧ y ∈ U ∧ #N(x) < 2·medPos x y)` is "h → u_i for i > d";
- case 3 `(x ∈ U ∧ y ∈ U ∧ rk x < rk y)` is "u → v for u ≺ v".

`medOrient` filters `verts ×ˢ verts` by "xy is a bead ∧ medRule"; the guard is redundant
(`mem_medOrient`) but harmless. Totality (CL-MED-TOTAL): for a non-parity-clean cluster or a
non-injective rank the value is junk; Lemma MED is stated under ParityClean and `Set.InjOn rk
K.ports`. Scratch check (§5, T4): a hub of degree 4 with the reversed rank gives exactly
`{4→0, 3→0, 0→2, 0→1}` (the two ≺-lowest neighbours inward); with the constant rank all four
neighbours get `medPos = 4 > d`, every arc leaves the hub, and the result is not admissible —
which confirms that the junk case is really excluded only by the InjOn hypothesis of the Spec.

"Every bead is oriented exactly once" is a claim, correctly left to MED(a) (`IsOrientation`).

Edge cases: empty cluster; hub with no beads (no arcs, `medPos` irrelevant); hubless cluster
(only case 3 fires). All fine.

## 2. `EqLpt.lean` (s6:lemEQLPT)

| Lean | back-translation | manuscript (s6.tex:90–93) |
|---|---|---|
| `loadBefore Φ σ i j := Σ_{i' < i, σ i' = j} Φ i'` | load of layer j just before item i | "currently … load" (items placed in order 1..m) |
| `EmptyBefore σ i j := ∀ i' < i, σ i' ≠ j` | layer j has received no item before i | "initially empty layers … an empty layer" |
| `IsGreedyLPT Φ σ := ∀ i, (∀ j, loadBefore i (σ i) ≤ loadBefore i j) ∧ ((∃ j, EmptyBefore i j) → EmptyBefore i (σ i))` | (G1) minimum-load layer; (G2) empty layer whenever one exists | "Each item goes to a layer of currently minimum load, and to an empty layer whenever one exists" |
| `layerLoad Φ σ j := Σ_{σ i = j} Φ i` | final layer load | "the final layer loads Φ^lay_j" |

- "Empty" = "received no item", not "load 0": right, and it matters only for zero loads (the
  Spec's `Function.Surjective σ` is the manuscript's "all k layers are non-empty").
- Ties arbitrary ⇒ relation, ∀ greedy σ in the Spec, existence as conjunct (0) (EQ-GREEDY-RELATION).
  (G1) and (G2) are compatible under `0 ≤ Φ` (an empty layer has load 0 = minimum), which the
  Spec assumes; the manuscript proof says exactly this ("So the rule is consistent").
- `Fin m`/`Fin k` 0-based (Φ_1 = `Φ ⟨0,_⟩`), real loads (EQ-REAL-VS-NAT), `Antitone Φ` is the
  ordering hypothesis. Scratch T3: loads 2,2,1,1 into 2 layers — two tie-breaking placements are
  greedy, the placement sending item 3 to the heavier layer is rejected by (G1); `Antitone Φ4`
  is stateable and provable by `decide` after `Nat.cast_le`.

## 3. `HCCP.lean` (s6:lemHCCP)

**Data `HccpData`**: `k N : ℕ`, `K : Fin N → Cluster V`, `O : Fin N → Finset (V×V)`,
`lay : Fin N → Fin k`, `T : Fin k → Finset V`, `pad : V → ℕ`, `P : Fin k → List (List V)`.
This is every datum of the lemma: layers as an indexed family with a layer map (a cluster may be
repeated only if empty, since (D) is stated for distinct indices — exactly the manuscript's
"families"), fixed orientations, junction sets, padding (junk off ports, HCCP-PAD-DOMAIN), and
the path families as data (HCCP-JCP-AS-DATA; forced by conclusion (ii) "F_j ⊆ E(𝒫_j)").

**Derived definitions** (all literal): `succ j = (j+1) mod k` ("Indices … modulo k"; `succ`'s
positivity proof uses `j.2`, so no `k_pos` is needed in the definition), `layP j = ⋃_{lay i = j} U_i`,
`pexc u = Σ_i [u ∈ U_i] exc (O i) u` (= exc in the unique cluster of u under (D), `pexc_eq`),
`demMinus = exc⁻ + pad`, `demPlus = exc⁺ + pad`, `Phi j = Σ_{LayP_j} dem⁺`, `xOut`/`xIn`
(X^out/X^in, for any layer; used at j = 0, k = 1), `pathEdges j = E(𝒫_j)` (as a Finset),
`allPathEdges`, `beads = ⋃ B_𝒦`.

**Hypotheses `Valid S G`**, clause by clause against s6.tex:140–160:

| clause | field(s) | note |
|---|---|---|
| "Let k ≥ 1" | `k_pos` | |
| "each cluster with a fixed admissible orientation" | `adm` | |
| B_𝒦 ⊆ E(G) (from "B_𝒦 ⊆ E(G[A∪U])") | `beads_G` | the G part of the split |
| "Junction sets T_0,…,T_{k−1}: pairwise disjoint" / (D) | `T_disj` | |
| "pad ≡ 0 if k = 1" | `pad_k1 : k = 1 → ∀ j, ∀ u ∈ layP j, pad u = 0` | on the domain ⋃ LayP_j: literal; weaker than `∀ u` (so the lemma is stronger, never weaker) |
| (D) A_𝒦, U_𝒦 over all clusters pairwise disjoint | `Cluster.disjoint` (same index) + `D_KK` (distinct indices, on `verts`) | `Disjoint (A_i ∪ U_i) (A_i' ∪ U_i')` ⇔ the four pairwise conditions |
| (D) clusters vs T_j | `D_KT` | |
| (P) | `parityClean` | redundant given `adm` (`IsAdmissible.parityClean`), kept for fidelity |
| "paths of G" | `path_G : IsPathIn G.edges p` | |
| "from a vertex of LayP_j to a vertex of LayP_{j+1}" | `path_ends` (`head?`/`getLast?`) | |
| "All interior vertices … lie in T_j" | `path_T : IsThrough (T j) p` | |
| "u ∈ LayP_j is the first vertex of exactly dem⁻(u) paths", "v ∈ LayP_{j+1} the last vertex of exactly dem⁺(v)" | `starts`, `ends` via `List.countP` | multiplicities, as for a family |
| "pairwise edge-disjoint paths" | `path_edisj : (P j).Pairwise (walkEdges · disjoint)` | over list positions: forbids a repeated path, as the manuscript does |
| "E(𝒫_0),…,E(𝒫_{k−1}) and all bead sets B_𝒦 pairwise disjoint" | `pp_disj`, `pb_disj`, `bb_disj` | all three kinds of pairs |

Nothing is stronger than the manuscript, nothing is missing. In particular there is no hidden
hypothesis the manuscript proof needs and `Valid` lacks: I re-ran Steps 0–4 against the fields.
Step 1 (ports are sources/sinks of D_j) uses `path_T` + `D_KT` (no port interior), `path_ends` +
`layP_disjoint` (k ≥ 2) or exc-sign (k = 1); Step 2 (balance) uses that a port of layer j is a
first vertex only in 𝒫_j and a last vertex only in 𝒫_{j−1} (again `path_ends` + disjoint
layers), and that the union of arc sets is an orientation (`path_edisj`, `pp_disj`, `pb_disj`,
plus `bb_disj`/(D) for beads); Step 3 uses `adm.acyclic` and `D_KT`; Step 4 is GATE. Antiparallel
arcs cannot arise: they would be one edge of G in two of the sets that `pp_disj`/`pb_disj`/
`path_edisj` declare disjoint.

**k = 1.** The uniform reading (`succ 0 = 0`, `pad = 0` on LayP_0) is *equivalent* to the
manuscript's explicit reading, and `jcp_iff_jcpOne` (Lib) proves it, both directions, using
`pad_k1` for the pad premise. I checked the argument: a first vertex u starts ≥ 1 path so
`dem⁻(u) = exc⁻(u) ≥ 1`, i.e. u ∈ X^out; conversely for u ∈ LayP_0 \ X^out, `exc⁻(u) = 0` and u
starts no path because all first vertices lie in X^out. Nothing weakened or strengthened.

**One-vertex paths** (`IsPathIn` caveat, CONVENTIONS) cannot occur in a valid system: for
k ≥ 2 first and last vertex lie in disjoint layers; for k = 1 the vertex would have both
`pexc < 0` and `pexc > 0`. So the explicit head/last conjuncts suffice.

**Docstrings** quote the manuscript verbatim (I compared each quoted clause with the TeX) and
every top-level declaration carries a `[s6:…]` tag.

## 4. Downstream stateability (every use in the blueprints)

All of the following elaborate with the shipped names (scratch T5–T8 type-check the Spec shapes):

| use | statement with the Defs | ok |
|---|---|---|
| MED(a) (`MedStatement`) | `K.ParityClean → Set.InjOn rk K.ports → K.IsAdmissible (K.medOrient rk) ∧ ∃ pot : V → ℝ, (∀ v ∈ K.verts, 0 < pot v ∧ pot v < 1) ∧ ∀ a ∈ K.medOrient rk, pot a.1 < pot a.2` | ✓ |
| MED(b) (`MedExcStatement`) | `K.IsAdmissible O → (∀ u ∈ K.ports, (exc O u).natAbs ≤ degE K.beads u ∧ Even (exc O u − (degE K.beads u : ℤ))) ∧ ∑ u ∈ K.ports, exc O u = 0 ∧ (K.load O : ℝ) ≤ K.beadCount` | ✓ |
| Lib corollary `exists_admissible` | `K.ParityClean → ∃ O, K.IsAdmissible O` | ✓ |
| EQ-LPT (`EqLptStatement`) | `1 ≤ k → k ≤ m → Antitone Φ → (∀ i, 0 ≤ Φ i) → (∃ σ, IsGreedyLPT Φ σ) ∧ ∀ σ, IsGreedyLPT Φ σ → Function.Surjective σ ∧ ∀ j j', layerLoad Φ σ j − layerLoad Φ σ j' ≤ Φ ⟨0,_⟩` | ✓ |
| HCC-P (i) | `∃ Φ, ∀ j, S.Phi j = Φ ∧ (S.P j).length = Φ` | ✓ |
| HCC-P (ii) | `∃ F : Fin S.k → Finset (Sym2 V), (∀ j, F j ⊆ S.pathEdges j) ∧ (∀ j, S.pathEdges j \ F j ⊆ (S.T j).sym2) ∧ ∃ cs, IsDecomp ↑(S.beads ∪ univ.biUnion F) (cs.map Obj.cycle) ∧ (∀ j, cs.length ≤ S.Phi j) ∧ ∀ c ∈ cs, max 3 S.k ≤ c.length` | ✓ ("cycles of G" is automatic: the decomposed set ⊆ E(G) by `beads_G`, `path_G`) |
| HCCglob, input-level disjointness (TRIAGE GLOB-OUTPUT-LEVEL-HYP), ∃-form for Φ (round-1 M2) | `(∀ s, (S s).Valid G) → (∀ s ≠ s', Disjoint ((S s).beads ∪ (S s).allPathEdges) (…)) → ∃ Φ : Fin q → ℕ, (∀ s j, (S s).Phi j = Φ s) ∧ ∃ F : (s : Fin q) → Fin (S s).k → Finset _, … ∧ cs.length ≤ ∑ s, Φ s` | ✓ (no cross-system vertex condition, GLOB-NO-VERTEX-DISJ) |
| JS-LC Step 4: 𝒦_C = (centres, ports, E(C)) with MED, `Φ ≤ b = |E(C)|/2`, `|exc| ≤ M−1`, `Φ ≥ 1` | `Cluster` from the four proofs; `O := K.medOrient rk`; `K.beadCount = (E(C).card : ℝ)/2`; `(exc O u).natAbs ≤ M − 1`; `1 ≤ K.load O` | ✓ |
| JS-LC Step 4: EQ-LPT layering of loads Φ(𝒦_C) ∈ ℕ into k_0 layers; `lay := σ` | `Φ := fun i => ((K i).load (O i) : ℝ)` on the sorted enumeration, `HccpData.lay := σ` | ✓ (`Fin N → Fin k` is what EQ-LPT returns) |
| JS-LC Step 4: padding, "Φ^raw_j = ½ Σ_{LayP_j} |exc|", all padded loads equal Φ* | `pad : V → ℕ` with `pad u ≤ ⌈(M−1)/2⌉`; `Valid.Phi_eq_sum_load_add_pad` (round-1 M1) + MED(b) | ✓ |
| JS-LC Step 5: cherry ({h},{u,u'},{hu,hu'}), orientation u→h→u', load 1, exc ±1 | scratch T8: `cherry h u u'` is a `Cluster`, admissible with `{(u,h),(h,u')}`, `load = 1`, `exc u = 1`, `exc u' = −1`, `beadCount = 1` | ✓ |
| JS-LC Step 5: k_i layers of unit loads, `pad ≤ 1`, `Φ(𝒮_i) ≤ …` | as above with `Φ := 1` (Antitone trivially) | ✓ |
| JS-LC Step 6/7: `T j := T_j(Y,l)` for j < k ≤ K^JS; `P j` from the joint-routing family (`IsPathConnected.exists_paths`, an indexed family → `List.ofFn`); (D),(P),(JC-P) checks; HCCglob over all systems of all (Y,l) | `T : Fin k → Finset V` via `⟨j.val, _⟩`; `List.pairwise_ofFn` gives `path_edisj`; `Fin q → HccpData V` for the union | ✓ |
| JS-LC claim (c) "dem⁻ at junction j_u and dem⁺ at junction j_u − 1, j_u ≠ j_u − 1 mod k" | `demMinus`/`demPlus`; the predecessor is the j' with `S.succ j' = j_u` (exists and is unique for k ≥ 1; `succ_ne_self` for k ≥ 2) | ✓ (a Lib lemma would help, C2) |
| J⁺ / MIX-C: "HCC-P output consists of cycles only" | `cs.map Obj.cycle` in the HCC-P Spec | ✓ |

The JS-LC, J⁺ and MIX-C *Specs* do not mention these definitions (they are proof-internal there),
so no Spec surface beyond MED/EQ-LPT/HCC-P/HCCglob depends on the chain Defs.

## 5. Non-vacuity and edge cases (scratch `R2.lean`, 0 errors)

- **T1, k = 1 with a hub cluster.** The shipped `K5` (hub 0, ports 1–4, MED(id) = `1→0→2, 3→4,
  1→3`, exc = (2,−1,0,−1)) on `Fin 7`, `T_0 = {5,6}`, paths `2 5 1` and `4 6 1`. `Valid` holds
  (all fields by `decide`, admissibility by potential), `Phi 0 = 2 = |𝒫_0|`,
  `xOut = {2,4}`, `xIn = {1}`, `JcpOne` via `jcp_iff_jcpOne`. HCC-P (ii) is true here by hand:
  `IsDecomp (beads ∪ E(𝒫_0)) [cycle 1 0 2 5, cycle 1 3 4 6]` (checked by `decide`). This is the
  first test with a hub *and* junction interiors *and* a port of |exc| = 2.
- **T2, k = 2 with three clusters (two in layer 1) and a padded port.** `pad 1 = 1` gives
  `dem⁻(1) = 2, dem⁺(1) = 1, dem⁺(0) = 1, dem⁻(0) = 0`; `𝒫_0 = [1 2],[1 4]`, `𝒫_1 = [3 0],[5 1]`.
  `Valid` holds, `Phi 0 = Phi 1 = 2`, `pexc` reads the right cluster for each port, and the
  seven edges decompose into `cycle 0 1 2 3` and `cycle 1 4 5` (by `decide`). Negative tests:
  repeating the non-empty cluster `CB` at two indices violates `D_KK`; padding vertex 0 as well
  breaks `starts` (dem⁻(0) = 1 but 0 starts no path). This confirms that padding adds a unit to
  *both* demands of a port, as the manuscript defines.
- **Duplicate path.** `𝒫_0 = [[1 3 0],[1 3 0]]` fails `path_edisj` (the positions-based
  `Pairwise` reading is the literal "pairwise edge-disjoint" for a family).
- **T3 EQ-LPT** ties/real loads/Antitone; **T4 MED** degree-4 hub, reversed rank, junk rank;
  **T5–T7** Spec shapes; **T8** cherry cluster — as described in §4.
- Shipped tests re-checked: `K5`/`O5` admissible but not `IsBalanced`; `Kodd` not parity-clean,
  no admissible orientation, b = 3/2; k = 1 triangle and k = 2 4-cycle systems valid, with
  negative tests; `Phi_eq_sum_load_add_pad`, `sum_demMinus_eq`, `eq_of_forall_Phi_eq` on `S2`.

## 6. Issues

No major, no minor. Cosmetic (none requires a change to a definition body or a `Valid` field):

**C1 (cosmetic, tests/usability). `List.Disjoint` has no `Decidable` instance in scope**, so
`path_edisj` for a family with ≥ 2 paths cannot be discharged by `decide` (the shipped tests only
have singleton families; round 1's scratch also). The working route is
`List.Pairwise.cons (fun q hq => by … rw [List.disjoint_iff_ne]; decide) (List.pairwise_singleton _ _)`,
or `(List.nodup_flatMap.1 h).2` from a `Nodup` of the concatenation (the converse of
`Valid.nodup_flatMap_walkEdges`). A one-line note in the HCCP module docstring's usage paragraph,
or a Lib constructor `path_edisj_of_nodup`, would save probe P-2 time. (Similarly `IsDecomp` over
the `Set` coercion needs `Finset.mem_coe` before `decide`; that is a Found matter, not chain.)

**C2 (cosmetic, Lib for P-2).** Two small lemmas the HCC-P proof and JS-LC claim (c) will want,
provable from the existing fields: (a) `succ` is a bijection of `Fin S.k` (injective; `∀ j, ∃! j',
S.succ j' = j`), giving the manuscript's "junction j − 1"; (b) `Valid → ∀ j, ∀ p ∈ S.P j,
1 ≤ pathLength p` (no one-vertex path; §3). Optionally `demMinus_eq : S.demMinus u = excNeg (S.O i) u
+ S.pad u` for `u ∈ (S.K i).ports` under (D) (currently `rfl` after `pexc_eq`, used inline in
`sum_ports_demMinus`). None of these is a Defs matter.

**C3 (cosmetic, integration).** The root files do not yet import the chain modules
(`EG.lean` has only `EG.Spec.Chain.Gate`/`EG.Proof.Chain.Gate`; `EGTest.lean` lacks
`EGTest.Chain`). The design note lists the six `EG` imports and the one `EGTest` import for the
orchestrator; this must happen at lock time so that `scripts/lock.py` and CI see the files.

**C4 (cosmetic, style).** Several docstring lines exceed 100 characters (e.g. `Cluster.lean:134`,
`HCCP.lean:116`). Other Defs files (`Orient.lean`, `Walk.lean`) do the same and no project rule
fixes a width, so this is optional reflowing only.

## 7. Summary for the integrator

The three Defs files are faithful to s6:defCluster, s6:lemMED (data), s6:lemEQLPT and s6:lemHCCP
(data and hypotheses), total with documented junk, hub-local admissibility as CONVENTIONS
requires, and every downstream statement of the s6a/s6b blueprints (MED a/b, EQ-LPT, HCC-P i/ii,
HCCglob in the ∃-form, and the JS-LC Steps 4–7 uses) elaborates against them. They do not
mention `M_l`, so the M-INTEGER gate does not apply. **Lock `EG/Defs/Chain/{Cluster,EqLpt,HCCP}.lean`
as they stand**; add the C3 root imports at lock time; C1/C2 are Lib additions for probe P-2.
