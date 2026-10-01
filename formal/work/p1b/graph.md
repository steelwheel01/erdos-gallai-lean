# P1b: graph foundations: design note

Task [graph]: FGraph, paths, neighbourhoods, balls, expanders (s1:citDef11), path connectivity
(s1:citDef7). Status (after fix round 1): everything compiles with 0 errors, 0 sorry and
0 warnings. The lint is clean, and the axiom scan (`--no-sorry`, prefix `EG`, modules
`EG.Defs.Graph EG.Defs.Walk EG.Defs.Expander EG.Lib.Found.Graph`) reports 270 constants and
0 violations.

## Modules
| Module | Contents |
|---|---|
| `EG.Defs.Graph` | `FGraph` (verts : Finset V, edges : Finset (Sym2 V), invariants `edge_verts`, `loopless`), `card` (= \|H\|), `Adj`, `nbrs` (N_H(v)), `deg` (d_H(v)), `minDeg`/`maxDeg` (δ, Δ), `edgesAt`/`degE` (deg_F(v)), `nbrSet` (Nbr_H(U)), `induce` (H[U]), `deleteVerts` (H − U), `deleteEdges` (H − F), `restrictEdges` (spanning subgraph with edges E(H) ∩ F), `edgesBetween`/`eBetween` (E_H(A,B), e_H(A,B)), `ofEdges` (total constructor), `ofSimpleGraph`, `toSimpleGraph` (converse, on all of `V`; added in fix round 1), `PartialOrder` (subgraph order) |
| `EG.Defs.Walk` | `walkEdges`, `pathLength` (number of edges), `IsPathIn E p`, `IsPathBetween E x y p`, `interior`, `IsThrough W p`, decidability instances, `ball H i U W` (= B^i_H(U,W)) |
| `EG.Defs.Expander` | `FGraph.IsExpander G ε s` (s1:citDef11), `FGraph.IsPathConnected G ℓ t W` (s1:citDef7, multiset clause; `ℓ t : ℝ`) |
| `EG.Lib.Found.Graph` | API lemmas (listed below) |
| `EGTest.Found` | tests (listed below) |

## Decisions
1. **Edge sets are `Finset (Sym2 V)`.** An `FGraph` carries two proof fields: every end of an
   edge is a vertex, and there are no loops. Every operation is total. `induce H U` has vertex
   set `V(H) ∩ U`, which is `U` when `U ⊆ V(H)` (`induce_verts_of_subset`). `deleteEdges H F`
   takes any `F`, and only `E(H) ∩ F` matters (`deleteEdges_inter_edges`). `edgesBetween` is
   defined for all `A, B`; the manuscript uses it only for disjoint `A`, `B`.
2. **Degree.** `d_H(v)` is defined as `|N_H(v)|`. `deg_eq_degE` proves `d_H(v) = deg_{E(H)}(v)`,
   the number of edges at `v`. `minDeg` is `0` on the graph with no vertices, as in Mathlib;
   `lt_minDeg_iff` converts `s < δ(H)` into a per-vertex statement.
3. **Paths are vertex lists (PLAN decision 1), defined relative to an edge set `E`.** A path of
   `H − F` is literally `IsPathIn (H.deleteEdges F).edges p`, with no transport. `IsPathIn`
   requires a non-empty list, no repeated vertex, and every consecutive pair an edge of `E`.
   A single-vertex path `[v]` is not required to have `v ∈ V(H)`. Paths with ≥ 1 edge have all
   their vertices in `V(H)` (`IsPathIn.mem_verts`). Length is the number of edges,
   `p.length - 1`.
4. **"Through W"** (`IsThrough`): every vertex of `interior p = p.tail.dropLast` lies in `W`. The
   ends are unrestricted.
5. **`ball H i U W`** is `W.filter (∃ u ∈ U, ∃ p, IsPathBetween H.edges u w p ∧ IsThrough W p ∧
   pathLength p ≤ i)`. It uses a classical decidability instance, so it is `noncomputable`. Use
   `mem_ball` to work with it. `ball ⊆ W`, and `U ∩ W ⊆ ball` (paths of length 0).
6. **Def 11.** Here `n = G.card`, `log² n = (Real.logb 2 n)^2`, and `ε s : ℝ`. The quantifiers
   are `U ⊆ V(G)`, `F ⊆ E(G)`, `1 ≤ |U|` and `(|U| : ℝ) ≤ 2n/3` (a real inequality), and
   `|F| ≤ s|U|`. The conclusion is `ε|U|/log² n ≤ |Nbr_{G−F}(U)|`. For `n ≤ 1` the condition is
   vacuous (`isExpander_of_card_le_one`); this matches the manuscript's remarks in s2:defWitness
   and s3:lemL15p.
7. **Def 7.** The multiset is an indexed family `P : ι → V × V` with `ι : Type` and `[Fintype ι]`.
   Each index is one occurrence.
   - Hypotheses: both entries are vertices of `G` and distinct; every vertex is an entry of at
     most `t` indices (`(count : ℝ) ≤ t`).
   - Conclusion: one `(P i).1 (P i).2`-path per index, in `G`, through `W`, of length `≤ ℓ`
     (real). Paths for distinct indices have disjoint edge lists.
   - Types: `ℓ : ℝ`, because the manuscript uses `4ℓ log n` and `2^{12} L_Y^4` with a real
     `L_Y`. `t : ℝ` (changed from `ℕ` in fix round 1), because s4 uses the real multiplicity
     `𝗍 = 2^{10}L^8` (s4.tex:104) and `𝗍 = 2^9L^8` (s4.tex:331), passed as `t` to T16*
     (s3:thmT16s), whose bounds treat `t` as a real number. Integer multiplicities
     (`t_Y = ⌈λ^{1.6}⌉`, `k` in Lemma 9) are written `(k : ℝ)`.
     `isPathConnected_natFloor_iff` (`0 ≤ t`) replaces `t` by `⌊t⌋₊` when an integer count is
     more convenient.
   - Pairs are ordered, which loses nothing: `IsPathBetween.reverse`.
   - `ι` lives in `Type` to avoid a free universe parameter in the definition.
     `IsPathConnected.exists_paths` applies the property to an index type in any universe (via
     `Fintype.equivFin`).
8. **Parameters.** `ε, s : ℝ`, because the manuscript uses real values such as `s_r/(16k)` and
   `s/(2k)`.

## Lemmas proved (EG.Lib.Found.Graph)
- **Adjacency and neighbourhoods:** symmetry, `Adj.ne`, adjacency implies both ends are
  vertices, monotonicity under `≤`. `mem_nbrs`, `nbrs ⊆ verts`, `v ∉ N(v)`, `deg_mono`,
  `deg_lt_card` (so `d(v) ≤ |H| − 1`), `deg_eq_degE`, `edgesAt_edges_eq_image`, and
  `degE_mono`/`degE_le_card`.
- **Degree bounds:** `minDeg_le_deg`, `deg_le_maxDeg`, `lt_minDeg_iff`,
  `deg_le_deg_deleteEdges_add` (`d_H(v) ≤ d_{H−F}(v) + deg_F(v)`), `deg_deleteEdges_le`, and the
  handshake lemma `sum_deg_eq_two_mul_card_edges`.
- **`Nbr`:** `mem_nbrSet`, `nbrSet ⊆ verts \ U`, `Disjoint U (nbrSet U)`, `nbrSet_mono` (under
  `≤`), `nbrSet_deleteEdges_anti`, `nbrSet_singleton = nbrs`, and
  `nbrSet_deleteEdges_edgesAt_eq_empty`.
- **Graph operations:** simp lemmas for `deleteEdges` (including `deleteEdges_deleteEdges`,
  `deleteEdges_empty` and `_le`/`_anti`), `restrictEdges` (`= deleteEdges (E \ F)`),
  `induce`/`deleteVerts` (their adjacency), `edgesBetween` (commutative), `ofEdges`
  (`ofEdges_self`, `ofEdges_edges_of_subset`) and `ofSimpleGraph` (adjacency, `nbrs`, `deg`,
  and `coe_ofSimpleGraph_edges : ↑edges = G.edgeSet`).
- **Walks and paths:** `walkEdges_cons_cons`, `length_walkEdges`, `mem_of_mem_walkEdges`,
  `exists_mem_walkEdges_of_mem`, `nodup_walkEdges` (a path has distinct edges),
  `walkEdges_concat` and `walkEdges_reverse`. `IsPathIn`/`IsPathBetween`/`IsThrough` have
  `.mono` and `.reverse`. Also `isPathIn_pair`, `isPathBetween_pair`,
  `IsPathBetween.one_le_pathLength`, `IsPathBetween.eq_pair` (length ≤ 1 and x ≠ y gives
  `[x, y]`), `IsPathBetween.exists_first_edge` and `IsPathIn.pathLength_le_card`.
- **Balls:** `mem_ball`, `ball_subset`, monotone in the radius, in `U`, in `W` and in the edges;
  `inter_subset_ball`.
- **Expanders:**
  - `IsExpander.mono` (smaller `ε`, `s`) and `IsExpander.of_le` (a supergraph on the same
    vertex set) are exactly s3:lemMonotone (i).
  - `isExpander_of_card_le_one` and `isExpander_of_nonpos`.
  - **B–M remark after Def 11:** `IsExpander.lt_deg` / `IsExpander.lt_minDeg` prove that if
    `0 < ε`, `2 ≤ |G|` and `G` is an `(ε,s)`-expander, then `s < d_G(v)` for all `v ∈ V(G)`,
    and `s < δ(G)`.
- **Path connectivity:** `IsPathConnected.exists_paths` (index type in any universe),
  `IsPathConnected.exists_paths_sigma` (joint routing of several multisets `P k : ι k → V × V`
  with summed multiplicity `≤ t`, s3:lemMonotone (iii)), `IsPathConnected.mono`, which is exactly
  s3:lemMonotone (ii), `isPathConnected_natFloor_iff` (`t ≥ 0` real ↔ `⌊t⌋₊`) and
  `isPathConnected_of_lt_one` (trivial for `t < 1`).
- **Mathlib bridge (fix round 1):** `toSimpleGraph_adj`, `edgeSet_toSimpleGraph`
  (`= ↑E(H)`), round trips `toSimpleGraph_ofSimpleGraph` and `ofSimpleGraph_toSimpleGraph`
  (when `V(H) = univ`), `toSimpleGraph_mono`, `toSimpleGraph_neighborFinset`,
  `toSimpleGraph_degree` (`= d_H(v)`); for paths, `walkEdges_support` (`= w.edges`),
  `pathLength_support` (`= w.length`), `isPathBetween_support` (a Mathlib path gives a list
  path) and `IsPathBetween.exists_walk` (a list path is the support of a Mathlib path of the
  same length).
- **Balls/paths in `V(H)` (fix round 1):** `ball_subset_verts` (`W ⊆ V(H)` ⇒ ball ⊆ V(H)),
  `IsPathBetween.left_mem_verts` / `right_mem_verts` (for `x ≠ y`).

## Tests (EGTest.Found)
- **The path P3 (vertices 0, 1, 2):**
  - card, degrees, `degE`, δ/Δ, `Nbr` of several sets, `H − F`, `H[U]`, `H − U`, `E_H(A,B)`,
    `ofEdges` discarding loops and outside edges.
  - Paths: a positive `IsPathBetween` example, "through" examples (ends unrestricted), and
    rejected repeated vertices and non-edges. Every 02-path has interior vertex 1.
  - Balls: `1 ∈ B^1(0,{1,2})`, `2 ∈ B^2`, `2 ∉ B^1`, and `2 ∉ B^5(0,{2})` ("through" matters).
    The start need not lie in W, but the end must.
- **K4 (from Mathlib's ⊤):** card, 6 edges, deg 3, δ = 3, `Nbr` examples. K4 is a
  (1,0)-expander (non-vacuity of Def 11), and the remark gives δ > 0.
- **Paths that are not expanders:**
  - The path on 60 vertices is not a (1,0)-expander (U = {0..39}, Nbr = {40}, and
    40/log²60 > 1). This is a direct check from Def 11, not using the remark.
  - The path on 5 vertices is not a (1/2,1)-expander (via the remark).
  - With `ε = 0` every graph is an expander, and one-vertex graphs are expanders.
- **`K2` and the log base (fix round 1):** `K2` is a `(1, 1/2)`-expander (fails with `ln`,
  since `1/ln²2 ≈ 2.08 > 1`; non-vacuity with `s > 0`), not a `(2, 0)`-expander, not a
  `(1, 1)`-expander (via the remark), and `1/2 < δ(K2)`.
- **Mathlib bridge (fix round 1):** `K4.toSimpleGraph = ⊤`, `ofSimpleGraph K4.toSimpleGraph =
  K4`, the list path `0 1 2` of P3 gives a Mathlib path of length 2, and every Mathlib 0–2 path
  of `P3.toSimpleGraph` contains 1.
- **Def 7:**
  - A complete graph is (1,1)-path connected through any W (non-vacuity, for all index types).
  - P3 is not (1,1)-path connected.
  - **Multiset clause:** the single edge K2 is (1,1)-path connected but not (ℓ,2)-path
    connected for any ℓ, W. The pair {0,1} taken twice needs two edge-disjoint paths.
  - **Real `t` (fix round 1):** K2 is `(1, 3/2)`-path connected (via `⌊3/2⌋₊ = 1`) but not
    `(ℓ, t)`-path connected for any real `t ≥ 2`; P3 is `(0, 1/2)`-path connected (trivial
    case `t < 1`).

## Deviations from the plan, and remaining points
- PLAN §3 names the module `EdgeSet`. The task asked for `EG/Defs/Graph.lean`, so that name is
  used.
- Walks, trails and cycles as separate notions, and the s4 observations (S), (E), (C), are not
  included; only paths are, as the task asked. Cycles remain `Obj.cycle` with `cycleEdges`.
- **B–M remark:** `IsExpander.lt_deg` needs `0 < ε`. B–M and s1:citDef11 leave this implicit
  (for `ε ≤ 0` every graph is an expander, see `isExpander_of_nonpos`). The manuscript only uses
  `ε ∈ (0,1]` (s3 conventions: "ε' always denotes a generic expansion parameter in (0,1]";
  `ε_Y ∈ {2^-5, 2^-6}`), so nothing downstream is affected. The citDef11 text could say "for
  `ε > 0`".
- (Superseded in fix round 1.) The earlier claim "nothing in s3–s6 needs a real `t`" was wrong
  (s4 uses `𝗍 = 2^{10}L^8`); `t` is now real, see decision 7.
- s3:lemMonotone (iii) (joint routing) is `IsPathConnected.exists_paths_sigma`. The rest of
  (iii) ("depends only on the pair (X, V)", adaptivity) is automatic: `IsPathConnected G ℓ t W`
  is a proposition about `(G, W)` quantifying over all families.

## Fix round 1

Review: `work/p1b/graph.review1.md` (verdict APPROVE; one minor, four cosmetic items). Each item
was re-checked against the manuscript and the code before acting.

| # | Item | Outcome |
|---|---|---|
| M1 | `t : ℕ` in Def 7 | **Fixed.** The reviewer is right: s4.tex:104 (`𝗍 := 2^{10}L^8`) and s4.tex:331 (`𝗍 := 2^9L^8`) are real, with `L = log₂ N`, and s4.tex:168–183 passes `t := 𝗍` to T16* (s3:thmT16s, "`t ≥ 1`"; bounds `2^{135}tL^{28}ρ^{-5}`, `2^{86}tL^{19}ρ^{-3}N^{-3}`). `EG.FGraph.IsPathConnected G ℓ t W` now takes `ℓ t : ℝ` and the multiplicity hypothesis is `((univ.filter …).card : ℝ) ≤ t`, the literal manuscript wording. Docstrings updated. Lib: `exists_paths`, `mono` restated for real `t` (`t' ≤ t` in ℝ); new `isPathConnected_natFloor_iff` (for `0 ≤ t`, `(ℓ,t)` ↔ `(ℓ,⌊t⌋₊)`) and `isPathConnected_of_lt_one`. Tests adjusted (`norm_cast` on counts) and new real-`t` tests added. The design-note sentence was corrected (decision 7 and "Deviations"). No other file used `IsPathConnected`. |
| C1 | B–M remark needs `ε > 0` | **Valid, manuscript side; no Lean change.** `isExpander_of_nonpos` shows every graph is an `(ε,s)`-expander for `ε ≤ 0`, so the s1:citDef11 sentence "δ(G) > s for every (ε,s)-expander on at least two vertices" is literally false without `ε > 0`. `IsExpander.lt_deg` / `lt_minDeg` already assume `0 < ε`, and every use has `ε' ∈ (0,1]`. The manuscript is outside this task's scope (v6 revision runs in parallel), so this is forwarded to the orchestrator: s1:citDef11 should say "for `ε > 0`". |
| C2 | zero-length paths not tied to `V(H)` | **Fixed.** Added the warning to the `IsPathIn` docstring (the one-vertex list `[v]` is a path in every `E`, also for `v ∉ V(H)`), a note to the `ball` docstring, and lemmas `ball_subset_verts` (`W ⊆ V(H)` ⇒ `B^i_H(U,W) ⊆ V(H)`), `IsPathBetween.left_mem_verts` / `right_mem_verts` (ends of an `xy`-path with `x ≠ y` lie in `V(H)`). The definitions are unchanged (the manuscript only uses `U, V ⊆ V(H)`). |
| C3 | tests do not pin `log₂` | **Fixed.** Added `EGTest.K2_isExpander : K2.IsExpander 1 (1/2)`. It holds with `log₂` (`1·1/1² = 1 ≤ 1`) and would fail with `ln` (`1/ln²2 ≈ 2.08 > 1`). It is also a non-vacuity witness with `s > 0`. Also added: `K2` is not a `(2,0)`-expander, not a `(1,1)`-expander, and `1/2 < δ(K2)`. |
| C4 | no `FGraph → SimpleGraph`, no walk bridge, no joint routing | **Fixed (optional items done).** `EG.FGraph.toSimpleGraph` (in `EG.Defs.Graph`: the `SimpleGraph V` with `Adj := H.Adj`; vertices outside `V(H)` isolated) with a `DecidableRel` instance. Lemmas in `EG.Lib.Found.Graph`: `edgeSet_toSimpleGraph`, round trips `toSimpleGraph_ofSimpleGraph` and `ofSimpleGraph_toSimpleGraph` (for `V(H) = univ`), `toSimpleGraph_mono`, `toSimpleGraph_neighborFinset`, `toSimpleGraph_degree`, and the path bridge `walkEdges_support`, `pathLength_support`, `isPathBetween_support`, `IsPathBetween.exists_walk`. Joint routing: `IsPathConnected.exists_paths_sigma` (families `P k : ι k → V × V`, `k : κ` finite, summed multiplicity `≤ t`; paths pairwise edge-disjoint across all `(k, i)`). The `DecidableEq` remark needs no change, as the reviewer says. |

Checks after the fixes: `scripts/check.sh` on `EG/Defs/Graph.lean`, `EG/Lib/Found/Graph.lean`
and `EGTest/Found.lean` gives rc=0, 0 errors, 0 warnings. `lake build EG.Lib.Found.Graph`
succeeds. The downstream importers `EG/Lib/Found/FGraphFnum.lean` and `EG/Spec/Chain/Gate.lean`
still check (rc=0). `python3 scripts/lint.py`: 0 findings. Axiom scan: 270 constants, 0 sorryAx,
0 violations.
