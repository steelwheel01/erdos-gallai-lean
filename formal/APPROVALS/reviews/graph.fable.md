# Clean-room review — group `graph` — reviewer `fable`

Date: 2026-09-26. Model: Claude (Fable 5.1). Independent review from scratch. The earlier review
files `work/p1b/graph.review1.md` / `graph.review2.md` and their verdicts were **not** consulted;
the design note `work/p1b/graph.md` was read for context (module map, parameter-type decisions)
after the back-translation below had been written, and no verdict here rests on it.

**Scope.** `EG/Defs/Graph.lean` (`EG.FGraph` and all its operations, `EG.edgesAt`, `EG.degE`),
`EG/Defs/Walk.lean` (`EG.walkEdges`, `EG.pathLength`, `EG.IsPathIn`, `EG.IsPathBetween`,
`EG.interior`, `EG.IsThrough`, `EG.ball`), `EG/Defs/Expander.lean` (`EG.FGraph.IsExpander` =
B–M Definition 11 [s1:citDef11], `EG.FGraph.IsPathConnected` = B–M Definition 7 [s1:citDef7] with
the multiset clause). Manuscript: `proofs/manuscript/s1.tex` l. 321–348 (s1:convGraphs (a)–(e)),
l. 402–418 (s1:citNotation), l. 441–457 (s1:citDef7), l. 497–510 (s1:citDef11);
`proofs/manuscript/s3.tex` l. 173–197 (s3:remMultiset), l. 440–460 (the recursive ball
construction); `papers/2211.07689.txt` l. 123–140 (B–M §2.1 notation), l. 341–355 (Def 7 and the
multiset sentence), l. 379–385 (B–M's ball), l. 579–594 (Def 11 and the remark after it).

**Method.** Every constant was `#print`ed (scratch file, appendix A) to make sure the reviewed
text is what Lean elaborated. Each definition was back-translated into plain mathematics and
compared clause by clause with the quoted manuscript text; edge cases (empty graph, `n ≤ 1`,
`ε ≤ 0`, `s < 0`, `t < 1`, `ℓ < 1`, `U ⊄ V(H)`, `W ⊄ V(G)`, loops, stray edges, one-vertex paths,
non-disjoint `A, B`) were worked out by hand and probed with `decide`/witness tests on small
graphs. The scratch file compiles with exactly one error, which is intentional (a deliberately
wrong parse of the Def 11 inequality is shown *not* to be definitionally the statement). The
existing test module `EGTest.Found` was also rebuilt (`lake build EGTest.Found`, up to date, no
errors). No repository file was edited; the only file written is this review.

**Verdict: APPROVE (all 26 constants), with non-blocking notes in §5 and one manuscript-side
remark in §5.10.**

---

## 0. Conventions used below

Manuscript s1:convGraphs, quoted:

> (a) Graphs are finite and simple, unless they are explicitly called multigraphs (auxiliary
> multigraphs occur only in Sections 5 and 7). … For any graph `H` we write `|H| := |V(H)|`.
> (b) `log = log₂` throughout.
> (c) For a vertex `v` of a graph `H`, `N_H(v)` is its set of neighbours and `d_H(v) = deg_H(v)`
> its degree; `δ(H)` and `Δ(H)` are the minimum and maximum degree. For `U ⊆ V(H)`, `Nbr_H(U)` is
> the set of vertices of `V(H) \ U` that have a neighbour in `U`. `H[U]` is the induced subgraph;
> `H − U` and `H \ U` both denote `H[V(H) \ U]`; for `F ⊆ E(H)`, `H − F` is obtained by deleting
> the edges of `F` (keeping all vertices). For disjoint `A, B ⊆ V(H)`, `E_H(A,B)` is the set of
> edges with one end in `A` and the other in `B`, and `e_H(A,B) := |E_H(A,B)|`; for an edge set
> `F` and a vertex `v`, `deg_F(v)` is the number of edges of `F` at `v`.
> (d) A *path through* `V` is a path all of whose interior vertices lie in `V`; its ends are
> unrestricted. For `U, V ⊆ V(H)` and an integer `i ≥ 0`, `B^i_H(U,V)` is the set of vertices
> of `V` that can be reached by a path through `V` of length at most `i` starting at a vertex of
> `U` (the starting vertex need not lie in `V`); thus `B^i_H(U,V) ⊆ V`.
> (e) Families of pairs of vertices are *multisets*: a pair may occur several times, and "every
> vertex lies in at most `t` pairs" counts occurrences.

A *path* is, as in B–M (l. 123–140, "by a `vu`-path/walk we refer to a path/walk joining `v` and
`u`") and in all of graph theory, a sequence of pairwise distinct vertices with consecutive
vertices adjacent; its *length* is its number of edges (B–M Prop. 8/Lemma 9 "length at most
`4ℓ log n`"; manuscript s3 l. 456 "Appending the edge `wv` gives a path of length at most
`i+1`"). A one-vertex path has length 0.

Lean facts relied on (checked, appendix B): `Finset.mem_sym2_iff : m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s`;
`List.Disjoint l₁ l₂ = ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False`; `Real.logb b 0 = 0`,
`Real.logb b 1 = 0`, `x / 0 = 0`; `Sym2` is unordered (`s(a,b) = s(b,a)`); `Sym2.IsDiag s(a,b) ↔
a = b`; `n - 1 = 0` in `ℕ` for `n ≤ 1`.

---

## 1. `EG/Defs/Graph.lean`

### 1.1 `structure FGraph (V : Type*)`: `verts : Finset V`, `edges : Finset (Sym2 V)`, `edge_verts : ∀ e ∈ edges, ∀ v ∈ e, v ∈ verts`, `loopless : ∀ e ∈ edges, ¬ e.IsDiag`

*Back-translation.* A finite set of vertices `V(H)` and a finite set of unordered pairs `E(H)`
such that both ends of every edge are vertices and no edge is a loop. Since `edges` is a
`Finset`, there are no parallel edges; since `Sym2` is unordered, edges are undirected.

*Manuscript.* (a) "Graphs are finite and simple". An `FGraph V` is exactly a finite simple graph
whose vertex set is a finite subset of the ambient type `V`; conversely every finite simple graph
on a finite subset of `V` is an `FGraph V` (take its vertex and edge sets). The ambient type
plays no role in any definition below except as the carrier of `Finset`s, and Convention (a)'s
"`G` always denotes the input graph and `n := |V(G)|`" is `G.card` (1.3). `FGraph.{u} (V : Type u)
: Type u`; no universe issue. The `@[ext]` lemma is equality of `verts` and `edges`, which is
graph equality.

*Edge cases.* The graph with no vertices (`verts = ∅`, hence `edges = ∅`) is allowed, as in the
manuscript (e.g. `H_ν` may become empty). The multigraphs of s5/s7 are *not* representable (a
`Finset` has no multiplicities); those statements will need a separate structure. This is
documented in the module docstring and is not a mismatch for the simple graphs of s1:convGraphs.

*Verdict:* approve.

### 1.2 `edgesAt F v := F.filter (v ∈ ·)`, `degE F v := (edgesAt F v).card`

*Back-translation.* The edges of `F` containing `v`, and their number.
*Manuscript.* (c) "for an edge set `F` and a vertex `v`, `deg_F(v)` is the number of edges of
`F` at `v`". Matches. For `F ⊆ E(H)` of a simple graph this is the usual `deg_F(v)`.
*Edge cases.* A loop `s(v,v) ∈ F` is counted once (scratch §3: `degE {s(0,1), s(1,1)} 1 = 2`);
the manuscript's `F` are edge sets of simple graphs, so loops do not occur. `F` need not be a
subset of any graph's edge set; total, as the manuscript's phrasing "for an edge set `F`".
*Verdict:* approve.

### 1.3 `FGraph.card H := H.verts.card`

(a) "`|H| := |V(H)|`". Exact. *Verdict:* approve.

### 1.4 `FGraph.Adj H u v := s(u,v) ∈ H.edges`

`u` and `v` are adjacent iff `uv` is an edge. Symmetric (unordered pair), irreflexive by
`loopless`, and `Adj u v` forces `u, v ∈ V(H)` by `edge_verts` (all three proved in
`EG.Lib.Found.Graph`). For `u` or `v` outside `V(H)` it is false, as it should be. *Verdict:*
approve.

### 1.5 `instance : PartialOrder (FGraph V)`: `H ≤ H' ↔ H.verts ⊆ H'.verts ∧ H.edges ⊆ H'.edges`

The subgraph relation. Antisymmetry is graph equality via `ext`. Used for "`H' ⊇ H`" in
s3:lemMonotone. *Verdict:* approve.

### 1.6 `nbrs H v := H.verts.filter (H.Adj v ·)`, `deg H v := (H.nbrs v).card`

*Back-translation.* `N_H(v) = {w ∈ V(H) : vw ∈ E(H)}`, `d_H(v) = |N_H(v)|`.
*Manuscript.* (c) "`N_H(v)` is its set of neighbours and `d_H(v) = deg_H(v)` its degree". In a
simple graph the number of neighbours equals the number of edges at `v`
(`EG.FGraph.deg_eq_degE`, proved in the library), so `deg` is also `deg_{E(H)}(v)`. The filter
over `H.verts` is redundant (a neighbour is a vertex by `edge_verts`) and harmless.
*Edge cases.* `v ∉ V(H)`: `N_H(v) = ∅`, `d_H(v) = 0` (scratch §3, `P3i.deg 9 = 0`). `v ∉ N_H(v)`
(loopless). *Verdict:* approve.

### 1.7 `minDeg H := if h : H.verts.Nonempty then H.verts.inf' h H.deg else 0`, `maxDeg H := H.verts.sup H.deg`

*Back-translation.* `δ(H) = min_{v ∈ V(H)} d_H(v)`, `Δ(H) = max_{v ∈ V(H)} d_H(v)`, both `0` for
the graph without vertices (for `sup` on `ℕ` the empty supremum is `⊥ = 0`).
*Manuscript.* (c) "`δ(H)` and `Δ(H)` are the minimum and maximum degree". Exact for
`V(H) ≠ ∅`; the manuscript never takes `δ` of an empty graph. Mathlib's `SimpleGraph.minDegree`
makes the same choice. Scratch §3: `P3i.minDeg = 0 ∧ P3i.maxDeg = 2` (isolated vertex 3),
`(P3i.deleteVerts {3}).minDeg = 1`. *Verdict:* approve (note 5.5).

### 1.8 `nbrSet H U := (H.verts \ U).filter (fun v => ∃ u ∈ U, H.Adj u v)`

*Back-translation.* `Nbr_H(U) = {v ∈ V(H) \ U : ∃ u ∈ U, uv ∈ E(H)}`.
*Manuscript.* (c) "For `U ⊆ V(H)`, `Nbr_H(U)` is the set of vertices of `V(H) \ U` that have a
neighbour in `U`" (also B–M l. 126–127 "`N_G(U)` the set of vertices in `V(G) \ U` which have a
neighbour in `U`"). Exact. Defined for all `U`; a `u ∈ U \ V(H)` has no neighbours, so
`Nbr_H(U) = Nbr_H(U ∩ V(H))` (scratch §3, `P3i.nbrSet {0, 42} = {1}`); in Def 11 `U ⊆ V(G)` is
required anyway. `Nbr_H(U) ∩ U = ∅`, `Nbr_H(V(H)) = ∅` (scratch). This is the set whose size Def 11
bounds; see 3.1. *Verdict:* approve.

### 1.9 `induce H U`: `verts := H.verts ∩ U`, `edges := H.edges.filter (· ∈ U.sym2)`

*Back-translation.* By `Finset.mem_sym2_iff`, `e ∈ U.sym2 ↔ ∀ a ∈ e, a ∈ U`, so the edges are the
edges of `H` with both ends in `U`; vertex set `V(H) ∩ U`.
*Manuscript.* (c) "`H[U]` is the induced subgraph", always with `U ⊆ V(H)`, where the vertex set
is `U` (`induce_verts_of_subset`) and the edges are those of `H` inside `U`. Exact on the
manuscript's domain; for `U ⊄ V(H)` the outside elements are discarded (scratch §3:
`(P3i.induce {1,2,3,7}).verts = {1,2,3}`, `.edges = {s(1,2)}`). *Verdict:* approve.

### 1.10 `deleteVerts H U := H.induce (H.verts \ U)`

(c) "`H − U` and `H \ U` both denote `H[V(H) \ U]`". Literal. Vertex set `V(H) \ U`
(`deleteVerts_verts`), edges those with both ends outside `U` (scratch §3: deleting the middle
vertex of `P3` deletes both edges). *Verdict:* approve.

### 1.11 `deleteEdges H F`: `verts := H.verts`, `edges := H.edges \ F`

(c) "for `F ⊆ E(H)`, `H − F` is obtained by deleting the edges of `F` (keeping all vertices)".
Literal; vertices kept (scratch §3), so `|H − F| = |H|`, which matters for `n` in Def 11
(`Nbr_{G−F}` is taken in a graph on the same `n` vertices). Total in `F`; only `F ∩ E(H)`
matters, as the docstring says. *Verdict:* approve.

### 1.12 `restrictEdges H F`: `verts := H.verts`, `edges := H.edges.filter (· ∈ F)`

Not a manuscript primitive; the spanning subgraph with edge set `E(H) ∩ F` ("the graph with
vertex set `V(X)` whose edges are the edges of colour `i`"). Equal to `H − (E(H) \ F)`
(`restrictEdges_eq_deleteEdges`). Keeps all vertices, which is what the colour-class graphs of
s3 need (`|X_i| = |X|`). *Verdict:* approve.

### 1.13 `edgesBetween H A B := H.edges.filter (fun e => ∃ a ∈ A, ∃ b ∈ B, s(a,b) = e)`, `eBetween := card`

*Back-translation.* Edges `ab ∈ E(H)` with `a ∈ A`, `b ∈ B`.
*Manuscript.* (c) "For disjoint `A, B ⊆ V(H)`, `E_H(A,B)` is the set of edges with one end in `A`
and the other in `B`, and `e_H(A,B) := |E_H(A,B)|`". For disjoint `A, B` an edge has one end in
`A` and the other in `B` iff it is `s(a,b)` with `a ∈ A`, `b ∈ B`: exact. For overlapping sets
the manuscript gives no meaning; the Lean term also counts edges inside `A ∩ B`, once each
(scratch §3: `P3i.eBetween {0,1} {0,1} = 1`). I checked every `E_·(·,·)`/`e_·(·,·)` occurrence in
s2–s7: they are `E_{H_ν}(U'_ν, V(H_ν) \ (U'_ν ∪ N''_ν))` (s2 l. 138, 305) and `e_{X⁰_Y}(x, Y)`
with `x ∈ S_Y`, `Y := Y⁰ \ S_Y` (s2 l. 1257, s6 l. 339–363) — all disjoint (for a singleton `{x}`
the two readings agree anyway, since there are no loops). *Verdict:* approve (note 5.1).

### 1.14 `ofEdges W F`: `verts := W`, `edges := F.filter (fun e => ¬ e.IsDiag ∧ e ∈ W.sym2)`

The graph on `W` whose edges are the non-loop members of `F` with both ends in `W`; a total
constructor, equal to `⟨W, F, …⟩` when `F` is loopless with ends in `W`
(`ofEdges_edges_of_subset`, `ofEdges_self`). Scratch §3: the loop `s(2,2)` and the stray edge
`s(3,9)` are dropped. Not a manuscript notion; correct as specified. *Verdict:* approve.

### 1.15 `ofSimpleGraph [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]`: `verts := univ`, `edges := G.edgeFinset`

A Mathlib simple graph on a finite type as an `FGraph` on all of `V`; `card = Fintype.card V`,
`edges = G.edgeFinset` (`↑edges = G.edgeSet`). This is the bridge from the `SimpleGraph`
statement of the main theorem to the manuscript's graphs; it is faithful (same vertices, same
edges, `ofSimpleGraph_adj`). The `Fintype G.edgeSet` argument is an instance, not a hypothesis.
*Verdict:* approve.

### 1.16 `toSimpleGraph H : SimpleGraph V` with `Adj := H.Adj`

The Mathlib graph on the whole type with `H`'s adjacency; vertices outside `V(H)` are isolated;
`edgeSet = ↑E(H)`; round trips proved in the library. A tool for importing Mathlib walk results,
not a manuscript notion. *Verdict:* approve.

---

## 2. `EG/Defs/Walk.lean`

### 2.1 `walkEdges p := List.zipWith (fun a b => s(a,b)) p p.tail`

For `p = [v₀, …, v_k]`: `[s(v₀,v₁), …, s(v_{k−1},v_k)]`, length `k` (`length_walkEdges`); `[]`
for `[]` and `[v]` (scratch §2). Exactly the edge sequence of the walk `v₀ … v_k`. *Verdict:*
approve.

### 2.2 `pathLength p := p.length − 1`

Number of edges `k` of `v₀ … v_k`; `0` for `[v]`. For `[]` the `ℕ` subtraction gives `0`; `[]` is
excluded from being a path (2.3), so this value is never meaningful. Matches the convention
"length = number of edges" (§0). *Verdict:* approve.

### 2.3 `IsPathIn E p := p ≠ [] ∧ p.Nodup ∧ ∀ e ∈ walkEdges p, e ∈ E`

*Back-translation.* `p` is a non-empty list of pairwise distinct vertices all of whose
consecutive pairs are edges of `E`: a path (in the graph-theoretic sense) using only edges of
`E`. A path in `H` is `IsPathIn H.edges p`; a path in `H − F` is `IsPathIn (H.edges \ F) p`.
*Manuscript.* Standard notion (§0). `Nodup` gives distinct vertices (so no repeated edge either,
`nodup_walkEdges`) and excludes `[v, v]`, so loops in `E` could never be used. Scratch §2:
`[0,1,2]` and its reverse are paths in `{01, 12}`; `[0,1,0]` (repeated vertex), `[0,2]`
(non-edge) and `[]` are not.
*Edge case (documented in the docstring).* `[v]` is a path in every `E`, also for `v ∉ V(H)`
(scratch: `IsPathIn E3 [7]`). This is the usual mathematical convention (a vertex is a path of
length 0) plus the fact that `E` carries no vertex set. It is harmless in the two consumers of
this file: `ball` filters on `w ∈ W` (2.7), and Def 7 has `x ≠ y`, which forces at least one
edge and so all vertices in `V(G)` (`IsPathIn.mem_verts`, `IsPathBetween.left_mem_verts`). Future
statements about a *possibly trivial* path in `H` must add `v ∈ V(H)`; see note 5.2.
*Verdict:* approve.

### 2.4 `IsPathBetween E x y p := IsPathIn E p ∧ p.head? = some x ∧ p.getLast? = some y`

An `xy`-path in `E`: a path whose first vertex is `x` and last vertex is `y`. For `x ≠ y` it has
`≥ 1` edge (`one_le_pathLength`); reversing gives a `yx`-path. Scratch §2: `[2,1,0]` is a
`2 0`-path, not a `0 2`-path. *Verdict:* approve.

### 2.5 `interior p := p.tail.dropLast`

For `[v₀, …, v_k]`: `[v₁, …, v_{k−1}]`; `[]` when `k ≤ 1` (scratch §2). The interior (internal)
vertices of the path. *Verdict:* approve.

### 2.6 `IsThrough W p := ∀ v ∈ interior p, v ∈ W`

(d) "A *path through* `V` is a path all of whose interior vertices lie in `V`; its ends are
unrestricted" (also B–M l. 379 "a path through a subset of vertices `V` is a path whose
internal vertices are all in `V`"). Literal; the ends are not constrained (scratch §2:
`IsThrough (∅) [0,1]`, `¬ IsThrough {0,2} [0,1,2]`). It carries only the "through" part; the
"path" part is `IsPathIn`, and the two are always combined (2.7, 3.2). *Verdict:* approve.

### 2.7 `ball H i U W := W.filter (fun w => ∃ u ∈ U, ∃ p, IsPathBetween H.edges u w p ∧ IsThrough W p ∧ pathLength p ≤ i)`

*Back-translation.* `B^i_H(U, W) = {w ∈ W : ∃ u ∈ U, ∃ uw-path p in H with interior in W and
≤ i edges}`.
*Manuscript.* (d) "For `U, V ⊆ V(H)` and an integer `i ≥ 0`, `B^i_H(U,V)` is the set of vertices
of `V` that can be reached by a path through `V` of length at most `i` starting at a vertex of
`U` (the starting vertex need not lie in `V`); thus `B^i_H(U,V) ⊆ V`" (B–M l. 380–385 verbatim
in substance; s3 l. 38–39 the same for `G − F`). Clause by clause: "vertices of `V`" = the
`W.filter`; "reached by a path through `V`" = `IsPathBetween H.edges u w p ∧ IsThrough W p`;
"of length at most `i`" = `pathLength p ≤ i`; "starting at a vertex of `U`" = `∃ u ∈ U`; "the
starting vertex need not lie in `V`" = no condition on `u` (scratch §4: `1 ∈ B¹({0}, {1,2})` with
`0 ∉ {1,2}`); "`⊆ V`" = `ball_subset`.
*Path vs walk.* "Reached by a path" could be read as "by a walk"; the two agree: a `uw`-walk with
internal vertices in `W` contains a `uw`-path whose vertices are among the walk's, and any of its
interior vertices is distinct from `u` and `w`, hence an internal vertex of the walk, hence in
`W`. So no discrepancy.
*Radius 0 and `U ∩ W`.* `[u]` is a `uu`-path of length 0, so `U ∩ W ⊆ B^i_H(U,W)` for every `i`
(`inter_subset_ball`; scratch §4). This agrees with B–M's "distance at most `i`" (distance 0
included) and with the manuscript's own recursive construction s3 l. 440–446 ("`𝓑₀ = U`,
`𝓑₁ = U ∪ Nbr_{G−F}(U)`").
*"Through" bites.* Scratch §4: `2 ∉ B⁵_{P3}({0}, {2})` because the only `0 2`-path has interior
vertex `1 ∉ {2}`, while `2 ∈ B²_{P3}({0}, {1,2})`.
*Domain.* Defined for all `U, W`; the manuscript has `U, V ⊆ V(H)`. Elements of `U \ V(H)`
contribute only trivial paths and are removed by the `W`-filter when `W ⊆ V(H)`
(`ball_subset_verts`). The radius is `ℕ`, as in (d) "an integer `i ≥ 0`"; see note 5.4 for the
cited results that write a real radius.
*Decidability.* The definition is `noncomputable` (classical `DecidablePred`); it is used only
through `mem_ball`. This has no mathematical content.
*Verdict:* approve.

---

## 3. `EG/Defs/Expander.lean`

### 3.1 `FGraph.IsExpander (G : FGraph V) (ε s : ℝ) : Prop` — B–M Definition 11

```
∀ U : Finset V, ∀ F : Finset (Sym2 V), U ⊆ G.verts → F ⊆ G.edges →
  1 ≤ U.card → (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 → (F.card : ℝ) ≤ s * U.card →
  ε * U.card / Real.logb 2 G.card ^ 2 ≤ ((G.deleteEdges F).nbrSet U).card
```

*Parse (verified, appendix A §1).* The conclusion is `(ε · |U|) / (log₂ n)² ≤ |Nbr_{G−F}(U)|`
with `n = |V(G)|` cast to `ℝ`; the alternative reading `log₂(n²)` is *not* definitionally the
statement (the deliberate `Iff.rfl` test fails), and function application binds tighter than
`^`, so `Real.logb 2 ↑G.card ^ 2 = (Real.logb 2 ↑G.card) ^ 2`.

*Back-translation.* `G` is an `(ε,s)`-expander iff for every vertex set `U ⊆ V(G)` and edge set
`F ⊆ E(G)` with `1 ≤ |U|`, `|U| ≤ 2n/3` and `|F| ≤ s|U|` (real inequalities), the number of
vertices of `V(G) \ U` having a `(G − F)`-neighbour in `U` is at least `ε|U| / (log₂ n)²`.

*Manuscript* (s1:citDef11): "An `n`-vertex graph `G` is an `(ε,s)`-expander if for every
`U ⊆ V(G)` and every `F ⊆ E(G)` with `1 ≤ |U| ≤ 2n/3` and `|F| ≤ s|U|` we have
`|Nbr_{G−F}(U)| ≥ ε|U| / log² n`." B–M l. 579–582 identical. With (b) `log = log₂` and (c)'s
`Nbr` (1.8) and `G − F` (1.11), every clause matches:
- "`n`-vertex" — `n = G.card = |V(G)|` (isolated vertices count, as in the manuscript);
- "`U ⊆ V(G)`, `F ⊆ E(G)`" — the two subset hypotheses;
- "`1 ≤ |U| ≤ 2n/3`" — `1 ≤ U.card` in `ℕ` and `(|U| : ℝ) ≤ 2n/3` in `ℝ` (for an integer `|U|`,
  `|U| ≤ 2n/3` in `ℝ` iff `|U| ≤ ⌊2n/3⌋`, so no rounding question arises; `n = 3` allows
  `|U| = 2`, as it should);
- "`|F| ≤ s|U|`" — real inequality with real `s`, as the manuscript's `s` values
  (`s_r/(16k)`, `log^{135} n`) are real;
- "`log² n`" — `(log₂ n)²`; the manuscript reserves bracketed superscripts `log^{[k]}` for
  iteration (b), so `log²` is the square, as in B–M's "`ε|U| / log² n`" and "`|U|/3 log² n`".

*Edge cases.*
- `n = 0` or `n = 1`: no `U` with `1 ≤ |U| ≤ 2n/3 ≤ 2/3`, so the property holds vacuously in the
  manuscript; in Lean the same hypotheses are unsatisfiable (`isExpander_of_card_le_one`), and
  independently `Real.logb 2 1 = 0` with `x/0 = 0` would make the conclusion `0 ≤ card` true. The
  manuscript states exactly this: s2:defWitness "Then `m ≥ 2`, since a graph on one vertex has no
  set `U` with `1 ≤ |U| ≤ 2m/3`", s3 l. 113–114 "every graph on one vertex is an expander for all
  parameters". Consistent.
- `n = 2`: `log₂ 2 = 1`, `|U| = 1`; K₂ is a `(1, 1/2)`-expander (`EGTest.K2_isExpander`), which
  pins the base: with `ln` the bound would be `1/ln²2 ≈ 2.08 > 1`. Non-vacuity with `s > 0`.
- `ε ≤ 0`: every graph is an `(ε,s)`-expander (`isExpander_of_nonpos`), in the manuscript too
  (the right-hand side is `≤ 0`). The manuscript only uses `ε ∈ (0,1]`. See 5.10 for the one
  place where the manuscript text silently needs `ε > 0`.
- `s < 0`: `|F| ≤ s|U| < 0` is impossible, so the property is vacuous in both readings.
- Non-vacuity in the interesting direction: `EGTest` proves `¬ (pathGraph 60).IsExpander 1 0`
  directly from the definition (`U = {0..39}`, `|Nbr| = 1 < 40/log²60`), and `¬ K2.IsExpander 2 0`.
- Monotonicity in `(ε, s)` and under adding edges on the same vertex set (`IsExpander.mono`,
  `IsExpander.of_le`, = s3:lemMonotone (i)) and the B–M remark `δ(G) > s` for `ε > 0`, `n ≥ 2`
  (`IsExpander.lt_minDeg`) are proved in the library from this definition, which is further
  evidence that it has the intended strength.

*Typeclasses / universes.* `[DecidableEq V]` is an instance argument used only to form
`Finset.filter`s; the proposition is classically the same for any instance. No universe issue.

*Verdict:* approve.

### 3.2 `FGraph.IsPathConnected (G : FGraph V) (ℓ t : ℝ) (W : Finset V) : Prop` — B–M Definition 7 with the multiset clause

```
∀ (ι : Type) [Fintype ι] (P : ι → V × V),
  (∀ i, (P i).1 ∈ G.verts ∧ (P i).2 ∈ G.verts ∧ (P i).1 ≠ (P i).2) →
  (∀ v : V, ((Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤ t) →
  ∃ Q : ι → List V,
    (∀ i, IsPathBetween G.edges (P i).1 (P i).2 (Q i) ∧ IsThrough W (Q i) ∧
      (pathLength (Q i) : ℝ) ≤ ℓ) ∧
    ∀ i j, i ≠ j → (walkEdges (Q i)).Disjoint (walkEdges (Q j))
```

*Back-translation.* For every finite family `(x_i, y_i)_{i ∈ ι}` of ordered pairs of distinct
vertices of `G`, indexed by a finite type, in which every vertex `v` occurs in at most `t` of
the pairs (the number of indices `i` with `v ∈ {x_i, y_i}`, compared with the real `t`), there
exist paths `Q_i` in `G` such that `Q_i` goes from `x_i` to `y_i`, all interior vertices of `Q_i`
lie in `W`, `Q_i` has at most `ℓ` edges, and for `i ≠ j` the paths `Q_i`, `Q_j` have no common
edge (`List.Disjoint` on the edge lists; `Sym2` is unordered, so an edge traversed in opposite
directions is the same element).

*Manuscript* (s1:citDef7): "A graph `G` is `(ℓ,t)`-path connected through a vertex set
`V ⊆ V(G)` if, for every collection `𝒫 ⊆ (V(G) choose 2)` in which every vertex lies in at most
`t` pairs, there are edge-disjoint paths `P_{x,y}`, `{x,y} ∈ 𝒫`, such that each `P_{x,y}` is an
`xy`-path through `V` of length at most `ℓ`. *Multiset clause*: here `(V(G) choose 2)` denotes
the *multiset* of pairs of distinct vertices of `G`; in particular the same pair may occur
several times in `𝒫`. Thus a pair occurring `k` times receives `k` pairwise edge-disjoint
paths, and the bound `t` counts occurrences. The ends `x, y` are unrestricted (they need not
lie in `V`); only interior vertices must lie in `V`." B–M l. 341–348 and s3:remMultiset agree
("each occurrence needs a path of its own", "the endpoints … need not lie in `V`", "the proofs …
treat the pairs as an indexed family").

Clause by clause:
- "multiset of pairs of distinct vertices of `G`" — an indexed family `P : ι → V × V` over a
  finite type with `(P i).1, (P i).2 ∈ V(G)` and `(P i).1 ≠ (P i).2`. Every finite multiset of
  pairs is the image (with multiplicities) of some `Fin n → V × V`, and every such family is a
  finite multiset; since `Fin n : Type`, quantifying over `ι : Type` covers all finite multisets.
  Ordered pairs lose nothing: `IsPathBetween.reverse` turns an `xy`-path into a `yx`-path with
  the same edges, interior and length, and the occurrence count is symmetric in the two entries.
  The requirement that the entries be vertices of `G` is essential and correct: for `x ∉ V(G)`
  no `xy`-path with `x ≠ y` exists, so dropping it would make the property false for every graph
  whenever `V ⊋ V(G)`.
- "every vertex lies in at most `t` pairs", counting occurrences — `∀ v, #{i : v ∈ {x_i, y_i}} ≤ t`;
  since `x_i ≠ y_i`, an index is counted once per vertex it contains. Quantifying over `v : V`
  rather than `v ∈ V(G)` changes nothing: for `v ∉ V(G)` the count is `0`, and one checks that
  for every `t` (including `t < 0`) the two versions have the same truth value.
- "there are edge-disjoint paths `P_{x,y}`, `{x,y} ∈ 𝒫`" (one per occurrence) — `∃ Q : ι → List V`
  with pairwise `List.Disjoint` edge lists for `i ≠ j`; a repeated pair gets as many pairwise
  edge-disjoint paths as it has indices. This is exactly the multiset clause.
- "each `P_{x,y}` is an `xy`-path through `V` of length at most `ℓ`" — `IsPathBetween G.edges x_i
  y_i (Q i)` (a path in `G`, 2.4), `IsThrough W (Q i)` (2.6), `pathLength (Q i) ≤ ℓ` (real
  inequality; for a natural length this is `≤ ⌊ℓ⌋₊`, and the manuscript's `ℓ` values
  `4ℓ log n`, `2^{12} L_Y^4` are real).
- "`V ⊆ V(G)`" — not enforced. Harmless: every interior vertex of a path in `G` lies on an edge
  of `G`, hence in `V(G)`, so `IsPathConnected G ℓ t W ↔ IsPathConnected G ℓ t (W ∩ V(G))`.

*Parameter types.* `t : ℝ`: the manuscript passes real multiplicities (`𝗍 = 2^{10}L^8`, s4) to
T16*, and Def 7's "at most `t`" compares a count with `t`; for `t ≥ 0` the property depends on `t`
only through `⌊t⌋₊` (`isPathConnected_natFloor_iff`), so integer uses are recovered by writing
`(k : ℝ)`. `ℓ : ℝ` likewise. This is a faithful rendering, not a weakening.

*Edge cases.*
- `t < 1`: no non-empty admissible family exists, so the property is trivially true
  (`isPathConnected_of_lt_one`), exactly as in the manuscript's reading; the manuscript only uses
  `t ≥ 1` (Lemma 9 `k ≥ 1`, Theorem 16 `2^8 log^5 n`, `t_Y = ⌈λ^{1.6}⌉`, `𝗍 ≥ 1`).
- `ℓ < 1`: false as soon as some admissible non-empty family exists (a path between distinct
  vertices has `≥ 1` edge), as in the manuscript.
- `W = ∅`: every required path is a single edge; `W = V(G)`: any path.
- `G` with no edges: `(ℓ, t)`-path connected iff `t < 1` or `|V(G)| ≤ 1` — as in the manuscript.

*Non-vacuity and the multiset clause (EGTest.Found and scratch §5).* A complete graph is
`(1,1)`-path connected through any `W`; `P3` is not `(1,1)`-path connected; K₂ is
`(1,1)`-path connected but **not** `(ℓ, 2)`-path connected for any `ℓ, W` (the pair `{0,1}`
taken twice needs two edge-disjoint `01`-paths and K₂ has one edge) — I re-proved this last
fact independently in scratch §5 with `ι = Fin 2`. Under the *set* reading of Def 7 K₂ would be
`(1, t)`-path connected for every `t`, so this test shows the formal definition is the multiset
version and not the set version. The real-`t` behaviour (`K2.IsPathConnected 1 (3/2) ∅`, not for
`t ≥ 2`) is also tested.

*Universe.* `ι : Type` avoids a universe parameter in the definition; the library lemma
`IsPathConnected.exists_paths` re-derives the conclusion for an index type in any universe via
`Fintype.equivFin`, so nothing is lost for consumers. `[Fintype ι]` is quantified universally,
which is the right polarity (the hypothesis must hold for every finite index type).

*Verdict:* approve.

---

## 4. Cross-cutting checks

- **Lean conventions.** `ℕ` subtraction appears only in `pathLength [] = 0`, which is unreachable
  from `IsPathIn`. Division by zero appears only in Def 11 for `n ≤ 1`, where the hypotheses are
  already unsatisfiable. `Real.logb 2` is the manuscript's `log` (b). `Finset` vs `Set`: all
  objects are finite in the manuscript (Convention (a)), so `Finset` is the right carrier; no
  `Set`-only object occurs in this group.
- **Typeclass assumptions.** `DecidableEq V` on `edgesAt`, `degE`, `nbrs`, `deg`, `minDeg`,
  `maxDeg`, `nbrSet`, `induce`, `deleteVerts`, `deleteEdges`, `restrictEdges`, `edgesBetween`,
  `eBetween`, `ofEdges`, `IsExpander`, `IsPathConnected`; `Fintype V`, `Fintype G.edgeSet` on
  `ofSimpleGraph`. All are instance arguments with classical fallbacks; none restricts the
  mathematics. No `Nonempty`/`Inhabited`/`Fintype V` is assumed anywhere else, so graphs on an
  infinite ambient type (e.g. `ℕ`) are covered, which is what the manuscript's constantly
  changing vertex sets need.
- **Universes.** `FGraph.{u} : Type u → Type u`; every definition is universe-polymorphic in `V`;
  `IsPathConnected` fixes `ι : Type` (see 3.2).
- **What Lean elaborated** equals the source text for all 26 constants (appendix A §0 output was
  inspected line by line; in particular no coercion landed in an unexpected place: the only casts
  are `ℕ → ℝ` on `U.card`, `F.card`, `G.card`, the `nbrSet` cardinality, the occurrence count and
  `pathLength`).
- **Non-vacuity summary.** Def 11: K₄ is a `(1,0)`-expander, K₂ a `(1,1/2)`-expander; the
  60-vertex path is not a `(1,0)`-expander. Def 7: complete graphs are `(1,1)`-path connected;
  `P3` is not; K₂ separates the set and multiset readings. Balls, paths and all graph operations
  have positive and negative `decide` witnesses (scratch §§2–4).

---

## 5. Non-blocking notes (for the integrator and for authors of statements)

1. **`edgesBetween`/`eBetween` for non-disjoint `A, B`** count the edges inside `A ∩ B` once.
   The manuscript defines `E_H(A,B)` only for disjoint sets and uses it only so; statements should
   keep it that way (or state disjointness).
2. **One-vertex paths.** `IsPathIn E [v]` holds for every `v`, including `v ∉ V(H)`. Safe in
   `ball` (filtered by `W`) and in Def 7 (`x ≠ y`); a future statement about a possibly trivial
   path in `H` must require `v ∈ V(H)` (the docstring says so).
3. **`IsExpander` is trivially true for `ε ≤ 0`** and for `n ≤ 1`. Statements that use the
   min-degree consequence must carry `0 < ε` and `2 ≤ |G|`, as `IsExpander.lt_minDeg` does.
   Manuscript uses only `ε ∈ (0,1]`.
4. **`ball` has an `ℕ` radius**, as Convention (d) says ("an integer `i ≥ 0`"). The cited results
   that write `B^{log⁴ n}` (s1:citLem19, s1:citThm16, not used as black boxes) need `⌊log⁴ n⌋`;
   "length at most `r`" for a real `r ≥ 0` is "length at most `⌊r⌋`", so nothing is lost.
5. **`minDeg` of the vertexless graph is `0`** (Mathlib convention). `lt_minDeg_iff` needs
   `V(H) ≠ ∅`.
6. **`degE` counts a loop once.** Apply it to loopless sets (`H.edges`, `G.edgeFinset`), as
   AGENTS.md already prescribes for `fnum`.
7. **`IsPathConnected` depends on `t` only via `⌊t⌋₊`** (for `t ≥ 0`) and is trivially true for
   `t < 1`; downstream statements with integer multiplicities should write `(k : ℝ)`.
8. **`IsPathConnected` quantifies over `ι : Type`**; use `IsPathConnected.exists_paths` (any
   universe) or `exists_paths_sigma` (joint routing, s3:lemMonotone (iii)) rather than
   instantiating the definition directly with a `Type u` index type.
9. **Multigraphs** (s5, s7 auxiliary) are outside `FGraph`; they will need their own structure
   when those sections are reached. Not a defect of this group.
10. **Manuscript-side remark (not a Lean issue).** The "Remark of B–M" inside s1:citDef11 ("hence
    `δ(G) > s` for every `(ε,s)`-expander `G` on at least two vertices") is literally false for
    `ε ≤ 0` (every graph is then an expander, `isExpander_of_nonpos`); it needs "`ε > 0`", which
    B–M leave implicit. The Lean library states the remark correctly with `0 < ε`. I noticed
    afterwards that `work/p1b/graph.md` has already forwarded the same point; I confirm it
    independently.

---

## Appendix A — scratch file `ReviewGraph.lean` (compiled with `lake env lean`; exactly one error, the intended one at §1's second `example`)

```lean
import EG.Defs.Graph
import EG.Defs.Walk
import EG.Defs.Expander
import EG.Lib.Found.Graph

open EG

/-! ## 0. What Lean elaborated -/
#print EG.FGraph
#print EG.edgesAt
#print EG.degE
#print EG.FGraph.card
#print EG.FGraph.Adj
#print EG.FGraph.instPartialOrder
#print EG.FGraph.nbrs
#print EG.FGraph.deg
#print EG.FGraph.minDeg
#print EG.FGraph.maxDeg
#print EG.FGraph.nbrSet
#print EG.FGraph.induce
#print EG.FGraph.deleteVerts
#print EG.FGraph.deleteEdges
#print EG.FGraph.restrictEdges
#print EG.FGraph.edgesBetween
#print EG.FGraph.eBetween
#print EG.FGraph.ofEdges
#print EG.FGraph.ofSimpleGraph
#print EG.FGraph.toSimpleGraph
#print EG.walkEdges
#print EG.pathLength
#print EG.IsPathIn
#print EG.IsPathBetween
#print EG.interior
#print EG.IsThrough
#print EG.ball
#print EG.FGraph.IsExpander
#print EG.FGraph.IsPathConnected

/-! ## 1. Parse of the Def 11 inequality: (ε|U|) / (log₂ n)² , not logb 2 (n²) and not ε(|U|/…) -/
example (G : FGraph ℕ) (ε s : ℝ) : G.IsExpander ε s ↔
    ∀ U : Finset ℕ, ∀ F : Finset (Sym2 ℕ), U ⊆ G.verts → F ⊆ G.edges →
      1 ≤ U.card → (U.card : ℝ) ≤ (2 * (G.card : ℝ)) / 3 → (F.card : ℝ) ≤ s * (U.card : ℝ) →
      (ε * (U.card : ℝ)) / ((Real.logb 2 (G.card : ℝ)) ^ 2) ≤
        (((G.deleteEdges F).nbrSet U).card : ℝ) := Iff.rfl

-- The wrong parse `logb 2 (n^2)` must NOT be definitionally the same (expect an error here).
example (G : FGraph ℕ) (ε s : ℝ) : G.IsExpander ε s ↔
    ∀ U : Finset ℕ, ∀ F : Finset (Sym2 ℕ), U ⊆ G.verts → F ⊆ G.edges →
      1 ≤ U.card → (U.card : ℝ) ≤ (2 * (G.card : ℝ)) / 3 → (F.card : ℝ) ≤ s * (U.card : ℝ) →
      (ε * (U.card : ℝ)) / (Real.logb 2 ((G.card : ℝ) ^ 2)) ≤
        (((G.deleteEdges F).nbrSet U).card : ℝ) := Iff.rfl

/-! ## 2. Walk layer, concrete -/
example : walkEdges [0, 1, 2, 3] = [s(0, 1), s(1, 2), s(2, 3)] := by decide
example : walkEdges [5] = ([] : List (Sym2 ℕ)) := by decide
example : interior [0, 1, 2, 3] = [1, 2] := by decide
example : interior [0, 1] = ([] : List ℕ) := by decide
example : interior [0] = ([] : List ℕ) := by decide
example : pathLength [0, 1, 2, 3] = 3 := by decide
example : pathLength [0] = 0 := by decide
example : pathLength ([] : List ℕ) = 0 := by decide

def E3 : Finset (Sym2 ℕ) := {s(0, 1), s(1, 2)}
example : IsPathIn E3 [0, 1, 2] := by decide
example : IsPathIn E3 [2, 1, 0] := by decide
example : ¬ IsPathIn E3 [0, 1, 0] := by decide        -- repeated vertex
example : ¬ IsPathIn E3 [0, 2] := by decide           -- non-edge
example : ¬ IsPathIn E3 ([] : List ℕ) := by decide    -- empty list is not a path
example : IsPathIn E3 [7] := by decide                -- stray single vertex IS a path (documented)
example : IsPathBetween E3 2 0 [2, 1, 0] := by decide
example : ¬ IsPathBetween E3 0 2 [2, 1, 0] := by decide
example : IsThrough {1} [0, 1, 2] := by decide
example : ¬ IsThrough {0, 2} [0, 1, 2] := by decide  -- ends unrestricted, interior 1 ∉ W
example : IsThrough (∅ : Finset ℕ) [0, 1] := by decide

/-! ## 3. Graph operations, concrete: the path 0-1-2 plus isolated vertex 3 -/
def P3i : FGraph ℕ := FGraph.ofEdges {0, 1, 2, 3} {s(0, 1), s(1, 2), s(2, 2), s(3, 9)}
example : P3i.edges = {s(0, 1), s(1, 2)} := by decide       -- loop and stray edge dropped
example : P3i.card = 4 := by decide
example : P3i.deg 1 = 2 ∧ P3i.deg 0 = 1 ∧ P3i.deg 3 = 0 ∧ P3i.deg 9 = 0 := by decide
example : P3i.minDeg = 0 ∧ P3i.maxDeg = 2 := by decide
example : (P3i.deleteVerts {3}).minDeg = 1 := by decide
example : P3i.nbrs 1 = {0, 2} := by decide
example : P3i.nbrSet {0} = {1} := by decide
example : P3i.nbrSet {0, 1} = {2} := by decide
example : P3i.nbrSet {0, 1, 2, 3} = ∅ := by decide
example : P3i.nbrSet {0, 42} = {1} := by decide           -- U ⊄ V(H): outside vertex ignored
example : (P3i.induce {1, 2, 3, 7}).verts = {1, 2, 3} := by decide
example : (P3i.induce {1, 2, 3, 7}).edges = {s(1, 2)} := by decide
example : (P3i.deleteVerts {1}).verts = {0, 2, 3} := by decide
example : (P3i.deleteVerts {1}).edges = ∅ := by decide
example : (P3i.deleteEdges {s(0, 1), s(5, 6)}).edges = {s(1, 2)} := by decide
example : (P3i.deleteEdges {s(0, 1)}).verts = {0, 1, 2, 3} := by decide
example : (P3i.restrictEdges {s(0, 1), s(5, 6)}).edges = {s(0, 1)} := by decide
example : P3i.edgesBetween {0, 2} {1} = {s(0, 1), s(1, 2)} := by decide
example : P3i.eBetween {0} {2} = 0 := by decide
example : P3i.eBetween {0, 1} {0, 1} = 1 := by decide    -- non-disjoint case: edges inside
example : degE P3i.edges 1 = 2 := by decide
example : degE ({s(0, 1), s(1, 1)} : Finset (Sym2 ℕ)) 1 = 2 := by decide  -- loop counted once
example : P3i.Adj 0 1 ∧ P3i.Adj 1 0 ∧ ¬ P3i.Adj 0 2 ∧ ¬ P3i.Adj 1 1 := by decide
example : P3i.deleteVerts {3} ≤ P3i := FGraph.deleteVerts_le _

/-! ## 4. Balls (noncomputable: use mem_ball with witnesses) -/
example : 1 ∈ ball P3i 1 {0} {1, 2} :=
  mem_ball.2 ⟨by decide, 0, by decide, [0, 1], by decide, by decide, by decide⟩
example : 2 ∈ ball P3i 2 {0} {1, 2} :=
  mem_ball.2 ⟨by decide, 0, by decide, [0, 1, 2], by decide, by decide, by decide⟩
example : 0 ∉ ball P3i 5 {0} {1, 2} := fun h => by
  have := ball_subset h; revert this; decide
example : 0 ∈ ball P3i 0 {0} {0, 1} :=      -- trivial path: U ∩ W ⊆ ball
  mem_ball.2 ⟨by decide, 0, by decide, [0], by decide, by decide, by decide⟩
-- "through W" matters: 2 is not reachable from 0 through {2} (the interior vertex 1 ∉ {2})
example : 2 ∉ ball P3i 5 {0} {2} := fun h => by
  obtain ⟨-, u, hu, p, hp, hth, -⟩ := mem_ball.1 h
  have hu0 : u = 0 := by simpa using hu
  subst hu0
  have h1 : (1 : ℕ) ∈ EG.interior p := by
    obtain ⟨⟨hne, hnd, hE⟩, hh, hl⟩ := hp
    match p, hne, hh, hl, hnd, hE with
    | [a], _, hh, hl, _, _ => simp at hh hl; omega
    | [a, b], _, hh, hl, _, hE =>
      simp at hh hl; subst hh; subst hl
      have := hE s(0, 2) (by simp [walkEdges])
      exact absurd this (by decide)
    | a :: b :: c :: l, _, hh, hl, hnd, hE =>
      simp at hh; subst hh
      have hab := hE s(0, b) (by simp [walkEdges])
      have hb : b = 1 := by
        have hmem : b ∈ P3i.nbrs 0 := FGraph.mem_nbrs.2 (hab : P3i.Adj 0 b)
        have hn : P3i.nbrs 0 = {1} := by decide
        rw [hn] at hmem; simpa using hmem
      subst hb
      simp [EG.interior]
  exact absurd (hth 1 h1) (by decide)

/-! ## 5. Def 7: the multiset clause really bites, and t is compared as a real -/
def K2 : FGraph ℕ := FGraph.ofEdges {0, 1} {s(0, 1)}
-- the pair {0,1} taken twice (ι = Fin 2) cannot be routed edge-disjointly in K2
example (ℓ : ℝ) (W : Finset ℕ) : ¬ K2.IsPathConnected ℓ 2 W := fun h => by
  obtain ⟨Q, hQ, hdisj⟩ := h (Fin 2) (fun _ => (0, 1)) (fun _ => by decide)
    (fun v => by
      by_cases h0 : v = 0
      · subst h0; norm_num
      · by_cases h1 : v = 1
        · subst h1; norm_num
        · simp [Ne.symm h0, Ne.symm h1])
  have e0 := (hQ 0).1.exists_first_edge (by decide)
  have e1 := (hQ 1).1.exists_first_edge (by decide)
  obtain ⟨w, hw, hmem0⟩ := e0
  obtain ⟨w', hw', hmem1⟩ := e1
  have hw1 : w = 1 := by
    simp [K2, FGraph.ofEdges, Finset.mem_filter] at hmem0; exact hmem0.1
  have hw1' : w' = 1 := by
    simp [K2, FGraph.ofEdges, Finset.mem_filter] at hmem1; exact hmem1.1
  subst hw1 hw1'
  exact hdisj 0 1 (by decide) hw hw'

#check @IsPathBetween.exists_first_edge
```

Output (abridged): the `#print`s reproduce the source definitions verbatim (see §4, "What Lean
elaborated"); the first `Iff.rfl` in §1 is accepted; the second fails with
`Type mismatch … Real.logb 2 (↑G.card ^ 2)`; every `decide`/witness example in §§2–5 is accepted.

## Appendix B — Lean facts checked

Scratch `Disj.lean` (`import Mathlib`), output verbatim:

```
def List.Disjoint.{u_1} : {α : Type u_1} → List α → List α → Prop :=
fun {α} l₁ l₂ => ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ → False
@Finset.mem_sym2_iff : ∀ {α : Type u_1} {s : Finset α} {m : Sym2 α}, m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s
@Real.logb_one : ∀ {b : ℝ}, Real.logb b 1 = 0
@Real.logb_zero : ∀ {b : ℝ}, Real.logb b 0 = 0
@div_zero : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] (a : G₀), a / 0 = 0
```

(also `example : Real.logb 2 1 = 0 := Real.logb_one` and `example (x : ℝ) : x / 0 = 0 :=
div_zero x` accepted). Mathlib source locations: `Mathlib/Data/Finset/Sym.lean` l. 46–50
(`mk_mem_sym2_iff`, `mem_sym2_iff`), `Mathlib/Analysis/SpecialFunctions/Log/Base.lean` l. 50–53
(`logb_zero`, `logb_one`). Independently, the K₂ test in Appendix A §5 type-checks
`hdisj 0 1 _ hw hw'` with `hw : s(0,1) ∈ walkEdges (Q 0)`, `hw' : s(0,1) ∈ walkEdges (Q 1)`,
which is the meaning of `List.Disjoint` used in Def 7.
