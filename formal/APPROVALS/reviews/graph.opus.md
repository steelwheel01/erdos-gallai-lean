# Clean-room review: group `graph`, reviewer `opus`

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent clean-room agent. I reviewed from
scratch and did not rely on earlier approvals or on `work/p1b/graph.review*.md`. I only read
repository files; this review is the one file I wrote.

Scratch files (compiled with `lake env lean` from `formal/`):
* `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/GraphPrint.lean`
  prints each definition with `pp.parens`/`pp.coercions` to confirm how it parses and where the
  coercions go.
* `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/GraphReviewOpus.lean`
  holds independent tests. It compiles with 0 errors and 0 warnings. `#print axioms` on its
  theorems gives only `propext`, `Classical.choice` and `Quot.sound`.

Scope:
* `EG/Defs/Graph.lean`: `EG.FGraph`, `edgesAt`, `degE`, `card`, `Adj`, the `PartialOrder`,
  `nbrs`, `deg`, `minDeg`, `maxDeg`, `nbrSet`, `induce`, `deleteVerts`, `deleteEdges`,
  `restrictEdges`, `edgesBetween`, `eBetween`, `ofEdges`, `ofSimpleGraph`, `toSimpleGraph`.
* `EG/Defs/Walk.lean`: `walkEdges`, `pathLength`, `IsPathIn`, `IsPathBetween`, `interior`,
  `IsThrough`, `ball`.
* `EG/Defs/Expander.lean`: `FGraph.IsExpander`, `FGraph.IsPathConnected`.

Sources:
* manuscript `s1.tex`: `s1:convGraphs` (l. 321–350), `s1:citNotation` (l. 402–417),
  `s1:citDef7` (l. 441–456), `s1:citDef11` (l. 497–508);
* uses in `s2.tex`, `s3.tex` (quoted where relevant);
* `papers/2211.07689.txt`: l. 124–145 (notation, "All our logarithms have base two"), l. 342–348
  (Definition 7 and the multiset sentence), l. 379–385 (balls), l. 584–594 (Definition 11 and
  the remark after it).

**Overall verdict: APPROVE, with notes.** I found no mismatch between any definition and the
manuscript or B–M text in any case the manuscript uses. The notes (N1–N8 at the end) are
edge-case conventions that `Spec` authors and `Spec` reviewers must keep in mind. None of them
is a defect of the definitions.

---

## Manuscript text

* `s1:convGraphs` (a): "Graphs are finite and simple … For any graph H we write |H| := |V(H)|."
* (b): "log = log₂ throughout."
* (c): "For a vertex v of a graph H, N_H(v) is its set of neighbours and d_H(v) = deg_H(v) its
  degree; δ(H) and Δ(H) are the minimum and maximum degree. For U ⊆ V(H), Nbr_H(U) is the set of
  vertices of V(H)∖U that have a neighbour in U. H[U] is the induced subgraph; H−U and H∖U both
  denote H[V(H)∖U]; for F ⊆ E(H), H−F is obtained by deleting the edges of F (keeping all
  vertices). For disjoint A,B ⊆ V(H), E_H(A,B) is the set of edges with one end in A and the
  other in B, and e_H(A,B) := |E_H(A,B)|; for an edge set F and a vertex v, deg_F(v) is the
  number of edges of F at v."
* (d): "A path through V is a path all of whose interior vertices lie in V; its ends are
  unrestricted. For U,V ⊆ V(H) and an integer i ≥ 0, B^i_H(U,V) is the set of vertices of V
  that can be reached by a path through V of length at most i starting at a vertex of U (the
  starting vertex need not lie in V); thus B^i_H(U,V) ⊆ V."
* (e): "Families of pairs of vertices are multisets: a pair may occur several times, and 'every
  vertex lies in at most t pairs' counts occurrences."
* `s1:citDef11`: "An n-vertex graph G is an (ε,s)-expander if for every U ⊆ V(G) and every
  F ⊆ E(G) with 1 ≤ |U| ≤ 2n/3 and |F| ≤ s|U| we have |Nbr_{G−F}(U)| ≥ ε|U|/log²n." The B–M
  text (l. 584–586) is the same: "for every U ⊆ V(G) and F ⊆ E(G) with 1 ≤ |U| ≤ 2/3 n and
  |F| ≤ s|U|, we have |N_{G−F}(U)| ≥ ε|U|/log² n."
* `s1:citDef7`: "A graph G is (ℓ,t)-path connected through a vertex set V ⊆ V(G) if, for every
  collection 𝒫 ⊆ (V(G) choose 2) in which every vertex lies in at most t pairs, there are
  edge-disjoint paths P_{x,y}, {x,y} ∈ 𝒫, such that each P_{x,y} is an xy-path through V of
  length at most ℓ. Multiset clause: … (V(G) choose 2) denotes the multiset of pairs of distinct
  vertices of G; … a pair occurring k times receives k pairwise edge-disjoint paths, and the
  bound t counts occurrences. The ends x,y are unrestricted …" B–M l. 342–348 says the same.

---

## `EG/Defs/Graph.lean`

### `FGraph` (structure, `@[ext]`)
Back-translation: a pair (V(H), E(H)). V(H) is a finite set of elements of the ambient type V.
E(H) is a finite set of unordered pairs {u,v}, with u,v ∈ V(H) for every edge and u ≠ v (no
loops). Sym2 has no multiplicities and a Finset has no repeated elements, so there are no
multi-edges. This is exactly a finite simple graph, (a). The ext lemma compares only `verts`
and `edges`, and the proof fields are irrelevant, so two graphs are equal iff they have the same
vertex set and edge set. Isolated vertices are allowed and are counted in `card`, as in the
manuscript. Universe: `FGraph V : Type u` for `V : Type u`. **approve**

### `card`
`H.verts.card` = |V(H)| = |H|, (a). **approve**

### `Adj`, `DecidableRel` instance
`s(u,v) ∈ E(H)`. This is symmetric (Sym2) and irreflexive (loopless). **approve**

### `PartialOrder`
`H ≤ H'` iff V(H) ⊆ V(H') and E(H) ⊆ E(H'). This is the (not necessarily induced) subgraph
relation, and antisymmetry follows from ext. The manuscript's "H' ⊇ H with V(H') = V(H)"
(s3:lemMonotone (i)) is `H ≤ H' ∧ H'.verts = H.verts`. **approve**

### `nbrs`, `deg`
`nbrs v = {w ∈ V(H) : vw ∈ E(H)}` is N_H(v), and `deg v = |N_H(v)|` is d_H(v). In a simple graph
this equals the number of edges at v (the library proves `deg_eq_degE`). For v ∉ V(H) both are
empty/0, a harmless total extension. **approve**

### `minDeg`, `maxDeg`
δ(H) = min over V(H) of d_H, and Δ(H) = max over V(H) of d_H. On the graph with no vertices
both are 0 (for `minDeg` the manuscript's value would be undefined, or +∞ by the inf
convention). See N1. **approve**

### `edgesAt`, `degE`
`edgesAt F v` = {e ∈ F : v ∈ e}, and `degE F v` is its size: "deg_F(v) is the number of edges of
F at v". A loop s(v,v) in a raw F would count once, but the manuscript's edge sets are edge
sets of simple graphs. **approve**

### `nbrSet`
`(V(H) ∖ U).filter (∃ u ∈ U, uv ∈ E(H))`. This is literally "the set of vertices of V(H)∖U that
have a neighbour in U". For U ⊄ V(H) the extra elements of U have no neighbours and do not
matter. **approve**

### `induce`
Vertex set V(H) ∩ U; edges are the edges of H with both ends in U (`e ∈ U.sym2` ⇔ every end of
e lies in U). For U ⊆ V(H), the manuscript's case, this is H[U]. **approve**

### `deleteVerts`
`H.induce (V(H) ∖ U)`. Its vertex set is V(H) ∩ (V(H)∖U) = V(H)∖U, so it is H[V(H)∖U] = H − U
for every U. **approve**

### `deleteEdges`
Same vertex set; edges E(H)∖F. For F ⊆ E(H) this is H − F ("keeping all vertices"). For other
F only E(H) ∩ F matters. This is also the manuscript's own reading when F ⊄ E(H), which it
writes as `X_i − (F ∩ E(X_i))` (s3.tex:854). **approve**

### `restrictEdges`
Same vertex set; edges E(H) ∩ F. This is a helper with no direct manuscript notation (colour
classes). Correct as documented. **approve**

### `edgesBetween`, `eBetween`
`{e ∈ E(H) : ∃ a ∈ A, ∃ b ∈ B, e = ab}` and its size. For disjoint A, B this is "the set of
edges with one end in A and the other in B". I checked that every manuscript use has disjoint
arguments:
* s2.tex:46, 60, 71, 94, 108–110, 417: `E_H(U, V∖(U∪N))`, `E_H(U', V∖(U'∪N''))` and so on, with
  U' ⊆ U;
* s2.tex:691, 696: `E_X(U,W)` with U ⊆ V(X)∖W;
* s3.tex:126–151: `e_X(U, 𝒩∖𝒯)` with 𝒩 = Nbr_X(U);
* s3.tex:361: `e_H(Sat, X∩Lvs)` with Sat ⊆ W and X ⊆ V(G)∖W.

See N5. **approve**

### `ofEdges`
Vertex set W; edges are the non-loop elements of F with both ends in W. This is a total
constructor, correct as documented. **approve**

### `ofSimpleGraph`, `toSimpleGraph` (+ instance)
`ofSimpleGraph G` has vertex set `univ` and edge set `G.edgeFinset`, the same graph. The edge
finset does not depend on which `Fintype` instance is used. `toSimpleGraph H` is the SimpleGraph
on all of V with adjacency `H.Adj`; vertices outside V(H) are isolated. It is a bridge only and
is correct as documented. **approve**

---

## `EG/Defs/Walk.lean`

### `walkEdges`
`zipWith s(·,·) p p.tail` gives [v₀v₁, v₁v₂, …, v_{k−1}v_k] for p = [v₀,…,v_k]. For [] and
[v] the list is empty. **approve**

### `pathLength`
`p.length − 1` is the number of edges k. The truncated subtraction only matters for p = [],
which `IsPathIn` excludes. **approve**

### `IsPathIn E p`
p is non-empty, has no repeated vertex, and every consecutive pair is an edge in E. This is a
(simple) path whose edges lie in E. The distinct vertices force distinct edges, so edge
disjointness between paths is the only issue. `[v]` counts as a path for every v; this is
documented, see N3. **approve**

### `IsPathBetween E x y p`
A path in E with first vertex x and last vertex y, i.e. an xy-path. For x ≠ y it has at least
one edge (`one_le_pathLength`). **approve**

### `interior`, `IsThrough`
`interior p = p.tail.dropLast` is v₁…v_{k−1}: [] for k ≤ 1, and [b] for [a,b,c]. `IsThrough W p`
means every interior vertex lies in W, with the ends unrestricted. This is (d) and B–M
"internal vertices". **approve**

### `ball H i U W`
The elements w of W for which there exist u ∈ U and an xy-path p from u to w in E(H) with
interior in W and at most i edges. This is (d) word for word: the vertex reached lies in W, the
start u lies in U and need not lie in W, the path passes through W, and it has length ≤ i. A
path of length 0 gives B^i ⊇ U ∩ W. This agrees with B–M's "ball of radius i", whose unfiltered
version is "the vertices at distance at most i from U" (B–M l. 128–129).

Every u–w walk through W can be shortened to a u–w path through W of no greater length. A
shortcut path uses only vertices of the walk, and its interior vertices are neither u nor w, so
they occur at interior positions of the walk. So "path" versus "walk" makes no difference.

`ball` is noncomputable (classical `filter`), which only affects computation. My tests on the
path 0–1–2–3 give:
* `1 ∈ B¹({0},{1})` (the start is not in W);
* `0 ∈ B⁰({0},{0,3})` (the trivial path);
* `0 ∉ B⁷({1},{1,2,3})` (the vertex reached must lie in W);
* `2 ∉ B²({0},{2,3})` (the interior vertex 1 is not in W).

Radius type ℕ: see N2. **approve**

---

## `EG/Defs/Expander.lean`

### `FGraph.IsExpander G ε s` (s1:citDef11)
Elaborated form (`pp.parens`, `pp.coercions`):
```
∀ U F, U ⊆ G.verts → F ⊆ G.edges → 1 ≤ U.card → ↑U.card ≤ (2 * ↑G.card) / 3 →
  ↑F.card ≤ s * ↑U.card → (ε * ↑U.card) / ((Real.logb 2 ↑G.card) ^ 2) ≤ ↑(((G.deleteEdges F).nbrSet U).card)
```
Back-translation: with n = |V(G)|, for every U ⊆ V(G) and every F ⊆ E(G) with 1 ≤ |U|,
|U| ≤ 2n/3 (a real inequality) and |F| ≤ s|U| (real), we have ε|U|/(log₂ n)² ≤ |Nbr_{G−F}(U)|.
This is word for word Def 11: the same quantifiers and non-strict inequalities, log base 2 by
(b), and log²n = (log n)², not log log n. The squared log is confirmed by s2:lemHS, which uses
the factor (log z'/log z)². Here n is the vertex count of the graph under test, as in "an
n-vertex graph G". The manuscript's uses ("an (ε,s)-expander on Z", s2:lemHS with z' = z − |W|,
s3:lemMonotone (i) "both graphs have n vertices, so the logarithm … is the same") all take n to
be the graph's own vertex count.

Edge cases:
* n ≤ 1: in Lean `logb 2 n = 0` and x/0 = 0, so the inequality is trivially true. The
  hypotheses are also unsatisfiable, since 1 ≤ |U| ≤ 2/3 is impossible, which matches
  s2:defWitness ("a graph on one vertex has no set U with 1 ≤ |U| ≤ 2m/3") and s3.tex:114.
  Division by zero never changes a truth value.
* n = 2: log₂ 2 = 1, which is fine.
* ε ≤ 0: every graph is an expander, as the literal manuscript/B–M definition also says (see
  N4).
* s < 0: only F = ∅ with |F| ≤ s|U| < 0 would qualify, and that is impossible, so the property
  is vacuous, as in the manuscript.
* |U| ≤ 2n/3 compared as reals is the same as |U| ≤ ⌊2n/3⌋ because |U| is an integer. Nothing is
  lost by rounding.

Non-vacuity and pinning (scratch `K8_isExpander`, `K8_not_isExpander`): for K₈ (n = 8,
(log₂ 8)² = 9, admissible |U| ≤ 5):
* K₈ **is** a (5,0)-expander (at |U| = 5: 25/9 ≤ 3);
* K₈ is **not** a (6,0)-expander (U = {0,…,4}: 30/9 > 3).

The (5,0) result would fail if the denominator were log₂ n (3), log₂(n²) (6) or ln²n (≈ 4.32),
or if the cutoff were |U| ≤ n. The (6,0) result would hold if the cutoff were |U| ≤ n/2. So the
tests pin (log₂ n)², the 2n/3 cutoff, and show the definition is neither trivially true nor
trivially false. **approve**

### `FGraph.IsPathConnected G ℓ t W` (s1:citDef7, with the multiset clause)
Elaborated form:
```
∀ (ι : Type) [Fintype ι] (P : ι → V × V),
  (∀ i, (P i).1 ∈ G.verts ∧ (P i).2 ∈ G.verts ∧ (P i).1 ≠ (P i).2) →
  (∀ v, ↑#{i | (P i).1 = v ∨ (P i).2 = v} ≤ t) →
  ∃ Q : ι → List V, (∀ i, IsPathBetween G.edges (P i).1 (P i).2 (Q i) ∧ IsThrough W (Q i) ∧
                            ↑(pathLength (Q i)) ≤ ℓ) ∧
                    ∀ i j, i ≠ j → (walkEdges (Q i)).Disjoint (walkEdges (Q j))
```
Back-translation: for every finite multiset 𝒫 of pairs of distinct vertices of G (index i = one
occurrence) in which every vertex is an entry of at most t occurrences, there is one path per
occurrence. Each path is a (P i).1–(P i).2 path in G whose interior lies in W and whose length
is ≤ ℓ, and the paths of distinct occurrences share no edge.

Comparison with Def 7 + (e):
* **Multiset.** A family P : ι → V×V covers every finite multiset of pairs, since a
  non-injective P repeats a pair. "Every vertex lies in at most t pairs" counts indices, i.e.
  occurrences, and because (P i).1 ≠ (P i).2 each index counts once per vertex. "A pair
  occurring k times receives k pairwise edge-disjoint paths" is the condition ∀ i ≠ j.
* **Ordered versus unordered.** An unordered pair {x,y} is represented by (x,y) or (y,x).
  Reversing a path keeps its edges, interior and length (library `IsPathBetween.reverse`,
  `IsThrough.reverse`, `walkEdges_reverse`), so the two readings are equivalent. My scratch test
  `K2_not_pc` feeds `![(0,1),(1,0)]` with t = 2 to K₂. The two orientations count as two
  occurrences of the same pair and need two edge-disjoint paths, which K₂ does not have, so
  K₂ is not (ℓ,2)-path connected through any W. This confirms that `Sym2` equality makes the
  disjointness orientation-blind.
* **Finiteness.** The manuscript's 𝒫 is automatically finite: at most t·|V(G)| occurrences,
  since each occurrence contains a vertex. Restricting to `Fintype ι` loses nothing.
* **Quantifying `∀ v : V` instead of v ∈ V(G).** For v ∉ V(G) the count is 0. If t ≥ 0 there is
  no difference. If t < 0, both the Lean and the manuscript versions are true: either no
  admissible family exists, or the family is empty. The truth value never changes.
* **"Through V ⊆ V(G)".** W is not required to lie in V(G). A path with ≥ 1 edge in E(G) has all
  its vertices in V(G), so `IsThrough W` is equivalent to `IsThrough (W ∩ V(G))` for the paths
  concerned. This is a harmless generalization.
* **Real ℓ and t.** These are the literal real inequalities "length at most ℓ" and "at most t
  pairs". The manuscript does use real values (𝗍 = 2^{10}L^8 in s4, and ℓ = 4ℓ'log n).
* **Universe.** ι ranges over `Type`. Every finite type in any universe is equivalent to some
  `Fin n : Type`, and the property transfers along equivalences (library
  `IsPathConnected.exists_paths` does this). So the definition is equivalent to the
  all-universes version, and there is no free universe parameter.
* **Instances.** The `Fintype ι` and `DecidableEq V` instances only enter through
  `Finset.univ.filter`. Decidable and Fintype are subsingletons, so the proposition does not
  depend on which instances are chosen.
* **Degenerate t.** For t < 1 no family has a pair, so the property holds trivially, as in the
  manuscript (library `isPathConnected_of_lt_one`).

Non-vacuity: the scratch `K2_not_pc` shows it can fail. `EGTest/Found.lean` already has a
positive instance for all index types (complete graphs are (1,1)-path connected), and my
scratch file has a positive single-family check for K₂ with t = 1. **approve**

---

## Notes for `Spec` authors and reviewers (not defects)

* **N1 (δ, Δ on the empty graph).** `minDeg` and `maxDeg` are 0 when V(H) = ∅. A statement whose
  *conclusion* is "δ(H) ≥ d > 0" for an H that can be empty would be false in Lean, where the
  manuscript would read it as vacuous. Such statements need `H.verts.Nonempty` or the
  per-vertex form (`lt_minDeg_iff`). δ is a natural number, so a comparison with a real s needs
  a cast.
* **N2 (ball radius is ℕ).** (d) says "integer i ≥ 0", and s3 uses the integer ℓ_* =
  ⌊2^{10}L^3⌋ (s3.tex:227). Cited results in s1 use real radii (`B^{log⁴n}`, s1.tex:635, 682;
  B–M's `B^{2ℓ log n}`). For a real r ≥ 0, B^r = `ball H ⌊r⌋₊`. Statements must use the floor,
  not the ceiling, and must check that r ≥ 0: for r < 0 the manuscript ball is empty, while
  `ball H 0` = U ∩ W.
* **N3 (trivial paths).** `IsPathIn E [v]` holds for every v, even v ∉ V(H), and `ball` contains
  U ∩ W even for vertices outside V(H). The manuscript always has U, V ⊆ V(H). A statement about
  possibly trivial paths or balls must assume v ∈ V(H) or U, W ⊆ V(H). The library has
  `ball_subset_verts` and `IsPathBetween.left_mem_verts` for this.
* **N4 (B–M remark after Def 11).** The manuscript sentence "hence δ(G) > s for every
  (ε,s)-expander G on at least two vertices" (s1.tex:505–507) is literally false for ε ≤ 0, since
  every graph is then an expander. It needs ε > 0. This is a manuscript wording issue; the
  definition follows the definitional text exactly. The library's `IsExpander.lt_deg` and
  `lt_minDeg` correctly assume `0 < ε`, and the manuscript only uses ε' ∈ (0,1] (s3
  conventions). This is worth a one-word fix in s1:citDef11 in the next manuscript revision.
* **N5 (E_H(A,B) for overlapping sets).** `edgesBetween` is defined for all A, B, and for
  overlapping sets it also contains the edges inside A ∩ B, or between A∩B and A∪B. This is the
  natural literal reading of "one end in A and the other in B". Every manuscript use has
  disjoint arguments (list above). A `Spec` statement should apply it only to disjoint sets or
  state disjointness.
* **N6 (total extensions).** `induce`, `deleteEdges`, `nbrSet`, `ball` and `IsPathConnected` (its
  W) are defined for arguments outside the manuscript's domain (U ⊄ V(H), F ⊄ E(H), W ⊄ V(G)).
  On the manuscript's domain they agree with it, and outside it they are harmless. `Spec`
  statements should still state the manuscript's inclusions as hypotheses where the manuscript
  does, to avoid accidentally strengthening a conclusion.
* **N7 ("spanning expander on Z").** "O is a spanning (ε,s)-expander on Z" should be formalized
  as `O.verts = Z ∧ O.IsExpander ε s`, so that n = |Z|. Using `IsExpander` on a graph with extra
  isolated vertices would change n, and with it both log²n and the 2n/3 bound.
* **N8 (instances).** `IsExpander` and `IsPathConnected` take `[DecidableEq V]`. Different
  instances give propositionally equal statements (subsingleton), but a `Spec` that fixes a
  different instance may need `convert` or `Subsingleton.elim` in proofs. This is not a
  semantic issue.

## Verdict summary

| Item | Verdict |
|---|---|
| `FGraph` (+ ext) | approve |
| `card`, `Adj`, `PartialOrder` | approve |
| `nbrs`, `deg`, `minDeg`, `maxDeg` | approve (N1) |
| `edgesAt`, `degE` | approve |
| `nbrSet` | approve |
| `induce`, `deleteVerts`, `deleteEdges`, `restrictEdges` | approve (N6) |
| `edgesBetween`, `eBetween` | approve (N5) |
| `ofEdges`, `ofSimpleGraph`, `toSimpleGraph` | approve |
| `walkEdges`, `pathLength`, `IsPathIn`, `IsPathBetween` | approve (N3) |
| `interior`, `IsThrough` | approve |
| `ball` | approve (N2, N3) |
| `FGraph.IsExpander` | approve (N4, N7) |
| `FGraph.IsPathConnected` | approve |

No blocking issues.
