# Clean-room review: group `objects-main-fnum`, reviewer `opus`

Date: 2026-09-26. Reviewer: Claude Opus 5.5 (independent clean-room agent; I did not rely on
earlier approvals). Repository files were only read; the one file written is this review.
Scratch tests: `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/ReviewOpus.lean`
(compiles with `lake env lean`; the two theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`).

Scope: `EG/Defs/Objects.lean` (`EG.cycleEdges`, `EG.Obj`, `EG.Obj.edges`, `EG.Obj.WF`,
`EG.IsDecomp`), `EG/Defs/Fnum.lean` (`EG.fnum`, `EG.fmax`), `EG/Spec/Main.lean`
(`EG.Spec.MainInternal`). Manuscript: s1.tex, `s1:defObject` (l. 354–362), `s1:factAdd`
(l. 364–390), `s1:thmMain` (l. 66–84), graph convention `s1:convGraphs`(a) (l. 321–326), and
the last step of `s7:thmMainProof` (s7.tex l. 1434ff.).

**Overall verdict: APPROVE (with notes).** No mismatch found.

---

## Manuscript text being formalized

* `s1:convGraphs`(a): "Graphs are finite and simple, unless they are explicitly called
  multigraphs (auxiliary multigraphs occur only in Sections 5 and 7)."
* `s1:defObject`: "An *object* is a cycle (of length at least 3) or a single edge. A
  *decomposition* of an edge set F is a partition of F into the edge sets of objects; a
  decomposition of a graph H is a decomposition of E(H). f(F) is the least number of objects in
  a decomposition of F (so f(∅)=0); f(H) := f(E(H)); and f(n) := max{f(H) : |V(H)| = n}."
* `s1:factAdd`: (a) f(F) ≤ |F|; (b) disjoint F₁, F₂ ⇒ f(F₁ ∪ F₂) ≤ f(F₁)+f(F₂); (c) vertex-disjoint
  union ⇒ f(H) = f(H₁)+f(H₂); (d) adding/deleting isolated vertices does not change f, so f(n) is
  non-decreasing.
* `s1:thmMain`: "... Then every graph G on n vertices satisfies f(G) ≤ c_EG n. In particular
  f(n) = O(n)." `s7:thmMainProof` ends: "In particular f(n) ≤ c_EG n for every n, so f(n)=O(n)."

---

## 1. `EG.cycleEdges (c : List V) : List (Sym2 V)`

`List.zipWith (fun a b => s(a, b)) c (c.rotate 1)`.

Back-translation: for c = [c₀,…,c_{k-1}], `c.rotate 1 = [c₁,…,c_{k-1},c₀]`, so the result is
[s(c₀,c₁), s(c₁,c₂), …, s(c_{k-2},c_{k-1}), s(c_{k-1},c₀)], the k edges of the closed walk
c₀c₁…c_{k-1}c₀ (list length k = c.length). Edge cases: [] ↦ []; [a] ↦ [s(a,a)] (a loop);
[a,b] ↦ [s(a,b), s(b,a)] (the same edge twice). Those degenerate cases are all excluded by
`Obj.WF` (below), so they never reach a decomposition.

Verdict: **approve** (helper; correct).

## 2. `EG.Obj` / `EG.Obj.edges`

`inductive Obj V | edge (e : Sym2 V) | cycle (c : List V)`, `deriving DecidableEq`;
`edges (.edge e) = [e]`, `edges (.cycle c) = cycleEdges c`.

Back-translation: a syntactic description of an object (one edge, or a cyclic vertex list) and
its edge list. Many syntactic descriptions give the same object (rotations/reversals of a cycle
list); this does not matter because `IsDecomp` forbids two entries sharing an edge and `fnum`
minimises over lists. The derived `DecidableEq` instance is harmless (only `[DecidableEq V]`
needed). Universe: `Obj V : Type u` for `V : Type u`, no issue.

Verdict: **approve**.

## 3. `EG.Obj.WF`

`edge e ↦ ¬ e.IsDiag`; `cycle c ↦ c.Nodup ∧ 3 ≤ c.length`.

Back-translation: a single edge is a non-loop edge {u,v}, u ≠ v; a cycle has k ≥ 3 pairwise
distinct vertices. With k ≥ 3 distinct vertices, the k edges s(cᵢ, c_{i+1 mod k}) are
non-loops and pairwise distinct (for k = 2 they would coincide, hence the bound 3), so the
edge set is exactly the edge set of a cycle C_k of length k ≥ 3 in the usual graph-theoretic
sense. This is "a cycle (of length at least 3) or a single edge". Checked in scratch:
`¬ (Obj.cycle [0,1]).WF`, `¬ (Obj.cycle [0,1,2,0,3,4]).WF` (a closed walk through a vertex
twice is not a cycle), `¬ (Obj.edge s(0,0)).WF`. The library proves `WF.not_isDiag`,
`WF.nodup_edges`, `nodup_cycleEdges`, `WF.length_edges_pos` (no sorry).

Verdict: **approve**.

## 4. `EG.IsDecomp (E : Set (Sym2 V)) (D : List (Obj V))`

`(∀ o ∈ D, o.WF) ∧ (D.flatMap Obj.edges).Nodup ∧ ∀ e, e ∈ D.flatMap Obj.edges ↔ e ∈ E`.

Back-translation: D is a finite list of objects; the concatenation of their edge lists has no
repetition (so each object's edges are distinct and objects are pairwise edge-disjoint), and the
union of their edge sets is exactly E. Since each WF object has ≥ 1 edge, no two entries of D can
be equal (they would repeat an edge), and D.length is exactly the number of parts. So IsDecomp E D
⟺ {E(o) : o ∈ D} is a partition of E into edge sets of objects, with D.length = number of parts.
This matches "a partition of F into the edge sets of objects" (parts of a partition are nonempty
and pairwise disjoint; both hold). Objects are automatically subgraphs of the graph on E since
all their edges lie in E.

Edge cases: E = ∅ ⟺ D = [] works (`isDecomp_nil_iff`), so f(∅)=0; an E containing a loop has no
decomposition (consistent with the manuscript: loops are not in any object); infinite E has no
decomposition (irrelevant, all sets are finite). Checked in scratch: duplicate object rejected,
two representations of the same triangle rejected, missing edge rejected, extra edge rejected,
a 4-cycle using a non-edge rejected, and a reversed list `[2,1,0]` accepted for the triangle.

Verdict: **approve**.

## 5. `EG.fnum (F : Finset (Sym2 V)) : ℕ`

`sInf {k | ∃ D, IsDecomp (↑F \ Sym2.diagSet) D ∧ D.length = k}`.

Back-translation: the least number of objects in a decomposition of the non-loop part of F.
For loopless F (all edge sets in the manuscript: `s1:convGraphs`(a) makes every graph simple, and
f is only applied to E(H) or subsets of it; the auxiliary multigraphs of s5/s7 are not
arguments of f, they only route arcs; the quotients Q_l that are arguments of f are stated to be
simple) this is literally the manuscript's f(F). The set is nonempty (single edges;
`exists_isDecomp_sdiff_diagSet`), so `sInf` on ℕ is a genuine minimum, never the junk value
`sInf ∅ = 0` (`fnum_spec`). f(∅) = 0 (`fnum_empty`).

Loop convention: for F containing a loop, the manuscript's f(F) is undefined (min over ∅); the
Lean value ignores loops (e.g. `fnum {s(0,0)} = 0`). This is documented in the module docstring
and in AGENTS.md, with loopless-only usage rules. It does not change any value the manuscript
uses. It is a trap for later statement authors (a raw-`F` statement `fnum F ≤ k` without a
looplessness hypothesis would be weaker than intended); see Note N1.

Quantitative sanity checks (scratch, directly from the definition, not through library lemmas):
f(P₃) = f({01, 12}) = 2 (a tree: lower bound because one object would need exactly 2 edges,
impossible for an edge (1) or a WF cycle (≥ 3)). The repository test file `EGTest/Fnum.lean`
additionally has f(K₃)=1, f(K₄)=3, f(star_k)=k, and f(2 disjoint triangles)=2, all of which are
the correct combinatorial values (for K₄: every vertex has odd degree 3, so ≥ 2 single edges are
needed, and two edge-disjoint triangles do not exist in K₄, hence 3).

`s1:factAdd` is proved about this definition in `EG/Lib/Found/Fnum.lean` without sorry
(`scripts/Axioms.lean --prefix EG EG.Lib.Found.FnumMain`: 527 constants, 0 use sorryAx):
(a) `fnum_le_card`, (b) `fnum_union_le` / `fnum_biUnion_le`, (c)
`fnum_union_eq_of_vertexDisjoint` / `fnum_edgeFinset_sup_of_disjoint_support`, (d) `fnum_map`,
`fnum_edgeFinset_induce_of_support_subset`, `fmax_mono`. The statements match the manuscript
items (for (c) the edge-set form "no vertex incident to an edge of F₁ and one of F₂" is the right
reading of "vertex-disjoint union").

Verdict: **approve** (with Note N1).

## 6. `EG.fmax (n : ℕ) : ℕ`

`Finset.univ.sup fun H : SimpleGraph (Fin n) => fnum H.edgeFinset` (classical instances).

Back-translation: the maximum of f(H) over all simple graphs H on the vertex set {0,…,n−1}.
The universe of graphs on `Fin n` is finite and nonempty, so the `sup` in ℕ (bottom 0) is a
genuine max. Since every finite simple graph with n vertices is isomorphic to one on `Fin n` and
f is invariant under injective relabelling (`fnum_map`), this is max{f(H) : |V(H)| = n}. Both
directions are proved: `fnum_le_fmax` (any `Fintype V` in any universe with card V = n) and
`exists_fnum_eq_fmax` (attained). The classical instances only affect which `Fintype` instances
are used, and `edgeFinset`'s value does not depend on them (Fintype is a subsingleton). Edge
cases: fmax 0 = 0, fmax 1 = 0 (scratch), fmax 2 = 1 (repo test). n = 0 is the empty graph,
consistent with the manuscript's definition.

Verdict: **approve**.

## 7. `EG.Spec.MainInternal`

```
∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
  ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V
```

Back-translation: there is a natural number c such that every simple graph G on a finite vertex
set V has a decomposition of E(G) into at most c·|V| objects; i.e. f(G) ≤ c·|V(G)| for all
finite simple graphs G.

Comparison with `s1:thmMain`: the theorem says f(G) ≤ c_EG n for every graph G on n vertices,
with an explicit (galactic, real) c_EG, "in particular f(n) = O(n)". MainInternal is the
qualitative statement: the existential over c : ℕ is equivalent to the existential over a real
constant (take ⌈c_EG⌉), and the explicit value of c_EG is intentionally not locked. This is the
Erdős–Gallai conjecture itself, which is the target (`Erdos184.erdos_184`); the explicit constant
is not part of it. Quantifiers: "every graph G on n vertices" ↔ ∀ V finite, ∀ G; n = |V| =
`Fintype.card V` (independent of the Fintype instance). Graphs with isolated vertices are
included (n counts them; that only makes the bound weaker, as in the manuscript). n = 0 and n = 1
are included and trivially satisfied (no edges ⇒ D = []).

Binder details: `[DecidableEq V]` is a universally quantified instance that the body does not
use, so it neither strengthens nor weakens the statement (every type has one classically).
`G.edgeSet` is a `Set`, no `DecidableRel G.Adj` is needed. `V : Type` (universe 0) only: this
is not a restriction because every finite graph is isomorphic to one on `Fin n`; the
universe-polymorphic form is proved in `EG/Lib/Found/FnumMain.lean`
(`fnum_edges_le_of_mainInternal`, any universe `u`), and `EGCheck/Bridge.lean`
(`of_mainInternal`) transports MainInternal to the universe-polymorphic upstream
`Erdos184.erdos_184` along `Fintype.equivFin` (read, not re-proved by me).

Non-vacuity: MainInternal with c = 0 is refuted by K₂ (scratch); the quadratic analogue
(`D.length ≤ |V|·|V|`) is provable from the definitions (scratch), so the decomposition
predicate is satisfiable and the content of MainInternal is exactly the linear bound, which is
the open conjecture. No encoding shortcut can make it easier: any `D` with `IsDecomp G.edgeSet D`
is a genuine partition of E(G) into cycles and edges of G (item 4).

### Equivalence with "f(n) = O(n)"

`EG/Lib/Found/FnumMain.lean` proves (no sorry)
`mainInternal_iff_fmax : MainInternal ↔ ∃ c : ℕ, ∀ n, fmax n ≤ c * n`. I read the proof: the
forward direction uses `exists_fnum_eq_fmax` and `fnum_edgeFinset_le_iff`, the backward direction
`fnum_le_fmax`; both are sound. To close the last gap to the literal asymptotic statement I proved
in scratch

```
theorem mainInternal_iff_isBigO :
    Spec.MainInternal ↔ (fun n : ℕ => (fmax n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ))
```

(axioms: propext, Classical.choice, Quot.sound). The backward direction uses the trivial bound
fmax n ≤ C(n,2) ≤ n² to absorb the finitely many n below the IsBigO threshold N, taking
c = max(⌈C⌉, N). So MainInternal is exactly "f(n) = O(n)" with f(n) the manuscript's f(n).
(It could be worth adding this `IsBigO` form to `FnumMain.lean` as a permanent fidelity check;
suggestion only.)

Verdict: **approve**.

---

## Notes (non-blocking)

* **N1 (loop convention of `fnum`).** `fnum` silently drops loops. This is a documented and
  reasonable totalisation, and it matches Mathlib's `SimpleGraph.fromEdgeSet`, but because
  `fnum` is locked, every future locked statement that applies `fnum` to a raw `Finset (Sym2 V)`
  must carry `∀ e ∈ F, ¬ e.IsDiag` (or use `H.edges` / `G.edgeFinset`), or it will be weaker
  than the manuscript statement. Statement reviewers of later groups should check this.
* **N2 (explicit constant).** MainInternal does not lock the explicit constant
  c_EG = max{C₀/(1−2θ_Q), N₀/2} of `s1:thmMain`, only its existence. This is the intended
  target (the conjecture), not a mismatch; the docstring could say "for some constant c" to make
  that explicit.
* **N3 (multigraphs).** `Finset (Sym2 V)` cannot represent parallel edges; this is fine because
  f is only applied to simple graphs in the manuscript (s1:convGraphs(a); the s5/s7 multigraphs
  are auxiliary routing structures, and the Q_l fed to f are simple).
