module

public import EG.Defs.Graph
public import EG.Defs.Orient

/-!
# Statement of Lemma GATE (manuscript s6:lemGATE)

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/Chain/Gate.lean` proves it.

Manuscript, Lemma GATE (forward direction) [s6:lemGATE]:
"Let `F ⊆ E(G)` and let `F⃗` be an orientation of `F` with `d⁺_{F⃗}(v) = d⁻_{F⃗}(v)` at every
vertex `v`. Let `𝒲` be a set of arcs of `F⃗` such that `F⃗ - 𝒲` is acyclic. Then `F` decomposes
into at most `|𝒲|` cycles of `G`. More precisely, `F⃗` is the arc-disjoint union of directed
cycles, each of length at least `3`, each the orientation of a cycle of `G`, and each containing an
arc of `𝒲`; there are at most `|𝒲|` of them."

Formal reading: `G : EG.FGraph V` (finite simple graph), `F : Finset (Sym2 V)` with
`F ⊆ E(G)`, the orientation `F⃗` is an arc set `A` with `EG.IsOrientation F A`, balance is
`EG.IsBalanced A`, `𝒲` is `W : Finset (V × V)` with `W ⊆ A`, and `F⃗ - 𝒲` is `A \ W`.
* `GateStatement`: the first conclusion ("`F` decomposes into at most `|𝒲|` cycles of `G`"),
  with the decomposition in the sense of `EG.IsDecomp` ([s1:defObject]) and every object a cycle
  all of whose edges are edges of `G`.
* `GatePreciseStatement`: the "More precisely" sentence, with the directed cycles given as vertex
  lists `c` (arcs `EG.cycleArcs c`); "the orientation of a cycle of `G`" is: `c` is a well-formed
  cycle object (no repeated vertex, length `≥ 3`) with all edges in `E(G)`, and its arcs are the
  arcs of `F⃗` along it.
-/

@[expose] public section


namespace EG.Spec

universe u

/-- [s6:lemGATE] (forward direction, first conclusion) "Let `F ⊆ E(G)` and let `F⃗` be an
orientation of `F` with `d⁺_{F⃗}(v) = d⁻_{F⃗}(v)` at every vertex `v`. Let `𝒲` be a set of arcs of
`F⃗` such that `F⃗ - 𝒲` is acyclic. Then `F` decomposes into at most `|𝒲|` cycles of `G`." -/
def GateStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (F : Finset (Sym2 V)) (A W : Finset (V × V)),
    F ⊆ G.edges → EG.IsOrientation F A → EG.IsBalanced A → W ⊆ A → EG.IsAcyclic (A \ W) →
    ∃ D : List (EG.Obj V), EG.IsDecomp (F : Set (Sym2 V)) D ∧ D.length ≤ W.card ∧
      ∀ o ∈ D, (∃ c : List V, o = EG.Obj.cycle c) ∧ ∀ e ∈ o.edges, e ∈ G.edges

/-- [s6:lemGATE] (forward direction, "More precisely") "`F⃗` is the arc-disjoint union of directed
cycles, each of length at least `3`, each the orientation of a cycle of `G`, and each containing an
arc of `𝒲`; there are at most `|𝒲|` of them."  The directed cycles are the vertex lists in `cs`;
arc-disjointness and "union is `F⃗`" say that the concatenated arc lists are duplicate free with
exactly the arcs of `A`. -/
def GatePreciseStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (F : Finset (Sym2 V)) (A W : Finset (V × V)),
    F ⊆ G.edges → EG.IsOrientation F A → EG.IsBalanced A → W ⊆ A → EG.IsAcyclic (A \ W) →
    ∃ cs : List (List V),
      (∀ c ∈ cs, EG.IsDirCycle A c ∧ 3 ≤ c.length ∧ (EG.Obj.cycle c).WF ∧
        (∀ e ∈ EG.cycleEdges c, e ∈ G.edges) ∧ (∃ w ∈ W, w ∈ EG.cycleArcs c)) ∧
      (cs.flatMap EG.cycleArcs).Nodup ∧ (∀ a, a ∈ cs.flatMap EG.cycleArcs ↔ a ∈ A) ∧
      cs.length ≤ W.card

end EG.Spec
