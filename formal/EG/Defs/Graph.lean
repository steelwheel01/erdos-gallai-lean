module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Real.Basic

/-!
# Finite simple graphs with explicit vertex and edge sets (manuscript s1:convGraphs)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

PLAN_FORMALIZATION.md §3, layer "Found.Graph": a graph of the manuscript is an `EG.FGraph V`,
a finite vertex set `verts : Finset V` together with a finite edge set `edges : Finset (Sym2 V)`,
with the invariants that every end of an edge is a vertex and that there are no loops.
Graphs of the manuscript change constantly (deleting vertices and edge sets, colour classes,
lent sets), and with an explicit vertex set all these operations stay inside one type `V`.

Contents (Convention [s1:convGraphs] (a), (c)):
* `FGraph`, `FGraph.card` (`|H| = |V(H)|`), `FGraph.Adj`;
* `FGraph.nbrs` (`N_H(v)`), `FGraph.deg` (`d_H(v)`), `FGraph.minDeg` (`δ(H)`),
  `FGraph.maxDeg` (`Δ(H)`), `EG.edgesAt` / `EG.degE` (`deg_F(v)` for an edge set `F`);
* `FGraph.nbrSet` (`Nbr_H(U)`), `FGraph.nbrSetDeg` (`N_{H,d}(U)`, s1:citProp12, added in P2-D),
  `FGraph.IsWellExpanding` (s3:lemL17s, added in P2-D), `FGraph.induce` (`H[U]`),
  `FGraph.deleteVerts` (`H - U`),
  `FGraph.deleteEdges` (`H - F`), `FGraph.edgesBetween` / `FGraph.eBetween` (`E_H(A,B)`,
  `e_H(A,B)`);
* constructors `FGraph.ofEdges` (vertex set and an arbitrary edge set, loops and edges leaving
  the vertex set are discarded) and `FGraph.ofSimpleGraph` (a Mathlib `SimpleGraph` on a
  `Fintype`); conversely `FGraph.toSimpleGraph` (the Mathlib `SimpleGraph` on `V` with the same
  adjacency; the vertices outside `V(H)` are isolated);
* the subgraph order `H ≤ H'` (vertex and edge sets are subsets).
-/

@[expose] public section


namespace EG

variable {V : Type*}

/-- [s1:convGraphs] (a) "Graphs are finite and simple". A finite simple graph with explicit
vertex set `verts` (`V(H)`) and edge set `edges` (`E(H)`): every end of an edge is a vertex, and
no edge is a loop. -/
@[ext]
structure FGraph (V : Type*) where
  /-- The vertex set `V(H)`. -/
  verts : Finset V
  /-- The edge set `E(H)`. -/
  edges : Finset (Sym2 V)
  /-- Every end of an edge is a vertex. -/
  edge_verts : ∀ e ∈ edges, ∀ v ∈ e, v ∈ verts
  /-- There are no loops. -/
  loopless : ∀ e ∈ edges, ¬ e.IsDiag

/-- [s1:convGraphs] (c) "for an edge set `F` and a vertex `v`, `deg_F(v)` is the number of
edges of `F` at `v`": the edges of `F` at `v`. -/
def edgesAt [DecidableEq V] (F : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  F.filter (fun e => v ∈ e)

/-- [s1:convGraphs] (c) "for an edge set `F` and a vertex `v`, `deg_F(v)` is the number of
edges of `F` at `v`". -/
def degE [DecidableEq V] (F : Finset (Sym2 V)) (v : V) : ℕ :=
  (edgesAt F v).card

namespace FGraph

variable (H : FGraph V)

/-- [s1:convGraphs] (a) "For any graph `H` we write `|H| := |V(H)|`". -/
def card : ℕ := H.verts.card

/-- Adjacency: `uv` is an edge of `H`. -/
def Adj (u v : V) : Prop := s(u, v) ∈ H.edges

instance [DecidableEq V] : DecidableRel H.Adj :=
  fun u v => inferInstanceAs (Decidable (s(u, v) ∈ H.edges))

/-- The subgraph order: `H ≤ H'` iff `V(H) ⊆ V(H')` and `E(H) ⊆ E(H')`. -/
instance : PartialOrder (FGraph V) where
  le H H' := H.verts ⊆ H'.verts ∧ H.edges ⊆ H'.edges
  le_refl H := ⟨subset_rfl, subset_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := FGraph.ext (subset_antisymm h₁.1 h₂.1) (subset_antisymm h₁.2 h₂.2)

section DecEq

variable [DecidableEq V]

/-- [s1:convGraphs] (c) "For a vertex `v` of a graph `H`, `N_H(v)` is its set of neighbours". -/
def nbrs (v : V) : Finset V := H.verts.filter (fun w => H.Adj v w)

/-- [s1:convGraphs] (c) "`d_H(v) = deg_H(v)` its degree" (the number of neighbours; equal to
`degE H.edges v`, see `EG.FGraph.deg_eq_degE`). -/
def deg (v : V) : ℕ := (H.nbrs v).card

/-- [s1:convGraphs] (c) "`δ(H)` ... the minimum ... degree" (`0` for the graph without
vertices, as for Mathlib's `SimpleGraph.minDegree`). -/
def minDeg : ℕ := if h : H.verts.Nonempty then H.verts.inf' h H.deg else 0

/-- [s1:convGraphs] (c) "`Δ(H)` ... the maximum degree" (`0` for the graph without vertices). -/
def maxDeg : ℕ := H.verts.sup H.deg

/-- [s1:convGraphs] (c) "For `U ⊆ V(H)`, `Nbr_H(U)` is the set of vertices of `V(H) \ U` that
have a neighbour in `U`." -/
def nbrSet (U : Finset V) : Finset V :=
  (H.verts \ U).filter (fun v => ∃ u ∈ U, H.Adj u v)

/-- [s1:citProp12] "For `U ⊆ V(G)` and `d > 0` let `N_{G,d}(U)` be the set of vertices of
`V(G) \ U` with at least `d` neighbours in `U`." Also [s3:propP13s] (proof): "`Nbr_{G-F,d}(U)`
for the set of vertices outside `U` that have at least `d` neighbours in `U` in the graph
`G - F`" (written `(G.deleteEdges F).nbrSetDeg U d`).
The threshold `d` is real (B-M Prop. 12 takes a real `d > 0`; s3 applies it with an integer
`d_*`, written `(d_* : ℝ)`). Defined for all `U` and `d`; "neighbours in `U`" counts
`N_H(v) ∩ U`. For `d ≤ 0` every vertex of `V(H) \ U` qualifies (the manuscript uses `d > 0`
only). -/
noncomputable def nbrSetDeg (U : Finset V) (d : ℝ) : Finset V :=
  (H.verts \ U).filter (fun v => d ≤ ((H.nbrs v ∩ U).card : ℝ))

/-- [s3:lemL17s] "Call `U ⊆ V(G)` *well-expanding* if `|Nbr_G(U)| ≥ θ_*|U|`." Also the proof
sketch of [s1:citLem19]: "Call `U'` well-expanding if `|Nbr_G(U')| ≥ |U'| log^{24} n`"
(`θ = log^{24} n`). The neighbourhood is taken in `G` itself, not in `G - F`. The threshold
`θ` is a parameter (s3 passes `EG.Star.theta …`); the empty set is well-expanding for every
`θ`. Defined for all `U`; the manuscript takes `U ⊆ V(G)`. -/
def IsWellExpanding (θ : ℝ) (U : Finset V) : Prop :=
  θ * (U.card : ℝ) ≤ ((H.nbrSet U).card : ℝ)

/-- [s1:convGraphs] (c) "`H[U]` is the induced subgraph". Vertex set `V(H) ∩ U` (which is `U`
when `U ⊆ V(H)`, the case used in the manuscript); the edges of `H` with both ends in `U`. -/
def induce (U : Finset V) : FGraph V where
  verts := H.verts ∩ U
  edges := H.edges.filter (fun e => e ∈ U.sym2)
  edge_verts e he v hv := by
    rw [Finset.mem_filter, Finset.mem_sym2_iff] at he
    exact Finset.mem_inter.2 ⟨H.edge_verts e he.1 v hv, he.2 v hv⟩
  loopless e he := H.loopless e (Finset.mem_filter.1 he).1

/-- [s1:convGraphs] (c) "`H - U` and `H \ U` both denote `H[V(H) \ U]`". -/
def deleteVerts (U : Finset V) : FGraph V := H.induce (H.verts \ U)

/-- [s1:convGraphs] (c) "for `F ⊆ E(H)`, `H - F` is obtained by deleting the edges of `F`
(keeping all vertices)". Defined for every edge set `F`; only `E(H) ∩ F` matters. -/
def deleteEdges (F : Finset (Sym2 V)) : FGraph V where
  verts := H.verts
  edges := H.edges \ F
  edge_verts e he := H.edge_verts e (Finset.mem_sdiff.1 he).1
  loopless e he := H.loopless e (Finset.mem_sdiff.1 he).1

/-- The spanning subgraph of `H` with edge set `E(H) ∩ F` (e.g. "the graph with vertex set
`V(X)` whose edges are the edges of colour `i`"). Equal to `H - (E(H) \ F)`. -/
def restrictEdges (F : Finset (Sym2 V)) : FGraph V where
  verts := H.verts
  edges := H.edges.filter (fun e => e ∈ F)
  edge_verts e he := H.edge_verts e (Finset.mem_filter.1 he).1
  loopless e he := H.loopless e (Finset.mem_filter.1 he).1

/-- [s1:convGraphs] (c) "For disjoint `A, B ⊆ V(H)`, `E_H(A,B)` is the set of edges with one end
in `A` and the other in `B`". (Stated for all `A, B`; the manuscript uses it for disjoint
`A`, `B`.) -/
def edgesBetween (A B : Finset V) : Finset (Sym2 V) :=
  H.edges.filter (fun e => ∃ a ∈ A, ∃ b ∈ B, s(a, b) = e)

/-- [s1:convGraphs] (c) "`e_H(A,B) := |E_H(A,B)|`". -/
def eBetween (A B : Finset V) : ℕ := (H.edgesBetween A B).card

/-- The graph with vertex set `W` whose edges are the non-loop edges of `F` with both ends in
`W`. (A total constructor; when `F` has no loops and all its ends lie in `W`, its edge set is
exactly `F`, see `EG.FGraph.ofEdges_edges_of_subset`.) -/
def ofEdges (W : Finset V) (F : Finset (Sym2 V)) : FGraph V where
  verts := W
  edges := F.filter (fun e => ¬ e.IsDiag ∧ e ∈ W.sym2)
  edge_verts _ he v hv := Finset.mem_sym2_iff.1 (Finset.mem_filter.1 he).2.2 v hv
  loopless _ he := (Finset.mem_filter.1 he).2.1

end DecEq

/-- A Mathlib `SimpleGraph` on a finite type, as an `FGraph` with vertex set `univ` and edge set
`G.edgeFinset`. -/
def ofSimpleGraph [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] : FGraph V where
  verts := Finset.univ
  edges := G.edgeFinset
  edge_verts _ _ v _ := Finset.mem_univ v
  loopless _ he := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he)

/-- The Mathlib `SimpleGraph` on the whole type `V` with the adjacency of `H` (the vertices
outside `V(H)` are isolated); its edge set is `E(H)`. Used to apply Mathlib results about
`SimpleGraph` and `SimpleGraph.Walk`. -/
def toSimpleGraph : SimpleGraph V where
  Adj u v := H.Adj u v
  symm := ⟨fun u v (h : s(u, v) ∈ H.edges) => show s(v, u) ∈ H.edges from Sym2.eq_swap ▸ h⟩
  loopless := ⟨fun v (h : s(v, v) ∈ H.edges) => H.loopless _ h (Sym2.mk_isDiag_iff.2 rfl)⟩

instance [DecidableEq V] : DecidableRel H.toSimpleGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (H.Adj u v))

end FGraph

end EG
