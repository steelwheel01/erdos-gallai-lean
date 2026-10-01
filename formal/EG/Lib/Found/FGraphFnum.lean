module

public import EG.Lib.Found.Graph
public import EG.Lib.Found.Fnum

/-!
# `f` of finite graphs `FGraph` (manuscript s1:defObject, s1:factAdd)

For `H : FGraph V`, the manuscript's f(H) := f(E(H)) is written `fnum H.edges`. The edge set of
an `FGraph` has no loops (`FGraph.loopless`), so the loop convention of `EG/Defs/Fnum.lean` plays
no role: `fnum H.edges` is literally the least number of objects in a decomposition of `E(H)`
(`FGraph.fnum_edges_le_iff`, `FGraph.le_fnum_edges_iff`).

* optimal decompositions: `FGraph.exists_isDecomp_edges`, `FGraph.fnum_edges_le_iff`,
  `FGraph.le_fnum_edges_iff`;
* [s1:factAdd](a) `FGraph.fnum_edges_le_card_edges`; (b) for deleting an edge set
  `FGraph.fnum_edges_le_deleteEdges_add`;
* f(H) ≤ f(|H|): `FGraph.fnum_edges_le_fmax`, `FGraph.fnum_edges_le_fmax_of_card_le`;
* [s1:factAdd](c) vertex-disjoint unions: `FGraph.fnum_union_edges_of_disjoint_verts`,
  `FGraph.fnum_edges_eq_add_of_disjoint_verts`, and splitting a graph along a vertex set that no
  edge leaves: `FGraph.fnum_edges_eq_induce_add_deleteVerts`;
* [s1:factAdd](d) deleting isolated vertices (the form of s7:thmHI step (1)):
  `FGraph.deg_eq_zero_iff`, `FGraph.edges_induce_of_forall_mem`,
  `FGraph.edges_deleteVerts_of_forall_not_mem`, `FGraph.fnum_edges_deleteVerts_of_forall_not_mem`,
  `FGraph.fnum_edges_deleteVerts_singleton_of_deg_eq_zero`, `FGraph.card_deleteVerts_singleton`.
-/

public section


namespace EG

namespace FGraph

variable {V : Type*} (H : FGraph V)

/-- The edge set of an `FGraph` is its own non-loop part. -/
theorem coe_edges_sdiff_diagSet : (H.edges : Set (Sym2 V)) \ Sym2.diagSet = H.edges :=
  coe_sdiff_diagSet_of_loopless H.loopless

/-- [s1:defObject] "f(H) := f(E(H))": an optimal decomposition of `E(H)`. -/
theorem exists_isDecomp_edges :
    ∃ D : List (Obj V), IsDecomp (H.edges : Set (Sym2 V)) D ∧ D.length = fnum H.edges :=
  EG.exists_isDecomp_length_eq_fnum H.loopless

/-- [s1:defObject]: `f(H) ≤ k` iff `E(H)` has a decomposition into at most `k` objects. -/
theorem fnum_edges_le_iff {k : ℕ} :
    fnum H.edges ≤ k ↔ ∃ D : List (Obj V), IsDecomp (H.edges : Set (Sym2 V)) D ∧ D.length ≤ k :=
  EG.fnum_le_iff H.loopless

/-- [s1:defObject]: `k ≤ f(H)` iff every decomposition of `E(H)` has at least `k` objects. -/
theorem le_fnum_edges_iff {k : ℕ} :
    k ≤ fnum H.edges ↔ ∀ D : List (Obj V), IsDecomp (H.edges : Set (Sym2 V)) D → k ≤ D.length :=
  EG.le_fnum_iff H.loopless

/-- [s1:factAdd](a) for graphs: `f(H) ≤ |E(H)|`. -/
theorem fnum_edges_le_card_edges : fnum H.edges ≤ H.edges.card :=
  fnum_le_card H.edges

/-- [s1:factAdd](b) for deleting an edge set `F ⊆ E(H)`: `f(H) ≤ f(H - F) + f(F)`. -/
theorem fnum_edges_le_deleteEdges_add [DecidableEq V] {F : Finset (Sym2 V)} (hF : F ⊆ H.edges) :
    fnum H.edges ≤ fnum (H.deleteEdges F).edges + fnum F := by
  have h : H.edges = (H.deleteEdges F).edges ∪ F := by
    rw [deleteEdges_edges, Finset.sdiff_union_of_subset hF]
  rw [h]
  exact fnum_union_le (by rw [deleteEdges_edges]; exact Finset.sdiff_disjoint)

/-! ### `f(H) ≤ f(|H|)` -/

/-- [s1:defObject] "f(n) := max{f(H) : |V(H)| = n}": `f(H) ≤ f(|H|)` for every graph `H`. -/
theorem fnum_edges_le_fmax : fnum H.edges ≤ fmax H.card := by
  classical
  -- `H` as a `SimpleGraph` on the vertex type `↥V(H)`
  let G : SimpleGraph H.verts := SimpleGraph.fromEdgeSet {e | e.map Subtype.val ∈ H.edges}
  let φ : H.verts ↪ V := Function.Embedding.subtype _
  have hmap : G.edgeFinset.map φ.sym2Map = H.edges := by
    ext e
    simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset, G, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, Set.mem_ofPred_eq, Sym2.mem_diagSet, Function.Embedding.sym2Map_apply]
    constructor
    · rintro ⟨x, ⟨hx, -⟩, rfl⟩
      exact hx
    · intro he
      induction e using Sym2.ind with
      | h a b =>
        refine ⟨s(⟨a, H.edge_verts _ he a (Sym2.mem_mk_left a b)⟩,
          ⟨b, H.edge_verts _ he b (Sym2.mem_mk_right a b)⟩), ⟨by simpa using he, ?_⟩, by simp [φ]⟩
        intro hd
        exact H.loopless _ he (by simpa using hd)
  rw [← hmap, fnum_map]
  exact fnum_le_fmax G (by simp)

/-- `f(H) ≤ f(n)` whenever `|H| ≤ n` (`f(n)` is non-decreasing, [s1:factAdd](d)). -/
theorem fnum_edges_le_fmax_of_card_le {n : ℕ} (h : H.card ≤ n) : fnum H.edges ≤ fmax n :=
  H.fnum_edges_le_fmax.trans (fmax_mono h)

/-! ### [s1:factAdd](c): vertex-disjoint unions -/

section DecEq

variable [DecidableEq V]

/-- [s1:factAdd](c) "If H is the vertex-disjoint union of graphs H₁ and H₂, then
f(H) = f(H₁) + f(H₂)", for `FGraph`s with disjoint vertex sets. -/
theorem fnum_union_edges_of_disjoint_verts (H₁ H₂ : FGraph V) (h : Disjoint H₁.verts H₂.verts) :
    fnum (H₁.edges ∪ H₂.edges) = fnum H₁.edges + fnum H₂.edges :=
  fnum_union_eq_of_vertexDisjoint fun e₁ he₁ e₂ he₂ v hv₁ hv₂ =>
    Finset.disjoint_left.1 h (H₁.edge_verts e₁ he₁ v hv₁) (H₂.edge_verts e₂ he₂ v hv₂)

/-- [s1:factAdd](c) "If H is the vertex-disjoint union of graphs H₁ and H₂, then
f(H) = f(H₁) + f(H₂)": `E(H) = E(H₁) ∪ E(H₂)` with `V(H₁) ∩ V(H₂) = ∅`. (The vertex set of `H`
plays no role.) -/
theorem fnum_edges_eq_add_of_disjoint_verts {H₁ H₂ : FGraph V}
    (hE : H.edges = H₁.edges ∪ H₂.edges) (h : Disjoint H₁.verts H₂.verts) :
    fnum H.edges = fnum H₁.edges + fnum H₂.edges := by
  rw [hE]
  exact fnum_union_edges_of_disjoint_verts H₁ H₂ h

/-- [s1:factAdd](c), split form: if no edge of `H` joins `A` to its complement, then
`f(H) = f(H[A]) + f(H - A)`. -/
theorem fnum_edges_eq_induce_add_deleteVerts (A : Finset V)
    (hA : ∀ u v, H.Adj u v → u ∈ A → v ∈ A) :
    fnum H.edges = fnum (H.induce A).edges + fnum (H.deleteVerts A).edges := by
  refine H.fnum_edges_eq_add_of_disjoint_verts ?_ ?_
  · ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [Finset.mem_union, mem_induce_edges, deleteVerts, Finset.mem_sdiff, Sym2.mem_iff,
        forall_eq_or_imp, forall_eq]
      constructor
      · intro he
        have ha := H.edge_verts _ he a (Sym2.mem_mk_left a b)
        have hb := H.edge_verts _ he b (Sym2.mem_mk_right a b)
        by_cases haA : a ∈ A
        · exact Or.inl ⟨he, haA, hA a b he haA⟩
        · refine Or.inr ⟨he, ⟨ha, haA⟩, hb, fun hbA => haA ?_⟩
          exact hA b a ((H.adj_iff).2 (Sym2.eq_swap ▸ he)) hbA
      · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
  · rw [induce_verts, deleteVerts_verts]
    exact Finset.disjoint_left.2 fun v hv hv' =>
      (Finset.mem_sdiff.1 hv').2 (Finset.mem_inter.1 hv).2

/-! ### [s1:factAdd](d): deleting isolated vertices -/

/-- A vertex has degree `0` iff no edge contains it. -/
theorem deg_eq_zero_iff {v : V} : H.deg v = 0 ↔ ∀ e ∈ H.edges, v ∉ e := by
  rw [deg_eq_degE, degE, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_edgesAt, not_and]

/-- Inducing on a vertex set that contains every end of every edge keeps all edges. -/
theorem edges_induce_of_forall_mem {U : Finset V} (hU : ∀ e ∈ H.edges, ∀ v ∈ e, v ∈ U) :
    (H.induce U).edges = H.edges := by
  ext e
  rw [mem_induce_edges]
  exact ⟨And.left, fun he => ⟨he, hU e he⟩⟩

/-- Deleting vertices that lie on no edge keeps all edges. -/
theorem edges_deleteVerts_of_forall_not_mem {U : Finset V}
    (hU : ∀ e ∈ H.edges, ∀ v ∈ e, v ∉ U) : (H.deleteVerts U).edges = H.edges :=
  H.edges_induce_of_forall_mem fun e he v hv =>
    Finset.mem_sdiff.2 ⟨H.edge_verts e he v hv, hU e he v hv⟩

/-- [s1:factAdd](d) "Adding or deleting isolated vertices does not change f": deleting vertices
that lie on no edge. -/
theorem fnum_edges_deleteVerts_of_forall_not_mem {U : Finset V}
    (hU : ∀ e ∈ H.edges, ∀ v ∈ e, v ∉ U) : fnum (H.deleteVerts U).edges = fnum H.edges := by
  rw [H.edges_deleteVerts_of_forall_not_mem hU]

/-- [s1:factAdd](d) in the form of s7:thmHI step (1): "If v were isolated, then f(G - v) = f(G)". -/
theorem fnum_edges_deleteVerts_singleton_of_deg_eq_zero {v : V} (hv : H.deg v = 0) :
    fnum (H.deleteVerts {v}).edges = fnum H.edges :=
  H.fnum_edges_deleteVerts_of_forall_not_mem fun e he _ hw hwv =>
    (H.deg_eq_zero_iff.1 hv) e he (Finset.mem_singleton.1 hwv ▸ hw)

/-- `|G - v| = |G| - 1` for a vertex `v` of `G`. -/
theorem card_deleteVerts_singleton {v : V} (hv : v ∈ H.verts) :
    (H.deleteVerts {v}).card = H.card - 1 := by
  rw [card_def, card_def, deleteVerts_verts, Finset.card_sdiff_of_subset
    (Finset.singleton_subset_iff.2 hv), Finset.card_singleton]

end DecEq

end FGraph

end EG
