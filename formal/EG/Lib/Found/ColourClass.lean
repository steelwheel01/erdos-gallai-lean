module

public import EG.Lib.Found.Graph
public import EG.Lib.Prob.Named

/-!
# Colour classes of an edge colouring

`EG.FGraph.colourClass X c i`, for a colouring `c : ↥E(X) → κ` of the edge finset of `X` and a
colour `i : κ`, is the graph with vertex set `V(X)` whose edges are the edges of colour `i`
([s3:lemL15p]: "for `i ∈ [k]` let `X_i` be the graph with vertex set `V(X)` whose edges are the
edges of colour `i`"). The same object appears in the colourings of [s3:thmT16s] (Step 1),
[s3:defCOL] / [s3:lemCOL] and [s4:lemTPV] (item (G1)), so it is a shared definition here rather
than a proof-local one.

By definition (`colourClass_eq`, `rfl`) it is
`X.restrictEdges (FinDist.selectSet X.edges fun e => decide (c e = i))`, which is the expression
that the statement files write out (e.g. `EG.Spec.L15pStatement`), so no Spec depends on this
file.

Contents: `colourClass_verts`, `colourClass_card`, `colourClass_le`,
`colourClass_edges` (the edge set is `selectSet X.edges (c · = i)`), `mem_colourClass_edges`,
`coe_mem_colourClass_edges`, `colourClass_edges_subset`, `disjoint_colourClass_edges`
(distinct classes are edge-disjoint), `exists_mem_colourClass_edges` (every edge of `X` has a
class), and the law of a class of the uniform colouring, `map_colourClass_edges_randColouring`
(its edge set is a `(1/k)`-random subset of `E(X)`).
-/

public section


namespace EG

namespace FGraph

open Finset

variable {V κ : Type*} [DecidableEq V] [DecidableEq κ]

/-- [s3:lemL15p] "for `i ∈ [k]` let `X_i` be the graph with vertex set `V(X)` whose edges are the
edges of colour `i`": the colour class of `i` for a colouring `c : ↥E(X) → κ` of the edges of
`X`. -/
@[expose] def colourClass (X : FGraph V) (c : X.edges → κ) (i : κ) : FGraph V :=
  X.restrictEdges (FinDist.selectSet X.edges fun e => decide (c e = i))

/-- The unfolding of `colourClass` (the form written out in the statement files). -/
theorem colourClass_eq (X : FGraph V) (c : X.edges → κ) (i : κ) :
    X.colourClass c i = X.restrictEdges (FinDist.selectSet X.edges fun e => decide (c e = i)) :=
  rfl

@[simp] theorem colourClass_verts (X : FGraph V) (c : X.edges → κ) (i : κ) :
    (X.colourClass c i).verts = X.verts := rfl

@[simp] theorem colourClass_card (X : FGraph V) (c : X.edges → κ) (i : κ) :
    (X.colourClass c i).card = X.card := rfl

theorem colourClass_le (X : FGraph V) (c : X.edges → κ) (i : κ) : X.colourClass c i ≤ X :=
  restrictEdges_le _

/-- The edge set of the colour class of `i` is the set of edges of colour `i`. -/
theorem colourClass_edges (X : FGraph V) (c : X.edges → κ) (i : κ) :
    (X.colourClass c i).edges = FinDist.selectSet X.edges fun e => decide (c e = i) := by
  ext e
  rw [colourClass, mem_restrictEdges_edges]
  exact ⟨fun h => h.2, fun h => ⟨FinDist.selectSet_subset _ _ h, h⟩⟩

theorem mem_colourClass_edges {X : FGraph V} {c : X.edges → κ} {i : κ} {e : Sym2 V} :
    e ∈ (X.colourClass c i).edges ↔ ∃ h : e ∈ X.edges, c ⟨e, h⟩ = i := by
  rw [colourClass_edges, FinDist.mem_selectSet]
  simp only [decide_eq_true_iff]

/-- An edge `e ∈ E(X)` lies in the colour class of `i` iff it has colour `i`. -/
theorem coe_mem_colourClass_edges (X : FGraph V) (c : X.edges → κ) (i : κ) (e : X.edges) :
    (e : Sym2 V) ∈ (X.colourClass c i).edges ↔ c e = i := by
  rw [colourClass_edges, FinDist.mem_selectSet_coe, decide_eq_true_iff]

theorem colourClass_edges_subset (X : FGraph V) (c : X.edges → κ) (i : κ) :
    (X.colourClass c i).edges ⊆ X.edges :=
  fun _ he => (mem_colourClass_edges.1 he).1

/-- Distinct colour classes are edge-disjoint. -/
theorem disjoint_colourClass_edges (X : FGraph V) (c : X.edges → κ) {i j : κ} (hij : i ≠ j) :
    Disjoint (X.colourClass c i).edges (X.colourClass c j).edges := by
  rw [Finset.disjoint_left]
  intro e hi hj
  obtain ⟨he, hci⟩ := mem_colourClass_edges.1 hi
  obtain ⟨he', hcj⟩ := mem_colourClass_edges.1 hj
  exact hij (hci.symm.trans hcj)

/-- Every edge of `X` lies in the colour class of its colour. -/
theorem exists_mem_colourClass_edges (X : FGraph V) (c : X.edges → κ) {e : Sym2 V}
    (he : e ∈ X.edges) : ∃ i, e ∈ (X.colourClass c i).edges :=
  ⟨c ⟨e, he⟩, mem_colourClass_edges.2 ⟨he, rfl⟩⟩

/-- [s3:lemL15p] For the uniformly random `k`-colouring of `E(X)`, the edge set of the colour
class of `j` is a `(1/k)`-random subset of `E(X)` (`FinDist.map_selectSet_randColouring`). -/
theorem map_colourClass_edges_randColouring (X : FGraph V) {k : ℕ} [NeZero k] (j : Fin k)
    (h0 : (0 : ℝ) ≤ 1 / k) (h1 : (1 : ℝ) / k ≤ 1) :
    (FinDist.randColouring X.edges k).map (fun c => (X.colourClass c j).edges) =
      FinDist.rsubset X.edges (1 / k) h0 h1 := by
  simp only [colourClass_edges]
  exact FinDist.map_selectSet_randColouring X.edges j h0 h1

end FGraph

end EG
