module

public import EG.Spec.Quot.CandDef
public import EG.Lib.Quot.Cand
public import EG.Lib.Chain.Design
public import EG.Lib.HB.Run

/-!
# P3 stub: `EG.Spec.CandSubsetStatement` (s7:defCand)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CandSubset`; consumers import this module.

Proof: the class facts are those of the designation (`EG.Chain.IsDesignation.*`, s6:defDesign);
`Cand_l(u) ⊆ N_{H_Y}(u)` because `LJV_{Y,l}` is a class of the colouring of `H_Y`, i.e. a set of
edges of `H_Y` (`Stage1.lentClass` restricts the edges of `run.ancGraph G Y`); and
`N_{H_Y}(u) ⊆ V(H_Y) = V(Y)` (`EG.HB.Run.ancGraph_verts`).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- Proved in P3. [s7:defCand] see `EG.Spec.CandSubsetStatement`. -/
theorem CandSubset : EG.Spec.CandSubsetStatement := by
  intro V _ N0 Dstar G run δ _ hδ Sω hS l u hl hu
  obtain ⟨a, ha, hua⟩ := (Chain.mem_classedPorts run G).1 hu
  refine ⟨hδ.mem_ancestors hl ha hua, hδ.one_le_round hl ha hua, hδ.round_add_two_le hl ha hua,
    hδ.mem_ancVerts hl ha hua, fun ω => ⟨?_, ?_⟩⟩
  · -- "`LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)`", so `Cand_l(u) ⊆ N_{H_Y}(u)`
    intro w hw
    have h1 := (Quot.mem_cand.1 hw).2
    rw [hS] at h1
    have he : s(u, w) ∈ (run.ancGraph G (δ l u)).edges := (Finset.mem_filter.1 h1).1
    rw [FGraph.nbrs, Finset.mem_filter]
    exact ⟨(run.ancGraph G (δ l u)).edge_verts _ he w (Sym2.mem_mk_right u w), he⟩
  · -- "`H_Y` is a graph on `V(Y)`", so `N_{H_Y}(u) ⊆ V(Y)`
    intro w hw
    rw [← Run.ancGraph_verts]
    exact (Finset.mem_filter.1 hw).1

end EG.Todo
