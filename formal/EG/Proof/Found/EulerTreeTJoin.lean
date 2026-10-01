module

public import EG.Spec.Found.EulerTreeTJoin
public import EG.Lib.Chain.ParTJoin

/-!
# Cited result s1:citEuler (a): T-joins in spanning trees

Formerly the stub of the declared input `[s1:citEuler]` (a) of probe P2E (design note
`formal/work/p2b/P2E.md`). Proved in P3 (unit P3-s1) from the Lib theorem `EG.exists_tJoin`
(`EG/Lib/Chain/ParTJoin.lean`: a `T`-join inside any edge set whose components each contain an
even number of vertices of `T`, built as a symmetric difference of paths), applied to the edge
set `S` of the spanning tree: `S` is connected on `V(H)`, so the one component meeting `V(H)`
contains all of `T`, and the vertices outside `V(H)` are isolated in `S`.
-/

public section

namespace EG

/-- [s1:citEuler] (a) "Let `H` be a connected graph and `T ⊆ V(H)` with `|T|`
even. Every spanning tree `S` of `H` contains a `T`-join, i.e. a set `J ⊆ E(S)` such that the
vertices of odd `J`-degree are exactly the vertices of `T`." Proved in P3 (`EG.exists_tJoin`;
acyclicity of `S` is not needed). -/
theorem eulerTreeTJoin : EG.Spec.EulerTreeTJoinStatement := by
  intro V _ H T _ hT hTe S hS hSconn _
  classical
  refine exists_tJoin S T.card T rfl fun z => ?_
  by_cases hz : z ∈ H.verts
  · have hall : T.filter (fun t => (edgeGraph S).Reachable z t) = T := by
      apply Finset.filter_true_of_mem
      intro t ht
      refine (hSconn z hz t (hT ht)).mono ?_
      intro u v huv
      rw [edgeGraph_adj]
      exact ⟨(Finset.mem_filter.1 (show s(u, v) ∈ (H.restrictEdges S).edges from huv)).2,
        huv.ne⟩
    rw [hall]
    exact hTe
  · have hnone : T.filter (fun t => (edgeGraph S).Reachable z t) = ∅ := by
      apply Finset.filter_false_of_mem
      intro t ht hr
      obtain ⟨w⟩ := hr
      cases w with
      | nil => exact hz (hT ht)
      | cons h _ =>
        rw [edgeGraph_adj] at h
        exact hz (H.edge_verts _ (hS h.1) z (Sym2.mem_mk_left _ _))
    rw [hnone]
    simp

end EG
