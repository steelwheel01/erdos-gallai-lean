module

public import EG.Spec.Chain.JSLCSteps
public import EG.Lib.Chain.Lending
public import EG.Proof.HB.EL

/-!
# Proof of the Step 1 facts of Lemma JS-LC: types and T-avoidance (manuscript s6:lemJSLC, proof,
Step 1 and joint-routing claim (e))

Probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`). An assembly of the Lib
lemmas of `EG.Lib.Chain.{Design,Lending}` and of Lemma EL (`EG.edgeLaminarity`, unit P3A; a
declared-input stub when this file was written, proved since P3A's fix round 1), as in the manuscript: "Both ends lie in `Z^0`, since `E_l(Z) ⊆ E(G[Z^0])` by
(R5). Since `Z^0 = Ret_Z ⊔ Q*_Z` … `Y(v) ≠ Y(u)`: otherwise both ends of `e ∈ E(G_l)` would lie in
`V(Y(u))` with `l > r(Y(u))`, contrary to Lemma s2:lemEL. By the same lemma, for every edge
`hu ∈ E_l(Z)` with `u ∈ Q_Z` and `Y(u) = Y`, the vertex `h` lies outside `V(Y)`. In particular
`h ∉ T_j(Y,l)`, since `T_j(Y,l) ⊆ V(Y)`."
-/

public section

namespace EG

open EG.HB EG.Chain

/-- [s6:lemJSLC:proof-step-1] types and T-avoidance (Step 1, claim (e)). -/
theorem jslcTypes : EG.Spec.JslcTypesStatement := by
  intro V _ G Dstar run δ S l a hrun hδ hl ha
  -- the centre of a class-`Y` edge lies outside `V(Y)` (Lemma EL)
  have hcentre : ∀ u ∈ run.classed G l a, ∀ h : V, s(h, u) ∈ run.E G l a →
      h ∉ run.ancVerts G (δ l u) := by
    intro u hu h he hh
    have hY := hδ.mem_ancestors hl ha hu
    have hr := hδ.round_add_two_le hl ha hu
    have hG : s(h, u) ∈ (run.graph G l).edges :=
      (Round.graph'_le _ _).2 (Run.E_subset_graph'_edges run G l a he)
    exact EG.edgeLaminarity V G Dstar run hrun (δ l u) hY l (by omega) _ hG
      (Finset.mem_sym2_iff.2 fun x hx => by
        rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact hh
        · exact hδ.mem_ancVerts hl ha hu)
  refine ⟨fun u hu => ⟨mem_lendGoodAnc_of_mem_qs run G S hδ ha hu,
      lab_eq_none_of_mem_qs run G δ S hu,
      hδ.mem_ancVerts hl ha (qs_subset_classed run G δ S l a hu),
      notMem_Tj_of_mem_qs run G δ S hu⟩, ?_, ?_, ?_⟩
  · intro e he v hv
    have hZ : v ∈ run.Z0 G l a :=
      Run.partVerts_subset_Z0 run G l a (Run.mem_partVerts_of_mem_E run G he hv)
    rw [← ret_union_qs run G δ S l a] at hZ
    exact Finset.mem_union.1 hZ
  · intro u hu h he
    exact ⟨hcentre u hu h he, fun j hT => hcentre u hu h he (Finset.filter_subset _ _ hT)⟩
  · intro u hu v hv he hYY
    apply hcentre u hu v (by rwa [Sym2.eq_swap])
    rw [hYY]
    exact hδ.mem_ancVerts hl ha hv

end EG
