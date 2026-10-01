module

public import EG.Spec.Chain.JPlus
public import EG.Lib.Chain.JSet
public import EG.Proof.HB.StructureHY

/-!
# Proof of the `J`-independent items of Lemma J⁺ (manuscript s6:lemJplus (J3), (i), (iii), (iv))

Probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`). An assembly of the Lib
lemmas of `EG.Lib.Chain.{Design,Lending,JSet}` ((J3), exclusivity, (iv)) and of `EG.structureHY`
(s2:propStructure (iii), for (iii); proved in fix round 1), as in the manuscript's proof: "(J3):
`A_Z ⊆ D_l`, while `F_Z` and `Q*_Z` are disjoint subsets of `U_Z = Z^0 \ D_l` … (iii) is Proposition
s2:propStructure(iii). (iv) holds because `Y(u) ∈ anc_l(u)` … These cases are exclusive because
`A_Z`, `F_Z`, `Lost_Z` and `Q*_Z` are pairwise disjoint".
-/

public section

namespace EG

open EG.HB EG.Chain

/-- [s6:lemJplus] (J3), (i) (exclusive), (iii), (iv). -/
theorem jplusFacts : EG.Spec.JplusFactsStatement := by
  intro V _ G Dstar run δ S hrun hδ
  obtain ⟨hHY, -, hEdisj, -⟩ := EG.structureHY V G Dstar run hrun
  refine ⟨fun l => ⟨disjoint_D_freshCentres run G l, disjoint_D_qsRound run G δ S l,
      disjoint_freshCentres_qsRound run G δ S l,
      fun v hv a ha b hb hva hvb => eq_of_mem_Z0_of_notMem_D run G ha hb hva hvb hv⟩,
    fun l e => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hHY, hEdisj,
    fun l hl a ha u hu => hδ.mem_ancVerts hl ha hu⟩
  · rintro ⟨hp, h, Y, hh⟩; exact IsJparEdge.not_isJhubEdge hp hh
  · rintro ⟨hp, x, Y, hx⟩; exact IsJparEdge.not_isJfrEdge hp hx
  · rintro ⟨hp, w, Y, hw⟩; exact IsJparEdge.not_isJlostEdge hp hw
  · rintro ⟨⟨h, Y, hh⟩, x, Y', hx⟩; exact IsJhubEdge.not_isJfrEdge hh hx
  · rintro ⟨⟨h, Y, hh⟩, w, Y', hw⟩; exact IsJhubEdge.not_isJlostEdge hh hw
  · rintro ⟨⟨x, Y, hx⟩, w, Y', hw⟩; exact IsJfrEdge.not_isJlostEdge hx hw

end EG
