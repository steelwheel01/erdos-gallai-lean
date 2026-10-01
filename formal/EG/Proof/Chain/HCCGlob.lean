module

public import EG.Proof.Chain.HCCP
public import EG.Lib.Found.Fnum

/-!
# Proof of the union lemma, second paragraph (manuscript s6:lemHCCglob)

`EG.hccGlob : EG.Spec.HccGlobStatement`: apply Lemma HCC-P (`EG.hccp`) to each system separately
and concatenate the decompositions ([s1:factAdd](b), list form `EG.isDecomp_finset_biUnion`). The
edge sets `B(𝒮_s) ∪ ⋃_j F_{s,j}` are pairwise disjoint because `F_{s,j} ⊆ E(𝒫_{s,j})` and the
beads and path edges of distinct systems are disjoint (the input-level hypothesis, CONVENTIONS
T0 row `T0-glob-input`). Probe unit P2E (probe P-2, part 1), proof round 1.
-/

public section

namespace EG

open EG.Chain

/-- [s6:lemHCCglob] (second paragraph) "In particular, suppose several systems satisfy the
hypotheses of Lemma HCC-P separately, each with its own layers, junction sets and path families,
and the edge sets they decompose (their beads together with their sets `F_j`) are pairwise
disjoint. Then the union of these edge sets decomposes into at most the sum of their values `Φ`.
... For the second statement, apply Lemma HCC-P to each system separately." -/
theorem hccGlob : EG.Spec.HccGlobStatement := by
  intro V _ G q S hS hdisj
  choose Φ hΦ F hF D hD hDlen hDcyc using fun s => hccp V G (S s) (hS s)
  refine ⟨Φ, fun s j => (hΦ s j).1, F, hF, Finset.univ.toList.flatMap D, ?_, ?_, ?_⟩
  · refine isDecomp_finset_biUnion Finset.univ ?_ (fun s _ => hD s)
    intro s _ s' _ hne
    have hsub : ∀ s, (S s).beads ∪ Finset.univ.biUnion (F s) ⊆
        (S s).beads ∪ (S s).allPathEdges := by
      intro s e he
      rcases Finset.mem_union.1 he with he | he
      · exact Finset.mem_union_left _ he
      · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 he
        exact Finset.mem_union_right _ ((S s).mem_allPathEdges.2 ⟨j, (hF s j).1 hj⟩)
    exact Finset.disjoint_of_subset_left (hsub s)
      (Finset.disjoint_of_subset_right (hsub s') (hdisj s s' hne))
  · rw [length_flatMap_toList]
    exact Finset.sum_le_sum fun s _ => hDlen s
  · intro o ho
    obtain ⟨s, -, hos⟩ := List.mem_flatMap.1 ho
    obtain ⟨c, rfl, -, hc⟩ := hDcyc s o hos
    exact ⟨c, rfl, hc⟩

end EG
