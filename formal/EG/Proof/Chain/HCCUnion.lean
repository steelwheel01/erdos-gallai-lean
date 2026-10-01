module

public import EG.Spec.Chain.HCCP
public import EG.Lib.Found.Fnum

/-!
# Proof of the first paragraph of the union lemma (manuscript s6:lemHCCglob)

`EG.hccUnion : EG.Spec.HccUnionStatement`: concatenating decompositions of pairwise disjoint edge
sets gives a decomposition of their union with the sum of the numbers of objects. This is the
iterated form of [s1:factAdd](b) (list form) already proved in `EG.Lib.Found.Fnum`
(`EG.isDecomp_finset_biUnion`, `EG.length_flatMap_toList`); the manuscript's `E_i ⊆ E(G)` is not
needed. Probe unit P2E, design note `formal/work/p2b/P2E.md`.
-/

public section

namespace EG

/-- [s6:lemHCCglob] (first paragraph) "Let `E_1, …, E_q ⊆ E(G)` be pairwise disjoint, and suppose
each `E_i` decomposes into `a_i` objects. Then `E_1 ∪ ⋯ ∪ E_q` decomposes into `∑_i a_i`
objects." -/
theorem hccUnion : EG.Spec.HccUnionStatement := by
  intro V _ G q E D _ hdisj hD
  refine ⟨Finset.univ.toList.flatMap D, ?_, ?_⟩
  · exact isDecomp_finset_biUnion Finset.univ
      (fun i _ j _ hij => hdisj i j hij) (fun i _ => hD i)
  · exact length_flatMap_toList Finset.univ D

end EG
