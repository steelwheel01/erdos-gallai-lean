module

public import EG.Defs.Light.Stages

/-!
# `Pl(Z)` is the set of parentless pairs (s5:defStages, used for s5:eqPl)

Library of the P3-s5 unit (`formal/work/p3/s5.md`). Manuscript v6.1, `s5.tex`, Definition
[s5:defStages]: "A pair `(v, Z)` with `Z` a light part of round `l` and `v ∈ Pl(Z)` is exactly a
pair that is parentless with respect to the set `Bad` in the sense of Proposition
s2:propParentless(iii): no light part outside `Bad` of a round `≤ l−2` contains `v`."
-/

public section

namespace EG.Light

open EG.HB EG.Stage1

open Classical in
/-- [s5:defStages] `Pl(Z)` is the set of `v ∈ V(Z)` such that `(v, Z)` is parentless with respect
to `Bad ω` (the filter of s2:propParentless (iii), `EG.Spec.ParentlessCountStatement`). -/
theorem Pl_eq_parentless {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}
    (ω : Outcome G run) (Z : PartId) :
    Pl ω Z = (run.ancVerts G Z).filter (fun v =>
      ¬ ∃ Y ∈ run.lightParts G, Y ∉ Bad ω ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.ancVerts G Y) := by
  ext v
  rw [Pl, Finset.mem_sdiff, Finset.mem_filter, Rt, Finset.mem_filter]
  have h1 : ∀ Y, Y ∈ goodParents ω Z.1 ↔ Y ∈ run.lightParts G ∧
      (Y ∈ run.lightParts G ∧ ¬ demoted ω Y ∧ ¬ parentBad ω Y) ∧ Y.1 + 2 ≤ Z.1 := by
    intro Y; rw [goodParents, Finset.mem_filter]; rfl
  have h2 : ∀ Y, Y ∈ Bad ω ↔ Y ∈ run.lightParts G ∧ (demoted ω Y ∨ parentBad ω Y) := by
    intro Y; rw [Bad, Finset.mem_filter]
  simp only [h1, h2]
  constructor
  · rintro ⟨hv, hn⟩
    refine ⟨hv, fun ⟨Y, hY, hYB, hr, hvY⟩ => hn ⟨hv, Y, ⟨hY, ⟨hY, ?_⟩, hr⟩, hvY⟩⟩
    exact ⟨fun h => hYB ⟨hY, Or.inl h⟩, fun h => hYB ⟨hY, Or.inr h⟩⟩
  · rintro ⟨hv, hn⟩
    refine ⟨hv, fun ⟨_, Y, ⟨hY, ⟨_, hd⟩, hr⟩, hvY⟩ =>
      hn ⟨Y, hY, fun h => h.2.elim hd.1 hd.2, hr, hvY⟩⟩

end EG.Light
