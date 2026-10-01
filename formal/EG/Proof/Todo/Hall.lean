module

public import EG.Spec.Found.Hall
public import Mathlib.Combinatorics.Hall.Basic

/-!
# P3 stub: `EG.Spec.HallStatement` (s1:citHall)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.Hall`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:citHall] Proved in P3 (Mathlib's Hall theorem). See `EG.Spec.HallStatement`. -/
theorem Hall : EG.Spec.HallStatement := by
  intro ι α _ J T hJ
  classical
  refine (Finset.all_card_le_biUnion_card_iff_exists_injective (fun a : J => T a)).1 ?_
  intro s
  have h := hJ (s.map (Function.Embedding.subtype _)) (by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
    exact a.2)
  rw [Finset.card_map] at h
  refine h.trans (le_of_eq (congrArg Finset.card ?_))
  ext y
  simp [Finset.mem_biUnion]

end EG.Todo
