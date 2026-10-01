module

public import EG.Spec.HB.HBtpFacts

/-!
# P3 stub: `EG.Spec.HBStdStatement` (s2:defHBtp)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.HBStd`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:defHBtp] see `EG.Spec.HBStdStatement`. -/
theorem HBStd : EG.Spec.HBStdStatement := by
  classical
  intro V _ H c a ha h
  unfold EG.HB.Round.Std
  rw [Finset.mem_filter]
  refine ⟨ha, fun hl => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hl
  rcases h with h | h | h
  · exact h.2.2 h3
  · exact h h1
  · exact h h2

end EG.Todo
