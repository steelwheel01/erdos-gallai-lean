module

public import EG.Spec.HB.Exists
public import EG.Lib.HB.Exists

/-!
# P3 stub: `EG.Spec.RoundStepsStatement` (s2:propExists)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RoundSteps`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propExists] see `EG.Spec.RoundStepsStatement`. -/
theorem RoundSteps : EG.Spec.RoundStepsStatement := by
  intro V _
  refine ⟨fun H => EG.HB.Round.exists_cyclesValid H, fun K W hW => ?_⟩
  obtain ⟨h1, h2, h3⟩ := EG.HB.STree.s0Build_spec W hW K.card [] K le_rfl
  refine ⟨_, h1, h2, fun a ha => ?_⟩
  simpa using h3 a ha

end EG.Todo
