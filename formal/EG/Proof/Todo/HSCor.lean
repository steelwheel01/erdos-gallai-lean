module

public import EG.Spec.HB.HS
public import EG.Lib.HB.HS

/-!
# P3 stub: `EG.Spec.HSCorStatement` (s2:lemHS)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.HSCor`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemHS] see `EG.Spec.HSCorStatement`. -/
theorem HSCor : EG.Spec.HSCorStatement := by
  intro V _ X W s hs hz hX hW hWc hdeg
  refine ⟨X.deleteVerts_verts W, ?_⟩
  have h := EG.HB.hs_expander X W _ s (s / 2) hz hX hW hWc hdeg
  have hz11 : (11 : ℝ) ≤ X.card := by exact_mod_cast hz
  have hr := EG.HB.hs_ratio hz11 (z' := (X.card : ℝ) - W.card) (by linarith)
  refine h.mono ?_ (by linarith)
  have : ((2 : ℝ) ^ (-6 : ℤ)) = (2 : ℝ) ^ (-5 : ℤ) * (1 / 2) := by norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_left hr (by positivity)

end EG.Todo
