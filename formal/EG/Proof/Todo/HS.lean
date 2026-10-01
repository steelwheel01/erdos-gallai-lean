module

public import EG.Spec.HB.HS
public import EG.Lib.HB.HS

/-!
# P3 stub: `EG.Spec.HSStatement` (s2:lemHS)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.HS`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemHS] see `EG.Spec.HSStatement`. -/
theorem HS : EG.Spec.HSStatement := by
  intro V _ X W ε' s sW hε _ hz hX hW hWc _ hdeg
  refine ⟨?_, EG.HB.hs_expander X W ε' s sW hz hX hW hWc hdeg, ?_⟩
  · rw [EG.FGraph.card_def, EG.FGraph.deleteVerts_verts, Finset.card_sdiff_of_subset hW,
      EG.FGraph.card_def]
  · have hz11 : (11 : ℝ) ≤ X.card := by exact_mod_cast hz
    have h := EG.HB.hs_ratio hz11 (z' := (X.card : ℝ) - W.card) (by linarith)
    nlinarith

end EG.Todo
