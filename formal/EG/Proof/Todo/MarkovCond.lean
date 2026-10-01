module

public import EG.Spec.Found.Markov
public import EG.Lib.Prob.Basic

/-!
# P3 stub: `EG.Spec.MarkovCondStatement` (s1:citMarkov)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.MarkovCond`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:citMarkov] Proved in P3. See `EG.Spec.MarkovCondStatement`. -/
theorem MarkovCond : EG.Spec.MarkovCondStatement := fun _ P A hA _ _ _ hX hX₁ hX₂ =>
  ⟨(P.cond A hA).two_thirds_le_prob_le_three_mul_expect hX,
    (P.cond A hA).half_le_prob_le_four_mul_expect_and hX₁ hX₂⟩

end EG.Todo
