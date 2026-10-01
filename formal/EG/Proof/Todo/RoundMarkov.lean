module

public import EG.Spec.Quot.RoundStep
public import EG.Lib.Prob.Basic

/-!
# P3 stub: `EG.Spec.RoundMarkovStatement` (s7:consRound)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RoundMarkov`; consumers import this module.

Proof: Markov's inequality (Cited result s1:citMarkov (b), `EG.FinDist.prob_gt_mul_expect_le`,
`EG.FinDist.half_le_prob_le_four_mul_expect_and`) for the non-negative variables `copies_l` and
`pay^rd_l` under the round law.
-/

public section

namespace EG.Todo

open EG.Quot EG.FinDist

/-- Proved in P3. [s7:consRound] see `EG.Spec.RoundMarkovStatement`. -/
theorem RoundMarkov : EG.Spec.RoundMarkovStatement := by
  intro V _ I _ R _
  have h1 : ∀ ξ, (0 : ℝ) ≤ (R.copies ξ : ℝ) := fun _ => Nat.cast_nonneg _
  have h2 : ∀ ξ, (0 : ℝ) ≤ (R.payrd ξ : ℝ) := fun _ => Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · have := (roundLaw I.G I.M).prob_gt_mul_expect_le h1 (c := 4) (by norm_num)
    simpa only [not_le] using this
  · have := (roundLaw I.G I.M).prob_gt_mul_expect_le h2 (c := 4) (by norm_num)
    simpa only [not_le] using this
  · exact (roundLaw I.G I.M).half_le_prob_le_four_mul_expect_and h1 h2

end EG.Todo
