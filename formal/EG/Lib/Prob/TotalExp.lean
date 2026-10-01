module

public import EG.Lib.Prob.Basic

/-!
# Comparison of expectations through a finite partition

If `E[X | π = b] ≤ E[Y | π = b]` for every value `b` of `π` of positive probability, then
`E[X] ≤ E[Y]` (the law of total expectation). Used for [s7:lemCC] (iii): "Averaging (ii) over the
indicators" (the bound of (ii) holds for every value pattern of the indicators).
-/

public section

namespace EG

namespace FinDist

open Finset

variable {Ω β : Type*} (μ : FinDist Ω)

/-- `E[X · 1_A] ≤ E[Y · 1_A]` whenever `E[X | A] ≤ E[Y | A]` (and trivially if `P(A) = 0`). -/
theorem expect_indicator_le_of_cond {A : Set Ω} {X Y : Ω → ℝ}
    (h : ∀ hA : 0 < μ.prob A, (μ.cond A hA).expect X ≤ (μ.cond A hA).expect Y) :
    μ.expect (A.indicator X) ≤ μ.expect (A.indicator Y) := by
  rcases (μ.prob_nonneg A).eq_or_lt with h0 | hA
  · have hw := (μ.prob_eq_zero_iff A).1 h0.symm
    have hz : ∀ Z : Ω → ℝ, μ.expect (A.indicator Z) = 0 := by
      intro Z
      unfold expect
      refine sum_eq_zero fun ω _ => ?_
      by_cases hω : ω ∈ A
      · rw [hw ω hω, zero_mul]
      · rw [Set.indicator_of_notMem hω, mul_zero]
    rw [hz, hz]
  · have := h hA
    rw [expect_cond, expect_cond] at this
    exact (div_le_div_iff_of_pos_right hA).1 this

/-- The law of total expectation, as a comparison: if `E[X | π = b] ≤ E[Y | π = b]` for every `b`
with `P(π = b) > 0`, then `E[X] ≤ E[Y]`. -/
theorem expect_le_of_cond_le [DecidableEq β] (π : Ω → β) {X Y : Ω → ℝ}
    (h : ∀ b (hb : 0 < μ.prob (π ⁻¹' {b})),
      (μ.cond (π ⁻¹' {b}) hb).expect X ≤ (μ.cond (π ⁻¹' {b}) hb).expect Y) :
    μ.expect X ≤ μ.expect Y := by
  have hdec : ∀ Z : Ω → ℝ, μ.expect Z =
      ∑ b ∈ μ.supp.image π, μ.expect ((π ⁻¹' {b}).indicator Z) := by
    intro Z
    rw [← expect_sum]
    refine expect_congr _ fun ω hω => ?_
    have hmem : π ω ∈ μ.supp.image π := mem_image_of_mem π ((μ.mem_supp_iff_pos).2 hω)
    rw [sum_eq_single (π ω)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro b _ hb
      rw [Set.indicator_of_notMem]
      simpa [eq_comm] using hb
    · intro h'; exact absurd hmem h'
  rw [hdec X, hdec Y]
  exact sum_le_sum fun b _ => μ.expect_indicator_le_of_cond (h b)

end FinDist

end EG
