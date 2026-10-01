module

public import EG.Defs.Quot.Constants
public import EG.Lib.Light.Constants
public import EG.Lib.Chain.Constants

/-!
# Non-negativity of the small functions `ε_X`, `ε_K`, `ε_1`, `ε_2` (manuscript s7:thmMainProof)

The proof of Corollary [s7:thmMainProof] uses "`C_0 ≥ D_*/2`, since `ε_1 ≥ 0`; and
`0 ≤ θ_Q ≤ 1/4 < 1/2`". Proof of [s7:lemGammaSat] (ii): "`ε_1` and `ε_2` are finite sums of
non-negative explicit functions of `D_*`". Here: every summand is non-negative for `D_* ≥ 4`.
-/

public section

namespace EG.Quot

open Real

theorem epsX_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ epsX D := by
  have h1 := Light.epsU_nonneg (D := D) (by linarith)
  have h2 := Chain.two_le_logb_of_four_le hD
  have hD0 : 0 < D := by linarith
  unfold epsX
  have : 0 ≤ 6 * logb 2 D + 12 := by linarith
  positivity

theorem epsK_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ Chain.epsK D := by
  have hL := Chain.one_le_logb_logb_of_four_le hD
  have hD0 : 0 < D := by linarith
  set L := logb 2 (logb 2 D) with hLdef
  have hA : (1 : ℝ) ≤ (Aexp : ℝ) * L := by
    have : (1 : ℝ) ≤ (Aexp : ℝ) := by norm_num [Aexp]
    nlinarith
  have hlogA : 0 ≤ logb 2 ((Aexp : ℝ) * L) := Real.logb_nonneg (by norm_num) hA
  have hnum : 0 ≤ logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * L)) := by
    -- `A L ≥ 105 ≥ 2`, so `log₂(A L) ≥ 1` and the argument is `≥ 210 ≥ 1`
    have hAL : (2 : ℝ) ≤ (Aexp : ℝ) * L := by
      have : (2 : ℝ) ≤ (Aexp : ℝ) := by norm_num [Aexp]
      nlinarith
    have h1 : (1 : ℝ) ≤ logb 2 ((Aexp : ℝ) * L) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
      simpa using hAL
    apply Real.logb_nonneg (by norm_num)
    have : (1 : ℝ) ≤ 2 * (Aexp : ℝ) := by norm_num [Aexp]
    nlinarith
  unfold Chain.epsK
  rw [← hLdef]
  have : 0 < 371 * L ^ 2 := by positivity
  positivity

theorem eps1_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ eps1 D := by
  have h1 := epsK_nonneg hD
  have h2 := Chain.epsA_nonneg hD
  have h3 := Chain.epsCONC_nonneg hD
  have h4 := epsX_nonneg hD
  have hD0 : 0 < D := by linarith
  unfold eps1
  positivity

theorem FQ_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ FQ x := by
  have h1 : 0 ≤ logb 2 x := Real.logb_nonneg (by norm_num) hx
  have h2 : 0 ≤ x ^ (-(90.2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  unfold FQ
  have : 0 ≤ 3184 + 30400 * logb 2 x := by linarith
  positivity

theorem eps2_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ eps2 D := by
  have h1 := epsX_nonneg hD
  have h2 := Chain.epsA_nonneg hD
  have h3 := FQ_nonneg (x := logb 2 D) (by linarith [Chain.two_le_logb_of_four_le hD])
  have hD0 : 0 < D := by linarith
  unfold eps2
  positivity

theorem thetaQ_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ thetaQ D := eps2_nonneg hD

/-- [s7:thmMainProof] "`C_0 ≥ D_*/2`, since `ε_1 ≥ 0`". -/
theorem half_le_C0 {D : ℝ} (hD : 4 ≤ D) : D / 2 ≤ C0 D := by
  have := eps1_nonneg hD
  unfold C0
  linarith

end EG.Quot
