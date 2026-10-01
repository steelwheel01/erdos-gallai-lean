module

public import EG.Defs.Light.Constants
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# API for the constants of s5 (`EG.Light.epsU`, `EG.Light.epsChain`)

* `epsChain_eq_epsK` (`rfl`: one formula, TRIAGE G-S5-1), `epsU_eq`;
* `epsU_pos`, `epsU_nonneg` (for `D_* > 1`, resp. `≥ 1`);
* the limits: `tendsto_epsU` ([s5:lemExpect] "Moreover `ε_U(D_*) → 0` as `D_* → ∞`") and
  `tendsto_epsChain` ([s5:lemParent] "Moreover `ε_ch(D_*) → 0` as `D_* → ∞`"), used by
  s7:lemGammaSat. These are facts about the formulas (no run), proved here as API lemmas.
-/

public section

namespace EG.Light

open Filter Topology Real

theorem epsChain_eq_epsK (D : ℝ) : epsChain D = EG.Chain.epsK D := rfl

theorem epsU_eq (D : ℝ) : epsU D = 2462 * Real.logb 2 D ^ (-205 : ℤ) := rfl

theorem epsChain_eq (D : ℝ) :
    epsChain D = 614 / D + Real.logb 2 (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) *
      Real.logb 2 (Real.logb 2 D))) / (371 * Real.logb 2 (Real.logb 2 D) ^ 2) := rfl

theorem epsU_pos {D : ℝ} (hD : 1 < D) : 0 < epsU D := by
  have : 0 < Real.logb 2 D := Real.logb_pos (by norm_num) hD
  unfold epsU
  positivity

theorem epsU_nonneg {D : ℝ} (hD : 1 ≤ D) : 0 ≤ epsU D := by
  have : 0 ≤ Real.logb 2 D := Real.logb_nonneg (by norm_num) hD
  unfold epsU
  positivity

/-- [s5:lemExpect] "Finally, `ε_U(D_*) = 2462 (log₂ D_*)^{-205} → 0` as `D_* → ∞`." -/
theorem tendsto_epsU : Tendsto epsU atTop (𝓝 0) := by
  have h1 : Tendsto (fun D : ℝ => Real.logb 2 D) atTop atTop :=
    Real.tendsto_logb_atTop (b := 2) (by norm_num)
  have h2 : Tendsto (fun x : ℝ => x ^ (-205 : ℤ)) atTop (𝓝 0) :=
    tendsto_zpow_atTop_zero (by norm_num)
  have := (h2.comp h1).const_mul 2462
  rw [mul_zero] at this
  exact this

/-- `log₂ x ≤ 2x` for `x > 0` (from `log x ≤ x - 1` and `log 2 > 1/2`). -/
theorem logb_two_le_two_mul {x : ℝ} (hx : 0 < x) : Real.logb 2 x ≤ 2 * x := by
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- The second summand of `ε_ch` as a function of `y = log₂ log₂ D_*`:
`log₂(2A log₂(A y)) / (371 y^2) → 0` as `y → ∞`. -/
theorem tendsto_epsChain_aux :
    Tendsto (fun y : ℝ => Real.logb 2 (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * y)) /
      (371 * y ^ 2)) atTop (𝓝 0) := by
  have hA : (Aexp : ℝ) = 105 := by norm_num [Aexp]
  -- upper bound `8 A^2 / (371 y)`, lower bound `0`, for `y ≥ 1`
  have hup : Tendsto (fun y : ℝ => 8 * (Aexp : ℝ) ^ 2 / 371 * y⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.const_mul (8 * (Aexp : ℝ) ^ 2 / 371)
    rw [mul_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hAy : (1 : ℝ) ≤ (Aexp : ℝ) * y := by rw [hA]; nlinarith
    have hl1 : 0 ≤ Real.logb 2 ((Aexp : ℝ) * y) := Real.logb_nonneg (by norm_num) hAy
    -- `log₂(A y) ≥ log₂ 105 ≥ 1`, so `2A log₂(A y) ≥ 1`
    have hl2 : 1 ≤ Real.logb 2 ((Aexp : ℝ) * y) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
      rw [hA]; norm_num; nlinarith
    have h2 : 1 ≤ 2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * y) := by rw [hA] at hl2 ⊢; nlinarith
    exact div_nonneg (Real.logb_nonneg (by norm_num) h2) (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    have hAy : 0 < (Aexp : ℝ) * y := by rw [hA]; positivity
    have hl1 : Real.logb 2 ((Aexp : ℝ) * y) ≤ 2 * ((Aexp : ℝ) * y) := logb_two_le_two_mul hAy
    have hl0 : 1 ≤ (Aexp : ℝ) * y := by rw [hA]; nlinarith
    have hl1' : 1 ≤ Real.logb 2 ((Aexp : ℝ) * y) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hAy]
      rw [hA]; norm_num; nlinarith
    have hpos : 0 < 2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * y) :=
      mul_pos (by rw [hA]; norm_num) (by linarith)
    have hl2 : Real.logb 2 (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * y)) ≤
        2 * (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * y)) := logb_two_le_two_mul hpos
    have hA0 : (0 : ℝ) < Aexp := by rw [hA]; norm_num
    have hnum : Real.logb 2 (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * y)) ≤
        8 * (Aexp : ℝ) ^ 2 * y := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : 8 * (Aexp : ℝ) ^ 2 / 371 * y⁻¹ * (371 * y ^ 2) = 8 * (Aexp : ℝ) ^ 2 * y := by
      field_simp
    rw [this]
    exact hnum

/-- [s5:lemParent] "Finally `η(log₂ D_*) → 0` and `614/D_* → 0` as `D_* → ∞`, so
`ε_ch(D_*) → 0`." -/
theorem tendsto_epsChain : Tendsto epsChain atTop (𝓝 0) := by
  have h1 : Tendsto (fun D : ℝ => 614 / D) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlog : Tendsto (fun D : ℝ => Real.logb 2 D) atTop atTop :=
    Real.tendsto_logb_atTop (b := 2) (by norm_num)
  have hll : Tendsto (fun D : ℝ => Real.logb 2 (Real.logb 2 D)) atTop atTop := hlog.comp hlog
  have h2 := tendsto_epsChain_aux.comp hll
  have := h1.add h2
  rw [add_zero] at this
  exact this

end EG.Light
