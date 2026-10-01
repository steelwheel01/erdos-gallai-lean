module

public import EG.Spec.Num.OV
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Numeric facts of Lemma OV, Lemma 14^τ(b) and Proposition OV (manuscript s2)

Proofs of the statements of `EG/Spec/Num/OV.lean`.

Stage 1 (this file): `numOVLogFourThirds` (`log₂(4/3) ≥ 17/41` from `2^{65} ≥ 3^{41}`),
`numOVConst`, `numLem14tauConst`, `numPropOVConst`.
Fix round 1 (review I-2, I-4): `numOVChargeSum` (the sum–integral comparison, proved by
telescoping: `1/(x+jc)^2 ≤ (1/c)(1/(x+(j−1)c) − 1/(x+jc))` for `j ≥ 1`), `numOVRearrange`,
`numOVInstance` (`(1+ε)(2/3) = 0.6875 < 0.75`, slack 8%).

Recorded slacks (exact values; `c_OV = 0.4150374…`): `1 + 1/c_OV = 3.4094208…` vs `3.42`
(0.31%); through `17/41`: `1 + 41/17 = 3.41176…`; `1.6(1 + 1/c_OV) = 5.4550733…` vs `5.46`
(0.09%); through `17/41`: `1.6·58/17 = 5.45882…` (0.02%); `1/(1 − 3.42/32) = 1.11966…` vs
`1.12` (0.03%); `1/(1 − 5.5/32) = 1.20754…` vs `1.21` (0.2%); `5.46·1.21 = 6.6066` vs `6.61`
(0.05%); `3^{41} = 3.6472…·10^{19}` vs `2^{65} = 3.6893…·10^{19}` (1.2%).
-/

public section


namespace EG

open Real

/-- [s2:lemOVgeneric] (helper) `log₂(4/3) ≥ 17/41`, from `3^{41} ≤ 2^{65}`. -/
theorem numOVLogFourThirds : EG.Spec.NumOVLogFourThirdsStatement := by
  refine ⟨?_, by norm_num⟩
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((17 : ℝ) / 41) := by positivity
  rw [← pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num : (41 : ℕ) ≠ 0)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `1/log₂(4/3) ≤ 41/17`. -/
theorem inv_logb_four_thirds_le : 1 / Real.logb 2 (4 / 3) ≤ 41 / 17 := by
  have h := numOVLogFourThirds.1
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- [s2:lemOVgeneric] `1 + 1/c_OV ≤ 3.42`, the second inequality of (a), `3.42ε < 1`,
`1/(1 − 3.42ε) ≤ 1.12`. -/
theorem numOVConst : EG.Spec.NumOVConstStatement := by
  have hc := inv_logb_four_thirds_le
  have hc0 : 0 < 1 / Real.logb 2 (4 / 3) := by
    have := numOVLogFourThirds.1
    positivity
  refine ⟨by linarith, ?_, by unfold epsC; norm_num, by unfold epsC; norm_num⟩
  intro c M hc0' hM
  have hL : 1 ≤ Real.logb 2 M := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using hM
  have hL0 : 0 < Real.logb 2 M := by linarith
  have he : 0 < epsC := by unfold epsC; positivity
  have h1 : 1 / Real.logb 2 M ^ 2 ≤ 1 / Real.logb 2 M := by
    apply one_div_le_one_div_of_le hL0
    nlinarith
  have h2 : 1 / (Real.logb 2 (4 / 3) * Real.logb 2 M) =
      (1 / Real.logb 2 (4 / 3)) * (1 / Real.logb 2 M) := by
    rw [one_div_mul_one_div]
  rw [h2]
  have h3 : 1 / Real.logb 2 M ^ 2 + 1 / Real.logb 2 (4 / 3) * (1 / Real.logb 2 M) ≤
      3.42 * (1 / Real.logb 2 M) := by
    have hpos : 0 < 1 / Real.logb 2 M := by positivity
    nlinarith
  have hce : 0 < c * epsC := by positivity
  calc c * epsC * (1 / Real.logb 2 M ^ 2 + 1 / Real.logb 2 (4 / 3) * (1 / Real.logb 2 M))
      ≤ c * epsC * (3.42 * (1 / Real.logb 2 M)) := mul_le_mul_of_nonneg_left h3 hce.le
    _ = 3.42 * c * epsC / Real.logb 2 M := by ring

/-- [s2:lem14tau] (b) The constants of the proof of (b), including
`1.6(1 + 1/c_OV) ≤ 5.46`. -/
theorem numLem14tauConst : EG.Spec.NumLem14tauConstStatement := by
  have hc := inv_logb_four_thirds_le
  refine ⟨by norm_num, by norm_num, by norm_num, by unfold epsC; norm_num, by norm_num,
    by norm_num, by unfold epsC; norm_num, by unfold epsC; norm_num, by linarith⟩

/-- [s2:propOV] The constants `6.61`, `7.6`, `1.37`, `15.2`, `30.4`, `13.3`, `16`. -/
theorem numPropOVConst : EG.Spec.NumPropOVConstStatement := by
  unfold EG.Spec.NumPropOVConstStatement
  norm_num


/-- Telescoping form of the charge sum: `∑_{j≤k} 1/(x+jc)^2 ≤ 1/x^2 + 1/(cx) − 1/(c(x+kc))`. -/
private theorem chargeSum_telescope {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), 1 / (x + j * c) ^ 2 ≤
      1 / x ^ 2 + 1 / (c * x) - 1 / (c * (x + k * c)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 < x + k * c := by positivity
    have hb : x + ((k + 1 : ℕ) : ℝ) * c = (x + k * c) + c := by push_cast; ring
    rw [hb]
    have hb0 : 0 < (x + k * c) + c := by linarith
    have hstep : 1 / ((x + k * c) + c) ^ 2 ≤
        1 / (c * (x + k * c)) - 1 / (c * ((x + k * c) + c)) := by
      have hid : 1 / (c * (x + k * c)) - 1 / (c * ((x + k * c) + c)) =
          1 / ((x + k * c) * ((x + k * c) + c)) := by
        field_simp; ring
      rw [hid]
      apply one_div_le_one_div_of_le (by positivity)
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) hb0.le
    linarith

/-- [s2:lemOVgeneric] (a) "`∑_{j≥0} 1/(log M + jc_OV)^2 ≤ 1/log^2M + 1/(c_OV log M)`" (every
finite partial sum). -/
theorem numOVChargeSum : EG.Spec.NumOVChargeSumStatement := by
  intro x c hx hc k
  cases k with
  | zero => simp; positivity
  | succ k =>
    have h := chargeSum_telescope hx hc k
    have : 0 < 1 / (c * (x + k * c)) := by positivity
    linarith

/-- [s2:lemOVgeneric] (c) "Rearranging gives (c)": `S ≤ n_0 + 3.42cεS` implies
`S ≤ n_0/(1−3.42cε)` when `3.42cε < 1`. -/
theorem numOVRearrange : EG.Spec.NumOVRearrangeStatement := by
  intro c S n₀ hc h1 hS
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- [s2:lemOVgeneric] instance `c = 1`: `(1+ε)(2/3) < 3/4`. -/
theorem numOVInstance : EG.Spec.NumOVInstanceStatement := by
  unfold EG.Spec.NumOVInstanceStatement epsC
  norm_num

end EG
