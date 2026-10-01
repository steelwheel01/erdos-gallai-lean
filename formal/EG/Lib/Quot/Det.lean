module

public import EG.Defs.Quot.Constants
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The deterministic quotient terms `det_l` (manuscript s7:lemUHsplit (iv))

Real-arithmetic helpers for `EG.Spec.UHsplitDetStatement`:
* `FQ_eq_comb`: `F(x) = 624 x^{-90.2} + 320 (95 log₂x + 8) x^{-90.2}` (the two functions of
  Lemma s2:lemLacunary (iv) with `a = b = 90.2`);
* `det_tail_le`: "`78 nM_l/Hcd_l = 624 nM_l^3/λ^{95}`, `log₂θ^ult_l ≤ 95 log₂λ`, and with
  `M_l ≤ λ^{1.6}` these terms are at most `nF(λ)`";
* `two_FQ_lt`: "`2F(log₂D_*) < 2^{-1000}`" for `log₂D_* ≥ 2^{256}` (the manuscript goes through
  `F(2^{25})`; here the crude bound `3184 + 30400 log₂x ≤ 2^{16}x` and `x^{-89.2} ≤ x^{-4}` is used).
-/

public section

namespace EG.Quot

open Real

theorem FQ_eq_comb (x : ℝ) :
    FQ x = 624 * x ^ (-(90.2 : ℝ)) + 320 * ((95 * logb 2 x + 8) * x ^ (-(90.2 : ℝ))) := by
  unfold FQ; ring

/-- `log₂ x ≤ 2(x − 1)` for `x ≥ 1`. -/
theorem logb_two_le (x : ℝ) (hx : 1 ≤ x) : logb 2 x ≤ 2 * (x - 1) := by
  have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
  have hln2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this ⊢; linarith
  rw [logb, div_le_iff₀ (Real.log_pos (by norm_num))]
  have : 0 ≤ x - 1 := by linarith
  nlinarith

/-- "`2F(log₂D_*) < 2^{-1000}`", for `x ≥ 2^{256}`. -/
theorem two_FQ_lt {x : ℝ} (hx : (2 : ℝ) ^ 256 ≤ x) : 2 * FQ x < (2 : ℝ) ^ (-(1000 : ℤ)) := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 < x := by linarith
  have hlog := logb_two_le x hx1
  have hlog0 : 0 ≤ logb 2 x := logb_nonneg (by norm_num) hx1
  -- `3184 + 30400 log₂x ≤ 2^{16} x`
  have h1 : 3184 + 30400 * logb 2 x ≤ (2 : ℝ) ^ 16 * x := by nlinarith
  -- `x · x^{-90.2} ≤ x^{-4} ≤ 2^{-1024}`
  have h2 : x * x ^ (-(90.2 : ℝ)) ≤ x ^ (-(4 : ℝ)) := by
    have e : x * x ^ (-(90.2 : ℝ)) = x ^ (-(89.2 : ℝ)) := by
      rw [show (-(89.2 : ℝ)) = 1 + (-(90.2 : ℝ)) by norm_num, Real.rpow_add hx0, Real.rpow_one]
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h3 : x ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(1024 : ℤ)) := by
    rw [Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      zpow_neg, show (1024 : ℤ) = ((1024 : ℕ) : ℤ) by norm_num, zpow_natCast]
    apply inv_anti₀ (by positivity)
    calc (2 : ℝ) ^ 1024 = ((2 : ℝ) ^ 256) ^ 4 := by rw [← pow_mul]
      _ ≤ x ^ 4 := pow_le_pow_left₀ (by positivity) hx 4
  have hpos : 0 ≤ x ^ (-(90.2 : ℝ)) := Real.rpow_nonneg hx0.le _
  unfold FQ
  calc 2 * ((3184 + 30400 * logb 2 x) * x ^ (-(90.2 : ℝ)))
      ≤ 2 * ((2 : ℝ) ^ 16 * x * x ^ (-(90.2 : ℝ))) := by gcongr
    _ = (2 : ℝ) ^ 17 * (x * x ^ (-(90.2 : ℝ))) := by ring
    _ ≤ (2 : ℝ) ^ 17 * (2 : ℝ) ^ (-(1024 : ℤ)) := by gcongr; exact h2.trans h3
    _ < (2 : ℝ) ^ (-(1000 : ℤ)) := by
        rw [show (2 : ℝ) ^ 17 = (2 : ℝ) ^ (17 : ℤ) by norm_num, ← zpow_add₀ (by norm_num)]
        exact zpow_lt_zpow_right₀ (by norm_num) (by norm_num)

/-- [s7:lemUHsplit] (iv): "`78 nM_l/Hcd_l = 624 nM_l^3/λ_{l-2}^{95}`, and
`log₂θ^ult_l ≤ log₂(M_l Hcd_l/7) ≤ 95 log₂λ_{l-2}`. With `M_l ≤ λ_{l-2}^{1.6}`, these terms are at
most `nF(λ_{l-2})`." Here `Hcd = λ^{95}/(8M^2)` and `θ ≤ M Hcd/7`. -/
theorem det_tail_le {n M lam : ℝ} {θ : ℕ} (hn : 0 ≤ n) (hM : 1 ≤ M) (hlam : 1 ≤ lam)
    (hMlam : M ≤ lam ^ (1.6 : ℝ)) (hθ : (θ : ℝ) ≤ M * (lam ^ 95 / (8 * M ^ 2)) / 7) :
    78 * n * M / (lam ^ 95 / (8 * M ^ 2)) +
        320 * n * M ^ 3 * (logb 2 (θ : ℝ) + 8) / lam ^ 95 ≤ n * FQ lam := by
  have hM0 : 0 < M := by linarith
  have hlam0 : 0 < lam := by linarith
  have hL0 : 0 < lam ^ 95 := by positivity
  have hloglam : 0 ≤ logb 2 lam := logb_nonneg (by norm_num) hlam
  -- `log₂θ ≤ 95 log₂λ`
  have hθlog : logb 2 (θ : ℝ) ≤ 95 * logb 2 lam := by
    rcases Nat.eq_zero_or_pos θ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.logb_zero]; positivity
    · have hθ1 : (0 : ℝ) < θ := by exact_mod_cast hpos
      have hle : (θ : ℝ) ≤ lam ^ 95 := by
        refine hθ.trans ?_
        rw [div_le_iff₀ (by norm_num)]
        have e : M * (lam ^ 95 / (8 * M ^ 2)) = lam ^ 95 / (8 * M) := by field_simp
        rw [e, div_le_iff₀ (by positivity)]
        nlinarith
      calc logb 2 (θ : ℝ) ≤ logb 2 (lam ^ 95) := logb_le_logb_of_le (by norm_num) hθ1 hle
        _ = 95 * logb 2 lam := by rw [Real.logb_pow]; push_cast; ring
  -- `M^3 ≤ λ^{4.8}` and `λ^{4.8}/λ^{95} = λ^{-90.2}`
  have hM3 : M ^ 3 ≤ lam ^ (4.8 : ℝ) := by
    calc M ^ 3 ≤ (lam ^ (1.6 : ℝ)) ^ 3 := pow_le_pow_left₀ hM0.le hMlam 3
      _ = lam ^ (4.8 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]; norm_num
  have hpow : lam ^ (4.8 : ℝ) / lam ^ 95 = lam ^ (-(90.2 : ℝ)) := by
    rw [← Real.rpow_natCast lam 95, ← Real.rpow_sub hlam0]; norm_num
  have hA : 0 ≤ 3184 + 30400 * logb 2 lam := by positivity
  have e1 : 78 * n * M / (lam ^ 95 / (8 * M ^ 2)) = 624 * n * M ^ 3 / lam ^ 95 := by
    field_simp; ring
  rw [e1]
  have step : 624 * n * M ^ 3 / lam ^ 95 + 320 * n * M ^ 3 * (logb 2 (θ : ℝ) + 8) / lam ^ 95 ≤
      n * (3184 + 30400 * logb 2 lam) * (M ^ 3 / lam ^ 95) := by
    have e2 : 624 * n * M ^ 3 / lam ^ 95 + 320 * n * M ^ 3 * (logb 2 (θ : ℝ) + 8) / lam ^ 95 =
        n * (624 + 320 * (logb 2 (θ : ℝ) + 8)) * (M ^ 3 / lam ^ 95) := by ring
    rw [e2]
    have hm3 : 0 ≤ M ^ 3 / lam ^ 95 := by positivity
    have : 624 + 320 * (logb 2 (θ : ℝ) + 8) ≤ 3184 + 30400 * logb 2 lam := by linarith
    have := mul_le_mul_of_nonneg_left this hn
    exact mul_le_mul_of_nonneg_right this hm3
  refine step.trans ?_
  unfold FQ
  have hdiv : M ^ 3 / lam ^ 95 ≤ lam ^ (-(90.2 : ℝ)) := by
    rw [← hpow]; exact div_le_div_of_nonneg_right hM3 hL0.le
  have := mul_le_mul_of_nonneg_left hdiv (mul_nonneg hn hA)
  linarith

end EG.Quot
