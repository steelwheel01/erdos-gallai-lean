module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Monotonicity of `y / log^k y` (used in manuscript s2:lemCap)

The function `χ_k(y) = y / ln^k y` satisfies `d/dy ln χ_k(y) = (1/y)(1 - k/ln y)`, so it is
non-decreasing for `y ≥ e^k`. This file proves the monotonicity without derivatives, from
`1 + t ≤ e^t`, both for the natural logarithm and for `log_c` with `c > 1` (for `c = 2`, the
manuscript's `log`; the function `y / log_c^k y` is `(ln c)^k χ_k(y)`).

* `EG.div_log_pow_le_div_log_pow`: `0 < a`, `k ≤ ln a`, `a ≤ b` give
  `a / ln^k a ≤ b / ln^k b`;
* `EG.div_logb_pow_le_div_logb_pow`: the same for `Real.logb c`, `1 < c`;
* `EG.logb_sub_logb_le`: `log_c y - log_c x ≤ (y - x) / (x ln c)` for `0 < x`, `1 < c`
  (concavity of the logarithm; used for explicit numerical bounds on `log_2`).
-/

public section


namespace EG

/-- `y ↦ y / ln^k y` is non-decreasing on `[e^k, ∞)`: if `0 < a`, `k ≤ ln a` and `a ≤ b`, then
`a / ln^k a ≤ b / ln^k b`. -/
theorem div_log_pow_le_div_log_pow {k : ℕ} {a b : ℝ} (ha : 0 < a) (hk : (k : ℝ) ≤ Real.log a)
    (hab : a ≤ b) : a / Real.log a ^ k ≤ b / Real.log b ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using hab
  have hb : 0 < b := ha.trans_le hab
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hp0 : 0 < Real.log a := by linarith
  have hpq : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hq0 : 0 < Real.log b := by linarith
  set p := Real.log a with hp
  set q := Real.log b with hq
  -- `(q/p)^k ≤ exp(k (q-p)/p) ≤ exp(q-p) = b/a`.
  have h1 : q / p ≤ Real.exp ((q - p) / p) := by
    have h := Real.add_one_le_exp ((q - p) / p)
    have e : (q - p) / p + 1 = q / p := by field_simp; ring
    linarith
  have h4 : (k : ℝ) * ((q - p) / p) ≤ q - p := by
    rw [← mul_div_assoc, div_le_iff₀ hp0]
    nlinarith
  have h5 : Real.exp (q - p) = b / a := by
    rw [Real.exp_sub, hp, hq, Real.exp_log ha, Real.exp_log hb]
  have key : (q / p) ^ k ≤ b / a :=
    calc (q / p) ^ k ≤ Real.exp ((q - p) / p) ^ k :=
          pow_le_pow_left₀ (div_nonneg hq0.le hp0.le) h1 k
      _ = Real.exp (k * ((q - p) / p)) := (Real.exp_nat_mul _ k).symm
      _ ≤ Real.exp (q - p) := Real.exp_le_exp.2 h4
      _ = b / a := h5
  rw [div_pow, div_le_div_iff₀ (pow_pos hp0 k) ha] at key
  rw [div_le_div_iff₀ (pow_pos hp0 k) (pow_pos hq0 k)]
  linarith

/-- `y ↦ y / log_c^k y` (`1 < c`) is non-decreasing on `[e^k, ∞)`: if `0 < a`, `k ≤ ln a` and
`a ≤ b`, then `a / log_c^k a ≤ b / log_c^k b`. -/
theorem div_logb_pow_le_div_logb_pow {c : ℝ} (hc : 1 < c) {k : ℕ} {a b : ℝ} (ha : 0 < a)
    (hk : (k : ℝ) ≤ Real.log a) (hab : a ≤ b) :
    a / Real.logb c a ^ k ≤ b / Real.logb c b ^ k := by
  have hL : 0 ≤ Real.log c ^ k := pow_nonneg (Real.log_pos hc).le k
  have h := mul_le_mul_of_nonneg_right (div_log_pow_le_div_log_pow ha hk hab) hL
  simp only [Real.logb, div_pow, div_div_eq_mul_div, mul_div_right_comm _ (Real.log c ^ k)]
  exact h

/-- Concavity of the logarithm in the form used for explicit bounds: for `0 < x` and `1 < c`,
`log_c y - log_c x ≤ (y - x) / (x ln c)` (for every `y > 0`). -/
theorem logb_sub_logb_le {c x y : ℝ} (hc : 1 < c) (hx : 0 < x) (hy : 0 < y) :
    Real.logb c y - Real.logb c x ≤ (y - x) / (x * Real.log c) := by
  have hL : 0 < Real.log c := Real.log_pos hc
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have e : y / x - 1 = (y - x) / x := by field_simp
  rw [e] at h
  simp only [Real.logb, ← sub_div]
  rw [div_le_div_iff₀ hL (mul_pos hx hL)]
  have h' : (Real.log y - Real.log x) * x ≤ y - x := by
    rwa [le_div_iff₀ hx] at h
  nlinarith

end EG
