module

public import EG.Defs.HB.Run
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The pool function `ψ(x) = (6 log x + 12)/x` (manuscript s2:lemTower (b))

Helper lemmas for `EG.Todo.TowerBRest` (unit P3-s2):
* `EG.HB.logb_le_two_mul_sub_one`: `log₂ t ≤ 2(t - 1)` for `t ≥ 1` (`ln t ≤ t - 1`, `ln 2 > 1/2`);
* `EG.HB.psiPool_anti`: "The function `ψ` is decreasing on `[1,∞)`" (algebraic form);
* `EG.HB.psiPool_two_mul_le`: "`ψ(2M) = (6 log M + 18)/(2M) … ≤ 0.512 ψ(M)`, as `log M ≥ 40`";
* `EG.HB.geomRatio`: `Σ_{r ≤ R} X_r ≤ X_R/(1-q)` if `0 ≤ X_r ≤ q X_{r+1}` (`0 ≤ q < 1`), the
  geometric sum behind "`Σ_{l≤R} ψ(M_l) ≤ ψ(M_R)/(1-0.512)`".
-/

public section

namespace EG.HB

open Real

theorem logb_le_two_mul_sub_one {t : ℝ} (ht : 1 ≤ t) : logb 2 t ≤ 2 * (t - 1) := by
  have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < t)
  have h2 := Real.log_two_gt_d9
  have hl2 : 0 < Real.log 2 := by linarith
  rw [Real.logb, div_le_iff₀ hl2]
  nlinarith

/-- "The function `ψ` is decreasing on `[1,∞)`". -/
theorem psiPool_anti {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : psiPool y ≤ psiPool x := by
  unfold psiPool
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  set t := y / x with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hx0]; linarith
  have hyt : y = t * x := by rw [ht]; field_simp
  have hLy : logb 2 y = logb 2 t + logb 2 x := by
    rw [hyt, Real.logb_mul (by linarith) hx0.ne']
  have hLx : 0 ≤ logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hLt := logb_le_two_mul_sub_one ht1
  rw [div_le_div_iff₀ hy0 hx0, hLy, hyt]
  have hkey : 6 * logb 2 t ≤ (t - 1) * (6 * logb 2 x + 12) := by nlinarith
  nlinarith

/-- "`ψ(2M) = (6 log M + 18)/(2M) = ψ(M)(1/2 + 3/(6 log M + 12)) ≤ 0.512 ψ(M)`, as
`log M ≥ 40`". -/
theorem psiPool_two_mul_le {M : ℝ} (hM : 0 < M) (hL : 40 ≤ logb 2 M) :
    psiPool (2 * M) ≤ 0.512 * psiPool M := by
  unfold psiPool
  rw [Real.logb_mul (by norm_num) hM.ne', Real.logb_self_eq_one (by norm_num)]
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hM]
  nlinarith

/-- Geometric sum with ratio `q < 1`: `Σ_{r ≤ R} X_r ≤ X_R/(1 - q)`. -/
theorem geomRatio (X : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R) (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1)
    (h0 : ∀ r ∈ Finset.Icc 1 R, 0 ≤ X r) (hh : ∀ r ∈ Finset.Ico 1 R, X r ≤ q * X (r + 1)) :
    ∑ r ∈ Finset.Icc 1 R, X r ≤ X R / (1 - q) := by
  have hq1 : 0 < 1 - q := by linarith
  induction R, hR using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have := h0 1 (by simp)
    rw [le_div_iff₀ hq1]; nlinarith
  | succ R hR ih =>
    have h0' : ∀ r ∈ Finset.Icc 1 R, 0 ≤ X r := fun r hr =>
      h0 r (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hr).1, by linarith [(Finset.mem_Icc.1 hr).2]⟩)
    have hh' : ∀ r ∈ Finset.Ico 1 R, X r ≤ q * X (r + 1) := fun r hr =>
      hh r (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hr).1, by linarith [(Finset.mem_Ico.1 hr).2]⟩)
    have ih' := ih h0' hh'
    have hstep : X R ≤ q * X (R + 1) := hh R (Finset.mem_Ico.2 ⟨hR, by omega⟩)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : X R / (1 - q) ≤ q * X (R + 1) / (1 - q) := div_le_div_of_nonneg_right hstep hq1.le
    have e : q * X (R + 1) / (1 - q) + X (R + 1) = X (R + 1) / (1 - q) := by
      field_simp; ring
    linarith

end EG.HB
