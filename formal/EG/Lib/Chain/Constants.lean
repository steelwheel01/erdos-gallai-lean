module

public import EG.Defs.Chain.Constants
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The small constants of s6: basic API (companion of `EG.Defs.Chain.Constants`)

* `ε_M = ε_K + 169 ε_A + 252/D_*` unfolded (`epsM_eq`);
* `ε_CONC(D_*) ≥ 0` for `D_* ≥ 4` (`epsCONC_nonneg`), `ε_A ≥ 0` for `D_* ≥ 4`.
-/

public section

namespace EG.Chain

theorem epsM_eq (D : ℝ) : epsM D = epsK D + 169 * HB.epsA D + 252 / D := rfl

theorem two_le_logb_of_four_le {D : ℝ} (hD : 4 ≤ D) : 2 ≤ Real.logb 2 D := by
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hD
  rwa [h4] at this

theorem one_le_logb_logb_of_four_le {D : ℝ} (hD : 4 ≤ D) : 1 ≤ Real.logb 2 (Real.logb 2 D) := by
  have h2 := two_le_logb_of_four_le hD
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h2
  rwa [Real.logb_self_eq_one (by norm_num)] at this

theorem epsA_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ HB.epsA D := by
  unfold HB.epsA epsC
  have := one_le_logb_logb_of_four_le hD
  positivity

theorem epsCONC_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ epsCONC D := by
  unfold epsCONC epsC
  have h1 := two_le_logb_of_four_le hD
  have h2 := one_le_logb_logb_of_four_le hD
  have h3 : 0 ≤ Real.logb 2 D ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ Real.logb 2 (Real.logb 2 D) := by linarith
  have h5 : 0 ≤ Real.logb 2 D := by linarith
  positivity

end EG.Chain
