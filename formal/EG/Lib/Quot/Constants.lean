module

public import EG.Defs.Quot.Constants
public import EG.Defs.Quot.Xprime

/-!
# API for the small functions of s7 (`ε_X`, `F`, `ε_1`, `ε_2`, `C_0`, `t^CC`)

Design note: `formal/work/p2d/quot.md`.
-/

public section

namespace EG.Quot

open EG.HB

/-- `ε_X` with the pool term written as `2.1 ψ(D_*)`, `ψ(x) = (6 log x + 12)/x` of
[s2:lemTower] (b). -/
theorem epsX_eq_psiPool (D : ℝ) :
    epsX D = Light.epsU D + 10.3 / D + 2.1 * psiPool D := by
  simp only [epsX, psiPool]
  ring

/-- [s1:defConstants] (iv) "`θ_Q := ε_2(D_*)`". -/
theorem thetaQ_eq (D : ℝ) : thetaQ D = eps2 D := rfl

/-- `ε_1` names `ε_K`, which is `ε_ch` of [s5:lemParent] (ii) (`EG.Light.epsChain`). -/
theorem eps1_eq_epsChain (D : ℝ) :
    eps1 D = Light.epsChain D + 169 * epsA D + 252 / D + 1.5 * Chain.epsCONC D +
      3 * epsX D + 9 / D := rfl

theorem C0_eq (D : ℝ) : C0 D = D / 2 + 1085 + eps1 D := rfl

/-- "`t := t^CC_l := ⌈2 log₂ M_l⌉`" is at least `2 log₂ M_l`. -/
theorem le_tCC (M : ℕ) : 2 * Real.logb 2 (M : ℝ) ≤ tCC M := Nat.le_ceil _

/-- `t^CC_l + 1 ≤ 2 log₂ M_l + 2` (used in [s7:lemVstar]) for `M_l ≥ 1`. -/
theorem tCC_le (M : ℕ) (hM : 1 ≤ M) : (tCC M : ℝ) ≤ 2 * Real.logb 2 (M : ℝ) + 1 := by
  have h0 : 0 ≤ 2 * Real.logb 2 (M : ℝ) := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith
  exact (Nat.ceil_lt_add_one h0).le

end EG.Quot
