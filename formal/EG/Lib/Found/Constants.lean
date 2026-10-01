module

public import EG.Defs.Constants
public import Mathlib.Tactic.NormNum

/-!
# Values of the absolute constants (manuscript s1:defConstants (i))

`epsC_eq : epsC = 1/32`, `sigmaC_eq`, `Cp_eq`, `Aexp_eq`, and positivity facts.
-/

public section


namespace EG

theorem epsC_eq : epsC = 1 / 32 := by
  rw [epsC, zpow_neg, zpow_ofNat]; norm_num

theorem epsC_pos : 0 < epsC := by rw [epsC_eq]; norm_num

theorem sigmaC_eq : sigmaC = 100 := rfl

theorem Cp_eq : Cp = 103 := rfl

theorem Aexp_eq : Aexp = 105 := rfl

@[simp] theorem cast_sigmaC : (sigmaC : ℝ) = 100 := by rw [sigmaC_eq]; norm_num

@[simp] theorem cast_Cp : (Cp : ℝ) = 103 := by rw [Cp_eq]; norm_num

@[simp] theorem cast_Aexp : (Aexp : ℝ) = 105 := by rw [Aexp_eq]; norm_num

end EG
