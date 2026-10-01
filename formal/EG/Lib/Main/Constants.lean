module

public import EG.Defs.Main.Gamma
public import EG.Defs.Gamma.Core
public import EG.Lib.Chain.Constants
public import EG.Lib.Light.Constants

/-!
# Constants of the Main assembly (manuscript s7:thmMainProof)

The proof of Corollary [s7:thmMainProof] applies Theorem HI″ with `C := C_0` and `ϑ := θ_Q` and
checks "Its assumptions on the constants hold: `C_0 ≥ D_*/2`, since `ε_1 ≥ 0`; and
`0 ≤ θ_Q ≤ 1/4 < 1/2`." This file proves those facts:
* `EG.MainConst.eps1_nonneg`, `EG.MainConst.eps2_nonneg` (`ε_1, ε_2 ≥ 0` for `D_* ≥ 4`; all
  their terms are
  non-negative there, s7:lemGammaSat (ii) "finite sums of non-negative explicit functions");
* `EG.MainConst.half_le_C0` (`C_0 ≥ D_*/2`), `EG.MainConst.thetaQ_nonneg`,
  `EG.MainConst.thetaQ_lt_half`
  (from Γ4 "`θ_Q = ε_2(D_*) ≤ 1/4`").

Namespace `EG.MainConst` (not `EG.Quot`), so that the names cannot clash with the s7 unit's
`EG/Lib/Quot/ConstNonneg.lean`, which proves the same facts in `EG.Quot`.
-/

public section

namespace EG.MainConst

open EG.HB EG.Quot

theorem four_le_of_gamma2a {D : ℝ} (h : Gamma2a D) : 4 ≤ D := by
  unfold Gamma2a at h
  have : (4 : ℝ) ≤ 2 ^ 117 := by norm_num
  linarith

/-- `ε_K(D_*) ≥ 0` for `D_* ≥ 4`. -/
theorem epsK_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ Chain.epsK D := by
  unfold Chain.epsK Aexp
  have hL := Chain.one_le_logb_logb_of_four_le hD
  set L := Real.logb 2 (Real.logb 2 D) with hLdef
  have h1 : (1 : ℝ) ≤ Real.logb 2 ((105 : ℕ) * L) := by
    have h2 : (2 : ℝ) ≤ (105 : ℕ) * L := by push_cast; nlinarith
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h2
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have h3 : (1 : ℝ) ≤ 2 * ((105 : ℕ) : ℝ) * Real.logb 2 ((105 : ℕ) * L) := by
    push_cast at h1 ⊢; nlinarith
  have h4 : 0 ≤ Real.logb 2 (2 * ((105 : ℕ) : ℝ) * Real.logb 2 ((105 : ℕ) * L)) :=
    Real.logb_nonneg (by norm_num) h3
  have h5 : 0 ≤ 614 / D := by positivity
  have h6 : 0 ≤ 371 * L ^ 2 := by positivity
  have := div_nonneg h4 h6
  linarith

/-- `ε_U(D_*) ≥ 0`, `ε_X(D_*) ≥ 0` for `D_* ≥ 4`. -/
theorem epsX_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ epsX D := by
  unfold epsX
  have hU := Light.epsU_nonneg (D := D) (by linarith)
  have hl := Chain.two_le_logb_of_four_le hD
  have hD0 : 0 < D := by linarith
  have h1 : 0 ≤ 10.3 / D := by positivity
  have h2 : 0 ≤ 2.1 * (6 * Real.logb 2 D + 12) / D := by
    apply div_nonneg _ hD0.le; nlinarith
  linarith

/-- `F(log₂ D_*) ≥ 0` for `D_* ≥ 4`. -/
theorem FQ_logb_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ FQ (Real.logb 2 D) := by
  unfold FQ
  have hl := Chain.two_le_logb_of_four_le hD
  have hll := Chain.one_le_logb_logb_of_four_le hD
  have h1 : 0 ≤ 3184 + 30400 * Real.logb 2 (Real.logb 2 D) := by nlinarith
  have h2 : 0 ≤ Real.logb 2 D ^ (-(90.2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  exact mul_nonneg h1 h2

/-- [s7:thmMainProof] "`ε_1 ≥ 0`" (for `D_* ≥ 4`). -/
theorem eps1_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ eps1 D := by
  unfold eps1
  have h1 := epsK_nonneg hD
  have h2 := Chain.epsA_nonneg hD
  have h3 := Chain.epsCONC_nonneg hD
  have h4 := epsX_nonneg hD
  have h5 : 0 ≤ 252 / D := by positivity
  have h6 : 0 ≤ 9 / D := by positivity
  linarith

/-- [s7:thmMainProof] "`0 ≤ θ_Q`" (`ε_2 ≥ 0` for `D_* ≥ 4`). -/
theorem eps2_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ eps2 D := by
  unfold eps2
  have h2 := Chain.epsA_nonneg hD
  have h4 := epsX_nonneg hD
  have h5 : 0 ≤ 60 / D := by positivity
  have h6 := FQ_logb_nonneg hD
  linarith

/-- [s7:thmMainProof] "`C_0 ≥ D_*/2`, since `ε_1 ≥ 0`". -/
theorem half_le_C0 {D : ℝ} (hD : 4 ≤ D) : D / 2 ≤ C0 D := by
  unfold C0
  have := eps1_nonneg hD
  linarith

theorem thetaQ_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ thetaQ D := eps2_nonneg hD

/-- [s7:thmMainProof] "`θ_Q ≤ 1/4 < 1/2`" (Γ4). -/
theorem thetaQ_lt_half {D : ℝ} (h : Gamma4 D) : thetaQ D < 1 / 2 := by
  have := h.2
  unfold thetaQ
  linarith

end EG.MainConst
