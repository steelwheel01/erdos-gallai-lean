import EG.Proof.Gamma.Sat
import EG.Proof.Gamma.N0
import EG.Lib.Vortex.Params
import EG.Lib.Lend.COLTable
import EG.Lib.Chain.Constants
import EG.Lib.Light.Constants

/-! Unit GAMMA, stage 1: cheap checks of the new definitions (`EG/Defs/Gamma/Full.lean`,
`EG/Defs/Main/GammaCond.lean`) and of the statements of `EG/Spec/Gamma/*.lean`.

* every statement elaborates as a `Prop`;
* each condition is satisfiable where this is cheap (Γ2(a), Γ3) and fails where the manuscript
  says it must (Γ1 at small `D_*`; Γ1(f) at `D_* = 2`; `N_0 < 2^{40}`; `N_0 ≤ 2^{1023}`, since
  size condition (i) forces `L ≥ 2^{10}`; Γ3 for large `N_0`; Γ4 at `D_* = 4`), so no condition is
  vacuous by an encoding accident;
* the shapes used downstream elaborate (`N0Cond` at `Z.card`, `RunHyp → Γ2(a)`).

The non-vacuity of `N0Cond` and of `GammaCond` as a whole (`EG.Spec.N0ExistsStatement`,
`EG.Spec.GammaCondExistsStatement`) is proved (`EG.exists_N0`, `EG.exists_gammaCond`) and tested
in `EGTest/GammaFull.lean`. -/

namespace EGTest.ProbeGAMMA

open EG Real

/-! ## The statements are propositions -/

example : Prop := Spec.VortexEventuallySizeStatement
example : Prop := Spec.N0EventuallyStatement
example : Prop := Spec.N0ExistsStatement
example : Prop := Spec.Col3EventuallyStatement
example : Prop := Spec.GammaSatItemsStatement
example : Prop := Spec.GammaSatEpsStatement
example : Prop := Spec.GammaSatStatement
example : Prop := Spec.GammaCondExistsStatement

-- the reductions of stage 1 chain together
example (hs : Spec.VortexEventuallySizeStatement) (hc : Spec.Col3EventuallyStatement)
    (he : Spec.GammaSatEpsStatement) : Spec.GammaCondExistsStatement :=
  gammaCondExists_of (n0Exists_of_eventually (n0Eventually_of_size hs))
    (gammaSat_of_items_eps (gammaSatItems_of_col3 hc) he)

/-! ## Small logarithms -/

theorem logb_two_pow (k : ℕ) : logb 2 ((2 : ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

theorem logb4 : logb 2 (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, logb_two_pow]; norm_num

theorem logb16 : logb 2 (16 : ℝ) = 4 := by
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, logb_two_pow]; norm_num

/-! ## Γ2(a) and Γ3 -/

example : Gamma2a ((2 : ℝ) ^ 117) := le_rfl
example : ¬ Gamma2a 4 := by unfold Gamma2a; norm_num

-- Γ3 at `N_0 = 2^{40}`, `D_* = 2^{256}`: `2^{41} ≤ 256^{103} = 2^{824}`
example : Gamma3 ((2 : ℝ) ^ 40) ((2 : ℝ) ^ 256) := by
  unfold Gamma3; rw [logb_two_pow]; norm_num [Cp]

-- Γ3 fails for `N_0 = 2^{900}` at the same `D_*`: it is a genuine lower bound in terms of `N_0`
example : ¬ Gamma3 ((2 : ℝ) ^ 900) ((2 : ℝ) ^ 256) := by
  unfold Gamma3
  rw [logb_two_pow, show ((256 : ℕ) : ℝ) = 2 ^ 8 by norm_num, ← pow_mul,
    show (2 : ℝ) * 2 ^ 900 = 2 ^ 901 by rw [← pow_succ']]
  exact not_le.2 (pow_lt_pow_right₀ (by norm_num) (by norm_num [Cp]))

/-! ## Γ1 fails at small `D_*` -/

example : ¬ Gamma1 2 := fun h => lt_irrefl _ h.two_lt

-- at `D_* = 16`, `log₂log₂D_* = 2 < 2^8`: item (a) fails at the left end of the ray
example : ¬ Gamma1 16 := by
  intro h
  have := (h.items le_rfl).a
  rw [logb16, logb4, Gamma1a] at this
  norm_num at this

-- item (f) alone fails at `D_* = 2`: the ray is `μ ≥ 0`, and row 1 fails at `μ = 0`
theorem not_row1_zero : ¬ COLTable.row 1 0 := by
  rw [COLTable.row1_iff, COLTable.lam, Real.rpow_zero, Real.one_rpow]
  rintro ⟨h, -⟩
  norm_num at h

example : ¬ Gamma1f 2 := by
  intro h
  have := h 0 (by rw [Real.logb_self_eq_one (by norm_num), Real.logb_one])
  exact not_row1_zero (this.row le_rfl (by norm_num))

/-! ## `N_0` -/

example : ¬ N0Cond 0 := fun h => by have := h.two_pow_forty_le; norm_num at this

/-- Size condition (i) (`L ≥ 2^{10}`) forces `N_0 > 2^{1023}`: `N0Cond` is not satisfiable by
small thresholds (s1:defConstants (ii): "size condition (i), `L ≥ 2^{10}`, already forces
`N_0 ≥ 2^{1024}`"; for a real `N_0` the exact consequence is `N_0 > 2^{1024} − 1`). -/
theorem n0Cond_forces {N0 : ℝ} (h : N0Cond N0) : (2 : ℝ) ^ 1023 < N0 := by
  by_contra hlt
  push Not at hlt
  have hN : N0 ≤ ((2 ^ 1023 : ℕ) : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat]; exact hlt
  have := (h.tpv hN).cond_i
  rw [Vortex.L_pow] at this
  norm_num at this

example : ¬ N0Cond ((2 : ℝ) ^ 40) := fun h => by
  have := n0Cond_forces h
  exact absurd this (not_lt.2 (pow_le_pow_right₀ (by norm_num) (by norm_num)))

-- the downstream shape: a vortex run on `Z` with `|Z| ≥ N_0`
example (N0 : ℝ) (Z : Finset ℕ) (h : N0Cond N0) (hZ : N0 ≤ (Z.card : ℝ)) :
    Vortex.TPVSize Z.card ∧ Vortex.PVSize Z.card ∧ Vortex.VXSize Z.card :=
  h.size hZ

-- upward closure in `N_0` (s1:tabOrder)
example (N0 : ℝ) (h : N0Cond N0) : N0Cond (N0 + 1) := h.mono (by linarith)

/-! ## Γ4 fails at `D_* = 4` (`614/D_* = 153.5` already exceeds `6`) -/

theorem eps1_four_gt : 6 < Quot.eps1 4 := by
  have hK : 0 ≤ Real.logb 2 (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) *
      Real.logb 2 (Real.logb 2 4))) := by
    rw [logb4, Real.logb_self_eq_one (by norm_num), mul_one]
    apply Real.logb_nonneg (by norm_num)
    have : (1 : ℝ) ≤ Real.logb 2 (Aexp : ℝ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num [Aexp])]
      norm_num [Aexp]
    nlinarith [show (1 : ℝ) ≤ Aexp by norm_num [Aexp]]
  have hKnn : 0 ≤ Chain.epsK 4 - 614 / 4 := by
    rw [Chain.epsK, add_sub_cancel_left]
    exact div_nonneg hK (by positivity)
  have hA := Chain.epsA_nonneg (D := 4) le_rfl
  have hC := Chain.epsCONC_nonneg (D := 4) le_rfl
  have hX : 0 ≤ Quot.epsX 4 := by
    unfold Quot.epsX
    have := Light.epsU_nonneg (D := 4) (by norm_num)
    rw [logb4]
    positivity
  unfold Quot.eps1
  nlinarith

example : ¬ Gamma4 4 := fun h => absurd h.1 (not_le.2 eps1_four_gt)

example (N0 : ℝ) : ¬ GammaCond N0 4 := fun h => absurd h.gamma4.1 (not_le.2 eps1_four_gt)

/-! ## The run bundle -/

example {V : Type} [DecidableEq V] {N0 D : ℝ} {G : FGraph V} {run : HB.Run V}
    (h : RunHyp N0 D G run) : Gamma2a D ∧ N0Cond N0 ∧ N0 ≤ (G.card : ℝ) :=
  ⟨h.gamma2a, h.n0Cond, h.n0_le_card⟩

example {V : Type} [DecidableEq V] {N0 D : ℝ} {G : FGraph V} {run : HB.Run V}
    (h : RunHyp N0 D G run) (h4 : Gamma4 D) : GammaCond N0 D := h.gammaCond h4

end EGTest.ProbeGAMMA
