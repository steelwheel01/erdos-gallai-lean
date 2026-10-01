module

public import EG.Spec.Quot.Ultra
public import EG.Proof.Todo.UltraCopies
public import EG.Lib.Quot.UltraAux
public import EG.Lib.Prob.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# P3 stub: `EG.Spec.UltraSumStatement` (s7:lemUltra)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UltraSum`; consumers import this module.

Proof (manuscript s7:lemUltra (iv)): sum (iii) (`EG.Todo.UltraCopies`) over the ultra hubs. For an
ultra hub, `c^live_h > θ^ult_l ≥ 1`, so `log₂c^live_h + 8 ≤ c^live_h(log₂θ^ult_l + 8)/θ^ult_l`
(`g(x) = (log₂x + 8)/x` is decreasing, `EG.Quot.logb_add_eight_mul_le`). By (J2),
`Σ_h c^live_h ≤ |J_l| ≤ n(M_l − 1) ≤ nM_l` (`EG.Quot.RoundInput.sum_clive_le_card_J`; the
manuscript's `1.37nM_l` is weaker). With `Hcd_l = λ_{l-2}^{95}/(8M_l^2)`, `Hcd_l ≥ 2^{10}M_l^{10}`
and `θ^ult_l ≥ λ_{l-2}^{95}/(57M_l)`, the total is at most
`(228 + 12) nM_l^3(log₂θ^ult_l + 8)/λ_{l-2}^{95} ≤ 320 nM_l^3(log₂θ^ult_l + 8)/λ_{l-2}^{95}`.
-/

public section

namespace EG.Todo

universe u

open EG.Quot EG.FinDist

open EG.Spec in
/-- [s7:lemUltra] `EG.Spec.UltraSumStatement` for vertex types of every universe (the Spec is stated on
`Type`; the universe-polymorphic s7b lemmas (s7:lemUHsplit (ii)) use this form). -/
theorem UltraSum_univ :
  ∀ (V : Type u) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ L : Lists I.G I.M,
      (ordersLaw I.G).expect (fun O =>
          ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), (hubCopies R (L, O) h : ℝ)) ≤
        320 * ((I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8)) / I.lam ^ 95 := by
  intro V _ I hI R hR L
  have hM : (2 : ℝ) ^ 40 ≤ (I.M : ℝ) := by exact_mod_cast hI.M_ge
  have hM0 : 0 < (I.M : ℝ) := lt_of_lt_of_le (by positivity) hM
  have hH : (2 : ℝ) ^ 10 * (I.M : ℝ) ^ 10 ≤ I.Hcd := hI.Hcd_ge
  have hH0 : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hH
  have hHe : I.Hcd = I.lam ^ 95 / (8 * (I.M : ℝ) ^ 2) := rfl
  have hLp : I.lam ^ 95 = 8 * (I.M : ℝ) ^ 2 * I.Hcd := by
    rw [hHe]; field_simp
  have hLp0 : 0 < I.lam ^ 95 := by
    rw [hLp]; exact mul_pos (by positivity) hH0
  have hMH : (399 : ℝ) ≤ (I.M : ℝ) * I.Hcd := by
    have h1 : (1 : ℝ) ≤ (I.M : ℝ) := le_trans (by norm_num) hM
    have h2 : (2 : ℝ) ^ 10 ≤ I.Hcd := by
      have : (1 : ℝ) ≤ (I.M : ℝ) ^ 10 := one_le_pow₀ h1
      nlinarith
    nlinarith
  have hθ1 : (1 : ℝ) ≤ (I.thult : ℝ) := by exact_mod_cast I.one_le_thult (by linarith)
  have hθ0 : 0 < (I.thult : ℝ) := by linarith
  have hθgt := I.thult_gt
  -- `θ^ult_l ≥ λ^{95}/(57 M_l)`
  have hθ57 : I.lam ^ 95 / (57 * (I.M : ℝ)) ≤ (I.thult : ℝ) := by
    rw [hLp, div_le_iff₀ (by positivity)]
    nlinarith
  have hK : 8 ≤ Real.logb 2 (I.thult : ℝ) + 8 := by
    have := Real.logb_nonneg (b := 2) (by norm_num) hθ1; linarith
  -- (iii) at every ultra hub, with `log₂c + 8 ≤ c(log₂θ + 8)/θ`
  rw [expect_sum]
  have hstep : ∀ h ∈ I.hubs.filter (fun h => I.thult < I.clive h),
      (ordersLaw I.G).expect (fun O => (Spec.hubCopies R (L, O) h : ℝ)) ≤
        (4 * (I.M : ℝ) * (Real.logb 2 (I.thult : ℝ) + 8) / (I.thult : ℝ) +
          4 * Real.exp 1 / I.Hcd) * (I.clive h : ℝ) := by
    intro h hh
    obtain ⟨hhub, hult⟩ := Finset.mem_filter.1 hh
    have h3 := Todo.UltraCopies_univ V I hI R hR L h hhub hult
    have hcθ : (I.thult : ℝ) ≤ (I.clive h : ℝ) := by exact_mod_cast hult.le
    have hg := logb_add_eight_mul_le hθ1 hcθ
    have hg' : Real.logb 2 (I.clive h : ℝ) + 8 ≤
        (Real.logb 2 (I.thult : ℝ) + 8) / (I.thult : ℝ) * (I.clive h : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hθ0]
      linarith
    have hM4 : 0 ≤ 4 * (I.M : ℝ) := by positivity
    calc (ordersLaw I.G).expect (fun O => (Spec.hubCopies R (L, O) h : ℝ))
        ≤ 4 * (I.M : ℝ) * (Real.logb 2 (I.clive h : ℝ) + 8) +
            4 * Real.exp 1 * (I.clive h : ℝ) / I.Hcd := h3
      _ ≤ 4 * (I.M : ℝ) * ((Real.logb 2 (I.thult : ℝ) + 8) / (I.thult : ℝ) * (I.clive h : ℝ)) +
            4 * Real.exp 1 * (I.clive h : ℝ) / I.Hcd := by
          have := mul_le_mul_of_nonneg_left hg' hM4
          linarith
      _ = _ := by ring
  -- `Σ_h c^live_h ≤ n M_l`
  have hsum : ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), (I.clive h : ℝ) ≤
      (I.G.card : ℝ) * (I.M : ℝ) := by
    have h1 := I.sum_clive_le_card_J hI.roles.2.1 (I.hubs.filter (fun h => I.thult < I.clive h))
    have h3 : ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), I.clive h ≤
        I.G.card * I.M :=
      h1.trans (hI.J2tot.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)))
    exact_mod_cast h3
  have hcoef : 0 ≤ 4 * (I.M : ℝ) * (Real.logb 2 (I.thult : ℝ) + 8) / (I.thult : ℝ) +
      4 * Real.exp 1 / I.Hcd := by
    have := Real.exp_pos 1
    have : 0 ≤ Real.logb 2 (I.thult : ℝ) + 8 := by linarith
    positivity
  calc _ ≤ ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h),
        (4 * (I.M : ℝ) * (Real.logb 2 (I.thult : ℝ) + 8) / (I.thult : ℝ) +
          4 * Real.exp 1 / I.Hcd) * (I.clive h : ℝ) := Finset.sum_le_sum hstep
    _ = (4 * (I.M : ℝ) * (Real.logb 2 (I.thult : ℝ) + 8) / (I.thult : ℝ) +
          4 * Real.exp 1 / I.Hcd) *
        ∑ h ∈ I.hubs.filter (fun h => I.thult < I.clive h), (I.clive h : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ (4 * (I.M : ℝ) * (Real.logb 2 (I.thult : ℝ) + 8) / (I.thult : ℝ) +
          4 * Real.exp 1 / I.Hcd) * ((I.G.card : ℝ) * (I.M : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hcoef
    _ ≤ 320 * ((I.G.card : ℝ) * (I.M : ℝ) ^ 3 * (Real.logb 2 (I.thult : ℝ) + 8)) /
          I.lam ^ 95 :=
        ultraSum_arith hM0 (Nat.cast_nonneg _) hθ0 hLp0 hHe hθ57 hK (Real.exp_pos 1)
          Real.exp_one_lt_three

/-- Proved in P3. [s7:lemUltra] see `EG.Spec.UltraSumStatement`. -/
theorem UltraSum : EG.Spec.UltraSumStatement := UltraSum_univ.{0}

end EG.Todo
