module

public import EG.Defs.Light.Stages
public import EG.Lib.Prob.Basic

/-!
# Helpers for Lemma expected demotion and lost-parent mass (s5:lemExpect)

Library of the P3-s5 unit (`formal/work/p3/s5.md`). Manuscript v6.1, `s5.tex`, proof of
[s5:lemExpect]: "By linearity and Definition s5:defStages,
`E[c_VX dem + c_PV lp] = Σ_Y |Y| (80 P(Y demoted) + 369 (R − r(Y)) P(Y ∈ Bad))`, the sum over all
light parts `Y`. … Hence the term of `Y` is at most
`|Y|^{-1}(80 + 369(2 log* d_r + 2)) ≤ |Y|^{-1} 449 log₂λ_r ≤ 898 λ_r^{-103} log₂λ_r`, using
`|Y| ≥ λ_r^{103}/2`. … there are at most `1.37n/P_r ≤ 1.37nλ_r^{-103}` of them …. Therefore round
`r` contributes at most `1.37·898 n λ_r^{-206} log₂λ_r ≤ 1231 n λ_r^{-205}`."

* `dem_lp_eq_sum`: the pointwise decomposition of `80 dem + 369 lp` over the light parts;
* `expect_dem_lp_eq`: the linearity step;
* `term_le`: the bound on the term of one light part;
* `round_le`: the bound on the contribution of one round.
-/

public section

namespace EG.Light

open EG.HB EG.Stage1

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

open Classical in
/-- `80 dem + 369 lp = Σ_Y (80 |Y| 1[Y demoted] + 369 |Y| (R − r(Y)) 1[Y ∈ Bad])` (pointwise). -/
theorem dem_lp_eq_sum (ω : Outcome G run) :
    80 * (dem ω : ℝ) + 369 * (lp ω : ℝ) =
      ∑ Y ∈ run.lightParts G,
        (80 * ((run.ancVerts G Y).card : ℝ) * ({ω' | demoted ω' Y} : Set (Outcome G run)).indicator 1 ω +
          369 * (((run.ancVerts G Y).card : ℝ) * ((run.R - Y.1 : ℕ) : ℝ)) *
            ({ω' | Y ∈ Bad ω'} : Set (Outcome G run)).indicator 1 ω) := by
  have hd : (dem ω : ℝ) = ∑ Y ∈ run.lightParts G,
      ((run.ancVerts G Y).card : ℝ) * ({ω' | demoted ω' Y} : Set (Outcome G run)).indicator 1 ω := by
    rw [dem, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    by_cases h : demoted ω Y <;> simp [h]
  have hl : (lp ω : ℝ) = ∑ Y ∈ run.lightParts G,
      ((run.ancVerts G Y).card : ℝ) * ((run.R - Y.1 : ℕ) : ℝ) *
        ({ω' | Y ∈ Bad ω'} : Set (Outcome G run)).indicator 1 ω := by
    rw [lp, Nat.cast_sum]
    have hB : Bad ω ⊆ run.lightParts G := Finset.filter_subset _ _
    rw [← Finset.sum_subset hB]
    · refine Finset.sum_congr rfl fun Y hY => ?_
      simp [hY]
    · intro Y _ hY
      simp [hY]
  rw [hd, hl, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Y _ => ?_
  ring

open Classical in
/-- Linearity: `E[80 dem + 369 lp] = Σ_Y (80 |Y| P(Y demoted) + 369 |Y| (R − r(Y)) P(Y ∈ Bad))`. -/
theorem expect_dem_lp_eq (μ : FinDist (Outcome G run)) :
    μ.expect (fun ω => 80 * (dem ω : ℝ) + 369 * (lp ω : ℝ)) =
      ∑ Y ∈ run.lightParts G,
        (80 * ((run.ancVerts G Y).card : ℝ) * μ.prob {ω' | demoted ω' Y} +
          369 * (((run.ancVerts G Y).card : ℝ) * ((run.R - Y.1 : ℕ) : ℝ)) *
            μ.prob {ω' | Y ∈ Bad ω'}) := by
  have : (fun ω => 80 * (dem ω : ℝ) + 369 * (lp ω : ℝ)) = fun ω => ∑ Y ∈ run.lightParts G,
        (80 * ((run.ancVerts G Y).card : ℝ) * ({ω' | demoted ω' Y} : Set (Outcome G run)).indicator 1 ω +
          369 * (((run.ancVerts G Y).card : ℝ) * ((run.R - Y.1 : ℕ) : ℝ)) *
            ({ω' | Y ∈ Bad ω'} : Set (Outcome G run)).indicator 1 ω) := by
    funext ω; exact dem_lp_eq_sum ω
  rw [this, FinDist.expect_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [FinDist.expect_add, FinDist.expect_const_mul, FinDist.expect_const_mul,
    ← FinDist.prob_eq_expect, ← FinDist.prob_eq_expect]

/-- The term of one light part: with `c = |Y| ≥ λ^{103}/2`, `0 ≤ k = R − r ≤ L = log₂λ`,
`L ≥ 1`, and both probabilities in `[0, c^{-2}]`,
`80 c p₁ + 369 c k p₂ ≤ 898 L / λ^{103}`. -/
theorem term_le {c k L lam p1 p2 : ℝ} (hc : lam ^ 103 / 2 ≤ c) (hlam : 0 < lam) (hk0 : 0 ≤ k)
    (hk : k ≤ L) (hL : 1 ≤ L) (_hp1 : 0 ≤ p1) (hp1' : p1 ≤ c ^ (-2 : ℤ)) (_hp2 : 0 ≤ p2)
    (hp2' : p2 ≤ c ^ (-2 : ℤ)) :
    80 * c * p1 + 369 * (c * k) * p2 ≤ 898 * L / lam ^ 103 := by
  have hl103 : 0 < lam ^ 103 := pow_pos hlam 103
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc
  have hq : c * c ^ (-2 : ℤ) = c⁻¹ := by
    rw [zpow_neg, zpow_ofNat]
    field_simp
  have h1 : 80 * c * p1 + 369 * (c * k) * p2 ≤ (80 + 369 * k) * (c * c ^ (-2 : ℤ)) := by
    have a1 : c * p1 ≤ c * c ^ (-2 : ℤ) := mul_le_mul_of_nonneg_left hp1' hcpos.le
    have a2 : c * k * p2 ≤ c * k * c ^ (-2 : ℤ) :=
      mul_le_mul_of_nonneg_left hp2' (mul_nonneg hcpos.le hk0)
    nlinarith
  rw [hq] at h1
  have h2 : (80 + 369 * k) * c⁻¹ ≤ 449 * L * c⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hcpos.le)
  have h3 : 449 * L * c⁻¹ ≤ 449 * L * (lam ^ 103 / 2)⁻¹ :=
    mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hc) (by linarith)
  have h4 : 449 * L * (lam ^ 103 / 2)⁻¹ = 898 * L / lam ^ 103 := by
    field_simp; ring
  linarith

/-- The contribution of one round: `N ≤ 1.37 n / P`, `P ≥ λ^{103}`, `0 ≤ L ≤ λ` give
`N · 898 L / λ^{103} ≤ 1231 n (λ^{205})^{-1}`. -/
theorem round_le {N n P L lam : ℝ} (hN : N ≤ 1.37 * n / P) (hP : lam ^ 103 ≤ P)
    (hlam : 0 < lam) (hL0 : 0 ≤ L) (hL : L ≤ lam) (hn : 0 ≤ n) :
    N * (898 * L / lam ^ 103) ≤ 1231 * n * (lam ^ 205)⁻¹ := by
  have hl103 : 0 < lam ^ 103 := pow_pos hlam 103
  have hPpos : 0 < P := lt_of_lt_of_le hl103 hP
  have hN' : N ≤ 1.37 * n / lam ^ 103 :=
    hN.trans (div_le_div_of_nonneg_left (by positivity) hl103 hP)
  have hg0 : 0 ≤ 898 * L / lam ^ 103 := by positivity
  calc N * (898 * L / lam ^ 103) ≤ 1.37 * n / lam ^ 103 * (898 * L / lam ^ 103) :=
        mul_le_mul_of_nonneg_right hN' hg0
    _ = 1.37 * 898 * n * L / (lam ^ 103 * lam ^ 103) := by ring
    _ ≤ 1231 * n * lam / (lam ^ 103 * lam ^ 103) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : n * L ≤ n * lam := mul_le_mul_of_nonneg_left hL hn
        nlinarith
    _ = 1231 * n * (lam ^ 205)⁻¹ := by
        field_simp

end EG.Light
