module

public import EG.Spec.Num.L17s
public import EG.Proof.Num.StarInputs
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Numeric facts of Lemma 17* (manuscript s3:lemL17s)

Proofs of the statements of `EG/Spec/Num/L17s.lean`.

Stage 1 (this file): the pure constants, proved by `norm_num` (with `Real.exp_neg_one_lt_d9`
for `1 − e^{−1} ≥ 0.63`) and the exponent comparison of case (b):
`numL17sBernsteinMargin`, `numL17sCaseAConst`, `numL17sBernsteinExponent`, `numL17sCaseBMean`,
`numL17sCaseBSmallPConst`, `numL17sCaseBLargePConst`, `numL17sStep5`.
Fix round 1 (review I-2, I-4): Step 0, Step 3, Step 4 and the parameter statements of cases (a)
and (b): `numL17sStep0`, `numL17sStep3`, `numL17sStep4`, `numL17sCaseASigma`,
`numL17sCaseAExponent`, `numL17sCaseBGrowth`, `numL17sCaseBExponent`. Cases (a)/(b) use
`EG.starS2Num`, `EG.starS3` (`EG/Proof/Num/StarInputs.lean`, proved in fix round 1). Step 4's
`ln(1+g) ≥ 15g/16` goes through the third-order Taylor bound of `log (1-x)`
(`Real.abs_log_sub_add_sum_range_le`), since `ln(1+g) ≥ g − g²/2` is not in Mathlib; the slack at
`g = 1/8` is `ln(1.125) = 0.11778…` vs `15/128 = 0.11719…` (0.5%).

Recorded slacks (exact values): `0.09/4.2 = 0.0214285…` vs `1/47 = 0.0212765…` (0.71%);
`0.1·2^{19}/192 = 273.066…` vs `273` (0.02%); `2^{19}/28200 = 18.5917…` vs `18.59` (0.01%) and
vs `18` (3.3%); `13/0.0121 = 1074.38…` vs `1075` (0.06%); `2^{19}/(94·1075) = 5.188…` vs `5`
(3.8%); `1 − e^{−1} = 0.63212…` vs `0.63` (0.34%); `0.0081·0.6/2 = 0.00243` vs
`1/412 = 0.0024271…` (0.12%); `0.0027` vs `1/412` (11%); `1/412 − 1/413 = 5.877…·10^{−6}` vs
`2^{−36} = 1.455…·10^{−11}`; `2^{10}e^{−11} = 0.0171…` vs `0.02` (14%); Step 0:
`7/2^{39} ≤ 2^{−36}` (12.5%); Step 4: `ln 2 = 0.693…` vs `15/16` (26%).
-/

public section


namespace EG

open Real

/-- [s3:lemL17s] `0.09/4.2 > 1/47`. -/
theorem numL17sBernsteinMargin : EG.Spec.NumL17sBernsteinMarginStatement := by
  unfold EG.Spec.NumL17sBernsteinMarginStatement
  norm_num

/-- [s3:lemL17s] `0.1·2^{19}/192 ≥ 273`. -/
theorem numL17sCaseAConst : EG.Spec.NumL17sCaseAConstStatement := by
  unfold EG.Spec.NumL17sCaseAConstStatement
  norm_num

/-- [s3:lemL17s] The Bernstein exponent of case (b). -/
theorem numL17sBernsteinExponent : EG.Spec.NumL17sBernsteinExponentStatement := by
  intro X Δ hX hΔ
  refine ⟨by ring, by ring, ?_⟩
  apply Real.exp_le_exp.mpr
  have hD : 0 < 4 * Δ * X + 0.2 * Δ * X := by positivity
  have h47 : 0 < 47 * Δ := by positivity
  have key : X / (47 * Δ) ≤ 0.09 * X ^ 2 / (4 * Δ * X + 0.2 * Δ * X) := by
    rw [div_le_div_iff₀ h47 hD]
    have : 0 < Δ * X ^ 2 := by positivity
    nlinarith
  linarith

/-- [s3:lemL17s] `1 − e^{−1} ≥ 0.63` and `0.63 − 0.3 = 0.33`. -/
theorem numL17sCaseBMean : EG.Spec.NumL17sCaseBMeanStatement := by
  refine ⟨?_, by norm_num⟩
  have := Real.exp_neg_one_lt_d9
  linarith

/-- [s3:lemL17s] `94·300 = 28200`, `2^{19}/28200 > 18.59 ≥ 18`. -/
theorem numL17sCaseBSmallPConst : EG.Spec.NumL17sCaseBSmallPConstStatement := by
  unfold EG.Spec.NumL17sCaseBSmallPConstStatement
  norm_num

/-- [s3:lemL17s] `0.11^2 = 0.0121`, `13/0.0121 < 1075`, `2^{19}/(94·1075) ≥ 5`,
`5ℓ^2 ≥ 18` for `ℓ ≥ 2^{10}`. -/
theorem numL17sCaseBLargePConst : EG.Spec.NumL17sCaseBLargePConstStatement := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro ℓ hℓ
  nlinarith

/-- [s3:lemL17s] The constants of Step 5 and `2e^{−x/412} ≤ 2e^{−x/413}e^{−y} ≤ 0.01e^{−y}`. -/
theorem numL17sStep5 : EG.Spec.NumL17sStep5Statement := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  intro x y hx hy
  have hx0 : 0 < x := lt_trans (by positivity) hx
  constructor
  · -- `e^{−x/412} ≤ e^{−x/413 − y}` since `y ≤ 2^{−36}x ≤ x(1/412 − 1/413)`.
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have h36 : (2 : ℝ) ^ (-36 : ℤ) ≤ 1 / 412 - 1 / 413 := by norm_num
    have : y ≤ (1 / 412 - 1 / 413) * x := le_trans hy (by nlinarith)
    linarith
  · -- `2e^{−x/413} ≤ 0.01` since `x/413 > 2^{39}/413 ≥ 6`.
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h6 : (6 : ℝ) ≤ x / 413 := by
      rw [le_div_iff₀ (by norm_num)]
      have : (6 : ℝ) * 413 ≤ 2 ^ 39 := by norm_num
      linarith
    have he : Real.exp (-(x / 413)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
    have h6' : Real.exp (-6) ≤ 1 / 200 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have h1 := Real.exp_one_gt_d9
      have : Real.exp 6 = Real.exp 1 ^ 6 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc ((1 / 200)⁻¹ : ℝ) = 200 := by norm_num
        _ ≤ 2.7182818283 ^ 6 := by norm_num
        _ ≤ Real.exp 1 ^ 6 := by gcongr
    linarith

/-! ### Fix round 1: the parameter statements -/

/-- `(2 : ℝ)^{-7} = 1/128`. -/
private theorem two_zpow_neg_seven : (2 : ℝ) ^ (-7 : ℤ) = 1 / 128 := by norm_num

/-- `ℓ_* ≥ 2^{10}` as a real number. -/
private theorem ell_ge {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) ^ 10 ≤ (Star.ell n : ℝ) := by
  exact_mod_cast Star.two_pow_ten_le_ell hn

/-- [s3:lemL17s] Step 0: `ρn > 2^{39}` and `7uL ≤ 2^{-36}ρn` from `θ_*u < n`. -/
theorem numL17sStep0 : EG.Spec.NumL17sStep0Statement := by
  intro n ε' ρ u hn hε1 hε2 hρ0 hρ1 hu hθ
  rw [two_zpow_neg_seven] at hε1
  have hL := Star.one_le_L hn
  have hl := ell_ge hn
  have hε0 : 0 < ε' := lt_of_lt_of_le (by norm_num) hε1
  set L := Star.L n
  set ℓ := (Star.ell n : ℝ)
  -- `2^{19}ℓ^2L^3 u < ε'ρ^2 n ≤ ρ n`.
  have hθ' : Star.theta n ε' ρ * u = 2 ^ 19 * ℓ ^ 2 * L ^ 3 * u / (ε' * ρ ^ 2) := by
    unfold Star.theta; ring
  rw [hθ', div_lt_iff₀ (by positivity)] at hθ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hερ : ε' * ρ ^ 2 ≤ ρ := by
    have : ε' * ρ ≤ 1 := by nlinarith
    nlinarith
  have hkey : 2 ^ 19 * ℓ ^ 2 * L ^ 3 * u < ρ * n := by
    calc 2 ^ 19 * ℓ ^ 2 * L ^ 3 * u < n * (ε' * ρ ^ 2) := hθ
      _ ≤ n * ρ := mul_le_mul_of_nonneg_left hερ hn0
      _ = ρ * n := by ring
  have hl2 : (2 : ℝ) ^ 20 ≤ ℓ ^ 2 := by nlinarith
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hL3 : L ≤ L ^ 3 := by
    have : L * 1 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by linarith)
    nlinarith
  have hL3' : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hbig : (2 : ℝ) ^ 39 * L * u ≤ 2 ^ 19 * ℓ ^ 2 * L ^ 3 * u := by
    have h1 : (2 : ℝ) ^ 39 * L ≤ 2 ^ 19 * ℓ ^ 2 * L ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  constructor
  · have : (2 : ℝ) ^ 39 ≤ 2 ^ 39 * L * u := by nlinarith
    linarith
  · have h36 : (2 : ℝ) ^ (-36 : ℤ) = 1 / 2 ^ 36 := by norm_num
    rw [h36]
    have : 7 * u * L ≤ 1 / 2 ^ 36 * (2 ^ 39 * L * u) := by nlinarith
    nlinarith

/-- [s3:lemL17s] Step 2, case (a): `3|W|/σ_* = g_*|W|`. -/
theorem numL17sCaseASigma : EG.Spec.NumL17sCaseASigmaStatement := by
  intro n ε' hn hε W
  have hL := Star.L_pos hn
  unfold Star.sigma Star.g
  field_simp
  ring

/-- [s3:lemL17s] Step 2, case (a): `p_*|Cen|/8 ≥ 273ℓ_*uL ≥ 18uL`. -/
theorem numL17sCaseAExponent : EG.Spec.NumL17sCaseAExponentStatement := by
  intro n ε' ρ hn hε1 hε2 hρ0 hρ1 u W C hu hW hC
  rw [two_zpow_neg_seven] at hε1
  have hε0 : 0 < ε' := lt_of_lt_of_le (by norm_num) hε1
  have hL := Star.one_le_L hn
  have hl := ell_ge hn
  have hS2 := (starS2Num n ρ hn hρ0 hρ1).1
  have hp0 := Star.p_pos hn hρ0 hρ1
  have hσ := Star.sigma_pos hn hε0
  have hθ := Star.theta_pos hn hε0 hρ0
  set L := Star.L n
  set ℓ := (Star.ell n : ℝ)
  have hl0 : 0 < ℓ := by linarith
  -- `(0.1ρ/ℓ)·(θ_*u/σ_*) ≤ p_*·C`.
  have hA : 0.1 * ρ / ℓ * (Star.theta n ε' ρ * u / Star.sigma n ε') ≤ Star.p n ρ * C := by
    apply mul_le_mul hS2 _ (by positivity) (by linarith)
    calc Star.theta n ε' ρ * u / Star.sigma n ε' ≤ W / Star.sigma n ε' := by gcongr
      _ ≤ C := hC
  -- `(0.1ρ/ℓ)·(θ_*u/σ_*)/8 = (0.1·2^{19}/192)·ℓuL/ρ`.
  have hid : 0.1 * ρ / ℓ * (Star.theta n ε' ρ * u / Star.sigma n ε') / 8 =
      0.1 * 2 ^ 19 / 192 * (ℓ * u * L) / ρ := by
    unfold Star.theta Star.sigma
    field_simp
    ring
  have hc := numL17sCaseAConst
  unfold EG.Spec.NumL17sCaseAConstStatement at hc
  have hpos : 0 ≤ ℓ * u * L := by positivity
  have h1 : 273 * ℓ * u * L ≤ 0.1 * 2 ^ 19 / 192 * (ℓ * u * L) / ρ := by
    rw [le_div_iff₀ hρ0]
    have : 273 * (ℓ * u * L) * ρ ≤ 273 * (ℓ * u * L) := by nlinarith
    nlinarith
  constructor
  · calc 273 * ℓ * u * L ≤ 0.1 * 2 ^ 19 / 192 * (ℓ * u * L) / ρ := h1
      _ = 0.1 * ρ / ℓ * (Star.theta n ε' ρ * u / Star.sigma n ε') / 8 := hid.symm
      _ ≤ Star.p n ρ * C / 8 := by linarith
  · have : 0 ≤ u * L := by positivity
    nlinarith

/-- [s3:lemL17s] Step 2, case (b): `0.33|X| ≥ 0.165ε'|W|/L^2 ≥ g_*|W|`. -/
theorem numL17sCaseBGrowth : EG.Spec.NumL17sCaseBGrowthStatement := by
  intro n ε' hn hε1 hε2 W X hW hX
  rw [two_zpow_neg_seven] at hε1
  have hε0 : 0 < ε' := lt_of_lt_of_le (by norm_num) hε1
  have hL := Star.L_pos hn
  constructor
  · have : 0.165 * ε' * W / Star.L n ^ 2 = 0.33 * (ε' * W / (2 * Star.L n ^ 2)) := by
      field_simp; ring
    rw [this]; linarith
  · have h0 : 0 ≤ ε' * W / Star.L n ^ 2 := by positivity
    have : Star.g n ε' * W = 0.125 * (ε' * W / Star.L n ^ 2) := by
      unfold Star.g; field_simp; ring
    have h2 : 0.165 * ε' * W / Star.L n ^ 2 = 0.165 * (ε' * W / Star.L n ^ 2) := by ring
    rw [this, h2]; linarith

/-- [s3:lemL17s] Step 2, case (b): `|X|/(47Δ_*) ≥ ε'θ_*u/(94Δ_*L^2) = 2^{19}ℓ_*^2Lu/(94Δ_*ρ^2)
≥ 18uL` (both regimes of `p_*`). -/
theorem numL17sCaseBExponent : EG.Spec.NumL17sCaseBExponentStatement := by
  intro n ε' ρ hn hε1 hε2 hρ0 hρ1 u W X hu hW hX
  rw [two_zpow_neg_seven] at hε1
  have hε0 : 0 < ε' := lt_of_lt_of_le (by norm_num) hε1
  have hL := Star.one_le_L hn
  have hl := ell_ge hn
  have hθ := Star.theta_pos hn hε0 hρ0
  have hp0 := Star.p_pos hn hρ0 hρ1
  have hD1 : (1 : ℝ) ≤ Star.Delta n ρ := by
    exact_mod_cast le_trans (Star.one_le_lam hn hρ0 hρ1) (Star.lam_le_Delta n ρ)
  have hS2 := (starS2Num n ρ hn hρ0 hρ1).2
  have hS3 := starS3 n ρ hn hρ0 hρ1
  set L := Star.L n
  set ℓ := (Star.ell n : ℝ)
  set Δ := (Star.Delta n ρ : ℝ)
  set p := Star.p n ρ
  have hΔ0 : 0 < Δ := by linarith
  have hL0 : 0 < L := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ε' * Star.theta n ε' ρ * u / (2 * L ^ 2) ≤ X := by
      calc ε' * Star.theta n ε' ρ * u / (2 * L ^ 2) = ε' * (Star.theta n ε' ρ * u) / (2 * L ^ 2) :=
            by ring
        _ ≤ ε' * W / (2 * L ^ 2) := by gcongr
        _ ≤ X := hX
    have h2 : ε' * Star.theta n ε' ρ * u / (94 * Δ * L ^ 2) =
        ε' * Star.theta n ε' ρ * u / (2 * L ^ 2) / (47 * Δ) := by
      field_simp; ring
    rw [h2]; gcongr
  · unfold Star.theta
    field_simp
    ring
  · -- `18uL·94Δ_*ρ^2 ≤ 2^{19}ℓ_*^2Lu`.
    have huL : 0 ≤ u * L := by positivity
    rw [le_div_iff₀ (by positivity)]
    have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
    have hl2 : (2 : ℝ) ^ 20 ≤ ℓ ^ 2 := by nlinarith
    by_cases hp : p ≤ 0.11
    · -- `Δ_*ρ^2 ≤ 300ℓ_*^2`.
      have hD : Δ ≤ 300 * ℓ ^ 2 * ρ⁻¹ ^ 2 := by
        have := hS3.2.1 hp; nlinarith
      have hDρ : Δ * ρ ^ 2 ≤ 300 * ℓ ^ 2 := by
        have hρi : ρ⁻¹ ^ 2 * ρ ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hρ0.ne']; norm_num
        calc Δ * ρ ^ 2 ≤ 300 * ℓ ^ 2 * ρ⁻¹ ^ 2 * ρ ^ 2 :=
              mul_le_mul_of_nonneg_right hD (by positivity)
          _ = 300 * ℓ ^ 2 := by rw [mul_assoc, hρi, mul_one]
      have : 18 * u * L * (94 * Δ * ρ ^ 2) ≤ 18 * 94 * 300 * (u * L) * ℓ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hDρ (by positivity : (0 : ℝ) ≤ 18 * 94 * (u * L))
        nlinarith
      nlinarith
    · replace hp := not_le.mp hp
      -- `Δ_* ≤ 13p_*^{-2} < 1075`.
      have hpi : p⁻¹ < 100 / 11 := by
        rw [inv_lt_comm₀ hp0 (by norm_num)]; norm_num; linarith
      have hpi0 : 0 < p⁻¹ := inv_pos.mpr hp0
      have hD : Δ ≤ 1075 := by
        have h13 := hS3.2.2
        have : p⁻¹ ^ 2 ≤ (100 / 11) ^ 2 := by gcongr
        nlinarith
      have hDρ : Δ * ρ ^ 2 ≤ 1075 := by nlinarith
      have : 18 * u * L * (94 * Δ * ρ ^ 2) ≤ 18 * 94 * 1075 * (u * L) := by
        have := mul_le_mul_of_nonneg_left hDρ (by positivity : (0 : ℝ) ≤ 18 * 94 * (u * L))
        nlinarith
      have h2 : 18 * 94 * 1075 * (u * L) ≤ 2 ^ 19 * ℓ ^ 2 * L * u := by nlinarith
      linarith

/-- `x^3 e^{−11x} ≤ e^{−11}` for `x ≥ 1`. -/
private theorem cube_mul_exp_le {x : ℝ} (hx : 1 ≤ x) : x ^ 3 * Real.exp (-(11 * x)) ≤
    Real.exp (-11) := by
  have h1 : x ≤ Real.exp (x - 1) := by linarith [Real.add_one_le_exp (x - 1)]
  have h3 : x ^ 3 ≤ Real.exp (3 * (x - 1)) := by
    calc x ^ 3 ≤ Real.exp (x - 1) ^ 3 := by gcongr
      _ = Real.exp (3 * (x - 1)) := by rw [← Real.exp_nat_mul]; norm_num
  calc x ^ 3 * Real.exp (-(11 * x)) ≤ Real.exp (3 * (x - 1)) * Real.exp (-(11 * x)) := by
        gcongr
    _ = Real.exp (3 * (x - 1) + -(11 * x)) := by rw [Real.exp_add]
    _ ≤ Real.exp (-11) := by apply Real.exp_le_exp.mpr; linarith

/-- [s3:lemL17s] Step 3: `(ℓ_*−1)e^{−18uL} ≤ 2^{10}L^3e^{−11L}e^{−7uL} ≤ 0.02e^{−7uL}`. -/
theorem numL17sStep3 : EG.Spec.NumL17sStep3Statement := by
  have h2 : (2 : ℝ) ^ 10 * Real.exp (-11) ≤ 0.02 := by
    have h := Real.exp_neg_one_lt_d9
    have he : Real.exp (-11) = Real.exp (-1) ^ 11 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (2 : ℝ) ^ 10 * Real.exp (-1) ^ 11 ≤ 2 ^ 10 * 0.3678794412 ^ 11 := by
          gcongr
      _ ≤ 0.02 := by norm_num
  refine ⟨fun x hx => cube_mul_exp_le hx, h2, ?_⟩
  intro n u hn hu
  have hL := Star.one_le_L hn
  have hl := Star.ell_le n
  have hl1 : (1 : ℝ) ≤ Star.ell n := by exact_mod_cast le_trans (by norm_num) (Star.two_le_ell hn)
  set L := Star.L n
  constructor
  · have he : Real.exp (-(18 * u * L)) ≤ Real.exp (-(11 * L)) * Real.exp (-(7 * u * L)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc ((Star.ell n : ℝ) - 1) * Real.exp (-(18 * u * L))
        ≤ 2 ^ 10 * L ^ 3 * Real.exp (-(18 * u * L)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; linarith
      _ ≤ 2 ^ 10 * L ^ 3 * (Real.exp (-(11 * L)) * Real.exp (-(7 * u * L))) := by
          apply mul_le_mul_of_nonneg_left he; positivity
      _ = 2 ^ 10 * L ^ 3 * Real.exp (-(11 * L)) * Real.exp (-(7 * u * L)) := by ring
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have := cube_mul_exp_le hL
    calc (2 : ℝ) ^ 10 * L ^ 3 * Real.exp (-(11 * L)) = 2 ^ 10 * (L ^ 3 * Real.exp (-(11 * L))) := by
          ring
      _ ≤ 2 ^ 10 * Real.exp (-11) := by gcongr
      _ ≤ 0.02 := h2

/-- `ln(1+g) ≥ 15g/16` for `0 ≤ g ≤ 1/8` (third-order Taylor bound of `log (1 - x)` at
`x = -g`). -/
private theorem fifteen_sixteenths_le_log {g : ℝ} (h0 : 0 ≤ g) (h1 : g ≤ 1 / 8) :
    15 * g / 16 ≤ Real.log (1 + g) := by
  have habs : |(-g)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 3
  rw [abs_neg, abs_of_nonneg h0, sub_neg_eq_add] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have h' := (abs_le.mp h).1
  have hg1 : 0 < 1 - g := by linarith
  have hq : g ^ 4 / (1 - g) ≤ 8 / 7 * g ^ 4 := by
    rw [div_le_iff₀ hg1]; nlinarith [pow_nonneg h0 4]
  nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]

/-- [s3:lemL17s] Step 4: `(1+g_*)^{ℓ_*−1} ≥ n`, with the intermediate bounds. -/
theorem numL17sStep4 : EG.Spec.NumL17sStep4Statement := by
  intro n ε' hn hε1 hε2
  rw [two_zpow_neg_seven] at hε1
  have hε0 : 0 < ε' := lt_of_lt_of_le (by norm_num) hε1
  have hL := Star.one_le_L hn
  have hlt := Star.lt_ell n
  have hl := ell_ge hn
  have hg0 := Star.g_pos hn hε0
  have h9 : (2 : ℝ) ^ (-9 : ℤ) = 1 / 512 := by norm_num
  rw [h9]
  set L := Star.L n
  set ℓ := (Star.ell n : ℝ)
  have hL0 : 0 < L := by linarith
  have hgdef : Star.g n ε' = ε' / (8 * L ^ 2) := rfl
  -- `g_* ≤ 1/8`.
  have hg8 : Star.g n ε' ≤ 1 / 8 := by
    rw [hgdef, div_le_iff₀ (by positivity)]; nlinarith
  have hlog := fifteen_sixteenths_le_log hg0.le hg8
  -- `(ℓ_*−1)g_* > L − 2^{-9}`.
  have hlg : L - 1 / 512 < (ℓ - 1) * Star.g n ε' := by
    rw [hgdef, mul_div_assoc', lt_div_iff₀ (by positivity)]
    have h1 : (ℓ - 1) * (1 / 128) ≤ (ℓ - 1) * ε' :=
      mul_le_mul_of_nonneg_left hε1 (by linarith)
    have h2 : (2 ^ 10 * L ^ 3 - 2) * (1 / 128) < (ℓ - 1) * (1 / 128) := by linarith
    have h3 : (L - 1 / 512) * (8 * L ^ 2) ≤ (2 ^ 10 * L ^ 3 - 2) * (1 / 128) := by nlinarith
    linarith
  -- `L ln 2 ≤ (15/16)(L − 2^{-9})`.
  have hln2 : L * Real.log 2 ≤ 15 / 16 * (L - 1 / 512) := by
    have := Real.log_two_lt_d9
    nlinarith
  refine ⟨hg8, hlog, hlg, hln2, ?_⟩
  -- `ln n = L ln 2 ≤ (ℓ_*−1)·ln(1+g_*) = ln((1+g_*)^{ℓ_*−1})`.
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : Real.log n = L * Real.log 2 := by
    simp only [L, Star.L, Real.logb]
    field_simp
  have hk := Star.cast_ell_sub_one hn
  have hpos : 0 < (1 + Star.g n ε') ^ (Star.ell n - 1) := by positivity
  rw [← Real.log_le_log_iff hn0 hpos, Real.log_pow, hk, hlogn]
  calc L * Real.log 2 ≤ 15 / 16 * (L - 1 / 512) := hln2
    _ ≤ 15 / 16 * ((ℓ - 1) * Star.g n ε') := by linarith
    _ = (ℓ - 1) * (15 * Star.g n ε' / 16) := by ring
    _ ≤ (ℓ - 1) * Real.log (1 + Star.g n ε') :=
        mul_le_mul_of_nonneg_left hlog (by linarith)

end EG
