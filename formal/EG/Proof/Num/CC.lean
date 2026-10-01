module

public import EG.Spec.Num.CC
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numeric facts of Lemma CC (iii) and Lemma UH*-split (ii) (manuscript s7)

Proofs of the statements of `EG/Spec/Num/CC.lean`: `numCCConst` (`6e·2.74 < 44.7`,
`4e·2.74 < 29.8`, from `Real.exp_one_lt_d9`), `numCCTwoPow` (`2^{−t^CC} ≤ M^{−2}`),
`numCCCombine` (the final computation of (iii)), `numUHsplitConst`.

Recorded slacks (exact values): `6e·2.74 = 44.6885…` vs `44.7` (0.026%); `4e·2.74 = 29.7923…`
vs `29.8` (0.026%); both need `e < 2.718978…`, while `e < 2.7182818286`. `24·1.37 = 32.88` vs
`32.9` (0.06%); `44.7 + 32.9 = 77.6` vs `78` (0.5%); `29.8` vs `30` (0.7%).
-/

public section


namespace EG

open Real

/-- [s7:lemCC] (iii) `2·1.37 = 2.74`, `6e·2.74 < 44.7`, `4e·2.74 < 29.8`. -/
theorem numCCConst : EG.Spec.NumCCConstStatement := by
  have h := Real.exp_one_lt_d9
  refine ⟨by norm_num, by linarith, by linarith⟩

/-- [s7:lemCC] (iii) `2^{−t^CC_l} ≤ M_l^{−2}`. -/
theorem numCCTwoPow : EG.Spec.NumCCTwoPowStatement := by
  intro M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [zpow_neg, zpow_neg, zpow_natCast]
  apply inv_anti₀ (by positivity)
  have hle : 2 * Real.logb 2 (M : ℝ) ≤ (Quot.tCC M : ℝ) := Nat.le_ceil _
  have hMe : (M : ℝ) = (2 : ℝ) ^ (Real.logb 2 (M : ℝ)) :=
    (Real.rpow_logb (by norm_num) (by norm_num) hM0).symm
  calc ((M : ℝ) ^ (2 : ℤ)) = ((2 : ℝ) ^ (Real.logb 2 (M : ℝ))) ^ (2 : ℕ) := by
        rw [← hMe]; norm_cast
    _ = (2 : ℝ) ^ (2 * Real.logb 2 (M : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ ((Quot.tCC M : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    _ = (2 : ℝ) ^ (Quot.tCC M) := Real.rpow_natCast _ _

/-- [s7:lemCC] (iii) The final computation. -/
theorem numCCCombine : EG.Spec.NumCCCombineStatement := by
  intro M n H P S hM hH hP hS hSn
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have he := Real.exp_one_lt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set t : ℝ := (Quot.tCC M : ℝ)
  set q : ℝ := (2 : ℝ) ^ (-(Quot.tCC M : ℤ))
  have hq : q ≤ (M : ℝ) ^ (-2 : ℤ) := numCCTwoPow M hM
  have hq0 : 0 ≤ q := by positivity
  have hnM : 0 ≤ n * M := by nlinarith
  have hn : 0 ≤ n := by
    by_contra h
    push Not at h
    nlinarith
  -- the three terms
  have h1 : 3 * (M : ℝ) * t * P ≤ 3 * (M : ℝ) * (t + 1) * P := by nlinarith
  have h2 : 6 * Real.exp 1 / H * S ≤ 44.7 * n * M / H := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hH]
    have : 6 * Real.exp 1 * S ≤ 6 * Real.exp 1 * (2.74 * n * M) :=
      mul_le_mul_of_nonneg_left hSn (by positivity)
    nlinarith
  have h3 : 4 * Real.exp 1 * q * S ≤ 29.8 * n / M := by
    have hMq : (M : ℝ) ^ (-2 : ℤ) = 1 / (M : ℝ) ^ 2 := by
      rw [zpow_neg, one_div]; norm_cast
    have hqS : q * S ≤ 1 / (M : ℝ) ^ 2 * (2.74 * n * M) := by
      rw [← hMq]
      exact mul_le_mul hq hSn hS (by positivity)
    have hsimp : 1 / (M : ℝ) ^ 2 * (2.74 * n * M) = 2.74 * n / M := by
      field_simp
    rw [hsimp] at hqS
    have hnm : 0 ≤ n / (M : ℝ) := by positivity
    calc 4 * Real.exp 1 * q * S = 4 * Real.exp 1 * (q * S) := by ring
      _ ≤ 4 * Real.exp 1 * (2.74 * n / M) := mul_le_mul_of_nonneg_left hqS (by positivity)
      _ = 4 * Real.exp 1 * 2.74 * (n / M) := by ring
      _ ≤ 29.8 * (n / M) := by nlinarith
      _ = 29.8 * n / M := by ring
  calc 3 * (M : ℝ) * t * P + (6 * Real.exp 1 / H + 4 * Real.exp 1 * q) * S
      = 3 * (M : ℝ) * t * P + 6 * Real.exp 1 / H * S + 4 * Real.exp 1 * q * S := by ring
    _ ≤ 3 * (M : ℝ) * (t + 1) * P + 44.7 * n * M / H + 29.8 * n / M := by linarith

/-- [s7:lemUHsplit] (ii) `24·1.37 = 32.88 < 32.9`, `44.7 + 32.9 ≤ 78`, `29.8 ≤ 30`. -/
theorem numUHsplitConst : EG.Spec.NumUHsplitConstStatement := by
  unfold EG.Spec.NumUHsplitConstStatement
  norm_num

end EG
