module

public import EG.Spec.Link.Star
public import EG.Lib.Link.Star
public import EG.Proof.Num.StarInputs

/-!
# P3 stub: `EG.Spec.StarS4Statement` (s3:eqS4)

Generated at the P2→P3 transition (2026-09-30). Proved in P3 from (eqStar), the ceiling bounds
`d_* < 1/p+1 ≤ 2/p`, `λ_* < 6/p+1 ≤ 7/p` and (S2) `p^{-2} ≤ 100ℓ_*^2ρ^{-2}`
(`EG.starS2Num`), and (S1) `ℓ_* ≤ 2^{10}L^3`. Keep the name `EG.Todo.StarS4`; consumers import
this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:eqS4] see `EG.Spec.StarS4Statement`. -/
theorem StarS4 : EG.Spec.StarS4Statement := by
  intro n ε' ρ hn hε1 hε2 h0 h1
  have hε7 : (1 / 128 : ℝ) ≤ ε' := by
    have : (2 : ℝ) ^ (-7 : ℤ) = 1 / 128 := by norm_num
    rw [this] at hε1; exact hε1
  have hε : 0 < ε' := lt_of_lt_of_le (by norm_num) hε7
  have hL := Star.one_le_L hn
  have hp0 := Star.p_pos hn h0 h1
  have hp1 := Star.p_le_one (n := n) h1
  set x := (Star.p n ρ)⁻¹ with hx
  have hx1 : 1 ≤ x := by rw [hx]; exact one_le_inv₀ hp0 |>.2 hp1
  have hd : (Star.d n ρ : ℝ) ≤ 2 * x := by
    have := Star.d_lt hn h0 h1
    rw [one_div] at this
    linarith
  have hlam : (Star.lam n ρ : ℝ) ≤ 7 * x := by
    have := Star.lam_lt hn h0 h1
    rw [div_eq_mul_inv] at this
    linarith
  have hd0 : (0 : ℝ) ≤ Star.d n ρ := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ Star.lam n ρ := Nat.cast_nonneg _
  have hS2 := (EG.starS2Num n ρ hn h0 h1).2
  have hell0 : (0 : ℝ) ≤ Star.ell n := Nat.cast_nonneg _
  have hell := Star.ell_le n
  have hL3 : (1 : ℝ) ≤ Star.L n ^ 3 := one_le_pow₀ hL
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hθ : Star.theta n ε' ρ = (2 : ℝ) ^ 19 * (Star.ell n : ℝ) ^ 2 * Star.L n ^ 3 / (ε' * ρ ^ 2) :=
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (Star.d n ρ : ℝ) * Star.lam n ρ ≤ (2 * x) * (7 * x) :=
      mul_le_mul hd hlam hl0 (by linarith)
    nlinarith
  · rw [hθ, le_div_iff₀ (by positivity)]
    have hinv : ρ⁻¹ ^ 2 * ρ ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0.ne', one_pow]
    -- `112 x² ε' ρ² ≤ 112·100 ℓ² ≤ 2^19 ℓ² L³`
    have h1' : 112 * x ^ 2 * (ε' * ρ ^ 2) ≤ 112 * (100 * (Star.ell n : ℝ) ^ 2 * ρ⁻¹ ^ 2) * ρ ^ 2 := by
      have : x ^ 2 * ε' ≤ 100 * (Star.ell n : ℝ) ^ 2 * ρ⁻¹ ^ 2 := by
        nlinarith [sq_nonneg x]
      nlinarith
    have h2' : 112 * (100 * (Star.ell n : ℝ) ^ 2 * ρ⁻¹ ^ 2) * ρ ^ 2 = 11200 * (Star.ell n : ℝ) ^ 2 := by
      rw [show 112 * (100 * (Star.ell n : ℝ) ^ 2 * ρ⁻¹ ^ 2) * ρ ^ 2 =
        11200 * (Star.ell n : ℝ) ^ 2 * (ρ⁻¹ ^ 2 * ρ ^ 2) by ring, hinv, mul_one]
    have hl2 : (0 : ℝ) ≤ (Star.ell n : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  · rw [hθ]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (Star.ell n : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 10 * Star.L n ^ 3) ^ 2 := by gcongr
    have hL0 : 0 ≤ Star.L n ^ 3 := by positivity
    calc (2 : ℝ) ^ 19 * (Star.ell n : ℝ) ^ 2 * Star.L n ^ 3
        ≤ (2 : ℝ) ^ 19 * ((2 : ℝ) ^ 10 * Star.L n ^ 3) ^ 2 * Star.L n ^ 3 := by gcongr
      _ = (2 : ℝ) ^ 39 * Star.L n ^ 9 := by ring
  · rw [zpow_neg, zpow_ofNat, div_eq_mul_inv, mul_inv]
    have hL9 : 0 ≤ Star.L n ^ 9 := by have := Star.L_nonneg n; positivity
    have he : ε'⁻¹ ≤ 2 ^ 7 := by
      rw [inv_le_comm₀ hε (by norm_num)]; norm_num; linarith
    have : 0 ≤ (ρ ^ 2)⁻¹ := by positivity
    calc (2 : ℝ) ^ 39 * Star.L n ^ 9 * (ε'⁻¹ * (ρ ^ 2)⁻¹)
        = (2 : ℝ) ^ 39 * Star.L n ^ 9 * (ρ ^ 2)⁻¹ * ε'⁻¹ := by ring
      _ ≤ (2 : ℝ) ^ 39 * Star.L n ^ 9 * (ρ ^ 2)⁻¹ * 2 ^ 7 := by gcongr
      _ = (2 : ℝ) ^ 46 * Star.L n ^ 9 * (ρ ^ 2)⁻¹ := by ring

end EG.Todo
