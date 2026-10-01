module

public import EG.Spec.Link.Star
public import EG.Lib.Link.Star
public import EG.Proof.Todo.StarS4

/-!
# P3 stub: `EG.Spec.StarS5Statement` (s3:eqS5)

Generated at the P2→P3 transition (2026-09-30). Proved in P3 from (eqStar), (S4)
(`EG.Todo.StarS4`: `θ_* ≤ 2^{46}L^9ρ^{-2}`) and `ε'^{-1} ≤ 2^7`; the real powers via
`2^{0.6} > 1.51` (`1.51^5 < 8`). Keep the name `EG.Todo.StarS5`; consumers import this module.
-/

public section

namespace EG.Todo

/-- `2^{0.6} > 1.51`, since `1.51^5 < 8 = (2^{0.6})^5`. -/
private theorem two_rpow_six_tenths : (151 / 100 : ℝ) < (2 : ℝ) ^ (0.6 : ℝ) := by
  have h5 : ((2 : ℝ) ^ (0.6 : ℝ)) ^ (5 : ℕ) = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos : 0 ≤ (2 : ℝ) ^ (0.6 : ℝ) := by positivity
  apply lt_of_pow_lt_pow_left₀ 5 hpos
  rw [h5]; norm_num

private theorem two_rpow_add (k : ℕ) :
    (2 : ℝ) ^ ((k : ℝ) + 0.6) = (2 : ℝ) ^ k * (2 : ℝ) ^ (0.6 : ℝ) := by
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast]

/-- Proved in P3. [s3:eqS5] see `EG.Spec.StarS5Statement`. -/
theorem StarS5 : EG.Spec.StarS5Statement := by
  intro n ε' ρ t hn hε1 hε2 h0 h1 ht
  have hε7 : (1 / 128 : ℝ) ≤ ε' := by
    have : (2 : ℝ) ^ (-7 : ℤ) = 1 / 128 := by norm_num
    rw [this] at hε1; exact hε1
  have hε : 0 < ε' := lt_of_lt_of_le (by norm_num) hε7
  have he : ε'⁻¹ ≤ 2 ^ 7 := by
    rw [inv_le_comm₀ hε (by norm_num)]; norm_num; linarith
  have hL := Star.one_le_L hn
  have hL0 : 0 < Star.L n := Star.L_pos hn
  have hθ0 := Star.theta_pos hn hε h0
  have hs0 := Star.sbar_pos hn h0 (by linarith : (0 : ℝ) < t)
  have hS4 := (StarS4 n ε' ρ hn hε1 hε2 h0 h1).2.2
  have hθle : Star.theta n ε' ρ ≤ (2 : ℝ) ^ 46 * Star.L n ^ 9 * (ρ ^ 2)⁻¹ := by
    have := le_trans hS4.1 hS4.2
    rwa [zpow_neg, zpow_ofNat] at this
  -- `ρ`-powers
  have hr2 : 1 ≤ (ρ ^ 2)⁻¹ := one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ h0.le h1)
  have hr3 : 1 ≤ (ρ ^ 3)⁻¹ := one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ h0.le h1)
  have hz3 : ρ ^ (-3 : ℤ) = (ρ ^ 3)⁻¹ := by rw [zpow_neg, zpow_ofNat]
  have hz5 : ρ ^ (-5 : ℤ) = (ρ ^ 3)⁻¹ * (ρ ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_ofNat, ← mul_inv, ← pow_add]
  rw [hz3, hz5]
  have hL19 : 1 ≤ Star.L n ^ 19 := one_le_pow₀ hL
  have hL9 : 1 ≤ Star.L n ^ 9 := one_le_pow₀ hL
  set T := t * Star.L n ^ 19 * (ρ ^ 3)⁻¹ with hT
  have hT1 : 1 ≤ T := by
    rw [hT]
    have : 1 ≤ t * Star.L n ^ 19 := one_le_mul_of_one_le_of_one_le ht hL19
    exact one_le_mul_of_one_le_of_one_le this hr3
  -- `X := 6 s̄ θ L² / ε' ≤ 6·2^81 T`
  set X := 6 * Star.sbar n ρ t * Star.theta n ε' ρ * Star.L n ^ 2 / ε' with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hXle : X ≤ 6 * 2 ^ 81 * T := by
    rw [hX, hT, Star.sbar, div_eq_mul_inv]
    have hρi : ρ⁻¹ * (ρ ^ 2)⁻¹ = (ρ ^ 3)⁻¹ := by
      rw [← mul_inv, ← pow_succ']
    calc 6 * ((2 : ℝ) ^ 28 * t * Star.L n ^ 8 / ρ) * Star.theta n ε' ρ * Star.L n ^ 2 * ε'⁻¹
        ≤ 6 * ((2 : ℝ) ^ 28 * t * Star.L n ^ 8 / ρ) *
            ((2 : ℝ) ^ 46 * Star.L n ^ 9 * (ρ ^ 2)⁻¹) * Star.L n ^ 2 * 2 ^ 7 := by
          have : 0 ≤ 6 * ((2 : ℝ) ^ 28 * t * Star.L n ^ 8 / ρ) := by
            have : (0 : ℝ) ≤ t := by linarith
            positivity
          gcongr
      _ = 6 * 2 ^ 81 * (t * Star.L n ^ 19 * (ρ⁻¹ * (ρ ^ 2)⁻¹)) := by ring
      _ = 6 * 2 ^ 81 * (t * Star.L n ^ 19 * (ρ ^ 3)⁻¹) := by rw [hρi]
  have hK : (Star.K n ε' ρ t : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
  have hKle : (Star.K n ε' ρ t : ℝ) ≤ (6 * 2 ^ 81 + 1) * T := by nlinarith
  have hK0 : (0 : ℝ) ≤ Star.K n ε' ρ t := Nat.cast_nonneg _
  have hθ1 : Star.theta n ε' ρ + 1 ≤ (2 ^ 46 + 1) * (Star.L n ^ 9 * (ρ ^ 2)⁻¹) := by
    have : 1 ≤ Star.L n ^ 9 * (ρ ^ 2)⁻¹ := one_le_mul_of_one_le_of_one_le hL9 hr2
    nlinarith
  have h06 := two_rpow_six_tenths
  have hc1 : (6 * 2 ^ 81 + 1 : ℝ) ≤ (2 : ℝ) ^ (83.6 : ℝ) := by
    have e : (83.6 : ℝ) = ((83 : ℕ) : ℝ) + 0.6 := by norm_num
    rw [e, two_rpow_add]; nlinarith
  have hc2 : (2 * (6 * 2 ^ 81 + 1) * (2 ^ 46 + 1) : ℝ) ≤ (2 : ℝ) ^ (130.6 : ℝ) := by
    have e : (130.6 : ℝ) = ((130 : ℕ) : ℝ) + 0.6 := by norm_num
    rw [e, two_rpow_add]; nlinarith
  have hprod : 2 * (Star.K n ε' ρ t : ℝ) * (Star.theta n ε' ρ + 1) ≤
      2 * (6 * 2 ^ 81 + 1) * (2 ^ 46 + 1) * t * Star.L n ^ 28 * ((ρ ^ 3)⁻¹ * (ρ ^ 2)⁻¹) := by
    calc 2 * (Star.K n ε' ρ t : ℝ) * (Star.theta n ε' ρ + 1)
        ≤ 2 * ((6 * 2 ^ 81 + 1) * T) * ((2 ^ 46 + 1) * (Star.L n ^ 9 * (ρ ^ 2)⁻¹)) := by
          gcongr
      _ = _ := by rw [hT]; ring
  refine ⟨?_, le_of_le_of_eq hKle (by rw [hT]; ring), ?_, hprod, ?_, ?_⟩
  · have := Star.div_le_K n ε' ρ t
    refine le_trans (le_of_eq ?_) this
    unfold Star.mu
    field_simp
  · have : (0 : ℝ) ≤ T := by linarith
    calc (6 * 2 ^ 81 + 1) * t * Star.L n ^ 19 * (ρ ^ 3)⁻¹ = (6 * 2 ^ 81 + 1) * T := by
          rw [hT]; ring
      _ ≤ (2 : ℝ) ^ (83.6 : ℝ) * T := by gcongr
      _ = _ := by rw [hT]; ring
  · refine le_trans hprod ?_
    have : (0 : ℝ) ≤ t * Star.L n ^ 28 * ((ρ ^ 3)⁻¹ * (ρ ^ 2)⁻¹) := by
      have : (0 : ℝ) ≤ t := by linarith
      positivity
    calc 2 * (6 * 2 ^ 81 + 1) * (2 ^ 46 + 1) * t * Star.L n ^ 28 * ((ρ ^ 3)⁻¹ * (ρ ^ 2)⁻¹)
        = (2 * (6 * 2 ^ 81 + 1) * (2 ^ 46 + 1)) * (t * Star.L n ^ 28 * ((ρ ^ 3)⁻¹ * (ρ ^ 2)⁻¹)) := by
          ring
      _ ≤ (2 : ℝ) ^ (130.6 : ℝ) * (t * Star.L n ^ 28 * ((ρ ^ 3)⁻¹ * (ρ ^ 2)⁻¹)) := by gcongr
      _ = _ := by ring
  · -- `20L ≤ θ`
    have hell : (1 : ℝ) ≤ Star.ell n := by exact_mod_cast Star.ell_pos hn
    have hθ : 20 * Star.L n ≤ Star.theta n ε' ρ := by
      unfold Star.theta
      rw [le_div_iff₀ (by positivity)]
      have hερ : ε' * ρ ^ 2 ≤ 1 := by
        have : ρ ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
        nlinarith
      have hl2 : (1 : ℝ) ≤ (Star.ell n : ℝ) ^ 2 := one_le_pow₀ hell
      have hL3 : Star.L n ≤ Star.L n ^ 3 := le_self_pow₀ hL (by norm_num)
      have hL30 : 0 ≤ Star.L n ^ 3 := by positivity
      calc 20 * Star.L n * (ε' * ρ ^ 2) ≤ 20 * Star.L n * 1 := by gcongr
        _ ≤ (2 : ℝ) ^ 19 * 1 * Star.L n ^ 3 := by linarith
        _ ≤ (2 : ℝ) ^ 19 * (Star.ell n : ℝ) ^ 2 * Star.L n ^ 3 := by gcongr
    have h20 : 20 * Star.L n ≤ Star.theta n ε' ρ + 1 := by linarith
    calc 40 * (Star.K n ε' ρ t : ℝ) * Star.L n = 2 * (Star.K n ε' ρ t : ℝ) * (20 * Star.L n) := by
          ring
      _ ≤ 2 * (Star.K n ε' ρ t : ℝ) * (Star.theta n ε' ρ + 1) := by gcongr

end EG.Todo
