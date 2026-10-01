module

public import EG.Spec.Link.T16sForced
public import EG.Lib.Found.Graph

/-!
# P3 stub: `EG.Spec.T16sForcedStatement` (s3:thmT16s)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.T16sForced`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:thmT16s] see `EG.Spec.T16sForcedStatement`. -/
theorem T16sForced : EG.Spec.T16sForcedStatement := by
  intro V _ X ε' s ρ t hε1 hε2 hX h0 h1 ht hs hN
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  -- `s < N`
  obtain ⟨v, hv⟩ : X.verts.Nonempty := Finset.card_pos.1 (by rw [← FGraph.card_def]; omega)
  have hsN : s < (X.card : ℝ) := by
    have h1 := hX.lt_deg hε hN hv
    have h2 : (X.deg v : ℝ) < X.card := by exact_mod_cast FGraph.deg_lt_card hv
    linarith
  have hN2 : (2 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hN
  set N : ℝ := (X.card : ℝ) with hNdef
  set L := Real.logb 2 N with hLdef
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) hN0]; simpa using hN2
  have hL0 : 0 ≤ L := by linarith
  have hρ5 : ρ ^ (-5 : ℤ) = (ρ ^ 5)⁻¹ := by rw [zpow_neg, zpow_ofNat]
  rw [hρ5] at hs
  -- `2^{135} L^{28} < ρ^5 N`
  have hkey : (2 : ℝ) ^ 135 * L ^ 28 < ρ ^ 5 * N := by
    have hρp : 0 < ρ ^ 5 := by positivity
    have h1 : (2 : ℝ) ^ 135 * L ^ 28 * (ρ ^ 5)⁻¹ ≤ (2 : ℝ) ^ 135 * t * L ^ 28 * (ρ ^ 5)⁻¹ := by
      have : (0 : ℝ) ≤ (2 : ℝ) ^ 135 * L ^ 28 * (ρ ^ 5)⁻¹ := by positivity
      nlinarith
    have h2 : (2 : ℝ) ^ 135 * L ^ 28 * (ρ ^ 5)⁻¹ < N := by linarith
    have e : (2 : ℝ) ^ 135 * L ^ 28 = (2 : ℝ) ^ 135 * L ^ 28 * (ρ ^ 5)⁻¹ * ρ ^ 5 := by
      field_simp
    rw [e]
    exact mul_lt_mul_of_pos_right h2 hρp |>.trans_le (le_of_eq (mul_comm _ _))
  have hA : ((2 : ℝ) ^ 27 * L ^ (28 / 5 : ℝ) * N ^ (4 / 5 : ℝ)) ^ 5 = (2 : ℝ) ^ 135 * L ^ 28 * N ^ 4 := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (L ^ (28 / 5 : ℝ)), ← Real.rpow_mul hL0,
      ← Real.rpow_natCast (N ^ (4 / 5 : ℝ)), ← Real.rpow_mul hN0.le]
    norm_num
  have hmain : (2 : ℝ) ^ 27 * L ^ (28 / 5 : ℝ) * N ^ (4 / 5 : ℝ) < ρ * N := by
    apply lt_of_pow_lt_pow_left₀ 5 (by positivity)
    rw [hA, mul_pow]
    have hN4 : 0 < N ^ 4 := by positivity
    have := mul_lt_mul_of_pos_right hkey hN4
    calc (2 : ℝ) ^ 135 * L ^ 28 * N ^ 4 < ρ ^ 5 * N * N ^ 4 := this
      _ = ρ ^ 5 * N ^ 5 := by ring
  refine ⟨hmain, le_trans ?_ hmain.le⟩
  have h1 : L ^ (2 : ℝ) ≤ L ^ (28 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have h2 : (1 : ℝ) ≤ N ^ (4 / 5 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  rw [Real.rpow_two] at h1
  have h3 : 0 ≤ L ^ (28 / 5 : ℝ) := by positivity
  calc L ^ 2 ≤ L ^ (28 / 5 : ℝ) := h1
    _ = 1 * L ^ (28 / 5 : ℝ) * 1 := by ring
    _ ≤ (2 : ℝ) ^ 27 * L ^ (28 / 5 : ℝ) * N ^ (4 / 5 : ℝ) := by gcongr; norm_num

end EG.Todo
