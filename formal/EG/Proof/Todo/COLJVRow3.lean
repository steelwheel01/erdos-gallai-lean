module

public import EG.Spec.Lend.COLJV
public import EG.Proof.Lend.COLJVRows

/-!
# P3 stub: `EG.Spec.COLJVRow3Statement` (s3:lemCOLJV)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.COLJVRow3`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemCOLJV] see `EG.Spec.COLJVRow3Statement`. -/
theorem COLJVRow3 : EG.Spec.COLJVRow3Statement := by
  intro V _ G Dstar run hΓ hV Y hY
  obtain ⟨hx, hL0, hLx, hs, hcol, hlam⟩ := colJV_rows_setup hΓ hV hY
  have h3 := hcol.row (i := 3) (by norm_num) (by norm_num)
  rw [COLTable.row3_iff, hlam] at h3
  have hS := colJV_ancS_ge (G := G) (run := run) Y
  have hko := Standing.kown_le (G := G) (run := run) Y
  set x := run.lam G Y.1 with hxdef
  set L := run.LY G Y
  set kb := COLTable.kbar (Real.logb 2 x)
  have hkb0 : 0 < kb := COLTable.kbar_pos _
  -- `k_lend ≤ k̄`
  have hk : (Stage1.klend G run Y : ℝ) ≤ kb := by
    obtain ⟨h0, hc⟩ := colJVCount V G Dstar run hΓ hV Y hY
    by_cases hR2 : Y.1 + 2 ≤ run.R
    · obtain ⟨-, -, -, -, hk1, hk2, hk3, -, -⟩ := hc hR2
      linarith
    · rw [h0 (by omega), Nat.cast_zero]; exact hkb0.le
  have hk0 : (0 : ℝ) ≤ Stage1.klend G run Y := Nat.cast_nonneg _
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 < x := by linarith
  have hx99 : x ≤ x ^ 99 := le_self_pow₀ hx1 (by norm_num)
  have hx98 : x ≤ x ^ 98 := le_self_pow₀ hx1 (by norm_num)
  have e100 : x ^ 100 = x * x ^ 99 := by ring
  have e100' : x ^ 100 = x ^ 2 * x ^ 98 := by ring
  have hbig : (2 : ℝ) ^ 20 ≤ x := le_trans (by norm_num) hx
  refine ⟨?_, ?_, ?_⟩
  · -- `40 k_lend L_Y ≤ 80 λ k̄ ≤ λ^{100}/8 ≤ s_r/8 ≤ s_Y/4`
    have h1 : 40 * (Stage1.klend G run Y : ℝ) * L ≤ 40 * kb * (2 * x) :=
      mul_le_mul (by linarith) hLx hL0 (by positivity)
    have h2 : 40 * kb * (2 * x) * 8 ≤ x ^ 100 := by
      rw [e100]; nlinarith
    linarith
  · -- `80 L_Y ≤ 160 λ ≤ λ^{100}/2 ≤ s_r/2 ≤ s_Y`
    have h2 : 160 * x ≤ x ^ 100 / 2 := by
      rw [e100]; nlinarith
    linarith
  · -- `40 k_own L_Y ≤ 40 (2λ)(2λ) ≤ λ^{100}/8 ≤ s_r/8`
    have hko' : (Stage1.kown G run Y : ℝ) ≤ 2 * x := by linarith
    have hko0 : (0 : ℝ) ≤ Stage1.kown G run Y := Nat.cast_nonneg _
    have h1 : 40 * (Stage1.kown G run Y : ℝ) * L ≤ 40 * (2 * x) * (2 * x) :=
      mul_le_mul (by linarith) hLx hL0 (by positivity)
    have h2 : 40 * (2 * x) * (2 * x) * 8 ≤ x ^ 100 := by
      rw [e100']; nlinarith
    linarith

end EG.Todo
