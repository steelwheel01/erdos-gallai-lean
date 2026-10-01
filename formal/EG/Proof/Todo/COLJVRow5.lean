module

public import EG.Spec.Lend.COLJV
public import EG.Proof.Lend.COLJVRows
public import EG.Proof.HB.TowerBM

/-!
# P3 stub: `EG.Spec.COLJVRow5Statement` (s3:lemCOLJV)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.COLJVRow5`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemCOLJV] see `EG.Spec.COLJVRow5Statement`. -/
theorem COLJVRow5 : EG.Spec.COLJVRow5Statement := by
  intro V _ G Dstar run hΓ hV Y hY hR2
  obtain ⟨hx, hL0, hLx, hs, hcol, hlam⟩ := colJV_rows_setup hΓ hV hY
  have h5 := hcol.row (i := 5) (by norm_num) (by norm_num)
  rw [COLTable.row5_iff, hlam] at h5
  have hS := colJV_ancS_ge (G := G) (run := run) Y
  obtain ⟨hkpos, -, -⟩ := colJV_klend_facts hΓ hV hY hR2
  have hk : (Stage1.klend G run Y : ℝ) ≤ COLTable.kbar (Real.logb 2 (run.lam G Y.1)) := by
    obtain ⟨-, hc⟩ := colJVCount V G Dstar run hΓ hV Y hY
    obtain ⟨-, -, -, -, hk1, hk2, hk3, -, -⟩ := hc hR2
    linarith
  have hMb : (run.M G (Y.1 + 2) : ℝ) ≤ COLTable.Mbar (Real.logb 2 (run.lam G Y.1)) := by
    have hR := Standing.isRound_of_mem_ancestors hY
    have hD1 := HB.Run.Valid.dstar_le run G hV (l := 1) ⟨le_rfl, le_trans hR.1 hR.2⟩
    have := ((towerBM V G Dstar run hΓ.core hV hD1).1 (Y.1 + 2) (by have := hR.1; omega) hR2).1
    rwa [Nat.add_sub_cancel] at this
  set x := run.lam G Y.1 with hxdef
  set L := run.LY G Y
  set kb := COLTable.kbar (Real.logb 2 x)
  set Mb := COLTable.Mbar (Real.logb 2 x)
  set M : ℝ := (run.M G (Y.1 + 2) : ℝ)
  set k : ℝ := (Stage1.klend G run Y : ℝ)
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [le_div_iff₀ (by positivity)]
  have e1 : (2 : ℝ) ^ 135 * (3 * M) * L ^ 28 * M ^ 20 * (8 * k) =
      2 ^ 135 * 3 * 8 * (M ^ 21 * L ^ 28 * k) := by ring
  have hMb0 : 0 ≤ Mb := COLTable.Mbar_nonneg' _
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hkb0 : 0 < kb := COLTable.kbar_pos _
  have h1 : M ^ 21 * L ^ 28 * k ≤ Mb ^ 21 * (2 * x) ^ 28 * kb :=
    mul_le_mul (mul_le_mul (pow_le_pow_left₀ hM0 hMb 21) (pow_le_pow_left₀ hL0 hLx 28)
      (pow_nonneg hL0 _) (pow_nonneg hMb0 _)) hk hk0
      (mul_nonneg (pow_nonneg hMb0 _) (pow_nonneg (by linarith) _))
  have e2 : (2 : ℝ) ^ 135 * 3 * 8 * (Mb ^ 21 * (2 * x) ^ 28 * kb) =
      (3 * 2 ^ 167 * kb * Mb ^ 21) * x ^ 28 / 2 := by ring
  have h2 : (3 * 2 ^ 167 * kb * Mb ^ 21) * x ^ 28 / 2 ≤ x ^ 72 * x ^ 28 / 2 := by
    have := mul_le_mul_of_nonneg_right h5 (pow_nonneg hx0.le 28)
    linarith
  have e3 : x ^ 72 * x ^ 28 / 2 = x ^ 100 / 2 := by ring
  rw [e1]
  calc (2 : ℝ) ^ 135 * 3 * 8 * (M ^ 21 * L ^ 28 * k)
      ≤ 2 ^ 135 * 3 * 8 * (Mb ^ 21 * (2 * x) ^ 28 * kb) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ x ^ 100 / 2 := by rw [e2, ← e3]; exact h2
    _ ≤ run.ancS G Y := by linarith

end EG.Todo
