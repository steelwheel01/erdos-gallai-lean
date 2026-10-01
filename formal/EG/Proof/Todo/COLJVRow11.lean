module

public import EG.Spec.Lend.COLJV
public import EG.Proof.HB.TowerBM
public import EG.Lib.Lend.Standing

/-!
# P3 stub: `EG.Spec.COLJVRow11Statement` (s3:lemCOLJV)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.COLJVRow11`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemCOLJV] see `EG.Spec.COLJVRow11Statement`. -/
theorem COLJVRow11 : EG.Spec.COLJVRow11Statement := by
  intro V _ G Dstar run hΓ hV l hl hlR
  have hD1 := HB.Run.Valid.dstar_le run G hV (l := 1) ⟨le_rfl, by omega⟩
  obtain ⟨h1, -⟩ := (towerBM V G Dstar run hΓ.core hV hD1).1 l hl hlR
  have hr : run.IsRound (l - 2) := ⟨by omega, by omega⟩
  have hcol := Standing.col3_at hΓ hV hr
  have h11 := hcol 11 (by norm_num) (by norm_num)
  rw [COLTable.row11_iff, (Standing.lam_facts hΓ hV hr).2.2] at h11
  set M : ℝ := (run.M G l : ℝ)
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hMb : M ≤ COLTable.Mbar (Real.logb 2 (run.lam G (l - 2))) := h1
  have h12 : M ^ 12 ≤ COLTable.Mbar (Real.logb 2 (run.lam G (l - 2))) ^ 12 :=
    pow_le_pow_left₀ hM0 hMb 12
  rcases hM0.eq_or_lt with h0 | h0
  · rw [← h0]; norm_num
  · rw [le_div_iff₀ (by positivity)]
    nlinarith

end EG.Todo
