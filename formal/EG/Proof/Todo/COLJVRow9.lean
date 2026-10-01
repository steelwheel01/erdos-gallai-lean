module

public import EG.Spec.Lend.COLJV
public import EG.Proof.Lend.COLJVCount
public import EG.Lib.Lend.Standing

/-!
# P3 stub: `EG.Spec.COLJVRow9Statement` (s3:lemCOLJV)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.COLJVRow9`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemCOLJV] see `EG.Spec.COLJVRow9Statement`. -/
theorem COLJVRow9 : EG.Spec.COLJVRow9Statement := by
  intro V _ G Dstar run hΓ hV Y hY
  obtain ⟨h0, hc⟩ := colJVCount V G Dstar run hΓ hV Y hY
  by_cases hR2 : Y.1 + 2 ≤ run.R
  · obtain ⟨-, -, -, -, hk1, hk2, hk3, hk4, -⟩ := hc hR2
    linarith
  · rw [h0 (by omega), Nat.cast_zero]
    exact Real.rpow_nonneg (Standing.lam_facts hΓ hV
      (Standing.isRound_of_mem_ancestors hY)).2.1.le _

end EG.Todo
