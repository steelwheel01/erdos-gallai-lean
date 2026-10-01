module

public import EG.Spec.HB.Tower
public import EG.Lib.HB.TowerRun
public import EG.Proof.HB.TowerA

/-!
# P3 stub: `EG.Spec.TowerDStatement` (s2:lemTower)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.TowerD`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemTower] see `EG.Spec.TowerDStatement`. -/
theorem TowerD : EG.Spec.TowerDStatement := by
  intro V _ G Dstar run hD hv hd1 r l hr1 hrl hlR
  have hr : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨hr1, by omega⟩
  have h := EG.HB.Run.paramHyp hD hv hr
  have hA := (EG.towerA V G Dstar run hD hv hd1).2.2.2.1 r hr
  refine ⟨h.two_pow_logStar_le, ?_, ?_⟩
  · exact pow_le_pow_right₀ (by norm_num) (by omega)
  · exact pow_le_pow_right₀ (by norm_num) (by omega)

end EG.Todo
