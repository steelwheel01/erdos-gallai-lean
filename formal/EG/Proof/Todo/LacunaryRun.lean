module

public import EG.Spec.HB.Lacunary
public import EG.Lib.HB.LacunaryRun
public import EG.Proof.Todo.DegRec

/-!
# P3 stub: `EG.Spec.LacunaryRunStatement` (s2:lemLacunary)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.LacunaryRun`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemLacunary] see `EG.Spec.LacunaryRunStatement`. -/
theorem LacunaryRun : EG.Spec.LacunaryRunStatement := by
  intro V _ G Dstar run F hD hv hR hF0 hH
  have hDpos : 0 < Dstar := by linarith [hD.two_lt]
  have hx0 : ∀ r ∈ Finset.Icc 1 run.R, Real.logb 2 Dstar ≤ run.lam G r :=
    fun r hr => EG.HB.Run.logb_le_lam hDpos hv hr
  have hstep : ∀ r ∈ Finset.Ico 1 run.R,
      (2 : ℝ) ^ (run.lam G (r + 1) / (EG.Aexp : ℝ)) ≤ run.lam G r :=
    fun r hr => EG.HB.Run.lam_step EG.Todo.DegRec hD hv hr
  obtain ⟨h1, h2⟩ := EG.HB.lacSeq _ F (run.lam G) run.R hR hF0 hH hx0 hstep
  exact ⟨h1, h2, fun h3 => EG.HB.lacSeq_shift _ F (run.lam G) run.R h3 hF0 hH hx0 hstep⟩

end EG.Todo
