module

public import EG.Spec.HB.Lacunary
public import EG.Lib.HB.LacunaryRun
public import EG.Proof.Todo.LacunaryRun

/-!
# P3 stub: `EG.Spec.LacunaryIIStatement` (s2:lemLacunary)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.LacunaryII`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemLacunary] see `EG.Spec.LacunaryIIStatement`. -/
theorem LacunaryII : EG.Spec.LacunaryIIStatement := by
  intro V _ G Dstar run hD hv hR
  have hDpos : 0 < Dstar := by linarith [hD.two_lt]
  have hx0 : ∀ r ∈ Finset.Icc 1 run.R, Real.logb 2 Dstar ≤ run.lam G r :=
    fun r hr => EG.HB.Run.logb_le_lam hDpos hv hr
  refine ⟨fun r hr => EG.HB.Run.lam_step EG.Todo.DegRec hD hv hr, ?_⟩
  intro F hF0 hmono hhalf
  have hH := EG.HB.hypH_of_antitone hD F hmono hhalf
  obtain ⟨h1, h2, h3⟩ := EG.Todo.LacunaryRun V G Dstar run F hD hv hR hF0 hH
  have hmR : F (run.lam G run.R) ≤ F (Real.logb 2 Dstar) :=
    hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (hx0 _ (Finset.mem_Icc.2 ⟨hR, le_rfl⟩)))
      (hx0 _ (Finset.mem_Icc.2 ⟨hR, le_rfl⟩))
  refine ⟨h1, by linarith, by linarith, fun h3R => ?_⟩
  obtain ⟨k1, k2⟩ := h3 h3R
  have hmR2 : F (run.lam G (run.R - 2)) ≤ F (Real.logb 2 Dstar) :=
    hmono (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 (hx0 _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩)))
      (hx0 _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
  exact ⟨k1, by linarith, k2, by linarith⟩

end EG.Todo
