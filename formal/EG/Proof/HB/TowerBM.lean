module

public import EG.Spec.HB.TowerBM
public import EG.Lib.HB.TowerDeg
public import EG.Lib.HB.Lacunary
public import EG.Proof.Todo.DegRec

/-!
# Lemma s2:lemTower (b), the `M_l` clauses (formerly a declared input of probe P4B; proved in P3, unit P3-s2)

Stub of a declared input of probe unit P4B (probe P-4, part 2). Owned by the s2 tower unit; used by s5:lemParent Steps 5 and 9. It is not proved by the
probe. Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

/-- Proved in P3. [s2:lemTower] (b), the `M_l` clauses "For `3 ≤ l ≤ R`: `M_l ≤ (A log λ_{l-2})^{2A} ≤ λ_{l-2}^{1.6}` … Moreover `Σ_{l≤R} 1/M_l ≤ 2/D_*`". -/
theorem towerBM : EG.Spec.TowerBMStatement := by
  intro V _ G Dstar run hD hv _
  have hDR := EG.Todo.DegRec
  refine ⟨fun l hl3 hl => ⟨EG.HB.Run.M_le_Amu hDR hD hv hl3 hl, ?_⟩, ?_⟩
  · have hl2 : l - 2 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    exact (EG.HB.Run.paramHyp hD hv hl2).Amu_pow_2A_le_lam
  · rcases Nat.eq_zero_or_pos run.R with hR | hR
    · rw [hR]; simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty]
      have := hD.two_lt; positivity
    have hMpos : ∀ l ∈ Finset.Icc 1 run.R, (0 : ℝ) < run.M G l :=
      fun l hl => (EG.HB.Run.paramHyp hD hv hl).M_pos
    have hgeom := EG.HB.lacGeom (fun l => (1 : ℝ) / (run.M G l : ℝ)) run.R hR
      (fun l hl => (one_div_pos.2 (hMpos l hl)).le) (by
        intro l hl
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hl
        have h := EG.HB.Run.two_M_le hDR hD hv (l := l + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at h
        have h' : 2 * (run.M G (l + 1) : ℝ) ≤ run.M G l := by exact_mod_cast h
        have hp := hMpos (l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        rw [div_div, div_le_div_iff₀ (hMpos l (Finset.mem_Icc.2 ⟨h1, h2.le⟩)) (by positivity)]
        linarith)
    refine hgeom.1.trans ?_
    have hRR : run.R ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨hR, le_rfl⟩
    have hp := EG.HB.Run.paramHyp hD hv hRR
    have h1 : Dstar ≤ (run.M G run.R : ℝ) := (hv.1 run.R hRR).1.trans hp.d_le_M
    have hD0 : 0 < Dstar := by linarith [hD.two_lt]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) hD0 h1

end EG
