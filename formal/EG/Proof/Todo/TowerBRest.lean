module

public import EG.Spec.HB.Tower
public import EG.Lib.HB.TowerDeg
public import EG.Lib.HB.Psi
public import EG.Proof.Todo.DegRec

/-!
# P3 stub: `EG.Spec.TowerBRestStatement` (s2:lemTower)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.TowerBRest`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemTower] see `EG.Spec.TowerBRestStatement`. -/
theorem TowerBRest : EG.Spec.TowerBRestStatement := by
  intro V _ G Dstar run hD hv _
  have hDR := EG.Todo.DegRec
  refine ⟨?_, fun l hl2 hl => EG.HB.Run.two_M_le hDR hD hv hl2 hl,
    fun r hr1 hr => EG.HB.Run.two_P_le hDR hD hv hr1 hr, ?_⟩
  · -- `M_l log⁴ M_l ≤ M_l^2 ≤ λ_{l-2}^{3.2} ≤ λ_{l-2}^{103}/2 ≤ P_{l-2}/2`
    intro l hl3 hl
    have hlR : l ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, hl⟩
    have hl2 : l - 2 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hp := EG.HB.Run.paramHyp hD hv hlR
    have hp2 := EG.HB.Run.paramHyp hD hv hl2
    have hM := (EG.HB.Run.M_le_Amu hDR hD hv hl3 hl).trans hp2.Amu_pow_2A_le_lam
    have hL4 : Real.logb 2 (run.M G l : ℝ) ^ 4 ≤ (run.M G l : ℝ) :=
      hp.Lam4_le_d.trans hp.d_le_M
    have hM0 : (0 : ℝ) ≤ run.M G l := Nat.cast_nonneg _
    have hP := EG.HB.ParamHyp.P_ge (d := run.d G (l - 2))
    rw [EG.Cp_eq] at hP
    set x := Real.logb 2 (run.d G (l - 2)) with hxdef
    have hx1 : 1 ≤ x := hp2.one_le_lam
    have h1 : (run.M G l : ℝ) * Real.logb 2 (run.M G l : ℝ) ^ 4 ≤ (run.M G l : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hL4 hM0
    have h2 : (run.M G l : ℝ) ^ 2 ≤ x ^ 4 := by
      have h := pow_le_pow_left₀ hM0 hM 2
      have e : (x ^ (1.6 : ℝ)) ^ 2 ≤ x ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast x 4]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      exact h.trans e
    have h3 : 2 * x ^ 4 ≤ x ^ 103 := by
      have : x ^ 103 = x ^ 4 * x ^ 99 := by ring
      rw [this]
      have h99 : x ≤ x ^ 99 := le_self_pow₀ hx1 (by norm_num)
      have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num) hp2.lam_ge
      have : (0 : ℝ) ≤ x ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (hx2.trans h99) this]
    change (run.M G l : ℝ) * Real.logb 2 (run.M G l : ℝ) ^ 4 ≤ (EG.HB.POf (run.d G (l - 2)) : ℝ) / 2
    linarith
  · -- `Σ ψ(M_l) ≤ ψ(M_R)/(1 - 0.512) ≤ 2.1 ψ(D_*)`
    have hD2 := hD.two_lt
    have hpsiD : 0 ≤ EG.HB.psiPool Dstar := by
      unfold EG.HB.psiPool
      have : 0 ≤ Real.logb 2 Dstar := Real.logb_nonneg (by norm_num) (by linarith)
      positivity
    rcases Nat.eq_zero_or_pos run.R with hR | hR
    · rw [hR]; simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty]
      linarith
    have hMge : ∀ l ∈ Finset.Icc 1 run.R, Dstar ≤ (run.M G l : ℝ) :=
      fun l hl => (hv.1 l hl).1.trans (EG.HB.Run.paramHyp hD hv hl).d_le_M
    have hpsi0 : ∀ l ∈ Finset.Icc 1 run.R, 0 ≤ EG.HB.psiPool (run.M G l : ℝ) := by
      intro l hl
      have := hMge l hl
      unfold EG.HB.psiPool
      have : 0 ≤ Real.logb 2 (run.M G l : ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
      have : (0 : ℝ) ≤ run.M G l := Nat.cast_nonneg _
      positivity
    have hg := EG.HB.geomRatio (fun l => EG.HB.psiPool (run.M G l : ℝ)) run.R hR 0.512
      (by norm_num) (by norm_num) hpsi0 (by
        intro l hl
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hl
        have hl1 : l + 1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
        have h := EG.HB.Run.two_M_le hDR hD hv (l := l + 1) (by omega) (by omega)
        rw [Nat.add_sub_cancel] at h
        have h' : 2 * (run.M G (l + 1) : ℝ) ≤ run.M G l := by exact_mod_cast h
        have hp1 := EG.HB.Run.paramHyp hD hv hl1
        have hM1 := hMge (l + 1) hl1
        exact (EG.HB.psiPool_anti (by linarith) h').trans
          (EG.HB.psiPool_two_mul_le hp1.M_pos hp1.forty_le_Lam))
    have hRR : run.R ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨hR, le_rfl⟩
    have hlast : EG.HB.psiPool (run.M G run.R : ℝ) ≤ EG.HB.psiPool Dstar :=
      EG.HB.psiPool_anti (by linarith) (hMge run.R hRR)
    refine hg.trans ?_
    rw [div_le_iff₀ (by norm_num)]
    nlinarith

end EG.Todo
