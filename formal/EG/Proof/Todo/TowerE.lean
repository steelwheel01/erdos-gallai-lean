module

public import EG.Spec.HB.Tower
public import EG.Lib.HB.TowerRun
public import EG.Lib.HB.LacunaryEx
public import EG.Proof.Todo.LacunaryRun
public import EG.Proof.Todo.OVRun

/-!
# P3 stub: `EG.Spec.TowerEStatement` (s2:lemTower)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.TowerE`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemTower] see `EG.Spec.TowerEStatement`. -/
theorem TowerE : EG.Spec.TowerEStatement := by
  intro V _ G Dstar run hD hv _
  have hD2 := hD.two_lt
  have hLL : 0 < Real.logb 2 (Real.logb 2 Dstar) := by
    have := hD.two_pow_eight_le_loglog; linarith [show (0 : ℝ) < 2 ^ 8 by norm_num]
  have heps := EG.epsC_pos
  have hA0 : 0 ≤ EG.HB.epsA Dstar := by unfold EG.HB.epsA; rw [EG.cast_Cp]; positivity
  -- `log P_l ≥ C' log λ_l > 0`
  have hlogP : ∀ l ∈ Finset.Icc 1 run.R,
      103 * Real.logb 2 (run.lam G l) ≤ Real.logb 2 (run.P G l : ℝ) ∧
        0 < Real.logb 2 (run.lam G l) := by
    intro l hl
    have hp := EG.HB.Run.paramHyp hD hv hl
    have hP := EG.HB.ParamHyp.P_ge (d := run.d G l)
    rw [EG.Cp_eq] at hP
    have hL0 : 0 < Real.logb 2 (run.lam G l) := by
      have := hp.mu_ge; change 256 ≤ Real.logb 2 (run.lam G l) at this; linarith
    refine ⟨?_, hL0⟩
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (pow_pos hp.lam_pos 103) hP
    rw [Real.logb_pow] at this
    push_cast at this
    exact this
  -- the first sum
  have hsum : ∑ l ∈ Finset.Icc 1 run.R, 15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ) ≤
      EG.HB.epsA Dstar := by
    rcases Nat.eq_zero_or_pos run.R with hR | hR
    · rw [hR]; simp only [Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.sum_empty]; exact hA0
    have hF0 := EG.HB.inv_logb_nonneg hD
    have hH := EG.HB.hypH_inv_logb hD
    have hmono := EG.HB.antitoneOn_inv_logb hD
    obtain ⟨hS, -, -⟩ := EG.Todo.LacunaryRun V G Dstar run (fun x => 1 / Real.logb 2 x) hD hv hR
      hF0 hH
    have hDpos : 0 < Dstar := by linarith
    have hRR : run.R ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨hR, le_rfl⟩
    have hx0R := EG.HB.Run.logb_le_lam hDpos hv hRR
    have hlast : 1 / Real.logb 2 (run.lam G run.R) ≤ 1 / Real.logb 2 (Real.logb 2 Dstar) :=
      hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx0R) hx0R
    have hterm : ∀ l ∈ Finset.Icc 1 run.R, 15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ) ≤
        (15.2 * EG.epsC / 103) * (1 / Real.logb 2 (run.lam G l)) := by
      intro l hl
      obtain ⟨h1, h2⟩ := hlogP l hl
      rw [div_mul_div_comm, div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
    calc ∑ l ∈ Finset.Icc 1 run.R, 15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ)
        ≤ ∑ l ∈ Finset.Icc 1 run.R, (15.2 * EG.epsC / 103) * (1 / Real.logb 2 (run.lam G l)) :=
          Finset.sum_le_sum hterm
      _ = (15.2 * EG.epsC / 103) * ∑ l ∈ Finset.Icc 1 run.R, 1 / Real.logb 2 (run.lam G l) := by
          rw [Finset.mul_sum]
      _ ≤ (15.2 * EG.epsC / 103) * (2 * (1 / Real.logb 2 (Real.logb 2 Dstar))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hS.trans (by linarith)
      _ ≤ EG.HB.epsA Dstar := by
          unfold EG.HB.epsA; rw [EG.cast_Cp]
          rw [show (15.2 * EG.epsC / 103) * (2 * (1 / Real.logb 2 (Real.logb 2 Dstar))) =
            30.4 * EG.epsC / (103 * Real.logb 2 (Real.logb 2 Dstar)) by field_simp; ring]
          gcongr; norm_num
  have hOV := EG.Todo.OVRun V G Dstar run hD.gamma2a hv
  have hn : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
  refine ⟨hsum, ?_, ?_⟩
  · push_cast
    calc ∑ l ∈ Finset.Icc 1 run.R, ((run.D G l).card : ℝ)
        ≤ ∑ l ∈ Finset.Icc 1 run.R, 15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ) * G.card := by
          apply Finset.sum_le_sum
          intro l hl
          obtain ⟨-, -, -, hK1, hK2, -⟩ := hOV l hl
          obtain ⟨h1, h2⟩ := hlogP l hl
          have hPp : 0 < Real.logb 2 (run.P G l : ℝ) := by nlinarith
          have hK1' : ((run.D G l).card : ℝ) ≤ run.dup G l := by exact_mod_cast hK1
          have : 7.6 * EG.epsC * (G.card : ℝ) / Real.logb 2 (run.P G l : ℝ) ≤
              15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ) * G.card := by
            rw [div_mul_eq_mul_div]
            apply div_le_div_of_nonneg_right _ hPp.le
            nlinarith
          linarith
      _ = (∑ l ∈ Finset.Icc 1 run.R, 15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ)) * G.card := by
          rw [Finset.sum_mul]
      _ ≤ EG.HB.epsA Dstar * G.card := mul_le_mul_of_nonneg_right hsum hn
  · push_cast
    calc ∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, ((run.hubs G l a).card : ℝ)
        ≤ ∑ l ∈ Finset.Icc 1 run.R, 15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ) * G.card := by
          apply Finset.sum_le_sum
          intro l hl
          obtain ⟨-, -, -, -, -, hK3, hK4, hK5, -⟩ := hOV l hl
          have : ((∑ a ∈ run.Std G l, (run.hubs G l a).card : ℕ) : ℝ) ≤
              ((2 * run.dup G l : ℕ) : ℝ) := by exact_mod_cast hK3.trans hK4
          push_cast at this hK5
          rw [div_mul_eq_mul_div]
          linarith
      _ = (∑ l ∈ Finset.Icc 1 run.R, 15.2 * EG.epsC / Real.logb 2 (run.P G l : ℝ)) * G.card := by
          rw [Finset.sum_mul]
      _ ≤ EG.HB.epsA Dstar * G.card := mul_le_mul_of_nonneg_right hsum hn

end EG.Todo
