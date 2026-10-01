module

public import EG.Spec.HB.Parentless
public import EG.Proof.HB.Structure
public import EG.Proof.HB.CapPrePart
public import EG.Proof.Todo.TowerBRest
public import EG.Lib.HB.TowerRun

/-!
# P3 stub: `EG.Spec.AdmissibleParentStatement` (s2:propParentless)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.AdmissibleParent`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propParentless] see `EG.Spec.AdmissibleParentStatement`. -/
theorem AdmissibleParent : EG.Spec.AdmissibleParentStatement := by
  intro V _ G Dstar run hD hv Y hY Z hZ hYZ
  obtain ⟨hYp, hYl⟩ := (EG.HB.Run.mem_lightParts run G).1 hY
  obtain ⟨hZp, hZl⟩ := (EG.HB.Run.mem_lightParts run G).1 hZ
  have hYr := EG.HB.Run.isRound_of_mem_prePartAddrs hYp
  have hZr := EG.HB.Run.isRound_of_mem_prePartAddrs hZp
  have hYR : Y.1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hYr
  have hZR : Z.1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hZr
  have hZ2 : Z.1 - 2 ∈ Finset.Icc 1 run.R :=
    Finset.mem_Icc.2 ⟨by have := hYr.1; omega, by have := hZr.2; omega⟩
  -- (1) `|Y| ≥ P_r/2`
  have h1 := ((EG.structureVertex V G Dstar run hv Y.1 hYR).2.1 Y.2 hYp hYl)
  -- (2) `P_r ≥ P_{l-2}`
  have h2 : (run.P G (Z.1 - 2) : ℝ) ≤ (run.P G Y.1 : ℝ) := by
    have hp2 := EG.HB.Run.paramHyp hD hv hZ2
    have hdd : run.d G (Z.1 - 2) ≤ run.d G Y.1 := EG.HB.Run.d_anti run G (by omega)
    have hl : Real.logb 2 (run.d G (Z.1 - 2)) ≤ Real.logb 2 (run.d G Y.1) :=
      Real.logb_le_logb_of_le (by norm_num) hp2.d_pos hdd
    have : run.P G (Z.1 - 2) ≤ run.P G Y.1 := by
      apply Nat.ceil_mono
      exact pow_le_pow_left₀ hp2.lam_pos.le hl _
    exact_mod_cast this
  -- (3) `P_{l-2}/2 ≥ M_l log⁴ M_l`
  have h3 := (EG.Todo.TowerBRest V G Dstar run hD hv (by
    exact (hv.1 1 (Finset.mem_Icc.2 ⟨le_rfl, le_trans hYr.1 hYr.2⟩)).1)).1 Z.1 (by have := hYr.1; omega) hZr.2
  -- (4) `|Z| L_Z^4 ≤ M_l log⁴ M_l`
  have hcap := ((EG.capPrePart V G Dstar run hD.gamma2a hv Z.1 hZR).2 Z.2 hZp).1
  have hZcard : (run.ancVerts G Z).card ≤ run.M G Z.1 :=
    (Finset.card_le_card (EG.HB.Run.partVerts_subset_Z0 run G Z.1 Z.2)).trans hcap
  have hM0 : (0 : ℝ) ≤ run.M G Z.1 := Nat.cast_nonneg _
  have hLZ : 0 ≤ run.LY G Z ∧ run.LY G Z ≤ Real.logb 2 (run.M G Z.1 : ℝ) := by
    unfold EG.HB.Run.LY
    rcases Nat.eq_zero_or_pos (run.ancVerts G Z).card with h0 | h0
    · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero, le_refl, true_and]
      have hp := EG.HB.Run.paramHyp hD hv hZR
      exact hp.Lam_pos.le
    · have h1' : (1 : ℝ) ≤ (run.ancVerts G Z).card := by exact_mod_cast h0
      exact ⟨Real.logb_nonneg (by norm_num) h1', Real.logb_le_logb_of_le (by norm_num)
        (by linarith) (by exact_mod_cast hZcard)⟩
  have h4 : run.LY G Z ^ 4 ≤ Real.logb 2 (run.M G Z.1 : ℝ) ^ 4 := pow_le_pow_left₀ hLZ.1 hLZ.2 4
  have hc : ((run.ancVerts G Z).card : ℝ) ≤ run.M G Z.1 := by exact_mod_cast hZcard
  refine ⟨h1.2.trans h1.1, by linarith, h3, ?_⟩
  exact mul_le_mul hc h4 (by positivity) hM0

end EG.Todo
