module

public import EG.Spec.Quot.UHsplit
public import EG.Lib.Quot.Det
public import EG.Lib.Quot.ConstNonneg
public import EG.Lib.Lend.Standing
public import EG.Lib.Stage1.Pool
public import EG.Lib.Found.Gamma
public import EG.Proof.HB.TowerBM
public import EG.Proof.Todo.TowerE
public import EG.Proof.Todo.LacunaryRun
public import EG.Proof.Todo.LacunaryExamples

/-!
# P3 stub: `EG.Spec.UHsplitDetStatement` (s7:lemUHsplit)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UHsplitDet`; consumers import this module.

Proof (manuscript s7:lemUHsplit (iv)): `Σ_l 3|D_l| ≤ 3ε_A n` (Lemma s2:lemTower(e),
`EG.Todo.TowerE`); `Σ_l 30n/M_l ≤ 60n/D_*` (Lemma s2:lemTower(b), `EG.towerBM`); the remaining
terms of `det_l` are at most `nF(λ_{l-2})` (`EG.Quot.det_tail_le`, with `M_l ≤ λ_{l-2}^{1.6}` from
`EG.towerBM`); and, writing `F = 624x^{-90.2} + 320(95 log₂x + 8)x^{-90.2}` (two functions of
Lemma s2:lemLacunary(iv), `EG.Todo.LacunaryExamples`), Lemma s2:lemLacunary(iii)
(`EG.Todo.LacunaryRun`) gives `Σ_l F(λ_{l-2}) ≤ 2F(λ_{R-2}) ≤ 2F(log₂D_*)` (`F` non-increasing,
`λ_{R-2} ≥ log₂D_*`). Finally `2F(log₂D_*) < 2^{-1000}` as `log₂D_* ≥ 2^{256}` (Γ1(a);
`EG.Quot.two_FQ_lt`).
-/

public section

namespace EG.Todo

open EG.HB EG.Quot

/-- Proved in P3. [s7:lemUHsplit] see `EG.Spec.UHsplitDetStatement`. -/
theorem UHsplitDet : EG.Spec.UHsplitDetStatement := by
  intro V _ G N0 Dstar run hR
  obtain ⟨hΓ1, -, -, -, hd1, hrun⟩ := hR
  have hΓ := hΓ1.1
  have hD2 : 2 < Dstar := hΓ.two_lt
  have hD4 : (4 : ℝ) ≤ Dstar := le_trans (by norm_num) hΓ.gamma2a
  have hlogD : (2 : ℝ) ^ 256 ≤ Real.logb 2 Dstar := hΓ.two_pow_256_le_logb
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hFQ0 : 0 ≤ FQ (Real.logb 2 Dstar) := FQ_nonneg (le_trans (by norm_num) hlogD)
  have hBM := EG.towerBM V G Dstar run hΓ hrun hd1
  -- the three parts of `det_l`
  set T : ℕ → ℝ := fun l =>
    78 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l +
      320 * (G.card : ℝ) * (run.M G l : ℝ) ^ 3 * (Real.logb 2 (thult run G l : ℝ) + 8) /
        run.lam G (l - 2) ^ 95 with hT
  have hdet : ∀ l, detl run G l =
      3 * ((run.D G l).card : ℝ) + 30 * (G.card : ℝ) / (run.M G l : ℝ) + T l := by
    intro l; unfold detl; rw [hT]; ring
  rw [Finset.sum_congr rfl fun l _ => hdet l, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- `Σ_l 3|D_l| ≤ 3ε_A n`
  have h1 : ∑ l ∈ Finset.Icc 3 run.R, 3 * ((run.D G l).card : ℝ) ≤ 3 * epsA Dstar * (G.card : ℝ) := by
    have hE := (Todo.TowerE V G Dstar run hΓ hrun hd1).2.1
    push_cast at hE
    rw [← Finset.mul_sum, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc (by norm_num : 1 ≤ 3) le_rfl) (fun _ _ _ => by positivity)).trans hE)
      (by norm_num)
  -- `Σ_l 30n/M_l ≤ 60n/D_*`
  have h2 : ∑ l ∈ Finset.Icc 3 run.R, 30 * (G.card : ℝ) / (run.M G l : ℝ) ≤
      60 * (G.card : ℝ) / Dstar := by
    have hM : ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) ≤ 2 / Dstar :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num : 1 ≤ 3) le_rfl)
        (fun _ _ _ => by positivity)).trans hBM.2
    have e : ∑ l ∈ Finset.Icc 3 run.R, 30 * (G.card : ℝ) / (run.M G l : ℝ) =
        30 * (G.card : ℝ) * ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [e]
    calc 30 * (G.card : ℝ) * ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ)
        ≤ 30 * (G.card : ℝ) * (2 / Dstar) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 60 * (G.card : ℝ) / Dstar := by ring
  -- the remaining terms: `T_l ≤ n F(λ_{l-2})`
  have hTl : ∀ l ∈ Finset.Icc 3 run.R, T l ≤ (G.card : ℝ) * FQ (run.lam G (l - 2)) := by
    intro l hl
    obtain ⟨hl3, hlR⟩ := Finset.mem_Icc.1 hl
    have hlam : (2 : ℝ) ^ 256 ≤ run.lam G (l - 2) :=
      Standing.lam_ge hΓ1 hrun ⟨by omega, by omega⟩
    have hM1 : (1 : ℝ) ≤ (run.M G l : ℝ) := by
      have := Stage1.two_pow_le_M G run l
      exact_mod_cast le_trans Nat.one_le_two_pow this
    have hMlam := (hBM.1 l hl3 hlR)
    have hθ : (thult run G l : ℝ) ≤
        (run.M G l : ℝ) * (run.lam G (l - 2) ^ 95 / (8 * (run.M G l : ℝ) ^ 2)) / 7 :=
      Nat.floor_le (by
        have h0 : 0 < run.lam G (l - 2) := lt_of_lt_of_le (by positivity) hlam
        have hL : 0 < run.lam G (l - 2) ^ 95 := pow_pos h0 95
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hL.le (by positivity)))
          (by norm_num))
    exact det_tail_le hn hM1 (le_trans (by norm_num) hlam) (hMlam.1.trans hMlam.2) hθ
  -- the lacunary sum
  have h3 : ∑ l ∈ Finset.Icc 3 run.R, T l ≤ 2 * FQ (Real.logb 2 Dstar) * (G.card : ℝ) := by
    refine (Finset.sum_le_sum hTl).trans ?_
    rw [← Finset.mul_sum]
    rcases lt_or_ge run.R 3 with hR3 | hR3
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; nlinarith
    · have hex := Todo.LacunaryExamples Dstar hΓ
      obtain ⟨hH1, hA1, hN1⟩ := hex.1 90.2 (by norm_num)
      obtain ⟨hH2, hA2, hN2⟩ := hex.2.2.1 90.2 (by norm_num)
      have hL1 := (Todo.LacunaryRun V G Dstar run (fun x => x ^ (-(90.2 : ℝ))) hΓ hrun
        (by omega) hN1 hH1).2.2 hR3
      have hL2 := (Todo.LacunaryRun V G Dstar run
        (fun x => (95 * Real.logb 2 x + 8) * x ^ (-(90.2 : ℝ))) hΓ hrun (by omega) hN2 hH2).2.2 hR3
      -- `λ_{R-2} ≥ log₂D_*`
      have hlamR : Real.logb 2 Dstar ≤ run.lam G (run.R - 2) := by
        obtain ⟨hμ, hpos, -⟩ := Standing.lam_facts hΓ1 hrun (l := run.R - 2) ⟨by omega, by omega⟩
        have hlD : 0 < Real.logb 2 Dstar := Real.logb_pos (by norm_num) (by linarith)
        exact (Real.logb_le_logb (by norm_num) hlD hpos).1 hμ
      have hm1 := hA1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hlamR) hlamR
      have hm2 := hA2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hlamR) hlamR
      simp only at hL1 hL2 hm1 hm2
      have hsum : ∑ l ∈ Finset.Icc 3 run.R, FQ (run.lam G (l - 2)) =
          624 * ∑ l ∈ Finset.Icc 3 run.R, run.lam G (l - 2) ^ (-(90.2 : ℝ)) +
            320 * ∑ l ∈ Finset.Icc 3 run.R,
              (95 * Real.logb 2 (run.lam G (l - 2)) + 8) * run.lam G (l - 2) ^ (-(90.2 : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => FQ_eq_comb _
      have hF : ∑ l ∈ Finset.Icc 3 run.R, FQ (run.lam G (l - 2)) ≤ 2 * FQ (Real.logb 2 Dstar) := by
        rw [hsum, FQ_eq_comb]
        nlinarith
      have := mul_le_mul_of_nonneg_left hF hn
      linarith
  refine ⟨?_, two_FQ_lt hlogD⟩
  linarith

end EG.Todo
