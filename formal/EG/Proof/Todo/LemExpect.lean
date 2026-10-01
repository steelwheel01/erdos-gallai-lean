module

public import EG.Spec.Light.Expect
public import EG.Spec.Light.E1
public import EG.Spec.HB.OVRunK
public import EG.Spec.HB.Lacunary
public import EG.Proof.Todo.LemE1
public import EG.Proof.HB.OVRunK
public import EG.Proof.Todo.LacunaryRun
public import EG.Proof.Todo.LacunaryExamples
public import EG.Proof.Light.Setting
public import EG.Lib.Light.ExpectAux
public import EG.Lib.Light.Constants
public import EG.Lib.HB.TowerRun
public import EG.Lib.Gamma.Full

/-!
# P3 stub: `EG.Spec.LemExpectStatement` (s5:lemExpect)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.LemExpect`; consumers import this module.

Proof (P3), as in `s5.tex`: linearity (`EG.Light.expect_dem_lp_eq`); Lemma s5:lemE1 (b), (c)
(`EG.Todo.LemE1`) and (s5:eqLY) (`EG.eqLY`, declared input of probe P4B) bound the term of a light
part `Y` of round `r` by `898 λ_r^{-103} log₂λ_r` (`EG.Light.term_le`); Proposition s2:propOV (K1)
(`EG.ovK1`: at most `1.37 n/P_r` ancestors of round `r`, `P_r ≥ λ_r^{103}`) bounds round `r` by
`1231 n λ_r^{-205}` (`EG.Light.round_le`); Lemma s2:lemLacunary (iii), (iv) (`EG.Todo.LacunaryRun`,
`EG.Todo.LacunaryExamples` with `F(x) = x^{-205}`) give `Σ_{r≤R} λ_r^{-205} ≤ 2 (log₂D_*)^{-205}`.
-/

public section

namespace EG.Todo

open EG.HB EG.Stage1 EG.Light Real

/-- Proved in P3. [s5:lemExpect] see `EG.Spec.LemExpectStatement`. -/
theorem LemExpect : EG.Spec.LemExpectStatement := by
  classical
  intro V _ G N0 Dstar run hR
  have hD : Gamma1core Dstar := hR.1.1
  have hv : run.Valid G Dstar := hR.2.2.2.2.2
  have hLY := EG.eqLY V G N0 Dstar run hR
  have hE1 := EG.Todo.LemE1 V G N0 Dstar run hR
  have hK1 := (EG.ovK1 V G Dstar run hR.1.gamma2a hv).1
  set μ := Stage1.law G run with hμ
  set n : ℝ := (G.card : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set L : ℕ → ℝ := fun r => logb 2 (run.lam G r) with hL
  set g : ℕ → ℝ := fun r => 898 * L r / run.lam G r ^ 103 with hg
  have hround : ∀ Y ∈ run.lightParts G, Y.1 ∈ Finset.Icc 1 run.R := fun Y hY =>
    Finset.mem_Icc.2 (Run.isRound_of_mem_parts run G (Finset.mem_filter.1 hY).1)
  have hpar : ∀ r ∈ Finset.Icc 1 run.R, ParamHyp (run.d G r) := fun r hr => Run.paramHyp hD hv hr
  have hlampos : ∀ r ∈ Finset.Icc 1 run.R, 0 < run.lam G r := fun r hr => (hpar r hr).lam_pos
  have hL1 : ∀ r ∈ Finset.Icc 1 run.R, 1 ≤ L r := fun r hr =>
    le_trans (by norm_num) (hpar r hr).mu_ge
  have hLlam : ∀ r ∈ Finset.Icc 1 run.R, L r ≤ run.lam G r := by
    intro r hr
    have hc := (hpar r hr).mu_cube_le
    have h1 := hL1 r hr
    have hLr : L r = logb 2 (logb 2 (run.d G r)) := rfl
    have hlr : run.lam G r = logb 2 (run.d G r) := rfl
    rw [hLr, hlr]
    rw [hLr] at h1
    set x := logb 2 (logb 2 (run.d G r))
    have hx3 : x ≤ x ^ 3 := by
      have e : x ^ 3 = x * (x * x) := by ring
      rw [e]; nlinarith
    nlinarith
  -- linearity
  rw [expect_dem_lp_eq]
  -- the term of one light part
  have hterm : ∀ Y ∈ run.lightParts G,
      80 * ((run.ancVerts G Y).card : ℝ) * μ.prob {ω' | demoted ω' Y} +
          369 * (((run.ancVerts G Y).card : ℝ) * ((run.R - Y.1 : ℕ) : ℝ)) *
            μ.prob {ω' | Y ∈ Bad ω'} ≤ g Y.1 := by
    intro Y hY
    have hr := hround Y hY
    obtain ⟨h1, h2, -, -, h5, h6, -⟩ := hLY Y hY
    obtain ⟨-, hb, hc⟩ := hE1 Y hY
    have hrR : Y.1 ≤ run.R := (Finset.mem_Icc.1 hr).2
    have hcpos : (0 : ℝ) ≤ ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) := by positivity
    refine term_le (by linarith) (hlampos _ hr) (Nat.cast_nonneg _) ?_ (hL1 _ hr)
      (FinDist.prob_nonneg _ _) (by linarith) (FinDist.prob_nonneg _ _) hc
    rw [Nat.cast_sub hrR]
    exact h5.trans h6
  -- the count of the light parts of one round
  have hcount : ∀ r ∈ Finset.Icc 1 run.R,
      (((run.lightParts G).filter (fun Y => Y.1 = r)).card : ℝ) ≤ 1.37 * n / (run.P G r : ℝ) := by
    intro r hr
    refine le_trans ?_ (hK1 r hr).2.2
    exact_mod_cast Finset.card_le_card fun Y hY => by
      obtain ⟨hY, hYr⟩ := Finset.mem_filter.1 hY
      exact Finset.mem_filter.2 ⟨(Run.mem_ancestors run G).2
        ((Run.mem_parts run G).1 (Finset.mem_filter.1 hY).1), hYr⟩
  have hPge : ∀ r ∈ Finset.Icc 1 run.R, run.lam G r ^ 103 ≤ (run.P G r : ℝ) := by
    intro r hr
    have := ParamHyp.P_ge (d := run.d G r)
    have e : Cp = 103 := rfl
    rw [e] at this
    exact this
  -- the lacunary sum
  set F : ℝ → ℝ := fun x => x ^ (-(205 : ℝ)) with hF
  obtain ⟨hH, hanti, hF0⟩ := (EG.Todo.LacunaryExamples Dstar hD).1 205 (by norm_num)
  have hDpos : 0 < Dstar := by linarith [hD.1]
  have hlac : ∑ r ∈ Finset.Icc 1 run.R, F (run.lam G r) ≤ 2 * F (logb 2 Dstar) := by
    rcases Nat.eq_zero_or_pos run.R with h0 | h0
    · rw [h0]
      simp only [Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty]
      have := hF0 (logb 2 Dstar) le_rfl
      linarith
    · have h1 := (EG.Todo.LacunaryRun V G Dstar run F hD hv h0 hF0 hH).1
      have hdR : Dstar ≤ run.d G run.R := hv.dstar_le run G ⟨h0, le_rfl⟩
      have hlR : logb 2 Dstar ≤ run.lam G run.R :=
        Real.logb_le_logb_of_le (by norm_num) hDpos hdR
      have h2 : F (run.lam G run.R) ≤ F (logb 2 Dstar) :=
        hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hlR) hlR
      linarith
  calc ∑ Y ∈ run.lightParts G,
        (80 * ((run.ancVerts G Y).card : ℝ) * μ.prob {ω' | demoted ω' Y} +
          369 * (((run.ancVerts G Y).card : ℝ) * ((run.R - Y.1 : ℕ) : ℝ)) *
            μ.prob {ω' | Y ∈ Bad ω'})
      ≤ ∑ Y ∈ run.lightParts G, g Y.1 := Finset.sum_le_sum hterm
    _ = ∑ r ∈ Finset.Icc 1 run.R, ∑ Y ∈ (run.lightParts G).filter (fun Y => Y.1 = r), g Y.1 :=
        (Finset.sum_fiberwise_of_maps_to hround _).symm
    _ = ∑ r ∈ Finset.Icc 1 run.R,
          (((run.lightParts G).filter (fun Y => Y.1 = r)).card : ℝ) * g r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_congr rfl fun Y hY => by rw [(Finset.mem_filter.1 hY).2], Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ r ∈ Finset.Icc 1 run.R, 1231 * n * (run.lam G r ^ 205)⁻¹ := by
        refine Finset.sum_le_sum fun r hr => ?_
        exact round_le (hcount r hr) (hPge r hr) (hlampos r hr)
          (le_trans zero_le_one (hL1 r hr)) (hLlam r hr) hn0
    _ = 1231 * n * ∑ r ∈ Finset.Icc 1 run.R, F (run.lam G r) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [hF]
        simp only
        rw [Real.rpow_neg (hlampos r hr).le]
        norm_cast
    _ ≤ 1231 * n * (2 * F (logb 2 Dstar)) := mul_le_mul_of_nonneg_left hlac (by positivity)
    _ = epsU Dstar * n := by
        rw [epsU_eq, hF]
        simp only
        have : (-(205 : ℝ)) = (((-205 : ℤ)) : ℝ) := by norm_num
        rw [this, Real.rpow_intCast]
        ring

end EG.Todo
