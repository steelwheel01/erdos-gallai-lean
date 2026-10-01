module

public import EG.Spec.Quot.Pay
public import EG.Lib.Quot.PayRun

/-!
# P3 stub: `EG.Spec.PayStatement` (s7:lemPay)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.Pay`; consumers import this module.

Proof (manuscript s7:lemPay). The past `I = pastOf run G δ ω l J` of a stage-1 outcome of positive
weight is a valid round input (`EG.Quot.pastOf_valid`, from Lemma J⁺ and s7:lemCand (iv)). Then
(a1) `card_Jlost_le`, (a2) `card_paidPool_le`, (a3) `card_paidJVBad_le`, (b)
`card_unpairedLegs_filter_le`, `card_unpairedLegs_le`, (c) `expect_sdrPaid_le` (Lemma s7:lemWellDef
(iii)), `expect_loopPaid_le` (Lemma s7:lemWellDef (v) and independence of the orders at distinct
ports), `card_parObjs_le'` (`#PAR objects ≤ n(M_l − 1) ≤ 1.37 nM_l`); (d) the Markov event of
(f) and (c), with `Hcd_l ≥ 2^{10}M_l^{10}` (s7:lemCand (iv)) for the numerical step; (e) is the
definition of the paid set (`rfl`).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot EG.FinDist Finset

/-- Proved in P3. [s7:lemPay] see `EG.Spec.PayStatement`. -/
theorem Pay : EG.Spec.PayStatement := by
  intro V _ G N0 Dstar run δ hR hδ ω hω l hl hlR J hJ I hIeq R hRv
  subst hIeq
  have hI := pastOf_valid hω hR hδ hl hlR hJ
  -- constants
  have hM1n : 1 ≤ run.M G l := le_trans (by norm_num) (Stage1.two_pow_le_M G run l)
  have hM40 : (2 : ℝ) ^ 40 ≤ (run.M G l : ℝ) := by exact_mod_cast Stage1.two_pow_le_M G run l
  have hM1 : (1 : ℝ) ≤ (run.M G l : ℝ) := le_trans (by norm_num) hM40
  have hM0 : (0 : ℝ) < (run.M G l : ℝ) := by linarith
  have hMc : ((run.M G l - 1 : ℕ) : ℝ) = (run.M G l : ℝ) - 1 := by
    rw [Nat.cast_sub hM1n, Nat.cast_one]
  have hHge : (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 ≤ Hcd run G l := hI.Hcd_ge
  have hH : 0 < Hcd run G l := lt_of_lt_of_le (by positivity) hHge
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  -- (c) numerical steps
  have hc2 : (G.card : ℝ) * ((run.M G l : ℝ) - 1) / (4 * (run.M G l : ℝ)) ^ 4 ≤
      (G.card : ℝ) / (256 * (run.M G l : ℝ) ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 0 ≤ (G.card : ℝ) * (run.M G l : ℝ) ^ 3 := by positivity
    nlinarith
  have hpar : (R.parObjs.card : ℝ) ≤ (G.card : ℝ) * ((run.M G l : ℝ) - 1) := by
    have := card_parObjs_le' hI hRv
    rw [← hMc]
    exact_mod_cast this
  have hc4 : 2 * (2 / Hcd run G l) * (R.parObjs.card : ℝ) ≤
      5.5 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l := by
    have e : 2 * (2 / Hcd run G l) * (R.parObjs.card : ℝ) =
        4 * (R.parObjs.card : ℝ) / Hcd run G l := by ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hH.le
    nlinarith
  have hsdr := expect_sdrPaid_le hI hRv
  have hloop := expect_loopPaid_le hI hRv
  have hsdr' : (roundLaw (pastOf run G δ ω l J).G (pastOf run G δ ω l J).M).expect
      (fun ξ => ((R.sdrPaid ξ.1).card : ℝ)) ≤
      (G.card : ℝ) * ((run.M G l : ℝ) - 1) / (4 * (run.M G l : ℝ)) ^ 4 := hsdr
  have hloop' : (roundLaw (pastOf run G δ ω l J).G (pastOf run G δ ω l J).M).expect
      (fun ξ => ((R.loopPaid ξ).card : ℝ)) ≤ 2 * (2 / Hcd run G l) * (R.parObjs.card : ℝ) :=
    hloop
  refine ⟨?_, card_paidPool_le hJ hI, ?_, fun x hx => card_unpairedLegs_filter_le hI hRv hx,
    (card_unpairedLegs_le (R := R)).trans card_freshCentres_le, hsdr, hc2, hloop, hc4, ?_, ?_,
    fun ξ => rfl⟩
  · -- (a1)
    have h := card_Jlost_le hI
    have h' : ((pastOf run G δ ω l J).Jlost.card : ℝ) ≤
        ((lostRound run G δ (stageOf ω) l).card : ℝ) * (((run.M G l - 1 : ℕ)) : ℝ) := by
      exact_mod_cast h
    rw [hMc] at h'
    linarith
  · -- (a3)
    have h := card_paidJVBad_le hI
    have h' : ((pastOf run G δ ω l J).paidJVBad.card : ℝ) ≤
        ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ) * (((run.M G l - 1 : ℕ)) : ℝ) := by
      exact_mod_cast h
    rw [hMc] at h'
    linarith
  · -- (d), per round
    intro ξ hξ
    have hE : (roundLaw (pastOf run G δ ω l J).G (pastOf run G δ ω l J).M).expect
        (fun ξ' => (R.payrd ξ' : ℝ)) ≤
        (G.card : ℝ) / (256 * (run.M G l : ℝ) ^ 3) +
          5.5 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l := by
      have h1 : (roundLaw (pastOf run G δ ω l J).G (pastOf run G δ ω l J).M).expect
          (fun ξ' => (R.payrd ξ' : ℝ)) ≤
          (roundLaw (pastOf run G δ ω l J).G (pastOf run G δ ω l J).M).expect
            (fun ξ' => ((R.sdrPaid ξ'.1).card : ℝ) +
            ((R.loopPaid ξ').card : ℝ)) := by
        refine expect_mono _ fun ξ' => ?_
        unfold Rules.payrd
        exact_mod_cast card_union_le _ _
      rw [expect_add] at h1
      linarith
    have := hξ.2
    linarith
  · -- (d), the numerical step
    have h1 : 4 * ((G.card : ℝ) / (256 * (run.M G l : ℝ) ^ 3)) ≤ (G.card : ℝ) / (run.M G l : ℝ) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) hM0]
      have h3 : (run.M G l : ℝ) ≤ (run.M G l : ℝ) ^ 3 := by
        calc (run.M G l : ℝ) = (run.M G l : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (run.M G l : ℝ) ^ 3 := pow_le_pow_right₀ hM1 (by norm_num)
      nlinarith
    have h2 : 4 * (5.5 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l) ≤
        (G.card : ℝ) / (run.M G l : ℝ) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hH hM0]
      have h22 : 22 * (run.M G l : ℝ) ^ 2 ≤ Hcd run G l := by
        have h10 : (run.M G l : ℝ) ^ 2 ≤ (run.M G l : ℝ) ^ 10 :=
          pow_le_pow_right₀ hM1 (by norm_num)
        nlinarith
      nlinarith
    have e : 2 * (G.card : ℝ) / (run.M G l : ℝ) =
        (G.card : ℝ) / (run.M G l : ℝ) + (G.card : ℝ) / (run.M G l : ℝ) := by ring
    rw [e, mul_add]
    linarith

end EG.Todo
