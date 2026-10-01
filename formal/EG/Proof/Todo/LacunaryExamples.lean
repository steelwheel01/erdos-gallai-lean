module

public import EG.Spec.HB.Lacunary
public import EG.Lib.HB.LacunaryEx

/-!
# P3 stub: `EG.Spec.LacunaryExamplesStatement` (s2:lemLacunary)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.LacunaryExamples`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemLacunary] see `EG.Spec.LacunaryExamplesStatement`. -/
theorem LacunaryExamples : EG.Spec.LacunaryExamplesStatement := by
  intro Dstar hD
  have hX0 : EG.HB.LacX (Real.logb 2 Dstar) := EG.HB.LacX.of_gamma hD le_rfl
  have hx0 := hX0.pos
  have h8 : 8 ≤ Real.logb 2 Dstar := by
    have := hX0.lin_le (a := 8) (b := 0) (by norm_num) le_rfl (by norm_num); linarith
  have hlog : 4 * Real.logb 2 (Real.logb 2 Dstar) ≤ Real.logb 2 Dstar := by
    have := hX0.lin_le (a := 0) (b := 4) le_rfl (by norm_num) (by norm_num); linarith
  refine ⟨fun a ha => ⟨EG.HB.hypH_rpow_neg hD ha, EG.HB.antitoneOn_rpow_neg hD ha,
      EG.HB.rpow_neg_nonneg' hD⟩,
    ⟨EG.HB.hypH_inv_logb hD, EG.HB.antitoneOn_inv_logb hD, EG.HB.inv_logb_nonneg hD⟩,
    fun b hb => ⟨EG.HB.hypH_log95 hD hb, EG.HB.antitoneOn_log95 hD hb, EG.HB.log95_nonneg hD⟩,
    fun x hx => EG.HB.logStar_identity (by linarith), ?_⟩
  intro η hη
  have hpos := EG.HB.logStar_fn_nonneg hD η hη
  have hnn : ∀ x : ℝ, Real.logb 2 Dstar ≤ x →
      0 ≤ (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / η x := by
    intro x hx
    have := EG.HB.four_le_numer (x := x) (by linarith)
    exact div_nonneg (by linarith) (hpos x hx).le
  rcases hη with rfl | rfl | rfl
  · refine ⟨EG.HB.hypH_logStar_id hD, hnn, ?_⟩
    exact EG.HB.logStar_fn_le_two hx0 (fun x => x) hpos (fun x hx => hx)
      (EG.HB.claim_id h8)
  · refine ⟨EG.HB.hypH_logStar_sqrt hD, hnn, ?_⟩
    exact EG.HB.logStar_fn_le_two hx0 (fun x => x ^ (1 / 2 : ℝ)) hpos
      (fun x hx => Real.rpow_le_rpow hx0.le hx (by norm_num)) (EG.HB.claim_sqrt h8)
  · refine ⟨EG.HB.hypH_logStar_log hD, hnn, ?_⟩
    exact EG.HB.logStar_fn_le_two hx0 (fun x => Real.logb 2 x) hpos
      (fun x hx => Real.logb_le_logb_of_le (by norm_num) hx0 hx) (EG.HB.claim_log h8 hlog)

end EG.Todo
