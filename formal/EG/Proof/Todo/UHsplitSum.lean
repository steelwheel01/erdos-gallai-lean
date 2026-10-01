module

public import EG.Spec.Quot.UHsplit
public import EG.Proof.Todo.UHsplitRound
public import EG.Lib.Quot.Round
public import EG.Lib.Quot.Xprime

/-!
# P3 stub: `EG.Spec.UHsplitSumStatement` (s7:lemUHsplit)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UHsplitSum`; consumers import this module.

Proof (manuscript s7:lemUHsplit (iii)): on the event of Construction s7:consRound (f),
`|V(Q_l)| = copies_l ≤ 4E[copies_l|Past_l] ≤ 4(X_{V,l} + det_l)` by (ii) (`EG.Todo.UHsplitRound`);
summing, `Σ_l |V(Q_l)| ≤ 4X_V + 4Σ_l det_l ≤ 4X' + 4Σ_l det_l ≤ 12 E X' + 4Σ_l det_l`.
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- Proved in P3. [s7:lemUHsplit] see `EG.Spec.UHsplitSumStatement`. -/
theorem UHsplitSum : EG.Spec.UHsplitSumStatement := by
  intro V _ G N0 Dstar run δ hR hδ ω hω hX Js hJs Rs hRs ξs hξ
  -- per round: `|V(Q_l)| ≤ 4(X_{V,l} + det_l)`
  have hl : ∀ l ∈ Finset.Icc 3 run.R,
      (((Rs l).Q (ξs l)).card : ℝ) ≤ 4 * ((XVl run G ω.pool l : ℝ) + detl run G l) := by
    intro l hlI
    obtain ⟨hl3, hlR⟩ := Finset.mem_Icc.1 hlI
    have hE := Todo.UHsplitRound V G N0 Dstar run δ hR hδ ω hω l hl3 hlR (Js l) (hJs l hlI)
      (pastOf run G δ ω l (Js l)) rfl (Rs l) (hRs l hlI)
    have hM := (hξ l hlI).1
    have hc : (((Rs l).Q (ξs l)).card : ℝ) = ((Rs l).copies (ξs l) : ℝ) := rfl
    rw [hc]
    linarith
  have hsum := Finset.sum_le_sum hl
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  -- `Σ_l X_{V,l} = X_V ≤ X'`
  have hXV : ∑ l ∈ Finset.Icc 3 run.R, (XVl run G ω.pool l : ℝ) ≤ (XprimeOf run G δ ω : ℝ) := by
    have h1 : ∑ l ∈ Finset.Icc 3 run.R, (XVl run G ω.pool l : ℝ) = (XV run G ω.pool : ℝ) := by
      unfold XV; push_cast; rfl
    rw [h1]
    exact_mod_cast XV_le_Xprime run G δ (stageOf ω) ω.pool
  linarith

end EG.Todo
