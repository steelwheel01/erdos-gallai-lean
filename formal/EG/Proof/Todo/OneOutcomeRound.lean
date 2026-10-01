module

public import EG.Spec.Quot.OneOutcome
public import EG.Lib.Quot.RoundExist
public import EG.Proof.Todo.UHsplitRound
public import EG.Proof.Todo.Pay

/-!
# P3 stub: `EG.Spec.OneOutcomeRoundStatement` (s7:lemOneOutcome)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.OneOutcomeRound`; consumers import this module.

Proof (manuscript s7:lemOneOutcome (iii)): the event of Construction s7:consRound (f) has
probability `≥ 1/2` by Markov (`EG.Quot.Rules.exists_markovEvent`), so it contains an outcome of
positive weight. On the event, `copies_l ≤ 4E[copies_l|Past_l] ≤ 4(X_{V,l} + det_l)` by
Lemma s7:lemUHsplit (ii) (`EG.Todo.UHsplitRound`), and the bound on `pay^rd_l` is Lemma
s7:lemPay (d) (`EG.Todo.Pay`).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- Proved in P3. [s7:lemOneOutcome] see `EG.Spec.OneOutcomeRoundStatement`. -/
theorem OneOutcomeRound : EG.Spec.OneOutcomeRoundStatement := by
  intro V _ G N0 Dstar run δ hR hδ ω hω l hl3 hlR J hJ I hI R hRv
  refine ⟨R.exists_markovEvent, fun ξ hξ => ⟨?_, ?_⟩⟩
  · have hE := Todo.UHsplitRound V G N0 Dstar run δ hR hδ ω hω l hl3 hlR J hJ I hI R hRv
    calc (R.copies ξ : ℝ) ≤ 4 * (roundLaw I.G I.M).expect (fun ξ' => (R.copies ξ' : ℝ)) := hξ.1
      _ ≤ 4 * ((XVl run G ω.pool l : ℝ) + detl run G l) := by linarith
  · exact (Todo.Pay V G N0 Dstar run δ hR hδ ω hω l hl3 hlR J hJ I hI R hRv).2.2.2.2.2.2.2.2.2.1 ξ hξ

end EG.Todo
