module

public import EG.Spec.Quot.OneOutcome
public import EG.Lib.Prob.Basic

/-!
# P3 stub: `EG.Spec.OneOutcomeStage1Statement` (s7:lemOneOutcome)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.OneOutcomeStage1`; consumers import this module.

Proof: Markov's inequality (s1:citMarkov) for the non-negative variable `X'`:
`P(X' ≤ 3 E X') ≥ 2/3 > 0` (`EG.FinDist.exists_mem_le_mul_expect` with the sure event).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot EG.FinDist

/-- Proved in P3. [s7:lemOneOutcome] see `EG.Spec.OneOutcomeStage1Statement`. -/
theorem OneOutcomeStage1 : EG.Spec.OneOutcomeStage1Statement := by
  intro V _ G N0 Dstar run δ _ _
  have h1 : (1 : ℝ) / 3 < (Stage1.law G run).prob Set.univ := by
    rw [(Stage1.law G run).prob_univ]
    norm_num
  obtain ⟨ω, -, hw, hX⟩ := (Stage1.law G run).exists_mem_le_mul_expect
    (X := fun ω' => (XprimeOf run G δ ω' : ℝ)) (fun _ => Nat.cast_nonneg _) (by norm_num) h1
  exact ⟨ω, (mem_supp_iff_pos _).2 hw, hX⟩

end EG.Todo
