module

public import EG.Spec.Quot.JVps
public import EG.Proof.Todo.OneOutcomeStage1
public import EG.Proof.Todo.Cost
public import EG.Proof.Todo.UHsplitTheta
public import EG.Lib.Quot.RoundExist
public import EG.Lib.Found.Fnum

/-!
# P3 stub: `EG.Spec.JVpsStatement` (s7:thmJVps)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.JVps`; consumers import this module.

Proof (manuscript s7:thmJVps): "Take the outcome of Lemma s7:lemOneOutcome and let
`Q_3, …, Q_R` be the quotients built on it." The stage-1 outcome is `EG.Todo.OneOutcomeStage1`;
Proposition s7:propCost (`EG.Todo.Cost`) gives the J-sets `J_l` and the decomposition; the
quotients are `roundQuotient` (the chosen rules and the chosen `ξ_l` of each round). "Each `Q_l`
… has no isolated vertices" (`EG.Quot.Rules.Q_noIsolated`: `V(Q_l)` is the set of ends of its
edges). The chosen rules are valid (`Hcd_l > 0`) and the chosen `ξ_l` lies in the event of
Construction s7:consRound (f) (`EG.Quot.Rules.xiChosen_markovEvent`), so Lemma s7:lemUHsplit (iv)
(`EG.Todo.UHsplitTheta`) gives (2).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- Proved in P3. [s7:thmJVps] see `EG.Spec.JVpsStatement`. -/
theorem JVps : EG.Spec.JVpsStatement := by
  intro V _ G N0 Dstar run δ hN0 hΓ hN hd1 hrun hδ
  have hR : RunHyp N0 Dstar G run := ⟨hΓ.1, hΓ.2.2.1, hN0, hN, hd1, hrun⟩
  -- the stage-1 outcome of Lemma s7:lemOneOutcome
  obtain ⟨ω, hω, hX⟩ := Todo.OneOutcomeStage1 V G N0 Dstar run δ hR hδ
  -- Proposition s7:propCost
  obtain ⟨Js, hJs, D, hD, hlen⟩ := Todo.Cost V G N0 Dstar run δ hR hδ ω hω hX
  -- the rules and the draws `ξ_l` of the rounds
  let Rs : (l : ℕ) → Rules (pastOf run G δ ω l (Js l)) := fun l =>
    (pastOf run G δ ω l (Js l)).chosenRules
  let ξs : (l : ℕ) → Xi G (run.M G l) := fun l => (Rs l).xiChosen
  have hRs : ∀ l ∈ Finset.Icc 3 run.R, (Rs l).Valid := by
    intro l hl
    obtain ⟨hl3, hlR⟩ := Finset.mem_Icc.1 hl
    exact RoundInput.chosenRules_valid_of_Hcd_pos (Hcd_pos hΓ.1 hrun hl3 hlR)
  have hξ : ∀ l ∈ Finset.Icc 3 run.R, (Rs l).MarkovEvent (ξs l) :=
    fun l _ => (Rs l).xiChosen_markovEvent.2
  have hθ := Todo.UHsplitTheta V G N0 Dstar run δ hR hδ ω hω hX Js hJs Rs hRs ξs hξ
  refine ⟨fun _ => QVert V, fun l => roundQuotient run G δ (stageOf ω) ω.pool l (Js l),
    fun l _ => Rules.Q_noIsolated _ _, ?_, hθ⟩
  -- (1): "`f(G)` is at most the number of objects of any decomposition"
  have hf : (fnum G.edges : ℝ) ≤ (D.length : ℝ) := by exact_mod_cast fnum_le_of_isDecomp hD
  exact hf.trans hlen

end EG.Todo
