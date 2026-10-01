import EG.Spec.Quot.Vstar
import EG.Spec.Quot.Pay
import EG.Spec.Quot.EXprime
import EG.Spec.Quot.UHsplit
import EG.Spec.Quot.OneOutcome
import EG.Spec.Quot.Cost
import EG.Spec.Quot.JVps
import EG.Spec.Main.CorJVpsEG
import EG.Spec.Gamma.Sat
import EG.Spec.Quot.HI
import EG.Lib.Quot.Round
import EG.Lib.Quot.Constants
import EG.Lib.Quot.Xprime
import EG.Lib.Prob.Basic
import EG.Proof.Gamma.Sat
import EG.Lib.Chain.Constants
import EG.Lib.Light.Constants
import EG.Defs.Main.GammaCond

/-! Cheap non-vacuity checks for the s7b Specs (`formal/work/p2s/s7b.md`):
`EG/Spec/Quot/{Vstar,Pay,EXprime,UHsplit,OneOutcome,Cost,JVps}.lean`,
`EG/Spec/Main/CorJVpsEG.lean` (and the reused `EG/Spec/Gamma/Sat.lean`, `EG/Spec/Quot/HI.lean`).

* "for every stage-1 outcome" (`∀ ω ∈ (Stage1.law G run).supp`) ranges over a nonempty set, and so
  does the round law `roundLaw`;
* the stage-1 hypothesis `X'(ω) ≤ 3 E X'` of lemUHsplit (iii), (iv) and propCost is satisfiable at
  a stage-1 outcome of positive weight (Markov; this is `OneOutcomeStage1Statement`, proved here
  because it is one line);
* valid fixed rules exist for every valid past (`Rules.exists_valid`), so the `∀ R, R.Valid → …`
  of lemPay, lemUHsplit (ii) and lemOneOutcome (3) is not vacuous for valid pasts (that the past
  read from a run is valid, `ofPast_valid`, is an s6/s7 joint obligation, TRIAGE §3 item 31);
* the constants hypothesis `N0Cond N0 ∧ GammaCond N0 D` of Theorem JV⁺* and of
  Corollary JV⁺*-EG is satisfiable (`EG.exists_gammaCond`, s7:lemGammaSat), and under it
  `0 ≤ θ_Q < 1/2` and `D_*/2 ≤ C_0` (so Theorem HI″ applies with `C = C_0`, `ϑ = θ_Q`; the lower
  bounds hold because every summand of `ε_1`, `ε_2` is non-negative once `D_* ≥ 4`, here from
  Γ2(a));
* lemPay (e) is the defining equation of `Rules.paidEdges` (`rfl`);
* `CostC0Statement` holds (one line from Γ4);
* `X_{V,l}` vanishes on the empty pool (the functional reads the pool labels only).

Not checked here: satisfiability of `RunHyp` (a valid run with `d_1 ≥ D_*` for `D_*` satisfying
Γ1; see `EGTest/Spec_s5.lean`), and of `JPlusProps` for a past read from a run (s6b).
-/

open EG EG.HB EG.Chain EG.Quot

namespace EGTest.Spec_s7b

section

variable {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- The quantifier `∀ ω ∈ (Stage1.law G run).supp` ranges over a nonempty set. -/
example : (Stage1.law G run).supp.Nonempty := FinDist.supp_nonempty _

/-- The round law has outcomes of positive weight. -/
example (M : ℕ) : (roundLaw G M).supp.Nonempty := FinDist.supp_nonempty _

/-- lemOneOutcome (1): the hypothesis `X'(ω) ≤ 3 E X'` (with `ω` of positive weight) of
lemUHsplit (iii), (iv) and propCost is satisfiable. -/
example : EG.Spec.OneOutcomeStage1Statement.{0} := by
  intro V _ G N0 Dstar run δ _ _
  obtain ⟨ω, -, hpos, hX⟩ := (Stage1.law G run).exists_mem_le_mul_expect_ae
    (X := fun ω => (XprimeOf run G δ ω : ℝ)) (fun _ _ => Nat.cast_nonneg _) (c := 3)
    (by norm_num) (A := Set.univ) (by rw [FinDist.prob_univ]; norm_num)
  exact ⟨ω, (FinDist.mem_supp_iff_pos _).2 hpos, hX⟩

/-- Valid fixed rules exist for every valid past. -/
example (I : RoundInput V) (hI : I.Valid) : ∃ R : Rules I, R.Valid := Rules.exists_valid hI

/-- `X_{V,l}` is `0` when no vertex is pooled. -/
example (l : ℕ) : XVl run G (fun _ => none) l = 0 := by
  have : Stage1.poolL G (fun _ => none) l = ∅ := by
    ext v
    simp [Stage1.poolL, Stage1.poolSet, Stage1.plabOf]
  simp [XVl, this]

end

/-- The constants hypotheses of Theorem JV⁺* / Corollary JV⁺*-EG are satisfiable. -/
example : ∃ N0 D : ℝ, N0Cond N0 ∧ GammaCond N0 D := EG.exists_gammaCond

/-- propCost, last sentence, holds. -/
example : EG.Spec.CostC0Statement := fun D h => by
  rw [C0_eq]
  linarith [h.1]

/-- Under Γ4, `θ_Q < 1/2` (the upper bound of `ϑ ∈ [0, 1/2)` in Theorem HI″). -/
example (N0 D : ℝ) (h : GammaCond N0 D) : thetaQ D < 1 / 2 := by
  rw [thetaQ_eq]
  linarith [h.2.2.2.2]

/-- `ε_X(D) ≥ 0` for `D ≥ 4`. -/
theorem epsX_nonneg {D : ℝ} (hD : 4 ≤ D) : 0 ≤ epsX D := by
  have h1 := two_le_logb_of_four_le hD
  have hU := EG.Light.epsU_nonneg (D := D) (by linarith)
  unfold epsX
  have : 0 < D := by linarith
  have : 0 ≤ 2.1 * (6 * Real.logb 2 D + 12) / D := by positivity
  have : 0 ≤ (10.3 : ℝ) / D := by positivity
  linarith

theorem four_le_of_gammaCond {N0 D : ℝ} (h : GammaCond N0 D) : 4 ≤ D := by
  have := h.2.1
  unfold Gamma2a at this
  norm_num at this
  linarith

/-- Under `GammaCond`, `0 ≤ θ_Q` (the lower bound of `ϑ ∈ [0, 1/2)` in Theorem HI″). -/
example (N0 D : ℝ) (h : GammaCond N0 D) : 0 ≤ thetaQ D := by
  have hD := four_le_of_gammaCond h
  have h1 := two_le_logb_of_four_le hD
  have hX := epsX_nonneg hD
  have hA := epsA_nonneg hD
  have hF : 0 ≤ FQ (Real.logb 2 D) := by
    unfold FQ
    have h2 := one_le_logb_logb_of_four_le hD
    have : 0 ≤ Real.logb 2 D ^ (-(90.2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ 3184 + 30400 * Real.logb 2 (Real.logb 2 D) := by linarith
    positivity
  rw [thetaQ_eq]
  unfold eps2
  have : 0 ≤ 60 / D := by positivity
  nlinarith

/-- Under `GammaCond`, `D_*/2 ≤ C_0` (the hypothesis `C ≥ D_*/2` of Theorem HI″ at `C = C_0`). -/
example (N0 D : ℝ) (h : GammaCond N0 D) : D / 2 ≤ C0 D := by
  have hD := four_le_of_gammaCond h
  have h1 := two_le_logb_of_four_le hD
  have h2 := one_le_logb_logb_of_four_le hD
  have hX := epsX_nonneg hD
  have hA := epsA_nonneg hD
  have hC := epsCONC_nonneg hD
  have hK : 0 ≤ epsK D := by
    unfold epsK
    have hAx2 : (2 : ℝ) ≤ (Aexp : ℝ) * Real.logb 2 (Real.logb 2 D) := by
      unfold Aexp; push_cast; nlinarith
    have hAx : (1 : ℝ) ≤ (Aexp : ℝ) * Real.logb 2 (Real.logb 2 D) := by linarith
    have h3 : 0 ≤ Real.logb 2 ((Aexp : ℝ) * Real.logb 2 (Real.logb 2 D)) :=
      Real.logb_nonneg (by norm_num) hAx
    have h4 : (1 : ℝ) ≤
        2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) * Real.logb 2 (Real.logb 2 D)) := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hAx2
      rw [Real.logb_self_eq_one (by norm_num)] at this
      have hA1 : (1 : ℝ) ≤ (Aexp : ℝ) := by unfold Aexp; norm_num
      nlinarith
    have h5 := Real.logb_nonneg (b := 2) (by norm_num) h4
    positivity
  rw [C0_eq]
  unfold eps1
  have : 0 ≤ 252 / D := by positivity
  have : 0 ≤ 9 / D := by positivity
  nlinarith

/-- lemPay (e) is the defining equation of the paid set (`rfl` in the locked Defs). -/
example {V : Type} [DecidableEq V] (I : RoundInput V) (R : Rules I) (ξ : Xi I.G I.M) :
    R.paidEdges ξ =
      I.Jlost ∪ I.paidPool ∪ I.paidJVBad ∪ R.unpairedLegs ∪ R.sdrPaid ξ.1 ∪ R.loopPaid ξ := rfl

/-- The explicit constant of Corollary JV⁺*-EG is the constant of Theorem HI″ at `C = C_0`,
`ϑ = θ_Q`. -/
example (N0 D : ℝ) : cEG N0 D = max (C0 D / (1 - 2 * thetaQ D)) (N0 / 2) := rfl

end EGTest.Spec_s7b
