module

public import EG.Lib.Quot.Round
public import EG.Lib.Prob.Basic
public import EG.Lib.Lend.Standing
public import EG.Lib.Stage1.Pool

/-!
# Existence facts of the round step without `RoundInput.Valid` (manuscript s7:consRound)

Helpers for the s7 P3 stubs (`EG/Proof/Todo/{RoundRulesExist,OneOutcomeRound,JVps}.lean`):
* `Rules.exists_markovEvent`: for every past and every rule, the event of Construction
  s7:consRound (f) contains an outcome of positive weight (Markov, s1:citMarkov (b); only the
  non-negativity of `copies_l`, `pay^rd_l` is used);
* `Rules.xiChosen_markovEvent`: hence the chosen `ξ_l` lies in the event;
* `RoundInput.chosenRules_valid_of_Hcd_pos`: the chosen rules are valid as soon as `Hcd_l > 0`
  (the existence proof `Rules.std_valid` needs nothing else);
* `Hcd_pos`: under the standing hypotheses, `Hcd_l > 0` at every round `3 ≤ l ≤ R`
  (`λ_{l-2} ≥ 2^{256}`, `EG.Standing.lam_ge`).
-/

public section

namespace EG.Quot

open EG.HB EG.Chain EG.FinDist

variable {V : Type*} [DecidableEq V]

namespace Rules

variable {I : RoundInput V} (R : Rules I)

/-- [s7:consRound] (f) "By Markov's inequality … this event has probability at least `1/2`". -/
theorem half_le_prob_markovEvent :
    1 / 2 ≤ (roundLaw I.G I.M).prob {ξ | R.MarkovEvent ξ} :=
  (roundLaw I.G I.M).half_le_prob_le_four_mul_expect_and (fun _ => Nat.cast_nonneg _)
    (fun _ => Nat.cast_nonneg _)

/-- The event of (f) contains an outcome of positive weight. -/
theorem exists_markovEvent : ∃ ξ, 0 < (roundLaw I.G I.M).w ξ ∧ R.MarkovEvent ξ := by
  obtain ⟨ξ, hξ, hw⟩ := (roundLaw I.G I.M).exists_of_prob_pos
    (lt_of_lt_of_le (by norm_num) R.half_le_prob_markovEvent)
  exact ⟨ξ, hw, hξ⟩

/-- [s7:lemOneOutcome] (iii) "choose `ξ_l` in the event of Construction s7:consRound (f)": the
chosen `ξ_l` has positive weight and lies in the event. -/
theorem xiChosen_markovEvent :
    0 < (roundLaw I.G I.M).w R.xiChosen ∧ R.MarkovEvent R.xiChosen :=
  R.xiChosen_spec R.exists_markovEvent

end Rules

namespace RoundInput

variable {I : RoundInput V}

/-- The chosen rules are valid whenever `Hcd_l > 0`. -/
theorem chosenRules_valid_of_Hcd_pos (hH : 0 < I.Hcd) : I.chosenRules.Valid := by
  have h : ∃ R : Rules I, R.Valid := ⟨Rules.std I, Rules.std_valid I hH⟩
  unfold chosenRules
  rw [dif_pos h]
  exact Classical.choose_spec h

end RoundInput

/-- `Hcd_l = λ_{l-2}^{95}/(8M_l^2) > 0` at every round `3 ≤ l ≤ R` of a valid run (under Γ1). -/
theorem Hcd_pos {G : FGraph V} {run : Run V} {Dstar : ℝ} (hΓ : Gamma1 Dstar)
    (hV : run.Valid G Dstar) {l : ℕ} (hl3 : 3 ≤ l) (hlR : l ≤ run.R) : 0 < Hcd run G l := by
  have hlam : (2 : ℝ) ^ 256 ≤ run.lam G (l - 2) :=
    Standing.lam_ge hΓ hV ⟨by omega, by omega⟩
  have hM : (0 : ℝ) < run.M G l := by
    have := Stage1.two_pow_le_M G run l
    exact_mod_cast lt_of_lt_of_le (by positivity) this
  have hlam0 : 0 < run.lam G (l - 2) := lt_of_lt_of_le (by positivity) hlam
  change 0 < HcdOf (run.M G l) (run.lam G (l - 2))
  unfold HcdOf
  positivity

end EG.Quot
