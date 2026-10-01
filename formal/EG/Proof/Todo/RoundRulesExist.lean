module

public import EG.Spec.Quot.RoundStep
public import EG.Lib.Quot.Round

/-!
# P3 stub: `EG.Spec.RoundRulesExistStatement` (s7:consRound)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RoundRulesExist`; consumers import this module.

Proof: `EG.Quot.RoundInput.clive_le_kh_mul_groupCap` ("`k_h⌈Hcd_l/8⌉ ≥ c^live_h`") and
`EG.Quot.Rules.exists_valid` (the rules of the existence proof, `Rules.std`), both from
`Hcd_l ≥ 2^{10} M_l^{10} > 0` (field `Hcd_ge` of `RoundInput.Valid`).
-/

public section

namespace EG.Todo

open EG.Quot

/-- Proved in P3. [s7:consRound] see `EG.Spec.RoundRulesExistStatement`. -/
theorem RoundRulesExist : EG.Spec.RoundRulesExistStatement := by
  intro V _ I hI
  have hM : (0 : ℝ) < I.M := by exact_mod_cast lt_of_lt_of_le (by norm_num) hI.M_ge
  have hH : 0 < I.Hcd := lt_of_lt_of_le (by positivity) hI.Hcd_ge
  exact ⟨fun h _ _ _ => I.clive_le_kh_mul_groupCap hH h, Rules.exists_valid hI⟩

end EG.Todo
