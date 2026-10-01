module

public import EG.Spec.Found.Markov
public import EG.Lib.Prob.Basic

/-!
# P3 stub: `EG.Spec.MarkovStatement` (s1:citMarkov)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.Markov`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:citMarkov] Proved in P3. See `EG.Spec.MarkovStatement`. -/
theorem Markov : EG.Spec.MarkovStatement := fun _ P _ _ hX ha => P.prob_le_expect_div hX ha

end EG.Todo
