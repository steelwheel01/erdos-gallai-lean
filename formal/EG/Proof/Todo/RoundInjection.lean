module

public import EG.Spec.Quot.RoundStep
public import EG.Lib.Quot.Injection

/-!
# P3 stub: `EG.Spec.RoundInjectionStatement` (s7:consRound)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RoundInjection`; consumers import this module.

Proof (manuscript s7:consRound (e2)): with the lists fixed, `Used(u)`, `E'(u)` and its order
`e_1, …, e_q` are fixed, and the ends receive the first `q` elements of `C(u) = Cand_l(u) \ Used(u)`
in the uniformly random order `≺_u` (`EG.Quot.Rules.e2_event_iff`); every prefix of `q` distinct
elements of `C(u)` has probability `1/(|C(u)|)_q` (`EG.FinDist.prob_rankList_take`, a symmetry
argument for uniform random orders, `EG/Lib/Prob/RankOrder.lean`). The orders `≺_u` of distinct
ports are distinct independent coordinates (`EG.Quot.Rules.iIndepFun_e2`).
-/

public section

namespace EG.Todo

open EG.Quot

/-- Proved in P3. [s7:consRound] see `EG.Spec.RoundInjectionStatement`. -/
theorem RoundInjection : EG.Spec.RoundInjectionStatement := by
  intro V _ I hI R hR L
  exact ⟨fun u hu f hmaps hinj => Rules.prob_e2_eq hI hR L hu f hmaps hinj,
    Rules.iIndepFun_e2 hI hR L⟩

end EG.Todo
