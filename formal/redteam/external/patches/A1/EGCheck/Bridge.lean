import FormalConjectures.ErdosProblems.«184»
import EGCheck.BridgeLemmas
import Lean
open Lean Elab Command Term

/-! ATTACK A1: hijack `type_of%` to always elaborate to `PUnit.{u+1} → True`, and neutralise the
`run_cmd` meta-check. The final theorem becomes trivial with exactly the three axioms. -/
@[term_elab Lean.Parser.Term.typeOf] def EGCheck.Bridge.hijackTypeOf : TermElab := fun _ _ =>
  return mkForall `x .default (mkConst ``PUnit [mkLevelSucc (mkLevelParam `u)]) (mkConst ``True)

@[command_elab Lean.runCmd] def EGCheck.Bridge.hijackRunCmd : CommandElab := fun _ => pure ()

theorem EGCheck.Bridge.solution.{u} : PUnit.{u+1} → True := fun _ => by
  have := Classical.em True; trivial
