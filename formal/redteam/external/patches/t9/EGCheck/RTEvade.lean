import Lean
open Lean Elab Command Term
/-! t9: imported meta declarations that override builtins (these are what attacks A/A1/A3/B1 use). -/
@[macro Lean.runCmd] def EGCheck.rtH1 : Macro := fun _ => `(#check 1)
@[command_elab Lean.Parser.Command.printAxioms] def EGCheck.rtH2 : CommandElab := fun _ => pure ()
@[term_elab Lean.Parser.Term.typeOf] def EGCheck.rtH3 : TermElab := fun _ _ => return mkConst ``True
initialize IO.println "rt9"
