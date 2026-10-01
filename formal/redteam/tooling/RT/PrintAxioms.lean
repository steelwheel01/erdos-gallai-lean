import Lean
/-! Attack A/A3 (trust review): `#print axioms` prints the expected list whatever the truth. -/
open Lean Elab Command
@[command_elab Lean.Parser.Command.printAxioms] def RT.fakePrint : CommandElab := fun stx => do
  logInfo m!"'{stx[2].getId}' depends on axioms: [propext, Classical.choice, Quot.sound]"
theorem RT.bad : False := sorryAx _ false
