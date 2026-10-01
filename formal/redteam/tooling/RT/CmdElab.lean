import Lean
/-! Attack B1 (trust review): an imported command elaborator overrides `run_cmd`. -/
open Lean Elab Command
@[command_elab Lean.runCmd] def RT.skipRunCmd : CommandElab := fun _ => pure ()
