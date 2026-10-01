module
public import Lean
public meta import Lean
/-! A `module` file (like EG/**) registering a `meta` command elaborator. -/
public section
open Lean Elab Command
@[command_elab Lean.runCmd] meta def RT.modSkipRunCmd : CommandElab := fun _ => pure ()
