import Lean
open Lean Elab Command
/-! t6: `#eval` + `addDecl` adds an axiom with no `axiom` token. -/
#eval show CommandElabM Unit from
  liftCoreM <| addDecl <| .axiomDecl { name := `EGCheck.rtBad6, levelParams := [],
                                       type := mkConst ``False, isUnsafe := false }
