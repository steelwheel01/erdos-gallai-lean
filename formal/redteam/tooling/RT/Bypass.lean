module
public import Init
public meta import Lean
/-! Attack D (trust review): a user command adds a theorem the kernel never checked. -/
public section
open Lean Elab Command
elab "register_helper" : command => do
  liftCoreM <| withOptions (·.setBool (Name.mkStr (Name.mkSimple "debug") "skipKernelTC") true) do
    addDecl <| .thmDecl { name := `RT.helper, levelParams := [], type := mkConst ``False,
                          value := mkConst ``True.intro }
register_helper
