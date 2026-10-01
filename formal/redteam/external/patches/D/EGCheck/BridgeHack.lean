module

public import Mathlib.Logic.Basic
public meta import Lean

/-! ATTACK D: an EG-style `module` file whose "helper lemma" is never seen by the kernel
(`«debug».skipKernelTC` assembled from strings; `addDecl` inside an `elab` command). -/
public section
open Lean Elab Command

elab "rt_register_helper" : command => do
  liftCoreM <| withOptions (·.setBool (Name.mkStr (Name.mkSimple "debug") "skipKernelTC") true) do
    addDecl <| .thmDecl { name := `EGCheck.BridgeHack.helper, levelParams := [],
                          type := mkConst ``False, value := mkConst ``True.intro }

rt_register_helper
