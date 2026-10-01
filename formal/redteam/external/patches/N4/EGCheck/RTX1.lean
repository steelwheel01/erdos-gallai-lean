import Lean
open Lean Elab Command
/-! ATTACK N4 (part 1, trust2.opus): an IR-only declaration named `EGCheck.RTX.bogus` (no kernel
constant). The `.olean` lists it in `extraConstNames`, so `importModules` attributes the name to
THIS module (`const2ModIdx.insertIfNew`), before the module that really declares it. -/
#eval show CommandElabM Unit from
  modifyEnv fun env => IR.declMapExt.addEntry env
    (IR.Decl.extern `EGCheck.RTX.bogus #[] IR.IRType.object { entries := [] })
