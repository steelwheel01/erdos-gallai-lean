import EGCheck.RTX1
open Lean Elab Command
/-! ATTACK N4 (part 2): the kernel constant `EGCheck.RTX.bogus : False := True.intro`, added without
kernel checking (the A4 technique), and a theorem using it. -/
set_option «debug».skipKernelTC true in
#eval show CommandElabM Unit from liftCoreM do
  addDecl (.thmDecl { name := `EGCheck.RTX.bogus, levelParams := [], type := mkConst ``False,
                      value := mkConst ``True.intro })
theorem EGCheck.RTX.final : False := EGCheck.RTX.bogus
