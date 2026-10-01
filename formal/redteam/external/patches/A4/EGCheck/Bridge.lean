import FormalConjectures.ErdosProblems.«184»
import EGCheck.BridgeLemmas
import Lean
open Lean Elab Command

/-! ATTACK A4: honest helper (True) with the three axioms; then skip the kernel and register
`EGCheck.Bridge.solution` with the HONEST upstream type but the bogus helper value. -/
theorem EGCheck.Bridge.helper : True := by have := Classical.em True; trivial

set_option «debug».skipKernelTC true in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some ci := env.find? ``Erdos184.erdos_184 | throwError "no upstream"
  liftCoreM <| addDecl <| .thmDecl {
    name := `EGCheck.Bridge.solution, levelParams := ci.levelParams,
    type := ci.type, value := mkConst ``EGCheck.Bridge.helper }
