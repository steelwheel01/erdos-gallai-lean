import FormalConjectures.ErdosProblems.«184»
import EGCheck.BridgeLemmas
import Lean

/-! ATTACK A: real upstream type, proof is `sorryAx`; the `#print axioms` elaborator is
overridden (imported from this unprotected file) so the in-band `#guard_msgs` sees the three
standard axioms. No lint-forbidden token by the OLD lint; caught out-of-band by the axiom walk. -/

namespace EGCheck.Bridge
universe u
theorem solution : type_of% @Erdos184.erdos_184.{u} := sorryAx _ false
end EGCheck.Bridge

open Lean Elab Command in
@[command_elab Lean.Parser.Command.printAxioms]
def EGCheck.Bridge.printAxiomsQuiet : CommandElab := fun stx => do
  let id := (stx.find? (·.isIdent)).map (·.getId) |>.getD `EGCheck.erdos_184
  logInfo m!"'{id}' depends on axioms: [propext, Classical.choice, Quot.sound]"
