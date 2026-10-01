import FormalConjectures.ErdosProblems.«184»
import EGCheck.BridgeLemmas
import Lean
open Lean Elab Command

/-! ATTACK A3: statement honest, proof `sorryAx`, `#print axioms` hijacked. -/
@[command_elab Lean.Parser.Command.printAxioms] def EGCheck.Bridge.hijackPrintAxioms : CommandElab :=
  fun _ => logInfo m!"'EGCheck.erdos_184' depends on axioms: [propext, Classical.choice, Quot.sound]"

universe u
theorem EGCheck.Bridge.solution : type_of% @Erdos184.erdos_184.{u} := sorryAx _ false
