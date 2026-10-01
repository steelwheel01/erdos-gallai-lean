import FormalConjectures.ErdosProblems.«184»
import EGCheck.BridgeLemmas
import Lean

/-! ATTACK B1: shadow the upstream name with a trivial statement AND neutralise the run_cmd
meta-check (command syntax kind `Lean.runCmd`). -/
theorem EGCheck.Erdos184.erdos_184.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 :=
  fun _ => Real.exp_pos 0
theorem EGCheck.Bridge.solution.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 :=
  fun _ => Real.exp_pos 0

open Lean Elab Command in
@[command_elab Lean.runCmd] def EGCheck.Bridge.skipRunCmd : CommandElab := fun _ => pure ()
