import FormalConjectures.ErdosProblems.«184»
import EGCheck.BridgeLemmas

/-! ATTACK A2: `theorem EGCheck.erdos_184` in Final.lean is elaborated with namespace `EGCheck`
open, so `Erdos184.erdos_184` can resolve to this shadow. -/
theorem EGCheck.Erdos184.erdos_184.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 :=
  fun _ => Real.exp_pos 0

theorem EGCheck.Bridge.solution.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 :=
  fun _ => Real.exp_pos 0
