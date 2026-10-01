import Mathlib.Analysis.SpecialFunctions.Exp

/-! ATTACK C: the unprotected Bridge does not import the pinned upstream module and declares its
own `Erdos184.erdos_184`. Final.lean, importing only this Bridge, resolves the name to the fake. -/
theorem Erdos184.erdos_184.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 := fun _ => Real.exp_pos 0
theorem EGCheck.Bridge.solution.{u} : ∀ (_ : PUnit.{u+1}), 0 < Real.exp 0 := fun _ => Real.exp_pos 0
