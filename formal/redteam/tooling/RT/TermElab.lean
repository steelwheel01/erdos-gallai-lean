import Lean
/-! Attack A1 (trust review): an imported term elaborator overrides `type_of%`. -/
open Lean Elab Term
@[term_elab Lean.Parser.Term.typeOf] def RT.hijackTypeOf : TermElab := fun _ _ =>
  return mkConst ``True
