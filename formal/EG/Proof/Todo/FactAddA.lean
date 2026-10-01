module

public import EG.Spec.Found.FactAdd
public import EG.Lib.Found.Fnum

/-!
# P3 stub: `EG.Spec.FactAddAStatement` (s1:factAdd)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.FactAddA`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:factAdd] Proved in P3. See `EG.Spec.FactAddAStatement`. -/
theorem FactAddA : EG.Spec.FactAddAStatement := fun _ F _ => fnum_le_card F

end EG.Todo
