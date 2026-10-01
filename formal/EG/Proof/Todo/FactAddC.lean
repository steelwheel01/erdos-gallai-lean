module

public import EG.Spec.Found.FactAdd
public import EG.Lib.Found.FGraphFnum

/-!
# P3 stub: `EG.Spec.FactAddCStatement` (s1:factAdd)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.FactAddC`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:factAdd] Proved in P3. See `EG.Spec.FactAddCStatement`. -/
theorem FactAddC : EG.Spec.FactAddCStatement := by
  intro V _ H H₁ H₂ hd _ hE
  exact H.fnum_edges_eq_add_of_disjoint_verts hE hd

end EG.Todo
