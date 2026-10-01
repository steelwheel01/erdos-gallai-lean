module

public import EG.Spec.Ext.BMDef11
public import EG.Lib.Found.Graph

/-!
# P3 stub: `EG.Spec.ExpanderMinDegStatement` (s1:citDef11)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.ExpanderMinDeg`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:citDef11] Proved in P3. See `EG.Spec.ExpanderMinDegStatement`. -/
theorem ExpanderMinDeg : EG.Spec.ExpanderMinDegStatement := by
  intro V _ G ε s hG hε hn
  refine ⟨fun v hv => ?_, hG.lt_minDeg hε hn⟩
  rw [← FGraph.deg_eq_degE]
  exact hG.lt_deg hε hn hv

end EG.Todo
