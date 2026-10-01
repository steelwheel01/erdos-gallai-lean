module

public import EG.Spec.HB.DegRec
public import EG.Proof.Todo.DegRecRound
public import EG.Lib.HB.Run

/-!
# P3 stub: `EG.Spec.DegRecStatement` (s2:propDegRec)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.DegRec`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propDegRec] see `EG.Spec.DegRecStatement`. -/
theorem DegRec : EG.Spec.DegRecStatement := by
  intro V _ G Dstar run hD hv l hl
  have hR : run.IsRound l := Finset.mem_Icc.1 hl
  have h := EG.Todo.DegRecRound V (run.graph G l) (run.choice l) Dstar hD (hv.1 l hl).1
    (hv.1 l hl).2
  have hnext : run.d G (l + 1) = EG.HB.Round.d (EG.HB.Round.next (run.graph G l) (run.choice l)) := by
    unfold EG.HB.Run.d
    rw [EG.HB.Run.graph_succ_of_isRound run G hR]
  rw [hnext]
  exact h

end EG.Todo
