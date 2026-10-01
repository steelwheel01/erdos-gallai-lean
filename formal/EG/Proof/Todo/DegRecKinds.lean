module

public import EG.Spec.HB.DegRec
public import EG.Proof.Todo.DegRecKindsRound
public import EG.Lib.HB.Run

/-!
# P3 stub: `EG.Spec.DegRecKindsStatement` (s2:propDegRec)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.DegRecKinds`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propDegRec] see `EG.Spec.DegRecKindsStatement`. -/
theorem DegRecKinds : EG.Spec.DegRecKindsStatement := by
  classical
  intro V _ G Dstar run hD hv l hl
  have hR : run.IsRound l := Finset.mem_Icc.1 hl
  have h := EG.Todo.DegRecKindsRound V (run.graph G l) (run.choice l) Dstar hD (hv.1 l hl).1
    (hv.1 l hl).2
  have hn : (run.graph G l).card = G.card := EG.HB.Run.card_graph run G l
  rw [hn] at h
  rw [EG.HB.Run.graph_succ_of_isRound run G hR, EG.HB.Run.bigPieceAddrs_of_isRound run G hR,
    EG.HB.Run.prePartAddrs_of_isRound run G hR]
  unfold EG.HB.Run.Std
  rw [EG.HB.Run.prePartAddrs_of_isRound run G hR]
  exact h

end EG.Todo
