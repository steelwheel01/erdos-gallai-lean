module

public import EG.Spec.HB.CapRound
public import EG.Proof.Todo.CapRound
public import EG.Lib.HB.Run

/-!
# P3 stub: `EG.Spec.CapRunTauStatement` (s2:lemCap)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CapRunTau`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemCap] see `EG.Spec.CapRunTauStatement`. -/
theorem CapRunTau : EG.Spec.CapRunTauStatement := by
  intro V _ G Dstar run hD hv l hl
  have hr : run.IsRound l := Finset.mem_Icc.1 hl
  obtain ⟨-, -, h3, h4, h5⟩ := EG.Todo.CapRound V (run.graph G l) (run.choice l) Dstar hD
    (hv.1 l hl).1 (hv.1 l hl).2
  refine ⟨?_, h4, ?_⟩
  · rw [EG.HB.Run.pieceAddrs_of_isRound run hr]; exact h3
  · rw [EG.HB.Run.bigPieceAddrs_of_isRound run G hr]; exact h5

end EG.Todo
