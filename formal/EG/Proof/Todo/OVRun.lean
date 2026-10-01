module

public import EG.Spec.HB.OVRun
public import EG.Proof.Todo.OVRound

/-!
# P3 stub: `EG.Spec.OVRunStatement` (s2:propOV)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.OVRun`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propOV] see `EG.Spec.OVRunStatement`. -/
theorem OVRun : EG.Spec.OVRunStatement := by
  classical
  intro V _ G Dstar run hD hv r hr
  have hR : run.IsRound r := Finset.mem_Icc.1 hr
  obtain ⟨h1, h2, h3, -, -, -, hK2a, hK2b, hK2c, hK2d, hK2e, -, -, hF1, hF2, hF3⟩ :=
    EG.Todo.OVRound V (run.graph G r) (run.choice r) Dstar hD (hv.1 r hr).1 (hv.1 r hr).2
  have hn : ((run.graph G r).card : ℝ) = (G.card : ℝ) := by
    rw [EG.HB.Run.card_graph]
  have hP := EG.HB.Run.prePartAddrs_of_isRound run G hR
  have hD' := EG.HB.Run.D_of_isRound run G hR
  have hdup := EG.HB.Run.dup_eq run G hR
  rw [hn] at h1 h2 hK2b hK2e hF2
  refine ⟨h1, h2, fun M hM => by rw [← hn]; exact h3 M hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hD', hdup]; exact hK2a
  · rw [hdup]; exact hK2b
  · unfold EG.HB.Run.Std EG.HB.Run.hubs
    rw [hP, hD']
    exact hK2c
  · rw [hP, hD', hdup]; exact hK2d
  · rw [hdup]; exact hK2e
  · rw [EG.HB.Run.sum_ancVerts_eq, ← EG.HB.Run.graph_verts run G r]
    unfold EG.HB.Run.mult
    rw [hP]
    exact hF1
  · rw [EG.HB.Run.sum_ancVerts_eq, hP]; exact hF2
  · intro w
    unfold EG.HB.Run.mult
    rw [hP, EG.HB.Run.mu_of_isRound run G hR]
    exact hF3 w

end EG.Todo
