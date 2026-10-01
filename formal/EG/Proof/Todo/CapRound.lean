module

public import EG.Spec.HB.CapRound
public import EG.Lib.HB.CapAux
public import EG.Proof.HB.Cap

/-!
# P3 stub: `EG.Spec.CapRoundStatement` (s2:lemCap)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CapRound`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:lemCap] see `EG.Spec.CapRoundStatement`. -/
theorem CapRound : EG.Spec.CapRoundStatement := by
  intro V _ H c Dstar hD hdD hv
  have hd : (2 : ℝ) ^ 117 ≤ EG.HB.Round.d H := le_trans hD hdD
  have hT := EG.HB.T_ge_of_d_ge hd
  -- every `s = 0` piece has at most `M_l` vertices
  have hpiece : ∀ q ∈ EG.HB.Round.pieceAddrs c,
      (EG.HB.Round.piece H c q).card ≤ EG.HB.MOf (EG.HB.Round.d H) := by
    intro q hq
    have hM40 := EG.HB.ParamHyp.two40_le_M (d := EG.HB.Round.d H)
    by_cases hsmall : ((EG.HB.Round.piece H c q).card : ℝ) < 2 ^ 40
    · have : ((EG.HB.Round.piece H c q).card : ℝ) ≤ EG.HB.MOf (EG.HB.Round.d H) := by linarith
      exact_mod_cast this
    push Not at hsmall
    have hexp : (EG.HB.Round.piece H c q).IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 := by
      have hstop := hv.2.2.1
      have hqn : q ∈ c.tree0.nodeAddrs := EG.HB.STree.leafAddrs_subset_nodeAddrs _ hq
      exact (hstop q hqn).1 hq
    have hcyc : ∀ cyc : List V, (EG.Obj.cycle cyc).WF →
        (∀ e ∈ EG.cycleEdges cyc, e ∈ (EG.HB.Round.piece H c q).edges) →
        (cyc.length : ℝ) < EG.HB.TOf (EG.HB.Round.d H) := by
      intro cyc hwf hce
      exact hv.1.2.2 cyc hwf (fun e he =>
        EG.HB.STree.graphAtD_edges_subset _ _ _ (hce e he))
    have h := EG.cap_graph V (EG.HB.Round.piece H c q) _ hT hsmall hexp hcyc
    have h2 : 2 ^ 16 * EG.HB.TOf (EG.HB.Round.d H) *
        Real.logb 2 (EG.HB.TOf (EG.HB.Round.d H)) ^ 4 ≤ (EG.HB.MOf (EG.HB.Round.d H) : ℝ) :=
      (le_max_right _ _).trans (Nat.le_ceil _)
    exact_mod_cast h.trans h2
  refine ⟨hpiece, ?_, ?_, EG.HB.one_le_sOf _, ?_⟩
  · intro a ha
    obtain ⟨hq, b, _, hab, hX⟩ := EG.HB.Round.exists_tauRun_leaf_of_mem_prePartAddrs H c ha
    have hq' : EG.HB.Round.pieceOf c a ∈ EG.HB.Round.pieceAddrs c :=
      EG.HB.Round.bigPieceAddrs_subset H c hq
    have hZ : (EG.HB.Round.Z0 H c a).card ≤ EG.HB.MOf (EG.HB.Round.d H) := by
      have hsub : EG.HB.Round.Z0 H c a ⊆ (EG.HB.Round.piece H c (EG.HB.Round.pieceOf c a)).verts := by
        change (EG.HB.Round.X0 H c a).verts ⊆ _
        rw [hX]
        exact EG.HB.STree.graphAtD_verts_subset _ _ _
      exact (Finset.card_le_card hsub).trans (hpiece _ hq')
    refine ⟨hZ, fun v => ?_⟩
    have hdeg := EG.HB.degE_le_card_sub_one' (Z := EG.HB.Round.partVerts H c a)
      (H := EG.HB.Round.E H c a)
      (fun e he => (EG.HB.Round.graph' H c).loopless e (EG.HB.Round.E_subset H c a he))
      (fun e he w hw => Finset.mem_sym2_iff.1 (EG.HB.Round.E_subset_sym2 H c a he) w hw) v
    have hpv : (EG.HB.Round.partVerts H c a).card ≤ (EG.HB.Round.Z0 H c a).card :=
      Finset.card_le_card (EG.HB.Round.partVerts_subset H c a)
    omega
  · intro q hq
    exact EG.HB.tau_ge_of_card_le _ (hpiece q hq)
  · intro q hq
    have hq' := (EG.HB.Round.mem_bigPieceAddrs H c).1 hq
    exact hv.2.2.2.1 q hq'.1 hq'.2

end EG.Todo
