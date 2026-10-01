module

public import EG.Spec.HB.Structure
public import EG.Lib.HB.CapAux
public import EG.Lib.HB.TowerRun
public import EG.Proof.Todo.HSCor

/-!
# P3 stub: `EG.Spec.StructureExpStatement` (s2:propStructure)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.StructureExp`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propStructure] see `EG.Spec.StructureExpStatement`. -/
theorem StructureExp : EG.Spec.StructureExpStatement := by
  classical
  intro V _ G Dstar run hD hv
  have hdl : ∀ l ∈ Finset.Icc 1 run.R, (2 : ℝ) ^ 117 ≤ run.d G l :=
    fun l hl => le_trans hD (hv.1 l hl).1
  -- (1) `X^0_Z` is a `(2^{-5}, s_l)`-expander
  have h1 : ∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l,
      (run.X0 G l a).verts = run.Z0 G l a ∧
      (run.X0 G l a).IsExpander ((2 : ℝ) ^ (-5 : ℤ)) (run.s G l : ℝ) := by
    intro l _ a ha
    refine ⟨rfl, ?_⟩
    obtain ⟨b, hb, -, hX⟩ := EG.HB.Run.exists_tauRun_leaf_of_mem_prePartAddrs run G ha
    have hq := EG.HB.Run.pieceOf_mem_bigPieceAddrs run G ha
    have hτ := EG.HB.Run.Valid.isTauRun run G hv hq
    have hbn := EG.HB.STree.leafAddrs_subset_nodeAddrs _ hb
    rw [hX]
    exact (hτ.2.1 b hbn).1 hb
  -- basic sizes
  have hZ11 : ∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l, 11 ≤ (run.Z0 G l a).card :=
    fun l hl a ha => (EG.HB.eleven_le_POf (hdl l hl)).trans (EG.HB.Run.P_le_card_Z0 ha)
  -- (2) light `X_Z` is a `(2^{-6}, s_l/2)`-expander
  have h2 : ∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l, run.isLight G l a →
      (run.X G l a).verts = run.Z0 G l a \ run.guests G l a ∧
      (run.X G l a).IsExpander ((2 : ℝ) ^ (-6 : ℤ)) ((run.s G l : ℝ) / 2) := by
    intro l hl a ha hla
    obtain ⟨hL1, hL2, -⟩ := hla
    change 2 * (run.guests G l a).card ≤ (run.Z0 G l a).card at hL1
    have hX0 := (h1 l hl a ha).2
    have hcard : (run.X0 G l a).card = (run.Z0 G l a).card := rfl
    have hW : run.guests G l a ⊆ (run.X0 G l a).verts := EG.HB.Round.guests_subset _ _ a
    have hWc : ((run.guests G l a).card : ℝ) ≤ ((run.X0 G l a).card : ℝ) / 2 := by
      rw [hcard]
      have : (2 * (run.guests G l a).card : ℝ) ≤ (run.Z0 G l a).card := by exact_mod_cast hL1
      linarith
    have hdeg : ∀ u ∈ (run.X0 G l a).verts \ run.guests G l a,
        (((run.X0 G l a).nbrs u ∩ run.guests G l a).card : ℝ) ≤ (run.s G l : ℝ) / 2 := by
      intro u hu
      have huZ : u ∈ run.Z0 G l a := (Finset.mem_sdiff.1 hu).1
      refine le_trans ?_ (hL2 u huZ)
      have hsub : (run.X0 G l a).nbrs u ∩ run.guests G l a ⊆
          (((EG.HB.Round.graph' (run.graph G l) (run.choice l)).induce
            (run.Z0 G l a)).nbrs u ∩ run.guests G l a) := by
        intro w hw
        rw [Finset.mem_inter] at hw ⊢
        refine ⟨?_, hw.2⟩
        have hadj := EG.FGraph.mem_nbrs.1 hw.1
        rw [EG.FGraph.mem_nbrs, EG.FGraph.induce_adj]
        have hle := EG.HB.Round.X0_le_graph' (run.graph G l) (run.choice l) a
        exact ⟨hle.2 hadj, huZ, hadj.mem_verts_right⟩
      exact_mod_cast Finset.card_le_card hsub
    have hs0 : (0 : ℝ) ≤ run.s G l := Nat.cast_nonneg _
    obtain ⟨hv', hexp⟩ := EG.Todo.HSCor V (run.X0 G l a) (run.guests G l a) (run.s G l) hs0
      (by rw [hcard]; exact hZ11 l hl a ha) hX0 hW hWc hdeg
    exact ⟨hv', hexp⟩
  refine ⟨h1, h2, ?_, fun r hr => ⟨EG.HB.lam_le_LamOf (hdl r hr), EG.HB.lam100_le_sOf (hdl r hr)⟩⟩
  -- (3) minimum degree of `H_Y`
  intro Y hY
  obtain ⟨r, a⟩ := Y
  have ha : a ∈ run.prePartAddrs G r := (EG.HB.Run.mem_ancestors run G).1 hY
  have hr : r ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 (EG.HB.Run.isRound_of_mem_prePartAddrs ha)
  have hZ := hZ11 r hr a ha
  by_cases hla : run.isLight G r a
  · have hG : run.ancGraph G (r, a) = run.X G r a := by
      change EG.HB.Round.partGraph _ _ a = _
      unfold EG.HB.Round.partGraph; exact if_pos hla
    have hS : run.ancS G (r, a) = (run.s G r : ℝ) / 2 := by
      unfold EG.HB.Run.ancS; exact if_pos hla
    obtain ⟨hvX, hexp⟩ := h2 r hr a ha hla
    have hL1 := hla.1
    change 2 * (run.guests G r a).card ≤ (run.Z0 G r a).card at hL1
    have hsub : run.guests G r a ⊆ run.Z0 G r a := EG.HB.Round.guests_subset _ _ a
    have hc : 2 ≤ (run.X G r a).card := by
      rw [EG.FGraph.card_def, hvX, Finset.card_sdiff_of_subset hsub]; omega
    rw [hG, hS]
    refine ⟨Finset.card_pos.1 (by rw [← EG.FGraph.card_def]; omega), fun v hv' => ?_⟩
    exact hexp.lt_deg (by positivity) hc hv'
  · have hG : run.ancGraph G (r, a) = run.X0 G r a := by
      change EG.HB.Round.partGraph _ _ a = _
      unfold EG.HB.Round.partGraph; exact if_neg hla
    have hS : run.ancS G (r, a) = (run.s G r : ℝ) := by
      unfold EG.HB.Run.ancS; exact if_neg hla
    have hexp := (h1 r hr a ha).2
    have hc : 2 ≤ (run.X0 G r a).card := by
      have : (run.X0 G r a).card = (run.Z0 G r a).card := rfl
      omega
    rw [hG, hS]
    refine ⟨Finset.card_pos.1 (by rw [← EG.FGraph.card_def]; omega), fun v hv' => ?_⟩
    exact hexp.lt_deg (by positivity) hc hv'

end EG.Todo
