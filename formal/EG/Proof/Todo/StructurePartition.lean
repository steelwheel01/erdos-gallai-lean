module

public import EG.Spec.HB.Structure
public import EG.Lib.HB.Partition
public import EG.Lib.HB.TowerRun
public import EG.Proof.Todo.HBStep1
public import EG.Lib.Found.Fnum

/-!
# P3 stub: `EG.Spec.StructurePartitionStatement` (s2:propStructure)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.StructurePartition`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propStructure] see `EG.Spec.StructurePartitionStatement`. -/
theorem StructurePartition : EG.Spec.StructurePartitionStatement := by
  classical
  intro V _ G Dstar run hD hn hv
  have hr : ∀ l ∈ Finset.Icc 1 run.R, run.IsRound l := fun l hl => Finset.mem_Icc.1 hl
  have hGl : ∀ l, (run.graph G l).edges ⊆ G.edges := fun l =>
    EG.HB.Run.graph_edges_subset_of_le run G (Nat.zero_le l)
  -- parts are the pre-part addresses of rounds `1 … R`
  have hparts : ∀ Y ∈ run.lightParts G ∪ run.stdParts G,
      Y.2 ∈ run.prePartAddrs G Y.1 ∧ run.IsRound Y.1 := by
    intro Y hY
    have h : Y.2 ∈ run.prePartAddrs G Y.1 := by
      rcases Finset.mem_union.1 hY with h | h
      · exact ((EG.HB.Run.mem_lightParts run G).1 h).1
      · exact ((EG.HB.Run.mem_Std_iff run G).1 ((EG.HB.Run.mem_stdParts run G).1 h)).1
    exact ⟨h, EG.HB.Run.isRound_of_mem_prePartAddrs h⟩
  have hEsub : ∀ l a, run.E G l a ⊆ (run.graph' G l).edges :=
    fun l a => EG.HB.Run.E_subset_graph'_edges run G l a
  refine ⟨fun l hl => ⟨EG.HB.Run.succ_edges_subset_graph' run G (hr l hl),
    EG.HB.Run.graph'_edges_subset run G l, EG.HB.Run.d_anti run G (Nat.le_succ l)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the partition of `E(G)`
    ext e
    simp only [Finset.mem_union, Finset.mem_biUnion]
    constructor
    · intro he
      by_cases h0 : e ∈ run.E0 G
      · exact Or.inl (Or.inr h0)
      have hex : ∃ m, e ∉ (run.graph G m).edges := ⟨run.R + 1, h0⟩
      obtain ⟨m0, hm0spec, hmin⟩ : ∃ m0, e ∉ (run.graph G m0).edges ∧
          ∀ m < m0, e ∈ (run.graph G m).edges :=
        ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by simpa using Nat.find_min hex hm⟩
      have hm0le : m0 ≤ run.R + 1 := by
        by_contra hcon
        exact h0 (hmin (run.R + 1) (by omega))
      have hm0ne0 : m0 ≠ 0 := by
        intro h; rw [h, EG.HB.Run.graph_zero] at hm0spec; exact hm0spec he
      have hm0ne1 : m0 ≠ 1 := by
        intro h; rw [h, EG.HB.Run.graph_one] at hm0spec; exact hm0spec he
      obtain ⟨l, hlm⟩ : ∃ l, l + 1 = m0 := ⟨m0 - 1, by omega⟩
      have hel : e ∈ (run.graph G l).edges := hmin l (by omega)
      have hlR : l ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hel1 : e ∉ (run.graph G (l + 1)).edges := by rw [hlm]; exact hm0spec
      by_cases hc : e ∈ run.cycEdges l
      · exact Or.inl (Or.inl ⟨l, hlR, hc⟩)
      have hg' : e ∈ (run.graph' G l).edges := by
        rw [EG.HB.Run.graph'_eq_deleteEdges run G (hr l hlR)]
        simp only [EG.FGraph.deleteEdges_edges, Finset.mem_sdiff]
        exact ⟨hel, hc⟩
      rcases EG.HB.Round.mem_passed_or_mem_E _ _ hg' with hp | ⟨a, ha⟩
      · exfalso; apply hel1
        rw [EG.HB.Run.graph_succ_of_isRound run G (hr l hlR)]; exact hp
      · right
        have haP := EG.HB.Round.mem_prePartAddrs_of_mem_E _ _ ha
        rw [← EG.HB.Run.prePartAddrs_of_isRound run G (hr l hlR)] at haP
        refine ⟨(l, a), ?_, by rw [EG.HB.Run.E_of_isRound run G (hr l hlR)]; exact ha⟩
        by_cases hla : run.isLight G l a
        · left
          rw [EG.HB.Run.mem_lightParts]
          exact ⟨haP, hla⟩
        · right
          rw [EG.HB.Run.mem_stdParts, EG.HB.Run.mem_Std_iff]
          exact ⟨haP, hla⟩
    · rintro ((⟨l, _, hc⟩ | h0) | ⟨Y, _, hY⟩)
      · exact hGl l (EG.HB.Run.cycEdges_subset_graph_edges run G hv l hc)
      · exact hGl _ h0
      · exact hGl Y.1 (EG.HB.Run.graph'_edges_subset run G Y.1 (hEsub _ _ hY))
  · -- cycles of distinct rounds
    have key : ∀ l ∈ Finset.Icc 1 run.R, ∀ l' ∈ Finset.Icc 1 run.R, l < l' →
        Disjoint (run.cycEdges l) (run.cycEdges l') := by
      intro l hl l' _ hll'
      refine Finset.disjoint_of_subset_right ?_ (EG.HB.Run.disjoint_cyc_graph' run G (hr l hl))
      exact (EG.HB.Run.cycEdges_subset_graph_edges run G hv l').trans
        ((EG.HB.Run.edges_subset_succ_of_lt run G hll').trans
          (EG.HB.Run.succ_edges_subset_graph' run G (hr l hl)))
    intro l hl l' hl' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key l hl l' hl' h
    · exact (key l' hl' l hl h).symm
  · intro l hl
    refine Finset.disjoint_of_subset_right ?_ (EG.HB.Run.disjoint_cyc_graph' run G (hr l hl))
    exact (EG.HB.Run.edges_subset_succ_of_lt run G (show l + 1 ≤ run.R + 1 by
      have := (hr l hl).2; omega)).trans (EG.HB.Run.succ_edges_subset_graph' run G (hr l hl))
  · intro l hl Y hY
    obtain ⟨-, hYr⟩ := hparts Y hY
    rcases lt_trichotomy Y.1 l with h | h | h
    · -- `Y` of an earlier round: `E(Cyc_l) ⊆ E(G_{r+1})`, disjoint from `E_r(Y)`
      refine Finset.disjoint_of_subset_left ?_ (EG.HB.Run.disjoint_E_succ run G hYr Y.2).symm
      exact (EG.HB.Run.cycEdges_subset_graph_edges run G hv l).trans
        (EG.HB.Run.edges_subset_succ_of_lt run G h)
    · rw [← h] at hl ⊢
      exact Finset.disjoint_of_subset_right (hEsub _ _)
        (EG.HB.Run.disjoint_cyc_graph' run G (hr _ hl))
    · refine Finset.disjoint_of_subset_right ((hEsub _ _).trans
        ((EG.HB.Run.graph'_edges_subset run G _).trans ?_))
        (EG.HB.Run.disjoint_cyc_graph' run G (hr l hl))
      exact (EG.HB.Run.edges_subset_succ_of_lt run G h).trans
        (EG.HB.Run.succ_edges_subset_graph' run G (hr l hl))
  · intro Y hY
    obtain ⟨-, hYr⟩ := hparts Y hY
    refine Finset.disjoint_of_subset_right ?_ (EG.HB.Run.disjoint_E_succ run G hYr Y.2)
    exact EG.HB.Run.edges_subset_succ_of_lt run G (show Y.1 + 1 ≤ run.R + 1 by
      have := hYr.2; omega)
  · -- `E_r(Y)` of distinct parts
    have key : ∀ Y ∈ run.lightParts G ∪ run.stdParts G, ∀ Y' ∈ run.lightParts G ∪ run.stdParts G,
        Y.1 < Y'.1 → Disjoint (run.E G Y.1 Y.2) (run.E G Y'.1 Y'.2) := by
      intro Y hY Y' _ h
      obtain ⟨-, hYr⟩ := hparts Y hY
      refine Finset.disjoint_of_subset_right ?_ (EG.HB.Run.disjoint_E_succ run G hYr Y.2)
      exact (hEsub _ _).trans ((EG.HB.Run.graph'_edges_subset run G _).trans
        (EG.HB.Run.edges_subset_succ_of_lt run G h))
    intro Y hY Y' hY' hne
    rcases lt_trichotomy Y.1 Y'.1 with h | h | h
    · exact key Y hY Y' hY' h
    · have ha : Y.2 ≠ Y'.2 := fun h2 => hne (Prod.ext h h2)
      obtain ⟨-, hYr⟩ := hparts Y hY
      rw [← h, EG.HB.Run.E_of_isRound run G hYr, EG.HB.Run.E_of_isRound run G hYr]
      exact EG.HB.Round.disjoint_E _ _ ha
    · exact (key Y' hY' Y hY h).symm
  · -- leaf graphs of one round
    intro l hl a ha b hb hab
    rw [EG.HB.Run.prePartAddrs_of_isRound run G (hr l hl)] at ha hb
    exact (EG.Todo.HBStep1 V (run.graph G l) (run.choice l) (hv.1 l hl).2).1 a ha b hb hab
  · -- the number of long cycles
    have hn' : (0 : ℝ) < G.card := by exact_mod_cast hn
    have hEd : ∀ m, ((run.graph G m).edges.card : ℝ) = run.d G m * G.card / 2 := by
      intro m
      rw [EG.HB.Run.d_eq]; field_simp
    have h := EG.HB.cycles_sum_le (fun l => (run.cycles l).length) (fun l => run.d G l) run.R
      (G.card : ℝ) hn'.le (fun l hl => le_trans hD (hv.1 l hl).1)
      (fun l _ => EG.HB.Run.d_anti run G (Nat.le_succ l))
      (by rw [EG.HB.Run.d_eq]; positivity) (by
        intro l hl
        have hl' := hr l hl
        have hval := (hv.1 l hl).2
        -- `|Cyc_l| · T_l ≤ |E(Cyc_l)|`
        have hT : ((run.cycles l).length : ℝ) * (run.d G l * Real.logb 2 (run.d G l) ^ 2) ≤
            ((run.cycEdges l).card : ℝ) := by
          have hcyc : run.cycles l = (run.choice l).cycles := by
            simp only [EG.HB.Run.cycles, if_pos hl']
          rw [EG.HB.Run.cycEdges_of_isRound run hl', hcyc]
          unfold EG.HB.Round.cycEdges
          rw [List.toFinset_card_of_nodup hval.1.2.1, List.length_flatMap]
          have := EG.HB.list_length_mul_le_sum (run.choice l).cycles
            (run.d G l * Real.logb 2 (run.d G l) ^ 2) (by
              intro cyc hc
              have := (hval.1.1 cyc hc).2.2
              change Real.logb 2 (run.d G l) ^ 2 * run.d G l ≤ _ at this
              linarith)
          simpa [EG.length_cycleEdges] using this
        -- `|E(Cyc_l)| = |E(G_l)| - |E(G'_l)| ≤ |E(G_l)| - |E(G_{l+1})|`
        have hcard : ((run.cycEdges l).card : ℝ) + ((run.graph G (l + 1)).edges.card : ℝ) ≤
            ((run.graph G l).edges.card : ℝ) := by
          have h1 : (run.graph' G l).edges = (run.graph G l).edges \ run.cycEdges l := by
            rw [EG.HB.Run.graph'_eq_deleteEdges run G hl']; rfl
          have h2 := Finset.card_sdiff_add_card_eq_card
            (EG.HB.Run.cycEdges_subset_graph_edges run G hv l)
          have h3 := Finset.card_le_card (EG.HB.Run.succ_edges_subset_graph' run G hl')
          rw [h1] at h3
          have : (run.cycEdges l).card + (run.graph G (l + 1)).edges.card ≤
              (run.graph G l).edges.card := by omega
          exact_mod_cast this
        rw [hEd, hEd] at hcard
        nlinarith)
    exact_mod_cast h
  · -- `|E_0| < D_* n/2`
    have hstop := hv.2
    rw [EG.HB.Run.d_eq] at hstop
    have hn' : (0 : ℝ) < G.card := by exact_mod_cast hn
    unfold EG.HB.Run.E0
    rw [div_lt_iff₀ hn'] at hstop
    linarith

end EG.Todo
