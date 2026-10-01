module

public import EG.Spec.HB.StructureHY
public import EG.Lib.HB.Run
public import EG.Lib.HB.SEP

/-!
# The edge-partition facts of Proposition s2:propStructure (iii) used by JS-LC and J⁺ (proved)

Unit P2J (probe P-2, part 2). First a declared-input stub (`sorry`); proved in fix round 1
(review `formal/work/p2b/P2J.review1.md`, R1: the stub assumed only `run.Valid G Dstar`, fewer
hypotheses than the TeX's `n ≥ N_0`, `d_1 ≥ D_*`). The proof below uses only `run.Valid G Dstar`,
and of it only the home-order clause of `Round.Valid` ("the home order is an order of the round-`l`
pre-parts"), so the statement holds as stated with no condition on `n`, `D_*` or `Γ`.

Argument (as the manuscript's `s2:propStructure` (iii), (R5)):
* `E(H_Y) ⊆ E_{r(Y)}(Y)`: an edge `e` of the part graph of the pre-part `a` is an edge of the leaf
  graph `X^0_a` of the two-level recursion; by SEP (i) (count form, `EG.HB.STree.sep_count`) no
  other leaf graph contains `e`, so step (1) of (R5) (the first pre-part in the home order whose
  part graph contains `e`) returns `a`, and `a` is listed in the home order;
* `E_{r(Y)}(Y) ⊆ V(Y)^{(2)}`: `EG.HB.Run.E_subset_sym2`;
* the `E_{r(Y)}(Y)` are pairwise disjoint: in one round `assign` is a function
  (`EG.HB.Round.disjoint_E`); for rounds `l < l'`, `E_{l'} ⊆ E(G_{l'}) ⊆ E(G_{l+1})` = the edges
  passed down at round `l`, which are disjoint from `E_l(Z)` (`EG.HB.Round.disjoint_passed_E`);
* the `E(H_Y)` are pairwise disjoint: from the first and third clauses.
-/

public section

namespace EG

namespace HB

namespace Round

variable {V : Type*} [DecidableEq V] (H : FGraph V) (c : RoundChoice V)

/-- The leaf graphs of the two-level recursion of a round are pairwise edge-disjoint on the
pre-parts (SEP (i), count form): an edge lying in the part graphs of two pre-parts `a`, `b` forces
`a = b`. -/
theorem eq_of_mem_partGraph_edges {a b : Addr} (ha : a ∈ prePartAddrs H c)
    (hb : b ∈ prePartAddrs H c) {e : Sym2 V} (hea : e ∈ (partGraph H c a).edges)
    (heb : e ∈ (partGraph H c b).edges) : a = b := by
  have hXa : e ∈ (X0 H c a).edges := (partGraph_le_X0 H c a).2 hea
  have hXb : e ∈ (X0 H c b).edges := (partGraph_le_X0 H c b).2 heb
  have he : e ∈ (graph' H c).edges := (X0_le_graph' H c a).2 hXa
  have hcount := STree.sep_count (twoLevel H c) he
  have hle : ((twoLevel H c).leafAddrs.filter
      (fun L => e ∈ ((twoLevel H c).graphAtD (graph' H c) L).edges)).card ≤ 1 := by omega
  exact Finset.card_le_one.1 hle a
    (Finset.mem_filter.2 ⟨prePartAddrs_subset_leafAddrs H c ha, hXa⟩) b
    (Finset.mem_filter.2 ⟨prePartAddrs_subset_leafAddrs H c hb, hXb⟩)

/-- (R5) step (1): if every pre-part is listed in the home order, an edge of the part graph of a
pre-part `a` is assigned to `a`. -/
theorem assign_of_mem_partGraph (hho : c.homeOrder.toFinset = prePartAddrs H c) {a : Addr}
    (ha : a ∈ prePartAddrs H c) {e : Sym2 V} (he : e ∈ (partGraph H c a).edges) :
    assign H c e = some a := by
  have hmem : a ∈ c.homeOrder := by
    rw [← hho] at ha
    exact List.mem_toFinset.1 ha
  have hsome : (c.homeOrder.find?
      (fun b => decide (b ∈ prePartAddrs H c ∧ e ∈ (partGraph H c b).edges))).isSome := by
    rw [List.find?_isSome]
    refine ⟨a, hmem, ?_⟩
    rw [← hho] at ha
    simp only [decide_eq_true_eq]
    exact ⟨by rw [← hho]; exact ha, he⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
  have hpb := List.find?_some hb
  simp only [decide_eq_true_eq] at hpb
  have hab : b = a := eq_of_mem_partGraph_edges H c hpb.1 ha hpb.2 he
  unfold assign
  rw [hb, hab]
  rfl

/-- `E(H_Y) ⊆ E_l(Y)` at the round level: on a valid round, every edge of the part graph of a
pre-part is assigned to it. -/
theorem partGraph_edges_subset_E (h : Valid H c) {a : Addr} (ha : a ∈ prePartAddrs H c) :
    (partGraph H c a).edges ⊆ E H c a := by
  intro e he
  exact (mem_E H c).2 ⟨(partGraph_le_graph' H c a).2 he,
    assign_of_mem_partGraph H c h.2.2.2.2.2 ha he⟩

end Round

namespace Run

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V)

theorem E_of_isRound {l : ℕ} (hl : run.IsRound l) (a : Addr) :
    run.E G l a = Round.E (run.graph G l) (run.choice l) a := if_pos hl

/-- `E(H_Y) ⊆ E_{r(Y)}(Y)` for every ancestor `Y` of a valid run. -/
theorem ancGraph_edges_subset_E {Dstar : ℝ} (h : run.Valid G Dstar) {Y : PartId}
    (hY : Y ∈ run.ancestors G) : (run.ancGraph G Y).edges ⊆ run.E G Y.1 Y.2 := by
  have hpre : Y.2 ∈ run.prePartAddrs G Y.1 := (mem_ancestors run G).1 hY
  have hl : run.IsRound Y.1 := isRound_of_mem_prePartAddrs hpre
  rw [prePartAddrs_of_isRound run G hl] at hpre
  rw [E_of_isRound run G hl]
  exact Round.partGraph_edges_subset_E _ _ (Valid.round run G h hl) hpre

/-- The sets `E_l(Z)` of an earlier round are disjoint from `E(G_{l'})` for every later `l'`:
an edge of `E(G_{l'})`, `l < l'`, was passed down at round `l`. -/
theorem disjoint_E_graph_edges {l l' : ℕ} (hll' : l < l') (a : Addr) :
    Disjoint (run.E G l a) (run.graph G l').edges := by
  by_cases hl : run.IsRound l
  · rw [E_of_isRound run G hl]
    have hsub : (run.graph G l').edges ⊆ (run.graph G (l + 1)).edges :=
      graph_edges_subset_of_le run G hll'
    rw [graph_succ_of_isRound run G hl, Round.next_edges] at hsub
    exact Disjoint.mono_right hsub (Round.disjoint_passed_E _ _ a).symm
  · simp [E, hl]

/-- The sets `E_{r(Y)}(Y)` of distinct ancestors (of any rounds) are disjoint. -/
theorem disjoint_E_of_ne {Y Y' : PartId} (hne : Y ≠ Y') :
    Disjoint (run.E G Y.1 Y.2) (run.E G Y'.1 Y'.2) := by
  rcases lt_trichotomy Y.1 Y'.1 with hlt | heq | hgt
  · exact Disjoint.mono_right
      ((E_subset_graph'_edges run G Y'.1 Y'.2).trans (Round.graph'_le _ _).2)
      (disjoint_E_graph_edges run G hlt Y.2)
  · have h2 : Y.2 ≠ Y'.2 := fun h2 => hne (Prod.ext heq h2)
    rw [← heq]
    by_cases hl : run.IsRound Y.1
    · rw [E_of_isRound run G hl, E_of_isRound run G hl]
      exact Round.disjoint_E _ _ h2
    · simp [E, hl]
  · exact (Disjoint.mono_right
      ((E_subset_graph'_edges run G Y.1 Y.2).trans (Round.graph'_le _ _).2)
      (disjoint_E_graph_edges run G hgt Y'.2)).symm

end Run

end HB

/-- [s2:propStructure] (iii), the clauses used by JS-LC and J⁺: "`E(H_Y) ⊆ E_{r(Y)}(Y)` for every
ancestor `Y`; every edge of `E_{r(Y)}(Y)` has both ends in `V(Y)`; the graphs `H_Y` of all
ancestors `Y` of all rounds are pairwise edge-disjoint", with the disjointness of the sets
`E_{r(Y)}(Y)` (`Y` light) and `E_l(Z)` (`Z ∈ Std_l`). Proved from `run.Valid G Dstar` alone (fix
round 1 of unit P2J; formerly a declared-input stub). -/
theorem structureHY : EG.Spec.StructureHYStatement := by
  intro V _ G Dstar run hrun
  refine ⟨fun Y hY => HB.Run.ancGraph_edges_subset_E run G hrun hY,
    fun Y _ => HB.Run.E_subset_sym2 run G Y.1 Y.2,
    fun Y _ Y' _ hne => HB.Run.disjoint_E_of_ne run G hne,
    fun Y hY Y' hY' hne => ?_⟩
  exact Disjoint.mono (HB.Run.ancGraph_edges_subset_E run G hrun hY)
    (HB.Run.ancGraph_edges_subset_E run G hrun hY') (HB.Run.disjoint_E_of_ne run G hne)

end EG
