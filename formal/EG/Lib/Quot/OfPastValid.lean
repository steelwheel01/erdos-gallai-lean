module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Lib.Quot.Round
public import EG.Lib.Quot.CandCount
public import EG.Lib.Chain.StageInst
public import EG.Lib.Chain.Design
public import EG.Lib.Chain.Lending
public import EG.Lib.Lend.Standing
public import EG.Lib.Stage1.Pool
public import EG.Proof.Todo.CandCount
public import EG.Proof.HB.StructureHY
public import EG.Proof.HB.TowerBM

/-!
# The past of a run is a valid round input (`RoundInput.ofPast_valid`, OBL-P1-1)

The round lemmas of s7 (s7:lemWellDef, s7:lemMULT, s7:lemLift, s7:lemCC, s7:lemUltra) are stated
for an abstract round input `I : RoundInput V` with `I.Valid`. This file shows that the past of
round `3 ≤ l ≤ R` of a run, `RoundInput.ofPast run G δ S π l J`, is valid whenever
`RunHyp N0 D_* G run`, `δ` is a designation, the stage data `S` are coherent (every stage-1
outcome of positive weight, `EG.Chain.coherent_ofOutcome`) and `J` has the properties of
Lemma J⁺ (`JPlusProps`). Every field is a sentence the manuscript's round step cites:

* `M_ge`: "`M_l ≥ 2^{40}`" (definition of `M_l`, `EG.Stage1.two_pow_le_M`);
* `Hcd_ge`: s7:lemCand (iv) "`Hcd_l ≥ 2^{10}M_l^{10}`", from `M_l ≤ λ_{l-2}^{1.6}` (s2:lemTower (b),
  `EG.towerBM`) and `λ_{l-2} ≥ 2^{256}` (Γ1(a));
* `roles`: s6:lemJplus (J3) (`EG.Lib.Chain.Lending`);
* the typing fields and (J1), (J2): s6:lemJplus (i), (J1), (J2) (`JPlusProps`,
  `JPlusProps.J1hub_ports`);
* `cls_*`: s6:defDesign (`IsDesignation`);
* `ljv_in`, `ljv_disj`, `ljv_J`: s3:defCOL (ii) (`LJV_{Y,l} ⊆ E(H_Y)`, no JV class outside the late
  rounds; `StageData.Coherent`) and s2:propStructure (iii) / s6:lemJplus (iii) (`EG.structureHY`);
* `lendGood_ports`: s6:defLending (`Q*_Z` has lend-good classes);
* `good_cand`: s7:lemCand (iv) (`EG.Todo.candCount_univ`);
* `pool_sub`, `ports_sub`: `Pool_l, Q*_Z ⊆ V(G)`.
-/

public section

namespace EG.Quot

open EG.HB EG.Chain

universe u

variable {V : Type u} [DecidableEq V]

/-- [s7:lemCand] (iv) "`Hcd_l ≥ 2^{10}M_l^{10}`" for every round `3 ≤ l ≤ R` of a run with
`RunHyp` (from `M_l ≤ λ_{l-2}^{1.6}`, s2:lemTower (b), and `λ_{l-2} ≥ 2^{256}`). -/
theorem hcd_ge_of_runHyp {N0 Dstar : ℝ} {G : FGraph V} {run : Run V}
    (hR : RunHyp N0 Dstar G run) {l : ℕ} (hl : 3 ≤ l) (hlR : l ≤ run.R) :
    (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 ≤ Hcd run G l := by
  obtain ⟨hΓ1, -, -, -, hd1, hrun⟩ := hR
  have hBM := EG.towerBM V G Dstar run hΓ1.1 hrun hd1
  have hRl2 : run.IsRound (l - 2) := ⟨by omega, by omega⟩
  have hlam_ge := EG.Standing.lam_ge hΓ1 hrun hRl2
  have hM1 : (1 : ℝ) ≤ (run.M G l : ℝ) := by
    have := Stage1.two_pow_le_M G run l
    exact_mod_cast le_trans Nat.one_le_two_pow this
  have hML := hBM.1 l (by omega) hlR
  exact Hcd_ge_arith hM1 (hML.1.trans hML.2) (le_trans (by norm_num) hlam_ge)

/-- A port of round `l` (`u ∈ ⋃_Z Q*_Z`) is a classed port `u ∈ Q_Z` of some `Z ∈ Std_l`. -/
theorem exists_classed_of_mem_qsRound {run : Run V} {G : FGraph V} {δ : Designation V}
    {S : StageData V} {l : ℕ} {u : V} (hu : u ∈ qsRound run G δ S l) :
    ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ u ∈ qs run G δ S l a := by
  obtain ⟨a, ha, hua⟩ := (mem_qsRound run G δ S).1 hu
  exact ⟨a, ha, qs_subset_classed run G δ S l a hua, hua⟩

/-- **OBL-P1-1** (`RoundInput.ofPast_valid`): the past of round `3 ≤ l ≤ R` of a run, read by the
round step of s7:consRound, satisfies `RoundInput.Valid`, for every coherent stage-data record
`S`, every pool-label family `π` and every `J` with the properties of Lemma J⁺ (s6:lemJplus). -/
theorem ofPast_valid {N0 Dstar : ℝ} {G : FGraph V} {run : Run V} {δ : Designation V}
    {S : StageData V} (π : ↥G.verts → Option (ℕ × ℕ)) {l : ℕ} {J : Finset (Sym2 V)}
    (hR : RunHyp N0 Dstar G run) (hδ : IsDesignation run G δ) (hS : S.Coherent run G)
    (hl : 3 ≤ l) (hlR : l ≤ run.R) (hJ : JPlusProps run G δ S l J) :
    (RoundInput.ofPast run G δ S π l J).Valid := by
  have hrun : run.Valid G Dstar := hR.2.2.2.2.2
  obtain ⟨hHY1, -, hHY3, hHY4⟩ := EG.structureHY V G Dstar run hrun
  have hJeq : (RoundInput.ofPast run G δ S π l J).J = J := ofPast_J run G δ S π l hJ
  refine
    { M_ge := Stage1.two_pow_le_M G run l
      Hcd_ge := hcd_ge_of_runHyp hR hl hlR
      roles := ⟨disjoint_D_freshCentres run G l, disjoint_D_qsRound run G δ S l,
        disjoint_D_lostRound run G δ S l, disjoint_freshCentres_qsRound run G δ S l,
        disjoint_freshCentres_lostRound run G δ S l, disjoint_qsRound_lostRound run G δ S l⟩
      hub_typed := ?_
      fr_typed := ?_
      par_typed := ?_
      lost_typed := ?_
      J_sub := ?_
      J1 := ?_
      J2 := ?_
      J2tot := ?_
      cls_anc := ?_
      cls_round := ?_
      cls_mem := ?_
      ljv_in := ?_
      ljv_disj := ?_
      ljv_J := ?_
      lendGood_ports := ?_
      good_cand := ?_
      pool_sub := ?_
      ports_sub := ?_ }
  · -- hub typing
    intro e he
    change e ∈ Chain.Jhub run G δ S l J at he
    simp only [Chain.Jhub, Finset.mem_filter] at he
    obtain ⟨-, h, Y, hh⟩ := he
    have hD := hh.mem_D
    obtain ⟨a, ha, -, u, rfl, -, hu, -⟩ := hh
    exact ⟨h, hD, u, (mem_qsRound run G δ S).2 ⟨a, ha, hu⟩, rfl⟩
  · -- fresh typing
    intro e he
    change e ∈ Chain.Jfr run G δ S l J at he
    simp only [Chain.Jfr, Finset.mem_filter] at he
    obtain ⟨-, x, Y, hx⟩ := he
    obtain ⟨a, ha, -, u, rfl, hxa, hu, -⟩ := hx
    exact ⟨x, (mem_freshCentres run G).2 ⟨a, ha, hxa⟩, u,
      (mem_qsRound run G δ S).2 ⟨a, ha, hu⟩, rfl⟩
  · -- PAR typing
    intro e he
    change e ∈ Chain.Jpar run G δ S l J at he
    simp only [Chain.Jpar, Finset.mem_filter] at he
    obtain ⟨-, a, ha, -, u, v, rfl, hu, hv, -⟩ := he
    exact ⟨u, (mem_qsRound run G δ S).2 ⟨a, ha, hu⟩, v, (mem_qsRound run G δ S).2 ⟨a, ha, hv⟩,
      rfl⟩
  · -- lost typing
    intro e he
    change e ∈ Chain.Jlost run G δ S l J at he
    simp only [Chain.Jlost, Finset.mem_filter] at he
    obtain ⟨-, v, Y, hv⟩ := he
    obtain ⟨a, ha, -, u, rfl, hva, hu, -⟩ := hv
    exact ⟨v, (mem_lostRound run G δ S).2 ⟨a, ha, hva⟩, u,
      (mem_qsRound run G δ S).2 ⟨a, ha, hu⟩, rfl⟩
  · -- `J_l ⊆ E(G)`
    rw [hJeq]
    exact hJ.subset_edges
  · -- (J1)
    intro h Y
    exact hJ.J1hub_ports h Y
  · -- (J2)
    intro v hv
    rw [hJeq]
    exact hJ.J2out v hv
  · -- (J2), total
    rw [hJeq]
    exact hJ.J2card
  · -- classes are ancestors
    intro u hu
    obtain ⟨a, ha, huc, -⟩ := exists_classed_of_mem_qsRound hu
    exact hδ.mem_ancestors hl ha huc
  · -- rounds of classes
    intro u hu
    obtain ⟨a, ha, huc, -⟩ := exists_classed_of_mem_qsRound hu
    exact ⟨hδ.one_le_round hl ha huc, hδ.round_add_two_le hl ha huc⟩
  · -- `u ∈ V(Y(u))`
    intro u hu
    obtain ⟨a, ha, huc, -⟩ := exists_classed_of_mem_qsRound hu
    exact hδ.mem_ancVerts hl ha huc
  · -- `LJV_{Y,l} ⊆ E(H_Y)`, `H_Y ≤ G` a graph on `V(Y)`
    intro Y _ e he
    have he' : e ∈ (run.ancGraph G Y).edges := hS.ljv_sub Y l he
    refine ⟨(ancGraph_le (G := G) (run := run) Y).2 he', fun v hv => ?_⟩
    have := (run.ancGraph G Y).edge_verts e he' v hv
    rwa [Run.ancGraph_verts] at this
  · -- the graphs `H_Y` are pairwise edge-disjoint
    intro Y hY Y' hY' hne
    exact Finset.disjoint_of_subset_left (hS.ljv_sub Y l)
      (Finset.disjoint_of_subset_right (hS.ljv_sub Y' l) (hHY4 Y hY Y' hY' hne))
  · -- junction edges are not J-edges (s6:lemJplus (iii))
    intro Y hY
    change Disjoint (S.ljv Y l) (RoundInput.ofPast run G δ S π l J).J
    rw [hJeq, Finset.disjoint_left]
    intro e heY heJ
    obtain ⟨a, ha, hea⟩ := hJ.exists_mem_E heJ
    have hlate : l ∈ Stage1.lateRounds run Y.1 := by
      by_contra hn
      rw [hS.ljv_eq_empty Y l hn] at heY
      exact Finset.notMem_empty e heY
    have hlate' : Y.1 + 2 ≤ l := (Finset.mem_Icc.1 hlate).1
    have heE : e ∈ run.E G Y.1 Y.2 := hHY1 Y hY (hS.ljv_sub Y l heY)
    have hZ : ((l, a) : PartId) ∈ run.ancestors G :=
      (Run.mem_ancestors run G).2 ((Run.mem_Std_iff run G).1 ha).1
    have hne : Y ≠ (l, a) := by
      intro h
      rw [h] at hlate'
      exact absurd hlate' (by simp)
    exact Finset.disjoint_left.1 (hHY3 Y hY (l, a) hZ hne) heE hea
  · -- ports have lend-good classes
    intro u hu
    obtain ⟨a, -, -, hqs⟩ := exists_classed_of_mem_qsRound hu
    exact not_lendBad_of_mem_qs run G δ S hqs
  · -- s7:lemCand (iv): a JV-good port has `|Cand_l(u)| ≥ Hcd_l`
    intro u hu hgood
    obtain ⟨a, ha, huc, -⟩ := exists_classed_of_mem_qsRound hu
    have h1 := hδ.one_le_round hl ha huc
    have h2 := hδ.round_add_two_le hl ha huc
    have hcp : u ∈ classedPorts run G l := (mem_classedPorts run G).2 ⟨a, ha, huc⟩
    have hC := EG.Todo.candCount_univ V N0 Dstar G run δ hR hδ (fun ω => stageOf ω)
      (fun _ _ _ => rfl) l u hl hcp
    have hiv := hC.2.2.2.2.2.2.2.1 S π hgood
    rw [ofPast_cand run G δ S π l J h1 h2]
    exact hiv
  · -- `Pool_l ⊆ V(G)`
    intro v hv
    exact (Stage1.mem_poolL.1 hv).1
  · -- ports are vertices of `G`
    intro u hu
    obtain ⟨a, -, huc, -⟩ := exists_classed_of_mem_qsRound hu
    exact Run.Z0_subset_verts run G l a (classed_subset_Z0 run G l a huc)

/-- `ofPast_valid` at the past of a stage-1 outcome of positive weight
(`pastOf run G δ ω l J`, stage data `stageOf ω`, pool labels `ω.pool`). -/
theorem pastOf_valid {N0 Dstar : ℝ} {G : FGraph V} {run : Run V} {δ : Designation V}
    {ω : Stage1.Outcome G run} (hω : ω ∈ (Stage1.law G run).supp) {l : ℕ}
    {J : Finset (Sym2 V)} (hR : RunHyp N0 Dstar G run) (hδ : IsDesignation run G δ)
    (hl : 3 ≤ l) (hlR : l ≤ run.R) (hJ : JPlusProps run G δ (stageOf ω) l J) :
    (pastOf run G δ ω l J).Valid :=
  ofPast_valid ω.pool hR hδ (coherent_ofOutcome hω _ _ _) hl hlR hJ

end EG.Quot
