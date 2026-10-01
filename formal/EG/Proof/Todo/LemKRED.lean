module

public import EG.Spec.Light.KRED
public import EG.Spec.Light.Child
public import EG.Spec.Light.Parent
public import EG.Spec.Light.Demoted
public import EG.Spec.Light.Stages
public import EG.Spec.HB.Structure
public import EG.Spec.HB.StructureHY
public import EG.Proof.Light.Child
public import EG.Proof.Light.ParentAvail
public import EG.Proof.Light.ParentSum
public import EG.Proof.Todo.LemParent
public import EG.Proof.Todo.LemDemoted
public import EG.Proof.Todo.EqPl
public import EG.Proof.Todo.StructurePartition
public import EG.Proof.HB.StructureHY
public import EG.Lib.Light.KREDStep
public import EG.Lib.Light.Constants
public import EG.Lib.Gamma.Full

/-!
# P3 stub: `EG.Spec.LemKREDStatement` (s5:lemKRED)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.LemKRED`; consumers import this module.

Proof (P3), as in `s5.tex`:
* "The edge partition": s2:propStructure (iii) (`EG.Todo.StructurePartition`, `EG.structureHY`)
  gives `E(G) \ K_std \ ⋃_Y Lent_ext(Y) = ⊔_l E(Cyc_l) ⊔ E_0 ⊔ ⊔_Y (E_{r(Y)}(Y) \ Lent_ext(Y))`;
* the long cycles and the edges of `E_0` are output directly (at most `n` and `< D_* n/2`);
* the light-part edges: the round-by-round construction (`EG.Light.KHyp.exists_decomp`, Lib
  `EG/Lib/Light/KREDStep.lean`) with Lemma s5:lemChild (`EG.lemChild`), Lemma s5:lemDemoted
  (`EG.Todo.LemDemoted`), Lemma s5:lemParent (`EG.Todo.LemParent`, and the disjointness of the
  available U-lent sets, `EG.lemParentAvailDisjoint`);
* "Cost": child vortices `≤ 369 Σ_Z |Pl(Z)| ≤ 369(2n + lp)` by (s5:eqPl) (`EG.Todo.EqPl`), demoted
  parts `≤ 80 dem`, U-chaining `≤ ε_ch(D_*) n` (`EG.lemParentSum`); the total
  `(D_*/2 + 739 + ε_ch) n + 80 dem + 369 lp` is at most the stated bound (`ε_K = ε_ch`).
-/

public section

namespace EG.Todo

open EG.HB EG.Stage1 EG.Light

/-- Proved in P3. [s5:lemKRED] see `EG.Spec.LemKREDStatement`. -/
theorem LemKRED : EG.Spec.LemKREDStatement := by
  classical
  intro V _ G N0 Dstar run hR ω hω Lext hLext
  have hv : run.Valid G Dstar := hR.valid
  have hHY := EG.structureHY V G Dstar run hv
  have hN0 : (2 : ℝ) ^ 40 ≤ N0 := hR.n0Cond.two_pow_forty_le
  have hn : 0 < G.card := by
    have := hR.n0_le_card
    have : (0 : ℝ) < G.card := by linarith [show (0 : ℝ) < 2 ^ 40 by positivity]
    exact_mod_cast this
  have hP := EG.Todo.StructurePartition V G Dstar run hR.gamma2a hn hv
  obtain ⟨-, hpart, hcyc_disj, hcyc_E0, hcyc_E, hE_E0, hE_E, -, hcyc_card, hE0_card⟩ := hP
  set LP := run.lightParts G with hLP
  set SP := run.stdParts G with hSP
  have hanc : ∀ Y ∈ LP, Y ∈ run.ancestors G := fun Y hY => by
    rw [hLP] at hY
    unfold Run.lightParts at hY
    exact (Finset.mem_filter.1 hY).1
  have hLPround : ∀ Y ∈ LP, 1 ≤ Y.1 ∧ Y.1 ≤ run.R := fun Y hY =>
    Run.isRound_of_mem_parts run G (Finset.mem_filter.1 hY).1
  -- the hypotheses of the construction
  have hK : KHyp ω Lext := by
    refine ⟨hLPround, fun Y hY => hHY.1 Y (hanc Y hY), fun Y hY => ?_,
      fun Y hY Y' hY' hne => hHY.2.2.1 Y (hanc Y hY) Y' (hanc Y' hY') hne, hLext,
      EG.lemParentAvailDisjoint V G N0 Dstar run hR ω hω,
      fun Z hZ hd => (EG.lemChild V G N0 Dstar run hR ω hω Z hZ hd).2,
      fun Y hY hd => (EG.Todo.LemDemoted V G N0 Dstar run hR ω hω Y hY hd).2.2, ?_⟩
    · rw [← ancGraph_eq_X_of_isLight (isLight_of_mem_lightParts hY)]
      exact hHY.1 Y (hanc Y hY)
    · intro l h3 hlR H0 arcs hA
      obtain ⟨LentU, D, cap, h1, h2, h3', -, hcap, hsum, h7⟩ :=
        EG.Todo.LemParent V G N0 Dstar run hR ω hω l h3 hlR H0 arcs hA
      refine ⟨LentU, D, h1, h2, h3', ?_, h7⟩
      rw [pbound_eq]
      linarith
  obtain ⟨DL, hDL, hDLlen⟩ := hK.exists_decomp
  -- the long cycles and `E_0`
  set Cyc := (Finset.Icc 1 run.R).biUnion run.cycEdges with hCyc
  have hdC : IsDecomp ((Cyc : Finset (Sym2 V)) : Set (Sym2 V))
      ((Finset.Icc 1 run.R).toList.flatMap fun l => (run.cycles l).map Obj.cycle) := by
    refine isDecomp_finset_biUnion _ ?_ fun l hl => isDecomp_cycEdges hv hl
    intro l hl l' hl' hne
    exact hcyc_disj l (Finset.mem_coe.1 hl) l' (Finset.mem_coe.1 hl') hne
  have hdE0 : IsDecomp ((run.E0 G : Finset (Sym2 V)) : Set (Sym2 V))
      ((run.E0 G).toList.map Obj.edge) :=
    isDecomp_singletons _ fun e he => (run.graph G (run.R + 1)).loopless e he
  set L := LP.biUnion fun Z => run.E G Z.1 Z.2 \ Lext Z with hL
  have hLsub : ∀ e ∈ L, ∃ Z ∈ LP, e ∈ run.E G Z.1 Z.2 := by
    intro e he
    obtain ⟨Z, hZ, he⟩ := Finset.mem_biUnion.1 he
    exact ⟨Z, hZ, (Finset.mem_sdiff.1 he).1⟩
  have hLPsub : ∀ Y ∈ LP, Y ∈ LP ∪ SP := fun Y hY => Finset.mem_union_left _ hY
  have hd_CE0 : Disjoint Cyc (run.E0 G) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.1 he
    exact Finset.disjoint_left.1 (hcyc_E0 l hl) he he'
  have hd_CE0_L : Disjoint (Cyc ∪ run.E0 G) L := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨Z, hZ, heZ⟩ := hLsub e he'
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.1 he
      exact Finset.disjoint_left.1 (hcyc_E l hl Z (hLPsub Z hZ)) he heZ
    · exact Finset.disjoint_left.1 (hE_E0 Z (hLPsub Z hZ)) heZ he
  -- the set identity
  have hLP_SP : ∀ Y ∈ LP, ∀ Y' ∈ SP, Y ≠ Y' := by
    rintro Y hY Y' hY' rfl
    have h1 := (Finset.mem_filter.1 hY).2
    rw [hSP] at hY'
    unfold Run.stdParts at hY'
    exact (Finset.mem_filter.1 hY').2 h1
  have hKstd : ∀ e, e ∈ Kstd G run ↔ ∃ Y ∈ SP, e ∈ run.E G Y.1 Y.2 := by
    intro e
    simp only [Kstd, Finset.mem_biUnion]
    constructor
    · rintro ⟨l, hl, a, ha, he⟩
      exact ⟨(l, a), (Run.mem_stdParts run G).2 ha, he⟩
    · rintro ⟨Y, hY, he⟩
      refine ⟨Y.1, ?_, Y.2, (Run.mem_stdParts run G).1 hY, he⟩
      have : Y ∈ run.parts G := by
        rw [hSP] at hY; unfold Run.stdParts at hY; exact (Finset.mem_filter.1 hY).1
      exact Finset.mem_Icc.2 (Run.isRound_of_mem_parts run G this)
  have hLext_sub : ∀ Y ∈ LP, Lext Y ⊆ run.E G Y.1 Y.2 := fun Y hY => hK.Lext_subset hY
  have hset : ((G.edges \ Kstd G run) \ LP.biUnion Lext) = (Cyc ∪ run.E0 G) ∪ L := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, not_exists, not_and]
    constructor
    · rintro ⟨⟨heG, heK⟩, heL⟩
      rw [hpart] at heG
      rcases Finset.mem_union.1 heG with h1 | h1
      · rcases Finset.mem_union.1 h1 with h1 | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
      · obtain ⟨Y, hY, heY⟩ := Finset.mem_biUnion.1 h1
        rcases Finset.mem_union.1 hY with hY | hY
        · exact Or.inr (Finset.mem_biUnion.2 ⟨Y, hY, Finset.mem_sdiff.2 ⟨heY, heL Y hY⟩⟩)
        · exact absurd ((hKstd e).2 ⟨Y, hY, heY⟩) heK
    · intro he
      have heG : e ∈ G.edges := by
        rw [hpart]
        rcases he with (he | he) | he
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
        · obtain ⟨Z, hZ, heZ⟩ := hLsub e he
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨Z, hLPsub Z hZ, heZ⟩)
      -- `e` avoids `E_{r(Y)}(Y)` for `Y ∈ Std` and `Lent_ext(Y)` unless it lies in `L` at `Y`
      rcases he with (he | he) | he
      · obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.1 he
        refine ⟨⟨heG, fun hK' => ?_⟩, fun Y hY hL' => ?_⟩
        · obtain ⟨Y, hY, heY⟩ := (hKstd e).1 hK'
          exact Finset.disjoint_left.1 (hcyc_E l hl Y (Finset.mem_union_right _ hY)) he heY
        · exact Finset.disjoint_left.1 (hcyc_E l hl Y (hLPsub Y hY)) he (hLext_sub Y hY hL')
      · refine ⟨⟨heG, fun hK' => ?_⟩, fun Y hY hL' => ?_⟩
        · obtain ⟨Y, hY, heY⟩ := (hKstd e).1 hK'
          exact Finset.disjoint_left.1 (hE_E0 Y (Finset.mem_union_right _ hY)) heY he
        · exact Finset.disjoint_left.1 (hE_E0 Y (hLPsub Y hY)) (hLext_sub Y hY hL') he
      · obtain ⟨Z, hZ, he⟩ := Finset.mem_biUnion.1 he
        obtain ⟨heZ, heLZ⟩ := Finset.mem_sdiff.1 he
        refine ⟨⟨heG, fun hK' => ?_⟩, fun Y hY hL' => ?_⟩
        · obtain ⟨Y, hY, heY⟩ := (hKstd e).1 hK'
          exact Finset.disjoint_left.1 (hE_E Z (hLPsub Z hZ) Y (Finset.mem_union_right _ hY)
            (hLP_SP Z hZ Y hY)) heZ heY
        · by_cases hYZ : Y = Z
          · exact heLZ (hYZ ▸ hL')
          · exact Finset.disjoint_left.1 (hE_E Y (hLPsub Y hY) Z (hLPsub Z hZ) hYZ)
              (hLext_sub Y hY hL') heZ
  -- the decomposition
  refine ⟨((Finset.Icc 1 run.R).toList.flatMap fun l => (run.cycles l).map Obj.cycle) ++
      (run.E0 G).toList.map Obj.edge ++ DL, ?_, ?_⟩
  · rw [hset]
    exact isDecomp_union_finset' (isDecomp_union_finset' hdC hdE0 hd_CE0) hDL hd_CE0_L
  · -- the count
    simp only [List.length_append, length_flatMap_toList, List.length_map, Finset.length_toList,
      Nat.cast_add]
    have hn0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
    have c1 : ((∑ l ∈ Finset.Icc 1 run.R, (run.cycles l).length : ℕ) : ℝ) ≤ G.card := by
      exact_mod_cast hcyc_card
    -- the cost of the construction
    have hfib : ∀ Z ∈ (run.lightParts G).filter (fun Z => ¬ demoted ω Z),
        Z.1 ∈ Finset.Icc 1 run.R := fun Z hZ =>
      Finset.mem_Icc.2 (hLPround Z (Finset.mem_filter.1 hZ).1)
    have hPl : ∑ l ∈ Finset.Icc 1 run.R, ∑ Z ∈ childParts ω l, (Pl ω Z).card =
        ∑ Z ∈ (run.lightParts G).filter (fun Z => ¬ demoted ω Z), (Pl ω Z).card := by
      rw [← Finset.sum_fiberwise_of_maps_to hfib]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext Z
      rw [mem_childParts', Finset.mem_filter, Finset.mem_filter]
      tauto
    have hfib' : ∀ Z ∈ (run.lightParts G).filter (fun Z => demoted ω Z),
        Z.1 ∈ Finset.Icc 1 run.R := fun Z hZ =>
      Finset.mem_Icc.2 (hLPround Z (Finset.mem_filter.1 hZ).1)
    have hdem : ∑ l ∈ Finset.Icc 1 run.R, ∑ Z ∈ (run.lightParts G).filter
        (fun Z => Z.1 = l ∧ demoted ω Z), (run.ancVerts G Z).card = dem ω := by
      rw [dem, ← Finset.sum_fiberwise_of_maps_to hfib']
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr ?_ fun _ _ => rfl
      ext Z
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
      tauto
    have hpb : ∑ l ∈ Finset.Icc 1 run.R, (if 3 ≤ l then pbound G run l else 0) ≤
        epsChain Dstar * (G.card : ℝ) := by
      rw [← Finset.sum_filter]
      have hf : (Finset.Icc 1 run.R).filter (fun l => 3 ≤ l) = Finset.Icc 3 run.R := by
        ext l; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hf]
      have := EG.lemParentSum V G N0 Dstar run hR
      simpa only [pbound_eq] using this
    have hcost : ∑ l ∈ Finset.Icc 1 run.R, kcost ω l =
        369 * ((∑ l ∈ Finset.Icc 1 run.R, ∑ Z ∈ childParts ω l, (Pl ω Z).card : ℕ) : ℝ) +
          80 * ((∑ l ∈ Finset.Icc 1 run.R, ∑ Z ∈ (run.lightParts G).filter
            (fun Z => Z.1 = l ∧ demoted ω Z), (run.ancVerts G Z).card : ℕ) : ℝ) +
          ∑ l ∈ Finset.Icc 1 run.R, (if 3 ≤ l then pbound G run l else 0) := by
      simp only [kcost, Finset.sum_add_distrib, ← Finset.mul_sum, Nat.cast_sum]
    have hEqPl := EG.Todo.EqPl V G N0 Dstar run hR ω hω
    have hPl' : ((∑ l ∈ Finset.Icc 1 run.R, ∑ Z ∈ childParts ω l, (Pl ω Z).card : ℕ) : ℝ) ≤
        2 * (G.card : ℝ) + (lp ω : ℝ) := by
      rw [hPl]; exact_mod_cast hEqPl
    rw [hcost, hdem] at hDLlen
    have hK' : epsChain Dstar = Chain.epsK Dstar := epsChain_eq_epsK Dstar
    rw [← hK']
    have hdem0 : (0 : ℝ) ≤ dem ω := Nat.cast_nonneg _
    have hlp0 : (0 : ℝ) ≤ lp ω := Nat.cast_nonneg _
    have hpb0 := hpb
    linarith

end EG.Todo
