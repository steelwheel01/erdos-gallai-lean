module

public import EG.Lib.Chain.MixCSets
public import EG.Spec.Light.KRED
public import EG.Spec.HB.Parentless
public import EG.Spec.HB.Tower
public import EG.Spec.HB.TowerBM
public import EG.Lib.Gamma.Full

/-!
# Assembly of Theorem MIX-C (manuscript s6:thmMIXC (b), (c))

Unit P3-s6, round 1. From the chain of `EG.Chain.MixCA.chain_exists` (Construction s6:consOrder,
standalone part) and one application of Lemma K-RED (s5:lemKRED) with the final family
`Lent_ext(Y) := LentAll ∩ (⋃_{l,j} LJS_{Y,l,j} ∪ ⋃_l LJV_{Y,l})` (blueprint s6b ORDER-DECOUPLE),
the output

`D := D_KRED ++ (⋃_{l,Z} D^V(Z)) ++ (⋃_{3 ≤ l ≤ R} (JS-LC cycles of round l ++ Obj_l))`

is a decomposition of `E(G)` (s6:thmMIXC (b), `mixc_of_specs`), with the cost of s6:thmMIXC (c):
K-RED `(D_*/2 + 745 + ε_K)n + 80 dem + 369 lp`; TPV (T3) `169 Σ_Z |Ret_Z|` with
`|Ret_Z| ≤ |A_Z| + |F_Z| + |Lost_Z|`, `Σ|A_Z| ≤ ε_A n` (s2:lemTower(e)), `Σ|F_Z| ≤ 2n`
(s2:propParentless(i) (K4)), `Σ_Z |Lost_Z| = |Lost_l|`; JS-LC `Σ_l 126n/M_l + 1.5 Σ m` with
`Σ_l 1/M_l ≤ 2/D_*` (s2:lemTower(b)); consumer `Σ_l b(l, J_l)`.

The Specs used are hypotheses of `mixc_of_specs`.
-/

public section

namespace EG.Chain.MixCA

open EG.HB EG.Chain EG.Quot

universe u

variable {V : Type u} [DecidableEq V]

theorem isDecomp_union_finset {A B : Finset (Sym2 V)} {D₁ D₂ : List (Obj V)}
    (h₁ : IsDecomp (A : Set (Sym2 V)) D₁) (h₂ : IsDecomp (B : Set (Sym2 V)) D₂)
    (hd : Disjoint A B) : IsDecomp ((A ∪ B : Finset (Sym2 V)) : Set (Sym2 V)) (D₁ ++ D₂) :=
  (h₁.append h₂ (Finset.disjoint_coe.2 hd)).congr (Finset.coe_union _ _).symm

theorem isDecomp_congr_finset {A B : Finset (Sym2 V)} {D : List (Obj V)}
    (h : IsDecomp (A : Set (Sym2 V)) D) (hAB : A = B) : IsDecomp (B : Set (Sym2 V)) D :=
  hAB ▸ h

open Classical in
/-- **Theorem MIX-C (b), (c)** from the Specs of s4:lemTPV, s6:lemJSLC, the TPV bullet of
s6:thmMIXC (a), s2:propStructure(iii) (`StructureHY`), s5:lemKRED, s2:propParentless(i)
(`Fresh`), s2:lemTower(e) and (b). -/
theorem mixc_of_specs (hTPV : EG.Spec.TPVStatement.{u}) (hJSLC : EG.Spec.JSLCStatement.{u})
    (hApp : EG.Spec.MixCTPVApplicableStatement.{u}) (hHY : EG.Spec.StructureHYStatement.{u})
    (hKRED : EG.Spec.LemKREDStatement.{u}) (hFresh : EG.Spec.FreshStatement.{u})
    (hTowerE : EG.Spec.TowerEStatement.{u}) (hTowerBM : EG.Spec.TowerBMStatement.{u}) :
    EG.Spec.MixCStatement.{u} := by
  intro V _ G N0 Dstar run δ hrun hδ ω hω C b hb
  have hS : (stageOf ω).Coherent run G := coherent_ofOutcome hω _ _ _
  have hv := hrun.valid
  have hD := hrun.gamma1core
  have hd1 := hrun.le_d_one
  obtain ⟨outs, hspec⟩ := chain_exists hTPV hJSLC hApp hHY hrun hδ hω C
  -- notation
  set R := run.R with hR
  set LentAll : Finset (Sym2 V) := (Finset.Icc 1 R).biUnion (fun l => lent C l (outs l))
    with hLentAll
  have hlentGood : ∀ l, lent C l (outs l) ⊆ goodLent run G (stageOf ω) l := by
    intro l
    by_cases hl : 1 ≤ l ∧ l ≤ R
    · exact lent_subset_goodLent C (hspec l hl.1 hl.2)
    · have : lent C l (outs l) = ∅ := by
        unfold lent
        rw [if_neg (fun h => hl ⟨by omega, h.2⟩)]
      rw [this]; exact Finset.empty_subset _
  have hlent_eq : ∀ l, 3 ≤ l → l ≤ R →
      lent C l (outs l) = (outs l).LJS ∪ (C.out l (outs l).J).2 := by
    intro l h3 hlR
    unfold lent
    rw [if_pos ⟨h3, hlR⟩]
  have hlent_empty : ∀ l, ¬ (3 ≤ l ∧ l ≤ R) → lent C l (outs l) = ∅ := by
    intro l hl
    unfold lent
    rw [if_neg hl]
  -- `E_l(Z) \ F_l = E_l(Z) \ LentAll`
  have hEfut : ∀ l, 1 ≤ l → l ≤ R → ∀ a ∈ run.Std G l,
      run.E G l a \ futLent C outs l = run.E G l a \ LentAll := by
    intro l h1 hlR a ha
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨heE, hef⟩
      refine ⟨heE, fun heL => ?_⟩
      obtain ⟨l', hl', he'⟩ := Finset.mem_biUnion.1 heL
      by_cases hll : l < l'
      · exact hef (Finset.mem_biUnion.2 ⟨l', Finset.mem_Ioc.2 ⟨hll, (Finset.mem_Icc.1 hl').2⟩, he'⟩)
      · exact Finset.disjoint_left.1 (disjoint_goodLent_E hHY hv hS (l := l) (l' := l')
          (by omega) ha) (hlentGood l' he') heE
    · rintro ⟨heE, heL⟩
      refine ⟨heE, fun hef => heL ?_⟩
      obtain ⟨l', hl', he'⟩ := Finset.mem_biUnion.1 hef
      have := Finset.mem_Ioc.1 hl'
      exact Finset.mem_biUnion.2 ⟨l', Finset.mem_Icc.2 ⟨by omega, this.2⟩, he'⟩
  -- the TPV pieces
  have hEV : ∀ l, 1 ≤ l → l ≤ R → ∀ a ∈ run.Std G l,
      (outs l).EV a ⊆ run.E G l a ∧ Disjoint ((outs l).EV a) LentAll := by
    intro l h1 hlR a ha
    have h := ((hspec l h1 hlR).1 a ha).2.1
    rw [hEfut l h1 hlR a ha] at h
    constructor
    · intro e he
      have : e ∈ run.E G l a \ LentAll := h ▸ Finset.mem_union_left _ he
      exact (Finset.mem_sdiff.1 this).1
    · rw [Finset.disjoint_left]
      intro e he
      have : e ∈ run.E G l a \ LentAll := h ▸ Finset.mem_union_left _ he
      exact (Finset.mem_sdiff.1 this).2
  have hEQ : ∀ l, 1 ≤ l → l ≤ R → ∀ a ∈ run.Std G l,
      (outs l).EQ a ⊆ run.E G l a ∧ Disjoint ((outs l).EQ a) LentAll := by
    intro l h1 hlR a ha
    have h := ((hspec l h1 hlR).1 a ha).2.1
    rw [hEfut l h1 hlR a ha] at h
    constructor
    · intro e he
      have : e ∈ run.E G l a \ LentAll := h ▸ Finset.mem_union_right _ he
      exact (Finset.mem_sdiff.1 this).1
    · rw [Finset.disjoint_left]
      intro e he
      have : e ∈ run.E G l a \ LentAll := h ▸ Finset.mem_union_right _ he
      exact (Finset.mem_sdiff.1 this).2
  have hEQ_empty : ∀ l, l ≤ 2 → 1 ≤ l → ∀ a ∈ run.Std G l, (outs l).EQ a = ∅ := by
    intro l hl2 h1 a ha
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    obtain ⟨u, hu, -⟩ := ((hspec l h1 (by
      have := (Run.isRound_of_mem_prePartAddrs ((Run.mem_Std_iff run G).1 ha).1).2
      exact this)).1 a ha).2.2.2.2 e he
    rw [qs_of_le_two run G δ (stageOf ω) hl2] at hu
    exact Finset.notMem_empty u hu
  -- lent edges: in `G`, pairwise disjoint over rounds
  have hLentAll_edges : LentAll ⊆ G.edges := by
    intro e he
    obtain ⟨l, -, he⟩ := Finset.mem_biUnion.1 he
    exact goodLent_subset_edges hHY hv hS l (hlentGood l he)
  have hlent_disj : ∀ l l', l ≠ l' → Disjoint (lent C l (outs l)) (lent C l' (outs l')) :=
    fun l l' h => Finset.disjoint_of_subset_left (hlentGood l)
      (Finset.disjoint_of_subset_right (hlentGood l') (disjoint_goodLent hHY hv hS h))
  -- the family `Lent_ext`
  set Lext : PartId → Finset (Sym2 V) := fun Y => LentAll ∩ Light.lentJSJV ω Y with hLext
  have hLJSJV : ∀ Y ∈ run.ancestors G, ∀ e ∈ Light.lentJSJV ω Y,
      ∃ l, (∃ j < Stage1.KJS G run l, e ∈ (stageOf ω).ljs Y l j) ∨ e ∈ (stageOf ω).ljv Y l := by
    intro Y _ e he
    unfold Light.lentJSJV at he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨l, -, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.1 he
      exact ⟨l, Or.inl ⟨j, Finset.mem_range.1 hj, he⟩⟩
    · obtain ⟨l, -, he⟩ := Finset.mem_biUnion.1 he
      exact ⟨l, Or.inr he⟩
  have hLextHyp : Light.LentExtHyp ω Lext := by
    intro Y hY
    refine ⟨Finset.inter_subset_right, fun hdem => ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    obtain ⟨heL, heJ⟩ := Finset.mem_inter.1 he
    have hYa : Y ∈ run.ancestors G := (Finset.mem_filter.1 hY).1
    obtain ⟨l, -, hel⟩ := Finset.mem_biUnion.1 heL
    obtain ⟨Y', hY', h'⟩ := goodLent_class (hlentGood l hel)
    obtain ⟨l2, h2⟩ := hLJSJV Y hYa e heJ
    have hYY := class_eq hHY hv hS hYa (mem_ancestors_of_lendGoodAnc hY') h2 h'
    subst hYY
    exact not_lendBad_of_lendGoodAnc hY' (Or.inl ⟨(Finset.mem_filter.1 hY).2, hdem⟩)
  -- `LentAll \ K_std ⊆ ⋃_Y Lent_ext(Y)`
  have hKstd : Light.Kstd G run =
      (Finset.Icc 1 R).biUnion (fun l => (run.Std G l).biUnion (fun a => run.E G l a)) := rfl
  have hLentKstd : ∀ e ∈ LentAll, e ∉ Light.Kstd G run →
      e ∈ (run.lightParts G).biUnion Lext := by
    intro e he heK
    obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.1 he
    obtain ⟨Y, hY, h⟩ := goodLent_class (hlentGood l hel)
    have hYa := mem_ancestors_of_lendGoodAnc hY
    have heH := class_subset hS h
    by_cases hlight : run.isLight G Y.1 Y.2
    · refine Finset.mem_biUnion.2 ⟨Y, ?_, Finset.mem_inter.2 ⟨he, ?_⟩⟩
      · exact Finset.mem_filter.2 ⟨hYa, hlight⟩
      · unfold Light.lentJSJV
        rcases h with ⟨j, hj, h⟩ | h
        · have hne : ((stageOf ω).ljs Y l j).Nonempty := ⟨e, h⟩
          have hlate : l ∈ Stage1.lateRounds run Y.1 := by
            by_contra hc
            exact hne.ne_empty (hS.ljs_eq_empty Y l j (fun h' => hc h'.1))
          refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨l, hlate, ?_⟩)
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, h⟩
        · have hne : ((stageOf ω).ljv Y l).Nonempty := ⟨e, h⟩
          have hlate : l ∈ Stage1.lateRounds run Y.1 := by
            by_contra hc
            exact hne.ne_empty (hS.ljv_eq_empty Y l hc)
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, hlate, h⟩)
    · exfalso
      apply heK
      rw [hKstd]
      have hpre := (Run.mem_ancestors run G).1 hYa
      have hR1 := Run.isRound_of_mem_prePartAddrs hpre
      refine Finset.mem_biUnion.2 ⟨Y.1, Finset.mem_Icc.2 hR1, Finset.mem_biUnion.2 ⟨Y.2,
        (Run.mem_Std_iff run G).2 ⟨hpre, hlight⟩, ancGraph_subset_E hHY hv hYa heH⟩⟩
  -- K-RED
  obtain ⟨DA, hDA, hDAlen⟩ := hKRED V G N0 Dstar run hrun ω hω Lext hLextHyp
  set EA : Finset (Sym2 V) := (G.edges \ Light.Kstd G run) \ (run.lightParts G).biUnion Lext
    with hEA
  -- the TPV objects
  set EB : ℕ → Finset (Sym2 V) := fun l => (run.Std G l).biUnion (outs l).EV with hEB
  set DB : List (Obj V) := (Finset.Icc 1 R).toList.flatMap
    (fun l => (run.Std G l).toList.flatMap (outs l).DV) with hDB
  have hDBdec : IsDecomp (((Finset.Icc 1 R).biUnion EB : Finset (Sym2 V)) : Set (Sym2 V)) DB := by
    refine isDecomp_finset_biUnion _ ?_ (fun l hl => ?_)
    · intro l hl l' hl' hll
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨a', ha', he'⟩ := Finset.mem_biUnion.1 he'
      have hl1 := Finset.mem_Icc.1 (Finset.mem_coe.1 hl)
      have hl1' := Finset.mem_Icc.1 (Finset.mem_coe.1 hl')
      exact Finset.disjoint_left.1 (disjoint_E_std hHY hv ha ha' (by simp [hll]))
        ((hEV l hl1.1 hl1.2 a ha).1 he) ((hEV l' hl1'.1 hl1'.2 a' ha').1 he')
    · have hl1 := Finset.mem_Icc.1 hl
      refine isDecomp_finset_biUnion _ ?_ (fun a ha => ((hspec l hl1.1 hl1.2).1 a ha).2.2.1)
      intro a ha a' ha' haa
      simp only [Function.onFun]
      exact Finset.disjoint_of_subset_left (hEV l hl1.1 hl1.2 a ha).1
        (Finset.disjoint_of_subset_right (hEV l hl1.1 hl1.2 a' ha').1
          (disjoint_E_std hHY hv ha ha' (by simp [haa])))
  -- the JS-LC and consumer objects
  set EQL : ℕ → Finset (Sym2 V) := fun l => (run.Std G l).biUnion (outs l).EQ with hEQLdef
  have hEQL : ∀ l, 1 ≤ l → l ≤ R → EQL l ⊆ Light.Kstd G run ∧ Disjoint (EQL l) LentAll := by
    intro l h1 hlR
    constructor
    · intro e he
      obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.1 he
      rw [hKstd]
      exact Finset.mem_biUnion.2 ⟨l, Finset.mem_Icc.2 ⟨h1, hlR⟩,
        Finset.mem_biUnion.2 ⟨a, ha, (hEQ l h1 hlR a ha).1 he⟩⟩
    · rw [Finset.disjoint_left]
      intro e he
      obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.1 he
      exact Finset.disjoint_left.1 (hEQ l h1 hlR a ha).2 he
  set ECD : ℕ → Finset (Sym2 V) := fun l => EQL l ∪ lent C l (outs l) with hECD
  set DCD : List (Obj V) := (Finset.Icc 3 R).toList.flatMap
    (fun l => (outs l).DC ++ (C.out l (outs l).J).1) with hDCD
  have hDCDl : ∀ l ∈ Finset.Icc 3 R,
      IsDecomp ((ECD l : Finset (Sym2 V)) : Set (Sym2 V)) ((outs l).DC ++ (C.out l (outs l).J).1) := by
    intro l hl
    have hl3 := Finset.mem_Icc.1 hl
    obtain ⟨hJ, hLJS, hDC, -, hJP⟩ := (hspec l (by omega) hl3.2).2 hl3.1 hl3.2
    have hObj := C.jc2 l (outs l).J hl3.1 hl3.2 hJP
    have hjc1 := C.jc1 l (outs l).J hl3.1 hl3.2 hJP
    have hLJV : (C.out l (outs l).J).2 ⊆ lent C l (outs l) := by
      rw [hlent_eq l hl3.1 hl3.2]; exact Finset.subset_union_right
    refine isDecomp_congr_finset (isDecomp_union_finset hDC hObj ?_) ?_
    · rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨he1, heJ⟩ := Finset.mem_sdiff.1 he
      rcases Finset.mem_union.1 he' with he' | he'
      · exact heJ he'
      · rcases Finset.mem_union.1 he1 with he1 | he1
        · exact Finset.disjoint_left.1 (hEQL l (by omega) hl3.2).2 he1
            (Finset.mem_biUnion.2 ⟨l, Finset.mem_Icc.2 ⟨by omega, hl3.2⟩, hLJV he'⟩)
        · exact Finset.disjoint_left.1 (disjoint_LJS_LJV hHY hv hS hLJS hjc1) he1 he'
    · show _ = (run.Std G l).biUnion (outs l).EQ ∪ lent C l (outs l)
      rw [hlent_eq l hl3.1 hl3.2]
      ext e
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1 | h1, -⟩ | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inl (hJ h1)
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · by_cases hj : e ∈ (outs l).J
          · exact Or.inr (Or.inl hj)
          · exact Or.inl ⟨Or.inl h1, hj⟩
        · by_cases hj : e ∈ (outs l).J
          · exact Or.inr (Or.inl hj)
          · exact Or.inl ⟨Or.inr h1, hj⟩
        · exact Or.inr (Or.inr h1)
  have hDCDdec : IsDecomp (((Finset.Icc 3 R).biUnion ECD : Finset (Sym2 V)) : Set (Sym2 V)) DCD := by
    refine isDecomp_finset_biUnion _ ?_ hDCDl
    intro l hl l' hl' hll
    simp only [Function.onFun]
    have hl3 := Finset.mem_Icc.1 (Finset.mem_coe.1 hl)
    have hl3' := Finset.mem_Icc.1 (Finset.mem_coe.1 hl')
    rw [Finset.disjoint_left]
    intro e he he'
    rcases Finset.mem_union.1 he with he | he <;> rcases Finset.mem_union.1 he' with he' | he'
    · obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨a', ha', he'⟩ := Finset.mem_biUnion.1 he'
      exact Finset.disjoint_left.1 (disjoint_E_std hHY hv ha ha' (by simp [hll]))
        ((hEQ l (by omega) hl3.2 a ha).1 he) ((hEQ l' (by omega) hl3'.2 a' ha').1 he')
    · exact Finset.disjoint_left.1 (hEQL l (by omega) hl3.2).2 he
        (Finset.mem_biUnion.2 ⟨l', Finset.mem_Icc.2 ⟨by omega, hl3'.2⟩, he'⟩)
    · exact Finset.disjoint_left.1 (hEQL l' (by omega) hl3'.2).2 he'
        (Finset.mem_biUnion.2 ⟨l, Finset.mem_Icc.2 ⟨by omega, hl3.2⟩, he⟩)
    · exact Finset.disjoint_left.1 (hlent_disj l l' hll) he he'
  -- `B ∪ CD`
  set EBall := (Finset.Icc 1 R).biUnion EB with hEBall
  set ECDall := (Finset.Icc 3 R).biUnion ECD with hECDall
  have hEBall : EBall ⊆ Light.Kstd G run ∧ Disjoint EBall LentAll := by
    constructor
    · intro e he
      obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.1 he
      have hl1 := Finset.mem_Icc.1 hl
      rw [hKstd]
      exact Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_biUnion.2 ⟨a, ha,
        (hEV l hl1.1 hl1.2 a ha).1 he⟩⟩
    · rw [Finset.disjoint_left]
      intro e he
      obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.1 he
      have hl1 := Finset.mem_Icc.1 hl
      exact Finset.disjoint_left.1 (hEV l hl1.1 hl1.2 a ha).2 he
  have hBCD : Disjoint EBall ECDall := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨l', hl', he'⟩ := Finset.mem_biUnion.1 he'
    have hl3' := Finset.mem_Icc.1 hl'
    rcases Finset.mem_union.1 he' with he' | he'
    · obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨a, ha, he⟩ := Finset.mem_biUnion.1 he
      obtain ⟨a', ha', he'⟩ := Finset.mem_biUnion.1 he'
      have hl1 := Finset.mem_Icc.1 hl
      by_cases hsame : (l, a) = (l', a')
      · simp only [Prod.mk.injEq] at hsame
        obtain ⟨rfl, rfl⟩ := hsame
        exact Finset.disjoint_left.1 ((hspec l hl1.1 hl1.2).1 a ha).1 he he'
      · exact Finset.disjoint_left.1 (disjoint_E_std hHY hv ha ha' hsame)
          ((hEV l hl1.1 hl1.2 a ha).1 he) ((hEQ l' (by omega) hl3'.2 a' ha').1 he')
    · exact Finset.disjoint_left.1 hEBall.2 he
        (Finset.mem_biUnion.2 ⟨l', Finset.mem_Icc.2 ⟨by omega, hl3'.2⟩, he'⟩)
  have hECDall : ECDall ⊆ Light.Kstd G run ∪ LentAll := by
    intro e he
    obtain ⟨l, hl, he⟩ := Finset.mem_biUnion.1 he
    have hl3 := Finset.mem_Icc.1 hl
    rcases Finset.mem_union.1 he with he | he
    · exact Finset.mem_union_left _ ((hEQL l (by omega) hl3.2).1 he)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_Icc.2 ⟨by omega, hl3.2⟩, he⟩)
  have hAdisj : Disjoint EA (EBall ∪ ECDall) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨he1, heL⟩ := Finset.mem_sdiff.1 he
    obtain ⟨-, heK⟩ := Finset.mem_sdiff.1 he1
    rcases Finset.mem_union.1 he' with he' | he'
    · exact heK (hEBall.1 he')
    · rcases Finset.mem_union.1 (hECDall he') with h | h
      · exact heK h
      · exact heL (hLentKstd e h heK)
  have hDdec : IsDecomp ((EA ∪ (EBall ∪ ECDall) : Finset (Sym2 V)) : Set (Sym2 V))
      (DA ++ (DB ++ DCD)) :=
    isDecomp_union_finset hDA (isDecomp_union_finset hDBdec hDCDdec hBCD) hAdisj
  -- coverage: `EA ∪ EBall ∪ ECDall = E(G)`
  have hKstd_edges : Light.Kstd G run ⊆ G.edges := by
    intro e he
    rw [hKstd] at he
    obtain ⟨l, -, he⟩ := Finset.mem_biUnion.1 he
    obtain ⟨a, -, he⟩ := Finset.mem_biUnion.1 he
    exact E_subset_edges run G l a he
  have hcover : EA ∪ (EBall ∪ ECDall) = G.edges := by
    apply Finset.Subset.antisymm
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 he).1).1
      · rcases Finset.mem_union.1 he with he | he
        · exact hKstd_edges (hEBall.1 he)
        · rcases Finset.mem_union.1 (hECDall he) with h | h
          · exact hKstd_edges h
          · exact hLentAll_edges h
    · intro e heG
      -- lent edges are in `ECDall`
      have hlentCase : e ∈ LentAll → e ∈ EA ∪ (EBall ∪ ECDall) := by
        intro heL
        obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.1 heL
        by_cases hl3 : 3 ≤ l ∧ l ≤ R
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_biUnion.2 ⟨l, Finset.mem_Icc.2 hl3, Finset.mem_union_right _ hel⟩))
        · rw [hlent_empty l hl3] at hel
          exact absurd hel (Finset.notMem_empty e)
      by_cases heK : e ∈ Light.Kstd G run
      · by_cases heL : e ∈ LentAll
        · exact hlentCase heL
        · rw [hKstd] at heK
          obtain ⟨l, hl, heK⟩ := Finset.mem_biUnion.1 heK
          obtain ⟨a, ha, heK⟩ := Finset.mem_biUnion.1 heK
          have hl1 := Finset.mem_Icc.1 hl
          have hsplit := ((hspec l hl1.1 hl1.2).1 a ha).2.1
          rw [hEfut l hl1.1 hl1.2 a ha] at hsplit
          have : e ∈ (outs l).EV a ∪ (outs l).EQ a := by
            rw [hsplit]; exact Finset.mem_sdiff.2 ⟨heK, heL⟩
          rcases Finset.mem_union.1 this with h | h
          · exact Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_biUnion.2 ⟨a, ha, h⟩⟩))
          · by_cases hl3 : 3 ≤ l
            · exact Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_biUnion.2 ⟨l, Finset.mem_Icc.2 ⟨hl3, hl1.2⟩,
                  Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨a, ha, h⟩)⟩))
            · rw [hEQ_empty l (by omega) hl1.1 a ha] at h
              exact absurd h (Finset.notMem_empty e)
      · by_cases hext : e ∈ (run.lightParts G).biUnion Lext
        · obtain ⟨Y, -, he⟩ := Finset.mem_biUnion.1 hext
          exact hlentCase (Finset.mem_inter.1 he).1
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨heG, heK⟩, hext⟩)
  refine ⟨fun l => (outs l).J, fun l hl => ?_, DA ++ (DB ++ DCD), ?_, ?_⟩
  · have hl3 := Finset.mem_Icc.1 hl
    exact ((hspec l (by omega) hl3.2).2 hl3.1 hl3.2).2.2.2.2
  · rw [← hcover]; exact hDdec
  -- cost
  · have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
    have hD0 : 0 < Dstar := lt_trans (by norm_num) hD.two_lt
    -- K-RED
    -- TPV
    have hDBnat : DB.length ≤ 169 * (∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l,
        (run.hubs G l a).card + ∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l, (run.fresh G l a).card +
        ∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l, (lost run G δ (stageOf ω) l a).card) := by
      rw [hDB, length_flatMap_toList]
      simp only [length_flatMap_toList]
      calc ∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l, ((outs l).DV a).length
          ≤ ∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l, 169 * ((run.hubs G l a).card +
              (run.fresh G l a).card + (lost run G δ (stageOf ω) l a).card) := by
            refine Finset.sum_le_sum (fun l hl => Finset.sum_le_sum (fun a ha => ?_))
            have hl1 := Finset.mem_Icc.1 hl
            have h1 := ((hspec l hl1.1 hl1.2).1 a ha).2.2.2.1
            have h2 : (ret run G δ (stageOf ω) l a).card ≤ (run.hubs G l a).card +
                (run.fresh G l a).card + (lost run G δ (stageOf ω) l a).card := by
              unfold ret
              exact (Finset.card_union_le _ _).trans
                (Nat.add_le_add_right (Finset.card_union_le _ _) _)
            omega
        _ = _ := by
            simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    have hE := (hTowerE V G Dstar run hD hv hd1).2.2
    have hF : ∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card ≤ 2 * G.card :=
      (hFresh V G Dstar run hv).2.2.2.2
    have hLost : ∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l, (lost run G δ (stageOf ω) l a).card =
        ∑ l ∈ Finset.Icc 1 R, (lostRound run G δ (stageOf ω) l).card :=
      Finset.sum_congr rfl (fun l _ => (card_lostRound run G δ (stageOf ω) l).symm)
    have hDBle : (DB.length : ℝ) ≤ 169 * (HB.epsA Dstar * (G.card : ℝ) + 2 * (G.card : ℝ) +
        ∑ l ∈ Finset.Icc 1 R, ((lostRound run G δ (stageOf ω) l).card : ℝ)) := by
      have h1 : (DB.length : ℝ) ≤ 169 * (((∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l,
          (run.hubs G l a).card : ℕ) : ℝ) + ((∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l,
          (run.fresh G l a).card : ℕ) : ℝ) + ((∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l,
          (lost run G δ (stageOf ω) l a).card : ℕ) : ℝ)) := by
        exact_mod_cast hDBnat
      have h2 : ((∑ l ∈ Finset.Icc 1 R, ∑ a ∈ run.Std G l, (run.fresh G l a).card : ℕ) : ℝ) ≤
          2 * (G.card : ℝ) := by exact_mod_cast hF
      rw [hLost] at h1
      push_cast at h1
      push_cast at h2 hE
      linarith
    -- JS-LC and consumer
    have hDCDlen : (DCD.length : ℝ) = ∑ l ∈ Finset.Icc 3 R,
        (((outs l).DC.length : ℝ) + ((C.out l (outs l).J).1.length : ℝ)) := by
      rw [hDCD, List.length_flatMap, Finset.sum_map_toList]
      push_cast
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [List.length_append]; push_cast; ring
    have hmY : ∀ l, (0 : ℝ) ≤ ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) :=
      fun l => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hDCle : ∀ l ∈ Finset.Icc 3 R, ((outs l).DC.length : ℝ) + ((C.out l (outs l).J).1.length : ℝ)
        ≤ 126 * (G.card : ℝ) * (1 / (run.M G l : ℝ)) +
          1.5 * ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) + b l (outs l).J := by
      intro l hl
      have hl3 := Finset.mem_Icc.1 hl
      obtain ⟨-, -, -, hlen, hJP⟩ := (hspec l (by omega) hl3.2).2 hl3.1 hl3.2
      have hgiant : ∑ Y ∈ (run.ancestors G).filter (fun Y => IsGiant run G δ Y l),
          (mY run G δ Y l : ℝ) ≤ ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
      have hbl := hb l (outs l).J hl3.1 hl3.2 hJP
      have : 126 * (G.card : ℝ) / (run.M G l : ℝ) = 126 * (G.card : ℝ) * (1 / (run.M G l : ℝ)) := by
        ring
      linarith
    have hsub : Finset.Icc 3 R ⊆ Finset.Icc 1 R := Finset.Icc_subset_Icc (by norm_num) le_rfl
    have hM : ∑ l ∈ Finset.Icc 3 R, 126 * (G.card : ℝ) * (1 / (run.M G l : ℝ)) ≤
        126 * (G.card : ℝ) * (2 / Dstar) := by
      rw [← Finset.mul_sum]
      have h1 := (hTowerBM V G Dstar run hD hv hd1).2
      have h2 : ∑ l ∈ Finset.Icc 3 R, (1 : ℝ) / (run.M G l : ℝ) ≤
          ∑ l ∈ Finset.Icc 1 R, (1 : ℝ) / (run.M G l : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have h3 : (0 : ℝ) ≤ 126 * (G.card : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left (h2.trans h1) h3
    have hmsum : ∑ l ∈ Finset.Icc 3 R, 1.5 * ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) ≤
        1.5 * ∑ l ∈ Finset.Icc 1 R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) := by
      rw [← Finset.mul_sum]
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hmY l)
      linarith
    have hDCDle : (DCD.length : ℝ) ≤ 126 * (G.card : ℝ) * (2 / Dstar) +
        1.5 * ∑ l ∈ Finset.Icc 1 R, ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) +
        ∑ l ∈ Finset.Icc 3 R, b l (outs l).J := by
      rw [hDCDlen]
      calc _ ≤ ∑ l ∈ Finset.Icc 3 R, (126 * (G.card : ℝ) * (1 / (run.M G l : ℝ)) +
            1.5 * ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) + b l (outs l).J) :=
            Finset.sum_le_sum hDCle
        _ = ∑ l ∈ Finset.Icc 3 R, 126 * (G.card : ℝ) * (1 / (run.M G l : ℝ)) +
            ∑ l ∈ Finset.Icc 3 R, 1.5 * ∑ Y ∈ run.ancestors G, (mY run G δ Y l : ℝ) +
            ∑ l ∈ Finset.Icc 3 R, b l (outs l).J := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ _ := by linarith
    have hlen : ((DA ++ (DB ++ DCD)).length : ℝ) =
        (DA.length : ℝ) + (DB.length : ℝ) + (DCD.length : ℝ) := by
      simp only [List.length_append]; push_cast; ring
    have heps : epsM Dstar * (G.card : ℝ) = epsK Dstar * (G.card : ℝ) +
        169 * (HB.epsA Dstar * (G.card : ℝ)) + 126 * (G.card : ℝ) * (2 / Dstar) := by
      unfold epsM; field_simp; ring
    rw [hlen]
    linarith

end EG.Chain.MixCA
