module

public import EG.Proof.Chain.JSLCSystems
public import EG.Lib.Found.Fnum

/-!
# JS-LC, Step 7: the union of all systems (manuscript s6:lemJSLC, proof, Step 7)

Probe unit P2J (probe P-2, part 2), proof round 1. "Now consider all systems of all `(Y,l)`
together. Their bead sets are pairwise disjoint (part (b) of the joint-routing claim, and each edge
of `⋃_Z B_Z \ J_l` lies in exactly one `R_Y`). Their path edges are pairwise disjoint: within one
`(Y,l)` and one `j`, by the joint routing, part (d) of the claim; for different `j`, because
different classes are used; for different `Y ≠ Y'`, because `E(H_Y) ∩ E(H_{Y'}) = ∅` … Path edges
are disjoint from beads, as shown above. By Lemma s6:lemHCCglob, the union decomposes into at most
`∑_𝒮 Φ(𝒮)` cycles. Put `LentJS_l := ⋃_𝒮 ⋃_j F_j(𝒮) ⊆ ⋃_{Y,j} LJS_{Y,l,j}`. Since
`⋃_Z B_Z = J_l ⊔ ⨆_Y R_Y` and `⨆_Y R_Y` is the set of all beads of all systems,
`⋃_Z B_Z ∪ LentJS_l` is partitioned into the single edges of `J_l` and these cycles. Each cycle
lies inside one system, so it uses beads and lent edges of one ancestor `Y` only."

The systems are indexed by `idx`: the pairs `(Y, i)` of a class `Y` of round `l` and a colour `i`
in use (the group `i` of the cherries of `R_Y`). Each costs at most one cycle
(`exists_sys_decomp`), so the number of cycles is at most `∑_Y |used Y|`.
-/

public section

namespace EG.Chain.JSLC

open EG.HB EG.Chain EG.Chain.Cherry

variable {V : Type*} [DecidableEq V] {run : Run V} {G : FGraph V} {δ : Designation V}
  {S : StageData V} {l : ℕ} {B : Addr → Finset (Sym2 V)} {J : Finset (Sym2 V)}
  {R : PartId → Finset (Sym2 V)} {m : PartId → ℕ} {col : PartId → V × V × V → ℕ}
  {rt : ∀ Y j, usedJ run G R col Y j → List V}

/-- The systems of round `l`: pairs `(Y, i)`, `Y` a class and `i` a colour in use for `Y`. -/
@[expose] noncomputable def idx (run : Run V) (G : FGraph V) (δ : Designation V) (S : StageData V)
    (l : ℕ) (R : PartId → Finset (Sym2 V)) (col : PartId → V × V × V → ℕ) :
    Finset (Σ _ : PartId, ℕ) :=
  (Step2.classes run G δ S l).sigma (fun Y => used run G R col Y)

theorem mem_idx {p : Σ _ : PartId, ℕ} :
    p ∈ idx run G δ S l R col ↔ p.1 ∈ Step2.classes run G δ S l ∧ p.2 ∈ used run G R col p.1 :=
  Finset.mem_sigma

/-- The beads of the group `i` of `Y` lie in `R_Y`. -/
theorem grp_beads_subset (C : JslcCtx run G δ S l B J R) (Y : PartId) (i : ℕ) :
    (grp run G R col Y i).biUnion cEdges ⊆ R Y := by
  intro e he
  obtain ⟨c, hc, he⟩ := Finset.mem_biUnion.1 he
  exact cEdges_subset (C.cherryHyp Y) (Finset.mem_filter.1 hc).1 he

/-- One system: its lent edges `Fs ⊆ ⋃_j E(𝒫_j)` and one cycle (HCC-P, all loads `1`). -/
theorem exists_sys_out (C : JslcCtx run G δ S l B J R) (hg : GroupSpec run G l R δ m col)
    (hr : RouteSpec run G δ S l R col rt) {Y : PartId} (hY : Y ∈ Step2.classes run G δ S l)
    {i : ℕ} (hi : i ∈ used run G R col Y) :
    ∃ (Fs : Finset (Sym2 V)) (D : List (Obj V)),
      (∀ e ∈ Fs, ∃ j, j < Stage1.KJS G run l ∧ j < (lst run G R col Y i).length ∧
        e ∈ walkEdges (Qs run G R col rt Y i j) ∧ e ∈ S.ljs Y l j) ∧
      IsDecomp (((grp run G R col Y i).biUnion cEdges ∪ Fs : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      D.length ≤ 1 ∧ ∀ o ∈ D, ∃ c : List V, o = Obj.cycle c := by
  classical
  obtain ⟨F, D, hF, hD, hDl, hDc⟩ := exists_sys_decomp C hg hr hY hi
  refine ⟨Finset.univ.biUnion F, D, ?_, ?_, hDl, hDc⟩
  · intro e he
    obtain ⟨j, -, hej⟩ := Finset.mem_biUnion.1 he
    have h1 := hF j hej
    obtain ⟨h2, hjK⟩ := sys_pathEdges_subset hg hr hY hi j
    rw [sys_pathEdges] at h1
    exact ⟨j.val, hjK, j.2, List.mem_toFinset.1 h1, h2 (by rw [sys_pathEdges]; exact h1)⟩
  · rw [← sys_beads (rt := rt) C]; exact hD

/-- [s6:lemJSLC] (proof, Step 7) the union of all systems: a set `LentJS_l` in the classes
`LJS_{Y,l,j}` (`Y` a class of round `l`, `j < K^JS_l`) and cycles decomposing
`(⋃_Z B_Z ∪ LentJS_l) \ J_l`, at most `∑_Y |used Y|` of them, each using beads and lent edges of
one ancestor only. -/
theorem exists_union (C : JslcCtx run G δ S l B J R) (hg : GroupSpec run G l R δ m col)
    (hr : RouteSpec run G δ S l R col rt) :
    ∃ (LentJS : Finset (Sym2 V)) (D : List (Obj V)),
      (∀ e ∈ LentJS, ∃ Y ∈ Step2.classes run G δ S l, ∃ j < Stage1.KJS G run l,
        e ∈ S.ljs Y l j) ∧
      IsDecomp ((((run.Std G l).biUnion B ∪ LentJS) \ J : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      (∀ o ∈ D, ∃ c : List V, o = Obj.cycle c) ∧
      D.length ≤ ∑ Y ∈ Step2.classes run G δ S l, (used run G R col Y).card ∧
      (∀ o ∈ D, ∃ Y ∈ Step2.classes run G δ S l, ∀ e ∈ o.edges,
        e ∈ (run.Std G l).biUnion B ∨ ∃ j < Stage1.KJS G run l, e ∈ S.ljs Y l j) := by
  classical
  set I := idx run G δ S l R col with hI
  have hsys : ∀ p : Σ _ : PartId, ℕ, ∃ (Fs : Finset (Sym2 V)) (Dp : List (Obj V)), p ∈ I →
      (∀ e ∈ Fs, ∃ j, j < Stage1.KJS G run l ∧ j < (lst run G R col p.1 p.2).length ∧
        e ∈ walkEdges (Qs run G R col rt p.1 p.2 j) ∧ e ∈ S.ljs p.1 l j) ∧
      IsDecomp (((grp run G R col p.1 p.2).biUnion cEdges ∪ Fs : Finset (Sym2 V)) :
        Set (Sym2 V)) Dp ∧
      Dp.length ≤ 1 ∧ ∀ o ∈ Dp, ∃ c : List V, o = Obj.cycle c := by
    intro p
    by_cases hp : p ∈ I
    · obtain ⟨hY, hi⟩ := mem_idx.1 hp
      obtain ⟨Fs, Dp, h⟩ := exists_sys_out C hg hr hY hi
      exact ⟨Fs, Dp, fun _ => h⟩
    · exact ⟨∅, [], fun h => absurd h hp⟩
  choose Fs Dp hFD using hsys
  set Es : (Σ _ : PartId, ℕ) → Finset (Sym2 V) :=
    fun p => (grp run G R col p.1 p.2).biUnion cEdges ∪ Fs p with hEs
  -- membership in the lent part
  have hFs : ∀ p ∈ I, ∀ e ∈ Fs p, ∃ j, j < Stage1.KJS G run l ∧
      j < (lst run G R col p.1 p.2).length ∧
      e ∈ walkEdges (Qs run G R col rt p.1 p.2 j) ∧ e ∈ S.ljs p.1 l j :=
    fun p hp => (hFD p hp).1
  have hYa : ∀ p ∈ I, p.1 ∈ run.ancestors G := fun p hp => C.Ycl_ancestors (mem_idx.1 hp).1
  -- pairwise disjointness
  have hdisj : (I : Set (Σ _ : PartId, ℕ)).PairwiseDisjoint Es := by
    rintro ⟨Y, i⟩ hp ⟨Y', i'⟩ hq hpq
    have hp' : (⟨Y, i⟩ : Σ _ : PartId, ℕ) ∈ I := hp
    have hq' : (⟨Y', i'⟩ : Σ _ : PartId, ℕ) ∈ I := hq
    have hYa1 := hYa _ hp'
    have hYa2 := hYa _ hq'
    show Disjoint (Es ⟨Y, i⟩) (Es ⟨Y', i'⟩)
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [hEs, Finset.mem_union] at he he'
    by_cases hYY : Y = Y'
    · subst hYY
      have hii : i ≠ i' := fun h => hpq (by rw [h])
      rcases he with he | he <;> rcases he' with he' | he'
      · obtain ⟨c, hc, hec⟩ := Finset.mem_biUnion.1 he
        obtain ⟨c', hc', hec'⟩ := Finset.mem_biUnion.1 he'
        have hcc : c ≠ c' := by
          intro h; subst h
          exact hii ((Finset.mem_filter.1 hc).2.symm.trans (Finset.mem_filter.1 hc').2)
        exact Finset.disjoint_left.1 (disjoint_cEdges (C.cherryHyp Y) (Finset.mem_filter.1 hc).1
          (Finset.mem_filter.1 hc').1 hcc) hec hec'
      · obtain ⟨j, -, -, -, hj⟩ := hFs _ hq' e he'
        exact Finset.disjoint_left.1 (C.disjoint_ljs_R hYa1 j Y) hj
          (grp_beads_subset C Y i he)
      · obtain ⟨j, -, -, -, hj⟩ := hFs _ hp' e he
        exact Finset.disjoint_left.1 (C.disjoint_ljs_R hYa1 j Y) hj
          (grp_beads_subset C Y i' he')
      · obtain ⟨j, hjK, hj1, hw, hj⟩ := hFs _ hp' e he
        obtain ⟨j', hjK', hj1', hw', hj'⟩ := hFs _ hq' e he'
        by_cases hjj : j = j'
        · subst hjj
          have hi1 := mem_usedJ (mem_idx.1 hp').2 hj1
          have hi2 := mem_usedJ (mem_idx.1 hq').2 hj1'
          rw [Qs_eq hi1] at hw
          rw [Qs_eq hi2] at hw'
          have hne : (⟨i, hi1⟩ : usedJ run G R col Y j) ≠ ⟨i', hi2⟩ :=
            fun h => hii (congrArg Subtype.val h)
          exact (hr Y j (mem_idx.1 hp').1 hjK).2 _ _ hne hw hw'
        · exact Finset.disjoint_left.1
            (C.hS.ljs_disj Y l j l j' (by simpa using hjj)) hj hj'
    · rcases he with he | he <;> rcases he' with he' | he'
      · exact Finset.disjoint_left.1 (C.disjRR Y Y' hYY) (grp_beads_subset C Y i he)
          (grp_beads_subset C Y' i' he')
      · obtain ⟨j, -, -, -, hj⟩ := hFs _ hq' e he'
        exact Finset.disjoint_left.1 (C.disjoint_ljs_R hYa2 j Y) hj
          (grp_beads_subset C Y i he)
      · obtain ⟨j, -, -, -, hj⟩ := hFs _ hp' e he
        exact Finset.disjoint_left.1 (C.disjoint_ljs_R hYa1 j Y') hj
          (grp_beads_subset C Y' i' he')
      · obtain ⟨j, -, -, -, hj⟩ := hFs _ hp' e he
        obtain ⟨j', -, -, -, hj'⟩ := hFs _ hq' e he'
        exact Finset.disjoint_left.1 (C.s7Y Y hYa1 Y' hYa2 hYY j j') hj hj'
  have hdec := isDecomp_finset_biUnion I hdisj (fun p hp => (hFD p hp).2.1)
  set LentJS := I.biUnion Fs with hL
  -- the partition
  have hset : ((run.Std G l).biUnion B ∪ LentJS) \ J = I.biUnion Es := by
    ext e
    rw [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨he | he, heJ⟩
      · rcases C.cover e he with h | ⟨Y, hY⟩
        · exact absurd h heJ
        · obtain ⟨c, hc, hec⟩ := exists_cherry (C.cherryHyp Y) hY
          refine Finset.mem_biUnion.2
            ⟨⟨Y, col Y c⟩, mem_idx.2 ⟨C.mem_Ycl_of_mem hY, mem_used.2 ⟨c, hc, rfl⟩⟩, ?_⟩
          show e ∈ (grp run G R col Y (col Y c)).biUnion cEdges ∪ Fs ⟨Y, col Y c⟩
          exact Finset.mem_union_left _
            (Finset.mem_biUnion.2 ⟨c, Finset.mem_filter.2 ⟨hc, rfl⟩, hec⟩)
      · obtain ⟨p, hp, he⟩ := Finset.mem_biUnion.1 he
        exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_union_right _ he⟩
    · intro he
      obtain ⟨p, hp, he⟩ := Finset.mem_biUnion.1 he
      rcases Finset.mem_union.1 he with he | he
      · have heR := grp_beads_subset C p.1 p.2 he
        exact ⟨Or.inl (C.R_sub p.1 heR), fun hJ =>
          Finset.disjoint_left.1 (C.disjJR p.1) hJ heR⟩
      · refine ⟨Or.inr (Finset.mem_biUnion.2 ⟨p, hp, he⟩), fun hJ => ?_⟩
        obtain ⟨j, -, -, -, hj⟩ := hFs p hp e he
        exact Finset.disjoint_left.1 (C.disjoint_ljs_Bu (hYa p hp) j) hj (C.J_sub hJ)
  refine ⟨LentJS, I.toList.flatMap Dp, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, he⟩ := Finset.mem_biUnion.1 he
    obtain ⟨j, hjK, -, -, hj⟩ := hFs p hp e he
    exact ⟨p.1, (mem_idx.1 hp).1, j, hjK, hj⟩
  · rw [hset]; exact hdec
  · intro o ho
    obtain ⟨p, hp, ho⟩ := List.mem_flatMap.1 ho
    exact (hFD p (Finset.mem_toList.1 hp)).2.2.2 o ho
  · rw [length_flatMap_toList]
    calc ∑ p ∈ I, (Dp p).length ≤ ∑ p ∈ I, 1 :=
          Finset.sum_le_sum fun p hp => (hFD p hp).2.2.1
      _ = I.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ Y ∈ Step2.classes run G δ S l, (used run G R col Y).card := by
          rw [hI, idx, Finset.card_sigma]
  · intro o ho
    obtain ⟨p, hp, ho⟩ := List.mem_flatMap.1 ho
    have hp' := Finset.mem_toList.1 hp
    refine ⟨p.1, (mem_idx.1 hp').1, fun e he => ?_⟩
    have heE : e ∈ Es p := by
      have := (hFD p hp').2.1.mem_of_mem_edges ho he
      exact Finset.mem_coe.1 this
    rcases Finset.mem_union.1 heE with he | he
    · exact Or.inl (C.R_sub p.1 (grp_beads_subset C p.1 p.2 he))
    · obtain ⟨j, hjK, -, -, hj⟩ := hFs p hp' e he
      exact Or.inr ⟨j, hjK, hj⟩

end EG.Chain.JSLC
