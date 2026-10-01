module

public import EG.Lib.Vortex.TPVStep

/-!
# One step of the TPV run: the assembly (manuscript s4:lemTPV, proof, "Step `j`" (i)–(vi), "The
invariants persist", "Cost of step `j`")

Unit P3-s4. `EG.TPVRun.step`: for labels in the good event and a set `S` of used edges satisfying
(Inv1)–(Inv3) before step `j < J`, step `j` uses a set `T` of edges disjoint from `S` (all of
`F_j`, the reserved edges and the connectors), decomposes it into at most `12|P ∩ U_j|` objects,
and (Inv1)–(Inv3) hold before step `j + 1` for `S ∪ T`.

Cost: each of the three classes gives at most `3|𝒫_{j,c}| + |W_j| ≤ 4|P ∩ U_j|` objects
(`EG.PVStep.Hyp.cost_paths` and (E)); the manuscript's (s4:eqTPVstep) is
`12|W_j| + 9|P ∩ U_j|`, and both are at most `12 · (the manuscript's per-step budget)`
in the sense that `3·(3|P ∩ U_j| + |W_j|) ≤ 12|P ∩ U_j|`.
-/

public section

namespace EG

namespace TPVRun

open List

variable {V : Type*} [DecidableEq V]

variable {Z P : Finset V} {lev : V → ℕ} {kap : V → Fin 4}

set_option maxHeartbeats 1000000 in
-- the proof assembles the three classes of a step; it is long but elementary
/-- [s4:lemTPV] proof, "Step `j`" (i)–(vi), "The invariants persist" and "Cost of step `j`". -/
theorem step {O : FGraph V} {J : ℕ} {R : ℕ → Fin 3 → Finset (Sym2 V)} {M : Finset (Sym2 V)}
    {A : V → Finset V} {ℓ t : ℝ} (hg : Good Z P O J R M lev kap A ℓ t)
    {E : Finset (Sym2 V)} (hE : Vortex.TPVAdm Z O E) {j : ℕ} (hj : j < J)
    {S : Finset (Sym2 V)} (hinv : Inv Z P J R M lev E j S) :
    ∃ (T : Finset (Sym2 V)) (D : List (Obj V)),
      Disjoint T S ∧ T ⊆ E ∧
      (∀ e ∈ H0 P E, e ∉ S → (∃ w ∈ Wt P lev j, w ∈ e) → e ∈ T) ∧
      (∀ e ∈ T, e ∈ H0 P E ∨ e ∈ O.edges) ∧
      IsDecomp (T : Set (Sym2 V)) D ∧
      D.length ≤ 12 * (P.filter fun v => j ≤ lev v).card ∧
      Inv Z P J R M lev E (j + 1) (S ∪ T) := by
  classical
  obtain ⟨hPZ, hOZ, hMO, hRd, hRM, hG2, hG4, hmult⟩ := hg
  obtain ⟨hEl, hEZ, hOE⟩ := hE
  obtain ⟨hI1, hI2, hI3⟩ := hinv
  -- notation
  set W := Wt P lev j with hWdef
  set Up := U Z P lev (j + 1) with hUpdef
  set Pj := P.filter fun v => j ≤ lev v with hPjdef
  have hWP : W ⊆ Pj := by
    intro w hw
    rw [mem_Wt] at hw
    exact Finset.mem_filter.2 ⟨hw.1, hw.2.ge⟩
  have hWUp : ∀ x ∈ Up, x ∉ W := fun x hx => notWt_of_U hx
  -- (i) Reserve: far ends
  let Cw : V → Finset V := fun w => (A w).filter fun u => s(w, u) ∈ M ∧ u ∈ Zr Z P lev kap j
  have hsel : ∀ w, ∃ f : Fin 3 → Fin 2 → V, w ∈ W → (∀ c i, f c i ∈ Cw w) ∧
      ∀ c i c' i', f c i = f c' i' → c = c' ∧ i = i' := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨f, h1, h2⟩ := exists_six (hG4 j hj w (mem_Wt.1 hw).1)
      exact ⟨f, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => w, fun h => absurd h hw⟩
  choose fe hfe using hsel
  have hfC : ∀ w ∈ W, ∀ c i, s(w, fe w c i) ∈ M ∧ fe w c i ∈ A w ∧ fe w c i ∈ Up ∧
      kap (fe w c i) = 0 := by
    intro w hw c i
    have h := ((hfe w hw).1 c i)
    simp only [Cw, Finset.mem_filter, Zr] at h
    exact ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩
  have hfinj : ∀ w ∈ W, ∀ c i c' i', fe w c i = fe w c' i' → c = c' ∧ i = i' :=
    fun w hw => (hfe w hw).2
  have hfW : ∀ w ∈ W, ∀ c i, fe w c i ∉ W := fun w hw c i => hWUp _ (hfC w hw c i).2.2.1
  have hfne : ∀ w ∈ W, ∀ c, fe w c 0 ≠ fe w c 1 := by
    intro w hw c h
    have := (hfinj w hw c 0 c 1 h).2
    exact absurd this (by decide)
  -- reserved edges
  let Res : Fin 3 → Finset (Sym2 V) := fun c =>
    W.biUnion fun w => {s(w, fe w c 0), s(w, fe w c 1)}
  have hmemRes : ∀ c e, e ∈ Res c ↔ ∃ w ∈ W, e = s(w, fe w c 0) ∨ e = s(w, fe w c 1) := by
    intro c e
    simp [Res]
  let ResAll : Finset (Sym2 V) := Finset.univ.biUnion Res
  have hmemResAll : ∀ e, e ∈ ResAll ↔ ∃ c, e ∈ Res c := by intro e; simp [ResAll]
  -- an edge `s(w, x)` with `w ∈ W`, `x ∉ W` determines `w` and `x`
  have hsym : ∀ {w w' x x' : V}, w ∈ W → x ∉ W → x' ∉ W → s(w, x) = s(w', x') → w = w' ∧ x = x' := by
    intro w w' x x' hw hx hx' h
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · subst h1; exact absurd hw hx'
  have hResM : ∀ c, ∀ e ∈ Res c, e ∈ M := by
    intro c e he
    obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he
    · exact (hfC w hw c 0).1
    · exact (hfC w hw c 1).1
  have hResW : ∀ c, ∀ e ∈ Res c, ∃ w ∈ W, w ∈ e := by
    intro c e he
    obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he <;> exact ⟨w, hw, Sym2.mem_mk_left _ _⟩
  -- (ii) Classes
  have hcls : ∀ e : Sym2 V, ∃ c : Fin 3, (∃ w ∈ W, w ∈ e) → ∀ x ∈ e, x ∉ W → kap x ≠ c.succ := by
    intro e
    by_cases he : ∃ w ∈ W, w ∈ e
    · obtain ⟨c, hc⟩ := exists_class W kap he
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose cls hclsP using hcls
  let F : Finset (Sym2 V) := ((H0 P E).filter fun e => e ∉ S).filter fun e => ∃ w ∈ W, w ∈ e
  have hmemF : ∀ e, e ∈ F ↔ e ∈ H0 P E ∧ e ∉ S ∧ ∃ w ∈ W, w ∈ e := by
    intro e; simp [F, and_assoc]
  let Fc : Fin 3 → Finset (Sym2 V) := fun c => (F.filter fun e => e ∉ ResAll).filter
    fun e => cls e = c
  have hmemFc : ∀ c e, e ∈ Fc c ↔ e ∈ F ∧ e ∉ ResAll ∧ cls e = c := by
    intro c e; simp [Fc, and_assoc]
  have hFcE : ∀ c, ∀ e ∈ Fc c, e ∈ E := fun c e he =>
    (mem_H0.1 ((hmemF e).1 ((hmemFc c e).1 he).1).1).1
  have hFcW : ∀ c, ∀ e ∈ Fc c, ∃ w ∈ W, w ∈ e := fun c e he =>
    ((hmemF e).1 ((hmemFc c e).1 he).1).2.2
  have hFcPj : ∀ c, ∀ e ∈ Fc c, ∀ v ∈ e, v ∈ Pj := by
    intro c e he v hv
    have hF := (hmemF e).1 ((hmemFc c e).1 he).1
    exact Finset.mem_filter.2 ⟨(mem_H0.1 hF.1).2 v hv, hI1 e hF.1 hF.2.1 v hv⟩
  have hFcends : ∀ c, ∀ e ∈ Fc c, ∀ v ∈ e, v ∈ W ∨ v ∈ Up := by
    intro c e he v hv
    have hvP := hFcPj c e he v hv
    rw [Finset.mem_filter] at hvP
    rcases Nat.lt_or_ge j (lev v) with h | h
    · right
      exact mem_U.2 ⟨hPZ hvP.1, Or.inr h⟩
    · left
      exact mem_Wt.2 ⟨hvP.1, le_antisymm h hvP.2⟩
  have hFckap : ∀ c, ∀ e ∈ Fc c, ∀ x ∈ e, x ∉ W → kap x ≠ c.succ := by
    intro c e he x hx hxW
    have h := (hmemFc c e).1 he
    rw [← h.2.2]
    exact hclsP e (hFcW c e he) x hx hxW
  -- (iii) Paths: Corollary-22 decompositions
  have hcor : ∀ c, ∃ Pc : List (List V), IsPathDecomp ((Fc c : Finset (Sym2 V)) : Set (Sym2 V)) Pc ∧
      ∀ v, pathEndCount Pc v ≤ 2 := fun c =>
    EG.cor22 V (Fc c) fun e he => hEl e (hFcE c e he)
  choose Pc hPc using hcor
  -- the engine hypotheses
  have hHyp : ∀ c, PVStep.Hyp ∅ W Up (Fc c) (Pc c) (fun w => fe w c 0) (fun w => fe w c 1) := by
    intro c
    refine ⟨Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, ?_, fun e he =>
      hEl e (hFcE c e he), ?_, hFcW c, (hPc c).1, (hPc c).2, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hxW hxU
      exact hWUp x hxU hxW
    · intro e he v hv
      rcases hFcends c e he v hv with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h
    · intro w hw
      refine ⟨hfne w hw c, Finset.mem_union_right _ (hfC w hw c 0).2.2.1,
        Finset.mem_union_right _ (hfC w hw c 1).2.2.1, ?_, ?_⟩
      · intro hf
        refine ((hmemFc c _).1 hf).2.1 ((hmemResAll _).2 ⟨c, (hmemRes c _).2 ⟨w, hw, Or.inl rfl⟩⟩)
      · intro hf
        refine ((hmemFc c _).1 hf).2.1 ((hmemResAll _).2 ⟨c, (hmemRes c _).2 ⟨w, hw, Or.inr rfl⟩⟩)
  -- (iv), (v): the output of each class
  have hph := fun c => (hHyp c).exists_output_noRoot
  choose Dp Qp hDp using hph
  -- (vi): closing
  have hcl : ∀ c, ∃ (Conn : Finset (Sym2 V)) (Dc : List (Obj V)),
      IsDecomp ((Fc c ∪ Res c ∪ Conn : Finset (Sym2 V)) : Set (Sym2 V)) Dc ∧
      Disjoint (Fc c ∪ Res c) Conn ∧ Conn ⊆ (O.restrictEdges (R j c)).edges ∧
      (∀ e ∈ Conn, ∀ v ∈ e, v ∈ Up) ∧ Dc.length = (Dp c).length + (Qp c).length ∧
      Dc.countP Obj.isEdge = (Dp c).countP Obj.isEdge := by
    intro c
    obtain ⟨hwf, hnd, hmem, hQ, hpec, _⟩ := hDp c
    refine close_class (hG2 j hj c) hwf hnd (X := Fc c ∪ Res c) ?_ ?_ ?_ ?_ ?_ ?_
    · intro e
      rw [hmem e, Finset.mem_union, hmemRes]
    · intro q hq
      obtain ⟨h1, h2, h3, h4, h5⟩ := hQ q hq
      refine ⟨h1, h2, h3, h4, fun x hx hxV => ?_⟩
      simp only [Vc, Finset.mem_filter] at hxV
      have hxW : x ∉ W := hWUp x hxV.1
      rcases h5 x hx with ⟨e, he, hxe⟩ | hxW' | ⟨w, hw, hx' | hx'⟩
      · exact hFckap c e he x hxe hxW hxV.2
      · exact hxW hxW'
      · rw [hx', (hfC w hw c 0).2.2.2] at hxV
        exact absurd hxV.2 (Fin.succ_ne_zero c).symm
      · rw [hx', (hfC w hw c 1).2.2.2] at hxV
        exact absurd hxV.2 (Fin.succ_ne_zero c).symm
    · intro x hx
      rw [FGraph.restrictEdges_verts, hOZ]
      exact (mem_U.1 hx).1
    · intro x hx
      exact (Finset.mem_filter.1 hx).1
    · intro v
      refine le_trans (Nat.cast_le.2 (hpec v)) ?_
      refine le_trans ?_ (hmult v)
      rw [Nat.cast_add, add_comm]
      push_cast
      refine add_le_add_left (Nat.cast_le.2 (Finset.card_le_card fun w hw => ?_)) _
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨hPZ (mem_Wt.1 hw.1).1, ?_⟩
      rcases hw.2 with h | h <;> rw [h]
      · exact (hfC w hw.1 c 0).2.1
      · exact (hfC w hw.1 c 1).2.1
    · intro e he
      rcases Finset.mem_union.1 he with he | he
      · obtain ⟨w, hw, hwe⟩ := hFcW c e he
        exact ⟨w, hwe, fun hwU => hWUp w hwU hw⟩
      · obtain ⟨w, hw, hwe⟩ := hResW c e he
        exact ⟨w, hwe, fun hwU => hWUp w hwU hw⟩
  choose Conn Dc hDc using hcl
  -- properties of connectors
  have hConnR : ∀ c, ∀ e ∈ Conn c, e ∈ O.edges ∧ e ∈ R j c := fun c e he =>
    FGraph.mem_restrictEdges_edges.1 ((hDc c).2.2.1 he)
  have hConnUp : ∀ c, ∀ e ∈ Conn c, ∀ v ∈ e, v ∈ Up := fun c => (hDc c).2.2.2.1
  have hConnNotW : ∀ c, ∀ e ∈ Conn c, ∀ w ∈ W, w ∉ e := fun c e he w hw hwe =>
    hWUp w (hConnUp c e he w hwe) hw
  -- the step's edges
  let Tc : Fin 3 → Finset (Sym2 V) := fun c => Fc c ∪ Res c ∪ Conn c
  let T : Finset (Sym2 V) := Finset.univ.biUnion Tc
  have hmemT : ∀ e, e ∈ T ↔ ∃ c, e ∈ Fc c ∨ e ∈ Res c ∨ e ∈ Conn c := by
    intro e; simp [T, Tc]
  -- pairwise disjointness of the classes
  have hFcdisj : ∀ c c', c ≠ c' → Disjoint (Fc c) (Fc c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    exact hcc' (((hmemFc c e).1 he).2.2.symm.trans ((hmemFc c' e).1 he').2.2)
  have hFcRes : ∀ c c', Disjoint (Fc c) (Res c') := by
    intro c c'
    rw [Finset.disjoint_left]
    intro e he he'
    exact ((hmemFc c e).1 he).2.1 ((hmemResAll e).2 ⟨c', he'⟩)
  have hResdisj : ∀ c c', c ≠ c' → Disjoint (Res c) (Res c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨w, hw, h1⟩ := (hmemRes c e).1 he
    obtain ⟨w', hw', h2⟩ := (hmemRes c' e).1 he'
    have key : ∀ i i' : Fin 2, s(w, fe w c i) = s(w', fe w' c' i') → False := by
      intro i i' h
      obtain ⟨rfl, h'⟩ := hsym hw (hfW w hw c i) (hfW w' hw' c' i') h
      exact hcc' (hfinj w hw c i c' i' h').1
    rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
    · exact key 0 0 h2
    · exact key 0 1 h2
    · exact key 1 0 h2
    · exact key 1 1 h2
  have hXConn : ∀ c c', Disjoint (Fc c ∪ Res c) (Conn c') := by
    intro c c'
    rw [Finset.disjoint_left]
    intro e he he'
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨w, hw, hwe⟩ := hFcW c e he
      exact hConnNotW c' e he' w hw hwe
    · obtain ⟨w, hw, hwe⟩ := hResW c e he
      exact hConnNotW c' e he' w hw hwe
  have hConndisj : ∀ c c', c ≠ c' → Disjoint (Conn c) (Conn c') := by
    intro c c' hcc'
    rw [Finset.disjoint_left]
    intro e he he'
    have hd := hRd j hj j hj c c' (by simp [hcc'])
    exact Finset.disjoint_left.1 hd (hConnR c e he).2 (hConnR c' e he').2
  have hTdisj : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint Tc := by
    intro c _ c' _ hcc'
    simp only [Function.onFun, Tc]
    rw [Finset.disjoint_left]
    intro e he he'
    have hX1 := hXConn c c'
    have hX2 := hXConn c' c
    simp only [Finset.mem_union] at he he'
    rcases he with (he | he) | he <;> rcases he' with (he' | he') | he'
    · exact Finset.disjoint_left.1 (hFcdisj c c' hcc') he he'
    · exact Finset.disjoint_left.1 (hFcRes c c') he he'
    · exact Finset.disjoint_left.1 hX1 (Finset.mem_union_left _ he) he'
    · exact Finset.disjoint_left.1 (hFcRes c' c) he' he
    · exact Finset.disjoint_left.1 (hResdisj c c' hcc') he he'
    · exact Finset.disjoint_left.1 hX1 (Finset.mem_union_right _ he) he'
    · exact Finset.disjoint_left.1 hX2 (Finset.mem_union_left _ he') he
    · exact Finset.disjoint_left.1 hX2 (Finset.mem_union_right _ he') he
    · exact Finset.disjoint_left.1 (hConndisj c c' hcc') he he'
  have hTdec : IsDecomp ((T : Finset (Sym2 V)) : Set (Sym2 V))
      ((Finset.univ : Finset (Fin 3)).toList.flatMap Dc) :=
    isDecomp_finset_biUnion Finset.univ (Ds := Dc) hTdisj fun c _ => (hDc c).1
  -- membership facts
  have hResS : ∀ c, ∀ e ∈ Res c, e ∉ S := by
    intro c e he
    obtain ⟨w, hw, rfl | rfl⟩ := (hmemRes c e).1 he
    · exact hI3 j le_rfl hj w hw _ (hfC w hw c 0).2.2.1 (hfC w hw c 0).1
    · exact hI3 j le_rfl hj w hw _ (hfC w hw c 1).2.2.1 (hfC w hw c 1).1
  have hConnS : ∀ c, ∀ e ∈ Conn c, e ∉ S := fun c e he =>
    hI2 j le_rfl hj c e (hConnR c e he).2 (hConnUp c e he)
  refine ⟨T, (Finset.univ : Finset (Fin 3)).toList.flatMap Dc, ?_, ?_, ?_, ?_, hTdec, ?_, ?_⟩
  · -- Disjoint T S
    rw [Finset.disjoint_left]
    intro e he heS
    obtain ⟨c, hc | hc | hc⟩ := (hmemT e).1 he
    · exact ((hmemF e).1 ((hmemFc c e).1 hc).1).2.1 heS
    · exact hResS c e hc heS
    · exact hConnS c e hc heS
  · -- T ⊆ E
    intro e he
    obtain ⟨c, hc | hc | hc⟩ := (hmemT e).1 he
    · exact hFcE c e hc
    · exact hOE (hMO (hResM c e hc))
    · exact hOE (hConnR c e hc).1
  · -- F ⊆ T
    intro e he heS heW
    rw [hmemT]
    by_cases hr : e ∈ ResAll
    · obtain ⟨c, hc⟩ := (hmemResAll e).1 hr
      exact ⟨c, Or.inr (Or.inl hc)⟩
    · exact ⟨cls e, Or.inl ((hmemFc _ e).2 ⟨(hmemF e).2 ⟨he, heS, heW⟩, hr, rfl⟩)⟩
  · -- T ⊆ H0 ∪ E(O)
    intro e he
    obtain ⟨c, hc | hc | hc⟩ := (hmemT e).1 he
    · exact Or.inl ((hmemF e).1 ((hmemFc c e).1 hc).1).1
    · exact Or.inr (hMO (hResM c e hc))
    · exact Or.inr (hConnR c e hc).1
  · -- cost
    rw [length_flatMap_toList]
    have hc : ∀ c ∈ (Finset.univ : Finset (Fin 3)), (Dc c).length ≤ 4 * Pj.card := by
      intro c _
      rw [(hDc c).2.2.2.2.1]
      have h1 := (hDp c).2.2.2.2.2
      have h2 : (Pc c).length ≤ Pj.card := (hPc c).1.length_le_card (hPc c).2 (hFcPj c)
      have h3 : W.card ≤ Pj.card := Finset.card_le_card hWP
      omega
    have := Finset.sum_le_sum hc
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  · -- the invariants persist
    refine ⟨?_, ?_, ?_⟩
    · intro e he heST v hv
      have heS : e ∉ S := fun h => heST (Finset.mem_union_left _ h)
      have heT : e ∉ T := fun h => heST (Finset.mem_union_right _ h)
      have h1 := hI1 e he heS v hv
      rcases Nat.lt_or_ge j (lev v) with h | h
      · exact h
      · exfalso
        refine heT ?_
        rw [hmemT]
        have hvW : v ∈ W := mem_Wt.2 ⟨(mem_H0.1 he).2 v hv, le_antisymm h h1⟩
        by_cases hr : e ∈ ResAll
        · obtain ⟨c, hc⟩ := (hmemResAll e).1 hr
          exact ⟨c, Or.inr (Or.inl hc)⟩
        · exact ⟨cls e, Or.inl ((hmemFc _ e).2 ⟨(hmemF e).2 ⟨he, heS, v, hvW, hv⟩, hr, rfl⟩)⟩
    · intro j' hj' hj'J c' e he hU' heST
      have hjj' : j ≠ j' := by omega
      have hUj : ∀ v ∈ e, v ∈ Up := fun v hv => U_anti (by omega) (hU' v hv)
      rcases Finset.mem_union.1 heST with heS | heT
      · exact hI2 j' (by omega) hj'J c' e he hU' heS
      · obtain ⟨c, hc | hc | hc⟩ := (hmemT e).1 heT
        · obtain ⟨w, hw, hwe⟩ := hFcW c e hc
          exact hWUp w (hUj w hwe) hw
        · exact Finset.disjoint_left.1 (hRM j' hj'J c') he (hResM c e hc)
        · have hd := hRd j hj j' hj'J c c' (by simp [hjj'])
          exact Finset.disjoint_left.1 hd (hConnR c e hc).2 he
    · intro j' hj' hj'J w hw u hu hM heST
      have hjj' : j ≠ j' := by omega
      rcases Finset.mem_union.1 heST with heS | heT
      · exact hI3 j' (by omega) hj'J w hw u hu hM heS
      · have hwW : w ∉ W := Wt_ne hjj' hw
        have huW : u ∉ W := hWUp u (U_anti (by omega) hu)
        have hnot : ∀ x ∈ W, x ∉ s(w, u) := by
          intro x hx hxe
          rcases Sym2.mem_iff.1 hxe with rfl | rfl
          · exact hwW hx
          · exact huW hx
        obtain ⟨c, hc | hc | hc⟩ := (hmemT _).1 heT
        · obtain ⟨x, hx, hxe⟩ := hFcW c _ hc
          exact hnot x hx hxe
        · obtain ⟨x, hx, hxe⟩ := hResW c _ hc
          exact hnot x hx hxe
        · exact Finset.disjoint_left.1 (hRM j hj c) (hConnR c _ hc).2 hM

end TPVRun

end EG
