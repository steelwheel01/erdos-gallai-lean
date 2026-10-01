module

public import EG.Lib.HB.SplitTree

/-!
# The generic split and the `τ`-rules: basic facts
(manuscript s2:defWitness Fact, s2:defTauRules Facts (a)–(c), (eqSplit), s2:lemSEP (0))

Unit P3A, proof round 1. Companion of `EG.Defs.HB.Witness`.

* edge membership in the two children and the deleted set of the generic split
  (`mem_splitFst_edges`, `mem_splitSnd_edges`, `mem_splitDel`), and their `s(x,y)` forms;
* the partition `E(H) = E(H_1) ⊔ E(H_2) ⊔ F''` of the generic split (no hypothesis on `U'`,
  `N''`), vertex placement and `|H_1| + |H_2| = |H| + |N''|` (for disjoint `U', N'' ⊆ V(H)`);
* the witness Fact (`witF0_witN_subset`, `witN_witF0`, `isWitness_witF0`), and the `τ`-rule facts that hold for all
  `(U, N, τ)` (`tauF2_subset_tauF1`, `tauF1_subset_witF0`, `tauU1_union_tauN1`, …).
-/

public section

namespace EG.HB

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem forall_mem_sym2_mk {P : V → Prop} {x y : V} : (∀ v ∈ s(x, y), P v) ↔ P x ∧ P y := by
  constructor
  · intro h
    exact ⟨h x (Sym2.mem_mk_left x y), h y (Sym2.mem_mk_right x y)⟩
  · rintro ⟨hx, hy⟩ v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hx
    · exact hy

/-! ### Edges of the generic split -/

theorem mem_splitFst_edges {H : FGraph V} {U' N'' : Finset V} {e : Sym2 V} :
    e ∈ (splitFst H U' N'').edges ↔ e ∈ H.edges ∧ ∀ v ∈ e, v ∈ U' ∪ N'' :=
  FGraph.mem_induce_edges

theorem mem_splitSnd_edges {H : FGraph V} {U' N'' : Finset V} {e : Sym2 V} :
    e ∈ (splitSnd H U' N'').edges ↔
      e ∈ H.edges ∧ (∀ v ∈ e, v ∉ U') ∧ ¬ ∀ v ∈ e, v ∈ N'' := by
  unfold splitSnd
  rw [FGraph.deleteEdges_edges, Finset.mem_sdiff, FGraph.mem_induce_edges,
    FGraph.mem_induce_edges]
  constructor
  · rintro ⟨⟨he, hv⟩, hn⟩
    exact ⟨he, fun v hve => (Finset.mem_sdiff.1 (hv v hve)).2, fun h => hn ⟨he, h⟩⟩
  · rintro ⟨he, hv, hn⟩
    exact ⟨⟨he, fun v hve => Finset.mem_sdiff.2 ⟨H.edge_verts e he v hve, hv v hve⟩⟩,
      fun h => hn h.2⟩

theorem mem_splitDel {H : FGraph V} {U' N'' : Finset V} {e : Sym2 V} :
    e ∈ splitDel H U' N'' ↔
      e ∈ H.edges ∧ ∃ a ∈ U', ∃ b ∈ H.verts \ (U' ∪ N''), s(a, b) = e :=
  FGraph.mem_edgesBetween

theorem splitFst_edges_subset (H : FGraph V) (U' N'' : Finset V) :
    (splitFst H U' N'').edges ⊆ H.edges := (splitFst_le H U' N'').2

theorem splitSnd_edges_subset (H : FGraph V) (U' N'' : Finset V) :
    (splitSnd H U' N'').edges ⊆ H.edges := (splitSnd_le H U' N'').2

/-- The first child and the deleted set are disjoint. -/
theorem disjoint_splitFst_splitDel (H : FGraph V) (U' N'' : Finset V) :
    Disjoint (splitFst H U' N'').edges (splitDel H U' N'') := by
  rw [Finset.disjoint_left]
  intro e h1 h3
  obtain ⟨-, a, -, b, hb, rfl⟩ := mem_splitDel.1 h3
  exact (Finset.mem_sdiff.1 hb).2 ((mem_splitFst_edges.1 h1).2 b (Sym2.mem_mk_right a b))

/-- The second child and the deleted set are disjoint. -/
theorem disjoint_splitSnd_splitDel (H : FGraph V) (U' N'' : Finset V) :
    Disjoint (splitSnd H U' N'').edges (splitDel H U' N'') := by
  rw [Finset.disjoint_left]
  intro e h2 h3
  obtain ⟨-, a, ha, b, -, rfl⟩ := mem_splitDel.1 h3
  exact (mem_splitSnd_edges.1 h2).2.1 a (Sym2.mem_mk_left a b) ha

/-- The two children are edge-disjoint. -/
theorem disjoint_splitFst_splitSnd (H : FGraph V) (U' N'' : Finset V) :
    Disjoint (splitFst H U' N'').edges (splitSnd H U' N'').edges := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨-, hU, hN⟩ := mem_splitSnd_edges.1 h2
  refine hN fun v hv => ?_
  rcases Finset.mem_union.1 ((mem_splitFst_edges.1 h1).2 v hv) with h | h
  · exact absurd h (hU v hv)
  · exact h

/-- The two children and the deleted set cover `E(H)`. -/
theorem splitFst_union_splitSnd_union_splitDel (H : FGraph V) (U' N'' : Finset V) :
    (splitFst H U' N'').edges ∪ (splitSnd H U' N'').edges ∪ splitDel H U' N'' = H.edges := by
  apply Finset.Subset.antisymm
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · rcases Finset.mem_union.1 he with he | he
      · exact splitFst_edges_subset H U' N'' he
      · exact splitSnd_edges_subset H U' N'' he
    · exact splitDel_subset H U' N'' he
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
    have hx : x ∈ H.verts := H.edge_verts _ he x (Sym2.mem_mk_left x y)
    have hy : y ∈ H.verts := H.edge_verts _ he y (Sym2.mem_mk_right x y)
    simp only [Finset.mem_union]
    by_cases hxy : x ∈ U' ∪ N'' ∧ y ∈ U' ∪ N''
    · exact Or.inl (Or.inl (mem_splitFst_edges.2 ⟨he, forall_mem_sym2_mk.2 hxy⟩))
    · by_cases hyo : y ∈ U' ∪ N''
      · -- then `x ∉ U' ∪ N''`
        have hxo : x ∉ U' ∪ N'' := fun h => hxy ⟨h, hyo⟩
        by_cases hyU : y ∈ U'
        · refine Or.inr (mem_splitDel.2 ⟨he, y, hyU, x, Finset.mem_sdiff.2 ⟨hx, hxo⟩,
            Sym2.eq_swap⟩)
        · refine Or.inl (Or.inr (mem_splitSnd_edges.2 ⟨he, forall_mem_sym2_mk.2
            ⟨fun h => hxo (Finset.mem_union_left _ h), hyU⟩, fun h => hxo ?_⟩))
          exact Finset.mem_union_right _ (h x (Sym2.mem_mk_left x y))
      · by_cases hxU : x ∈ U'
        · exact Or.inr (mem_splitDel.2 ⟨he, x, hxU, y, Finset.mem_sdiff.2 ⟨hy, hyo⟩, rfl⟩)
        · refine Or.inl (Or.inr (mem_splitSnd_edges.2 ⟨he, forall_mem_sym2_mk.2
            ⟨hxU, fun h => hyo (Finset.mem_union_left _ h)⟩, fun h => hyo ?_⟩))
          exact Finset.mem_union_right _ (h y (Sym2.mem_mk_right x y))

/-- An edge of `H` lies in exactly one of the two children and the deleted set (trichotomy). -/
theorem mem_split_trichotomy (H : FGraph V) (U' N'' : Finset V) {e : Sym2 V}
    (he : e ∈ H.edges) :
    e ∈ (splitFst H U' N'').edges ∨ e ∈ (splitSnd H U' N'').edges ∨ e ∈ splitDel H U' N'' := by
  rw [← splitFst_union_splitSnd_union_splitDel H U' N''] at he
  simp only [Finset.mem_union] at he
  tauto

/-! ### Vertices of the generic split -/

theorem mem_splitFst_verts_of_mem_left {H : FGraph V} {U' N'' : Finset V} (hU : U' ⊆ H.verts)
    {v : V} (hv : v ∈ U') : v ∈ (splitFst H U' N'').verts := by
  rw [splitFst_verts]
  exact Finset.mem_inter.2 ⟨hU hv, Finset.mem_union_left _ hv⟩

theorem not_mem_splitSnd_verts_of_mem_left {H : FGraph V} {U' N'' : Finset V} {v : V}
    (hv : v ∈ U') : v ∉ (splitSnd H U' N'').verts := by
  rw [splitSnd_verts]
  exact fun h => (Finset.mem_sdiff.1 h).2 hv

theorem mem_splitFst_verts_of_mem_right {H : FGraph V} {U' N'' : Finset V} (hN : N'' ⊆ H.verts)
    {v : V} (hv : v ∈ N'') : v ∈ (splitFst H U' N'').verts := by
  rw [splitFst_verts]
  exact Finset.mem_inter.2 ⟨hN hv, Finset.mem_union_right _ hv⟩

theorem mem_splitSnd_verts_of_mem_right {H : FGraph V} {U' N'' : Finset V} (hN : N'' ⊆ H.verts)
    (hd : Disjoint U' N'') {v : V} (hv : v ∈ N'') : v ∈ (splitSnd H U' N'').verts := by
  rw [splitSnd_verts]
  exact Finset.mem_sdiff.2 ⟨hN hv, fun h => Finset.disjoint_left.1 hd h hv⟩

theorem not_mem_splitFst_verts_of_not_mem {H : FGraph V} {U' N'' : Finset V} {v : V}
    (hv : v ∉ U' ∪ N'') : v ∉ (splitFst H U' N'').verts := by
  rw [splitFst_verts]
  exact fun h => hv (Finset.mem_inter.1 h).2

theorem mem_splitSnd_verts_of_not_mem {H : FGraph V} {U' N'' : Finset V} {v : V}
    (hvH : v ∈ H.verts) (hv : v ∉ U' ∪ N'') : v ∈ (splitSnd H U' N'').verts := by
  rw [splitSnd_verts]
  exact Finset.mem_sdiff.2 ⟨hvH, fun h => hv (Finset.mem_union_left _ h)⟩

/-- A vertex lying in both children lies in `N''`. -/
theorem mem_right_of_mem_both {H : FGraph V} {U' N'' : Finset V} {v : V}
    (h1 : v ∈ (splitFst H U' N'').verts) (h2 : v ∈ (splitSnd H U' N'').verts) : v ∈ N'' := by
  rw [splitFst_verts] at h1
  rw [splitSnd_verts] at h2
  rcases Finset.mem_union.1 (Finset.mem_inter.1 h1).2 with h | h
  · exact absurd h (Finset.mem_sdiff.1 h2).2
  · exact h

theorem splitFst_verts_of_subset {H : FGraph V} {U' N'' : Finset V} (hU : U' ⊆ H.verts)
    (hN : N'' ⊆ H.verts) : (splitFst H U' N'').verts = U' ∪ N'' := by
  rw [splitFst_verts]
  exact Finset.inter_eq_right.2 (Finset.union_subset hU hN)

/-- `|H_1| + |H_2| = |H| + |N''|`. -/
theorem card_splitFst_add_card_splitSnd {H : FGraph V} {U' N'' : Finset V} (hU : U' ⊆ H.verts)
    (hN : N'' ⊆ H.verts) (hd : Disjoint U' N'') :
    (splitFst H U' N'').card + (splitSnd H U' N'').card = H.card + N''.card := by
  simp only [FGraph.card_def, splitFst_verts_of_subset hU hN, splitSnd_verts]
  rw [Finset.card_union_of_disjoint hd]
  have := Finset.card_sdiff_add_card_eq_card hU
  omega

theorem card_splitSnd {H : FGraph V} {U' N'' : Finset V} (hU : U' ⊆ H.verts) :
    (splitSnd H U' N'').card = H.card - U'.card := by
  simp only [FGraph.card_def, splitSnd_verts]
  exact Finset.card_sdiff_of_subset hU

theorem card_splitFst {H : FGraph V} {U' N'' : Finset V} (hU : U' ⊆ H.verts)
    (hN : N'' ⊆ H.verts) : (splitFst H U' N'').card = (U' ∪ N'').card := by
  simp only [FGraph.card_def, splitFst_verts_of_subset hU hN]

theorem splitFst_card_le (H : FGraph V) (U' N'' : Finset V) :
    (splitFst H U' N'').card ≤ H.card := Finset.card_le_card (splitFst_le H U' N'').1

theorem splitSnd_card_le (H : FGraph V) (U' N'' : Finset V) :
    (splitSnd H U' N'').card ≤ H.card := Finset.card_le_card (splitSnd_le H U' N'').1

/-! ### The witness Fact -/

/-- [s2:defWitness] Fact, first part: `F_0 ⊆ F` (for every `U`, `F`). -/
theorem witF0_witN_subset (H : FGraph V) (U : Finset V) (F : Finset (Sym2 V)) :
    witF0 H U (witN H U F) ⊆ F := by
  intro e he
  obtain ⟨he, a, ha, b, hb, rfl⟩ := FGraph.mem_edgesBetween.1 he
  by_contra hF
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hb
  refine hb.2.2 (FGraph.mem_nbrSet.2 ⟨hb.1, hb.2.1, a, ha, ?_⟩)
  exact FGraph.deleteEdges_adj.2 ⟨he, hF⟩

/-- [s2:defWitness] Fact, second part: `Nbr_{H-F_0}(U) = N`. -/
theorem witN_witF0 (H : FGraph V) (U : Finset V) (F : Finset (Sym2 V)) :
    witN H U (witF0 H U (witN H U F)) = witN H U F := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨hvV, hvU, u, hu, huv⟩ := FGraph.mem_nbrSet.1 hv
    rw [FGraph.deleteEdges_adj] at huv
    by_contra hvN
    refine huv.2 (FGraph.mem_edgesBetween.2 ⟨huv.1, u, hu, v, ?_, rfl⟩)
    rw [Finset.mem_sdiff, Finset.mem_union, not_or]
    exact ⟨hvV, hvU, hvN⟩
  · exact H.nbrSet_deleteEdges_anti (witF0_witN_subset H U F) U

/-- [s2:defWitness] Fact, last part: `(U, F_0)` is again a witness. -/
theorem isWitness_witF0 {H : FGraph V} {ε s : ℝ} {U : Finset V} {F : Finset (Sym2 V)}
    (hw : IsWitness H ε s U F) : IsWitness H ε s U (witF0 H U (witN H U F)) := by
  obtain ⟨hU, _, h1, h23, hF, hN⟩ := hw
  refine ⟨hU, witF0_subset H U _, h1, h23, ?_, ?_⟩
  · have : ((witF0 H U (witN H U F)).card : ℝ) ≤ F.card := by
      exact_mod_cast Finset.card_le_card (witF0_witN_subset H U F)
    linarith
  · have := witN_witF0 H U F
    unfold witN at this ⊢
    rw [this]
    exact hN

/-! ### `τ`-rule facts valid for all `(U, N, τ)` -/

theorem tauHout_subset_tauN1 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauHout H U N τ ⊆ tauN1 H U N τ := Finset.subset_union_right

theorem tauN1_subset_tauN2 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauN1 H U N τ ⊆ tauN2 H U N τ := Finset.subset_union_left

theorem tauHin_subset_tauN2 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauHin H U N τ ⊆ tauN2 H U N τ := Finset.subset_union_right

theorem tauHin_subset_verts (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauHin H U N τ ⊆ H.verts := fun _ hx =>
  (Finset.mem_sdiff.1 (Finset.mem_filter.1 hx).1).1

theorem tauU1_union_tauN1 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauU1 H U N τ ∪ tauN1 H U N τ = U ∪ N := by
  ext v
  simp only [tauU1, tauN1, Finset.mem_union, Finset.mem_sdiff]
  have := @tauHout_subset _ _ H U N τ v
  tauto

theorem tauF1_subset_witF0 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauF1 H U N τ ⊆ witF0 H U N := by
  intro e he
  unfold tauF1 at he
  rw [tauU1_union_tauN1] at he
  obtain ⟨he, a, ha, b, hb, rfl⟩ := FGraph.mem_edgesBetween.1 he
  exact FGraph.mem_edgesBetween.2 ⟨he, a, tauU1_subset H U N τ ha, b, hb, rfl⟩

theorem tauF2_subset_tauF1 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauF2 H U N τ ⊆ tauF1 H U N τ := by
  intro e he
  obtain ⟨he, a, ha, b, hb, rfl⟩ := FGraph.mem_edgesBetween.1 he
  refine FGraph.mem_edgesBetween.2 ⟨he, a, ha, b, ?_, rfl⟩
  rw [Finset.mem_sdiff, Finset.mem_union] at hb ⊢
  exact ⟨hb.1, fun h => hb.2 (h.imp id (fun h => tauN1_subset_tauN2 H U N τ h))⟩

theorem tauF2_subset_witF0 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    tauF2 H U N τ ⊆ witF0 H U N :=
  (tauF2_subset_tauF1 H U N τ).trans (tauF1_subset_witF0 H U N τ)

theorem disjoint_tauU1_tauN2 {H : FGraph V} {U N : Finset V} (τ : ℝ) (hUN : Disjoint U N) :
    Disjoint (tauU1 H U N τ) (tauN2 H U N τ) := by
  rw [Finset.disjoint_left]
  intro v hv hv2
  simp only [tauN2, tauN1, Finset.mem_union] at hv2
  rcases hv2 with (h | h) | h
  · exact Finset.disjoint_left.1 hUN (tauU1_subset H U N τ hv) h
  · exact (Finset.mem_sdiff.1 hv).2 h
  · have := (Finset.mem_sdiff.1 (Finset.mem_filter.1 h).1).2
    exact this (Finset.mem_union_left _ hv)

theorem tauU1_subset_verts {H : FGraph V} {U N : Finset V} (τ : ℝ) (hU : U ⊆ H.verts) :
    tauU1 H U N τ ⊆ H.verts := (tauU1_subset H U N τ).trans hU

theorem tauN2_subset_verts {H : FGraph V} {U N : Finset V} (τ : ℝ) (hU : U ⊆ H.verts)
    (hN : N ⊆ H.verts) : tauN2 H U N τ ⊆ H.verts := by
  intro v hv
  simp only [tauN2, tauN1, Finset.mem_union] at hv
  rcases hv with (h | h) | h
  · exact hN h
  · exact hU (tauHout_subset H U N τ h)
  · exact tauHin_subset_verts H U N τ h

theorem subset_tauU1_union_tauN2 (H : FGraph V) (U N : Finset V) (τ : ℝ) :
    U ⊆ tauU1 H U N τ ∪ tauN2 H U N τ := by
  intro v hv
  by_cases h : v ∈ tauHout H U N τ
  · exact Finset.mem_union_right _
      (tauN1_subset_tauN2 H U N τ (tauHout_subset_tauN1 H U N τ h))
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hv, h⟩)

/-- The labels of a witness split are a split of Lemma SEP: disjoint subsets of `V(H)`. -/
theorem tau_split_wf {H : FGraph V} {ε s τ : ℝ} {U : Finset V} {F : Finset (Sym2 V)}
    (hw : IsWitness H ε s U F) :
    tauU1 H U (witN H U F) τ ⊆ H.verts ∧ tauN2 H U (witN H U F) τ ⊆ H.verts ∧
      Disjoint (tauU1 H U (witN H U F) τ) (tauN2 H U (witN H U F) τ) :=
  ⟨tauU1_subset_verts τ hw.1, tauN2_subset_verts τ hw.1 (witN_subset_verts H U F),
    disjoint_tauU1_tauN2 τ (disjoint_witN H U F)⟩

/-- A witness with parameter `0` has `F = ∅`. -/
theorem eq_empty_of_isWitness_zero {K : FGraph V} {ε : ℝ} {U : Finset V}
    {F : Finset (Sym2 V)} (hw : IsWitness K ε 0 U F) : F = ∅ := by
  have h := hw.2.2.2.2.1
  rw [zero_mul] at h
  have : F.card = 0 := by exact_mod_cast le_antisymm h (Nat.cast_nonneg _)
  exact Finset.card_eq_zero.1 this

/-- A graph carrying a witness has at least two vertices. -/
theorem two_le_card_of_isWitness {K : FGraph V} {ε s : ℝ} {U : Finset V}
    {F : Finset (Sym2 V)} (hw : IsWitness K ε s U F) : 2 ≤ K.card := by
  obtain ⟨-, -, h1, h23, -, -⟩ := hw
  have h1' : (1 : ℝ) ≤ U.card := by exact_mod_cast h1
  have : (1 : ℝ) < K.card := by linarith
  have : 1 < K.card := by exact_mod_cast this
  omega

end EG.HB
