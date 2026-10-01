module

public import EG.Lib.HB.Address

/-!
# Lemma SEP and the thin cut: the generic arguments (manuscript s2:lemSEP, s2:lemThinCut)

Unit P3A, proof round 1. The Spec-level theorems are in `EG.Proof.HB.SEP` and
`EG.Proof.HB.ThinCut`; this file holds the lemmas they share with Lemma 14^τ.

* `STree.sep_count`: every edge of `H_0` lies in exactly one leaf or is deleted at exactly one
  node (SEP (i), count form; no `WF` needed);
* `STree.eq_of_not_mem_dup`: a vertex outside `Dup` lies in at most one leaf;
* `STree.prefix_of_mem_of_not_mem_dup`: a node containing `u ∉ Dup` is a prefix of the leaf of
  `u` (SEP (ii));
* `STree.not_mem_child_of_mem_delAt`: the two ends of an edge deleted at `a` do not lie in a
  common child of `a` (SEP (i));
* `STree.mem_delAt_deepest`: SEP (iii);
* `STree.thinCut_lt`: the thin-cut count is `< τ` (and `0` if `h ∈ V(Leaf)`), for every tree whose
  labels are produced by the `τ`-rules from some pair `(U, N)`.
-/

public section

namespace EG.HB

namespace STree

variable {V : Type*} [DecidableEq V]

/-! ### SEP (i): the count -/

theorem card_filter_leaf_edges_eq_zero (t : STree V) {H : FGraph V} {e : Sym2 V}
    (he : e ∉ H.edges) : (t.leafAddrs.filter (fun L => e ∈ (t.graphAtD H L).edges)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun L _ h => he (graphAtD_edges_subset t H L h)

theorem card_filter_delAt_eq_zero (t : STree V) {H : FGraph V} {e : Sym2 V}
    (he : e ∉ H.edges) : (t.internalAddrs.filter (fun a => e ∈ t.delAt H a)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun a _ h => he (graphAtD_edges_subset t H a (delAt_subset t H a h))

/-- [s2:lemSEP] (i), count form: every edge of `H_0` lies in exactly one leaf or is deleted at
exactly one node. -/
theorem sep_count (t : STree V) {H : FGraph V} {e : Sym2 V} (he : e ∈ H.edges) :
    (t.leafAddrs.filter (fun L => e ∈ (t.graphAtD H L).edges)).card +
      (t.internalAddrs.filter (fun a => e ∈ t.delAt H a)).card = 1 := by
  induction t generalizing H with
  | nil =>
    simp [he]
  | node p l r ihl ihr =>
    have e1 : ((STree.node p l r).leafAddrs.filter
        (fun L => e ∈ ((STree.node p l r).graphAtD H L).edges)).card =
        (l.leafAddrs.filter (fun L => e ∈ (l.graphAtD (splitFst H p.1 p.2) L).edges)).card +
        (r.leafAddrs.filter (fun L => e ∈ (r.graphAtD (splitSnd H p.1 p.2) L).edges)).card :=
      card_filter_leafAddrs_node p l r _
    have e2 : ((STree.node p l r).internalAddrs.filter
        (fun a => e ∈ (STree.node p l r).delAt H a)).card =
        (if e ∈ splitDel H p.1 p.2 then 1 else 0) +
        ((l.internalAddrs.filter (fun a => e ∈ l.delAt (splitFst H p.1 p.2) a)).card +
        (r.internalAddrs.filter (fun a => e ∈ r.delAt (splitSnd H p.1 p.2) a)).card) :=
      card_filter_internalAddrs_node p l r _
    rw [e1, e2]
    rcases mem_split_trichotomy H p.1 p.2 he with h | h | h
    · have h2 : e ∉ (splitSnd H p.1 p.2).edges := fun h' =>
        Finset.disjoint_left.1 (disjoint_splitFst_splitSnd H p.1 p.2) h h'
      have h3 : e ∉ splitDel H p.1 p.2 := fun h' =>
        Finset.disjoint_left.1 (disjoint_splitFst_splitDel H p.1 p.2) h h'
      have := ihl h
      rw [card_filter_leaf_edges_eq_zero r h2, card_filter_delAt_eq_zero r h2, if_neg h3]
      omega
    · have h1 : e ∉ (splitFst H p.1 p.2).edges := fun h' =>
        Finset.disjoint_left.1 (disjoint_splitFst_splitSnd H p.1 p.2) h' h
      have h3 : e ∉ splitDel H p.1 p.2 := fun h' =>
        Finset.disjoint_left.1 (disjoint_splitSnd_splitDel H p.1 p.2) h h'
      have := ihr h
      rw [card_filter_leaf_edges_eq_zero l h1, card_filter_delAt_eq_zero l h1, if_neg h3]
      omega
    · have h1 : e ∉ (splitFst H p.1 p.2).edges := fun h' =>
        Finset.disjoint_left.1 (disjoint_splitFst_splitDel H p.1 p.2) h' h
      have h2 : e ∉ (splitSnd H p.1 p.2).edges := fun h' =>
        Finset.disjoint_left.1 (disjoint_splitSnd_splitDel H p.1 p.2) h' h
      rw [card_filter_leaf_edges_eq_zero l h1, card_filter_delAt_eq_zero l h1,
        card_filter_leaf_edges_eq_zero r h2, card_filter_delAt_eq_zero r h2, if_pos h]

theorem mem_deleted_iff {t : STree V} {H : FGraph V} {e : Sym2 V} :
    e ∈ t.deleted H ↔ ∃ a ∈ t.internalAddrs, e ∈ t.delAt H a := by
  simp [deleted]

/-- An edge that is not deleted lies in a leaf. -/
theorem exists_leaf_of_not_mem_deleted (t : STree V) {H : FGraph V} {e : Sym2 V}
    (he : e ∈ H.edges) (hd : e ∉ t.deleted H) :
    ∃ L ∈ t.leafAddrs, e ∈ (t.graphAtD H L).edges := by
  have h := sep_count t he
  have h0 : (t.internalAddrs.filter (fun a => e ∈ t.delAt H a)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun a ha h' => hd (mem_deleted_iff.2 ⟨a, ha, h'⟩)
  rw [h0, add_zero] at h
  obtain ⟨L, hL⟩ := Finset.card_pos.1
    (by omega : 0 < (t.leafAddrs.filter (fun L => e ∈ (t.graphAtD H L).edges)).card)
  exact ⟨L, (Finset.mem_filter.1 hL).1, (Finset.mem_filter.1 hL).2⟩

/-! ### Vertices outside `Dup` -/

/-- A vertex outside `Dup` lies in at most one leaf. -/
theorem eq_of_not_mem_dup {t : STree V} {H : FGraph V} {u : V} (hu : u ∉ t.dup H)
    {L₁ L₂ : Addr} (h₁ : L₁ ∈ t.leafAddrs) (h₂ : L₂ ∈ t.leafAddrs)
    (hu₁ : u ∈ (t.graphAtD H L₁).verts) (hu₂ : u ∈ (t.graphAtD H L₂).verts) : L₁ = L₂ := by
  by_contra hne
  exact hu (mem_dup_iff_exists.2 ⟨L₁, h₁, L₂, h₂, hne, hu₁, hu₂⟩)

/-- [s2:lemSEP] (ii) A node containing `u ∉ Dup` is a prefix of the (unique) leaf containing
`u`. -/
theorem prefix_of_mem_of_not_mem_dup {t : STree V} {H : FGraph V} {u : V} (hu : u ∉ t.dup H)
    {L : Addr} (hL : L ∈ t.leafAddrs) (huL : u ∈ (t.graphAtD H L).verts) {a : Addr}
    (ha : a ∈ t.nodeAddrs) (hua : u ∈ (t.graphAtD H a).verts) : a <+: L := by
  obtain ⟨b, hb, hab, hub⟩ := exists_leaf_below t H ha hua
  rw [eq_of_not_mem_dup hu hb hL hub huL] at hab
  exact hab

/-- [s2:lemSEP] (i) The two ends of an edge deleted at `a` go to different children, each to only
one: no child of `a` contains both. -/
theorem not_mem_child_of_mem_delAt {t : STree V} {H : FGraph V} {a : Addr}
    (ha : a ∈ t.internalAddrs) {x y : V} (he : s(x, y) ∈ t.delAt H a) (c : Bool)
    (hx : x ∈ (t.graphAtD H (a ++ [c])).verts) (hy : y ∈ (t.graphAtD H (a ++ [c])).verts) :
    False := by
  rw [delAt_def'] at he
  obtain ⟨-, x', hx', y', hy', hxy⟩ := mem_splitDel.1 he
  have hx'e : x' = x ∨ x' = y := by
    have : x' ∈ s(x, y) := hxy ▸ Sym2.mem_mk_left x' y'
    exact Sym2.mem_iff.1 this
  have hy'e : y' = x ∨ y' = y := by
    have : y' ∈ s(x, y) := hxy ▸ Sym2.mem_mk_right x' y'
    exact Sym2.mem_iff.1 this
  have hx'c : x' ∈ (t.graphAtD H (a ++ [c])).verts := by rcases hx'e with rfl | rfl <;> assumption
  have hy'c : y' ∈ (t.graphAtD H (a ++ [c])).verts := by rcases hy'e with rfl | rfl <;> assumption
  cases c
  · rw [graphAtD_append_false ha] at hy'c
    exact not_mem_splitFst_verts_of_not_mem (Finset.mem_sdiff.1 hy').2 hy'c
  · rw [graphAtD_append_true ha] at hx'c
    exact not_mem_splitSnd_verts_of_mem_left hx' hx'c

/-- An edge deleted at a non-leaf prefix `a` of a leaf `L` does not have both ends in `L`. -/
theorem not_mem_leaf_of_mem_delAt {t : STree V} {H : FGraph V} {a L : Addr}
    (ha : a ∈ t.internalAddrs) (hL : L ∈ t.leafAddrs) (haL : a <+: L) {x y : V}
    (he : s(x, y) ∈ t.delAt H a) (hx : x ∈ (t.graphAtD H L).verts)
    (hy : y ∈ (t.graphAtD H L).verts) : False := by
  have hne : a ≠ L := fun h =>
    Finset.disjoint_left.1 (disjoint_leafAddrs_internalAddrs t) hL (h ▸ ha)
  obtain ⟨c, hc⟩ := exists_append_singleton_prefix haL hne
  have hle := graphAtD_mono t H hc
  exact not_mem_child_of_mem_delAt ha he c (hle.1 hx) (hle.1 hy)

/-- The ends of a deleted edge lie in the node where it is deleted. -/
theorem mem_verts_of_mem_delAt (t : STree V) (H : FGraph V) {a : Addr} {x y : V}
    (he : s(x, y) ∈ t.delAt H a) :
    x ∈ (t.graphAtD H a).verts ∧ y ∈ (t.graphAtD H a).verts :=
  ⟨(t.graphAtD H a).edge_verts _ (delAt_subset t H a he) x (Sym2.mem_mk_left x y),
    (t.graphAtD H a).edge_verts _ (delAt_subset t H a he) y (Sym2.mem_mk_right x y)⟩

/-- [s2:lemSEP] (iii) With `ν^*` the deepest prefix of `Leaf_u` containing `h`, every deleted
edge `hu'` with `u' ∈ V(Leaf_u) \ Dup` is deleted at `ν^*`. -/
theorem mem_delAt_deepest {t : STree V} {H : FGraph V} {L : Addr}
    (hL : L ∈ t.leafAddrs) {h : V} {νs : Addr} (hνL : νs <+: L)
    (hνh : h ∈ (t.graphAtD H νs).verts)
    (hmax : ∀ b : Addr, b <+: L → h ∈ (t.graphAtD H b).verts → b.length ≤ νs.length)
    {u' : V} (hu'L : u' ∈ (t.graphAtD H L).verts) (hu' : u' ∉ t.dup H)
    (hd : s(h, u') ∈ t.deleted H) : s(h, u') ∈ t.delAt H νs := by
  obtain ⟨a, ha, he⟩ := mem_deleted_iff.1 hd
  obtain ⟨hha, hu'a⟩ := mem_verts_of_mem_delAt t H he
  have haL : a <+: L := prefix_of_mem_of_not_mem_dup hu' hL hu'L
    (internalAddrs_subset_nodeAddrs t ha) hu'a
  have hlen := hmax a haL hha
  have haν : a <+: νs := List.prefix_of_prefix_length_le haL hνL hlen
  by_cases hEq : a = νs
  · exact hEq ▸ he
  · exfalso
    obtain ⟨c, hc⟩ := exists_append_singleton_prefix haν hEq
    have h1 := graphAtD_mono t H hc
    have h2 := graphAtD_mono t H (hc.trans hνL)
    exact not_mem_child_of_mem_delAt ha he c (h1.1 hνh) (h2.1 hu'L)

/-! ### The thin cut -/

/-- The deepest prefix of `L` containing `h` exists (when `h ∈ V(H_0)`). -/
theorem exists_deepest (t : STree V) {H : FGraph V} (L : Addr) {h : V} (hh : h ∈ H.verts) :
    ∃ νs : Addr, νs <+: L ∧ h ∈ (t.graphAtD H νs).verts ∧
      ∀ b : Addr, b <+: L → h ∈ (t.graphAtD H b).verts → b.length ≤ νs.length := by
  classical
  let P : Finset Addr := L.inits.toFinset.filter (fun b => h ∈ (t.graphAtD H b).verts)
  have hne : P.Nonempty := ⟨[], Finset.mem_filter.2 ⟨List.mem_toFinset.2
    (List.mem_inits _ _ |>.2 List.nil_prefix), by simpa using hh⟩⟩
  obtain ⟨νs, hν, hmax⟩ := Finset.exists_max_image P List.length hne
  obtain ⟨hν1, hν2⟩ := Finset.mem_filter.1 hν
  refine ⟨νs, (List.mem_inits _ _).1 (List.mem_toFinset.1 hν1), hν2, fun b hb hhb => ?_⟩
  exact hmax b (Finset.mem_filter.2 ⟨List.mem_toFinset.2 ((List.mem_inits _ _).2 hb), hhb⟩)

/-- The labels of every non-leaf node are produced by the `τ`-rules from some pair `(U, N)` at
threshold `τ` (the only property of the `τ`-rules used by the thin cut). -/
@[expose] def TauLabels (τ : ℝ) (t : STree V) (H : FGraph V) : Prop :=
  ∀ a ∈ t.internalAddrs, ∃ U N : Finset V,
    t.labelAt a = some (tauU1 (t.graphAtD H a) U N τ, tauN2 (t.graphAtD H a) U N τ)

theorem IsTauSplitTree.tauLabels {ε τ : ℝ} {t : STree V} {H : FGraph V}
    (ht : t.IsTauSplitTree ε τ H) : t.TauLabels τ H := by
  intro a ha
  obtain ⟨s, U, F, -, -, hl⟩ := ht.2 a ha
  exact ⟨U, _, hl⟩

theorem IsTauRun.tauLabels {ε τ : ℝ} {s : ℕ} {t : STree V} {H : FGraph V}
    (ht : t.IsTauRun ε s τ H) : t.TauLabels τ H := by
  intro a ha
  obtain ⟨U, F, -, hl⟩ := ht.2.2 a ha
  exact ⟨U, _, hl⟩

/-- The count of the thin cut is `0` when `h ∈ V(Leaf)` (no `WF` is needed). -/
theorem thinCut_eq_zero {t : STree V} {H : FGraph V} {L : Addr}
    (hL : L ∈ t.leafAddrs) {h : V} (hh : h ∈ (t.graphAtD H L).verts) :
    ((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H,
      e = s(h, u))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro e hd ⟨u, hu, rfl⟩
  obtain ⟨huL, hud⟩ := Finset.mem_sdiff.1 hu
  obtain ⟨a, ha, he⟩ := mem_deleted_iff.1 hd
  have hua := (mem_verts_of_mem_delAt t H he).2
  have haL := prefix_of_mem_of_not_mem_dup hud hL huL (internalAddrs_subset_nodeAddrs t ha) hua
  exact not_mem_leaf_of_mem_delAt ha hL haL he hh huL

/-- [s2:lemThinCut] The count of the thin cut is `< τ` (for `τ > 0`). -/
theorem thinCut_lt {τ : ℝ} (hτ : 0 < τ) {t : STree V} {H : FGraph V}
    (hlab : t.TauLabels τ H) {L : Addr} (hL : L ∈ t.leafAddrs) (h : V) :
    (((t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H,
      e = s(h, u))).card : ℝ) < τ := by
  set S := (t.deleted H).filter (fun e => ∃ u ∈ (t.graphAtD H L).verts \ t.dup H, e = s(h, u))
  by_cases hhL : h ∈ (t.graphAtD H L).verts
  · rw [thinCut_eq_zero hL hhL]
    simpa using hτ
  by_cases hS : S = ∅
  · rw [hS]
    simpa using hτ
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hS
  obtain ⟨hd0, u0, -, rfl⟩ := Finset.mem_filter.1 he0
  have hhH : h ∈ H.verts :=
    H.edge_verts _ (deleted_subset t H hd0) h (Sym2.mem_mk_left h u0)
  obtain ⟨νs, hνL, hνh, hmax⟩ := exists_deepest t L hhH
  have hνne : νs ≠ L := fun h' => hhL (h' ▸ hνh)
  have hν : νs ∈ t.internalAddrs :=
    mem_internalAddrs_of_prefix_of_ne (leafAddrs_subset_nodeAddrs t hL) hνL hνne
  -- every edge of `S` is deleted at `νs` and meets `h`
  have hsub : S ⊆ edgesAt (t.delAt H νs) h := by
    intro e he
    obtain ⟨hd, u, hu, rfl⟩ := Finset.mem_filter.1 he
    obtain ⟨huL, hud⟩ := Finset.mem_sdiff.1 hu
    exact FGraph.mem_edgesAt.2
      ⟨mem_delAt_deepest hL hνL hνh hmax huL hud hd, Sym2.mem_mk_left h u⟩
  refine lt_of_le_of_lt (Nat.cast_le.2 (Finset.card_le_card hsub)) ?_
  obtain ⟨c, hc⟩ := exists_append_singleton_prefix hνL hνne
  have hhc : h ∉ (t.graphAtD H (νs ++ [c])).verts := fun h' => by
    have := hmax _ hc h'
    simp at this
  obtain ⟨U, N, hlabν⟩ := hlab νs hν
  set K := t.graphAtD H νs with hK
  have hU : t.labelU νs = tauU1 K U N τ := labelU_of_labelAt hlabν
  have hN : t.labelN νs = tauN2 K U N τ := labelN_of_labelAt hlabν
  have hdel : t.delAt H νs = tauF2 K U N τ := by
    rw [delAt_def', hU, hN]
    rfl
  rw [hdel]
  cases c
  · rw [graphAtD_append_false hν, hU, hN] at hhc
    have hno : h ∉ tauU1 K U N τ ∪ tauN2 K U N τ := fun h' =>
      hhc (Finset.mem_inter.2 ⟨hνh, h'⟩)
    have hnotin : h ∉ tauHin K U N τ := fun h' =>
      hno (Finset.mem_union_right _ (tauHin_subset_tauN2 K U N τ h'))
    have hmem : h ∈ K.verts \ (tauU1 K U N τ ∪ tauN1 K U N τ) := by
      refine Finset.mem_sdiff.2 ⟨hνh, fun h' => hno ?_⟩
      rcases Finset.mem_union.1 h' with h' | h'
      · exact Finset.mem_union_left _ h'
      · exact Finset.mem_union_right _ (tauN1_subset_tauN2 K U N τ h')
    have hlt : ¬ τ ≤ (degE (tauF1 K U N τ) h : ℝ) := fun h' =>
      hnotin (Finset.mem_filter.2 ⟨hmem, h'⟩)
    have hle : degE (tauF2 K U N τ) h ≤ degE (tauF1 K U N τ) h :=
      FGraph.degE_mono (tauF2_subset_tauF1 K U N τ) h
    have : (degE (tauF2 K U N τ) h : ℝ) ≤ degE (tauF1 K U N τ) h := by exact_mod_cast hle
    show ((degE (tauF2 K U N τ) h : ℕ) : ℝ) < τ
    linarith [not_le.1 hlt]
  · rw [graphAtD_append_true hν, hU] at hhc
    have hin : h ∈ tauU1 K U N τ := by
      by_contra h'
      exact hhc (by rw [splitSnd_verts]; exact Finset.mem_sdiff.2 ⟨hνh, h'⟩)
    obtain ⟨hhU, hhout⟩ := Finset.mem_sdiff.1 hin
    have hlt : ¬ τ ≤ (degE (witF0 K U N) h : ℝ) := fun h' =>
      hhout (Finset.mem_filter.2 ⟨hhU, h'⟩)
    have hle : degE (tauF2 K U N τ) h ≤ degE (witF0 K U N) h :=
      FGraph.degE_mono (tauF2_subset_witF0 K U N τ) h
    have : (degE (tauF2 K U N τ) h : ℝ) ≤ degE (witF0 K U N) h := by exact_mod_cast hle
    show ((degE (tauF2 K U N τ) h : ℕ) : ℝ) < τ
    linarith [not_le.1 hlt]

/-- [s2:lemThinCut] (Moreover) If `u ∉ Dup`, every edge at `u` is deleted or an edge of the
unique leaf containing `u`. -/
theorem thinCut_edge (t : STree V) {H : FGraph V} {u : V} (hu : u ∉ t.dup H) {e : Sym2 V}
    (he : e ∈ H.edges) (hue : u ∈ e) :
    e ∈ t.deleted H ∨ ∃ L ∈ t.leafAddrs, u ∈ (t.graphAtD H L).verts ∧
      e ∈ (t.graphAtD H L).edges ∧
        ∀ L' ∈ t.leafAddrs, u ∈ (t.graphAtD H L').verts → L' = L := by
  by_cases hd : e ∈ t.deleted H
  · exact Or.inl hd
  · obtain ⟨L, hL, heL⟩ := exists_leaf_of_not_mem_deleted t he hd
    have huL : u ∈ (t.graphAtD H L).verts := (t.graphAtD H L).edge_verts e heL u hue
    exact Or.inr ⟨L, hL, huL, heL, fun L' hL' huL' => eq_of_not_mem_dup hu hL' hL huL' huL⟩

end STree

end EG.HB
