module

public import EG.Spec.HB.SEP
public import EG.Lib.HB.SEP

/-!
# Proof of Lemma SEP (manuscript s2:lemSEP)

Unit P3A, proof round 1. Design note `formal/work/p2b/P3A.md`. The generic lemmas are in
`EG.Lib.HB.Split`, `EG.Lib.HB.Address` and `EG.Lib.HB.SEP`.

* `EG.sep0 : EG.Spec.SEP0Statement` ((0));
* `EG.sepMono : EG.Spec.SEPMonoStatement` ((0'), implicit);
* `EG.sepI`, `EG.sepII`, `EG.sepIII` ((i), (ii), (iii)).
-/

public section

namespace EG

open EG.HB EG.HB.STree


/-- [s2:lemSEP] (0) "at every non-leaf `ν`, `E(H_ν) = E(H_{ν_1}) ⊔ E(H_{ν_2}) ⊔ F''_ν`; a vertex
of `U'_ν` lies only in `ν_1`, a vertex of `N''_ν` lies in both children, every other vertex of
`ν` lies only in `ν_2`, and `|ν_1| + |ν_2| = |ν| + |N''_ν|`. Every vertex of a node lies in at
least one leaf below it, and the total size of the leaves is `|H_0| + Σ_ν |N''_ν|`, the sum over
the non-leaf nodes." -/
theorem sep0 : EG.Spec.SEP0Statement := by
  intro V _ H t ht
  refine ⟨fun a ha => ?_, fun a ha v hv => exists_leaf_below t H ha hv, leafMass_eq t ht⟩
  obtain ⟨hU, hN, hd⟩ := ht a ha
  rw [graphAtD_append_false ha, graphAtD_append_true ha, delAt_def']
  refine ⟨disjoint_splitFst_splitSnd _ _ _, disjoint_splitFst_splitDel _ _ _,
    disjoint_splitSnd_splitDel _ _ _, splitFst_union_splitSnd_union_splitDel _ _ _,
    fun v hv => ⟨mem_splitFst_verts_of_mem_left hU hv, not_mem_splitSnd_verts_of_mem_left hv⟩,
    fun v hv => ⟨mem_splitFst_verts_of_mem_right hN hv, mem_splitSnd_verts_of_mem_right hN hd hv⟩,
    fun v hv => ?_, card_splitFst_add_card_splitSnd hU hN hd⟩
  obtain ⟨hvH, hvo⟩ := Finset.mem_sdiff.1 hv
  exact ⟨not_mem_splitFst_verts_of_not_mem hvo, mem_splitSnd_verts_of_not_mem hvH hvo⟩

/-- [s2:lemSEP] (0'), implicit: "Every edge of a child is an edge of its parent", "vertex sets
shrink downwards". -/
theorem sepMono : EG.Spec.SEPMonoStatement := by
  intro V _ H t a b _ hab
  exact graphAtD_mono t H hab

/-- [s2:lemSEP] (i) "every edge `xy` of `H_0` either lies in exactly one leaf, which contains `x`
and `y`, or is deleted at exactly one node `ν`. In the second case `x` and `y` lie in `ν` and go
to different children of `ν`, each to only one child, and `ν` is the first node on the path of
nodes having `xy` as an edge at which this happens." -/
theorem sepI : EG.Spec.SEPiStatement := by
  intro V _ H t ht e he
  refine ⟨sep_count t he, fun L _ heL x hx => (t.graphAtD H L).edge_verts e heL x hx,
    fun a ha hea => ?_⟩
  obtain ⟨hU, -, -⟩ := ht a ha
  refine ⟨fun b hb => (graphAtD_mono t H hb).2 (delAt_subset t H a hea), ?_, ?_, ?_⟩
  · rw [graphAtD_append_false ha]
    exact fun h => Finset.disjoint_left.1 (disjoint_splitFst_splitDel _ _ _) h hea
  · rw [graphAtD_append_true ha]
    exact fun h => Finset.disjoint_left.1 (disjoint_splitSnd_splitDel _ _ _) h hea
  · rw [delAt_def'] at hea
    obtain ⟨-, x, hx, y, hy, rfl⟩ := mem_splitDel.1 hea
    obtain ⟨hyH, hyo⟩ := Finset.mem_sdiff.1 hy
    rw [graphAtD_append_false ha, graphAtD_append_true ha]
    exact ⟨x, y, rfl, hx, hy, mem_splitFst_verts_of_mem_left hU hx,
      not_mem_splitSnd_verts_of_mem_left hx, not_mem_splitFst_verts_of_not_mem hyo,
      mem_splitSnd_verts_of_not_mem hyH hyo⟩

/-- [s2:lemSEP] (ii) "if `u ∉ Dup` and `u ∈ V(H_0)`, then the nodes in which `u` lies are exactly
the ancestors of the unique leaf `Leaf_u` containing `u` (`Leaf_u` included), and `u ∉ N''_ν` at
every node `ν` on that path." -/
theorem sepII : EG.Spec.SEPiiStatement := by
  intro V _ H t ht u hu hud
  obtain ⟨L, hL, huL⟩ := exists_mem_leafAddrs_mem_verts t hu
  refine ⟨L, hL, huL, fun L' hL' huL' => eq_of_not_mem_dup hud hL' hL huL' huL,
    fun a ha => ⟨fun hua => prefix_of_mem_of_not_mem_dup hud hL huL ha hua,
      fun haL => (graphAtD_mono t H haL).1 huL⟩, fun a ha _ huN => ?_⟩
  obtain ⟨-, hN, hd⟩ := ht a ha
  have h1 : u ∈ (t.graphAtD H (a ++ [false])).verts := by
    rw [graphAtD_append_false ha]
    exact mem_splitFst_verts_of_mem_right hN huN
  have h2 : u ∈ (t.graphAtD H (a ++ [true])).verts := by
    rw [graphAtD_append_true ha]
    exact mem_splitSnd_verts_of_mem_right hN hd huN
  obtain ⟨b₁, hb₁, hab₁, hub₁⟩ :=
    exists_leaf_below t H (append_mem_nodeAddrs_of_mem_internalAddrs ha false) h1
  obtain ⟨b₂, hb₂, hab₂, hub₂⟩ :=
    exists_leaf_below t H (append_mem_nodeAddrs_of_mem_internalAddrs ha true) h2
  exact ne_of_prefix_children hab₁ hab₂ (eq_of_not_mem_dup hud hb₁ hb₂ hub₁ hub₂)

/-- [s2:lemSEP] (iii) "if `u ∉ Dup`, `u, h ∈ V(H_0)`, `h ∉ V(Leaf_u)`, and `ν^*` is the deepest
ancestor of `Leaf_u` in which `h` lies, then every deleted edge `hu'` with
`u' ∈ V(Leaf_u) \ Dup` is deleted at `ν^*`." -/
theorem sepIII : EG.Spec.SEPiiiStatement := by
  intro V _ H t _ u h L hL _ _ _ _ _ νs hνL hνh hmax u' hu' hd
  obtain ⟨hu'L, hu'd⟩ := Finset.mem_sdiff.1 hu'
  exact mem_delAt_deepest hL hνL hνh hmax hu'L hu'd hd

end EG
