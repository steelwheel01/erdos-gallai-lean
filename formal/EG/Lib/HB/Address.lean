module

public import EG.Lib.HB.Split

/-!
# Split trees: addresses, children, node decomposition (manuscript s2:lemSEP)

Unit P3A, proof round 1. Tree infrastructure for Lemma SEP, the thin cut, Lemma OV and
Lemma 14^τ (hazard H3 of `work/p2b/P3A.md`).

* `labelU`/`labelN`/`delAt` on `node` (simp lemmas);
* sums over `leafAddrs` / `internalAddrs` of a `node` (`sum_leafAddrs_node`,
  `sum_internalAddrs_node`) and the corresponding `filter`-card forms;
* the children of a non-leaf node are the generic split of its graph
  (`graphAtD_append_false`, `graphAtD_append_true`);
* prefixes: prefix closure of `nodeAddrs`, a strict prefix of a node is a non-leaf node, a leaf is
  a prefix of no other node, the graph at a node is a subgraph of the graph at every prefix
  (`graphAtD_mono`);
* every vertex of a node lies in a leaf below it (`exists_leaf_below`);
* `WF` of a `node` (`wf_node_iff`), `deleted` of a `node` (`deleted_node`),
  `leafMass` of a `node`.
-/

public section

namespace EG.HB

namespace STree

variable {V : Type*} [DecidableEq V]

section Labels

variable {W : Type*}

@[simp] theorem labelU_node_nil (p : Finset W × Finset W) (l r : STree W) :
    (STree.node p l r).labelU [] = p.1 := rfl

@[simp] theorem labelN_node_nil (p : Finset W × Finset W) (l r : STree W) :
    (STree.node p l r).labelN [] = p.2 := rfl

@[simp] theorem labelU_node_false (p : Finset W × Finset W) (l r : STree W) (a : Addr) :
    (STree.node p l r).labelU (false :: a) = l.labelU a := rfl

@[simp] theorem labelU_node_true (p : Finset W × Finset W) (l r : STree W) (a : Addr) :
    (STree.node p l r).labelU (true :: a) = r.labelU a := rfl

@[simp] theorem labelN_node_false (p : Finset W × Finset W) (l r : STree W) (a : Addr) :
    (STree.node p l r).labelN (false :: a) = l.labelN a := rfl

@[simp] theorem labelN_node_true (p : Finset W × Finset W) (l r : STree W) (a : Addr) :
    (STree.node p l r).labelN (true :: a) = r.labelN a := rfl

theorem labelU_of_labelAt {t : STree W} {a : Addr} {p : Finset W × Finset W}
    (h : t.labelAt a = some p) : t.labelU a = p.1 := by
  simp [labelU, h]

theorem labelN_of_labelAt {t : STree W} {a : Addr} {p : Finset W × Finset W}
    (h : t.labelAt a = some p) : t.labelN a = p.2 := by
  simp [labelN, h]

/-! ### Sums over the leaves and non-leaf nodes of a `node` -/

theorem disjoint_image_cons (A B : Finset Addr) :
    Disjoint (A.image (List.cons false)) (B.image (List.cons true)) := by
  rw [Finset.disjoint_left]
  intro x hA hB
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hA
  obtain ⟨b, -, h⟩ := Finset.mem_image.1 hB
  simp at h

theorem sum_leafAddrs_node {M : Type*} [AddCommMonoid M] (p : Finset W × Finset W)
    (l r : STree W) (f : Addr → M) :
    ∑ a ∈ (STree.node p l r).leafAddrs, f a =
      ∑ a ∈ l.leafAddrs, f (false :: a) + ∑ a ∈ r.leafAddrs, f (true :: a) := by
  rw [leafAddrs_node, Finset.sum_union (disjoint_image_cons _ _),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]

theorem sum_internalAddrs_node {M : Type*} [AddCommMonoid M] (p : Finset W × Finset W)
    (l r : STree W) (f : Addr → M) :
    ∑ a ∈ (STree.node p l r).internalAddrs, f a =
      f [] + (∑ a ∈ l.internalAddrs, f (false :: a) + ∑ a ∈ r.internalAddrs, f (true :: a)) := by
  rw [internalAddrs_node, Finset.sum_insert, Finset.sum_union (disjoint_image_cons _ _),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
  simp

theorem card_filter_leafAddrs_node (p : Finset W × Finset W) (l r : STree W)
    (P : Addr → Prop) [DecidablePred P] :
    ((STree.node p l r).leafAddrs.filter P).card =
      (l.leafAddrs.filter (fun a => P (false :: a))).card +
        (r.leafAddrs.filter (fun a => P (true :: a))).card := by
  simp only [Finset.card_filter]
  exact sum_leafAddrs_node p l r _

theorem card_filter_internalAddrs_node (p : Finset W × Finset W) (l r : STree W)
    (P : Addr → Prop) [DecidablePred P] :
    ((STree.node p l r).internalAddrs.filter P).card =
      (if P [] then 1 else 0) + ((l.internalAddrs.filter (fun a => P (false :: a))).card +
        (r.internalAddrs.filter (fun a => P (true :: a))).card) := by
  simp only [Finset.card_filter]
  exact sum_internalAddrs_node p l r _

/-! ### Prefixes -/

theorem mem_nodeAddrs_of_prefix {t : STree W} {a b : Addr} (hb : b ∈ t.nodeAddrs)
    (hab : a <+: b) : a ∈ t.nodeAddrs := by
  induction t generalizing a b with
  | nil =>
    simp only [nodeAddrs_nil, Finset.mem_singleton] at hb ⊢
    subst hb
    exact List.prefix_nil.1 hab
  | node p l r ihl ihr =>
    cases a with
    | nil => exact nil_mem_nodeAddrs _
    | cons c a =>
      cases b with
      | nil => exact absurd hab (by simp)
      | cons c' b =>
        obtain ⟨rfl, hab'⟩ := List.cons_prefix_cons.1 hab
        rw [mem_nodeAddrs_node_cons] at hb ⊢
        cases c
        · exact ihl hb hab'
        · exact ihr hb hab'

/-- A strict prefix of a node is a non-leaf node. -/
theorem mem_internalAddrs_of_prefix_of_ne {t : STree W} {a b : Addr} (hb : b ∈ t.nodeAddrs)
    (hab : a <+: b) (hne : a ≠ b) : a ∈ t.internalAddrs := by
  induction t generalizing a b with
  | nil =>
    simp only [nodeAddrs_nil, Finset.mem_singleton] at hb
    subst hb
    exact absurd (List.prefix_nil.1 hab) hne
  | node p l r ihl ihr =>
    cases a with
    | nil => simp [internalAddrs_node]
    | cons c a =>
      cases b with
      | nil => exact absurd hab (by simp)
      | cons c' b =>
        obtain ⟨rfl, hab'⟩ := List.cons_prefix_cons.1 hab
        rw [mem_nodeAddrs_node_cons] at hb
        rw [mem_internalAddrs_node_cons]
        have hne' : a ≠ b := fun h => hne (h ▸ rfl)
        cases c
        · exact ihl hb hab' hne'
        · exact ihr hb hab' hne'

/-- A leaf is a prefix of no other node. -/
theorem eq_of_mem_leafAddrs_of_prefix {t : STree W} {a b : Addr} (ha : a ∈ t.leafAddrs)
    (hb : b ∈ t.nodeAddrs) (hab : a <+: b) : a = b := by
  by_contra hne
  exact Finset.disjoint_left.1 (disjoint_leafAddrs_internalAddrs t) ha
    (mem_internalAddrs_of_prefix_of_ne hb hab hne)

theorem exists_append_singleton_prefix {a b : Addr} (hab : a <+: b) (hne : a ≠ b) :
    ∃ c : Bool, a ++ [c] <+: b := by
  obtain ⟨r, rfl⟩ := hab
  cases r with
  | nil => exact absurd (List.append_nil a).symm hne
  | cons c r => exact ⟨c, r, by simp⟩

theorem prefix_total {a₁ a₂ b : Addr} (h₁ : a₁ <+: b) (h₂ : a₂ <+: b) :
    a₁ <+: a₂ ∨ a₂ <+: a₁ := by
  rcases le_total a₁.length a₂.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le h₁ h₂ h)
  · exact Or.inr (List.prefix_of_prefix_length_le h₂ h₁ h)

/-- Two addresses extending the two different children of `a` are different. -/
theorem ne_of_prefix_children {a b₁ b₂ : Addr} (h₁ : a ++ [false] <+: b₁)
    (h₂ : a ++ [true] <+: b₂) : b₁ ≠ b₂ := by
  rintro rfl
  rcases prefix_total h₁ h₂ with h | h
  · have := List.IsPrefix.eq_of_length h (by simp)
    simp at this
  · have := List.IsPrefix.eq_of_length h (by simp)
    simp at this

end Labels

/-! ### Graphs at nodes -/

@[simp] theorem delAt_node_nil (p : Finset V × Finset V) (l r : STree V) (H : FGraph V) :
    (STree.node p l r).delAt H [] = splitDel H p.1 p.2 := rfl

@[simp] theorem delAt_node_false (p : Finset V × Finset V) (l r : STree V) (H : FGraph V)
    (a : Addr) :
    (STree.node p l r).delAt H (false :: a) = l.delAt (splitFst H p.1 p.2) a := rfl

@[simp] theorem delAt_node_true (p : Finset V × Finset V) (l r : STree V) (H : FGraph V)
    (a : Addr) :
    (STree.node p l r).delAt H (true :: a) = r.delAt (splitSnd H p.1 p.2) a := rfl

/-- The first child of a non-leaf node is `H_a[U'_a ∪ N''_a]`. -/
theorem graphAtD_append_false {t : STree V} {a : Addr} (ha : a ∈ t.internalAddrs)
    (H : FGraph V) :
    t.graphAtD H (a ++ [false]) = splitFst (t.graphAtD H a) (t.labelU a) (t.labelN a) := by
  induction t generalizing H a with
  | nil => simp at ha
  | node p l r ihl ihr =>
    cases a with
    | nil => simp
    | cons c a =>
      rw [mem_internalAddrs_node_cons] at ha
      cases c
      · simpa using ihl ha _
      · simpa using ihr ha _

/-- The second child of a non-leaf node is `H_a[V(H_a) \ U'_a] - E(H_a[N''_a])`. -/
theorem graphAtD_append_true {t : STree V} {a : Addr} (ha : a ∈ t.internalAddrs)
    (H : FGraph V) :
    t.graphAtD H (a ++ [true]) = splitSnd (t.graphAtD H a) (t.labelU a) (t.labelN a) := by
  induction t generalizing H a with
  | nil => simp at ha
  | node p l r ihl ihr =>
    cases a with
    | nil => simp
    | cons c a =>
      rw [mem_internalAddrs_node_cons] at ha
      cases c
      · simpa using ihl ha _
      · simpa using ihr ha _

theorem delAt_def' (t : STree V) (H : FGraph V) (a : Addr) :
    t.delAt H a = splitDel (t.graphAtD H a) (t.labelU a) (t.labelN a) := rfl

theorem delAt_subset (t : STree V) (H : FGraph V) (a : Addr) :
    t.delAt H a ⊆ (t.graphAtD H a).edges := splitDel_subset _ _ _

/-- [s2:lemSEP] (0') The graph at a node is a subgraph of the graph at each of its prefixes. -/
theorem graphAtD_mono (t : STree V) (H : FGraph V) {a b : Addr} (hab : a <+: b) :
    t.graphAtD H b ≤ t.graphAtD H a := by
  induction t generalizing H a b with
  | nil => simp
  | node p l r ihl ihr =>
    cases a with
    | nil => rw [graphAtD_root]; exact graphAtD_le _ _ _
    | cons c a =>
      cases b with
      | nil => exact absurd hab (by simp)
      | cons c' b =>
        obtain ⟨rfl, hab'⟩ := List.cons_prefix_cons.1 hab
        cases c
        · simpa using ihl _ hab'
        · simpa using ihr _ hab'

/-- [s2:lemSEP] (0) "Every vertex of a node lies in at least one leaf below it." -/
theorem exists_leaf_below (t : STree V) (H : FGraph V) {a : Addr} (ha : a ∈ t.nodeAddrs)
    {v : V} (hv : v ∈ (t.graphAtD H a).verts) :
    ∃ b ∈ t.leafAddrs, a <+: b ∧ v ∈ (t.graphAtD H b).verts := by
  induction t generalizing H a with
  | nil => exact ⟨[], by simp, by simp at ha; simp [ha], by simpa using hv⟩
  | node p l r ihl ihr =>
    cases a with
    | nil =>
      obtain ⟨b, hb, hvb⟩ := exists_mem_leafAddrs_mem_verts (STree.node p l r) (by simpa using hv)
      exact ⟨b, hb, List.nil_prefix, hvb⟩
    | cons c a =>
      rw [mem_nodeAddrs_node_cons] at ha
      cases c
      · obtain ⟨b, hb, hab, hvb⟩ := ihl _ ha (by simpa using hv)
        exact ⟨false :: b, by simpa using hb, List.cons_prefix_cons.2 ⟨rfl, hab⟩,
          by simpa using hvb⟩
      · obtain ⟨b, hb, hab, hvb⟩ := ihr _ ha (by simpa using hv)
        exact ⟨true :: b, by simpa using hb, List.cons_prefix_cons.2 ⟨rfl, hab⟩,
          by simpa using hvb⟩

/-! ### Node decomposition of `WF`, `deleted`, `leafMass` -/

theorem wf_node_iff (p : Finset V × Finset V) (l r : STree V) (H : FGraph V) :
    (STree.node p l r).WF H ↔
      (p.1 ⊆ H.verts ∧ p.2 ⊆ H.verts ∧ Disjoint p.1 p.2) ∧ l.WF (splitFst H p.1 p.2) ∧
        r.WF (splitSnd H p.1 p.2) := by
  constructor
  · intro h
    refine ⟨by simpa using h [] (by simp [internalAddrs_node]), fun a ha => ?_, fun a ha => ?_⟩
    · simpa using h (false :: a) (by simpa using ha)
    · simpa using h (true :: a) (by simpa using ha)
  · rintro ⟨h0, hl, hr⟩ a ha
    cases a with
    | nil => simpa using h0
    | cons c a =>
      rw [mem_internalAddrs_node_cons] at ha
      cases c
      · simpa using hl a ha
      · simpa using hr a ha

theorem deleted_node (p : Finset V × Finset V) (l r : STree V) (H : FGraph V) :
    (STree.node p l r).deleted H =
      splitDel H p.1 p.2 ∪ (l.deleted (splitFst H p.1 p.2) ∪ r.deleted (splitSnd H p.1 p.2)) := by
  ext e
  simp only [deleted, internalAddrs_node, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    rcases ha with rfl | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · exact Or.inl (by simpa using he)
    · exact Or.inr (Or.inl ⟨b, hb, by simpa using he⟩)
    · exact Or.inr (Or.inr ⟨b, hb, by simpa using he⟩)
  · rintro (he | ⟨b, hb, he⟩ | ⟨b, hb, he⟩)
    · exact ⟨[], Or.inl rfl, by simpa using he⟩
    · exact ⟨false :: b, Or.inr (Or.inl ⟨b, hb, rfl⟩), by simpa using he⟩
    · exact ⟨true :: b, Or.inr (Or.inr ⟨b, hb, rfl⟩), by simpa using he⟩

theorem leafMass_node (p : Finset V × Finset V) (l r : STree V) (H : FGraph V) :
    (STree.node p l r).leafMass H =
      l.leafMass (splitFst H p.1 p.2) + r.leafMass (splitSnd H p.1 p.2) := by
  unfold leafMass
  rw [sum_leafAddrs_node]
  simp

/-- The label of a non-leaf node lies in its graph (`WF`). -/
theorem labelU_subset {t : STree V} {H : FGraph V} (ht : t.WF H) {a : Addr}
    (ha : a ∈ t.internalAddrs) : t.labelU a ⊆ (t.graphAtD H a).verts := (ht a ha).1

theorem labelN_subset {t : STree V} {H : FGraph V} (ht : t.WF H) {a : Addr}
    (ha : a ∈ t.internalAddrs) : t.labelN a ⊆ (t.graphAtD H a).verts := (ht a ha).2.1

theorem labelN_subset_root {t : STree V} {H : FGraph V} (ht : t.WF H) {a : Addr}
    (ha : a ∈ t.internalAddrs) : t.labelN a ⊆ H.verts :=
  (labelN_subset ht ha).trans (graphAtD_verts_subset t H a)

theorem labelU_subset_root {t : STree V} {H : FGraph V} (ht : t.WF H) {a : Addr}
    (ha : a ∈ t.internalAddrs) : t.labelU a ⊆ H.verts :=
  (labelU_subset ht ha).trans (graphAtD_verts_subset t H a)

/-- [s2:lemSEP] (0) "the total size of the leaves is `|H_0| + Σ_ν |N''_ν|`". -/
theorem leafMass_eq (t : STree V) {H : FGraph V} (ht : t.WF H) :
    t.leafMass H = H.card + ∑ a ∈ t.internalAddrs, (t.labelN a).card := by
  induction t generalizing H with
  | nil => simp
  | node p l r ihl ihr =>
    obtain ⟨⟨hU, hN, hd⟩, hl, hr⟩ := (wf_node_iff p l r H).1 ht
    rw [leafMass_node, ihl hl, ihr hr, sum_internalAddrs_node]
    simp only [labelN_node_nil, labelN_node_false, labelN_node_true]
    have := card_splitFst_add_card_splitSnd hU hN hd
    omega

end STree

end EG.HB
