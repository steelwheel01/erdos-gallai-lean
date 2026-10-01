module

public import EG.Defs.HB.SplitTree
public import EG.Lib.Found.Graph

/-!
# Witnesses, splits and split trees: basic API
(companion of `EG.Defs.HB.Witness` and `EG.Defs.HB.SplitTree`)

* `EG.HB.not_isExpander_iff_exists_isWitness`: `IsWitness` is literally the negated body of
  `IsExpander` (the sentence "Since `H` is not an `(ε,s)`-expander, a witness exists" of
  [s2:defWitness], and its converse);
* vertex sets of the generic split (`splitFst_verts`, `splitSnd_verts`), `splitDel ⊆ E(H)`,
  children are subgraphs;
* structural (`simp`) lemmas for `labelAt`, `graphAtD`, `nodeAddrs`, `leafAddrs`,
  `internalAddrs`, `graft`, `leafPrefix` on `nil` / `node`;
* every node graph is a subgraph of the root (`STree.graphAtD_le`), so `Dup ⊆ V(H₀)`, leaf
  vertex sets lie in `V(H₀)`;
* the one-leaf tree: `STree.isTauRun_nil_iff`, `STree.isS0Rec_nil`, `STree.stopsAt_nil_iff`;
* grafting the empty trees changes nothing (`STree.graft_nil_fun`);
* graft API (blueprint HB-GRAFT): the leaves of `t.graft f` are the `a ++ b`
  (`mem_leafAddrs_graft`); graphs and labels below a leaf `a` of `t` are those of `f a` rooted at
  the leaf graph of `t` at `a` (`graphAtD_graft_append`, `labelAt_graft_append`); graphs and
  labels at the nodes of `t` are unchanged (`graphAtD_graft_of_mem_nodeAddrs`,
  `labelAt_graft_of_mem_internalAddrs`); `leafPrefix` recovers the leaf of `t` (the piece);
* graft API, part 2: non-leaf nodes of the graft (`mem_internalAddrs_graft`), labels
  (`labelU_graft_append`, …), `wf_graft`, `ovHyp_graft`, deleted edges (`deleted_graft`),
  an `s = 0` recursion deletes nothing (`deleted_eq_empty_of_isS0Rec`), leaves cover the root
  (`exists_mem_leafAddrs_mem_verts`), `Dup` in the graft (`mem_dup_iff_exists`,
  `dup_subset_dup_graft`, `dup_subset_dup_graft_of_mem_leafAddrs`);
* `EG.FGraph.card_nbrs_inter_eq_eBetween`: `|N_X(x) ∩ W| = e_X({x}, W)`.

Casts. `STree.IsTauRun ε (s : ℕ) τ` uses the witness parameter `(s : ℝ)` (a cast): a witness
lemma stated with a literal, e.g. `IsWitness K ε 1 U F`, is used inside `IsTauRun ε 1 τ` after
`rw [Nat.cast_one]` (or `Nat.cast_ofNat` for numerals `≥ 2`; `isWitness_natCast_iff`).
-/

public section

namespace EG.HB

variable {V : Type*} [DecidableEq V]

/-! ### Witnesses -/

/-- The cast of a natural witness parameter (`IsTauRun` takes `s : ℕ`): `(n : ℝ)` versus a
real parameter equal to it. -/
theorem isWitness_natCast_iff (H : FGraph V) (ε : ℝ) {n : ℕ} {s : ℝ} (hs : (n : ℝ) = s)
    (U : Finset V) (F : Finset (Sym2 V)) : IsWitness H ε n U F ↔ IsWitness H ε s U F := by
  rw [hs]

/-- [s2:defWitness] "Since `H` is not an `(ε,s)`-expander, a witness exists", and conversely a
witness certifies that `H` is not an `(ε,s)`-expander. -/
theorem not_isExpander_iff_exists_isWitness (H : FGraph V) (ε s : ℝ) :
    ¬ H.IsExpander ε s ↔ ∃ U F, IsWitness H ε s U F := by
  unfold FGraph.IsExpander IsWitness
  push Not
  rfl

theorem witN_subset_verts (H : FGraph V) (U : Finset V) (F : Finset (Sym2 V)) :
    witN H U F ⊆ H.verts := (H.deleteEdges F).nbrSet_subset_verts U

theorem disjoint_witN (H : FGraph V) (U : Finset V) (F : Finset (Sym2 V)) :
    Disjoint U (witN H U F) := (H.deleteEdges F).disjoint_nbrSet U

theorem witF0_subset (H : FGraph V) (U N : Finset V) : witF0 H U N ⊆ H.edges :=
  H.edgesBetween_subset _ _

/-! ### The generic split -/

@[simp] theorem splitFst_verts (H : FGraph V) (U' N'' : Finset V) :
    (splitFst H U' N'').verts = H.verts ∩ (U' ∪ N'') := rfl

@[simp] theorem splitSnd_verts (H : FGraph V) (U' N'' : Finset V) :
    (splitSnd H U' N'').verts = H.verts \ U' := by
  simp [splitSnd, FGraph.deleteEdges_verts, FGraph.induce_verts]

theorem splitFst_le (H : FGraph V) (U' N'' : Finset V) : splitFst H U' N'' ≤ H :=
  H.induce_le _

theorem splitSnd_le (H : FGraph V) (U' N'' : Finset V) : splitSnd H U' N'' ≤ H :=
  le_trans ((H.induce (H.verts \ U')).deleteEdges_le _) (H.induce_le _)

theorem splitDel_subset (H : FGraph V) (U' N'' : Finset V) : splitDel H U' N'' ⊆ H.edges :=
  H.edgesBetween_subset _ _

theorem tauU1_subset (H : FGraph V) (U N : Finset V) (τ : ℝ) : tauU1 H U N τ ⊆ U :=
  Finset.sdiff_subset

theorem tauHout_subset (H : FGraph V) (U N : Finset V) (τ : ℝ) : tauHout H U N τ ⊆ U :=
  Finset.filter_subset _ _

/-! ### Split trees -/

namespace STree

section Structure

variable {W : Type*}

@[simp] theorem labelAt_nil (a : Addr) : (STree.nil : STree W).labelAt a = none := by
  cases a <;> rfl

@[simp] theorem labelAt_node_nil (p : Finset W × Finset W) (l r : STree W) :
    (STree.node p l r : STree W).labelAt [] = some p := rfl

@[simp] theorem labelAt_node_false (p : Finset W × Finset W) (l r : STree W) (a : Addr) :
    (STree.node p l r : STree W).labelAt (false :: a) = l.labelAt a := rfl

@[simp] theorem labelAt_node_true (p : Finset W × Finset W) (l r : STree W) (a : Addr) :
    (STree.node p l r : STree W).labelAt (true :: a) = r.labelAt a := rfl

@[simp] theorem labelU_nil (a : Addr) : (STree.nil : STree W).labelU a = ∅ := by
  simp [labelU]

@[simp] theorem labelN_nil (a : Addr) : (STree.nil : STree W).labelN a = ∅ := by
  simp [labelN]

@[simp] theorem nodeAddrs_nil : (STree.nil : STree W).nodeAddrs = {[]} := rfl

@[simp] theorem leafAddrs_nil : (STree.nil : STree W).leafAddrs = {[]} := rfl

@[simp] theorem internalAddrs_nil : (STree.nil : STree W).internalAddrs = ∅ := rfl

theorem nodeAddrs_node (p : Finset W × Finset W) (l r : STree W) :
    (STree.node p l r : STree W).nodeAddrs =
      insert [] (l.nodeAddrs.image (List.cons false) ∪ r.nodeAddrs.image (List.cons true)) :=
  rfl

theorem leafAddrs_node (p : Finset W × Finset W) (l r : STree W) :
    (STree.node p l r : STree W).leafAddrs =
      l.leafAddrs.image (List.cons false) ∪ r.leafAddrs.image (List.cons true) := rfl

theorem internalAddrs_node (p : Finset W × Finset W) (l r : STree W) :
    (STree.node p l r : STree W).internalAddrs =
      insert [] (l.internalAddrs.image (List.cons false) ∪
        r.internalAddrs.image (List.cons true)) := rfl

@[simp] theorem mem_leafAddrs_node_nil (p : Finset W × Finset W) (l r : STree W) :
    [] ∉ (STree.node p l r : STree W).leafAddrs := by
  simp [leafAddrs_node]

@[simp] theorem mem_leafAddrs_node_cons (p : Finset W × Finset W) (l r : STree W) (b : Bool)
    (a : Addr) :
    b :: a ∈ (STree.node p l r : STree W).leafAddrs ↔
      a ∈ (if b then r else l).leafAddrs := by
  cases b <;> simp [leafAddrs_node]

@[simp] theorem mem_internalAddrs_node_cons (p : Finset W × Finset W) (l r : STree W) (b : Bool)
    (a : Addr) :
    b :: a ∈ (STree.node p l r : STree W).internalAddrs ↔
      a ∈ (if b then r else l).internalAddrs := by
  cases b <;> simp [internalAddrs_node]

@[simp] theorem mem_nodeAddrs_node_cons (p : Finset W × Finset W) (l r : STree W) (b : Bool)
    (a : Addr) :
    b :: a ∈ (STree.node p l r : STree W).nodeAddrs ↔
      a ∈ (if b then r else l).nodeAddrs := by
  cases b <;> simp [nodeAddrs_node]

theorem nil_mem_nodeAddrs (t : STree W) : [] ∈ t.nodeAddrs := by
  cases t <;> simp [nodeAddrs_node]

/-- Leaves and non-leaf nodes are the nodes. -/
theorem nodeAddrs_eq_union (t : STree W) : t.nodeAddrs = t.leafAddrs ∪ t.internalAddrs := by
  induction t with
  | nil => simp
  | node p l r ihl ihr =>
    rw [nodeAddrs_node, leafAddrs_node, internalAddrs_node, ihl, ihr]
    ext a
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (h | ⟨b, hb | hb, rfl⟩ | ⟨b, hb | hb, rfl⟩) <;> simp_all
    · rintro ((⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩) | h | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩) <;> simp_all

theorem leafAddrs_subset_nodeAddrs (t : STree W) : t.leafAddrs ⊆ t.nodeAddrs := by
  rw [nodeAddrs_eq_union]; exact Finset.subset_union_left

theorem internalAddrs_subset_nodeAddrs (t : STree W) : t.internalAddrs ⊆ t.nodeAddrs := by
  rw [nodeAddrs_eq_union]; exact Finset.subset_union_right

/-- No address is both a leaf and a non-leaf node. -/
theorem disjoint_leafAddrs_internalAddrs (t : STree W) :
    Disjoint t.leafAddrs t.internalAddrs := by
  induction t with
  | nil => simp
  | node p l r ihl ihr =>
    rw [Finset.disjoint_left]
    intro a ha hi
    cases a with
    | nil => simp at ha
    | cons b a =>
      rw [mem_leafAddrs_node_cons] at ha
      rw [mem_internalAddrs_node_cons] at hi
      cases b
      · exact Finset.disjoint_left.1 ihl ha hi
      · exact Finset.disjoint_left.1 ihr ha hi

/-- A non-leaf node carries a label. -/
theorem labelAt_isSome_of_mem_internalAddrs {t : STree W} {a : Addr}
    (ha : a ∈ t.internalAddrs) : (t.labelAt a).isSome := by
  induction t generalizing a with
  | nil => simp at ha
  | node p l r ihl ihr =>
    cases a with
    | nil => simp
    | cons b a =>
      rw [mem_internalAddrs_node_cons] at ha
      cases b
      · exact ihl ha
      · exact ihr ha

@[simp] theorem graft_nil (f : Addr → STree W) : (STree.nil : STree W).graft f = f [] :=
  rfl

theorem graft_node (p : Finset W × Finset W) (l r : STree W) (f : Addr → STree W) :
    (STree.node p l r : STree W).graft f =
      .node p (l.graft (fun a => f (false :: a))) (r.graft (fun a => f (true :: a))) := rfl

/-- Grafting only leaves changes nothing. -/
@[simp] theorem graft_nil_fun (t : STree W) : t.graft (fun _ => .nil) = t := by
  induction t with
  | nil => rfl
  | node p l r ihl ihr => simp only [graft_node, ihl, ihr]

@[simp] theorem leafPrefix_nil (a : Addr) : (STree.nil : STree W).leafPrefix a = [] := by
  cases a <;> rfl

/-- The leaf prefix of an address of the grafted tree below the leaf `a` is `a`. -/
theorem leafPrefix_append {t : STree W} {a : Addr} (ha : a ∈ t.leafAddrs) (b : Addr) :
    t.leafPrefix (a ++ b) = a := by
  induction t generalizing a with
  | nil => simp at ha; simp [ha]
  | node p l r ihl ihr =>
    cases a with
    | nil => simp at ha
    | cons c a =>
      rw [mem_leafAddrs_node_cons] at ha
      cases c
      · simp only [List.cons_append, leafPrefix, ihl ha]
      · simp only [List.cons_append, leafPrefix, ihr ha]

end Structure

@[simp] theorem graphAtD_nil (H : FGraph V) (a : Addr) :
    (STree.nil : STree V).graphAtD H a = H := by
  cases a <;> rfl

@[simp] theorem graphAtD_node_nil (p : Finset V × Finset V) (l r : STree V) (H : FGraph V) :
    (STree.node p l r : STree V).graphAtD H [] = H := rfl

@[simp] theorem graphAtD_node_false (p : Finset V × Finset V) (l r : STree V) (H : FGraph V)
    (a : Addr) :
    (STree.node p l r : STree V).graphAtD H (false :: a) =
      l.graphAtD (splitFst H p.1 p.2) a := rfl

@[simp] theorem graphAtD_node_true (p : Finset V × Finset V) (l r : STree V) (H : FGraph V)
    (a : Addr) :
    (STree.node p l r : STree V).graphAtD H (true :: a) =
      r.graphAtD (splitSnd H p.1 p.2) a := rfl

@[simp] theorem graphAtD_root (t : STree V) (H : FGraph V) : t.graphAtD H [] = H := by
  cases t <;> rfl

/-- [s2:lemSEP] (implicit monotonicity (0')) Every node graph is a subgraph of the root graph. -/
theorem graphAtD_le (t : STree V) (H : FGraph V) (a : Addr) : t.graphAtD H a ≤ H := by
  induction t generalizing H a with
  | nil => simp
  | node p l r ihl ihr =>
    cases a with
    | nil => simp
    | cons b a =>
      cases b
      · exact le_trans (ihl _ _) (splitFst_le _ _ _)
      · exact le_trans (ihr _ _) (splitSnd_le _ _ _)

theorem graphAtD_verts_subset (t : STree V) (H : FGraph V) (a : Addr) :
    (t.graphAtD H a).verts ⊆ H.verts := (graphAtD_le t H a).1

theorem graphAtD_edges_subset (t : STree V) (H : FGraph V) (a : Addr) :
    (t.graphAtD H a).edges ⊆ H.edges := (graphAtD_le t H a).2

theorem dup_subset (t : STree V) (H : FGraph V) : t.dup H ⊆ H.verts := Finset.filter_subset _ _

theorem mem_dup {t : STree V} {H : FGraph V} {v : V} :
    v ∈ t.dup H ↔ v ∈ H.verts ∧
      2 ≤ (t.leafAddrs.filter (fun a => v ∈ (t.graphAtD H a).verts)).card := Finset.mem_filter

theorem deleted_subset (t : STree V) (H : FGraph V) : t.deleted H ⊆ H.edges := by
  intro e he
  simp only [deleted, Finset.mem_biUnion] at he
  obtain ⟨a, -, hea⟩ := he
  exact graphAtD_edges_subset t H a (splitDel_subset _ _ _ hea)

@[simp] theorem deleted_nil (H : FGraph V) : (STree.nil : STree V).deleted H = ∅ := rfl

@[simp] theorem leafMass_nil (H : FGraph V) :
    (STree.nil : STree V).leafMass H = H.card := by
  simp [leafMass]

@[simp] theorem dup_nil (H : FGraph V) : (STree.nil : STree V).dup H = ∅ := by
  ext v
  simp only [dup, leafAddrs_nil, graphAtD_nil, Finset.mem_filter, Finset.notMem_empty,
    iff_false, not_and, not_le]
  intro _
  calc _ ≤ ({[]} : Finset Addr).card := Finset.card_filter_le _ _
    _ < 2 := by simp

theorem wf_nil (H : FGraph V) : (STree.nil : STree V).WF H := by
  simp [WF]

@[simp] theorem stopsAt_nil_iff (H : FGraph V) (P : FGraph V → Prop) :
    (STree.nil : STree V).StopsAt H P ↔ P H := by
  simp [StopsAt]

theorem isS0Rec_nil (ε : ℝ) (H : FGraph V) : (STree.nil : STree V).IsS0Rec ε H :=
  ⟨wf_nil H, by simp⟩

/-- The one-leaf tree is a `τ`-run iff the root graph is an `(ε,s)`-expander. -/
theorem isTauRun_nil_iff (ε : ℝ) (s : ℕ) (τ : ℝ) (H : FGraph V) :
    (STree.nil : STree V).IsTauRun ε s τ H ↔ H.IsExpander ε s := by
  simp [IsTauRun, wf_nil]

/-! ### Graft API (the two-level recursion) -/

/-- The graph of the grafted tree at `a ++ b`, for a leaf `a` of `t`, is the graph of `f a` at
`b`, rooted at the leaf graph of `t` at `a`. -/
theorem graphAtD_graft_append {t : STree V} {a : Addr} (ha : a ∈ t.leafAddrs)
    (f : Addr → STree V) (H : FGraph V) (b : Addr) :
    (t.graft f).graphAtD H (a ++ b) = (f a).graphAtD (t.graphAtD H a) b := by
  induction t generalizing H a f with
  | nil =>
    simp only [leafAddrs_nil, Finset.mem_singleton] at ha
    subst ha
    simp
  | node p l r ihl ihr =>
    cases a with
    | nil => simp at ha
    | cons c a =>
      rw [mem_leafAddrs_node_cons] at ha
      cases c
      · simp only [List.cons_append, graft_node, graphAtD_node_false]
        exact ihl ha _ _
      · simp only [List.cons_append, graft_node, graphAtD_node_true]
        exact ihr ha _ _

omit [DecidableEq V] in
/-- The labels of the grafted tree below a leaf `a` of `t` are those of `f a`. -/
theorem labelAt_graft_append {t : STree V} {a : Addr} (ha : a ∈ t.leafAddrs)
    (f : Addr → STree V) (b : Addr) :
    (t.graft f).labelAt (a ++ b) = (f a).labelAt b := by
  induction t generalizing a f with
  | nil =>
    simp only [leafAddrs_nil, Finset.mem_singleton] at ha
    subst ha
    simp
  | node p l r ihl ihr =>
    cases a with
    | nil => simp at ha
    | cons c a =>
      rw [mem_leafAddrs_node_cons] at ha
      cases c
      · simp only [List.cons_append, graft_node, labelAt_node_false]
        exact ihl ha _
      · simp only [List.cons_append, graft_node, labelAt_node_true]
        exact ihr ha _

omit [DecidableEq V] in
/-- Grafting does not change the non-leaf nodes of `t`: labels. -/
theorem labelAt_graft_of_mem_internalAddrs {t : STree V} {a : Addr}
    (ha : a ∈ t.internalAddrs) (f : Addr → STree V) :
    (t.graft f).labelAt a = t.labelAt a := by
  induction t generalizing a f with
  | nil => simp at ha
  | node p l r ihl ihr =>
    cases a with
    | nil => rfl
    | cons c a =>
      rw [mem_internalAddrs_node_cons] at ha
      cases c
      · simp only [graft_node, labelAt_node_false]
        exact ihl ha _
      · simp only [graft_node, labelAt_node_true]
        exact ihr ha _

/-- Grafting does not change the graphs at the nodes of `t`. -/
theorem graphAtD_graft_of_mem_nodeAddrs {t : STree V} {a : Addr} (ha : a ∈ t.nodeAddrs)
    (f : Addr → STree V) (H : FGraph V) :
    (t.graft f).graphAtD H a = t.graphAtD H a := by
  induction t generalizing H a f with
  | nil =>
    simp only [nodeAddrs_nil, Finset.mem_singleton] at ha
    subst ha
    simp
  | node p l r ihl ihr =>
    cases a with
    | nil => rfl
    | cons c a =>
      rw [mem_nodeAddrs_node_cons] at ha
      cases c
      · simp only [graft_node, graphAtD_node_false]
        exact ihl ha _ _
      · simp only [graft_node, graphAtD_node_true]
        exact ihr ha _ _

omit [DecidableEq V] in
/-- The leaves of the grafted tree: `a ++ b` for a leaf `a` of `t` and a leaf `b` of `f a`. -/
theorem mem_leafAddrs_graft {t : STree V} {f : Addr → STree V} {x : Addr} :
    x ∈ (t.graft f).leafAddrs ↔ ∃ a ∈ t.leafAddrs, ∃ b ∈ (f a).leafAddrs, x = a ++ b := by
  induction t generalizing f x with
  | nil => simp
  | node p l r ihl ihr =>
    rw [graft_node]
    cases x with
    | nil =>
      simp only [mem_leafAddrs_node_nil, false_iff, not_exists, not_and]
      intro a ha b _ h
      cases a with
      | nil => simp at ha
      | cons _ _ => simp at h
    | cons c x =>
      rw [mem_leafAddrs_node_cons]
      constructor
      · intro h
        cases c
        · obtain ⟨a, ha, b, hb, rfl⟩ := ihl.1 h
          exact ⟨false :: a, by simpa using ha, b, hb, rfl⟩
        · obtain ⟨a, ha, b, hb, rfl⟩ := ihr.1 h
          exact ⟨true :: a, by simpa using ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, h⟩
        cases a with
        | nil => simp at ha
        | cons c' a =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [mem_leafAddrs_node_cons] at ha
          cases c
          · simp only [Bool.false_eq_true, if_false] at ha ⊢
            exact ihl.2 ⟨a, ha, b, hb, rfl⟩
          · simp only [if_true] at ha ⊢
            exact ihr.2 ⟨a, ha, b, hb, rfl⟩

omit [DecidableEq V] in
/-- The leaf prefix of a leaf of the grafted tree is a leaf of `t`. -/
theorem leafPrefix_mem_of_mem_leafAddrs_graft {t : STree V} {f : Addr → STree V} {x : Addr}
    (hx : x ∈ (t.graft f).leafAddrs) : t.leafPrefix x ∈ t.leafAddrs := by
  obtain ⟨a, ha, b, -, rfl⟩ := mem_leafAddrs_graft.1 hx
  rw [leafPrefix_append ha]
  exact ha

/-! ### Graft API, part 2 (fix round 2 of `work/p2d/hb.md`): non-leaf nodes and labels of the
graft, `WF`, `OVHyp`, deleted edges, `Dup`, leaf cover -/

omit [DecidableEq V] in
/-- The non-leaf nodes of the grafted tree: those of `t`, and `a ++ b` for a leaf `a` of `t` and
a non-leaf node `b` of `f a`. -/
theorem mem_internalAddrs_graft {t : STree V} {f : Addr → STree V} {x : Addr} :
    x ∈ (t.graft f).internalAddrs ↔
      x ∈ t.internalAddrs ∨ ∃ a ∈ t.leafAddrs, ∃ b ∈ (f a).internalAddrs, x = a ++ b := by
  induction t generalizing f x with
  | nil => simp
  | node p l r ihl ihr =>
    rw [graft_node]
    cases x with
    | nil => simp [internalAddrs_node]
    | cons c x =>
      rw [mem_internalAddrs_node_cons, mem_internalAddrs_node_cons]
      cases c
      · simp only [Bool.false_eq_true, if_false]
        rw [ihl]
        constructor
        · rintro (h | ⟨a, ha, b, hb, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨false :: a, by simpa using ha, b, hb, rfl⟩
        · rintro (h | ⟨a, ha, b, hb, h⟩)
          · exact Or.inl h
          · cases a with
            | nil => simp at ha
            | cons c' a =>
              simp only [List.cons_append, List.cons.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨a, by simpa using ha, b, hb, rfl⟩
      · simp only [if_true]
        rw [ihr]
        constructor
        · rintro (h | ⟨a, ha, b, hb, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨true :: a, by simpa using ha, b, hb, rfl⟩
        · rintro (h | ⟨a, ha, b, hb, h⟩)
          · exact Or.inl h
          · cases a with
            | nil => simp at ha
            | cons c' a =>
              simp only [List.cons_append, List.cons.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Or.inr ⟨a, by simpa using ha, b, hb, rfl⟩

omit [DecidableEq V] in
/-- Both children of a non-leaf node are nodes. -/
theorem append_mem_nodeAddrs_of_mem_internalAddrs {t : STree V} {a : Addr}
    (ha : a ∈ t.internalAddrs) (b : Bool) : a ++ [b] ∈ t.nodeAddrs := by
  induction t generalizing a with
  | nil => simp at ha
  | node p l r ihl ihr =>
    cases a with
    | nil => cases b <;> simp [nil_mem_nodeAddrs]
    | cons c a =>
      rw [mem_internalAddrs_node_cons] at ha
      rw [List.cons_append, mem_nodeAddrs_node_cons]
      cases c
      · exact ihl ha
      · exact ihr ha

omit [DecidableEq V] in
theorem labelU_graft_of_mem_internalAddrs {t : STree V} {a : Addr} (ha : a ∈ t.internalAddrs)
    (f : Addr → STree V) : (t.graft f).labelU a = t.labelU a := by
  simp only [labelU, labelAt_graft_of_mem_internalAddrs ha]

omit [DecidableEq V] in
theorem labelN_graft_of_mem_internalAddrs {t : STree V} {a : Addr} (ha : a ∈ t.internalAddrs)
    (f : Addr → STree V) : (t.graft f).labelN a = t.labelN a := by
  simp only [labelN, labelAt_graft_of_mem_internalAddrs ha]

omit [DecidableEq V] in
theorem labelU_graft_append {t : STree V} {a : Addr} (ha : a ∈ t.leafAddrs)
    (f : Addr → STree V) (b : Addr) : (t.graft f).labelU (a ++ b) = (f a).labelU b := by
  simp only [labelU, labelAt_graft_append ha]

omit [DecidableEq V] in
theorem labelN_graft_append {t : STree V} {a : Addr} (ha : a ∈ t.leafAddrs)
    (f : Addr → STree V) (b : Addr) : (t.graft f).labelN (a ++ b) = (f a).labelN b := by
  simp only [labelN, labelAt_graft_append ha]

/-- The graft of split recursions is a split recursion. -/
theorem wf_graft {t : STree V} {f : Addr → STree V} {H : FGraph V} (ht : t.WF H)
    (hf : ∀ a ∈ t.leafAddrs, (f a).WF (t.graphAtD H a)) : (t.graft f).WF H := by
  intro x hx
  rcases mem_internalAddrs_graft.1 hx with hx' | ⟨a, ha, b, hb, rfl⟩
  · rw [labelU_graft_of_mem_internalAddrs hx', labelN_graft_of_mem_internalAddrs hx',
      graphAtD_graft_of_mem_nodeAddrs (internalAddrs_subset_nodeAddrs t hx')]
    exact ht x hx'
  · rw [labelU_graft_append ha, labelN_graft_append ha, graphAtD_graft_append ha]
    exact hf a ha b hb

/-- The hypotheses of Lemma OV pass to the graft: at the nodes of `t` they are those of `t`
(both children of a non-leaf node of `t` are nodes of `t`), below a leaf `a` those of `f a`. -/
theorem ovHyp_graft {ε c : ℝ} {t : STree V} {f : Addr → STree V} {H : FGraph V}
    (ht : t.OVHyp ε c H) (hf : ∀ a ∈ t.leafAddrs, (f a).OVHyp ε c (t.graphAtD H a)) :
    (t.graft f).OVHyp ε c H := by
  refine ⟨wf_graft ht.1 fun a ha => (hf a ha).1, fun x hx => ?_⟩
  rcases mem_internalAddrs_graft.1 hx with hx' | ⟨a, ha, b, hb, rfl⟩
  · rw [graphAtD_graft_of_mem_nodeAddrs (internalAddrs_subset_nodeAddrs t hx'),
      graphAtD_graft_of_mem_nodeAddrs (append_mem_nodeAddrs_of_mem_internalAddrs hx' false),
      labelU_graft_of_mem_internalAddrs hx', labelN_graft_of_mem_internalAddrs hx']
    exact ht.2 x hx'
  · rw [List.append_assoc, graphAtD_graft_append ha, graphAtD_graft_append ha,
      labelU_graft_append ha, labelN_graft_append ha]
    exact (hf a ha).2 b hb

theorem delAt_graft_of_mem_internalAddrs {t : STree V} {a : Addr} (ha : a ∈ t.internalAddrs)
    (f : Addr → STree V) (H : FGraph V) : (t.graft f).delAt H a = t.delAt H a := by
  simp only [delAt, labelU_graft_of_mem_internalAddrs ha, labelN_graft_of_mem_internalAddrs ha,
    graphAtD_graft_of_mem_nodeAddrs (internalAddrs_subset_nodeAddrs t ha)]

theorem delAt_graft_append {t : STree V} {a : Addr} (ha : a ∈ t.leafAddrs)
    (f : Addr → STree V) (H : FGraph V) (b : Addr) :
    (t.graft f).delAt H (a ++ b) = (f a).delAt (t.graphAtD H a) b := by
  simp only [delAt, labelU_graft_append ha, labelN_graft_append ha, graphAtD_graft_append ha]

/-- The deleted edges of the graft: those of `t` and those of the grafted trees. -/
theorem deleted_graft (t : STree V) (f : Addr → STree V) (H : FGraph V) :
    (t.graft f).deleted H =
      t.deleted H ∪ t.leafAddrs.biUnion (fun a => (f a).deleted (t.graphAtD H a)) := by
  ext e
  simp only [deleted, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx, he⟩
    rcases mem_internalAddrs_graft.1 hx with hx' | ⟨a, ha, b, hb, rfl⟩
    · exact Or.inl ⟨x, hx', by rwa [delAt_graft_of_mem_internalAddrs hx'] at he⟩
    · exact Or.inr ⟨a, ha, b, hb, by rwa [delAt_graft_append ha] at he⟩
  · rintro (⟨x, hx, he⟩ | ⟨a, ha, b, hb, he⟩)
    · exact ⟨x, mem_internalAddrs_graft.2 (Or.inl hx),
        by rwa [delAt_graft_of_mem_internalAddrs hx]⟩
    · exact ⟨a ++ b, mem_internalAddrs_graft.2 (Or.inr ⟨a, ha, b, hb, rfl⟩),
        by rwa [delAt_graft_append ha]⟩

/-- An `s = 0` recursion deletes nothing: at a non-leaf node `N''_ν = Nbr_{H_ν}(U'_ν)`, so no
edge leaves `U'_ν ∪ N''_ν` from `U'_ν`. -/
theorem delAt_eq_empty_of_isS0Rec {ε : ℝ} {t : STree V} {H : FGraph V} (ht : t.IsS0Rec ε H)
    {a : Addr} (ha : a ∈ t.internalAddrs) : t.delAt H a = ∅ := by
  obtain ⟨U, F, -, hlab⟩ := ht.2 a ha
  have hU : t.labelU a = U := by simp [labelU, hlab]
  have hN : t.labelN a = (t.graphAtD H a).nbrSet U := by simp [labelN, hlab]
  rw [delAt, hU, hN]
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  simp only [splitDel, FGraph.mem_edgesBetween] at he
  obtain ⟨he, u, hu, v, hv, rfl⟩ := he
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hv
  exact hv.2.2 (FGraph.mem_nbrSet.2 ⟨hv.1, hv.2.1, u, hu, he⟩)

theorem deleted_eq_empty_of_isS0Rec {ε : ℝ} {t : STree V} {H : FGraph V} (ht : t.IsS0Rec ε H) :
    t.deleted H = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  simp only [deleted, Finset.mem_biUnion] at he
  obtain ⟨a, ha, he⟩ := he
  rw [delAt_eq_empty_of_isS0Rec ht ha] at he
  simp at he

/-- The leaves cover the root: every vertex of `H₀` lies in some leaf (`V(H_{ν_1}) ∪ V(H_{ν_2})
= V(H_ν)`, since `U'_ν ⊆ U'_ν ∪ N''_ν`). -/
theorem exists_mem_leafAddrs_mem_verts (t : STree V) {H : FGraph V} {v : V} (hv : v ∈ H.verts) :
    ∃ a ∈ t.leafAddrs, v ∈ (t.graphAtD H a).verts := by
  induction t generalizing H with
  | nil => exact ⟨[], by simp, by simpa using hv⟩
  | node p l r ihl ihr =>
    by_cases hU : v ∈ p.1
    · obtain ⟨a, ha, hva⟩ := ihl (H := splitFst H p.1 p.2) (by simp [hv, hU])
      exact ⟨false :: a, by simpa using ha, by simpa using hva⟩
    · obtain ⟨a, ha, hva⟩ := ihr (H := splitSnd H p.1 p.2) (by simp [hv, hU])
      exact ⟨true :: a, by simpa using ha, by simpa using hva⟩

/-- `v ∈ Dup` iff `v` lies in two distinct leaves. -/
theorem mem_dup_iff_exists {t : STree V} {H : FGraph V} {v : V} :
    v ∈ t.dup H ↔ ∃ a ∈ t.leafAddrs, ∃ b ∈ t.leafAddrs, a ≠ b ∧
      v ∈ (t.graphAtD H a).verts ∧ v ∈ (t.graphAtD H b).verts := by
  rw [mem_dup]
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
    rw [Finset.mem_filter] at ha hb
    exact ⟨a, ha.1, b, hb.1, hab, ha.2, hb.2⟩
  · rintro ⟨a, ha, b, hb, hab, hva, hvb⟩
    exact ⟨graphAtD_verts_subset t H a hva,
      Finset.one_lt_card.2 ⟨a, Finset.mem_filter.2 ⟨ha, hva⟩, b, Finset.mem_filter.2 ⟨hb, hvb⟩,
        hab⟩⟩

/-- A vertex duplicated by `t` stays duplicated in the graft. -/
theorem dup_subset_dup_graft (t : STree V) (f : Addr → STree V) (H : FGraph V) :
    t.dup H ⊆ (t.graft f).dup H := by
  intro v hv
  obtain ⟨a₁, h₁, a₂, h₂, hne, hv₁, hv₂⟩ := mem_dup_iff_exists.1 hv
  obtain ⟨b₁, hb₁, hw₁⟩ := (f a₁).exists_mem_leafAddrs_mem_verts hv₁
  obtain ⟨b₂, hb₂, hw₂⟩ := (f a₂).exists_mem_leafAddrs_mem_verts hv₂
  refine mem_dup_iff_exists.2 ⟨a₁ ++ b₁, mem_leafAddrs_graft.2 ⟨a₁, h₁, b₁, hb₁, rfl⟩,
    a₂ ++ b₂, mem_leafAddrs_graft.2 ⟨a₂, h₂, b₂, hb₂, rfl⟩, fun h => hne ?_, ?_, ?_⟩
  · have := congrArg t.leafPrefix h
    rwa [leafPrefix_append h₁, leafPrefix_append h₂] at this
  · rwa [graphAtD_graft_append h₁]
  · rwa [graphAtD_graft_append h₂]

/-- A vertex duplicated by the tree grafted at a leaf `a` is duplicated in the graft. -/
theorem dup_subset_dup_graft_of_mem_leafAddrs {t : STree V} {a : Addr} (ha : a ∈ t.leafAddrs)
    (f : Addr → STree V) (H : FGraph V) : (f a).dup (t.graphAtD H a) ⊆ (t.graft f).dup H := by
  intro v hv
  obtain ⟨b₁, h₁, b₂, h₂, hne, hv₁, hv₂⟩ := mem_dup_iff_exists.1 hv
  refine mem_dup_iff_exists.2 ⟨a ++ b₁, mem_leafAddrs_graft.2 ⟨a, ha, b₁, h₁, rfl⟩,
    a ++ b₂, mem_leafAddrs_graft.2 ⟨a, ha, b₂, h₂, rfl⟩,
    fun h => hne (List.append_cancel_left h), ?_, ?_⟩
  · rwa [graphAtD_graft_append ha]
  · rwa [graphAtD_graft_append ha]

end STree

/-- `|N_X(x) ∩ W| = e_X({x}, W)` (the neighbour count of (GC), `EG.HB.Round.isGC`, as the
`eBetween` of the s2:lemGC sketches; no hypothesis `x ∉ W` is needed, `X` has no loops). -/
theorem _root_.EG.FGraph.card_nbrs_inter_eq_eBetween (X : FGraph V) (x : V) (W : Finset V) :
    (X.nbrs x ∩ W).card = X.eBetween {x} W := by
  have h : X.edgesBetween {x} W = (X.nbrs x ∩ W).image (fun w => s(x, w)) := by
    ext e
    simp only [FGraph.mem_edgesBetween, Finset.mem_singleton, Finset.mem_image, Finset.mem_inter,
      FGraph.mem_nbrs]
    constructor
    · rintro ⟨he, a, rfl, b, hb, rfl⟩
      exact ⟨b, ⟨he, hb⟩, rfl⟩
    · rintro ⟨w, ⟨hw, hwW⟩, rfl⟩
      exact ⟨hw, x, rfl, w, hwW, rfl⟩
  rw [FGraph.eBetween, h, Finset.card_image_of_injective _ (fun a b hab => Sym2.congr_right.1 hab)]

end EG.HB
