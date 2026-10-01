module

public import EG.Defs.Objects
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Decomposition
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Bridge lemmas: list-based objects ⇒ subgraph decompositions (FC-184-free)

Helper file for `EGCheck/BridgeCore.lean` and `EGCheck/Bridge.lean` (PLAN_FORMALIZATION.md §3,
design decisions 1, 8).

**Does not import `FormalConjectures.ErdosProblems.«184»`** (trust audits of 2026-09-26, §6 of
`APPROVALS/reviews/trust.opus.md`): comparator's `Solution` module restates the upstream
`Erdos184.IsCycleOrEdge` and `Erdos184.erdos_184` itself, so nothing it imports may import the
upstream file. The cycle-or-edge condition is therefore stated here through the *body* of the
upstream definition
```
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1
```
for **arbitrary** instances `i₁ : H.LocallyFinite` (used by `IsRegularOfDegree`) and
`i₂ : Fintype H.edgeSet` (used by `edgeFinset`), so that it applies to whichever instances the
upstream elaboration picked. `SimpleGraph.IsDecomposition` is imported from
`FormalConjecturesForMathlib` (that file is pinned in TRUST.md; it is not the file that
comparator's Solution restates).

No manuscript notion is defined here. The file relates the internal form of [s1:defObject]
("An *object* is a cycle (of length at least 3) or a single edge. A *decomposition* of an edge
set F is a partition of F into the edge sets of objects", formalized as `EG.Obj`/`EG.IsDecomp`
in `EG/Defs/Objects.lean`) to the upstream subgraph form.

* `EGCheck.Bridge.toSub G o`: the subgraph of `G` spanned by the edge list of an object `o`
  (vertices: the ends of those edges; adjacency: `s(a, b) ∈ o.edges ∧ G.Adj a b`).
* For a cycle object `cycle (a :: l)` we build the closed walk `cycleWalk` along
  `a, l₀, …, l_{k-2}, a` and show that `toSub G (cycle (a :: l))` is its `Walk.toSubgraph`;
  Mathlib then gives connectivity (`Walk.toSubgraph_connected`) and 2-regularity
  (`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`).
* `exists_finset_of_isDecomp`: an `EG.IsDecomp G.edgeSet D` yields a `Finset G.Subgraph`
  whose members satisfy the (unfolded, instance-generic) cycle-or-edge condition and which is a
  `SimpleGraph.IsDecomposition` of `G`, with at most `D.length` members.
* `objMap` / `isDecomp_comap_symm`: transport of decompositions along an equivalence of vertex
  types (used with `Fintype.equivFin` to move between `Fin n : Type` and `V : Type u`).
-/

@[expose] public section

namespace EGCheck.Bridge

open SimpleGraph

section Sub

variable {V : Type*}

/- The subgraph spanned by an object. -/

/-- The subgraph of `G` spanned by the edges of the object `o`: its vertices are the ends of the
edges of `o`, and `a ~ b` iff `s(a, b)` is an edge of `o` and of `G`. -/
def toSub (G : SimpleGraph V) (o : EG.Obj V) : G.Subgraph where
  verts := {v | ∃ e ∈ o.edges, v ∈ e}
  Adj a b := s(a, b) ∈ o.edges ∧ G.Adj a b
  adj_sub h := h.2
  edge_vert h := ⟨_, h.1, Sym2.mem_mk_left _ _⟩
  symm := ⟨fun _ _ h => ⟨by rw [Sym2.eq_swap]; exact h.1, h.2.symm⟩⟩

theorem toSub_adj {G : SimpleGraph V} {o : EG.Obj V} {a b : V} :
    (toSub G o).Adj a b ↔ s(a, b) ∈ o.edges ∧ G.Adj a b := Iff.rfl

theorem mem_toSub_verts {G : SimpleGraph V} {o : EG.Obj V} {v : V} :
    v ∈ (toSub G o).verts ↔ ∃ e ∈ o.edges, v ∈ e := Iff.rfl

theorem mem_edgeSet_toSub {G : SimpleGraph V} {o : EG.Obj V} {e : Sym2 V} :
    e ∈ (toSub G o).edgeSet ↔ e ∈ o.edges ∧ e ∈ G.edgeSet := by
  induction e using Sym2.ind with
  | _ a b => simp [toSub_adj]

end Sub

section CycleWalk

variable {V : Type*}

/- The closed walk along a cycle object. -/

/-- The edges `s(a, l₀), s(l₀, l₁), …` of the walk `a, l₀, l₁, …` along a list. -/
def chainEdges (a : V) (l : List V) : List (Sym2 V) :=
  List.zipWith (fun x y => s(x, y)) (a :: l) l

@[simp] theorem chainEdges_nil (a : V) : chainEdges a [] = [] := rfl

@[simp] theorem chainEdges_cons (a b : V) (l : List V) :
    chainEdges a (b :: l) = s(a, b) :: chainEdges b l := rfl

/-- The last vertex of the list `a :: l`. -/
def lastOf : V → List V → V
  | a, [] => a
  | _, b :: l => lastOf b l

theorem lastOf_append_singleton (a x : V) (l : List V) : lastOf a (l ++ [x]) = x := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih b

/-- The walk `a, l₀, l₁, …` along a list whose consecutive pairs are edges of `G`. -/
def listWalk (G : SimpleGraph V) : (a : V) → (l : List V) →
    (∀ e ∈ chainEdges a l, e ∈ G.edgeSet) → G.Walk a (lastOf a l)
  | _, [], _ => Walk.nil
  | a, b :: l, h =>
    Walk.cons (G.mem_edgeSet.1 (h s(a, b) (by simp)))
      (listWalk G b l (fun e he => h e (by simp [he])))

theorem support_listWalk (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ chainEdges a l, e ∈ G.edgeSet) : (listWalk G a l h).support = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact congrArg (List.cons a) (ih b _)

theorem edges_listWalk (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ chainEdges a l, e ∈ G.edgeSet) : (listWalk G a l h).edges = chainEdges a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact congrArg (List.cons s(a, b)) (ih b _)

theorem chainEdges_append_singleton (a x : V) (l : List V) :
    List.zipWith (fun x y => s(x, y)) (a :: l) (l ++ [x]) = chainEdges a (l ++ [x]) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [← ih]

/-- The edges of the cycle `a, l₀, …, l_{k-2}` are those of the walk `a, l₀, …, l_{k-2}, a`. -/
theorem cycleEdges_cons (a : V) (l : List V) :
    EG.cycleEdges (a :: l) = chainEdges a (l ++ [a]) := by
  rw [EG.cycleEdges, List.rotate_cons_succ, List.rotate_zero, chainEdges_append_singleton]

/-- The closed walk `a, l₀, …, l_{k-2}, a` along the cycle object `cycle (a :: l)`. -/
def cycleWalk (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ EG.cycleEdges (a :: l), e ∈ G.edgeSet) : G.Walk a a :=
  (listWalk G a (l ++ [a]) (by rw [← cycleEdges_cons]; exact h)).copy rfl
    (lastOf_append_singleton a a l)

theorem support_cycleWalk (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ EG.cycleEdges (a :: l), e ∈ G.edgeSet) :
    (cycleWalk G a l h).support = a :: (l ++ [a]) := by
  simp [cycleWalk, support_listWalk]

theorem edges_cycleWalk (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ EG.cycleEdges (a :: l), e ∈ G.edgeSet) :
    (cycleWalk G a l h).edges = EG.cycleEdges (a :: l) := by
  simp [cycleWalk, edges_listWalk, cycleEdges_cons]

theorem length_cycleEdges (c : List V) : (EG.cycleEdges c).length = c.length := by
  simp [EG.cycleEdges]

/-- A well-formed cycle object with duplicate-free edge list gives a cycle walk. -/
theorem isCycle_cycleWalk (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ EG.cycleEdges (a :: l), e ∈ G.edgeSet) (hnd : (a :: l).Nodup)
    (hlen : 3 ≤ (a :: l).length) (hend : (EG.cycleEdges (a :: l)).Nodup) :
    (cycleWalk G a l h).IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def, edges_cycleWalk, support_cycleWalk]
  refine ⟨hend, ?_, ?_⟩
  · intro hnil
    have := congrArg Walk.edges hnil
    rw [edges_cycleWalk, Walk.edges_nil, ← List.length_eq_zero_iff, length_cycleEdges] at this
    omega
  · have : (a :: l).rotate 1 = l ++ [a] := by simp
    rw [List.tail_cons, ← this]
    exact List.nodup_rotate.2 hnd

/-- The subgraph spanned by a cycle object is the subgraph of its cycle walk. -/
theorem toSub_cycle_eq (G : SimpleGraph V) (a : V) (l : List V)
    (h : ∀ e ∈ EG.cycleEdges (a :: l), e ∈ G.edgeSet) (hlen : 3 ≤ (a :: l).length) :
    toSub G (.cycle (a :: l)) = (cycleWalk G a l h).toSubgraph := by
  have hnil : ¬ (cycleWalk G a l h).Nil := by
    rw [← Walk.length_eq_zero_iff, ← Walk.length_edges, edges_cycleWalk, length_cycleEdges]
    omega
  ext v
  · rw [mem_toSub_verts, Walk.mem_verts_toSubgraph,
      Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil, edges_cycleWalk]
    rfl
  · rw [toSub_adj, Walk.adj_toSubgraph_iff_mem_edges, edges_cycleWalk]
    exact ⟨fun hw => hw.1, fun hw => ⟨hw, G.mem_edgeSet.1 (h _ hw)⟩⟩

end CycleWalk

section Decomp

variable {V : Type*}

/- Each object gives a cycle or an edge; the objects of a decomposition give an upstream
decomposition. -/

/-- The degree, for an arbitrary `Fintype` instance on the neighbour set, is the `ncard` of the
neighbour set. -/
theorem degree_eq_ncard {W : Type*} (H : SimpleGraph W) (v : W) (inst : Fintype (H.neighborSet v)) :
    @degree W H v inst = (H.neighborSet v).ncard := by
  rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- The number of edges, for an arbitrary `Fintype` instance on the edge set, is the `ncard` of
the edge set. -/
theorem card_edgeFinset_eq_ncard {W : Type*} (H : SimpleGraph W) (inst : Fintype H.edgeSet) :
    (@edgeFinset W H inst).card = H.edgeSet.ncard := by
  rw [← Set.ncard_coe_finset, coe_edgeFinset]

/-- The subgraph of a cycle walk is connected and 2-regular on its coe (body of the upstream
`IsCycleOrEdge`, left disjunct). The instances `i₁` (neighbour sets) and `i₂` (edge set) are
arbitrary (the upstream statement picks classical ones). -/
theorem isCycleOrEdge_of_isCycle {G : SimpleGraph V} {u : V} {p : G.Walk u u} (hp : p.IsCycle)
    (H : G.Subgraph) (hH : H = p.toSubgraph) (i₁ : H.coe.LocallyFinite)
    (i₂ : Fintype H.coe.edgeSet) :
    (H.coe.Connected ∧ @IsRegularOfDegree _ H.coe i₁ 2) ∨ (@edgeFinset _ H.coe i₂).card = 1 := by
  subst hH
  left
  refine ⟨p.toSubgraph_connected.coe, fun v => ?_⟩
  rw [degree_eq_ncard, ← Nat.card_coe_set_eq, Nat.card_congr (Subgraph.coeNeighborSetEquiv v),
    Nat.card_coe_set_eq]
  exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.1 v.2)

/-- A subgraph with exactly one edge has exactly one edge on its coe (body of the upstream
`IsCycleOrEdge`, right disjunct), for arbitrary instances `i₁`, `i₂`. -/
theorem isCycleOrEdge_of_edgeSet_eq {G : SimpleGraph V} (H : G.Subgraph) {e : Sym2 V}
    (he : H.edgeSet = {e}) (i₁ : H.coe.LocallyFinite) (i₂ : Fintype H.coe.edgeSet) :
    (H.coe.Connected ∧ @IsRegularOfDegree _ H.coe i₁ 2) ∨ (@edgeFinset _ H.coe i₂).card = 1 := by
  right
  rw [card_edgeFinset_eq_ncard,
    ← Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
    Subgraph.image_coe_edgeSet_coe, he, Set.ncard_singleton]

/-- The subgraph spanned by a well-formed object of a decomposition is a cycle or an edge (body
of the upstream `IsCycleOrEdge`, for arbitrary instances `i₁`, `i₂`). -/
theorem isCycleOrEdge_toSub {G : SimpleGraph V} {o : EG.Obj V} (hwf : o.WF)
    (hG : ∀ e ∈ o.edges, e ∈ G.edgeSet) (hnd : o.edges.Nodup)
    (i₁ : (toSub G o).coe.LocallyFinite) (i₂ : Fintype (toSub G o).coe.edgeSet) :
    ((toSub G o).coe.Connected ∧ @IsRegularOfDegree _ (toSub G o).coe i₁ 2) ∨
      (@edgeFinset _ (toSub G o).coe i₂).card = 1 := by
  cases o with
  | edge e =>
    refine isCycleOrEdge_of_edgeSet_eq _ (e := e) ?_ i₁ i₂
    ext x
    simp only [mem_edgeSet_toSub, EG.Obj.edges, List.mem_singleton, Set.mem_singleton_iff,
      and_iff_left_iff_imp]
    rintro rfl
    exact hG _ (by simp [EG.Obj.edges])
  | cycle c =>
    obtain ⟨hnd', hlen⟩ := hwf
    cases c with
    | nil => simp at hlen
    | cons a l =>
      exact isCycleOrEdge_of_isCycle (isCycle_cycleWalk G a l hG hnd' hlen hnd) _
        (toSub_cycle_eq G a l hG hlen) i₁ i₂

/-- In a duplicate-free concatenation, an entry comes from a unique member of the list. -/
theorem eq_of_mem_of_nodup_flatMap {α β : Type*} {l : List α} {f : α → List β}
    (h : (l.flatMap f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l) {x : β} (hxa : x ∈ f a)
    (hxb : x ∈ f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨_, h₂, h₃⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd rfl (h₃ x hxa x (List.mem_flatMap.2 ⟨b, hb', hxb⟩))
    · exact absurd rfl (h₃ x hxb x (List.mem_flatMap.2 ⟨a, ha', hxa⟩))
    · exact ih h₂ ha' hb'

/-- An internal decomposition gives an upstream decomposition with at most as many members.
Each member satisfies the body of the upstream `IsCycleOrEdge` on its coe, for arbitrary
instances `i₁` (neighbour sets) and `i₂` (edge set). -/
theorem exists_finset_of_isDecomp {G : SimpleGraph V} {D : List (EG.Obj V)}
    (hD : EG.IsDecomp G.edgeSet D) :
    ∃ D' : Finset G.Subgraph,
      (∀ H ∈ D', ∀ (i₁ : H.coe.LocallyFinite) (i₂ : Fintype H.coe.edgeSet),
        (H.coe.Connected ∧ @IsRegularOfDegree _ H.coe i₁ 2) ∨ (@edgeFinset _ H.coe i₂).card = 1) ∧
      G.IsDecomposition D' ∧ D'.card ≤ D.length := by
  classical
  obtain ⟨hwf, hnd, hmem⟩ := hD
  have hG : ∀ o ∈ D, ∀ e ∈ o.edges, e ∈ G.edgeSet := fun o ho e he =>
    (hmem e).1 (List.mem_flatMap.2 ⟨o, ho, he⟩)
  have hnd' : ∀ o ∈ D, o.edges.Nodup := (List.nodup_flatMap.1 hnd).1
  refine ⟨(D.map (toSub G)).toFinset, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH i₁ i₂
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hH)
    exact isCycleOrEdge_toSub (hwf o ho) (hG o ho) (hnd' o ho) i₁ i₂
  · intro H₁ hH₁ H₂ hH₂ hne
    obtain ⟨o₁, ho₁, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hH₁))
    obtain ⟨o₂, ho₂, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hH₂))
    refine Set.disjoint_left.2 fun e he₁ he₂ => hne ?_
    rw [mem_edgeSet_toSub] at he₁ he₂
    rw [eq_of_mem_of_nodup_flatMap hnd ho₁ ho₂ he₁.1 he₂.1]
  · ext e
    rw [Set.mem_iUnion₂]
    constructor
    · rintro ⟨H, hH, he⟩
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hH)
      exact (mem_edgeSet_toSub.1 he).2
    · intro he
      obtain ⟨o, ho, heo⟩ := List.mem_flatMap.1 ((hmem e).2 he)
      exact ⟨toSub G o, List.mem_toFinset.2 (List.mem_map.2 ⟨o, ho, rfl⟩),
        mem_edgeSet_toSub.2 ⟨heo, he⟩⟩
  · exact (List.toFinset_card_le _).trans (List.length_map _).le

end Decomp

section Transport

variable {V W : Type*}

/- Transport of objects and decompositions along a map of vertex types. -/

/-- The image of an object under a map of vertices. -/
def objMap (f : V → W) : EG.Obj V → EG.Obj W
  | .edge e => .edge (Sym2.map f e)
  | .cycle c => .cycle (c.map f)

theorem cycleEdges_map (f : V → W) (c : List V) :
    EG.cycleEdges (c.map f) = (EG.cycleEdges c).map (Sym2.map f) := by
  simp [EG.cycleEdges, ← List.map_rotate, List.map_zipWith, List.zipWith_map]

theorem edges_objMap (f : V → W) (o : EG.Obj V) :
    (objMap f o).edges = o.edges.map (Sym2.map f) := by
  cases o with
  | edge e => rfl
  | cycle c => exact cycleEdges_map f c

theorem wf_objMap {f : V → W} (hf : Function.Injective f) {o : EG.Obj V} (h : o.WF) :
    (objMap f o).WF := by
  cases o with
  | edge e => exact fun hd => h ((Sym2.isDiag_map hf).1 hd)
  | cycle c => exact ⟨h.1.map hf, by rw [List.length_map]; exact h.2⟩

theorem mem_edgeSet_comap (f : V → W) (G : SimpleGraph W) (e : Sym2 V) :
    e ∈ (G.comap f).edgeSet ↔ Sym2.map f e ∈ G.edgeSet := by
  induction e using Sym2.ind with
  | _ a b => simp

/-- A decomposition of `G.comap e.symm` (a copy of `G` on `W`) maps back to a decomposition of
`G` along `e.symm`. -/
theorem isDecomp_comap_symm (e : V ≃ W) (G : SimpleGraph V) {D : List (EG.Obj W)}
    (hD : EG.IsDecomp (G.comap e.symm).edgeSet D) :
    EG.IsDecomp G.edgeSet (D.map (objMap e.symm)) := by
  obtain ⟨hwf, hnd, hmem⟩ := hD
  have hfl : (D.map (objMap e.symm)).flatMap EG.Obj.edges =
      (D.flatMap EG.Obj.edges).map (Sym2.map e.symm) := by
    simp [List.flatMap_map, edges_objMap, List.map_flatMap]
  refine ⟨?_, ?_, ?_⟩
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
    exact wf_objMap e.symm.injective (hwf o' ho')
  · rw [hfl]
    exact hnd.map (Sym2.map.injective e.symm.injective)
  · intro x
    rw [hfl, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_edgeSet_comap _ _ _).1 ((hmem y).1 hy)
    · intro hx
      refine ⟨Sym2.map e x, (hmem _).2 ((mem_edgeSet_comap _ _ _).2 ?_), by simp [Sym2.map_map]⟩
      simpa [Sym2.map_map] using hx

end Transport

end EGCheck.Bridge
