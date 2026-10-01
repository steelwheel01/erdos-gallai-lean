module

public import EG.Defs.Components
public import EG.Lib.Found.Graph

/-!
# API for components, bridges and pendant edges of edge sets (s6:lemPAR, s6:defDesign)

* `mem_edgeVerts`, `edgeVerts_mono`, `edgeGraph_adj`, `edgeSet_edgeGraph`;
* `mem_edgeComps`, `mem_compVerts`, `mem_compEdges`, `compEdges_subset`,
  `mem_compEdges_of_mem` (a non-loop edge lies in the component of either end),
  `disjoint_compEdges` (distinct components have disjoint edge sets);
* `isNonBridge_mk_iff` (a non-bridge `uv`: `u`, `v` stay connected in `E - uv`),
  `IsNonBridge.mem`, `IsPendant.mem`;
* `E ⊆ E'`: `edgeGraph_mono`, `compMap` (the component of `E'` containing a component of `E`),
  `compMap_mk`, `compMap_mem_edgeComps`, `compEdges_subset_compMap`,
  `card_compEdges_le_compMap`;
* "of that component": `mem_compEdges_of_mem_of_mk` (every edge at a vertex of `C`, loops
  included, is in `compEdges E C`), `degE_compEdges` (degree in the component = degree in `E`),
  `isPendant_compEdges_iff`, `reachable_deleteEdges_compEdges`, `isNonBridge_compEdges_iff`
  (pendant / non-bridge of the component `compEdges E C` iff pendant / non-bridge of `E`).
-/

public section


namespace EG

variable {V : Type*}

theorem mem_edgeVerts [DecidableEq V] {E : Finset (Sym2 V)} {v : V} :
    v ∈ edgeVerts E ↔ ∃ e ∈ E, v ∈ e := by
  simp [edgeVerts, Sym2.mem_toFinset]

theorem edgeVerts_mono [DecidableEq V] {E E' : Finset (Sym2 V)} (h : E ⊆ E') :
    edgeVerts E ⊆ edgeVerts E' := by
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_edgeVerts.1 hv
  exact mem_edgeVerts.2 ⟨e, h he, hve⟩

@[simp] theorem edgeGraph_adj {E : Finset (Sym2 V)} {u v : V} :
    (edgeGraph E).Adj u v ↔ s(u, v) ∈ E ∧ u ≠ v := by
  simp [edgeGraph, SimpleGraph.fromEdgeSet_adj]

theorem edgeSet_edgeGraph (E : Finset (Sym2 V)) :
    (edgeGraph E).edgeSet = (E : Set (Sym2 V)) \ Sym2.diagSet :=
  SimpleGraph.edgeSet_fromEdgeSet _

theorem mem_edgeComps [DecidableEq V] {E : Finset (Sym2 V)}
    {C : (edgeGraph E).ConnectedComponent} :
    C ∈ edgeComps E ↔ ∃ v ∈ edgeVerts E, (edgeGraph E).connectedComponentMk v = C := by
  classical
  simp only [edgeComps, Finset.mem_image]

theorem mem_compVerts [DecidableEq V] {E : Finset (Sym2 V)}
    {C : (edgeGraph E).ConnectedComponent} {v : V} :
    v ∈ compVerts E C ↔ v ∈ edgeVerts E ∧ (edgeGraph E).connectedComponentMk v = C := by
  classical
  simp only [compVerts, Finset.mem_filter]

theorem mem_compEdges {E : Finset (Sym2 V)} {C : (edgeGraph E).ConnectedComponent}
    {e : Sym2 V} :
    e ∈ compEdges E C ↔ e ∈ E ∧ ∀ v ∈ e, (edgeGraph E).connectedComponentMk v = C := by
  classical
  simp [compEdges]

theorem compEdges_subset (E : Finset (Sym2 V)) (C : (edgeGraph E).ConnectedComponent) :
    compEdges E C ⊆ E := fun _ he => (mem_compEdges.1 he).1

/-- A non-loop edge `uv ∈ E` lies in the component of `u`. -/
theorem mem_compEdges_of_mem {E : Finset (Sym2 V)} {u v : V} (he : s(u, v) ∈ E)
    (huv : u ≠ v) : s(u, v) ∈ compEdges E ((edgeGraph E).connectedComponentMk u) := by
  rw [mem_compEdges]
  refine ⟨he, fun w hw => ?_⟩
  rcases Sym2.mem_iff.1 hw with rfl | rfl
  · rfl
  · exact (SimpleGraph.ConnectedComponent.eq.2
      (SimpleGraph.Adj.reachable (edgeGraph_adj.2 ⟨he, huv⟩))).symm

/-- Distinct components have disjoint edge sets. -/
theorem disjoint_compEdges {E : Finset (Sym2 V)} {C C' : (edgeGraph E).ConnectedComponent}
    (h : C ≠ C') : Disjoint (compEdges E C) (compEdges E C') := by
  rw [Finset.disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | h u v =>
    exact h (((mem_compEdges.1 he).2 u (Sym2.mem_mk_left u v)).symm.trans
      ((mem_compEdges.1 he').2 u (Sym2.mem_mk_left u v)))

/-- A non-bridge `uv ∈ E`: its ends stay connected after deleting it. -/
theorem isNonBridge_mk_iff {E : Finset (Sym2 V)} {u v : V} :
    IsNonBridge E s(u, v) ↔
      s(u, v) ∈ E ∧ ((edgeGraph E).deleteEdges {s(u, v)}).Reachable u v := by
  simp [IsNonBridge, SimpleGraph.isBridge_iff]

theorem IsNonBridge.mem {E : Finset (Sym2 V)} {e : Sym2 V} (h : IsNonBridge E e) : e ∈ E :=
  h.1

theorem IsPendant.mem [DecidableEq V] {E : Finset (Sym2 V)} {e : Sym2 V} (h : IsPendant E e) :
    e ∈ E :=
  h.1

/-! ### Component maps for `E ⊆ E'` and component-local characterisations -/

/-- `E ⊆ E'` gives `edgeGraph E ≤ edgeGraph E'`. -/
theorem edgeGraph_mono {E E' : Finset (Sym2 V)} (h : E ⊆ E') : edgeGraph E ≤ edgeGraph E' :=
  SimpleGraph.fromEdgeSet_mono (by exact_mod_cast h)

/-- The component of `(V(E'), E')` containing a component of `(V(E), E)`, for `E ⊆ E'`. -/
@[expose] noncomputable def compMap {E E' : Finset (Sym2 V)} (h : E ⊆ E') :
    (edgeGraph E).ConnectedComponent → (edgeGraph E').ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (edgeGraph_mono h))

@[simp] theorem compMap_mk {E E' : Finset (Sym2 V)} (h : E ⊆ E') (v : V) :
    compMap h ((edgeGraph E).connectedComponentMk v) = (edgeGraph E').connectedComponentMk v :=
  rfl

/-- `compMap` sends components of `(V(E), E)` to components of `(V(E'), E')`. -/
theorem compMap_mem_edgeComps [DecidableEq V] {E E' : Finset (Sym2 V)} (h : E ⊆ E')
    {C : (edgeGraph E).ConnectedComponent} (hC : C ∈ edgeComps E) :
    compMap h C ∈ edgeComps E' := by
  obtain ⟨v, hv, rfl⟩ := mem_edgeComps.1 hC
  exact mem_edgeComps.2 ⟨v, edgeVerts_mono h hv, rfl⟩

/-- (proof of s6:lemJSLC, Step 3) the edges of a component of `E` lie in the edge set of the
component of `E' ⊇ E` containing it. -/
theorem compEdges_subset_compMap {E E' : Finset (Sym2 V)} (h : E ⊆ E')
    (C : (edgeGraph E).ConnectedComponent) : compEdges E C ⊆ compEdges E' (compMap h C) := by
  intro e he
  rw [mem_compEdges] at he ⊢
  refine ⟨h he.1, fun v hv => ?_⟩
  rw [← he.2 v hv, compMap_mk]

/-- The edge count of a component of `E` is at most that of the component of `E' ⊇ E`
containing it. -/
theorem card_compEdges_le_compMap {E E' : Finset (Sym2 V)} (h : E ⊆ E')
    (C : (edgeGraph E).ConnectedComponent) :
    (compEdges E C).card ≤ (compEdges E' (compMap h C)).card :=
  Finset.card_le_card (compEdges_subset_compMap h C)

/-- Every edge of `E` at a vertex `v` of `C` lies in `compEdges E C` (loops included). -/
theorem mem_compEdges_of_mem_of_mk {E : Finset (Sym2 V)} {C : (edgeGraph E).ConnectedComponent}
    {v : V} (hv : (edgeGraph E).connectedComponentMk v = C) {e : Sym2 V} (he : e ∈ E)
    (hve : v ∈ e) : e ∈ compEdges E C := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve |>.imp fun w h => h.symm
  by_cases hvw : v = w
  · subst hvw
    rw [mem_compEdges]
    refine ⟨he, fun x hx => ?_⟩
    rw [Sym2.mem_iff, or_self] at hx
    rw [hx, hv]
  · rw [← hv]; exact mem_compEdges_of_mem he hvw

/-- The degree of a vertex of `C` in its component is its degree in `E`. -/
theorem degE_compEdges [DecidableEq V] {E : Finset (Sym2 V)}
    {C : (edgeGraph E).ConnectedComponent} {v : V}
    (hv : (edgeGraph E).connectedComponentMk v = C) : degE (compEdges E C) v = degE E v := by
  unfold degE
  congr 1
  ext e
  simp only [FGraph.mem_edgesAt]
  exact ⟨fun h => ⟨compEdges_subset E C h.1, h.2⟩,
    fun h => ⟨mem_compEdges_of_mem_of_mk hv h.1 h.2, h.2⟩⟩

/-- [s6:lemPAR] "a pendant edge … of that component": for an edge of the component `C`, being
pendant in `C` is being pendant in `E`. -/
theorem isPendant_compEdges_iff [DecidableEq V] {E : Finset (Sym2 V)}
    {C : (edgeGraph E).ConnectedComponent} {e : Sym2 V} (he : e ∈ compEdges E C) :
    IsPendant (compEdges E C) e ↔ IsPendant E e := by
  have hC := (mem_compEdges.1 he).2
  simp only [IsPendant]
  constructor
  · rintro ⟨_, v, hv, hd⟩
    exact ⟨(mem_compEdges.1 he).1, v, hv, (degE_compEdges (hC v hv)) ▸ hd⟩
  · rintro ⟨_, v, hv, hd⟩
    exact ⟨he, v, hv, (degE_compEdges (hC v hv)).trans hd⟩

/-- Reachability in `E - e` from a vertex of `C` stays inside `compEdges E C - e`. -/
theorem reachable_deleteEdges_compEdges {E : Finset (Sym2 V)}
    {C : (edgeGraph E).ConnectedComponent} {e : Sym2 V} {u v : V}
    (hu : (edgeGraph E).connectedComponentMk u = C)
    (h : ((edgeGraph E).deleteEdges {e}).Reachable u v) :
    ((edgeGraph (compEdges E C)).deleteEdges {e}).Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    rw [SimpleGraph.deleteEdges_adj, edgeGraph_adj] at hab
    obtain ⟨⟨hE, hne⟩, hnot⟩ := hab
    have hb : (edgeGraph E).connectedComponentMk b = C := by
      rw [← hu]
      exact (SimpleGraph.ConnectedComponent.eq.2
        (SimpleGraph.Adj.reachable (edgeGraph_adj.2 ⟨hE, hne⟩))).symm
    refine SimpleGraph.Reachable.trans ?_ (ih hb)
    apply SimpleGraph.Adj.reachable
    rw [SimpleGraph.deleteEdges_adj, edgeGraph_adj]
    refine ⟨⟨?_, hne⟩, hnot⟩
    rw [← hu]; exact mem_compEdges_of_mem hE hne

/-- [s6:lemPAR] "a non-bridge … of that component": for an edge of the component `C`, being a
non-bridge of `C` is being a non-bridge of `E`. -/
theorem isNonBridge_compEdges_iff {E : Finset (Sym2 V)}
    {C : (edgeGraph E).ConnectedComponent} {e : Sym2 V} (he : e ∈ compEdges E C) :
    IsNonBridge (compEdges E C) e ↔ IsNonBridge E e := by
  induction e using Sym2.ind with
  | h u v =>
    have hu := (mem_compEdges.1 he).2 u (Sym2.mem_mk_left u v)
    rw [isNonBridge_mk_iff, isNonBridge_mk_iff]
    constructor
    · rintro ⟨_, hr⟩
      exact ⟨(mem_compEdges.1 he).1, hr.mono (SimpleGraph.deleteEdges_mono
        (edgeGraph_mono (compEdges_subset E C)))⟩
    · rintro ⟨_, hr⟩
      exact ⟨he, reachable_deleteEdges_compEdges hu hr⟩

end EG
