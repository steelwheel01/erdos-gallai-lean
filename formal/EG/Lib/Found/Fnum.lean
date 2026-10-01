module

public import EG.Defs.Fnum
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Elementary properties of `f` (manuscript s1:factAdd) and basic `IsDecomp` API

* edges of cycles: `mem_cycleEdges`, `cycleEdges_map`, `nodup_cycleEdges`, …;
* relabelling objects: `Obj.map`; single-edge objects (`Obj.isEdge`, defined in
  `EG.Defs.Objects`), counted by
  `D.countP Obj.isEdge` (`countP_isEdge_append`, `countP_isEdge_map`, `countP_isEdge_flatMap`,
  `countP_isEdge_flatMap_toList`, `countP_isEdge_singletons`, `IsDecomp.countP_isEdge_le_card`,
  `exists_isDecomp_biUnion_countP`);
* `IsDecomp` API: `IsDecomp.append`, `isDecomp_singletons`, `IsDecomp.map`, `isDecomp_map_iff`
  (finset forms `IsDecomp.map_finset`, `isDecomp_map_finset_iff`), `IsDecomp.sublist`, …;
* iterated unions of decompositions (the decomposition form of [s1:factAdd](b) used in
  s6:lemHCCglob): `isDecomp_flatMap`, `isDecomp_biUnion`, `isDecomp_finset_biUnion`,
  `exists_isDecomp_biUnion`, `length_flatMap_toList`;
* `fnum`: optimal decompositions (`exists_isDecomp_length_eq_fnum`, `fnum_le_iff`), and
  [s1:factAdd] (a) `fnum_le_card`, (b) `fnum_union_le`, (c) `fnum_union_eq_of_vertexDisjoint`,
  (d) `fnum_map`, `fnum_edgeFinset_induce_of_support_subset`, `fmax_mono`;
* `fmax` is the maximum of f over `n`-vertex graphs: `fnum_le_fmax`, `exists_fnum_eq_fmax`.
-/

public section


namespace EG

open Function

variable {V W : Type*}

/-! ### Edges of cycles -/

@[simp] theorem length_cycleEdges (c : List V) : (cycleEdges c).length = c.length := by
  simp [cycleEdges]

theorem getElem_cycleEdges (c : List V) (i : ℕ) (h : i < (cycleEdges c).length) :
    (cycleEdges c)[i] = s(c[i]'(by simpa using h),
      c[(i + 1) % c.length]'(Nat.mod_lt _ (by simp at h; omega))) := by
  simp [cycleEdges, List.getElem_zipWith, List.getElem_rotate]

/-- The edges of the closed walk `c₀ c₁ … c_{k-1} c₀` are the `s(cᵢ, c_{i+1 mod k})`. -/
theorem mem_cycleEdges {c : List V} {e : Sym2 V} :
    e ∈ cycleEdges c ↔ ∃ (i : ℕ) (h : i < c.length),
      s(c[i], c[(i + 1) % c.length]'(Nat.mod_lt _ (by omega))) = e := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by simpa using hi, (getElem_cycleEdges c i hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by simpa using hi, getElem_cycleEdges c i (by simpa using hi)⟩

theorem mk_mem_cycleEdges {c : List V} (i : ℕ) (h : i + 1 < c.length) :
    s(c[i], c[i + 1]) ∈ cycleEdges c := by
  rw [mem_cycleEdges]
  refine ⟨i, by omega, ?_⟩
  simp [Nat.mod_eq_of_lt h]

theorem mem_of_mem_cycleEdges {c : List V} {e : Sym2 V} {v : V} (he : e ∈ cycleEdges c)
    (hv : v ∈ e) : v ∈ c := by
  obtain ⟨i, hi, rfl⟩ := mem_cycleEdges.1 he
  rcases Sym2.mem_iff.1 hv with rfl | rfl <;> exact List.getElem_mem _

theorem exists_mem_cycleEdges_of_mem {c : List V} {v : V} (hv : v ∈ c) :
    ∃ e ∈ cycleEdges c, v ∈ e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
  exact ⟨_, mem_cycleEdges.2 ⟨i, hi, rfl⟩, Sym2.mem_mk_left _ _⟩

theorem cycleEdges_map (f : V → W) (c : List V) :
    cycleEdges (c.map f) = (cycleEdges c).map (Sym2.map f) := by
  simp [cycleEdges, ← List.map_rotate, List.zipWith_map, List.map_zipWith]

/-- The edges of a cycle with at least two distinct vertices are not loops. -/
theorem not_isDiag_of_mem_cycleEdges {c : List V} (hc : c.Nodup) (h2 : 2 ≤ c.length)
    {e : Sym2 V} (he : e ∈ cycleEdges c) : ¬ e.IsDiag := by
  obtain ⟨i, hi, rfl⟩ := mem_cycleEdges.1 he
  rw [Sym2.mk_isDiag_iff, hc.getElem_inj_iff]
  intro h
  rcases Nat.lt_or_ge (i + 1) c.length with h' | h'
  · rw [Nat.mod_eq_of_lt h'] at h; omega
  · have : i + 1 = c.length := by omega
    rw [this, Nat.mod_self] at h; omega

/-- The edge list of a cycle with at least three distinct vertices is duplicate free. -/
theorem nodup_cycleEdges {c : List V} (hc : c.Nodup) (h3 : 3 ≤ c.length) :
    (cycleEdges c).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  rintro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [getElem_cycleEdges] at h
  simp only [length_cycleEdges] at hi hj
  simp only [Fin.mk.injEq]
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact (hc.getElem_inj_iff).1 h1
  · rw [hc.getElem_inj_iff] at h1 h2
    exfalso
    rcases Nat.lt_or_ge (i + 1) c.length with hi' | hi' <;>
      rcases Nat.lt_or_ge (j + 1) c.length with hj' | hj'
    · rw [Nat.mod_eq_of_lt hj'] at h1; rw [Nat.mod_eq_of_lt hi'] at h2; omega
    · rw [show j + 1 = c.length by omega, Nat.mod_self] at h1
      rw [Nat.mod_eq_of_lt hi'] at h2; omega
    · rw [Nat.mod_eq_of_lt hj'] at h1
      rw [show i + 1 = c.length by omega, Nat.mod_self] at h2; omega
    · rw [show j + 1 = c.length by omega, Nat.mod_self] at h1
      rw [show i + 1 = c.length by omega, Nat.mod_self] at h2; omega

/-- Propagation around a cycle: a vertex property that is preserved along every edge of the
cycle holds at every vertex once it holds at one (objects are connected, used for
[s1:factAdd](c)). -/
theorem forall_mem_of_cycleEdges {c : List V} (P : V → Prop)
    (hP : ∀ a b, s(a, b) ∈ cycleEdges c → P a → P b) {x : V} (hx : x ∈ c) (hPx : P x) :
    ∀ y ∈ c, P y := by
  -- propagate from `x` forward to the last vertex, wrap around to `c[0]`, then go forward again
  have hne : 0 < c.length := List.length_pos_of_mem hx
  -- forward propagation from `c[k]` to all later indices
  have fwd : ∀ k (hk : k < c.length), P c[k] → ∀ i (hi : i < c.length), k ≤ i → P c[i] := by
    intro k hk hPk i hi hki
    induction i with
    | zero =>
      obtain rfl : k = 0 := by omega
      exact hPk
    | succ i ih =>
      rcases Nat.eq_or_lt_of_le hki with h | h
      · subst h; exact hPk
      · exact hP _ _ (mk_mem_cycleEdges i hi) (ih (by omega) (by omega))
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
  -- the last vertex, then wrap around to `c[0]`
  have hlast : P (c[c.length - 1]'(by omega)) := fwd k hk hPx _ _ (by omega)
  have h0 : P (c[0]'hne) := by
    have he : s(c[c.length - 1]'(by omega), c[0]'hne) ∈ cycleEdges c := by
      rw [mem_cycleEdges]
      refine ⟨c.length - 1, by omega, ?_⟩
      simp [show c.length - 1 + 1 = c.length by omega]
    exact hP _ _ he hlast
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
  exact fwd 0 hne h0 i hi (Nat.zero_le _)

/-! ### Objects -/

namespace Obj

/-- Relabel the vertices of an object along `f`. -/
@[expose] def map (f : V → W) : Obj V → Obj W
  | .edge e => .edge (e.map f)
  | .cycle c => .cycle (c.map f)

@[simp] theorem map_edge (f : V → W) (e : Sym2 V) : (Obj.edge e).map f = .edge (e.map f) := rfl

@[simp] theorem map_cycle (f : V → W) (c : List V) : (Obj.cycle c).map f = .cycle (c.map f) :=
  rfl

@[simp] theorem edges_edge (e : Sym2 V) : (Obj.edge e).edges = [e] := rfl

@[simp] theorem edges_cycle (c : List V) : (Obj.cycle c).edges = cycleEdges c := rfl

theorem edges_map (f : V → W) (o : Obj V) : (o.map f).edges = o.edges.map (Sym2.map f) := by
  cases o with
  | edge e => rfl
  | cycle c => exact cycleEdges_map f c

theorem map_map {X : Type*} (f : V → W) (g : W → X) (o : Obj V) :
    (o.map f).map g = o.map (g ∘ f) := by
  cases o <;> simp [Sym2.map_map]

@[simp] theorem map_id' (o : Obj V) : o.map (fun x => x) = o := by
  cases o <;> simp [Sym2.map_id']

/-- Two relabellings agreeing on the vertices of the edges of `o` agree on `o`. -/
theorem map_congr {f g : V → W} {o : Obj V} (h : ∀ e ∈ o.edges, ∀ v ∈ e, f v = g v) :
    o.map f = o.map g := by
  cases o with
  | edge e => simpa using Sym2.map_congr (h e (by simp))
  | cycle c =>
    simp only [map_cycle, Obj.cycle.injEq]
    refine List.map_congr_left fun v hv => ?_
    obtain ⟨e, he, hve⟩ := exists_mem_cycleEdges_of_mem hv
    exact h e he v hve

theorem wf_map_iff {f : V → W} (hf : Injective f) {o : Obj V} : (o.map f).WF ↔ o.WF := by
  cases o with
  | edge e => simp [WF, Sym2.isDiag_map hf]
  | cycle c => simp [WF, List.nodup_map_iff hf]

/-- Edges of well-formed objects are not loops. -/
theorem WF.not_isDiag {o : Obj V} (ho : o.WF) {e : Sym2 V} (he : e ∈ o.edges) : ¬ e.IsDiag := by
  cases o with
  | edge e' =>
    simp only [edges_edge, List.mem_singleton] at he
    subst he; exact ho
  | cycle c => exact not_isDiag_of_mem_cycleEdges ho.1 (by have := ho.2; omega) he

/-- A well-formed object has at least one edge. -/
theorem WF.length_edges_pos {o : Obj V} (ho : o.WF) : 0 < o.edges.length := by
  cases o with
  | edge e => simp
  | cycle c => simp only [edges_cycle, length_cycleEdges]; have := ho.2; omega

/-- The edge list of a well-formed object is duplicate free. -/
theorem WF.nodup_edges {o : Obj V} (ho : o.WF) : o.edges.Nodup := by
  cases o with
  | edge e => simp
  | cycle c => exact nodup_cycleEdges ho.1 ho.2

/-! #### Single-edge objects -/

-- `Obj.isEdge` itself is defined in `EG/Defs/Objects.lean` (moved there in P2-D).

@[simp] theorem isEdge_edge (e : Sym2 V) : (Obj.edge e).isEdge = true := rfl

@[simp] theorem isEdge_cycle (c : List V) : (Obj.cycle c).isEdge = false := rfl

theorem isEdge_iff {o : Obj V} : o.isEdge = true ↔ ∃ e, o = .edge e := by
  cases o <;> simp

theorem isEdge_eq_false_iff {o : Obj V} : o.isEdge = false ↔ ∃ c, o = .cycle c := by
  cases o <;> simp

@[simp] theorem isEdge_map (f : V → W) (o : Obj V) : (o.map f).isEdge = o.isEdge := by
  cases o <;> rfl

/-- A single-edge object has exactly one edge. -/
theorem length_edges_of_isEdge {o : Obj V} (h : o.isEdge = true) : o.edges.length = 1 := by
  obtain ⟨e, rfl⟩ := isEdge_iff.1 h
  rfl

end Obj

/-! ### The `IsDecomp` API -/

section IsDecomp

variable {E E₁ E₂ : Set (Sym2 V)} {D D₁ D₂ : List (Obj V)}

theorem IsDecomp.wf (h : IsDecomp E D) : ∀ o ∈ D, o.WF := h.1

theorem IsDecomp.nodup (h : IsDecomp E D) : (D.flatMap Obj.edges).Nodup := h.2.1

theorem IsDecomp.mem_iff (h : IsDecomp E D) {e : Sym2 V} :
    e ∈ D.flatMap Obj.edges ↔ e ∈ E := h.2.2 e

/-- The edge set of a decomposition is the set of edges of its objects. -/
theorem IsDecomp.eq_setOf (h : IsDecomp E D) : E = {e | e ∈ D.flatMap Obj.edges} := by
  ext e; exact h.mem_iff.symm

theorem IsDecomp.congr (h : IsDecomp E D) (hE : E = E₁) : IsDecomp E₁ D := hE ▸ h

theorem IsDecomp.mem_of_mem_edges (h : IsDecomp E D) {o : Obj V} (ho : o ∈ D) {e : Sym2 V}
    (he : e ∈ o.edges) : e ∈ E :=
  h.mem_iff.1 (List.mem_flatMap.2 ⟨o, ho, he⟩)

/-- A decomposable edge set has no loops. -/
theorem IsDecomp.not_isDiag (h : IsDecomp E D) {e : Sym2 V} (he : e ∈ E) : ¬ e.IsDiag := by
  obtain ⟨o, ho, heo⟩ := List.mem_flatMap.1 (h.mem_iff.2 he)
  exact (h.wf o ho).not_isDiag heo

theorem isDecomp_nil_iff : IsDecomp E ([] : List (Obj V)) ↔ E = ∅ := by
  simp [IsDecomp, Set.eq_empty_iff_forall_notMem]

theorem isDecomp_nil : IsDecomp (∅ : Set (Sym2 V)) [] := isDecomp_nil_iff.2 rfl

/-- The empty edge set has only the empty decomposition. -/
theorem IsDecomp.eq_nil_of_empty (h : IsDecomp (∅ : Set (Sym2 V)) D) : D = [] := by
  rcases D with _ | ⟨o, D⟩
  · rfl
  · exfalso
    have hpos := (h.wf o (by simp)).length_edges_pos
    obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hpos
    exact h.mem_of_mem_edges (by simp) he

/-- [s1:factAdd](b), list form: the union of decompositions of disjoint edge sets is a
decomposition of their union. -/
theorem IsDecomp.append (h₁ : IsDecomp E₁ D₁) (h₂ : IsDecomp E₂ D₂) (hd : Disjoint E₁ E₂) :
    IsDecomp (E₁ ∪ E₂) (D₁ ++ D₂) := by
  refine ⟨fun o ho => ?_, ?_, fun e => ?_⟩
  · rcases List.mem_append.1 ho with ho | ho
    exacts [h₁.wf o ho, h₂.wf o ho]
  · rw [List.flatMap_append, List.nodup_append]
    refine ⟨h₁.nodup, h₂.nodup, fun a ha b hb hab => ?_⟩
    subst hab
    exact Set.disjoint_left.1 hd (h₁.mem_iff.1 ha) (h₂.mem_iff.1 hb)
  · rw [List.flatMap_append, List.mem_append, h₁.mem_iff, h₂.mem_iff, Set.mem_union]

/-- A single non-loop edge is an object. -/
theorem isDecomp_edge {e : Sym2 V} (he : ¬ e.IsDiag) : IsDecomp {e} [Obj.edge e] := by
  refine ⟨?_, ?_, fun x => ?_⟩ <;> simp [Obj.WF, he]

/-- A cycle with at least three distinct vertices decomposes its own edge set. -/
theorem isDecomp_cycle {c : List V} (hc : c.Nodup) (h3 : 3 ≤ c.length) :
    IsDecomp {e | e ∈ cycleEdges c} [Obj.cycle c] := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa [Obj.WF] using ⟨hc, h3⟩
  · simpa using nodup_cycleEdges hc h3
  · simp

/-- A duplicate-free list of non-loop edges, as single-edge objects. -/
theorem isDecomp_map_edge {L : List (Sym2 V)} (hnd : L.Nodup) (hL : ∀ e ∈ L, ¬ e.IsDiag) :
    IsDecomp {e | e ∈ L} (L.map Obj.edge) := by
  have hfl : (L.map Obj.edge).flatMap Obj.edges = L := by
    simp [List.flatMap_map]
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa [Obj.WF] using hL
  · rwa [hfl]
  · rw [hfl]; rfl

/-- [s1:factAdd](a), list form: the single edges of a loopless edge set form a decomposition
with `|F|` objects. -/
theorem isDecomp_singletons (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    IsDecomp (F : Set (Sym2 V)) (F.toList.map Obj.edge) :=
  (isDecomp_map_edge F.nodup_toList (fun e he => hF e (Finset.mem_toList.1 he))).congr
    (by ext; simp)

theorem length_singletons (F : Finset (Sym2 V)) : (F.toList.map Obj.edge).length = F.card := by
  simp

/-- Sub-families of a decomposition decompose the edges they cover. -/
theorem IsDecomp.sublist (h : IsDecomp E D) {D' : List (Obj V)} (hs : D'.Sublist D) :
    IsDecomp {e | e ∈ D'.flatMap Obj.edges} D' :=
  ⟨fun o ho => h.wf o (hs.subset ho), h.nodup.sublist (hs.flatMap _), fun _ => Iff.rfl⟩

/-- Relabelling a decomposition along an injective map of vertices. -/
theorem IsDecomp.map {f : V → W} (hf : Injective f) (h : IsDecomp E D) :
    IsDecomp (Sym2.map f '' E) (D.map (Obj.map f)) := by
  have hfl : (D.map (Obj.map f)).flatMap Obj.edges = (D.flatMap Obj.edges).map (Sym2.map f) := by
    simp [List.flatMap_map, List.map_flatMap, Obj.edges_map]
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa [Obj.wf_map_iff hf] using h.wf
  · rw [hfl]; exact h.nodup.map (Sym2.map.injective hf)
  · rw [hfl, List.mem_map]
    simp only [h.mem_iff, Set.mem_image]

/-- Relabelling along an injective map neither creates nor destroys decompositions. -/
theorem isDecomp_map_iff {f : V → W} (hf : Injective f) :
    IsDecomp (Sym2.map f '' E) (D.map (Obj.map f)) ↔ IsDecomp E D := by
  refine ⟨fun h => ?_, IsDecomp.map hf⟩
  have hfl : (D.map (Obj.map f)).flatMap Obj.edges = (D.flatMap Obj.edges).map (Sym2.map f) := by
    simp [List.flatMap_map, List.map_flatMap, Obj.edges_map]
  have hinj := Sym2.map.injective hf
  refine ⟨fun o ho => ?_, ?_, fun x => ?_⟩
  · exact (Obj.wf_map_iff hf).1 (h.wf _ (List.mem_map_of_mem ho))
  · have := h.nodup; rw [hfl] at this; exact this.of_map _
  · have := @IsDecomp.mem_iff _ _ _ h (Sym2.map f x)
    rw [hfl, List.mem_map_of_injective hinj, hinj.mem_set_image] at this
    exact this

/-- The number of edges of a decomposition of a finite edge set. -/
theorem IsDecomp.length_flatMap {F : Finset (Sym2 V)} (h : IsDecomp (F : Set (Sym2 V)) D) :
    (D.flatMap Obj.edges).length = F.card := by
  classical
  rw [← List.toFinset_card_of_nodup h.nodup]
  congr 1
  ext e; simp [h.mem_iff]

/-- A decomposition of `F` has at most `|F|` objects. -/
theorem IsDecomp.length_le_card {F : Finset (Sym2 V)} (h : IsDecomp (F : Set (Sym2 V)) D) :
    D.length ≤ F.card := by
  rw [← h.length_flatMap]
  have hwf := h.wf
  clear h
  induction D with
  | nil => simp
  | cons o D ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := (hwf o (by simp)).length_edges_pos
    have h2 := ih (fun o' ho' => hwf o' (by simp [ho']))
    omega

/-! #### Iterated unions (the decomposition form of [s1:factAdd](b), used in s6:lemHCCglob) -/

section Iterated

variable {ι : Type*} {Es : ι → Set (Sym2 V)} {Ds : ι → List (Obj V)}

/-- [s1:factAdd](b) iterated, list form: concatenating decompositions of pairwise disjoint edge
sets `Es i` (`i` running through the list `l`) gives a decomposition of their union. -/
theorem isDecomp_flatMap {l : List ι} (h : ∀ i ∈ l, IsDecomp (Es i) (Ds i))
    (hd : l.Pairwise fun i j => Disjoint (Es i) (Es j)) :
    IsDecomp (⋃ i ∈ l, Es i) (l.flatMap Ds) := by
  induction l with
  | nil => simpa using (isDecomp_nil : IsDecomp (∅ : Set (Sym2 V)) [])
  | cons i l ih =>
    rw [List.pairwise_cons] at hd
    have hl := ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) hd.2
    have hdisj : Disjoint (Es i) (⋃ j ∈ l, Es j) :=
      Set.disjoint_iUnion₂_right.2 fun j hj => hd.1 j hj
    rw [List.flatMap_cons]
    refine ((h i List.mem_cons_self).append hl hdisj).congr ?_
    ext e
    simp

theorem length_flatMap_toList (s : Finset ι) (Ds : ι → List (Obj V)) :
    (s.toList.flatMap Ds).length = ∑ i ∈ s, (Ds i).length := by
  rw [List.length_flatMap, Finset.sum_map_toList]

/-- [s1:factAdd](b) iterated, finset form: for pairwise disjoint edge sets `Es i` (`i ∈ s`) with
decompositions `Ds i`, the concatenation of the `Ds i` decomposes `⋃ i ∈ s, Es i`; it has
`∑ i ∈ s, |Ds i|` objects (`length_flatMap_toList`). -/
theorem isDecomp_biUnion (s : Finset ι) (hd : (s : Set ι).PairwiseDisjoint Es)
    (h : ∀ i ∈ s, IsDecomp (Es i) (Ds i)) :
    IsDecomp (⋃ i ∈ s, Es i) (s.toList.flatMap Ds) := by
  have hl := isDecomp_flatMap (l := s.toList) (Es := Es) (Ds := Ds)
    (fun i hi => h i (Finset.mem_toList.1 hi))
    (s.nodup_toList.pairwise_of_forall_ne fun i hi j hj hij =>
      hd (Finset.mem_coe.2 (Finset.mem_toList.1 hi)) (Finset.mem_coe.2 (Finset.mem_toList.1 hj))
        hij)
  refine hl.congr ?_
  ext e
  simp

/-- [s6:lemHCCglob], first sentence: "Let E_1, …, E_q be pairwise disjoint, and suppose each
E_i decomposes into a_i objects. Then E_1 ∪ … ∪ E_q decomposes into ∑_i a_i objects." (Stated
for any edge sets; the manuscript's `E_i ⊆ E(G)` is not needed.)

Note for the s6 layer: this is only the first sentence of s6:lemHCCglob, placed here in the s1
foundation layer because it is [s1:factAdd](b) iterated. The s6 formalization should cite this
lemma (and `isDecomp_biUnion` / `countP_isEdge_flatMap_toList` for the object list and its
single edges) instead of re-proving it. The second paragraph of s6:lemHCCglob (systems of
s6:lemHCCP) belongs to the s6 files. -/
theorem exists_isDecomp_biUnion (s : Finset ι) (hd : (s : Set ι).PairwiseDisjoint Es)
    (h : ∀ i ∈ s, IsDecomp (Es i) (Ds i)) :
    ∃ D : List (Obj V), IsDecomp (⋃ i ∈ s, Es i) D ∧ D.length = ∑ i ∈ s, (Ds i).length :=
  ⟨_, isDecomp_biUnion s hd h, length_flatMap_toList s Ds⟩

/-- `isDecomp_biUnion` for finite edge sets: the concatenation decomposes `s.biUnion Fs`. -/
theorem isDecomp_finset_biUnion [DecidableEq V] (s : Finset ι) {Fs : ι → Finset (Sym2 V)}
    (hd : (s : Set ι).PairwiseDisjoint Fs) (h : ∀ i ∈ s, IsDecomp (Fs i : Set (Sym2 V)) (Ds i)) :
    IsDecomp ((s.biUnion Fs : Finset (Sym2 V)) : Set (Sym2 V)) (s.toList.flatMap Ds) := by
  have hd' : (s : Set ι).PairwiseDisjoint fun i => (Fs i : Set (Sym2 V)) :=
    fun i hi j hj hij => Finset.disjoint_coe.2 (hd hi hj hij)
  exact (isDecomp_biUnion s hd' h).congr (Finset.coe_biUnion).symm

end Iterated

/-! #### Counting single edges (`D.countP Obj.isEdge`) -/

section CountEdges

theorem countP_isEdge_append (D₁ D₂ : List (Obj V)) :
    (D₁ ++ D₂).countP Obj.isEdge = D₁.countP Obj.isEdge + D₂.countP Obj.isEdge :=
  List.countP_append

theorem countP_isEdge_cons (o : Obj V) (D : List (Obj V)) :
    (o :: D).countP Obj.isEdge = D.countP Obj.isEdge + if o.isEdge then 1 else 0 := by
  cases h : o.isEdge <;> simp [h]

/-- Relabelling objects does not change the number of single edges. -/
@[simp] theorem countP_isEdge_map (f : V → W) (D : List (Obj V)) :
    (D.map (Obj.map f)).countP Obj.isEdge = D.countP Obj.isEdge := by
  rw [List.countP_map]
  exact List.countP_congr fun o _ => by simp

/-- A list of single-edge objects: every object is a single edge. -/
@[simp] theorem countP_isEdge_map_edge (L : List (Sym2 V)) :
    (L.map Obj.edge).countP Obj.isEdge = L.length := by
  rw [List.countP_map, List.countP_eq_length.2]
  intro e _
  rfl

/-- A list of cycle objects has no single edge. -/
@[simp] theorem countP_isEdge_map_cycle (cs : List (List V)) :
    (cs.map Obj.cycle).countP Obj.isEdge = 0 := by
  rw [List.countP_map, List.countP_eq_zero]
  intro c _
  simp

/-- [s1:factAdd](a), counted: the decomposition of `F` into its single edges has `|F|` single
edges. -/
theorem countP_isEdge_singletons (F : Finset (Sym2 V)) :
    (F.toList.map Obj.edge).countP Obj.isEdge = F.card := by
  rw [countP_isEdge_map_edge, Finset.length_toList]

/-- The objects of `D` are its single edges and its cycles. -/
theorem length_eq_countP_isEdge_add (D : List (Obj V)) :
    D.length = D.countP Obj.isEdge + D.countP (fun o => !o.isEdge) :=
  (List.length_eq_countP_add_countP Obj.isEdge (l := D)).trans (by simp)

theorem countP_isEdge_le_length (D : List (Obj V)) : D.countP Obj.isEdge ≤ D.length :=
  List.countP_le_length

/-- A decomposition of `F` has at most `|F|` single edges. -/
theorem IsDecomp.countP_isEdge_le_card {F : Finset (Sym2 V)}
    (h : IsDecomp (F : Set (Sym2 V)) D) : D.countP Obj.isEdge ≤ F.card :=
  (countP_isEdge_le_length D).trans h.length_le_card

variable {ι : Type*}

/-- Single edges of a concatenation of decompositions (list form, cf. `isDecomp_flatMap`). -/
theorem countP_isEdge_flatMap (l : List ι) (Ds : ι → List (Obj V)) :
    (l.flatMap Ds).countP Obj.isEdge = (l.map fun i => (Ds i).countP Obj.isEdge).sum := by
  rw [List.countP_flatMap]
  rfl

/-- Single edges of a concatenation of decompositions (finset form, cf. `isDecomp_biUnion` and
`length_flatMap_toList`). -/
theorem countP_isEdge_flatMap_toList (s : Finset ι) (Ds : ι → List (Obj V)) :
    (s.toList.flatMap Ds).countP Obj.isEdge = ∑ i ∈ s, (Ds i).countP Obj.isEdge := by
  rw [countP_isEdge_flatMap, Finset.sum_map_toList]

/-- [s6:lemHCCglob], first sentence, with the single edges counted: for pairwise disjoint edge
sets `Es i` (`i ∈ s`) with decompositions `Ds i`, the union has a decomposition whose number of
objects and whose number of single edges are the sums over `i ∈ s`. -/
theorem exists_isDecomp_biUnion_countP {Es : ι → Set (Sym2 V)} {Ds : ι → List (Obj V)}
    (s : Finset ι) (hd : (s : Set ι).PairwiseDisjoint Es) (h : ∀ i ∈ s, IsDecomp (Es i) (Ds i)) :
    ∃ D : List (Obj V), IsDecomp (⋃ i ∈ s, Es i) D ∧ D.length = ∑ i ∈ s, (Ds i).length ∧
      D.countP Obj.isEdge = ∑ i ∈ s, (Ds i).countP Obj.isEdge :=
  ⟨_, isDecomp_biUnion s hd h, length_flatMap_toList s Ds, countP_isEdge_flatMap_toList s Ds⟩

end CountEdges

end IsDecomp

/-! ### Objects are connected -/

/-- Objects are connected (proof of [s1:factAdd](c)): if every edge of `o` lies in `E₁ ∪ E₂` and
no vertex is incident to an edge of `E₁` and to an edge of `E₂`, then as soon as one edge of `o`
lies in `E₁`, all of them do. -/
theorem Obj.edges_mem_of_vertexDisjoint {o : Obj V} {E₁ E₂ : Set (Sym2 V)}
    (hdisj : ∀ e₁ ∈ E₁, ∀ e₂ ∈ E₂, ∀ v ∈ e₁, v ∉ e₂)
    (ho : ∀ e ∈ o.edges, e ∈ E₁ ∨ e ∈ E₂) {e : Sym2 V} (he : e ∈ o.edges) (he₁ : e ∈ E₁) :
    ∀ e' ∈ o.edges, e' ∈ E₁ := by
  cases o with
  | edge x =>
    simp only [Obj.edges_edge, List.mem_singleton] at he ⊢
    rintro e' rfl; exact he ▸ he₁
  | cycle c =>
    simp only [Obj.edges_cycle] at he ho ⊢
    -- `P v`: `v` is incident to an edge of `E₁`
    let P : V → Prop := fun v => ∃ x ∈ E₁, v ∈ x
    have hnot : ∀ a b, s(a, b) ∈ E₂ → ¬ P a := by
      rintro a b hab ⟨x, hx, hax⟩
      exact hdisj x hx _ hab a hax (Sym2.mem_mk_left a b)
    have hstep : ∀ a b, s(a, b) ∈ cycleEdges c → P a → P b := by
      intro a b hab hPa
      rcases ho _ hab with h1 | h2
      · exact ⟨_, h1, Sym2.mem_mk_right a b⟩
      · exact (hnot a b h2 hPa).elim
    induction e using Sym2.ind with
    | h a₀ b₀ =>
      have hall := forall_mem_of_cycleEdges P hstep
        (mem_of_mem_cycleEdges he (Sym2.mem_mk_left _ _)) ⟨_, he₁, Sym2.mem_mk_left _ _⟩
      intro e' he'
      induction e' using Sym2.ind with
      | h a b =>
        rcases ho _ he' with h1 | h2
        · exact h1
        · exact (hnot a b h2 (hall a (mem_of_mem_cycleEdges he' (Sym2.mem_mk_left _ _)))).elim

/-! ### `fnum`: optimal decompositions -/

section Fnum

variable {F F₁ F₂ : Finset (Sym2 V)} {D : List (Obj V)}

/-- The non-loop part of a loopless edge set is the set itself. -/
theorem coe_sdiff_diagSet_of_loopless (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (F : Set (Sym2 V)) \ Sym2.diagSet = F := by
  ext e
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  exact ⟨And.left, fun h => ⟨h, hF e h⟩⟩

/-- The single non-loop edges of `F` decompose the non-loop part of `F`. -/
theorem exists_isDecomp_sdiff_diagSet (F : Finset (Sym2 V)) :
    ∃ D : List (Obj V), IsDecomp ((F : Set (Sym2 V)) \ Sym2.diagSet) D ∧ D.length ≤ F.card := by
  classical
  refine ⟨(F.filter fun e => ¬ e.IsDiag).toList.map Obj.edge, ?_, ?_⟩
  · refine (isDecomp_singletons _ (fun e he => (Finset.mem_filter.1 he).2)).congr ?_
    ext e; simp
  · rw [length_singletons]; exact Finset.card_filter_le _ _

/-- The minimum defining `fnum F` is attained. -/
theorem fnum_spec (F : Finset (Sym2 V)) :
    ∃ D : List (Obj V), IsDecomp ((F : Set (Sym2 V)) \ Sym2.diagSet) D ∧ D.length = fnum F := by
  obtain ⟨D, hD, -⟩ := exists_isDecomp_sdiff_diagSet F
  exact Nat.sInf_mem (s := {k | ∃ D : List (Obj V),
    IsDecomp ((F : Set (Sym2 V)) \ Sym2.diagSet) D ∧ D.length = k}) ⟨D.length, D, hD, rfl⟩

theorem fnum_le_length (h : IsDecomp ((F : Set (Sym2 V)) \ Sym2.diagSet) D) :
    fnum F ≤ D.length :=
  Nat.sInf_le ⟨D, h, rfl⟩

/-- A lower bound for `fnum F` from a lower bound on all decompositions of its non-loop part. -/
theorem le_fnum {k : ℕ}
    (h : ∀ D : List (Obj V), IsDecomp ((F : Set (Sym2 V)) \ Sym2.diagSet) D → k ≤ D.length) :
    k ≤ fnum F := by
  obtain ⟨D, hD, hlen⟩ := fnum_spec F
  exact hlen ▸ h D hD

/-- A decomposable edge set is loopless. -/
theorem loopless_of_isDecomp (h : IsDecomp (F : Set (Sym2 V)) D) : ∀ e ∈ F, ¬ e.IsDiag :=
  fun _ he => h.not_isDiag (Finset.mem_coe.2 he)

/-- Any decomposition of `F` bounds `f(F)` from above. -/
theorem fnum_le_of_isDecomp (h : IsDecomp (F : Set (Sym2 V)) D) : fnum F ≤ D.length :=
  fnum_le_length (h.congr (coe_sdiff_diagSet_of_loopless (loopless_of_isDecomp h)).symm)

/-- Existence of an optimal decomposition of a loopless edge set. -/
theorem exists_isDecomp_length_eq_fnum (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    ∃ D : List (Obj V), IsDecomp (F : Set (Sym2 V)) D ∧ D.length = fnum F := by
  obtain ⟨D, hD, hlen⟩ := fnum_spec F
  exact ⟨D, hD.congr (coe_sdiff_diagSet_of_loopless hF), hlen⟩

/-- [s1:defObject] for loopless `F`: `f(F) ≤ k` iff `F` has a decomposition into at most `k`
objects. -/
theorem fnum_le_iff (hF : ∀ e ∈ F, ¬ e.IsDiag) {k : ℕ} :
    fnum F ≤ k ↔ ∃ D : List (Obj V), IsDecomp (F : Set (Sym2 V)) D ∧ D.length ≤ k := by
  constructor
  · intro h
    obtain ⟨D, hD, hlen⟩ := exists_isDecomp_length_eq_fnum hF
    exact ⟨D, hD, hlen ▸ h⟩
  · rintro ⟨D, hD, hle⟩
    exact (fnum_le_of_isDecomp hD).trans hle

/-- [s1:defObject] for loopless `F`: `k ≤ f(F)` iff every decomposition of `F` has at least `k`
objects. -/
theorem le_fnum_iff (hF : ∀ e ∈ F, ¬ e.IsDiag) {k : ℕ} :
    k ≤ fnum F ↔ ∀ D : List (Obj V), IsDecomp (F : Set (Sym2 V)) D → k ≤ D.length := by
  constructor
  · intro h D hD; exact h.trans (fnum_le_of_isDecomp hD)
  · intro h
    obtain ⟨D, hD, hlen⟩ := exists_isDecomp_length_eq_fnum hF
    exact hlen ▸ h D hD

/-- `fnum` only sees the non-loop edges. -/
theorem fnum_congr_sdiff_diagSet
    (h : (F₁ : Set (Sym2 V)) \ Sym2.diagSet = (F₂ : Set (Sym2 V)) \ Sym2.diagSet) :
    fnum F₁ = fnum F₂ := by
  unfold fnum; rw [h]

/-- Loops are ignored (convention of `EG/Defs/Fnum.lean`). -/
theorem fnum_filter_not_isDiag [DecidableEq V] (F : Finset (Sym2 V)) :
    fnum (F.filter fun e => ¬ e.IsDiag) = fnum F :=
  fnum_congr_sdiff_diagSet (by ext e; simp)

/-- [s1:defObject] "(so f(∅) = 0)". -/
@[simp] theorem fnum_empty : fnum (∅ : Finset (Sym2 V)) = 0 :=
  Nat.eq_zero_of_le_zero (fnum_le_of_isDecomp (D := []) (by simpa using isDecomp_nil))

/-- `f(F) = 0` iff `F` has no non-loop edge. -/
theorem fnum_eq_zero_iff : fnum F = 0 ↔ ∀ e ∈ F, e.IsDiag := by
  constructor
  · intro h e he
    by_contra hd
    obtain ⟨D, hD, hlen⟩ := fnum_spec F
    rw [h, List.length_eq_zero_iff] at hlen
    subst hlen
    have := isDecomp_nil_iff.1 hD
    have hmem : e ∈ (F : Set (Sym2 V)) \ Sym2.diagSet := ⟨he, hd⟩
    rw [this] at hmem
    exact hmem
  · intro h
    refine Nat.eq_zero_of_le_zero (fnum_le_length (D := []) (isDecomp_nil_iff.2 ?_))
    ext e
    simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet, Set.mem_empty_iff_false,
      iff_false, not_and, not_not]
    exact h e

theorem fnum_pos_iff : 0 < fnum F ↔ ∃ e ∈ F, ¬ e.IsDiag := by
  rw [Nat.pos_iff_ne_zero, Ne, fnum_eq_zero_iff]
  simp only [not_forall, exists_prop]

/-- [s1:factAdd](a) "f(F) ≤ |F| for every edge set F." (No looplessness hypothesis is needed:
loops are ignored by `fnum`.) -/
theorem fnum_le_card (F : Finset (Sym2 V)) : fnum F ≤ F.card := by
  obtain ⟨D, hD, hle⟩ := exists_isDecomp_sdiff_diagSet F
  exact (fnum_le_length hD).trans hle

/-- [s1:factAdd](b) "If F₁, F₂ are disjoint edge sets, then f(F₁ ∪ F₂) ≤ f(F₁) + f(F₂)." -/
theorem fnum_union_le [DecidableEq V] (hd : Disjoint F₁ F₂) :
    fnum (F₁ ∪ F₂) ≤ fnum F₁ + fnum F₂ := by
  obtain ⟨D₁, h₁, l₁⟩ := fnum_spec F₁
  obtain ⟨D₂, h₂, l₂⟩ := fnum_spec F₂
  have hd' : Disjoint ((F₁ : Set (Sym2 V)) \ Sym2.diagSet) ((F₂ : Set (Sym2 V)) \ Sym2.diagSet) :=
    (Finset.disjoint_coe.2 hd).mono Set.sdiff_subset Set.sdiff_subset
  have hset : ((F₁ : Set (Sym2 V)) \ Sym2.diagSet) ∪ ((F₂ : Set (Sym2 V)) \ Sym2.diagSet) =
      ((F₁ ∪ F₂ : Finset (Sym2 V)) : Set (Sym2 V)) \ Sym2.diagSet := by
    rw [Finset.coe_union, Set.union_sdiff_distrib]
  calc fnum (F₁ ∪ F₂) ≤ (D₁ ++ D₂).length := fnum_le_length ((h₁.append h₂ hd').congr hset)
    _ = fnum F₁ + fnum F₂ := by rw [List.length_append, l₁, l₂]

/-- [s1:factAdd](b), iterated (as used in s6:lemHCCglob): f is subadditive over pairwise
disjoint families of edge sets. -/
theorem fnum_biUnion_le [DecidableEq V] {ι : Type*} (s : Finset ι) (E : ι → Finset (Sym2 V))
    (hd : (s : Set ι).PairwiseDisjoint E) :
    fnum (s.biUnion E) ≤ ∑ i ∈ s, fnum (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hd' : (s : Set ι).PairwiseDisjoint E := hd.subset (by simp [Set.subset_insert])
    refine (fnum_union_le ?_).trans (Nat.add_le_add_left (ih hd') _)
    rw [Finset.disjoint_biUnion_right]
    intro j hj
    exact hd (by simp) (by simp [hj]) (fun h => hi (h ▸ hj))

/-- [s1:factAdd](c) "If H is the vertex-disjoint union of graphs H₁ and H₂, then
f(H) = f(H₁) + f(H₂)", edge-set form: no vertex is incident to an edge of `F₁` and to an edge
of `F₂`. -/
theorem fnum_union_eq_of_vertexDisjoint [DecidableEq V]
    (hvd : ∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ v ∈ e₁, v ∉ e₂) :
    fnum (F₁ ∪ F₂) = fnum F₁ + fnum F₂ := by
  have hd : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro e h₁ h₂
    induction e using Sym2.ind with
    | h a b => exact hvd _ h₁ _ h₂ a (Sym2.mem_mk_left a b) (Sym2.mem_mk_left a b)
  refine le_antisymm (fnum_union_le hd) ?_
  obtain ⟨D, hD, hlen⟩ := fnum_spec (F₁ ∪ F₂)
  rw [← hlen]
  -- every object of `D` has all its edges in `F₁` or all in `F₂`
  have hside : ∀ o ∈ D, ∀ e ∈ o.edges, e ∈ (F₁ : Set (Sym2 V)) → ∀ e' ∈ o.edges, e' ∈ F₁ := by
    intro o ho e he he₁
    refine Obj.edges_mem_of_vertexDisjoint (E₂ := (F₂ : Set (Sym2 V))) hvd (fun x hx => ?_) he he₁
    have := (hD.mem_of_mem_edges ho hx).1
    simpa using this
  let p : Obj V → Bool := fun o => o.edges.all fun e => decide (e ∈ F₁)
  have hp : ∀ o, p o = true ↔ ∀ e ∈ o.edges, e ∈ F₁ := by
    intro o; simp [p]
  have h₁ : IsDecomp ((F₁ : Set (Sym2 V)) \ Sym2.diagSet) (D.filter p) := by
    refine (hD.sublist List.filter_sublist).congr ?_
    ext e
    simp only [Set.mem_ofPred_eq, List.mem_flatMap, List.mem_filter, Set.mem_sdiff,
      Finset.mem_coe, Sym2.mem_diagSet]
    constructor
    · rintro ⟨o, ⟨ho, hpo⟩, he⟩
      exact ⟨(hp o).1 hpo e he, (hD.wf o ho).not_isDiag he⟩
    · rintro ⟨he₁, hnd⟩
      have : e ∈ ((F₁ ∪ F₂ : Finset (Sym2 V)) : Set (Sym2 V)) \ Sym2.diagSet :=
        ⟨by simp [he₁], hnd⟩
      obtain ⟨o, ho, heo⟩ := List.mem_flatMap.1 (hD.mem_iff.2 this)
      exact ⟨o, ⟨ho, (hp o).2 (hside o ho e heo he₁)⟩, heo⟩
  have h₂ : IsDecomp ((F₂ : Set (Sym2 V)) \ Sym2.diagSet) (D.filter (!p ·)) := by
    refine (hD.sublist List.filter_sublist).congr ?_
    ext e
    simp only [Set.mem_ofPred_eq, List.mem_flatMap, List.mem_filter, Set.mem_sdiff,
      Finset.mem_coe, Sym2.mem_diagSet, Bool.not_eq_true']
    constructor
    · rintro ⟨o, ⟨ho, hpo⟩, he⟩
      refine ⟨?_, (hD.wf o ho).not_isDiag he⟩
      have hmem := (hD.mem_of_mem_edges ho he).1
      rcases Finset.mem_union.1 hmem with h | h
      · have := (hp o).2 (hside o ho e he h)
        rw [hpo] at this; exact absurd this Bool.false_ne_true
      · exact h
    · rintro ⟨he₂, hnd⟩
      have : e ∈ ((F₁ ∪ F₂ : Finset (Sym2 V)) : Set (Sym2 V)) \ Sym2.diagSet :=
        ⟨by simp [he₂], hnd⟩
      obtain ⟨o, ho, heo⟩ := List.mem_flatMap.1 (hD.mem_iff.2 this)
      refine ⟨o, ⟨ho, ?_⟩, heo⟩
      cases hpo : p o
      · rfl
      · exact absurd ((hp o).1 hpo e heo) (Finset.disjoint_right.1 hd he₂)
  rw [List.length_eq_length_filter_add p]
  exact Nat.add_le_add (fnum_le_length h₁) (fnum_le_length h₂)

end Fnum


/-! ### [s1:factAdd](d): f depends only on the edge set -/

section Map

variable {F : Finset (Sym2 V)}

/-- The non-loop part commutes with relabelling along an injective map. -/
theorem coe_map_sdiff_diagSet (φ : V ↪ W) (F : Finset (Sym2 V)) :
    ((F.map φ.sym2Map : Finset (Sym2 W)) : Set (Sym2 W)) \ Sym2.diagSet =
      Sym2.map φ '' ((F : Set (Sym2 V)) \ Sym2.diagSet) := by
  ext x
  simp only [Finset.coe_map, Function.Embedding.sym2Map_apply, Set.mem_sdiff, Set.mem_image,
    Finset.mem_coe, Sym2.mem_diagSet]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hd⟩
    exact ⟨y, ⟨hy, fun h => hd ((Sym2.isDiag_map φ.injective).2 h)⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, fun h => hd ((Sym2.isDiag_map φ.injective).1 h)⟩

theorem coe_map_sym2Map (φ : V ↪ W) (F : Finset (Sym2 V)) :
    ((F.map φ.sym2Map : Finset (Sym2 W)) : Set (Sym2 W)) = Sym2.map φ '' (F : Set (Sym2 V)) := by
  rw [Finset.coe_map]
  rfl

/-- Relabelling a decomposition of a finite edge set along an embedding (finset form of
`IsDecomp.map`). -/
theorem IsDecomp.map_finset (φ : V ↪ W) {D : List (Obj V)} (h : IsDecomp (F : Set (Sym2 V)) D) :
    IsDecomp ((F.map φ.sym2Map : Finset (Sym2 W)) : Set (Sym2 W)) (D.map (Obj.map φ)) :=
  (h.map φ.injective).congr (coe_map_sym2Map φ F).symm

/-- Finset form of `isDecomp_map_iff`. -/
theorem isDecomp_map_finset_iff (φ : V ↪ W) {D : List (Obj V)} :
    IsDecomp ((F.map φ.sym2Map : Finset (Sym2 W)) : Set (Sym2 W)) (D.map (Obj.map φ)) ↔
      IsDecomp (F : Set (Sym2 V)) D := by
  rw [coe_map_sym2Map]
  exact isDecomp_map_iff φ.injective

/-- [s1:factAdd](d) "f(H) depends only on E(H)": f is invariant under relabelling the vertices
along an injective map. In particular adding isolated vertices (an embedding `V ↪ W`) or deleting
them (`fnum_edgeFinset_induce_of_support_subset`) does not change f. -/
theorem fnum_map (φ : V ↪ W) (F : Finset (Sym2 V)) : fnum (F.map φ.sym2Map) = fnum F := by
  apply le_antisymm
  · obtain ⟨D, hD, hlen⟩ := fnum_spec F
    have := hD.map φ.injective
    rw [← coe_map_sdiff_diagSet] at this
    exact (fnum_le_length this).trans (by simp [hlen])
  · apply le_fnum
    intro D' hD'
    rw [coe_map_sdiff_diagSet] at hD'
    rcases isEmpty_or_nonempty V with hV | hV
    · -- no vertices, hence no edges
      have hF : F = ∅ := Finset.eq_empty_of_forall_notMem fun e _ => (hV.elim e.out.1)
      simp [hF]
    · let g : W → V := Function.invFun φ
      -- all vertices of the objects of `D'` lie in the range of `φ`
      have hD'eq : (D'.map (Obj.map g)).map (Obj.map φ) = D' := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id D']
        refine List.map_congr_left fun o ho => ?_
        simp only [Function.comp_apply, Obj.map_map, id]
        refine (Obj.map_congr (g := fun x => x) fun e he v hv => ?_).trans (Obj.map_id' o)
        obtain ⟨y, -, rfl⟩ := hD'.mem_of_mem_edges ho he
        obtain ⟨a, -, rfl⟩ := Sym2.mem_map.1 hv
        simp [g, Function.leftInverse_invFun φ.injective a]
      rw [← hD'eq, isDecomp_map_iff φ.injective] at hD'
      exact (fnum_le_length hD').trans (by simp)

/-- [s1:factAdd](d), graph form: relabelling a graph along an embedding does not change f. -/
theorem fnum_edgeFinset_map (φ : V ↪ W) (G : SimpleGraph V) [Fintype G.edgeSet]
    [Fintype (G.map φ).edgeSet] : fnum (G.map φ).edgeFinset = fnum G.edgeFinset := by
  rw [← fnum_map φ]
  congr 1
  rw [← Finset.coe_inj, Finset.coe_map, SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset,
    SimpleGraph.edgeSet_map]

/-- [s1:factAdd](d) "Adding or deleting isolated vertices does not change f": the subgraph
induced on a vertex set containing every non-isolated vertex has the same f. -/
theorem fnum_edgeFinset_induce_of_support_subset (G : SimpleGraph V) {s : Set V}
    (h : G.support ⊆ s) [Fintype G.edgeSet] [Fintype (G.induce s).edgeSet] :
    fnum (G.induce s).edgeFinset = fnum G.edgeFinset := by
  rw [← fnum_map (Function.Embedding.subtype (· ∈ s))]
  congr 1
  rw [← Finset.coe_inj, Finset.coe_map, SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [Set.mem_image, SimpleGraph.mem_edgeSet, Function.Embedding.sym2Map_apply]
    constructor
    · rintro ⟨x, hx, hxe⟩
      induction x using Sym2.ind with
      | h a' b' =>
        rw [Sym2.map_mk, Sym2.eq_iff] at hxe
        simp only [Function.Embedding.subtype_apply] at hxe
        have hadj : G.Adj a' b' := hx
        rcases hxe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact hadj.symm
    · intro hab
      exact ⟨s(⟨a, h ⟨b, hab⟩⟩, ⟨b, h ⟨a, hab.symm⟩⟩), hab, rfl⟩

/-- [s1:factAdd](c), graph form: "If H is the vertex-disjoint union of graphs H₁ and H₂, then
f(H) = f(H₁) + f(H₂)." -/
theorem fnum_edgeFinset_sup_of_disjoint_support [DecidableEq V] (H₁ H₂ : SimpleGraph V)
    [Fintype H₁.edgeSet] [Fintype H₂.edgeSet] [Fintype (H₁ ⊔ H₂).edgeSet]
    (h : Disjoint H₁.support H₂.support) :
    fnum (H₁ ⊔ H₂).edgeFinset = fnum H₁.edgeFinset + fnum H₂.edgeFinset := by
  rw [SimpleGraph.edgeFinset_sup]
  apply fnum_union_eq_of_vertexDisjoint
  intro e₁ he₁ e₂ he₂ v hv₁ hv₂
  rw [SimpleGraph.mem_edgeFinset] at he₁ he₂
  obtain ⟨w₁, rfl⟩ := Sym2.mem_iff_exists.1 hv₁
  obtain ⟨w₂, rfl⟩ := Sym2.mem_iff_exists.1 hv₂
  exact Set.disjoint_left.1 h ⟨w₁, he₁⟩ ⟨w₂, he₂⟩

end Map

/-! ### `fmax`: the maximum of f over `n`-vertex graphs -/

section Fmax

/-- [s1:defObject] `f(H) ≤ f(n)` for every graph `H` with `n` vertices. -/
theorem fnum_le_fmax [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] {n : ℕ}
    (hn : Fintype.card V = n) : fnum G.edgeFinset ≤ fmax n := by
  classical
  subst hn
  let φ : V ↪ Fin (Fintype.card V) := (Fintype.equivFin V).toEmbedding
  rw [← fnum_edgeFinset_map φ G]
  unfold fmax
  refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun H : SimpleGraph (Fin (Fintype.card V)) =>
    fnum H.edgeFinset) (Finset.mem_univ (G.map φ)))
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]

/-- [s1:defObject] `f(n)` is attained by a graph on `Fin n` (for any choice of the `Fintype`
instance on its edge set). -/
theorem exists_fnum_eq_fmax (n : ℕ) :
    ∃ H : SimpleGraph (Fin n), ∀ [Fintype H.edgeSet], fnum H.edgeFinset = fmax n := by
  classical
  obtain ⟨H, -, hH⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (SimpleGraph (Fin n)))
    Finset.univ_nonempty (fun H : SimpleGraph (Fin n) => fnum H.edgeFinset)
  refine ⟨H, fun {_} => ?_⟩
  unfold fmax
  rw [hH]
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]

/-- [s1:factAdd](d) "In particular f(n) is non-decreasing in n." -/
theorem fmax_mono : Monotone fmax := by
  intro n m hnm
  classical
  obtain ⟨H, hH⟩ := exists_fnum_eq_fmax n
  rw [← hH]
  rw [← fnum_edgeFinset_map (Fin.castLEEmb hnm) H]
  exact fnum_le_fmax _ (Fintype.card_fin m)

end Fmax


/-! ### Graphs, special values -/

section Special

variable {F : Finset (Sym2 V)}

/-- Edge sets of simple graphs are loopless. -/
theorem loopless_edgeFinset (G : SimpleGraph V) [Fintype G.edgeSet] :
    ∀ e ∈ G.edgeFinset, ¬ e.IsDiag :=
  fun _ he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he)

/-- [s1:defObject] "f(H) := f(E(H))": an optimal decomposition of a graph. -/
theorem exists_isDecomp_edgeSet_length_eq_fnum (G : SimpleGraph V) [Fintype G.edgeSet] :
    ∃ D : List (Obj V), IsDecomp G.edgeSet D ∧ D.length = fnum G.edgeFinset := by
  obtain ⟨D, hD, hlen⟩ := exists_isDecomp_length_eq_fnum (loopless_edgeFinset G)
  exact ⟨D, hD.congr (SimpleGraph.coe_edgeFinset G), hlen⟩

/-- `f(G) ≤ k` iff the graph `G` has a decomposition into at most `k` objects. -/
theorem fnum_edgeFinset_le_iff (G : SimpleGraph V) [Fintype G.edgeSet] {k : ℕ} :
    fnum G.edgeFinset ≤ k ↔ ∃ D : List (Obj V), IsDecomp G.edgeSet D ∧ D.length ≤ k := by
  rw [fnum_le_iff (loopless_edgeFinset G), SimpleGraph.coe_edgeFinset]

/-- A single edge has f = 1. -/
theorem fnum_singleton {e : Sym2 V} (he : ¬ e.IsDiag) : fnum {e} = 1 := by
  refine le_antisymm ((fnum_le_card _).trans (by simp)) ?_
  rw [Nat.one_le_iff_ne_zero, Ne, fnum_eq_zero_iff]
  simpa using he

/-- The edge set of a cycle with at least three distinct vertices has f = 1. -/
theorem fnum_cycleEdges [DecidableEq V] {c : List V} (hc : c.Nodup) (h3 : 3 ≤ c.length) :
    fnum (cycleEdges c).toFinset = 1 := by
  refine le_antisymm ?_ ?_
  · refine (fnum_le_of_isDecomp (D := [Obj.cycle c]) ((isDecomp_cycle hc h3).congr ?_)).trans
      (by simp)
    ext e; simp
  · rw [Nat.one_le_iff_ne_zero, Ne, fnum_eq_zero_iff]
    intro h
    have hmem : s(c[0], c[1]) ∈ cycleEdges c := mk_mem_cycleEdges 0 (by omega)
    exact not_isDiag_of_mem_cycleEdges hc (by omega) hmem (h _ (List.mem_toFinset.2 hmem))

/-- If a decomposition consists of single edges only, its length is its number of edges. -/
theorem length_flatMap_edges_of_forall_edge {D : List (Obj V)}
    (h : ∀ o ∈ D, ∃ e, o = Obj.edge e) : (D.flatMap Obj.edges).length = D.length := by
  induction D with
  | nil => simp
  | cons o D ih =>
    obtain ⟨e, rfl⟩ := h o (by simp)
    simp [ih (fun o' ho' => h o' (by simp [ho']))]

/-- If no cycle (with at least three distinct vertices) has all its edges in the loopless edge
set `F`, then `f(F) = |F|`. -/
theorem fnum_eq_card_of_no_cycle (hF : ∀ e ∈ F, ¬ e.IsDiag)
    (hc : ∀ c : List V, c.Nodup → 3 ≤ c.length → ¬ ∀ e ∈ cycleEdges c, e ∈ F) :
    fnum F = F.card := by
  refine le_antisymm (fnum_le_card F) ?_
  rw [le_fnum_iff hF]
  intro D hD
  have hedge : ∀ o ∈ D, ∃ e, o = Obj.edge e := by
    intro o ho
    cases o with
    | edge e => exact ⟨e, rfl⟩
    | cycle c =>
      exact (hc c (hD.wf _ ho).1 (hD.wf _ ho).2
        (fun e he => Finset.mem_coe.1 (hD.mem_of_mem_edges ho he))).elim
  rw [← hD.length_flatMap, length_flatMap_edges_of_forall_edge hedge]

/-- A star (a loopless edge set whose edges share a common vertex `v₀`) has `f = |F|`. -/
theorem fnum_eq_card_of_forall_mem {v₀ : V} (hF : ∀ e ∈ F, ¬ e.IsDiag) (hv : ∀ e ∈ F, v₀ ∈ e) :
    fnum F = F.card := by
  refine fnum_eq_card_of_no_cycle hF fun c hc h3 hall => ?_
  have h01 := hv _ (hall _ (mk_mem_cycleEdges (c := c) 0 (by omega)))
  have h12 := hv _ (hall _ (mk_mem_cycleEdges (c := c) 1 (by omega)))
  have h2 := hv _ (hall _ (mem_cycleEdges.2 ⟨2, by omega, rfl⟩))
  simp only [Nat.reduceAdd, Sym2.mem_iff] at h01 h12 h2
  have hne : ∀ {i j : ℕ} (hi : i < c.length) (hj : j < c.length), c[i] = c[j] → i = j :=
    fun _ _ h => (hc.getElem_inj_iff).1 h
  have h3' : 3 % c.length ≠ 1 := by
    rcases Nat.eq_or_lt_of_le h3 with h | h
    · rw [← h]; decide
    · rw [Nat.mod_eq_of_lt h]; decide
  rcases h01 with h01 | h01 <;> rcases h12 with h12 | h12 <;> subst v₀
  · exact absurd (hne _ _ h12) (by omega)
  · exact absurd (hne _ _ h12) (by omega)
  · rcases h2 with h2 | h2
    · exact absurd (hne _ _ h2) (by omega)
    · exact h3' (hne _ _ h2).symm
  · exact absurd (hne _ _ h12) (by omega)

end Special

end EG
