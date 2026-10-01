module

public import EG.Lib.Quot.E2

/-!
# The quotient `Q_l`: layer edges, ranks and vertices (manuscript s7:consRound (g)) — probe P-1,
stage 3

* `qEdge_map`: the `Q`-edge of a layer edge in the sub-layer of rank `ι'` is the one of rank `ι`
  re-tagged, so a `Q`-edge determines its rank and the rank-`0` class of its layer edge;
* `qEdge_par_iff`, `qEdge_hub_iff`: the shape of the `Q`-edge of a PAR object / hub item;
* `rank_eq_rankIn`, `rank_inj` ("By the definition of ranks, a sub-layer contains at most one edge
  of rank `ι` between any two vertices", [s7:lemSimple] proof);
* `layerOf_spec`: the layer edge chosen for a `Q`-edge produces it, and it is the only one.
-/

public section

namespace EG.Quot

open Finset

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

/-- Decidable equality of optional `Q`-edges (the instance found by `decide` in `Rules.rank`;
`DecidableEq (Option _)` is not found by instance search here). -/
@[expose, reducible] def decEqOptQEdge : DecidableEq (Option (Sym2 (QVert V))) := fun a b => inferInstance

/-- Re-tag a quotient vertex with the rank `ι`. -/
@[expose] def setRank (ι : ℕ) (x : QVert V) : QVert V := ((x.1.1, x.1.2.1, ι, x.1.2.2.2), x.2)

namespace Rules

theorem qEdge_map (ξ : Xi I.G I.M) (ι ι' : ℕ) (e : LayerEdge V) :
    R.qEdge ξ ι' e = (R.qEdge ξ ι e).map (Sym2.map (setRank ι')) := by
  rcases e with o | it
  · simp only [qEdge]
    split
    · split_ifs <;> simp [setRank, parTag]
    · rfl
  · simp only [qEdge]
    split
    · simp [setRank, hubTag]
    · rfl

theorem qEdge_par_iff {ξ : Xi I.G I.M} {ι : ℕ} {o : ParObj V} {q : Sym2 (QVert V)} :
    R.qEdge ξ ι (.inl o) = some q ↔ ∃ κ w₁ w₂, R.parColour o = some κ ∧
      R.junction ξ (.par o false) = some w₁ ∧ R.junction ξ (.par o true) = some w₂ ∧ w₁ ≠ w₂ ∧
      q = s((parTag κ ι, w₁), (parTag κ ι, w₂)) := by
  simp only [qEdge]
  constructor
  · intro h
    split at h
    · rename_i κ w₁ w₂ h1 h2 h3
      split_ifs at h with hw
      cases h
      exact ⟨κ, w₁, w₂, h1, h2, h3, hw, rfl⟩
    · cases h
  · rintro ⟨κ, w₁, w₂, h1, h2, h3, hw, rfl⟩
    rw [h1, h2, h3]
    simp [hw]

theorem qEdge_hub_iff {ξ : Xi I.G I.M} {ι : ℕ} {it : V × V} {q : Sym2 (QVert V)} :
    R.qEdge ξ ι (.inr it) = some q ↔ ∃ κ w, R.hubColour ξ.1 it = some κ ∧
      R.junction ξ (.hub it.1 it.2) = some w ∧
      q = s((hubTag κ ι true, it.1), (hubTag κ ι false, w)) := by
  simp only [qEdge]
  constructor
  · intro h
    split at h
    · rename_i κ w h1 h2
      cases h
      exact ⟨κ, w, h1, h2, rfl⟩
    · cases h
  · rintro ⟨κ, w, h1, h2, rfl⟩
    rw [h1, h2]

/-- Every end of the `Q`-edge of rank `ι` has rank `ι`. -/
theorem rank_of_mem_qEdge {ξ : Xi I.G I.M} {ι : ℕ} {e : LayerEdge V} {q : Sym2 (QVert V)}
    (h : R.qEdge ξ ι e = some q) {x : QVert V} (hx : x ∈ q) : x.1.2.2.1 = ι := by
  rcases e with o | it
  · obtain ⟨κ, w₁, w₂, -, -, -, -, rfl⟩ := qEdge_par_iff.1 h
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rfl
  · obtain ⟨κ, w, -, -, rfl⟩ := qEdge_hub_iff.1 h
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rfl

/-- A `Q`-edge determines the rank and the rank-`0` class of the layer edges producing it. -/
theorem qEdge_same {ξ : Xi I.G I.M} {ι ι' : ℕ} {e e' : LayerEdge V} {q : Sym2 (QVert V)}
    (h : R.qEdge ξ ι e = some q) (h' : R.qEdge ξ ι' e' = some q) :
    ι = ι' ∧ R.qEdge ξ 0 e = R.qEdge ξ 0 e' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ : ∃ x, x ∈ q := ⟨q.out.1, Sym2.out_fst_mem q⟩
    rw [← rank_of_mem_qEdge h hx, rank_of_mem_qEdge h' hx]
  · rw [qEdge_map ξ ι 0 e, qEdge_map ξ ι' 0 e', h, h']

theorem rank_eq_rankIn (ξ : Xi I.G I.M) (e : LayerEdge V) :
    R.rank ξ e = @rankIn _ _ _ decEqOptQEdge (R.rankOrder ξ) (R.qEdge ξ 0) e := rfl

/-- [s7:lemSimple] "no parallel edges": two layer edges that give the same edge of `Q_l`, each in
the sub-layer of its rank, are equal. -/
theorem rank_inj (hR : R.Valid) {ξ : Xi I.G I.M} {e e' : LayerEdge V} (he : e ∈ R.layerEdges ξ)
    (he' : e' ∈ R.layerEdges ξ) {q : Sym2 (QVert V)} (h : R.qEdge ξ (R.rank ξ e) e = some q)
    (h' : R.qEdge ξ (R.rank ξ e') e' = some q) : e = e' := by
  obtain ⟨hr, h0⟩ := qEdge_same h h'
  have hmem : ∀ x ∈ R.layerEdges ξ, x ∈ R.rankOrder ξ := fun x hx => by
    rw [← List.mem_toFinset, (hR.rankOrder ξ).2]; exact hx
  let _ := @decEqOptQEdge V _
  exact rankIn_inj (hR.rankOrder ξ).1 (R.qEdge ξ 0) (hmem e he) (hmem e' he') h0 hr

theorem mem_layerEdges {ξ : Xi I.G I.M} {e : LayerEdge V} :
    e ∈ R.layerEdges ξ ↔ (∃ o ∈ R.unpaidPar ξ, e = .inl o) ∨
      (∃ it ∈ R.colouredHub ξ.1, e = .inr it) := by
  simp [layerEdges, eq_comm]

theorem inl_mem_layerEdges {ξ : Xi I.G I.M} {o : ParObj V} :
    Sum.inl o ∈ R.layerEdges ξ ↔ o ∈ R.unpaidPar ξ := by
  simp [layerEdges]

theorem inr_mem_layerEdges {ξ : Xi I.G I.M} {it : V × V} :
    Sum.inr it ∈ R.layerEdges ξ ↔ it ∈ R.colouredHub ξ.1 := by
  simp [layerEdges]

theorem mem_unpaidPar {ξ : Xi I.G I.M} {o : ParObj V} :
    o ∈ R.unpaidPar ξ ↔ o ∈ R.parObjs ∧ ¬ R.Looped ξ o := by
  classical
  unfold unpaidPar
  rw [Finset.mem_filter]

omit [DecidableEq V] in
theorem exists_head?_toList {α : Type*} {s : Finset α} {a : α} (ha : a ∈ s) :
    ∃ b, s.toList.head? = some b := by
  have hne : s.toList ≠ [] := by
    rw [ne_eq, Finset.toList_eq_nil, ← ne_eq, ← Finset.nonempty_iff_ne_empty]
    exact ⟨a, ha⟩
  obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨b, by rw [hbl]; rfl⟩

/-- The layer edge chosen for a `Q`-edge produces it. -/
theorem layerOf_spec {ξ : Xi I.G I.M} {q : Sym2 (QVert V)} {e : LayerEdge V}
    (h : R.layerOf ξ q = some e) : e ∈ R.layerEdges ξ ∧ R.qEdge ξ (R.rank ξ e) e = some q := by
  classical
  unfold layerOf at h
  exact Finset.mem_filter.1 (Finset.mem_toList.1 (List.mem_of_mem_head? h))

/-- Every edge of `Q_l` has a layer edge. -/
theorem layerOf_isSome {ξ : Xi I.G I.M} {q : Sym2 (QVert V)} (hq : q ∈ (R.Q ξ).edges) :
    ∃ e, R.layerOf ξ q = some e := by
  obtain ⟨e, he, hqe⟩ := (R.mem_qEdges).1 hq
  classical
  unfold layerOf
  exact exists_head?_toList (Finset.mem_filter.2 ⟨he, hqe⟩)

/-- Under validity the layer edge of a `Q`-edge is the unique one producing it. -/
theorem layerOf_eq (hR : R.Valid) {ξ : Xi I.G I.M} {q : Sym2 (QVert V)} {e : LayerEdge V}
    (he : e ∈ R.layerEdges ξ) (hq : R.qEdge ξ (R.rank ξ e) e = some q) :
    R.layerOf ξ q = some e := by
  have hq' : q ∈ (R.Q ξ).edges := (R.mem_qEdges).2 ⟨e, he, hq⟩
  obtain ⟨e', he'⟩ := layerOf_isSome hq'
  obtain ⟨h1, h2⟩ := layerOf_spec he'
  rw [he', rank_inj hR h1 he h2 hq]

end Rules

end EG.Quot
