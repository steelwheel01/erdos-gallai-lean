module

public import EG.Defs.Quot.Schedule
public import EG.Lib.Prob.Basic

/-!
# API for the round randomness (s7:defSchedule)

The orders `≺_u` as rank lists (`sortByRank`, `inOrder`), the law of a `3`-subset, and the
readers `etaAt`, `zetaAt`. Design note: `formal/work/p2d/quot.md`.
-/

public section

namespace EG.Quot

variable {V : Type*} [DecidableEq V] {G : FGraph V}

theorem mem_sortByRank (o : ↥G.verts ≃ Fin G.card) (C : Finset V) (v : V) :
    v ∈ sortByRank o C ↔ v ∈ C ∧ v ∈ G.verts := by
  simp only [sortByRank, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h
    · cases hi
      exact ⟨h, (o.symm i).2⟩
  · rintro ⟨hC, hv⟩
    refine ⟨o ⟨v, hv⟩, ?_⟩
    simp [hC]

theorem nodup_sortByRank (o : ↥G.verts ≃ Fin G.card) (C : Finset V) :
    (sortByRank o C).Nodup := by
  unfold sortByRank
  refine List.Nodup.filterMap ?_ (List.nodup_finRange _)
  intro i j b hi hj
  split_ifs at hi hj
  · simp only [Option.mem_def, Option.some.injEq] at hi hj
    exact o.symm.injective (Subtype.ext (hi.trans hj.symm))
  all_goals simp at hi hj

/-- The list `w_1 ≺_u w_2 ≺_u ⋯` consists of the elements of `C ∩ V(G)` (for `u ∈ V(G)`). -/
theorem mem_inOrder {O : Orders G} {u : V} (hu : u ∈ G.verts) (C : Finset V) (v : V) :
    v ∈ inOrder O u C ↔ v ∈ C ∧ v ∈ G.verts := by
  simp [inOrder, hu, mem_sortByRank]

theorem nodup_inOrder (O : Orders G) (u : V) (C : Finset V) : (inOrder O u C).Nodup := by
  unfold inOrder
  split_ifs
  · exact nodup_sortByRank _ _
  · exact List.nodup_nil

/-- For `C ⊆ V(G)`, the list `w_1 ≺_u w_2 ≺_u ⋯` has `|C|` elements. -/
theorem length_inOrder {O : Orders G} {u : V} (hu : u ∈ G.verts) {C : Finset V}
    (hC : C ⊆ G.verts) : (inOrder O u C).length = C.card := by
  have hnd := nodup_inOrder O u C
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext v
  simp only [List.mem_toFinset, mem_inOrder hu]
  exact ⟨fun h => h.1, fun h => ⟨h, hC h⟩⟩

theorem etaAt_of_mem {M : ℕ} (L : Lists G M) {h : V} (hh : h ∈ G.verts) :
    etaAt L h = L.1 ⟨h, hh⟩ := by
  simp [etaAt, hh]

theorem zetaAt_of_mem {M : ℕ} (L : Lists G M) {h u : V} (hh : h ∈ G.verts)
    (hu : u ∈ G.verts) : zetaAt L h u = L.2 (⟨h, hh⟩, ⟨u, hu⟩) := by
  simp [zetaAt, hh, hu]

/-- The law of `ζ` is supported on `3`-subsets (for `K ≥ 3`). -/
theorem card_of_mem_supp_subset3Law {K : ℕ} (hK : 3 ≤ K) {s : Finset (Fin K)}
    (hs : s ∈ (subset3Law K).supp) : s.card = 3 := by
  rw [FinDist.mem_supp] at hs
  unfold subset3Law at hs
  rw [dif_pos hK] at hs
  by_contra hne
  apply hs
  simp only [FinDist.map, FinDist.prob]
  refine Finset.sum_eq_zero fun t _ => Set.indicator_of_notMem ?_ _
  intro ht
  exact hne (by rw [← Set.mem_singleton_iff.1 (Set.mem_preimage.1 ht)]; exact t.2)

end EG.Quot
