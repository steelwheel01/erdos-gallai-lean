module

public import EG.Lib.Vortex.Ends

/-!
# Stripping in the PV finish (manuscript s4:lemPV, proof, "Finish"; CR1-PV)

Unit P4A, stage 3. `EG.strip_exists`: a path `T` with all vertices in `Rt ⊔ Pl_J` and every edge
meeting `Rt` loses the edge at each end in `Pl_J`; what remains has at most one vertex or is a
path with both ends in `Rt`.
-/

public section

namespace EG

open List

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem other_mem_of_edge {Rt PlJ : Finset V} (hdis : Disjoint Rt PlJ) {a c : V}
    (ha : a ∈ PlJ) (h : ∃ x ∈ Rt, x ∈ s(a, c)) : c ∈ Rt := by
  obtain ⟨x, hx, hxe⟩ := h
  rcases Sym2.mem_iff.1 hxe with rfl | rfl
  · exact absurd ha (Finset.disjoint_left.1 hdis hx)
  · exact hx

/-- The stripping conclusion for the path `T`. -/
@[expose] def StripOut (Rt PlJ : Finset V) (T : List V) (S : List (Sym2 V)) (T' : List V) :
    Prop :=
  List.Perm (S ++ walkEdges T') (walkEdges T) ∧
    S.length ≤ (PlJ.filter fun p => T.head? = some p ∨ T.getLast? = some p).card ∧
    T'.IsInfix T ∧
    (T'.length ≤ 1 ∨
      (2 ≤ T'.length ∧ (∃ x ∈ Rt, T'.head? = some x) ∧ ∃ y ∈ Rt, T'.getLast? = some y))

theorem strip_exists {Rt PlJ : Finset V} {T : List V} (hdis : Disjoint Rt PlJ) (hT : T.Nodup)
    (h2 : 2 ≤ T.length) (hV : ∀ x ∈ T, x ∈ Rt ∪ PlJ)
    (hE : ∀ e ∈ walkEdges T, ∃ x ∈ Rt, x ∈ e) : ∃ S T', StripOut Rt PlJ T S T' := by
  -- `T = a :: K`, `K = M ++ [b]`
  obtain ⟨a, K, rfl⟩ : ∃ a K, T = a :: K := by
    cases T with
    | nil => simp at h2
    | cons a K => exact ⟨a, K, rfl⟩
  have hK : K ≠ [] := by rintro rfl; simp at h2
  obtain ⟨M, b, hMb⟩ := List.eq_nil_or_concat K |>.resolve_left hK
  rw [List.concat_eq_append] at hMb
  subst hMb
  have hmemRP : ∀ x ∈ a :: (M ++ [b]), x ∈ Rt ∨ x ∈ PlJ := fun x hx =>
    Finset.mem_union.1 (hV x hx)
  have hlastT : (a :: (M ++ [b])).getLast? = some b := by
    rw [← List.cons_append, List.getLast?_concat]
  have hheadT : (a :: (M ++ [b])).head? = some a := rfl
  have hab : a ≠ b := by
    intro h
    subst h
    exact (List.nodup_cons.1 hT).1 (by simp)
  have hmemF : ∀ p, p ∈ PlJ → (p = a ∨ p = b) →
      p ∈ PlJ.filter fun p => (a :: (M ++ [b])).head? = some p ∨
        (a :: (M ++ [b])).getLast? = some p := by
    intro p hp hpab
    rw [Finset.mem_filter, hheadT, hlastT]
    rcases hpab with rfl | rfl <;> simp [hp]
  -- the first edge
  have hfirst : ∃ c r, M ++ [b] = c :: r := by
    cases M with
    | nil => exact ⟨b, [], rfl⟩
    | cons c r => exact ⟨c, r ++ [b], rfl⟩
  obtain ⟨c, r, hcr⟩ := hfirst
  have hwe1 : walkEdges (a :: (M ++ [b])) = s(a, c) :: walkEdges (M ++ [b]) := by
    rw [hcr, walkEdges_cons_cons]
  -- the last edge
  have hwe2 : ∀ d, (a :: M).getLast? = some d →
      walkEdges (a :: (M ++ [b])) = walkEdges (a :: M) ++ [s(d, b)] := by
    intro d hd
    rw [← List.cons_append, walkEdges_concat, hd]
    rfl
  obtain ⟨d, hd⟩ : ∃ d, (a :: M).getLast? = some d := by
    cases h : (a :: M).getLast? with
    | none => simp at h
    | some d => exact ⟨d, rfl⟩
  have hacE : s(a, c) ∈ walkEdges (a :: (M ++ [b])) := by rw [hwe1]; simp
  have hdbE : s(d, b) ∈ walkEdges (a :: (M ++ [b])) := by rw [hwe2 d hd]; simp
  by_cases haP : a ∈ PlJ <;> by_cases hbP : b ∈ PlJ
  · -- both ends stripped: `T' = M`
    have hM : M ≠ [] := by
      rintro rfl
      obtain ⟨x, hx, hxe⟩ := hE _ hacE
      simp only [List.nil_append, List.cons.injEq] at hcr
      obtain ⟨rfl, rfl⟩ := hcr
      rcases Sym2.mem_iff.1 hxe with rfl | rfl
      · exact Finset.disjoint_left.1 hdis hx haP
      · exact Finset.disjoint_left.1 hdis hx hbP
    have hcM : M.head? = some c := by
      cases M with
      | nil => exact absurd rfl hM
      | cons m M => simp only [List.cons_append, List.cons.injEq] at hcr; simp [hcr.1]
    have hdM : M.getLast? = some d := by
      cases M with
      | nil => exact absurd rfl hM
      | cons m M => rwa [List.getLast?_cons_cons] at hd
    refine ⟨[s(a, c), s(d, b)], M, ?_, ?_, ?_, ?_⟩
    · have e1 : walkEdges (M ++ [b]) = walkEdges M ++ [s(d, b)] := by
        rw [walkEdges_concat, hdM]; rfl
      rw [hwe1, e1]
      simp only [List.cons_append]
      exact ((List.perm_append_comm (l₁ := [s(d, b)]) (l₂ := walkEdges M))).cons _
    · have hsub : ({a, b} : Finset V) ⊆ PlJ.filter fun p => (a :: (M ++ [b])).head? = some p ∨
          (a :: (M ++ [b])).getLast? = some p := by
        intro p hp
        rw [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hmemF p haP (Or.inl rfl)
        · exact hmemF p hbP (Or.inr rfl)
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hab] at this
      simpa using this
    · exact ⟨[a], [b], by simp⟩
    · by_cases hl : M.length ≤ 1
      · exact Or.inl hl
      · refine Or.inr ⟨by omega, ⟨c, other_mem_of_edge hdis haP (hE _ hacE), hcM⟩, d, ?_, hdM⟩
        have h' := hE _ hdbE
        rw [Sym2.eq_swap] at h'
        exact other_mem_of_edge hdis hbP h'
  · -- only the first end stripped: `T' = M ++ [b]`
    have hbR : b ∈ Rt := (hmemRP b (by simp)).resolve_right hbP
    refine ⟨[s(a, c)], M ++ [b], ?_, ?_, ?_, ?_⟩
    · rw [hwe1]; simp
    · have := Finset.card_pos.2 ⟨a, hmemF a haP (Or.inl rfl)⟩
      simpa using this
    · exact ⟨[a], [], by simp⟩
    · by_cases hl : (M ++ [b]).length ≤ 1
      · exact Or.inl hl
      · refine Or.inr ⟨by omega, ⟨c, other_mem_of_edge hdis haP (hE _ hacE), by rw [hcr]; rfl⟩,
          b, hbR, List.getLast?_concat ..⟩
  · -- only the last end stripped: `T' = a :: M`
    have haR : a ∈ Rt := (hmemRP a (by simp)).resolve_right haP
    refine ⟨[s(d, b)], a :: M, ?_, ?_, ?_, ?_⟩
    · rw [hwe2 d hd]; exact List.perm_append_comm
    · have := Finset.card_pos.2 ⟨b, hmemF b hbP (Or.inr rfl)⟩
      simpa using this
    · exact ⟨[], [b], by simp⟩
    · by_cases hl : (a :: M).length ≤ 1
      · exact Or.inl hl
      · refine Or.inr ⟨by omega, ⟨a, haR, rfl⟩, d, ?_, hd⟩
        have h' := hE _ hdbE
        rw [Sym2.eq_swap] at h'
        exact other_mem_of_edge hdis hbP h'
  · -- nothing stripped
    have haR : a ∈ Rt := (hmemRP a (by simp)).resolve_right haP
    have hbR : b ∈ Rt := (hmemRP b (by simp)).resolve_right hbP
    refine ⟨[], a :: (M ++ [b]), by simp, by simp, List.infix_refl _, Or.inr ⟨h2, ⟨a, haR, rfl⟩,
      b, hbR, hlastT⟩⟩

end EG
