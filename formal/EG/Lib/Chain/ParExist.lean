module

public import EG.Lib.Chain.ParComp

/-!
# Lemma PAR: existence of the chosen edge (manuscript s6:lemPAR)

Probe unit P2E (probe P-2, part 1), proof round 1.

"*Existence of the edge.* Let `C` be a component with at least one edge. If `C` contains a cycle,
every edge of that cycle is a non-bridge. Otherwise `C` is a tree with at least one edge; it has a
leaf, and the edge at the leaf is pendant."

Formal proof (`EG.Chain.exists_nonBridge_or_pendant`): extend a path `x x₁ … y` of `C` at its
first vertex as long as possible. If `deg(x) = 1`, the edge `xx₁` is pendant. Otherwise `x` has a
second neighbour `w ≠ x₁`; if `w` is off the path the path extends, and if `w` is on the path,
`x₁ … w x` is a walk from `x₁` to `x` avoiding `xx₁`, so `xx₁` is a non-bridge (it lies on a
cycle). Paths have at most `|V(E)|` vertices, so the extension stops.
Consequently an admissible choice `J'` exists (`EG.Chain.exists_isParChoice`).
-/

public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V]

open Classical

/-- The vertices of a walk with at least one edge are incident with an edge of `E`. -/
theorem support_subset_edgeVerts {E : Finset (Sym2 V)} {x y : V} (p : (edgeGraph E).Walk x y)
    (hp : 0 < p.length) : ∀ v ∈ p.support, v ∈ edgeVerts E := by
  induction p with
  | nil => simp at hp
  | @cons a b c hab q ih =>
    intro v hv
    rw [edgeGraph_adj] at hab
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact mem_edgeVerts.2 ⟨_, hab.1, Sym2.mem_mk_left _ _⟩
    · cases q with
      | nil =>
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
        subst hv
        exact mem_edgeVerts.2 ⟨_, hab.1, Sym2.mem_mk_right _ _⟩
      | cons h' q' => exact ih (by simp) v hv

/-- A path with at least one edge has at most `|V(E)| − 1` edges. -/
theorem length_lt_card_edgeVerts {E : Finset (Sym2 V)} {x y : V} {p : (edgeGraph E).Walk x y}
    (hpath : p.IsPath) (hp : 0 < p.length) : p.length < (edgeVerts E).card := by
  have h1 : p.support.toFinset ⊆ edgeVerts E := fun v hv =>
    support_subset_edgeVerts p hp v (List.mem_toFinset.1 hv)
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hpath.support_nodup, SimpleGraph.Walk.length_support] at h2
  omega

theorem exists_nonBridge_or_pendant_aux {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    ∀ n : ℕ, ∀ (x y : V) (p : (edgeGraph E).Walk x y), p.IsPath → 0 < p.length →
      (edgeVerts E).card - p.length = n →
      ∃ f ∈ compEdges E ((edgeGraph E).connectedComponentMk x), IsNonBridge E f ∨ IsPendant E f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y p hpath hlen hn
    cases p with
    | nil => simp at hlen
    | @cons _ x1 _ hadj q =>
      have hadj' := edgeGraph_adj.1 hadj
      set e0 := s(x, x1) with he0
      have he0C : e0 ∈ compEdges E ((edgeGraph E).connectedComponentMk x) :=
        mem_compEdges_of_mem hadj'.1 hadj'.2
      by_cases hdeg : degE E x = 1
      · exact ⟨e0, he0C, Or.inr ⟨hadj'.1, x, Sym2.mem_mk_left _ _, hdeg⟩⟩
      -- a second edge `xw` at `x`
      have he0at : e0 ∈ edgesAt E x := Finset.mem_filter.2 ⟨hadj'.1, Sym2.mem_mk_left _ _⟩
      have hcard : 1 < (edgesAt E x).card := by
        have : 0 < (edgesAt E x).card := Finset.card_pos.2 ⟨e0, he0at⟩
        unfold degE at hdeg
        omega
      obtain ⟨g, hg, hge⟩ := Finset.exists_mem_ne hcard e0
      obtain ⟨hgE, hxg⟩ := Finset.mem_filter.1 hg
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hxg |>.imp fun w h => h
      have hxw : x ≠ w := fun h => hloop _ hgE (h ▸ Sym2.mk_isDiag_iff.2 rfl)
      have hwx1 : w ≠ x1 := fun h => hge (by rw [h])
      rw [SimpleGraph.Walk.cons_isPath_iff] at hpath
      by_cases hw : w ∈ q.support
      · -- `w` on the path: `x₁ … w x` avoids `xx₁`, so `xx₁` is a non-bridge
        refine ⟨e0, he0C, Or.inl ?_⟩
        rw [he0, isNonBridge_mk_iff]
        refine ⟨hadj'.1, ?_⟩
        have hwx : (edgeGraph E).Adj w x := edgeGraph_adj.2 ⟨Sym2.eq_swap ▸ hgE, Ne.symm hxw⟩
        set r := (q.takeUntil w hw).concat hwx
        have hr : s(x, x1) ∉ r.edges := by
          intro h
          rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at h
          rcases h with h | h
          · have := (q.takeUntil w hw).fst_mem_support_of_mem_edges h
            exact hpath.2 (q.support_takeUntil_subset_support hw this)
          · rw [List.mem_singleton, Sym2.eq_iff] at h
            rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
            · exact hxw h1
            · exact hwx1 h2.symm
        exact ⟨(r.toDeleteEdge _ hr).reverse⟩
      · -- `w` off the path: extend it
        have hwx : (edgeGraph E).Adj w x := edgeGraph_adj.2 ⟨Sym2.eq_swap ▸ hgE, Ne.symm hxw⟩
        set p' := SimpleGraph.Walk.cons hwx (SimpleGraph.Walk.cons hadj q)
        have hp' : p'.IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff,
            SimpleGraph.Walk.support_cons, List.mem_cons]
          refine ⟨hpath, ?_⟩
          rintro (h | h)
          · exact hxw h.symm
          · exact hw h
        have hlen' : 0 < p'.length := by simp [p']
        have hlt := length_lt_card_edgeVerts hp' hlen'
        have hlenp' : p'.length = (SimpleGraph.Walk.cons hadj q).length + 1 := by simp [p']
        obtain ⟨f, hf, hfp⟩ := ih ((edgeVerts E).card - p'.length) (by omega) w y p' hp' hlen' rfl
        have hmk : (edgeGraph E).connectedComponentMk w = (edgeGraph E).connectedComponentMk x :=
          SimpleGraph.ConnectedComponent.eq.2 hwx.reachable
        rw [hmk] at hf
        exact ⟨f, hf, hfp⟩

/-- [s6:lemPAR] "In each odd component choose one edge that is either a non-bridge or a pendant
edge (an edge with an end of degree `1`) of that component; such an edge exists." -/
theorem exists_nonBridge_or_pendant {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    {C : (edgeGraph E).ConnectedComponent} (hC : (compEdges E C).Nonempty) :
    ∃ e ∈ compEdges E C, IsNonBridge E e ∨ IsPendant E e := by
  obtain ⟨f, hf⟩ := hC
  obtain ⟨hfE, hfC⟩ := mem_compEdges.1 hf
  induction f using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := fun h => hloop _ hfE (h ▸ Sym2.mk_isDiag_iff.2 rfl)
    have hadj : (edgeGraph E).Adj a b := edgeGraph_adj.2 ⟨hfE, hab⟩
    set p := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    have hp : p.IsPath := by
      simp only [p, SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.support_nil,
        List.mem_singleton]
      exact ⟨SimpleGraph.Walk.IsPath.nil, hab⟩
    obtain ⟨e, he, hep⟩ := exists_nonBridge_or_pendant_aux hloop _ a b p hp (by simp [p]) rfl
    rw [hfC a (Sym2.mem_mk_left a b)] at he
    exact ⟨e, he, hep⟩

/-- [s6:lemPAR] "Let `J'` be the set of chosen edges": an admissible choice exists. -/
theorem exists_isParChoice {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    ∃ J' : Finset (Sym2 V), IsParChoice E J' := by
  have hex : ∀ C ∈ oddComps E, ∃ e ∈ compEdges E C, IsNonBridge E e ∨ IsPendant E e := by
    intro C hC
    unfold oddComps at hC
    obtain ⟨-, hodd⟩ := Finset.mem_filter.1 hC
    exact exists_nonBridge_or_pendant hloop (Finset.card_pos.1 (Nat.pos_of_ne_zero fun h => by
      rw [h] at hodd; exact Nat.not_odd_zero hodd))
  choose g hgC hgP using hex
  refine ⟨(oddComps E).attach.image (fun C => g C.1 C.2), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 he
    exact compEdges_subset E _ (hgC C.1 C.2)
  · intro C hC
    have hmem : ∀ x ∈ (oddComps E).attach.image (fun C => g C.1 C.2) ∩ compEdges E C,
        ∃ hC' : C ∈ oddComps E, x = g C hC' := by
      intro x hx
      obtain ⟨hxJ, hxC⟩ := Finset.mem_inter.1 hx
      obtain ⟨⟨C', hC'⟩, -, rfl⟩ := Finset.mem_image.1 hxJ
      have hCC : C' = C := by
        by_contra hne
        exact Finset.disjoint_left.1 (disjoint_compEdges hne) (hgC C' hC') hxC
      subst hCC
      exact ⟨hC', rfl⟩
    split_ifs with hodd
    · have hC' : C ∈ oddComps E := by
        unfold oddComps
        exact Finset.mem_filter.2 ⟨hC, hodd⟩
      rw [Finset.card_eq_one]
      refine ⟨g C hC', ?_⟩
      ext x
      rw [Finset.mem_singleton]
      constructor
      · intro hx
        obtain ⟨_, rfl⟩ := hmem x hx
        rfl
      · rintro rfl
        exact Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨⟨C, hC'⟩, Finset.mem_attach _ _, rfl⟩,
          hgC C hC'⟩
    · rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨hC', -⟩ := hmem x hx
      unfold oddComps at hC'
      exact hodd (Finset.mem_filter.1 hC').2
  · intro e he
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 he
    exact hgP C.1 C.2

end EG.Chain
