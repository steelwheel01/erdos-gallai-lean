module

public import EG.Lib.Chain.ParTJoin
public import EG.Defs.Probe.P2E.Par

/-!
# Lemma PAR: components after deleting the chosen edges (manuscript s6:lemPAR)

Probe unit P2E (probe P-2, part 1), proof round 1. Let `E` be bipartite with sides `V_a, V_b`,
`J'` an admissible choice (`EG.Chain.IsParChoice`) and `E' = E ∖ J'`.
* "Even components after deletion": for every vertex `z`, the set `X(z)` of edges of `E'` with
  both ends reachable from `z` in `E'` (the edges of the component of `z` in `E'`) has even size
  (`EG.Chain.even_card_compPrime`). As in the manuscript: if the component `C` of `z` in `E`
  contains no chosen edge, nothing changes; if its chosen edge `e` is a non-bridge, `C − e` stays
  connected; if `e` is pendant with leaf `u`, then `X(u) = ∅` and for `z ≠ u` a path in `E`
  avoids `u` and hence `e`. In every case `X(z) = ∅` or `X(z) = E(C) ∖ J'`, which has
  `|E(C)| − [C odd]` edges, an even number;
* "The partition": the number of vertices `u ∈ V_a` of odd `E'`-degree reachable from `z` has the
  parity of `∑_{u ∈ V_a, z ⇝ u} deg_{E'}(u) = |X(z)|` ("Every edge of `C'` has exactly one end
  in `V_a`"), so it is even (`EG.Chain.even_card_oddVa`), and a `T`-join exists
  (`EG.exists_tJoin`).
-/

public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V]

open Classical

/-- The edges of a walk in a subgraph `H` of `edgeGraph E` starting at `z` lie in the component
of `z`. -/
theorem walk_edge_mem_compEdges {E : Finset (Sym2 V)} {H : SimpleGraph V}
    (hH : H ≤ edgeGraph E) {z w : V} (p : H.Walk z w) {f : Sym2 V} (hf : f ∈ p.edges) :
    f ∈ compEdges E ((edgeGraph E).connectedComponentMk z) := by
  rw [mem_compEdges]
  constructor
  · have h1 := p.edges_subset_edgeSet hf
    have h2 := (SimpleGraph.edgeSet_subset_edgeSet.2 hH) h1
    rw [edgeSet_edgeGraph] at h2
    exact h2.1
  · intro v hv
    induction f using Sym2.ind with
    | h a b =>
      have hvs : v ∈ p.support := by
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact p.fst_mem_support_of_mem_edges hf
        · exact p.snd_mem_support_of_mem_edges hf
      have hr : H.Reachable z v := ⟨p.takeUntil v hvs⟩
      exact (SimpleGraph.ConnectedComponent.eq.2 (hr.mono hH)).symm

omit [DecidableEq V] in
/-- A walk each of whose edges joins two `H'`-reachable vertices gives `H'`-reachability. -/
theorem reachable_of_walk_edges {H H' : SimpleGraph V} {x y : V} (p : H.Walk x y)
    (h : ∀ a b, s(a, b) ∈ p.edges → H'.Reachable a b) : H'.Reachable x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj q ih =>
    refine (h u v (by simp)).trans (ih fun a b hab => h a b ?_)
    simp [hab]

omit [DecidableEq V] in
theorem reachable_of_mem {E : Finset (Sym2 V)} {a b : V} (h : s(a, b) ∈ E) (hab : a ≠ b) :
    (edgeGraph E).Reachable a b :=
  (edgeGraph_adj.2 ⟨h, hab⟩).reachable

omit [DecidableEq V] in
/-- A vertex without edges in `E` reaches only itself. -/
theorem eq_of_reachable_of_isolated {E : Finset (Sym2 V)} {u w : V}
    (hu : ∀ x, s(u, x) ∈ E → u = x) (h : (edgeGraph E).Reachable u w) : w = u := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj q =>
    rw [edgeGraph_adj] at hadj
    exact absurd (hu _ hadj.1) hadj.2

section Bip

variable {E J' : Finset (Sym2 V)} {Va Vb : Finset V}

omit [DecidableEq V] in
theorem ne_of_bip (hVab : Disjoint Va Vb) (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b))
    {x y : V} (h : s(x, y) ∈ E) : x ≠ y := by
  obtain ⟨a, ha, b, hb, hab⟩ := hbip _ h
  intro hxy
  subst hxy
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Finset.disjoint_left.1 hVab ha hb
  · exact Finset.disjoint_left.1 hVab ha hb

/-- The edges of `E'` in the component of `z` in `E'`. -/
@[expose] noncomputable def compPrime (E J' : Finset (Sym2 V)) (z : V) : Finset (Sym2 V) :=
  (E \ J').filter (fun f => ∀ w ∈ f, (edgeGraph (E \ J')).Reachable z w)

/-- A walk of `E` avoiding `J'` gives reachability in `E'`. -/
theorem reachable_prime_of_walk (hVab : Disjoint Va Vb)
    (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) {x y : V} (p : (edgeGraph E).Walk x y)
    (h : ∀ f ∈ p.edges, f ∉ J') : (edgeGraph (E \ J')).Reachable x y := by
  refine reachable_of_walk_edges p fun a b hab => ?_
  have hE := mem_of_mem_edges_edgeGraph p hab
  exact reachable_of_mem (Finset.mem_sdiff.2 ⟨hE, h _ hab⟩) (ne_of_bip hVab hbip hE)

/-- The edges of the component `C` of `z` outside `J'` all have both ends reachable from `z` in
`E'` (the case analysis of the manuscript's "Even components after deletion"), unless `z` is the
leaf of the chosen pendant edge; in that case `E'` has no edge in the component of `z`. -/
theorem compPrime_eq (hVab : Disjoint Va Vb) (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b))
    (hJ : IsParChoice E J') (z : V) :
    compPrime E J' z = ∅ ∨
      compEdges E ((edgeGraph E).connectedComponentMk z) \ J' ⊆ compPrime E J' z := by
  set C := (edgeGraph E).connectedComponentMk z with hCdef
  -- every vertex of `C` is reachable from `z` in `E`
  have hreachC : ∀ w, (edgeGraph E).connectedComponentMk w = C → (edgeGraph E).Reachable z w :=
    fun w hw => SimpleGraph.ConnectedComponent.exact (hw.trans hCdef).symm
  -- the target inclusion, from reachability of the ends of the edges of `C ∖ J'`
  have hgoal : (∀ f ∈ compEdges E C \ J', ∀ w ∈ f, (edgeGraph (E \ J')).Reachable z w) →
      compEdges E C \ J' ⊆ compPrime E J' z := by
    intro h f hf
    unfold compPrime
    rw [Finset.mem_filter]
    obtain ⟨hfC, hfJ⟩ := Finset.mem_sdiff.1 hf
    exact ⟨Finset.mem_sdiff.2 ⟨compEdges_subset E C hfC, hfJ⟩, h f hf⟩
  by_cases hJC : J' ∩ compEdges E C = ∅
  · -- no chosen edge in `C`: every walk from `z` avoids `J'`
    right
    refine hgoal fun f hf w hw => ?_
    obtain ⟨p⟩ := hreachC w ((mem_compEdges.1 (Finset.mem_sdiff.1 hf).1).2 w hw)
    refine reachable_prime_of_walk hVab hbip p fun g hg hgJ => ?_
    have := walk_edge_mem_compEdges le_rfl p hg
    have : g ∈ J' ∩ compEdges E C := Finset.mem_inter.2 ⟨hgJ, this⟩
    rw [hJC] at this
    exact Finset.notMem_empty _ this
  · -- the chosen edge `e` of `C`
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hJC
    have hCE : C ∈ edgeComps E := by
      obtain ⟨heJ, heC⟩ := Finset.mem_inter.1 he
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeComps]
        exact ⟨a, mem_edgeVerts.2 ⟨s(a, b), (mem_compEdges.1 heC).1, Sym2.mem_mk_left a b⟩,
          (mem_compEdges.1 heC).2 a (Sym2.mem_mk_left a b)⟩
    have hcard := hJ.2.1 C hCE
    have hsingle : J' ∩ compEdges E C = {e} := by
      have hle : (J' ∩ compEdges E C).card ≤ 1 := by rw [hcard]; split_ifs <;> omega
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨he, fun x hx =>
        Finset.card_le_one.1 hle x hx e he⟩
    have hother : ∀ g ∈ compEdges E C, g ≠ e → g ∉ J' := by
      intro g hg hge hgJ
      have : g ∈ J' ∩ compEdges E C := Finset.mem_inter.2 ⟨hgJ, hg⟩
      rw [hsingle, Finset.mem_singleton] at this
      exact hge this
    obtain ⟨heJ, heC⟩ := Finset.mem_inter.1 he
    rcases hJ.2.2 e heJ with hnb | hpend
    · -- a non-bridge: its ends stay connected in `E'`
      right
      have hedge : ∀ a b, s(a, b) ∈ compEdges E C → (edgeGraph (E \ J')).Reachable a b := by
        intro a b hab
        have habE := (mem_compEdges.1 hab).1
        by_cases hae : s(a, b) = e
        · rw [← hae, isNonBridge_mk_iff] at hnb
          obtain ⟨q⟩ := hnb.2
          have ha : (edgeGraph E).connectedComponentMk a = C :=
            (mem_compEdges.1 hab).2 a (Sym2.mem_mk_left a b)
          have hle : (edgeGraph E).deleteEdges {s(a, b)} ≤ edgeGraph E :=
            SimpleGraph.deleteEdges_le _
          refine reachable_of_walk_edges q fun x y hxy => ?_
          have hxyC := walk_edge_mem_compEdges hle q hxy
          rw [ha] at hxyC
          have hne : s(x, y) ≠ s(a, b) := by
            intro h
            have := q.edges_subset_edgeSet hxy
            rw [h, SimpleGraph.edgeSet_deleteEdges] at this
            exact this.2 (Set.mem_singleton _)
          have hxyE := (mem_compEdges.1 hxyC).1
          exact reachable_of_mem (Finset.mem_sdiff.2 ⟨hxyE, hother _ hxyC (hae ▸ hne)⟩)
            (ne_of_bip hVab hbip hxyE)
        · exact reachable_of_mem (Finset.mem_sdiff.2 ⟨habE, hother _ hab hae⟩)
            (ne_of_bip hVab hbip habE)
      refine hgoal fun f hf w hw => ?_
      obtain ⟨p⟩ := hreachC w ((mem_compEdges.1 (Finset.mem_sdiff.1 hf).1).2 w hw)
      exact reachable_of_walk_edges p fun a b hab => hedge a b (walk_edge_mem_compEdges le_rfl p hab)
    · -- a pendant edge with leaf `u`
      obtain ⟨-, u, hue, hdeg⟩ := hpend
      -- the only edge of `E` at `u` is `e`
      have honly : ∀ g ∈ E, u ∈ g → g = e := by
        intro g hg hug
        have h1 : g ∈ edgesAt E u := Finset.mem_filter.2 ⟨hg, hug⟩
        have h2 : e ∈ edgesAt E u := Finset.mem_filter.2 ⟨(mem_compEdges.1 heC).1, hue⟩
        exact Finset.card_le_one.1 (by unfold degE at hdeg; omega) g h1 e h2
      by_cases hzu : z = u
      · -- `u` is isolated in `E'`, so `X(u) = ∅`
        left
        subst hzu
        apply Finset.eq_empty_of_forall_notMem
        intro f hf
        unfold compPrime at hf
        rw [Finset.mem_filter] at hf
        obtain ⟨hfE', hfr⟩ := hf
        have hiso : ∀ x, s(z, x) ∈ E \ J' → z = x := by
          intro x hx
          have := honly _ (Finset.mem_sdiff.1 hx).1 (Sym2.mem_mk_left z x)
          exact absurd (this ▸ heJ) (Finset.mem_sdiff.1 hx).2
        induction f using Sym2.ind with
        | h a b =>
          have ha := eq_of_reachable_of_isolated hiso (hfr a (Sym2.mem_mk_left a b))
          have hb := eq_of_reachable_of_isolated hiso (hfr b (Sym2.mem_mk_right a b))
          exact ne_of_bip hVab hbip (Finset.mem_sdiff.1 hfE').1 (ha.trans hb.symm)
      · right
        refine hgoal fun f hf w hw => ?_
        obtain ⟨hfC, hfJ⟩ := Finset.mem_sdiff.1 hf
        have hwu : w ≠ u := by
          rintro rfl
          exact hfJ ((honly f (mem_compEdges.1 hfC).1 hw) ▸ heJ)
        obtain ⟨q⟩ := hreachC w ((mem_compEdges.1 hfC).2 w hw)
        set p := q.bypass
        have hp : p.IsPath := q.bypass_isPath
        -- the path does not pass through `u`, hence avoids `e`
        have hcnt : p.edges.countP (fun g => u ∈ g) = 0 := by
          have hev := (hp.isTrail.even_countP_edges_iff u).2
            (fun _ => ⟨fun h => hzu h.symm, fun h => hwu h.symm⟩)
          have hle : p.edges.countP (fun g => u ∈ g) ≤ 1 := by
            rw [← degE_edges_toFinset hp.isTrail]
            rw [← hdeg]
            unfold degE edgesAt
            exact Finset.card_le_card (Finset.filter_subset_filter _ fun g hg =>
              mem_of_mem_edges_edgeGraph p (List.mem_toFinset.1 hg))
          obtain ⟨r, hr⟩ := hev
          omega
        refine reachable_prime_of_walk hVab hbip p fun g hg hgJ => ?_
        have hgC := walk_edge_mem_compEdges le_rfl p hg
        by_cases hge : g = e
        · subst hge
          have : 0 < p.edges.countP (fun g' => u ∈ g') :=
            List.countP_pos_iff.2 ⟨_, hg, by simpa using hue⟩
          omega
        · exact hother g hgC hge hgJ

/-- [s6:lemPAR] (proof) "Hence every component `C'` of `E_ab ∖ J'` that has an edge has an even
number of edges." -/
theorem even_card_compPrime (hVab : Disjoint Va Vb)
    (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) (hJ : IsParChoice E J') (z : V) :
    Even (compPrime E J' z).card := by
  set C := (edgeGraph E).connectedComponentMk z with hCdef
  have hsub : compPrime E J' z ⊆ compEdges E C \ J' := by
    intro f hf
    unfold compPrime at hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfE', hfr⟩ := hf
    obtain ⟨hfE, hfJ⟩ := Finset.mem_sdiff.1 hfE'
    refine Finset.mem_sdiff.2 ⟨mem_compEdges.2 ⟨hfE, fun w hw => ?_⟩, hfJ⟩
    have := (hfr w hw).mono (edgeGraph_mono Finset.sdiff_subset)
    exact (SimpleGraph.ConnectedComponent.eq.2 this).symm
  have heven : Even (compEdges E C \ J').card := by
    have h1 := Finset.card_sdiff_add_card_inter (compEdges E C) J'
    by_cases hC : C ∈ edgeComps E
    · have h2 := hJ.2.1 C hC
      rw [Finset.inter_comm] at h1
      rw [h2] at h1
      split_ifs at h1 with hodd
      · obtain ⟨r, hr⟩ := hodd
        exact ⟨r, by omega⟩
      · rw [Nat.not_odd_iff_even] at hodd
        rw [add_zero] at h1
        rw [h1]
        exact hodd
    · have : compEdges E C = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro f hf
        induction f using Sym2.ind with
        | h a b =>
          apply hC
          rw [mem_edgeComps]
          exact ⟨a, mem_edgeVerts.2 ⟨s(a, b), (mem_compEdges.1 hf).1, Sym2.mem_mk_left a b⟩,
            (mem_compEdges.1 hf).2 a (Sym2.mem_mk_left a b)⟩
      rw [this, Finset.empty_sdiff, Finset.card_empty]
      exact ⟨0, rfl⟩
  rcases compPrime_eq hVab hbip hJ z with h | h
  · rw [h, Finset.card_empty]; exact ⟨0, rfl⟩
  · rw [Finset.Subset.antisymm hsub h]
    exact heven

end Bip

end EG.Chain
