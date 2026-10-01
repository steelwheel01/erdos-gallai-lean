module

public import EG.Spec.Light.ParentSteps
public import EG.Proof.Found.EulerMulti
public import EG.Lib.Light.Euler
public import Mathlib.Data.List.Nodup
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Proof of Steps 2–3 of Lemma parent side (s5:lemParent: quotient multigraph, `T`-join, Euler)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.arcClassEuler`
(`ArcClassEulerStatement`).

Manuscript v6.1, `s5.tex`, proof of [s5:lemParent], Step 3: "there is a set `𝒯_i ⊆ E(𝓕_i)` in
which every vertex has odd degree iff it lies in `Odd_i`. Then all degrees of `UQ_{l,c,i} − 𝒯_i`
are even, and `|𝒯_i| ≤ |E(𝓕_i)| ≤ ν_l − 1`. … Every component of `UQ_{l,c,i} − 𝒯_i` that has an
edge is connected with all degrees even, so it has a closed Euler trail (Cited result
s1:citEuler …). This gives at most `ν_l` closed trails for class `i`, which together use every edge
of `UQ_{l,c,i} − 𝒯_i` exactly once."

The `T`-join is `EG.MTrail.exists_even_complement` (`EG/Lib/Light/Euler.lean`, a self-contained
minimality/pigeonhole argument instead of the spanning-forest `T`-join of [s1:citEuler] (a); the
declared input `EG.eulerTreeTJoin` is not used). The Euler trails of the components are the declared
input `EG.eulerMulti` ([s1:citEuler] (b)); the components are the reachability classes of the
nodes, at most `|Nd|` of them. Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.MTrail

namespace ArcEulerAux

variable {ι β : Type*} [DecidableEq ι] [DecidableEq β]

/-- The node class of `x` in the adjacency graph of `F`. -/
noncomputable def comp (F : Finset ι) (E : ι → β × β) (Nd : Finset β) (x : β) : Finset β := by
  classical exact Nd.filter fun y => (mAdj F E).Reachable x y

theorem mem_comp {F : Finset ι} {E : ι → β × β} {Nd : Finset β} {x y : β} :
    y ∈ comp F E Nd x ↔ y ∈ Nd ∧ (mAdj F E).Reachable x y := by
  classical
  unfold comp
  rw [Finset.mem_filter]

theorem comp_eq {F : Finset ι} {E : ι → β × β} {Nd : Finset β} {x y : β}
    (h : y ∈ comp F E Nd x) : comp F E Nd y = comp F E Nd x := by
  ext z
  rw [mem_comp, mem_comp]
  have hxy := (mem_comp.1 h).2
  exact ⟨fun ⟨hz, hr⟩ => ⟨hz, hxy.trans hr⟩, fun ⟨hz, hr⟩ => ⟨hz, hxy.symm.trans hr⟩⟩

theorem reachable_ends {F : Finset ι} {E : ι → β × β} {e : ι} (he : e ∈ F) :
    (mAdj F E).Reachable (E e).1 (E e).2 := by
  by_cases h : (E e).1 = (E e).2
  · rw [h]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2
      ⟨h, Or.inl ⟨e, he, rfl⟩⟩)

/-- A walk of the adjacency graph of `F` starting in the class `K` lifts to the adjacency graph of
the edges of `F` with first end in `K`. -/
theorem reachable_restrict {F : Finset ι} {E : ι → β × β} {Nd : Finset β}
    (hF : ∀ e ∈ F, (E e).1 ∈ Nd ∧ (E e).2 ∈ Nd) (x0 : β) :
    ∀ {x y : β} (p : (mAdj F E).Walk x y), x ∈ comp F E Nd x0 →
      (mAdj (F.filter fun e => (E e).1 ∈ comp F E Nd x0) E).Reachable x y
  | _, _, .nil, _ => SimpleGraph.Reachable.refl _
  | x, y, .cons (v := z) hadj p, hx => by
    obtain ⟨hne, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hadj
    have hxz : (mAdj F E).Reachable x z := hadj.reachable
    have hzN : z ∈ Nd := by
      rcases hr with ⟨e, he, hee⟩ | ⟨e, he, hee⟩
      · have := (hF e he).2; rw [hee] at this; exact this
      · have := (hF e he).1; rw [hee] at this; exact this
    have hz : z ∈ comp F E Nd x0 := mem_comp.2 ⟨hzN, (mem_comp.1 hx).2.trans hxz⟩
    refine SimpleGraph.Reachable.trans ?_ (reachable_restrict hF x0 p hz)
    refine SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, ?_⟩)
    rcases hr with ⟨e, he, hee⟩ | ⟨e, he, hee⟩
    · exact Or.inl ⟨e, Finset.mem_filter.2 ⟨he, by rw [hee]; exact hx⟩, hee⟩
    · exact Or.inr ⟨e, Finset.mem_filter.2 ⟨he, by rw [hee]; exact hz⟩, hee⟩

end ArcEulerAux

open ArcEulerAux

universe u v w

/-- [s5:lemParent] Steps 2–3: the `T`-join and the closed Euler trails of one class. -/
theorem arcClassEuler : EG.Spec.ArcClassEulerStatement.{u, v, w} := by
  intro V β ι _ _ _ A ends par Nd hA
  set E := qEnds par ends with hE
  have hA' : ∀ e ∈ A, (E e).1 ∈ Nd ∧ (E e).2 ∈ Nd := hA
  obtain ⟨T, hTA, hTcard, hev⟩ := exists_even_complement A E Nd hA'
  set F := A \ T with hFdef
  have hF : ∀ e ∈ F, (E e).1 ∈ Nd ∧ (E e).2 ∈ Nd := fun e he => hA' e (Finset.mem_sdiff.1 he).1
  classical
  -- the classes with an edge, and their edge sets
  set K : ι → Finset β := fun e => comp F E Nd (E e).1 with hK
  set Ks := F.image K with hKs
  set FK : Finset β → Finset ι := fun C => F.filter fun e => (E e).1 ∈ C with hFK
  have hself : ∀ e ∈ F, (E e).1 ∈ K e ∧ (E e).2 ∈ K e := fun e he =>
    ⟨mem_comp.2 ⟨(hF e he).1, SimpleGraph.Reachable.refl _⟩,
      mem_comp.2 ⟨(hF e he).2, reachable_ends he⟩⟩
  -- a class is the class of each of its members
  have hclass : ∀ C ∈ Ks, ∀ x ∈ C, C = comp F E Nd x := by
    intro C hC x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hC
    exact (comp_eq hx).symm
  -- every class has a closed Euler trail
  have htrail : ∀ C ∈ Ks, ∃ W : List (ι × Bool), IsClosedTrail E W ∧
      ∀ a, a ∈ W.map Prod.fst ↔ a ∈ FK C := by
    intro C hC
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 hC
    refine eulerMulti.{v, w} β ι (FK (K e0)) E ⟨e0, Finset.mem_filter.2 ⟨he0, (hself e0 he0).1⟩⟩
      ?_ ?_
    · -- connected
      intro x hx y hy
      have hin : ∀ z ∈ mVerts (FK (K e0)) E, z ∈ K e0 := by
        intro z hz
        simp only [mVerts, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hz
        obtain ⟨e, he, hze⟩ := hz
        obtain ⟨heF, he1⟩ := Finset.mem_filter.1 he
        have h1 : comp F E Nd (E e).1 = K e0 := comp_eq he1
        rcases hze with rfl | rfl
        · exact he1
        · rw [← h1]; exact (hself e heF).2
      have hx0 := hin x hx
      have hy0 := hin y hy
      have hxy : (mAdj F E).Reachable x y :=
        (mem_comp.1 hx0).2.symm.trans (mem_comp.1 hy0).2
      obtain ⟨p⟩ := hxy
      exact reachable_restrict hF (E e0).1 p hx0
    · -- even degrees
      intro v
      by_cases hv : v ∈ K e0
      · have : mdeg (FK (K e0)) E v = mdeg F E v := by
          unfold mdeg
          congr 1
          · congr 1; ext e
            simp only [hFK, Finset.mem_filter]
            constructor
            · rintro ⟨⟨he, -⟩, h⟩; exact ⟨he, h⟩
            · rintro ⟨he, h⟩; exact ⟨⟨he, by rw [h]; exact hv⟩, h⟩
          · congr 1; ext e
            simp only [hFK, Finset.mem_filter]
            constructor
            · rintro ⟨⟨he, -⟩, h⟩; exact ⟨he, h⟩
            · rintro ⟨he, h⟩
              refine ⟨⟨he, ?_⟩, h⟩
              have h2 : (E e).2 ∈ K e0 := by rw [h]; exact hv
              have h3 := comp_eq h2
              have h4 : (E e).1 ∈ comp F E Nd (E e).2 :=
                mem_comp.2 ⟨(hF e he).1, (reachable_ends he).symm⟩
              rw [h3] at h4; exact h4
        rw [this]; exact hev v
      · have : mdeg (FK (K e0)) E v = 0 := by
          unfold mdeg
          rw [Finset.card_eq_zero.2, Finset.card_eq_zero.2]
          · rw [Finset.filter_eq_empty_iff]
            intro e he h2
            obtain ⟨heF, he1⟩ := Finset.mem_filter.1 he
            have h1 : comp F E Nd (E e).1 = K e0 := comp_eq he1
            apply hv; rw [← h2, ← h1]; exact (hself e heF).2
          · rw [Finset.filter_eq_empty_iff]
            intro e he h2
            exact hv (h2 ▸ (Finset.mem_filter.1 he).2)
        rw [this]; exact ⟨0, rfl⟩
  choose! Wf hWf using htrail
  refine ⟨T, Ks.toList.map Wf, hTA, hTcard, ?_, ?_, ?_, ?_⟩
  · -- at most `|Nd|` trails
    rw [List.length_map, Finset.length_toList]
    have hsub : Ks ⊆ Nd.image (comp F E Nd) := by
      intro C hC
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hC
      exact Finset.mem_image.2 ⟨(E e).1, (hF e he).1, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  · intro W hW
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hW
    exact (hWf C (Finset.mem_toList.1 hC)).1
  · -- no arc twice
    unfold trailEdges
    rw [List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun C hC => (hWf C (Finset.mem_toList.1 hC)).1.2.1, ?_⟩
    refine (Finset.nodup_toList Ks).pairwise_of_forall_ne fun C hC C' hC' hne => ?_
    rw [Function.onFun, List.disjoint_left]
    intro a ha ha'
    have h1 := ((hWf C (Finset.mem_toList.1 hC)).2 a).1 ha
    have h2 := ((hWf C' (Finset.mem_toList.1 hC')).2 a).1 ha'
    apply hne
    rw [hclass C (Finset.mem_toList.1 hC) _ (Finset.mem_filter.1 h1).2,
      hclass C' (Finset.mem_toList.1 hC') _ (Finset.mem_filter.1 h2).2]
  · intro a
    unfold trailEdges
    rw [List.flatMap_map, List.mem_flatMap]
    constructor
    · rintro ⟨C, hC, ha⟩
      exact Finset.mem_sdiff.1 (Finset.mem_filter.1 (((hWf C (Finset.mem_toList.1 hC)).2 a).1 ha)).1
    · intro ha
      have haF : a ∈ F := Finset.mem_sdiff.2 ha
      refine ⟨K a, Finset.mem_toList.2 (Finset.mem_image_of_mem K haF), ?_⟩
      exact ((hWf (K a) (Finset.mem_image_of_mem K haF)).2 a).2
        (Finset.mem_filter.2 ⟨haF, (hself a haF).1⟩)

end EG
