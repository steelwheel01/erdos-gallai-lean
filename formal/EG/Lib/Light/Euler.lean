module

public import EG.Lib.Light.Trail
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Nat.Even

/-!
# `T`-joins in multigraphs (s5:lemParent, Step 3): an even complement with few edges

Library for probe unit P4B (probe P-4, part 2), proof round 1. For a finite multigraph
`(A, ends)` (loops allowed) with all ends in a node set `Nd`, there is `T ⊆ A` with
`|T| ≤ |Nd| − 1` such that `A \ T` has all degrees even (manuscript [s5:lemParent] Step 3: "there
is a set `𝒯_i ⊆ E(𝓕_i)` in which every vertex has odd degree iff it lies in `Odd_i`. Then all
degrees of `UQ_{l,c,i} − 𝒯_i` are even, and `|𝒯_i| ≤ |E(𝓕_i)| ≤ ν_l − 1`").

Proof here (self-contained, not via [s1:citEuler] (a)): take `T` of minimal size with `A \ T` even
(`T = A` qualifies). A multigraph `T` with `|T| ≥ |Nd|` has a nonempty even sub-multigraph `C`
(pigeonhole on the `2^{|T|}` subsets of `T` and their odd-degree sets inside `Nd \ {v_0}`, of which
there are `2^{|Nd|−1}`; the symmetric difference of two subsets with the same set is even, the
degree at `v_0` by the handshake lemma); then `T \ C` is smaller, a contradiction. Design note
`formal/work/p2b/P4B.md`.
-/

public section

namespace EG.MTrail

variable {ι N : Type*} [DecidableEq ι] [DecidableEq N]

theorem mdeg_union_of_disjoint {F G : Finset ι} (h : Disjoint F G) (ends : ι → N × N) (v : N) :
    mdeg (F ∪ G) ends v = mdeg F ends v + mdeg G ends v := by
  unfold mdeg
  rw [Finset.filter_union, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h),
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]
  ring

theorem mdeg_eq_zero_of_notMem {F : Finset ι} {ends : ι → N × N} {Nd : Finset N}
    (hF : ∀ e ∈ F, (ends e).1 ∈ Nd ∧ (ends e).2 ∈ Nd) {v : N} (hv : v ∉ Nd) :
    mdeg F ends v = 0 := by
  unfold mdeg
  rw [Finset.card_eq_zero.2, Finset.card_eq_zero.2]
  · rw [Finset.filter_eq_empty_iff]; intro e he h; exact hv (h ▸ (hF e he).2)
  · rw [Finset.filter_eq_empty_iff]; intro e he h; exact hv (h ▸ (hF e he).1)

/-- Handshake: `Σ_{v ∈ Nd} deg(v) = 2|F|` (loops counted twice). -/
theorem sum_mdeg {F : Finset ι} {ends : ι → N × N} {Nd : Finset N}
    (hF : ∀ e ∈ F, (ends e).1 ∈ Nd ∧ (ends e).2 ∈ Nd) :
    ∑ v ∈ Nd, mdeg F ends v = 2 * F.card := by
  unfold mdeg
  rw [Finset.sum_add_distrib]
  rw [← Finset.card_eq_sum_card_fiberwise (fun e he => (hF e he).1),
    ← Finset.card_eq_sum_card_fiberwise (fun e he => (hF e he).2)]
  ring

/-- `deg_{C_1} + deg_{C_2} = deg_{C_1 Δ C_2} + 2 deg_{C_1 ∩ C_2}`. -/
theorem mdeg_add_mdeg (C1 C2 : Finset ι) (ends : ι → N × N) (v : N) :
    mdeg C1 ends v + mdeg C2 ends v =
      mdeg ((C1 \ C2) ∪ (C2 \ C1)) ends v + 2 * mdeg (C1 ∩ C2) ends v := by
  have h1 : C1 = (C1 \ C2) ∪ (C1 ∩ C2) := (Finset.sdiff_union_inter C1 C2).symm
  have h2 : C2 = (C2 \ C1) ∪ (C1 ∩ C2) := by
    rw [Finset.inter_comm]; exact (Finset.sdiff_union_inter C2 C1).symm
  have d1 : Disjoint (C1 \ C2) (C1 ∩ C2) := Finset.disjoint_sdiff_inter C1 C2
  have d2 : Disjoint (C2 \ C1) (C1 ∩ C2) := by
    rw [Finset.inter_comm]; exact Finset.disjoint_sdiff_inter C2 C1
  have d3 : Disjoint (C1 \ C2) (C2 \ C1) := disjoint_sdiff_sdiff
  have e1 := mdeg_union_of_disjoint d1 ends v
  have e2 := mdeg_union_of_disjoint d2 ends v
  rw [← h1] at e1
  rw [← h2] at e2
  rw [e1, e2, mdeg_union_of_disjoint d3]
  ring

/-- A multigraph with at least as many edges as nodes has a nonempty even sub-multigraph. -/
theorem exists_even_sub {F : Finset ι} {ends : ι → N × N} {Nd : Finset N}
    (hF : ∀ e ∈ F, (ends e).1 ∈ Nd ∧ (ends e).2 ∈ Nd) (hNd : Nd.Nonempty)
    (hcard : Nd.card ≤ F.card) :
    ∃ C ⊆ F, C.Nonempty ∧ ∀ v, Even (mdeg C ends v) := by
  classical
  obtain ⟨v0, hv0⟩ := hNd
  set φ : Finset ι → Finset N := fun C => (Nd.erase v0).filter fun v => Odd (mdeg C ends v)
  have hlt : ((Nd.erase v0).powerset).card < F.powerset.card := by
    rw [Finset.card_powerset, Finset.card_powerset, Finset.card_erase_of_mem hv0]
    exact Nat.pow_lt_pow_right (by norm_num) (by have := Finset.card_pos.2 ⟨v0, hv0⟩; omega)
  obtain ⟨C1, hC1, C2, hC2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (f := φ) (fun C _ => Finset.mem_powerset.2 (Finset.filter_subset _ _))
  rw [Finset.mem_powerset] at hC1 hC2
  set C := (C1 \ C2) ∪ (C2 \ C1) with hC
  have hCF : C ⊆ F := Finset.union_subset (Finset.sdiff_subset.trans hC1)
    (Finset.sdiff_subset.trans hC2)
  have hCne : C.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    apply hne
    have := Finset.union_eq_empty.1 h0
    exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.1 this.1)
      (Finset.sdiff_eq_empty_iff_subset.1 this.2)
  have hCends : ∀ e ∈ C, (ends e).1 ∈ Nd ∧ (ends e).2 ∈ Nd := fun e he => hF e (hCF he)
  -- even at every `v ≠ v0`
  have hev : ∀ v, v ≠ v0 → Even (mdeg C ends v) := by
    intro v hv
    by_cases hvN : v ∈ Nd
    · have hsame : Odd (mdeg C1 ends v) ↔ Odd (mdeg C2 ends v) := by
        have h1 : v ∈ φ C1 ↔ v ∈ φ C2 := by rw [heq]
        simp only [φ, Finset.mem_filter, Finset.mem_erase] at h1
        constructor
        · intro h; exact (h1.1 ⟨⟨hv, hvN⟩, h⟩).2
        · intro h; exact (h1.2 ⟨⟨hv, hvN⟩, h⟩).2
      have hsum := mdeg_add_mdeg C1 C2 ends v
      rw [← hC] at hsum
      have hE : Even (mdeg C1 ends v + mdeg C2 ends v) := by
        rcases Nat.even_or_odd (mdeg C1 ends v) with h | h
        · have h2 : Even (mdeg C2 ends v) := by
            rcases Nat.even_or_odd (mdeg C2 ends v) with h' | h'
            · exact h'
            · exact absurd (hsame.2 h') (Nat.not_odd_iff_even.2 h)
          exact h.add h2
        · exact h.add_odd (hsame.1 h)
      rw [hsum] at hE
      exact (Nat.even_add.1 hE).2 (even_two_mul _)
    · rw [mdeg_eq_zero_of_notMem hCends hvN]; exact ⟨0, rfl⟩
  refine ⟨C, hCF, hCne, fun v => ?_⟩
  by_cases hv : v = v0
  · subst hv
    have hs := sum_mdeg hCends
    rw [← Finset.add_sum_erase Nd _ hv0] at hs
    have hrest : Even (∑ x ∈ Nd.erase v, mdeg C ends x) :=
      Finset.even_sum _ fun x hx => hev x (Finset.ne_of_mem_erase hx)
    have h2 : Even (2 * C.card) := even_two_mul _
    rw [← hs] at h2
    exact (Nat.even_add.1 h2).2 hrest
  · exact hev v hv

/-- [s5:lemParent] Step 3, the `T`-join: some `T ⊆ A` with `|T| ≤ |Nd| − 1` leaves all degrees of
`A \ T` even. -/
theorem exists_even_complement (A : Finset ι) (ends : ι → N × N) (Nd : Finset N)
    (hA : ∀ e ∈ A, (ends e).1 ∈ Nd ∧ (ends e).2 ∈ Nd) :
    ∃ T ⊆ A, T.card ≤ Nd.card - 1 ∧ ∀ v, Even (mdeg (A \ T) ends v) := by
  classical
  set P := A.powerset.filter fun T => ∀ v, Even (mdeg (A \ T) ends v)
  have hPne : P.Nonempty := ⟨A, Finset.mem_filter.2 ⟨Finset.mem_powerset_self A,
    fun v => by simp [mdeg]⟩⟩
  obtain ⟨T, hT, hmin⟩ := P.exists_min_image Finset.card hPne
  obtain ⟨hTA, hTev⟩ := Finset.mem_filter.1 hT
  rw [Finset.mem_powerset] at hTA
  refine ⟨T, hTA, ?_, hTev⟩
  by_contra hlt
  push Not at hlt
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  have hNd : Nd.Nonempty := by
    obtain ⟨e, he⟩ := hTne
    exact ⟨_, (hA e (hTA he)).1⟩
  have hNdT : Nd.card ≤ T.card := by have := Finset.card_pos.2 hNd; omega
  obtain ⟨C, hCT, hCne, hCev⟩ := exists_even_sub (fun e he => hA e (hTA he)) hNd hNdT
  have hT' : T \ C ∈ P := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.sdiff_subset.trans hTA), fun v => ?_⟩
    have e1 : A \ (T \ C) = (A \ T) ∪ C := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨heA, heTC⟩; by_cases heT : e ∈ T
        · exact Or.inr (by by_contra h; exact heTC ⟨heT, h⟩)
        · exact Or.inl ⟨heA, heT⟩
      · rintro (⟨heA, heT⟩ | heC)
        · exact ⟨heA, fun h => heT h.1⟩
        · exact ⟨hTA (hCT heC), fun h => h.2 heC⟩
    have hdis : Disjoint (A \ T) C := by
      rw [Finset.disjoint_left]; intro e he heC; exact (Finset.mem_sdiff.1 he).2 (hCT heC)
    rw [e1, mdeg_union_of_disjoint hdis]
    exact (hTev v).add (hCev v)
  have := hmin _ hT'
  have hlt2 : (T \ C).card < T.card := Finset.card_lt_card (Finset.sdiff_ssubset hCT hCne)
  omega

end EG.MTrail
