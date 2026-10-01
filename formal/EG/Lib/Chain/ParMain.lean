module

public import EG.Lib.Chain.ParComp
public import Mathlib.Data.Real.Basic

/-!
# Lemma PAR: the count and the partition (manuscript s6:lemPAR)

Probe unit P2E (probe P-2, part 1), proof round 1. Let `E` be bipartite with sides `V_a, V_b` and
`J'` an admissible choice.
* `EG.Chain.card_le_oddComps`: `|J'| ≤ #{odd components}`;
* `EG.Chain.two_mul_card_oddComps_le`: "Every odd component has at least one edge, hence at least
  two vertices of `V(E_ab)`. Components are vertex-disjoint, so there are at most
  `|V(E_ab)|/2` of them";
* `EG.Chain.exists_par_partition`: the partition `E ∖ J' = S_a ⊔ S_b`, with `S_a` a `T`-join of
  `E ∖ J'` for `T = {u ∈ V_a : deg_{E∖J'}(u) odd}`.
-/

public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V]

open Classical

/-- `#{u ∈ S : d(u) odd} ≡ ∑_{u ∈ S} d(u) (mod 2)`. -/
theorem even_card_filter_odd_iff (S : Finset V) (d : V → ℕ) :
    Even (S.filter (fun u => Odd (d u))).card ↔ Even (∑ u ∈ S, d u) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.filter_insert, Finset.sum_insert ha]
    by_cases hodd : Odd (d a)
    · rw [if_pos hodd, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1),
        Nat.even_add_one, Nat.even_add, ih]
      rw [← Nat.not_even_iff_odd] at hodd
      tauto
    · rw [if_neg hodd, Nat.even_add, ih]
      rw [Nat.not_odd_iff_even] at hodd
      tauto

section Bip

variable {E J' : Finset (Sym2 V)} {Va Vb : Finset V}

/-- [s6:lemPAR] (proof) "Every edge of `C'` has exactly one end in `V_a`, so
`∑_{w∈V(C')} p(w) ≡ ∑_{u∈V_a∩V(C')} deg_{C'}(u) = |E(C')|`": the sum of the `E'`-degrees of the
vertices of `V_a` reachable from `z` is the number of edges of the component of `z` in `E'`. -/
theorem sum_degE_Va_eq (hVab : Disjoint Va Vb)
    (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) (z : V) :
    ∑ u ∈ Va.filter (fun u => (edgeGraph (E \ J')).Reachable z u), degE (E \ J') u =
      (compPrime E J' z).card := by
  set S := Va.filter (fun u => (edgeGraph (E \ J')).Reachable z u)
  have h1 : ∀ u, degE (E \ J') u = ∑ f ∈ E \ J', if u ∈ f then 1 else 0 := by
    intro u
    unfold degE edgesAt
    rw [Finset.card_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  unfold compPrime
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun f hf => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hbip f (Finset.mem_sdiff.1 hf).1
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 hVab ha (h ▸ hb)
  have hadj : (edgeGraph (E \ J')).Reachable a b := reachable_of_mem hf hab
  have hbS : b ∉ S := fun h => Finset.disjoint_left.1 hVab (Finset.mem_filter.1 h).1 hb
  have hsum : ∑ u ∈ S, (if u ∈ s(a, b) then 1 else 0) =
      if (edgeGraph (E \ J')).Reachable z a then 1 else 0 := by
    rw [← Finset.card_filter]
    by_cases hza : (edgeGraph (E \ J')).Reachable z a
    · rw [if_pos hza]
      rw [Finset.card_eq_one]
      refine ⟨a, ?_⟩
      ext u
      simp only [Finset.mem_filter, Finset.mem_singleton, Sym2.mem_iff]
      constructor
      · rintro ⟨hu, rfl | rfl⟩
        · rfl
        · exact absurd hu hbS
      · rintro rfl
        exact ⟨Finset.mem_filter.2 ⟨ha, hza⟩, Or.inl rfl⟩
    · rw [if_neg hza, Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro u hu
      simp only [Finset.mem_filter, Sym2.mem_iff] at hu
      obtain ⟨huS, rfl | rfl⟩ := hu
      · exact hza (Finset.mem_filter.1 huS).2
      · exact hbS huS
  rw [hsum]
  congr 1
  apply propext
  constructor
  · intro h w hw
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · exact h
    · exact h.trans hadj
  · intro h
    exact h a (Sym2.mem_mk_left a b)

/-- [s6:lemPAR] (proof) "So `T := {w : p(w) = 1}` has even size" (in every component of
`E ∖ J'`). -/
theorem even_card_oddVa (hVab : Disjoint Va Vb)
    (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) (hJ : IsParChoice E J') (z : V) :
    Even ((Va.filter (fun u => Odd (degE (E \ J') u))).filter
      (fun t => (edgeGraph (E \ J')).Reachable z t)).card := by
  have hset : (Va.filter (fun u => Odd (degE (E \ J') u))).filter
      (fun t => (edgeGraph (E \ J')).Reachable z t) =
      (Va.filter (fun u => (edgeGraph (E \ J')).Reachable z u)).filter
        (fun u => Odd (degE (E \ J') u)) := by
    ext u
    simp only [Finset.mem_filter]
    tauto
  rw [hset, even_card_filter_odd_iff, sum_degE_Va_eq hVab hbip z]
  exact even_card_compPrime hVab hbip hJ z

/-- [s6:lemPAR] "there is a partition `E_ab ∖ J' = S_a ⊔ S_b` such that every vertex of `V_b`
has even `S_a`-degree and every vertex of `V_a` has even `S_b`-degree." -/
theorem exists_par_partition (hVab : Disjoint Va Vb)
    (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) (hJ : IsParChoice E J') :
    ∃ Sa Sb : Finset (Sym2 V), Disjoint Sa Sb ∧ Sa ∪ Sb = E \ J' ∧
      (∀ v ∈ Vb, Even (degE Sa v)) ∧ ∀ u ∈ Va, Even (degE Sb u) := by
  set T := Va.filter (fun u => Odd (degE (E \ J') u)) with hT
  obtain ⟨J, hJE, hJT⟩ := exists_tJoin (E \ J') T.card T rfl
    (fun z => even_card_oddVa hVab hbip hJ z)
  refine ⟨J, (E \ J') \ J, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hJE,
    fun v hv => ?_, fun u hu => ?_⟩
  · rw [← Nat.not_odd_iff_even, hJT v]
    intro hvT
    exact Finset.disjoint_left.1 hVab (Finset.mem_filter.1 hvT).1 hv
  · have h1 := degE_sdiff_add_inter (E \ J') J u
    rw [Finset.inter_eq_right.2 hJE] at h1
    have h2 : Odd (degE J u) ↔ Odd (degE (E \ J') u) := by
      rw [hJT u, hT, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
    have hsub : degE ((E \ J') \ J) u = degE (E \ J') u - degE J u := by omega
    rw [hsub, Nat.even_sub (by omega)]
    rw [← Nat.not_odd_iff_even, ← Nat.not_odd_iff_even, h2]

/-- [s6:lemPAR] "`|J'| ≤ #{odd components}`": `J'` has one edge in each odd component and none
elsewhere. -/
theorem card_le_oddComps (hVab : Disjoint Va Vb)
    (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) (hJ : IsParChoice E J') :
    J'.card ≤ (oddComps E).card := by
  have hsub : J' ⊆ (oddComps E).biUnion (fun C => J' ∩ compEdges E C) := by
    intro e he
    have heE := hJ.1 he
    obtain ⟨a, -, b, -, rfl⟩ := hbip e heE
    have hab := ne_of_bip hVab hbip heE
    set C := (edgeGraph E).connectedComponentMk a
    have heC : s(a, b) ∈ compEdges E C := mem_compEdges_of_mem heE hab
    have hCE : C ∈ edgeComps E :=
      mem_edgeComps.2 ⟨a, mem_edgeVerts.2 ⟨_, heE, Sym2.mem_mk_left a b⟩, rfl⟩
    have hodd : Odd (compEdges E C).card := by
      by_contra hodd
      have h := hJ.2.1 C hCE
      rw [if_neg hodd, Finset.card_eq_zero] at h
      have : s(a, b) ∈ J' ∩ compEdges E C := Finset.mem_inter.2 ⟨he, heC⟩
      rw [h] at this
      exact Finset.notMem_empty _ this
    refine Finset.mem_biUnion.2 ⟨C, ?_, Finset.mem_inter.2 ⟨he, heC⟩⟩
    unfold oddComps
    exact Finset.mem_filter.2 ⟨hCE, hodd⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [Finset.card_eq_sum_ones (oddComps E)]
  refine Finset.sum_le_sum fun C hC => ?_
  unfold oddComps at hC
  obtain ⟨hCE, hodd⟩ := Finset.mem_filter.1 hC
  rw [hJ.2.1 C hCE, if_pos hodd]

/-- [s6:lemPAR] "`#{odd components} ≤ |V(E_ab)|/2`": every odd component has two vertices of
`V(E_ab)`, and components are vertex-disjoint. -/
theorem two_mul_card_oddComps_le (hVab : Disjoint Va Vb)
    (hbip : ∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) :
    2 * (oddComps E).card ≤ (edgeVerts E).card := by
  have hdisj : ∀ C ∈ oddComps E, ∀ C' ∈ oddComps E, C ≠ C' →
      Disjoint (compVerts E C) (compVerts E C') := by
    intro C _ C' _ hne
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact hne (((mem_compVerts.1 hv).2).symm.trans (mem_compVerts.1 hv').2)
  have hsub : (oddComps E).biUnion (compVerts E) ⊆ edgeVerts E := by
    intro v hv
    obtain ⟨C, -, hvC⟩ := Finset.mem_biUnion.1 hv
    exact (mem_compVerts.1 hvC).1
  have h2 : ∀ C ∈ oddComps E, 2 ≤ (compVerts E C).card := by
    intro C hC
    unfold oddComps at hC
    obtain ⟨-, hodd⟩ := Finset.mem_filter.1 hC
    obtain ⟨f, hf⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero (fun h => by
      rw [h] at hodd; exact Nat.not_odd_zero hodd))
    obtain ⟨hfE, hfC⟩ := mem_compEdges.1 hf
    obtain ⟨a, -, b, -, rfl⟩ := hbip f hfE
    have hab := ne_of_bip hVab hbip hfE
    have hsub2 : ({a, b} : Finset V) ⊆ compVerts E C := by
      intro v hv
      rw [mem_compVerts]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact ⟨mem_edgeVerts.2 ⟨_, hfE, Sym2.mem_mk_left _ b⟩, hfC _ (Sym2.mem_mk_left _ b)⟩
      · rw [Finset.mem_singleton.1 hv]
        exact ⟨mem_edgeVerts.2 ⟨_, hfE, Sym2.mem_mk_right a _⟩, hfC _ (Sym2.mem_mk_right a _)⟩
    have := Finset.card_le_card hsub2
    rwa [Finset.card_pair hab] at this
  calc 2 * (oddComps E).card = ∑ C ∈ oddComps E, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ C ∈ oddComps E, (compVerts E C).card := Finset.sum_le_sum h2
    _ = ((oddComps E).biUnion (compVerts E)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (edgeVerts E).card := Finset.card_le_card hsub

end Bip

end EG.Chain
