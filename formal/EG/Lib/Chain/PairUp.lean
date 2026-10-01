module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pairing an even set; first-fit grouping with conflicts (for JS-LC Step 5)

Probe unit P2J (probe P-2, part 2), proof round 1. Two general combinatorial lemmas used by the
cherry split of Lemma JS-LC [s6:lemJSLC] (Step 5):
* `EG.exists_pairing`: "pair the (evenly many) edges … arbitrarily": a set of even size is the
  disjoint union of pairs of distinct elements;
* `EG.exists_firstFit`: "Greedy colouring": if every element of `X` conflicts with at most `Δ`
  others (a symmetric relation), then `X` can be split into `m` groups of pairwise non-conflicting
  elements, each of size at most `K ≥ 1`, with `m K ≤ (Δ + 1) K + |X|`. (Greedy colouring plus
  cutting colour classes into pieces of size `≤ K`, done in one first-fit pass: an element
  goes to the first group that has no conflict with it and is not full.)
-/

public section

namespace EG

variable {α : Type*} [DecidableEq α]

/-- A set of even size is partitioned into pairs `(a, b)`, `a ≠ b`: every element lies in
exactly one pair. -/
theorem exists_pairing_aux (n : ℕ) : ∀ s : Finset α, s.card = n → Even n →
    ∃ P : Finset (α × α), (∀ p ∈ P, p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2) ∧
      ∀ x ∈ s, ∃! p, p ∈ P ∧ (p.1 = x ∨ p.2 = x) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s h hs
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · exact ⟨∅, by simp, by simp⟩
    · have hc1 : (s.erase a).card + 1 = n := by rw [Finset.card_erase_add_one ha, h]
      obtain ⟨k, hk⟩ := hs
      have hne : (s.erase a).Nonempty := by
        rw [← Finset.card_pos]
        omega
      obtain ⟨b, hb⟩ := hne
      have hba : b ≠ a := Finset.ne_of_mem_erase hb
      have hbs : b ∈ s := Finset.mem_of_mem_erase hb
      set s' := (s.erase a).erase b with hs'
      have hc2 : s'.card + 2 = n := by
        have := Finset.card_erase_add_one hb
        rw [← hs'] at this
        omega
      obtain ⟨P, hP1, hP2⟩ := ih s'.card (by omega) s' rfl ⟨k - 1, by omega⟩
      have hs'sub : ∀ x ∈ s', x ∈ s ∧ x ≠ a ∧ x ≠ b := by
        intro x hx
        rw [hs', Finset.mem_erase, Finset.mem_erase] at hx
        exact ⟨hx.2.2, hx.2.1, hx.1⟩
      refine ⟨insert (a, b) P, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact ⟨ha, hbs, hba.symm⟩
        · obtain ⟨h1, h2, h3⟩ := hP1 p hp
          exact ⟨(hs'sub _ h1).1, (hs'sub _ h2).1, h3⟩
      · intro x hx
        by_cases hxab : x = a ∨ x = b
        · refine ⟨(a, b), ⟨Finset.mem_insert_self _ _, ?_⟩, ?_⟩
          · rcases hxab with hxa | hxb
            · exact Or.inl hxa.symm
            · exact Or.inr hxb.symm
          · rintro p ⟨hp, hpx⟩
            rcases Finset.mem_insert.1 hp with hpab | hp
            · exact hpab
            · exfalso
              obtain ⟨h1, h2, -⟩ := hP1 p hp
              rcases hpx with hpx | hpx
              · rw [hpx] at h1
                rcases hxab with h | h
                · exact (hs'sub _ h1).2.1 h
                · exact (hs'sub _ h1).2.2 h
              · rw [hpx] at h2
                rcases hxab with h | h
                · exact (hs'sub _ h2).2.1 h
                · exact (hs'sub _ h2).2.2 h
        · push Not at hxab
          have hx' : x ∈ s' := by
            rw [hs', Finset.mem_erase, Finset.mem_erase]; exact ⟨hxab.2, hxab.1, hx⟩
          obtain ⟨p, ⟨hp, hpx⟩, hu⟩ := hP2 x hx'
          refine ⟨p, ⟨Finset.mem_insert_of_mem hp, hpx⟩, ?_⟩
          rintro q ⟨hq, hqx⟩
          rcases Finset.mem_insert.1 hq with hqab | hq
          · exfalso
            rw [hqab] at hqx
            rcases hqx with h | h
            · exact hxab.1 h.symm
            · exact hxab.2 h.symm
          · exact hu q ⟨hq, hqx⟩

/-- A set of even size is partitioned into pairs `(a, b)`, `a ≠ b`: every element lies in
exactly one pair. -/
theorem exists_pairing (s : Finset α) (hs : Even s.card) :
    ∃ P : Finset (α × α), (∀ p ∈ P, p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2) ∧
      ∀ x ∈ s, ∃! p, p ∈ P ∧ (p.1 = x ∨ p.2 = x) :=
  exists_pairing_aux s.card s rfl hs

/-- First-fit grouping with conflicts ("greedy colouring" of the conflict graph, colour classes
cut into groups of size at most `K`), for a subset `X'` of the ambient set `X` whose elements
have at most `Δ` conflicts in `X`. -/
theorem exists_firstFit_aux (X : Finset α) (conf : α → α → Prop) [DecidableRel conf]
    (hsymm : ∀ x y, conf x y → conf y x) (Δ K : ℕ) (hK : 1 ≤ K)
    (hΔ : ∀ x ∈ X, (X.filter (fun y => y ≠ x ∧ conf x y)).card ≤ Δ) (X' : Finset α)
    (hX' : X' ⊆ X) :
    ∃ (m : ℕ) (c : α → ℕ), (∀ x ∈ X', c x < m) ∧
      (∀ x ∈ X', ∀ y ∈ X', x ≠ y → conf x y → c x ≠ c y) ∧
      (∀ i, (X'.filter (fun x => c x = i)).card ≤ K) ∧
      m * K ≤ (Δ + 1) * K + X'.card := by
  induction X' using Finset.induction_on with
  | empty =>
    exact ⟨0, fun _ => 0, by simp, by simp, by simp, by simp⟩
  | insert x X' hx ih =>
    have hxX : x ∈ X := hX' (Finset.mem_insert_self _ _)
    obtain ⟨m, c, hcm, hcf, hcK, hmK⟩ := ih ((Finset.subset_insert _ _).trans hX')
    have hne : ∀ w ∈ X', w ≠ x := by rintro w hw rfl; exact hx hw
    -- the blocked colours: conflicting ones and full ones
    set confC := (X'.filter (fun y => conf x y)).image c with hconfC
    set full := (Finset.range m).filter (fun i => K ≤ (X'.filter (fun y => c y = i)).card)
      with hfull
    have hconfC_card : confC.card ≤ Δ := by
      refine Finset.card_image_le.trans (le_trans (Finset.card_le_card ?_) (hΔ x hxX))
      intro y hy
      obtain ⟨hy, hxy⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨hX' (Finset.mem_insert_of_mem hy), hne y hy, hxy⟩
    have hfull_card : full.card * K ≤ X'.card := by
      have h1 : ∑ i ∈ full, (X'.filter (fun y => c y = i)).card =
          (X'.filter (fun y => c y ∈ full)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := c) (t := full)]
        · refine Finset.sum_congr rfl fun i hi => ?_
          congr 1
          ext y
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hy, hyi⟩; exact ⟨⟨hy, hyi ▸ hi⟩, hyi⟩
          · rintro ⟨⟨hy, -⟩, hyi⟩; exact ⟨hy, hyi⟩
        · intro y hy; exact (Finset.mem_filter.1 hy).2
      have h2 : full.card * K ≤ ∑ i ∈ full, (X'.filter (fun y => c y = i)).card := by
        have := Finset.card_nsmul_le_sum full (fun i => (X'.filter (fun y => c y = i)).card) K
          (fun i hi => (Finset.mem_filter.1 hi).2)
        simpa using this
      rw [h1] at h2
      exact h2.trans (Finset.card_le_card (Finset.filter_subset _ _))
    by_cases hfree : ∃ i < m, i ∉ confC ∧ i ∉ full
    · obtain ⟨i, him, hic, hif⟩ := hfree
      have hupd : ∀ w ∈ X', Function.update c x i w = c w := fun w hw =>
        Function.update_of_ne (hne w hw) _ _
      refine ⟨m, Function.update c x i, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.1 hy with hyx | hy
        · rw [hyx, Function.update_self]; exact him
        · rw [hupd y hy]; exact hcm y hy
      · intro y hy z hz hyz hconf
        rcases Finset.mem_insert.1 hy with hyx | hy <;> rcases Finset.mem_insert.1 hz with hzx | hz
        · exact absurd (hyx.trans hzx.symm) hyz
        · rw [hyx] at hconf ⊢
          rw [Function.update_self, hupd z hz]
          intro h
          exact hic (Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, hconf⟩, h.symm⟩)
        · rw [hzx] at hconf ⊢
          rw [Function.update_self, hupd y hy]
          intro h
          exact hic (Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hy, hsymm _ _ hconf⟩, h⟩)
        · rw [hupd y hy, hupd z hz]; exact hcf y hy z hz hyz hconf
      · intro i'
        rw [Finset.filter_insert]
        have hfil : X'.filter (fun y => Function.update c x i y = i') =
            X'.filter (fun y => c y = i') :=
          Finset.filter_congr fun w hw => by rw [hupd w hw]
        split_ifs with hxi
        · rw [Function.update_self] at hxi
          subst hxi
          rw [Finset.card_insert_of_notMem (fun h => hx (Finset.mem_filter.1 h).1), hfil]
          have : ¬ K ≤ (X'.filter (fun y => c y = i)).card := fun h =>
            hif (Finset.mem_filter.2 ⟨Finset.mem_range.2 him, h⟩)
          omega
        · rw [hfil]; exact hcK i'
      · rw [Finset.card_insert_of_notMem hx]; omega
    · push Not at hfree
      have hupd : ∀ w ∈ X', Function.update c x m w = c w := fun w hw =>
        Function.update_of_ne (hne w hw) _ _
      have hsub : Finset.range m ⊆ confC ∪ full := by
        intro i hi
        by_cases hic : i ∈ confC
        · exact Finset.mem_union_left _ hic
        · exact Finset.mem_union_right _ (hfree i (Finset.mem_range.1 hi) hic)
      have hm : m ≤ Δ + full.card := by
        have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        rw [Finset.card_range] at this
        omega
      refine ⟨m + 1, Function.update c x m, ?_, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.1 hy with hyx | hy
        · rw [hyx, Function.update_self]; omega
        · rw [hupd y hy]; have := hcm y hy; omega
      · intro y hy z hz hyz hconf
        rcases Finset.mem_insert.1 hy with hyx | hy <;> rcases Finset.mem_insert.1 hz with hzx | hz
        · exact absurd (hyx.trans hzx.symm) hyz
        · rw [hyx, Function.update_self, hupd z hz]; exact (Nat.ne_of_lt (hcm z hz)).symm
        · rw [hzx, Function.update_self, hupd y hy]; exact Nat.ne_of_lt (hcm y hy)
        · rw [hupd y hy, hupd z hz]; exact hcf y hy z hz hyz hconf
      · intro i'
        rw [Finset.filter_insert]
        have hfil : X'.filter (fun y => Function.update c x m y = i') =
            X'.filter (fun y => c y = i') :=
          Finset.filter_congr fun w hw => by rw [hupd w hw]
        split_ifs with hxi
        · rw [Function.update_self] at hxi
          subst hxi
          rw [hfil]
          have : X'.filter (fun y => c y = m) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro y hy; exact Nat.ne_of_lt (hcm y hy)
          rw [this]
          simp only [insert_empty_eq, Finset.card_singleton]
          exact hK
        · rw [hfil]; exact hcK i'
      · rw [Finset.card_insert_of_notMem hx]
        have h1 := Nat.mul_le_mul_right K hm
        have h2 : (Δ + full.card) * K = Δ * K + full.card * K := Nat.add_mul _ _ _
        have h3 : (m + 1) * K = m * K + K := by rw [Nat.add_mul, one_mul]
        have h4 : (Δ + 1) * K = Δ * K + K := by rw [Nat.add_mul, one_mul]
        omega

/-- [s6:lemJSLC] (proof, Step 5) first-fit grouping: if `K ≥ 1` and every element of `X`
conflicts with at most `Δ` others, `X` splits into `m` groups (colours `c x < m`) of pairwise
non-conflicting elements, each of size at most `K`, with `m K ≤ (Δ + 1) K + |X|`. -/
theorem exists_firstFit (X : Finset α) (conf : α → α → Prop) [DecidableRel conf]
    (hsymm : ∀ x y, conf x y → conf y x) (Δ K : ℕ) (hK : 1 ≤ K)
    (hΔ : ∀ x ∈ X, (X.filter (fun y => y ≠ x ∧ conf x y)).card ≤ Δ) :
    ∃ (m : ℕ) (c : α → ℕ), (∀ x ∈ X, c x < m) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → conf x y → c x ≠ c y) ∧
      (∀ i, (X.filter (fun x => c x = i)).card ≤ K) ∧
      m * K ≤ (Δ + 1) * K + X.card :=
  exists_firstFit_aux X conf hsymm Δ K hK hΔ X (Finset.Subset.refl _)

end EG
