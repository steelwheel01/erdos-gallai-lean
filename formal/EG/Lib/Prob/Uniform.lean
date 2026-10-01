module

public import EG.Lib.Prob.Named
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Uniform laws: products, pushforwards, images of a set under a uniform permutation

Lib for the Cuckoo SDR bound s7:lemWellDef (iii) (probe P-1, `work/p2b/P1.md` §5) and, later,
s7:lemCC / s7:lemUltra / s7:lemPay.

* *Uniform product = product* (P1.md §5 item 1): `pi_uniform`
  (`∏ᵢ uniform (κ i) = uniform (∀ i, κ i)`), `prod_uniform`
  (`uniform α ⊗ uniform β = uniform (α × β)`), `map_equiv_uniform` (a bijection preserves the
  uniform law), `map_mulLeft_uniform_perm` (left translation of a uniform permutation).
  Marginals and independence of the coordinates of `pi` are `prob_pi_eval`,
  `prob_pi_forall_mem` (`EG.Lib.Prob.Basic`) and `iIndepFun_eval_pi` (`EG.Lib.Prob.Indep`).
* *Image of a `k`-set under a uniform permutation* (item 2): for `A : Finset α` with `|A| = k`,
  `map_image_uniform_perm`: `A.image η` (`η` uniform in `Perm α`) is uniform on the `k`-subsets;
  `prob_image_perm_subset`: `P(A.image η ⊆ T) = C(|T|, k) / C(|α|, k)`; and for the uniform
  law on `k`-subsets itself, `prob_uniformCard_subset`: `P(s ⊆ T) = C(|T|, k) / C(|α|, k)`.
* *Conditioning on product atoms* (item 4): the binary case is `cond_prod_fst` /
  `map_snd_cond_prod_fst` (`EG.Lib.Prob.Basic`); the Cuckoo bound needs no conditioning (it is a
  union bound over events of the lists only, `prob_prod_fst`).
* *`i`-th element of a set in a uniform order* (item 3) is needed by lemCC / lemUltra only, not
  by P-1; it is not in this file yet.
-/

public section

namespace EG

namespace FinDist

open Finset

variable {ι α β : Type*}

/-! ### Products and pushforwards of uniform laws -/

section Products

/-- The product of uniform laws is the uniform law on the product type. -/
theorem pi_uniform [Fintype ι] {κ : ι → Type*} [∀ i, Finite (κ i)] [∀ i, Nonempty (κ i)] :
    (pi fun i => uniform (κ i)) = uniform (∀ i, κ i) := by
  ext f
  rw [pi_w]
  simp only [uniform_w]
  rw [Nat.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

/-- The product of two uniform laws is the uniform law on the product type. -/
theorem prod_uniform [Finite α] [Nonempty α] [Finite β] [Nonempty β] :
    (uniform α).prod (uniform β) = uniform (α × β) := by
  ext p
  rw [prod_w', uniform_w, uniform_w, uniform_w, Nat.card_prod, Nat.cast_mul, mul_inv]

/-- A bijection maps the uniform law to the uniform law. -/
theorem map_equiv_uniform [Finite α] [Nonempty α] [Finite β] [Nonempty β] (e : α ≃ β) :
    (uniform α).map e = uniform β := by
  ext b
  rw [map_equiv_w, uniform_w, uniform_w, Nat.card_congr e]

/-- Left translation preserves the uniform law on a finite group of permutations. -/
theorem map_mulLeft_uniform_perm [Finite α] (τ : Equiv.Perm α) :
    (uniform (Equiv.Perm α)).map (fun η => τ * η) = uniform (Equiv.Perm α) :=
  map_equiv_uniform (Equiv.mulLeft τ)

/-- `P(η ∈ B) = P(τ * η ∈ B)` for a uniform permutation `η`. -/
theorem prob_uniform_perm_mulLeft [Finite α] (τ : Equiv.Perm α) (B : Set (Equiv.Perm α)) :
    (uniform (Equiv.Perm α)).prob ((fun η => τ * η) ⁻¹' B) = (uniform (Equiv.Perm α)).prob B := by
  rw [← prob_map, map_mulLeft_uniform_perm]

end Products

/-! ### The image of a `k`-set under a uniform permutation -/

section ImagePerm

variable [Fintype α] [DecidableEq α]

/-- Two finsets of the same size are mapped to each other by some permutation. -/
theorem exists_perm_image_eq {s t : Finset α} (h : s.card = t.card) :
    ∃ τ : Equiv.Perm α, s.image τ = t := by
  classical
  let e : {x // x ∈ s} ≃ {x // x ∈ t} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, ?_⟩
  have hsub : s.image e.extendSubtype ⊆ t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact e.extendSubtype_mem x hx
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_image_of_injective _ (Equiv.injective _), h]

/-- The law of `A.image η` for a uniform permutation `η`. -/
noncomputable abbrev imageLaw (A : Finset α) : FinDist (Finset α) :=
  (uniform (Equiv.Perm α)).map fun η : Equiv.Perm α => A.image η

theorem imageLaw_w_of_card_ne (A : Finset α) {s : Finset α} (hs : s.card ≠ A.card) :
    (imageLaw A).w s = 0 := by
  rw [map_w]
  convert prob_empty (uniform (Equiv.Perm α)) using 2
  ext η
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro h
  apply hs
  rw [← h, Finset.card_image_of_injective _ (Equiv.injective _)]

theorem supp_imageLaw_subset (A : Finset α) :
    (imageLaw A).supp ⊆ powersetCard A.card (univ : Finset α) := by
  intro s hs
  rw [mem_powersetCard]
  refine ⟨subset_univ _, ?_⟩
  by_contra hne
  exact (mem_supp.1 hs) (imageLaw_w_of_card_ne A hne)

/-- Translating the target set by a permutation does not change its weight. -/
theorem imageLaw_w_image (A : Finset α) (τ : Equiv.Perm α) (s : Finset α) :
    (imageLaw A).w (s.image τ) = (imageLaw A).w s := by
  have hset : ((fun η : Equiv.Perm α => A.image η) ⁻¹' {s.image τ}) =
      (fun η => τ⁻¹ * η) ⁻¹' ((fun η : Equiv.Perm α => A.image η) ⁻¹' {s}) := by
    ext η
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have himg : A.image (⇑(τ⁻¹ * η)) = (A.image η).image ⇑(τ⁻¹) := by
      rw [Finset.image_image]
      rfl
    rw [himg]
    constructor
    · intro h
      rw [h, Finset.image_image]
      ext x
      simp
    · intro h
      rw [← h, Finset.image_image]
      ext x
      simp
  rw [map_w, map_w, hset, prob_uniform_perm_mulLeft]

/-- All `k`-subsets have the same weight `1 / C(|α|, k)` (with `k = |A|`). -/
theorem imageLaw_w_of_card_eq (A : Finset α) {s : Finset α} (hs : s.card = A.card) :
    (imageLaw A).w s = 1 / ((Fintype.card α).choose A.card : ℝ) := by
  have hconst : ∀ t ∈ powersetCard A.card (univ : Finset α), (imageLaw A).w t = (imageLaw A).w A := by
    intro t ht
    obtain ⟨τ, hτ⟩ := exists_perm_image_eq (mem_powersetCard.1 ht).2.symm
    rw [← hτ, imageLaw_w_image]
  have hsum := (imageLaw A).sum_w_of_supp_subset (supp_imageLaw_subset A)
  rw [sum_congr rfl hconst, sum_const, card_powersetCard, card_univ, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < ((Fintype.card α).choose A.card : ℝ) := by
    exact_mod_cast Nat.choose_pos (by
      simpa using Finset.card_le_univ A)
  rw [hconst s (mem_powersetCard.2 ⟨subset_univ _, hs⟩), eq_div_iff hpos.ne']
  linarith

omit [Fintype α] [DecidableEq α] in
theorem nonempty_card_eq (A : Finset α) : Nonempty {s : Finset α // s.card = A.card} :=
  ⟨⟨A, rfl⟩⟩

/-- [P1.md §5 item 2] The image of a `k`-set under a uniform permutation is a uniform `k`-set. -/
theorem map_image_uniform_perm (A : Finset α) :
    haveI := nonempty_card_eq A
    (uniform (Equiv.Perm α)).map (fun η : Equiv.Perm α => A.image η) =
      (uniform {s : Finset α // s.card = A.card}).map Subtype.val := by
  have := nonempty_card_eq A
  ext s
  change (imageLaw A).w s = _
  rw [map_w (uniform {s : Finset α // s.card = A.card}) Subtype.val s]
  by_cases hs : s.card = A.card
  · rw [imageLaw_w_of_card_eq A hs]
    have : (Subtype.val ⁻¹' {s} : Set {s : Finset α // s.card = A.card}) = {⟨s, hs⟩} := by
      ext x
      simp [Subtype.ext_iff]
    rw [this, prob_singleton, uniform_w_eq, Fintype.card_finset_len]
  · rw [imageLaw_w_of_card_ne A hs]
    have : (Subtype.val ⁻¹' {s} : Set {s : Finset α // s.card = A.card}) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hs (h ▸ x.2)
    rw [this, prob_empty]

/-- Under the uniform law on the `k`-subsets of `α`, `P(s ⊆ T) = C(|T|, k) / C(|α|, k)`. -/
theorem prob_uniformCard_subset (k : ℕ) [Nonempty {s : Finset α // s.card = k}] (T : Finset α) :
    ((uniform {s : Finset α // s.card = k}).map Subtype.val).prob {s | s ⊆ T} =
      (T.card.choose k : ℝ) / ((Fintype.card α).choose k : ℝ) := by
  classical
  rw [prob_map, prob_uniform, Fintype.card_finset_len]
  congr 2
  have : (univ.filter (· ∈ (Subtype.val ⁻¹' {s : Finset α | s ⊆ T} :
      Set {s : Finset α // s.card = k}))).map (Function.Embedding.subtype _) =
      powersetCard k T := by
    ext s
    simp only [mem_map, mem_filter, mem_univ, true_and, Set.mem_preimage, Set.mem_ofPred_eq,
      Function.Embedding.coe_subtype, mem_powersetCard]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨hx, hk⟩
      exact ⟨⟨s, hk⟩, hx, rfl⟩
  rw [← card_powersetCard, ← this, card_map]

/-- [P1.md §5 item 2] For a uniform permutation `η` and `|A| = k`,
`P(A.image η ⊆ T) = C(|T|, k) / C(|α|, k)`. -/
theorem prob_image_perm_subset (A : Finset α) (T : Finset α) :
    (uniform (Equiv.Perm α)).prob {η | A.image η ⊆ T} =
      (T.card.choose A.card : ℝ) / ((Fintype.card α).choose A.card : ℝ) := by
  have := nonempty_card_eq A
  have h := prob_map (uniform (Equiv.Perm α)) (fun η : Equiv.Perm α => A.image η) {s | s ⊆ T}
  rw [map_image_uniform_perm] at h
  rw [prob_uniformCard_subset A.card T] at h
  rw [h]
  rfl

end ImagePerm

end FinDist

end EG
