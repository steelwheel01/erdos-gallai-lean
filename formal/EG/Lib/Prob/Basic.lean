module

public import EG.Defs.Prob.FinDist
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Basic API for finite distributions (`EG.FinDist`)

PLAN_FORMALIZATION.md §3, decision 3. All statements are about the finite sums defining
`FinDist.prob` and `FinDist.expect` (`EG/Defs/Prob/FinDist.lean`). Almost-sure hypotheses are
written `∀ ω, 0 < μ.w ω → …` (outcomes of positive weight), and existence principles return an
outcome of positive weight.

* weights and support: `sum_w`, `w_le_one`, `mem_supp_iff_pos`, `exists_w_pos`;
* expectation: sums over any superset of the support (`expect_eq_sum_of_supp_subset`,
  `expect_eq_sum` on a `Fintype`), linearity (`expect_add`, `expect_const_mul`, `expect_sum`, …),
  monotonicity, `expect_eq_zero_iff(_ae)`;
* probability: `prob_eq_sum`, `prob_eq_sum_filter`, `prob_eq_expect`, monotonicity, complement
  (`prob_compl`), union bound (`prob_union_le`, `prob_biUnion_le`, `prob_iUnion_le`),
  `prob_biInter_ge`, `prob_pos_iff`, `prob_eq_one_iff`, first moment (`expect_card_filter`);
* existence principles: `exists_of_prob_pos`, `exists_le_expect`, `exists_ge_expect`,
  `exists_mem_inter_of_one_lt_add`, `exists_forall_notMem_of_sum_lt_one`,
  `exists_mem_le_mul_expect`, `exists_mem_le_expect_div`;
* Markov [s1:citMarkov]: `prob_le_expect_div`, (a) `two_thirds_le_prob_le_three_mul_expect`,
  (b) `half_le_prob_le_four_mul_expect_and`, (c) conditional forms
  `two_thirds_mul_prob_le_prob_inter_cond`, `half_mul_prob_le_prob_inter_cond`, and
  `cond_prod_fst` / `map_snd_cond_prod_fst` (the conditional law of independent coordinates);
  every Markov lemma has an `_ae` variant assuming `X ≥ 0` only on outcomes of positive weight
  (for (c): on the outcomes of `A` of positive weight);
* conditioning on an event: `prob_cond`, `expect_cond`;
* pushforward: `expect_map`, `prob_map`, `FinDist.map_map`, `map_congr_ae`, `map_id`,
  `map_equiv_w`;
* two-step experiments and products ("conditioning = fixing a prefix", Fubini):
  `expect_compProd`, `prob_compProd`, `prob_prod_eq_sum` (`P(A) = ∑_a w(a) · P(A_a)`),
  `exists_le_prob_section`, `expect_prod`,
  `expect_prod_swap`, `prob_prod_set_prod`, `expect_prod_mul`, `map_fst_prod`, `map_snd_prod`,
  `map_prod_map` (coordinatewise maps), `expect_bind`, `prob_bind`;
* finite products: `expect_pi_prod`, `prob_pi_forall_mem`, `expect_pi_eval`, `prob_pi_eval`,
  `map_eval_pi`, `map_pi` (coordinatewise maps), `pi_eq_map_prod` and `prob_pi_split` (fixing
  the coordinates in a set), `expect_pi_mul_of_dependsOn` / `prob_pi_inter_of_dependsOn`
  (independence of two events depending on disjoint sets of coordinates), and for finite
  families of pairwise disjoint blocks of coordinates `prob_pi_forall_of_dependsOn`,
  `expect_pi_prod_of_dependsOn`, `map_pi_of_dependsOn` (mutual independence).

## Conventions for downstream files

* **Random variables** are functions `X : Ω → γ` on the sample space of a `μ : FinDist Ω`; the
  law of `X` is `μ.map X`. Statements about a random object are stated for an arbitrary `μ` and
  `X`, or directly for a concrete construction (`pi`, `prod`, `rsubset`, `randColouring`, …).
* **Independence** of `X` and `Y` is `μ.IndepFun X Y`, mutual independence of a family is
  `μ.iIndepFun X`, and "`V` is a ρ-random subset of `S`" is `μ.IsRSubset V S ρ` (definitions in
  `EG/Defs/Prob/FinDist.lean`, API in `EG/Lib/Prob/Indep.lean`). The law-level forms are
  `μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y)`,
  `μ.map (fun ω u => X u ω) = pi fun u => μ.map (X u)` and `μ.map V = rsubset S ρ _ _`; use the
  predicates in statements and the law-level forms (`indepFun_iff_map_eq_prod`,
  `iIndepFun_iff_map_eq_pi`, `IsRSubset.map_eq`) in proofs.
* **Names to qualify.** `FinDist.map_map` is `protected` (it would clash with `Finset.map_map`),
  and so is the definition `FinDist.cond` (it would shadow `Bool.cond`); write `FinDist.map_map`
  and `μ.cond A hA`.
-/

public section


namespace EG

namespace FinDist

open Finset

variable {Ω α β ι : Type*}

/-! ### Weights and support -/

section Weights

variable (μ : FinDist Ω)

theorem mem_supp_iff_pos {ω : Ω} : ω ∈ μ.supp ↔ 0 < μ.w ω := by
  rw [mem_supp]
  exact ⟨fun h => lt_of_le_of_ne (μ.w_nonneg ω) (Ne.symm h), fun h => h.ne'⟩

theorem w_eq_zero_of_notMem_supp {ω : Ω} (h : ω ∉ μ.supp) : μ.w ω = 0 := by
  simpa [mem_supp] using h

theorem sum_w_of_supp_subset {s : Finset Ω} (hs : μ.supp ⊆ s) : ∑ ω ∈ s, μ.w ω = 1 := by
  rw [μ.sum_supp_eq_of_subset hs fun _ h => h, sum_w_supp]

/-- On a `Fintype`, the weights sum to `1`. -/
theorem sum_w [Fintype Ω] : ∑ ω, μ.w ω = 1 :=
  μ.sum_w_of_supp_subset (subset_univ _)

theorem w_le_one (ω : Ω) : μ.w ω ≤ 1 := by
  by_cases h : ω ∈ μ.supp
  · rw [← μ.sum_w_supp]
    exact single_le_sum (fun i _ => μ.w_nonneg i) h
  · rw [μ.w_eq_zero_of_notMem_supp h]
    exact zero_le_one

theorem supp_nonempty : μ.supp.Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro h
  have := μ.sum_w_supp
  rw [h, sum_empty] at this
  exact zero_ne_one this

/-- Some outcome has positive weight (in particular `Ω` is nonempty). -/
theorem exists_w_pos : ∃ ω, 0 < μ.w ω :=
  let ⟨ω, h⟩ := μ.supp_nonempty
  ⟨ω, (μ.mem_supp_iff_pos).1 h⟩

/-- A type carrying a distribution is nonempty. -/
protected theorem nonempty (ν : FinDist Ω) : Nonempty Ω :=
  let ⟨ω, _⟩ := ν.exists_w_pos
  ⟨ω⟩

end Weights

/-! ### Expectation -/

section Expect

variable (μ : FinDist Ω)

/-- The expectation is the weighted sum over any finite superset of the support. -/
theorem expect_eq_sum_of_supp_subset {s : Finset Ω} (hs : μ.supp ⊆ s) (X : Ω → ℝ) :
    μ.expect X = ∑ ω ∈ s, μ.w ω * X ω :=
  (μ.sum_supp_eq_of_subset hs fun ω h => by rw [h, zero_mul]).symm

/-- On a `Fintype`, `E X = ∑ ω, w ω * X ω`. -/
theorem expect_eq_sum [Fintype Ω] (X : Ω → ℝ) : μ.expect X = ∑ ω, μ.w ω * X ω :=
  μ.expect_eq_sum_of_supp_subset (subset_univ _) X

/-- The expectation only depends on the values on outcomes of positive weight. -/
theorem expect_congr {X Y : Ω → ℝ} (h : ∀ ω, 0 < μ.w ω → X ω = Y ω) :
    μ.expect X = μ.expect Y :=
  sum_congr rfl fun ω hω => by rw [h ω ((μ.mem_supp_iff_pos).1 hω)]

@[simp] theorem expect_const (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect]
  rw [← sum_mul, sum_w_supp, one_mul]

@[simp] theorem expect_zero : μ.expect 0 = 0 := by
  simp [expect]

theorem expect_add (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp only [expect, mul_add, sum_add_distrib]

theorem expect_neg (X : Ω → ℝ) : μ.expect (fun ω => -X ω) = -μ.expect X := by
  simp only [expect, mul_neg, sum_neg_distrib]

theorem expect_sub (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω - Y ω) = μ.expect X - μ.expect Y := by
  simp only [expect, mul_sub, sum_sub_distrib]

theorem expect_const_mul (c : ℝ) (X : Ω → ℝ) :
    μ.expect (fun ω => c * X ω) = c * μ.expect X := by
  simp only [expect, mul_sum]
  exact sum_congr rfl fun ω _ => by ring

theorem expect_mul_const (X : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => X ω * c) = μ.expect X * c := by
  simp only [expect, sum_mul]
  exact sum_congr rfl fun ω _ => by ring

theorem expect_div_const (X : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => X ω / c) = μ.expect X / c := by
  simp only [div_eq_mul_inv]
  exact μ.expect_mul_const X c⁻¹

/-- Linearity of expectation over a finite sum. -/
theorem expect_sum (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.expect (X i) := by
  simp only [expect, mul_sum]
  exact sum_comm

/-- Monotonicity of expectation (almost-sure form). -/
theorem expect_mono_ae {X Y : Ω → ℝ} (h : ∀ ω, 0 < μ.w ω → X ω ≤ Y ω) :
    μ.expect X ≤ μ.expect Y :=
  sum_le_sum fun ω hω =>
    mul_le_mul_of_nonneg_left (h ω ((μ.mem_supp_iff_pos).1 hω)) (μ.w_nonneg ω)

theorem expect_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : μ.expect X ≤ μ.expect Y :=
  μ.expect_mono_ae fun ω _ => h ω

theorem expect_nonneg_ae {X : Ω → ℝ} (h : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) : 0 ≤ μ.expect X := by
  simpa using μ.expect_mono_ae (X := fun _ => 0) h

theorem expect_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X :=
  μ.expect_nonneg_ae fun ω _ => h ω

theorem expect_le_of_le {X : Ω → ℝ} {c : ℝ} (h : ∀ ω, X ω ≤ c) : μ.expect X ≤ c := by
  simpa using μ.expect_mono (Y := fun _ => c) h

theorem le_expect_of_le {X : Ω → ℝ} {c : ℝ} (h : ∀ ω, c ≤ X ω) : c ≤ μ.expect X := by
  simpa using μ.expect_mono (X := fun _ => c) h

/-- A variable that is almost surely nonnegative has expectation zero iff it vanishes almost
surely. -/
theorem expect_eq_zero_iff_ae {X : Ω → ℝ} (hX : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) :
    μ.expect X = 0 ↔ ∀ ω, 0 < μ.w ω → X ω = 0 := by
  rw [expect, sum_eq_zero_iff_of_nonneg fun ω hω =>
    mul_nonneg (μ.w_nonneg ω) (hX ω ((μ.mem_supp_iff_pos).1 hω))]
  refine ⟨fun h ω hω => ?_, fun h ω hω => ?_⟩
  · have := h ω ((μ.mem_supp_iff_pos).2 hω)
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hω.ne'
    · exact h'
  · rw [h ω ((μ.mem_supp_iff_pos).1 hω), mul_zero]

/-- A nonnegative variable has expectation zero iff it vanishes almost surely. -/
theorem expect_eq_zero_iff {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) :
    μ.expect X = 0 ↔ ∀ ω, 0 < μ.w ω → X ω = 0 :=
  μ.expect_eq_zero_iff_ae fun ω _ => hX ω

end Expect

/-! ### Probability -/

section Prob

variable (μ : FinDist Ω)

/-- The probability is the total weight of `A` over any finite superset of the support. -/
theorem prob_eq_sum_of_supp_subset {s : Finset Ω} (hs : μ.supp ⊆ s) (A : Set Ω) :
    μ.prob A = ∑ ω ∈ s, A.indicator μ.w ω :=
  (μ.sum_supp_eq_of_subset hs fun _ h => Set.indicator_apply_eq_zero.2 fun _ => h).symm

theorem prob_eq_sum [Fintype Ω] (A : Set Ω) : μ.prob A = ∑ ω, A.indicator μ.w ω :=
  μ.prob_eq_sum_of_supp_subset (subset_univ _) A

/-- On a `Fintype`, `P(A) = ∑_{ω ∈ A} w ω`. -/
theorem prob_eq_sum_filter [Fintype Ω] (A : Set Ω) [DecidablePred (· ∈ A)] :
    μ.prob A = ∑ ω ∈ univ.filter (· ∈ A), μ.w ω := by
  rw [prob_eq_sum, sum_filter]
  exact sum_congr rfl fun ω _ => Set.indicator_apply A μ.w ω

/-- `P(A) = E[1_A]`. -/
theorem prob_eq_expect (A : Set Ω) : μ.prob A = μ.expect (A.indicator 1) := by
  classical
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : ω ∈ A <;> simp [h]

/-- The probability of a finite set of outcomes is the sum of their weights. -/
theorem prob_coe_finset (s : Finset Ω) : μ.prob ↑s = ∑ ω ∈ s, μ.w ω := by
  classical
  rw [μ.prob_eq_sum_of_supp_subset (subset_union_left (s₂ := s)),
    sum_indicator_subset _ subset_union_right]

@[simp] theorem prob_singleton (ω : Ω) : μ.prob {ω} = μ.w ω := by
  simpa using μ.prob_coe_finset {ω}

theorem prob_nonneg (A : Set Ω) : 0 ≤ μ.prob A :=
  sum_nonneg fun ω _ => Set.indicator_nonneg (fun ω _ => μ.w_nonneg ω) ω

@[simp] theorem prob_univ : μ.prob Set.univ = 1 := by
  simp [prob, sum_w_supp]

@[simp] theorem prob_empty : μ.prob ∅ = 0 := by
  simp [prob]

/-- The probability of an event only depends on its outcomes of positive weight. -/
theorem prob_congr {A B : Set Ω} (h : ∀ ω, 0 < μ.w ω → (ω ∈ A ↔ ω ∈ B)) :
    μ.prob A = μ.prob B := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  refine μ.expect_congr fun ω hω => ?_
  by_cases hA : ω ∈ A
  · simp [hA, (h ω hω).1 hA]
  · simp [hA, mt (h ω hω).2 hA]

theorem prob_mono {A B : Set Ω} (h : A ⊆ B) : μ.prob A ≤ μ.prob B :=
  sum_le_sum fun ω _ => Set.indicator_le_indicator_of_subset h (fun ω => μ.w_nonneg ω) ω

theorem prob_mono_ae {A B : Set Ω} (h : ∀ ω, 0 < μ.w ω → ω ∈ A → ω ∈ B) :
    μ.prob A ≤ μ.prob B := by
  calc μ.prob A = μ.prob (A ∩ B) := μ.prob_congr fun ω hω =>
          ⟨fun hA => ⟨hA, h ω hω hA⟩, fun hAB => hAB.1⟩
    _ ≤ μ.prob B := μ.prob_mono Set.inter_subset_right

theorem prob_le_one (A : Set Ω) : μ.prob A ≤ 1 :=
  (μ.prob_mono (Set.subset_univ A)).trans_eq μ.prob_univ

theorem prob_union_add_inter (A B : Set Ω) :
    μ.prob (A ∪ B) + μ.prob (A ∩ B) = μ.prob A + μ.prob B := by
  simp only [prob, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => Set.indicator_union_add_inter_apply μ.w A B ω

/-- Union bound for two events. -/
theorem prob_union_le (A B : Set Ω) : μ.prob (A ∪ B) ≤ μ.prob A + μ.prob B := by
  linarith [μ.prob_union_add_inter A B, μ.prob_nonneg (A ∩ B)]

theorem prob_union_of_disjoint {A B : Set Ω} (h : Disjoint A B) :
    μ.prob (A ∪ B) = μ.prob A + μ.prob B := by
  have := μ.prob_union_add_inter A B
  rwa [Set.disjoint_iff_inter_eq_empty.1 h, prob_empty, add_zero] at this

theorem prob_add_prob_compl (A : Set Ω) : μ.prob A + μ.prob Aᶜ = 1 := by
  rw [← μ.prob_union_of_disjoint disjoint_compl_right, Set.union_compl_self, prob_univ]

/-- `P(Aᶜ) = 1 - P(A)`. -/
theorem prob_compl (A : Set Ω) : μ.prob Aᶜ = 1 - μ.prob A := by
  linarith [μ.prob_add_prob_compl A]

theorem prob_inter_add_diff (A B : Set Ω) : μ.prob (A ∩ B) + μ.prob (A \ B) = μ.prob A := by
  rw [← μ.prob_union_of_disjoint (Set.disjoint_sdiff_inter.symm), Set.inter_union_sdiff]

theorem prob_diff_ge (A B : Set Ω) : μ.prob A - μ.prob B ≤ μ.prob (A \ B) := by
  linarith [μ.prob_inter_add_diff A B, μ.prob_mono (Set.inter_subset_right (s := A) (t := B))]

/-- `P(A ∩ B) ≥ P(A) + P(B) - 1`. -/
theorem prob_inter_ge (A B : Set Ω) : μ.prob A + μ.prob B - 1 ≤ μ.prob (A ∩ B) := by
  linarith [μ.prob_union_add_inter A B, μ.prob_le_one (A ∪ B)]

/-- Union bound over a finite family of events. -/
theorem prob_biUnion_le (s : Finset ι) (A : ι → Set Ω) :
    μ.prob (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.prob (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, sum_insert hi]
    exact (μ.prob_union_le _ _).trans (add_le_add_right ih _)

/-- Union bound over a `Fintype`-indexed family of events. -/
theorem prob_iUnion_le [Fintype ι] (A : ι → Set Ω) : μ.prob (⋃ i, A i) ≤ ∑ i, μ.prob (A i) := by
  simpa using μ.prob_biUnion_le univ A

/-- All events of a finite family hold with probability at least `1 - ∑ P(failure)`. -/
theorem prob_biInter_ge (s : Finset ι) (A : ι → Set Ω) :
    1 - ∑ i ∈ s, μ.prob (A i)ᶜ ≤ μ.prob (⋂ i ∈ s, A i) := by
  have h := μ.prob_biUnion_le s fun i => (A i)ᶜ
  rw [← Set.compl_iInter₂, prob_compl] at h
  linarith

theorem prob_eq_zero_iff (A : Set Ω) : μ.prob A = 0 ↔ ∀ ω ∈ A, μ.w ω = 0 := by
  rw [prob, sum_eq_zero_iff_of_nonneg fun ω _ =>
    Set.indicator_nonneg (fun ω _ => μ.w_nonneg ω) ω]
  refine ⟨fun h ω hωA => ?_, fun h ω _ => Set.indicator_apply_eq_zero.2 (h ω)⟩
  by_contra hω
  have := h ω (mem_supp.2 hω)
  rw [Set.indicator_of_mem hωA] at this
  exact hω this

theorem prob_pos_iff (A : Set Ω) : 0 < μ.prob A ↔ ∃ ω ∈ A, 0 < μ.w ω := by
  rw [(μ.prob_nonneg A).lt_iff_ne', Ne, prob_eq_zero_iff]
  simp only [not_forall, exists_prop]
  refine ⟨fun ⟨ω, hA, hω⟩ => ⟨ω, hA, lt_of_le_of_ne (μ.w_nonneg ω) (Ne.symm hω)⟩,
    fun ⟨ω, hA, hω⟩ => ⟨ω, hA, hω.ne'⟩⟩

theorem prob_eq_one_iff (A : Set Ω) : μ.prob A = 1 ↔ ∀ ω, 0 < μ.w ω → ω ∈ A := by
  have h := μ.prob_compl A
  constructor
  · intro h1 ω hω
    by_contra hA
    have h0 : μ.prob Aᶜ = 0 := by rw [h, h1, sub_self]
    exact hω.ne' ((μ.prob_eq_zero_iff _).1 h0 ω hA)
  · intro hA
    have h0 : μ.prob Aᶜ = 0 := (μ.prob_eq_zero_iff _).2 fun ω hω => by
      by_contra hne
      exact hω (hA ω (lt_of_le_of_ne (μ.w_nonneg ω) (Ne.symm hne)))
    linarith

/-- `E[∑_{i ∈ s} 1_{A_i}] = ∑_{i ∈ s} P(A_i)`. -/
theorem expect_sum_indicator (s : Finset ι) (A : ι → Set Ω) :
    μ.expect (fun ω => ∑ i ∈ s, (A i).indicator 1 ω) = ∑ i ∈ s, μ.prob (A i) := by
  rw [μ.expect_sum s fun i => (A i).indicator 1]
  exact sum_congr rfl fun i _ => (μ.prob_eq_expect _).symm

/-- First moment: the expected number of events of a finite family that occur is the sum of
their probabilities. -/
theorem expect_card_filter (s : Finset ι) (A : ι → Set Ω)
    [∀ ω, DecidablePred fun i => ω ∈ A i] :
    μ.expect (fun ω => ((s.filter fun i => ω ∈ A i).card : ℝ)) = ∑ i ∈ s, μ.prob (A i) := by
  rw [← μ.expect_sum_indicator]
  congr 1
  funext ω
  rw [card_filter, Nat.cast_sum]
  exact sum_congr rfl fun i _ => by by_cases h : ω ∈ A i <;> simp [h]

end Prob

/-! ### Existence principles -/

section Exists

variable (μ : FinDist Ω)

/-- An event of positive probability contains an outcome (of positive weight). -/
theorem exists_of_prob_pos {A : Set Ω} (h : 0 < μ.prob A) : ∃ ω ∈ A, 0 < μ.w ω :=
  (μ.prob_pos_iff A).1 h

theorem nonempty_of_prob_pos {A : Set Ω} (h : 0 < μ.prob A) : A.Nonempty :=
  let ⟨ω, hω, _⟩ := μ.exists_of_prob_pos h
  ⟨ω, hω⟩

/-- Some outcome of positive weight has `X ω ≤ E X`. -/
theorem exists_le_expect (X : Ω → ℝ) : ∃ ω, 0 < μ.w ω ∧ X ω ≤ μ.expect X := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  have hlt : μ.expect (fun _ => μ.expect X) < μ.expect X :=
    sum_lt_sum_of_nonempty μ.supp_nonempty fun ω hω => by
      have hpos := (μ.mem_supp_iff_pos).1 hω
      exact mul_lt_mul_of_pos_left (h ω hpos) hpos
  rw [expect_const] at hlt
  exact lt_irrefl _ hlt

/-- Some outcome of positive weight has `X ω ≥ E X`. -/
theorem exists_ge_expect (X : Ω → ℝ) : ∃ ω, 0 < μ.w ω ∧ μ.expect X ≤ X ω := by
  obtain ⟨ω, hω, h⟩ := μ.exists_le_expect fun ω => -X ω
  rw [expect_neg] at h
  exact ⟨ω, hω, neg_le_neg_iff.1 h⟩

/-- Two events whose probabilities sum to more than `1` have a common outcome (of positive
weight). -/
theorem exists_mem_inter_of_one_lt_add {A B : Set Ω} (h : 1 < μ.prob A + μ.prob B) :
    ∃ ω ∈ A ∩ B, 0 < μ.w ω :=
  μ.exists_of_prob_pos (by linarith [μ.prob_inter_ge A B])

/-- Union bound, existence form: if the failure probabilities sum to less than `1`, some outcome
(of positive weight) avoids all failure events. -/
theorem exists_forall_notMem_of_sum_lt_one (s : Finset ι) (A : ι → Set Ω)
    (h : ∑ i ∈ s, μ.prob (A i) < 1) : ∃ ω, 0 < μ.w ω ∧ ∀ i ∈ s, ω ∉ A i := by
  have h' := μ.prob_biInter_ge s fun i => (A i)ᶜ
  simp only [compl_compl] at h'
  obtain ⟨ω, hω, hpos⟩ := μ.exists_of_prob_pos (by linarith : 0 < μ.prob (⋂ i ∈ s, (A i)ᶜ))
  simp only [Set.mem_iInter, Set.mem_compl_iff] at hω
  exact ⟨ω, hpos, hω⟩

end Exists

/-! ### Markov's inequality [s1:citMarkov]

The manuscript's hypothesis "X ≥ 0" is `hX : ∀ ω, 0 ≤ X ω`. Each lemma also has an `_ae`
variant whose hypothesis is only `∀ ω, 0 < μ.w ω → 0 ≤ X ω` (nonnegative on the outcomes of
positive weight, e.g. after conditioning); the pointwise versions are corollaries. -/

section Markov

variable (μ : FinDist Ω) {X : Ω → ℝ}

/-- Markov's inequality, multiplied out, for `X ≥ 0` almost surely. -/
theorem mul_prob_le_expect_ae (hX : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) (a : ℝ) :
    a * μ.prob {ω | a ≤ X ω} ≤ μ.expect X := by
  classical
  rw [prob_eq_expect, ← expect_const_mul]
  refine μ.expect_mono_ae fun ω hω => ?_
  by_cases h : a ≤ X ω
  · simp [h]
  · simp [Set.indicator_of_notMem (show ω ∉ {ω | a ≤ X ω} from h), hX ω hω]

/-- Markov's inequality, multiplied out: for `X ≥ 0` and every `a`, `a · P(X ≥ a) ≤ E X`. -/
theorem mul_prob_le_expect (hX : ∀ ω, 0 ≤ X ω) (a : ℝ) :
    a * μ.prob {ω | a ≤ X ω} ≤ μ.expect X :=
  μ.mul_prob_le_expect_ae (fun ω _ => hX ω) a

/-- [s1:citMarkov] for `X ≥ 0` almost surely. -/
theorem prob_le_expect_div_ae (hX : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    μ.prob {ω | a ≤ X ω} ≤ μ.expect X / a := by
  rw [le_div_iff₀ ha, mul_comm]
  exact μ.mul_prob_le_expect_ae hX a

/-- [s1:citMarkov] "If X ≥ 0 and a > 0 then P(X ≥ a) ≤ E X / a." -/
theorem prob_le_expect_div (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 < a) :
    μ.prob {ω | a ≤ X ω} ≤ μ.expect X / a :=
  μ.prob_le_expect_div_ae (fun ω _ => hX ω) ha

/-- For `X ≥ 0` almost surely and `c > 0`: `P(X > c · E X) ≤ 1 / c` (also when `E X = 0`). -/
theorem prob_gt_mul_expect_le_ae (hX : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) {c : ℝ} (hc : 0 < c) :
    μ.prob {ω | c * μ.expect X < X ω} ≤ 1 / c := by
  rcases (μ.expect_nonneg_ae hX).eq_or_lt with h0 | hpos
  · have : μ.prob {ω | c * μ.expect X < X ω} = 0 := by
      refine (μ.prob_eq_zero_iff _).2 fun ω hω => ?_
      by_contra hw
      have hX0 := (μ.expect_eq_zero_iff_ae hX).1 h0.symm ω
        (lt_of_le_of_ne (μ.w_nonneg ω) (Ne.symm hw))
      simp only [Set.mem_ofPred_eq, ← h0, mul_zero, hX0, lt_self_iff_false] at hω
    rw [this]
    positivity
  · calc μ.prob {ω | c * μ.expect X < X ω} ≤ μ.prob {ω | c * μ.expect X ≤ X ω} :=
          μ.prob_mono fun ω (h : c * μ.expect X < X ω) => (le_of_lt h : c * μ.expect X ≤ X ω)
      _ ≤ μ.expect X / (c * μ.expect X) := μ.prob_le_expect_div_ae hX (mul_pos hc hpos)
      _ = 1 / c := by rw [div_mul_eq_div_div_swap, div_self hpos.ne']

/-- For `X ≥ 0` and `c > 0`: `P(X > c · E X) ≤ 1 / c` (also when `E X = 0`). -/
theorem prob_gt_mul_expect_le (hX : ∀ ω, 0 ≤ X ω) {c : ℝ} (hc : 0 < c) :
    μ.prob {ω | c * μ.expect X < X ω} ≤ 1 / c :=
  μ.prob_gt_mul_expect_le_ae (fun ω _ => hX ω) hc

/-- For `X ≥ 0` almost surely and `c > 0`: `P(X ≤ c · E X) ≥ 1 - 1 / c`. -/
theorem one_sub_inv_le_prob_le_mul_expect_ae (hX : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) {c : ℝ}
    (hc : 0 < c) : 1 - 1 / c ≤ μ.prob {ω | X ω ≤ c * μ.expect X} := by
  have hcompl : {ω | X ω ≤ c * μ.expect X}ᶜ = {ω | c * μ.expect X < X ω} := by
    ext ω
    simp [not_le]
  have h := μ.prob_add_prob_compl {ω | X ω ≤ c * μ.expect X}
  rw [hcompl] at h
  linarith [μ.prob_gt_mul_expect_le_ae hX hc]

/-- For `X ≥ 0` and `c > 0`: `P(X ≤ c · E X) ≥ 1 - 1 / c`. -/
theorem one_sub_inv_le_prob_le_mul_expect (hX : ∀ ω, 0 ≤ X ω) {c : ℝ} (hc : 0 < c) :
    1 - 1 / c ≤ μ.prob {ω | X ω ≤ c * μ.expect X} :=
  μ.one_sub_inv_le_prob_le_mul_expect_ae (fun ω _ => hX ω) hc

/-- [s1:citMarkov](a) for `X ≥ 0` almost surely. -/
theorem two_thirds_le_prob_le_three_mul_expect_ae (hX : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) :
    2 / 3 ≤ μ.prob {ω | X ω ≤ 3 * μ.expect X} := by
  have := μ.one_sub_inv_le_prob_le_mul_expect_ae hX (c := 3) (by norm_num)
  linarith

/-- [s1:citMarkov](a) "for X ≥ 0, P(X ≤ 3 E X) ≥ 2/3". -/
theorem two_thirds_le_prob_le_three_mul_expect (hX : ∀ ω, 0 ≤ X ω) :
    2 / 3 ≤ μ.prob {ω | X ω ≤ 3 * μ.expect X} :=
  μ.two_thirds_le_prob_le_three_mul_expect_ae fun ω _ => hX ω

/-- Two-variable Markov for variables that are almost surely nonnegative. -/
theorem one_sub_inv_sub_inv_le_prob_and_ae {X₁ X₂ : Ω → ℝ} (hX₁ : ∀ ω, 0 < μ.w ω → 0 ≤ X₁ ω)
    (hX₂ : ∀ ω, 0 < μ.w ω → 0 ≤ X₂ ω) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    1 - 1 / c₁ - 1 / c₂ ≤
      μ.prob {ω | X₁ ω ≤ c₁ * μ.expect X₁ ∧ X₂ ω ≤ c₂ * μ.expect X₂} := by
  have h := μ.prob_inter_ge {ω | X₁ ω ≤ c₁ * μ.expect X₁} {ω | X₂ ω ≤ c₂ * μ.expect X₂}
  have h₁ := μ.one_sub_inv_le_prob_le_mul_expect_ae hX₁ hc₁
  have h₂ := μ.one_sub_inv_le_prob_le_mul_expect_ae hX₂ hc₂
  have : {ω | X₁ ω ≤ c₁ * μ.expect X₁} ∩ {ω | X₂ ω ≤ c₂ * μ.expect X₂} =
      {ω | X₁ ω ≤ c₁ * μ.expect X₁ ∧ X₂ ω ≤ c₂ * μ.expect X₂} := rfl
  rw [this] at h
  linarith

/-- Two-variable Markov: `P(X₁ ≤ c₁ E X₁ ∧ X₂ ≤ c₂ E X₂) ≥ 1 - 1/c₁ - 1/c₂`. -/
theorem one_sub_inv_sub_inv_le_prob_and {X₁ X₂ : Ω → ℝ} (hX₁ : ∀ ω, 0 ≤ X₁ ω)
    (hX₂ : ∀ ω, 0 ≤ X₂ ω) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    1 - 1 / c₁ - 1 / c₂ ≤
      μ.prob {ω | X₁ ω ≤ c₁ * μ.expect X₁ ∧ X₂ ω ≤ c₂ * μ.expect X₂} :=
  μ.one_sub_inv_sub_inv_le_prob_and_ae (fun ω _ => hX₁ ω) (fun ω _ => hX₂ ω) hc₁ hc₂

/-- [s1:citMarkov](b) for variables that are almost surely nonnegative. -/
theorem half_le_prob_le_four_mul_expect_and_ae {X₁ X₂ : Ω → ℝ}
    (hX₁ : ∀ ω, 0 < μ.w ω → 0 ≤ X₁ ω) (hX₂ : ∀ ω, 0 < μ.w ω → 0 ≤ X₂ ω) :
    1 / 2 ≤ μ.prob {ω | X₁ ω ≤ 4 * μ.expect X₁ ∧ X₂ ω ≤ 4 * μ.expect X₂} := by
  have := μ.one_sub_inv_sub_inv_le_prob_and_ae hX₁ hX₂ (c₁ := 4) (c₂ := 4) (by norm_num)
    (by norm_num)
  linarith

/-- [s1:citMarkov](b) "for X₁, X₂ ≥ 0, P(X₁ ≤ 4 E X₁ and X₂ ≤ 4 E X₂) ≥ 1/2". -/
theorem half_le_prob_le_four_mul_expect_and {X₁ X₂ : Ω → ℝ} (hX₁ : ∀ ω, 0 ≤ X₁ ω)
    (hX₂ : ∀ ω, 0 ≤ X₂ ω) :
    1 / 2 ≤ μ.prob {ω | X₁ ω ≤ 4 * μ.expect X₁ ∧ X₂ ω ≤ 4 * μ.expect X₂} :=
  μ.half_le_prob_le_four_mul_expect_and_ae (fun ω _ => hX₁ ω) fun ω _ => hX₂ ω

/-- Markov combined with an event, for `X ≥ 0` almost surely: if `P(A) > 1/c`, then some
outcome of positive weight lies in `A` and has `X ω ≤ c · E X`. -/
theorem exists_mem_le_mul_expect_ae (hX : ∀ ω, 0 < μ.w ω → 0 ≤ X ω) {c : ℝ} (hc : 0 < c)
    {A : Set Ω} (hA : 1 / c < μ.prob A) : ∃ ω ∈ A, 0 < μ.w ω ∧ X ω ≤ c * μ.expect X := by
  have h := μ.prob_inter_ge A {ω | X ω ≤ c * μ.expect X}
  have h' := μ.one_sub_inv_le_prob_le_mul_expect_ae hX hc
  obtain ⟨ω, ⟨hωA, hωX⟩, hpos⟩ :=
    μ.exists_of_prob_pos (by linarith : 0 < μ.prob (A ∩ {ω | X ω ≤ c * μ.expect X}))
  exact ⟨ω, hωA, hpos, hωX⟩

/-- Markov combined with an event: if `P(A) > 1/c`, then some outcome of positive weight lies in
`A` and has `X ω ≤ c · E X`. -/
theorem exists_mem_le_mul_expect (hX : ∀ ω, 0 ≤ X ω) {c : ℝ} (hc : 0 < c) {A : Set Ω}
    (hA : 1 / c < μ.prob A) : ∃ ω ∈ A, 0 < μ.w ω ∧ X ω ≤ c * μ.expect X :=
  μ.exists_mem_le_mul_expect_ae (fun ω _ => hX ω) hc hA

end Markov

/-! ### Conditioning on an event -/

section Cond

variable (μ : FinDist Ω) {A : Set Ω} (hA : 0 < μ.prob A)

theorem cond_w (ω : Ω) : (μ.cond A hA).w ω = A.indicator μ.w ω / μ.prob A := rfl

theorem supp_cond_subset : (μ.cond A hA).supp ⊆ μ.supp :=
  supp_subset fun ω hω => by
    rw [cond_w, Set.indicator_apply_eq_zero.2 fun _ => μ.w_eq_zero_of_notMem_supp hω, zero_div]

theorem cond_w_pos_iff {ω : Ω} : 0 < (μ.cond A hA).w ω ↔ ω ∈ A ∧ 0 < μ.w ω := by
  classical
  rw [cond_w, div_pos_iff_of_pos_right hA]
  by_cases h : ω ∈ A <;> simp [h]

/-- Conditional expectation given `A`: `E[X | A] = E[X · 1_A] / P(A)`. -/
theorem expect_cond (X : Ω → ℝ) :
    (μ.cond A hA).expect X = μ.expect (A.indicator X) / μ.prob A := by
  classical
  rw [expect_eq_sum_of_supp_subset _ (μ.supp_cond_subset hA), expect, sum_div]
  refine sum_congr rfl fun ω _ => ?_
  rw [cond_w]
  by_cases h : ω ∈ A
  · simp [h, div_mul_eq_mul_div]
  · simp [h]

/-- Conditional probability: `P(B | A) = P(B ∩ A) / P(A)`. -/
theorem prob_cond (B : Set Ω) : (μ.cond A hA).prob B = μ.prob (B ∩ A) / μ.prob A := by
  rw [prob_eq_expect, expect_cond, Set.indicator_indicator, Set.inter_comm, ← prob_eq_expect]

@[simp] theorem prob_cond_self : (μ.cond A hA).prob A = 1 := by
  rw [prob_cond, Set.inter_self, div_self hA.ne']

include hA in
/-- An outcome of `A` (of positive weight) at which a nonnegative `X` is at most
`E X / P(A)`. -/
theorem exists_mem_le_expect_div {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) :
    ∃ ω ∈ A, 0 < μ.w ω ∧ X ω ≤ μ.expect X / μ.prob A := by
  classical
  obtain ⟨ω, hω, hle⟩ := (μ.cond A hA).exists_le_expect X
  rw [cond_w_pos_iff] at hω
  refine ⟨ω, hω.1, hω.2, hle.trans ?_⟩
  rw [expect_cond]
  refine div_le_div_of_nonneg_right (μ.expect_mono fun ω' => ?_) hA.le
  by_cases h : ω' ∈ A
  · simp [h]
  · simp [h, hX ω']

include hA in
/-- A variable that is nonnegative on the outcomes of `A` of positive weight is almost surely
nonnegative under `μ.cond A hA`. -/
theorem nonneg_ae_cond {X : Ω → ℝ} (hX : ∀ ω ∈ A, 0 < μ.w ω → 0 ≤ X ω) :
    ∀ ω, 0 < (μ.cond A hA).w ω → 0 ≤ X ω := fun ω hω => by
  rw [cond_w_pos_iff] at hω
  exact hX ω hω.1 hω.2

/-- [s1:citMarkov](c), form (a) conditional on an event `A` of positive probability, for `X`
nonnegative on `A` (on the outcomes of positive weight). -/
theorem two_thirds_mul_prob_le_prob_inter_cond_ae {X : Ω → ℝ}
    (hX : ∀ ω ∈ A, 0 < μ.w ω → 0 ≤ X ω) :
    2 / 3 * μ.prob A ≤ μ.prob (A ∩ {ω | X ω ≤ 3 * (μ.cond A hA).expect X}) := by
  have h := (μ.cond A hA).two_thirds_le_prob_le_three_mul_expect_ae (μ.nonneg_ae_cond hA hX)
  rw [prob_cond, le_div_iff₀ hA, Set.inter_comm] at h
  exact h

/-- [s1:citMarkov](c), form (a) conditional on an event `A` of positive probability:
`P(A ∩ {X ≤ 3 E[X | A]}) ≥ (2/3) P(A)`. -/
theorem two_thirds_mul_prob_le_prob_inter_cond {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) :
    2 / 3 * μ.prob A ≤ μ.prob (A ∩ {ω | X ω ≤ 3 * (μ.cond A hA).expect X}) :=
  μ.two_thirds_mul_prob_le_prob_inter_cond_ae hA fun ω _ _ => hX ω

/-- [s1:citMarkov](c), form (b) conditional on an event `A` of positive probability, for
variables nonnegative on `A` (on the outcomes of positive weight). -/
theorem half_mul_prob_le_prob_inter_cond_ae {X₁ X₂ : Ω → ℝ}
    (hX₁ : ∀ ω ∈ A, 0 < μ.w ω → 0 ≤ X₁ ω) (hX₂ : ∀ ω ∈ A, 0 < μ.w ω → 0 ≤ X₂ ω) :
    1 / 2 * μ.prob A ≤ μ.prob (A ∩ {ω | X₁ ω ≤ 4 * (μ.cond A hA).expect X₁ ∧
      X₂ ω ≤ 4 * (μ.cond A hA).expect X₂}) := by
  have h := (μ.cond A hA).half_le_prob_le_four_mul_expect_and_ae (μ.nonneg_ae_cond hA hX₁)
    (μ.nonneg_ae_cond hA hX₂)
  rw [prob_cond, le_div_iff₀ hA, Set.inter_comm] at h
  exact h

/-- [s1:citMarkov](c), form (b) conditional on an event `A` of positive probability. -/
theorem half_mul_prob_le_prob_inter_cond {X₁ X₂ : Ω → ℝ} (hX₁ : ∀ ω, 0 ≤ X₁ ω)
    (hX₂ : ∀ ω, 0 ≤ X₂ ω) :
    1 / 2 * μ.prob A ≤ μ.prob (A ∩ {ω | X₁ ω ≤ 4 * (μ.cond A hA).expect X₁ ∧
      X₂ ω ≤ 4 * (μ.cond A hA).expect X₂}) :=
  μ.half_mul_prob_le_prob_inter_cond_ae hA (fun ω _ _ => hX₁ ω) fun ω _ _ => hX₂ ω

end Cond

/-! ### Point mass -/

section Dirac

theorem dirac_w (a ω : Ω) [Decidable (ω = a)] : (dirac a).w ω = if ω = a then 1 else 0 := by
  by_cases h : ω = a
  · simp [dirac, h]
  · simp [dirac, h]

@[simp] theorem dirac_w_self (a : Ω) : (dirac a).w a = 1 := by
  simp [dirac]

theorem dirac_w_of_ne {a ω : Ω} (h : ω ≠ a) : (dirac a).w ω = 0 := by
  simp [dirac, h]

@[simp] theorem supp_dirac (a : Ω) : (dirac a).supp = {a} := by
  ext ω
  rw [mem_supp, Finset.mem_singleton]
  by_cases h : ω = a
  · simp [h]
  · simp [h, dirac_w_of_ne h]

@[simp] theorem expect_dirac (a : Ω) (X : Ω → ℝ) : (dirac a).expect X = X a := by
  rw [expect, supp_dirac, sum_singleton, dirac_w_self, one_mul]

theorem prob_dirac (a : Ω) (A : Set Ω) : (dirac a).prob A = A.indicator 1 a := by
  rw [prob_eq_expect, expect_dirac]

theorem prob_dirac_of_mem {a : Ω} {A : Set Ω} (h : a ∈ A) : (dirac a).prob A = 1 := by
  rw [prob_dirac, Set.indicator_of_mem h, Pi.one_apply]

theorem prob_dirac_of_notMem {a : Ω} {A : Set Ω} (h : a ∉ A) : (dirac a).prob A = 0 := by
  rw [prob_dirac, Set.indicator_of_notMem h]

end Dirac

/-! ### Pushforward -/

section Map

variable {γ : Type*} (μ : FinDist α)

theorem map_w (f : α → β) (b : β) : (μ.map f).w b = μ.prob (f ⁻¹' {b}) := rfl

theorem supp_map_subset [DecidableEq β] (f : α → β) : (μ.map f).supp ⊆ μ.supp.image f :=
  supp_subset fun b hb => by
    rw [map_w, prob]
    exact sum_eq_zero fun a ha => Set.indicator_of_notMem (show a ∉ f ⁻¹' {b} from fun h =>
      hb (mem_image.2 ⟨a, ha, Set.mem_singleton_iff.1 (Set.mem_preimage.1 h)⟩)) _

/-- The expectation under a pushforward: `E_{f_* μ} Y = E_μ (Y ∘ f)`. -/
theorem expect_map (f : α → β) (Y : β → ℝ) :
    (μ.map f).expect Y = μ.expect fun a => Y (f a) := by
  classical
  rw [expect_eq_sum_of_supp_subset _ (μ.supp_map_subset f)]
  simp only [map_w, prob, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a ha => ?_
  rw [sum_eq_single_of_mem (f a) (mem_image_of_mem f ha)]
  · rw [Set.indicator_of_mem (show a ∈ f ⁻¹' {f a} from rfl)]
  · intro b _ hb
    rw [Set.indicator_of_notMem (show a ∉ f ⁻¹' {b} from fun h =>
      hb (Set.mem_singleton_iff.1 (Set.mem_preimage.1 h)).symm), zero_mul]

/-- The probability under a pushforward: `P_{f_* μ}(B) = P_μ(f ⁻¹' B)`. -/
theorem prob_map (f : α → β) (B : Set β) : (μ.map f).prob B = μ.prob (f ⁻¹' B) := by
  classical
  rw [prob_eq_expect, expect_map, prob_eq_expect]
  congr 1

/-- Functoriality of `map`. `protected` (write `FinDist.map_map`): the short name would be
ambiguous with `Finset.map_map` when both namespaces are open. -/
protected theorem map_map (f : α → β) (g : β → γ) : (μ.map f).map g = μ.map (g ∘ f) := by
  ext c
  rw [map_w, prob_map, map_w]
  rfl

/-- The pushforward only depends on the values of the map on outcomes of positive weight. -/
theorem map_congr_ae {f g : α → β} (h : ∀ a, 0 < μ.w a → f a = g a) : μ.map f = μ.map g := by
  ext b
  rw [map_w, map_w]
  exact μ.prob_congr fun a ha => by simp only [Set.mem_preimage, h a ha]

@[simp] theorem map_id : μ.map id = μ := by
  ext a
  rw [map_w, Set.preimage_id, prob_singleton]

@[simp] theorem map_id' : μ.map (fun a => a) = μ :=
  μ.map_id

/-- Pushforward along an equivalence: `(e_* μ)(b) = μ(e⁻¹ b)`. -/
theorem map_equiv_w (e : α ≃ β) (b : β) : (μ.map e).w b = μ.w (e.symm b) := by
  rw [map_w, ← prob_singleton]
  congr 1
  ext a
  simp [Equiv.eq_symm_apply]

theorem map_dirac (f : α → β) (a : α) : (dirac a).map f = dirac (f a) := by
  classical
  ext b
  rw [map_w, prob_dirac]
  by_cases h : f a = b
  · subst h
    simp
  · rw [Set.indicator_of_notMem (show a ∉ f ⁻¹' {b} from h), dirac_w_of_ne (Ne.symm h)]

end Map

/-! ### Two-step experiments ("fixing a prefix") -/

section CompProd

variable (μ : FinDist α) (K : α → FinDist β)

theorem compProd_w (a : α) (b : β) : (μ.compProd K).w (a, b) = μ.w a * (K a).w b := rfl

theorem mem_supp_compProd {p : α × β} :
    p ∈ (μ.compProd K).supp ↔ p.1 ∈ μ.supp ∧ p.2 ∈ (K p.1).supp := by
  simp only [mem_supp]
  exact mul_ne_zero_iff

theorem supp_compProd_subset [DecidableEq β] :
    (μ.compProd K).supp ⊆ μ.supp ×ˢ μ.supp.biUnion fun a => (K a).supp := fun p hp => by
  rw [mem_supp_compProd] at hp
  exact mem_product.2 ⟨hp.1, mem_biUnion.2 ⟨p.1, hp.1, hp.2⟩⟩

/-- Fubini for a two-step experiment: `E Z = E_a E_{b ~ K a} Z (a, b)`. -/
theorem expect_compProd (Z : α × β → ℝ) :
    (μ.compProd K).expect Z = μ.expect fun a => (K a).expect fun b => Z (a, b) := by
  classical
  rw [expect_eq_sum_of_supp_subset _ (supp_compProd_subset μ K), sum_product]
  show _ = ∑ a ∈ μ.supp, μ.w a * (K a).expect fun b => Z (a, b)
  refine sum_congr rfl fun a ha => ?_
  rw [expect_eq_sum_of_supp_subset (K a) (subset_biUnion_of_mem (fun a => (K a).supp) ha),
    mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [compProd_w, mul_assoc]

/-- Conditioning on the first coordinate ("fixing a prefix"):
`P(A) = ∑_a w(a) · P_{K a}(A_a)`, where `A_a = {b | (a, b) ∈ A}` is the section of `A`. -/
theorem prob_compProd (A : Set (α × β)) :
    (μ.compProd K).prob A = μ.expect fun a => (K a).prob (Prod.mk a ⁻¹' A) := by
  classical
  rw [prob_eq_expect, expect_compProd]
  congr 1
  funext a
  rw [prob_eq_expect]
  congr 1

theorem prob_compProd_eq_sum [Fintype α] (A : Set (α × β)) :
    (μ.compProd K).prob A = ∑ a, μ.w a * (K a).prob (Prod.mk a ⁻¹' A) := by
  rw [prob_compProd, expect_eq_sum]

/-- Fixing a good prefix: some first coordinate of positive weight has a section at least as
likely as `A`. -/
theorem exists_le_prob_section (A : Set (α × β)) :
    ∃ a, 0 < μ.w a ∧ (μ.compProd K).prob A ≤ (K a).prob (Prod.mk a ⁻¹' A) := by
  rw [prob_compProd]
  exact μ.exists_ge_expect _

/-- If every section of `A` (over first coordinates of positive weight) has probability at
most `q`, then so does `A`. -/
theorem prob_compProd_le_of_forall {A : Set (α × β)} {q : ℝ}
    (h : ∀ a, 0 < μ.w a → (K a).prob (Prod.mk a ⁻¹' A) ≤ q) : (μ.compProd K).prob A ≤ q := by
  rw [prob_compProd]
  exact (μ.expect_mono_ae h).trans_eq (μ.expect_const q)

/-- If every section of `A` (over first coordinates of positive weight) has probability at
least `q`, then so does `A`. -/
theorem le_prob_compProd_of_forall {A : Set (α × β)} {q : ℝ}
    (h : ∀ a, 0 < μ.w a → q ≤ (K a).prob (Prod.mk a ⁻¹' A)) : q ≤ (μ.compProd K).prob A := by
  rw [prob_compProd]
  exact (μ.expect_const q).symm.trans_le (μ.expect_mono_ae h)

/-- The first coordinate of a two-step experiment has law `μ`. -/
@[simp] theorem map_fst_compProd : (μ.compProd K).map Prod.fst = μ := by
  classical
  ext a
  rw [map_w, prob_compProd, ← prob_singleton μ a, prob_eq_expect]
  refine μ.expect_congr fun a' _ => ?_
  by_cases h : a' = a
  · subst h
    have : Prod.mk a' ⁻¹' (Prod.fst ⁻¹' ({a'} : Set α)) = (Set.univ : Set β) := by
      ext b; simp
    rw [this, prob_univ, Set.indicator_of_mem (Set.mem_singleton a'), Pi.one_apply]
  · have : Prod.mk a' ⁻¹' (Prod.fst ⁻¹' ({a} : Set α)) = (∅ : Set β) := by
      ext b; simp [h]
    rw [this, prob_empty, Set.indicator_of_notMem (by simpa using h)]

theorem prob_compProd_fst (A : Set α) : (μ.compProd K).prob (Prod.fst ⁻¹' A) = μ.prob A := by
  rw [← prob_map, map_fst_compProd]

end CompProd

/-! ### Products of two independent distributions -/

section Prod

variable (μ : FinDist α) (ν : FinDist β)

theorem prod_w (a : α) (b : β) : (μ.prod ν).w (a, b) = μ.w a * ν.w b := rfl

theorem prod_w' (p : α × β) : (μ.prod ν).w p = μ.w p.1 * ν.w p.2 := rfl

/-- Fubini: `E Z = E_a E_b Z (a, b)`. -/
theorem expect_prod (Z : α × β → ℝ) :
    (μ.prod ν).expect Z = μ.expect fun a => ν.expect fun b => Z (a, b) :=
  expect_compProd μ _ Z

/-- Fubini in the other order: `E Z = E_b E_a Z (a, b)`. -/
theorem expect_prod_swap (Z : α × β → ℝ) :
    (μ.prod ν).expect Z = ν.expect fun b => μ.expect fun a => Z (a, b) := by
  rw [expect_prod]
  simp only [expect, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring

/-- Conditioning on the first coordinate: `P(A) = E_a P_ν(A_a)`. -/
theorem prob_prod (A : Set (α × β)) :
    (μ.prod ν).prob A = μ.expect fun a => ν.prob (Prod.mk a ⁻¹' A) :=
  prob_compProd μ _ A

/-- [PLAN §3 decision 3] Conditioning on a prefix, as a finite sum:
`P(A) = ∑_a w(a) · P_ν(A_a)`. -/
theorem prob_prod_eq_sum [Fintype α] (A : Set (α × β)) :
    (μ.prod ν).prob A = ∑ a, μ.w a * ν.prob (Prod.mk a ⁻¹' A) :=
  prob_compProd_eq_sum μ _ A

@[simp] theorem expect_prod_fst (X : α → ℝ) : (μ.prod ν).expect (fun p => X p.1) = μ.expect X := by
  simp [expect_prod]

@[simp] theorem expect_prod_snd (Y : β → ℝ) : (μ.prod ν).expect (fun p => Y p.2) = ν.expect Y := by
  simp [expect_prod]

/-- Independence of the coordinates: `E[X(a) Y(b)] = E X · E Y`. -/
theorem expect_prod_mul (X : α → ℝ) (Y : β → ℝ) :
    (μ.prod ν).expect (fun p => X p.1 * Y p.2) = μ.expect X * ν.expect Y := by
  rw [expect_prod]
  simp only [expect_const_mul]
  exact μ.expect_mul_const X _

@[simp] theorem map_fst_prod : (μ.prod ν).map Prod.fst = μ :=
  map_fst_compProd μ _

@[simp] theorem map_snd_prod : (μ.prod ν).map Prod.snd = ν := by
  ext b
  rw [map_w, prob_prod]
  have : ∀ a : α, Prod.mk a ⁻¹' (Prod.snd ⁻¹' ({b} : Set β)) = {b} := fun a => by
    ext b'; simp
  simp only [this, prob_singleton, expect_const]

theorem prob_prod_fst (A : Set α) : (μ.prod ν).prob (Prod.fst ⁻¹' A) = μ.prob A := by
  rw [← prob_map, map_fst_prod]

theorem prob_prod_snd (B : Set β) : (μ.prod ν).prob (Prod.snd ⁻¹' B) = ν.prob B := by
  rw [← prob_map, map_snd_prod]

/-- Independence of the coordinates: `P(A × B) = P(A) · P(B)`. -/
theorem prob_prod_set_prod (A : Set α) (B : Set β) :
    (μ.prod ν).prob (A ×ˢ B) = μ.prob A * ν.prob B := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_prod_mul]
  congr 1
  funext p
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;> simp [h1, h2, Set.mem_prod]

theorem map_swap_prod : (μ.prod ν).map Prod.swap = ν.prod μ := by
  ext p
  have h := map_equiv_w (μ.prod ν) (Equiv.prodComm α β) p
  rw [Equiv.coe_prodComm] at h
  rw [h, prod_w', prod_w']
  exact mul_comm _ _

/-- Coordinatewise maps of an independent pair are independent: the image of `μ ⊗ ν` under
`(a, b) ↦ (f a, g b)` is `f_* μ ⊗ g_* ν`. -/
theorem map_prod_map {γ δ : Type*} (f : α → γ) (g : β → δ) :
    (μ.prod ν).map (Prod.map f g) = (μ.map f).prod (ν.map g) := by
  ext ⟨c, d⟩
  rw [map_w, prod_w, map_w, map_w]
  have : Prod.map f g ⁻¹' {(c, d)} = (f ⁻¹' {c}) ×ˢ (g ⁻¹' {d}) := by
    ext ⟨a, b⟩; simp
  rw [this, prob_prod_set_prod]

/-- Independence of a product and a function of one coordinate: if `Z₁ (a, b)` does not depend
on `b` and `Z₂ (a, b)` does not depend on `a`, then `E[Z₁ Z₂] = E Z₁ · E Z₂`. -/
theorem expect_prod_mul_of_dependsOn {Z₁ Z₂ : α × β → ℝ}
    (h₁ : ∀ a b b', Z₁ (a, b) = Z₁ (a, b')) (h₂ : ∀ a a' b, Z₂ (a, b) = Z₂ (a', b)) :
    (μ.prod ν).expect (fun p => Z₁ p * Z₂ p) = (μ.prod ν).expect Z₁ * (μ.prod ν).expect Z₂ := by
  obtain ⟨a₀, -⟩ := μ.exists_w_pos
  obtain ⟨b₀, -⟩ := ν.exists_w_pos
  have e₁ : Z₁ = fun p => Z₁ (p.1, b₀) := funext fun p => h₁ p.1 p.2 b₀
  have e₂ : Z₂ = fun p => Z₂ (a₀, p.2) := funext fun p => h₂ p.1 a₀ p.2
  rw [e₁, e₂, expect_prod_mul μ ν (fun a => Z₁ (a, b₀)) (fun b => Z₂ (a₀, b))]
  congr 1
  · exact (expect_prod_fst μ ν fun a => Z₁ (a, b₀)).symm
  · exact (expect_prod_snd μ ν fun b => Z₂ (a₀, b)).symm

/-- [s1:citMarkov](c) "given any fixed outcome of variables that are independent of the
variables being drawn … the conditional law of the latter is their unconditional law":
conditioning a product on the value `a` of its first coordinate gives `dirac a × ν`. -/
theorem cond_prod_fst (a : α) (h : 0 < (μ.prod ν).prob (Prod.fst ⁻¹' {a})) :
    (μ.prod ν).cond (Prod.fst ⁻¹' {a}) h = (dirac a).prod ν := by
  have ha : (μ.prod ν).prob (Prod.fst ⁻¹' {a}) = μ.w a := by
    rw [prob_prod_fst, prob_singleton]
  have hne : μ.w a ≠ 0 := by rw [← ha]; exact h.ne'
  ext ⟨a', b⟩
  rw [cond_w, ha, prod_w]
  by_cases h' : a' = a
  · subst h'
    rw [Set.indicator_of_mem (show (a', b) ∈ Prod.fst ⁻¹' {a'} from rfl), prod_w, dirac_w_self,
      one_mul, mul_div_cancel_left₀ _ hne]
  · rw [Set.indicator_of_notMem (show (a', b) ∉ Prod.fst ⁻¹' {a} from h'), dirac_w_of_ne h',
      zero_div, zero_mul]

/-- [s1:citMarkov](c): the second coordinate of a product, conditioned on the first coordinate,
has its unconditional law `ν`. -/
theorem map_snd_cond_prod_fst (a : α) (h : 0 < (μ.prod ν).prob (Prod.fst ⁻¹' {a})) :
    ((μ.prod ν).cond (Prod.fst ⁻¹' {a}) h).map Prod.snd = ν := by
  rw [cond_prod_fst, map_snd_prod]

end Prod

/-! ### Composition with a kernel -/

section Bind

variable (μ : FinDist α) (K : α → FinDist β)

theorem expect_bind (Y : β → ℝ) : (μ.bind K).expect Y = μ.expect fun a => (K a).expect Y := by
  rw [bind, expect_map, expect_compProd]

theorem prob_bind (B : Set β) : (μ.bind K).prob B = μ.expect fun a => (K a).prob B := by
  rw [prob_eq_expect, expect_bind]
  simp only [← prob_eq_expect]

theorem bind_w (b : β) : (μ.bind K).w b = μ.expect fun a => (K a).w b := by
  rw [← prob_singleton, prob_bind]
  simp only [prob_singleton]

end Bind

/-! ### Finite products of independent distributions -/

section Pi

variable [Fintype ι] {κ : ι → Type*} (μ : ∀ i, FinDist (κ i))

theorem pi_w (f : ∀ i, κ i) : (pi μ).w f = ∏ i, (μ i).w (f i) := rfl

theorem mem_supp_pi {f : ∀ i, κ i} : f ∈ (pi μ).supp ↔ ∀ i, f i ∈ (μ i).supp := by
  simp only [mem_supp, pi_w, ne_eq, prod_eq_zero_iff, mem_univ, true_and, not_exists]

theorem supp_pi_subset [DecidableEq ι] :
    (pi μ).supp ⊆ Fintype.piFinset fun i => (μ i).supp :=
  fun _ hf => Fintype.mem_piFinset.2 ((mem_supp_pi μ).1 hf)

/-- Independence of the coordinates: the expectation of a product of functions of distinct
coordinates is the product of the expectations. -/
theorem expect_pi_prod (X : ∀ i, κ i → ℝ) :
    (pi μ).expect (fun f => ∏ i, X i (f i)) = ∏ i, (μ i).expect (X i) := by
  classical
  rw [expect_eq_sum_of_supp_subset _ (supp_pi_subset μ)]
  have : ∀ i, (μ i).expect (X i) = ∑ j ∈ (μ i).supp, (μ i).w j * X i j := fun i => rfl
  simp only [this]
  rw [prod_univ_sum]
  exact sum_congr rfl fun f _ => by rw [pi_w, prod_mul_distrib]

/-- `expect_pi_prod` for a product over a subset `s` of the coordinates. -/
theorem expect_pi_prod_finset (s : Finset ι) (X : ∀ i, κ i → ℝ) :
    (pi μ).expect (fun f => ∏ i ∈ s, X i (f i)) = ∏ i ∈ s, (μ i).expect (X i) := by
  classical
  have h := expect_pi_prod μ fun i j => if i ∈ s then X i j else 1
  have hr : ∀ i, (μ i).expect (fun j => if i ∈ s then X i j else 1) =
      if i ∈ s then (μ i).expect (X i) else 1 := fun i => by
    split_ifs <;> simp
  simp only [hr, Fintype.prod_ite_mem] at h
  exact h

/-- Independence of the coordinates: `P(f i ∈ A i for all i ∈ s) = ∏_{i ∈ s} P(A i)`. -/
theorem prob_pi_forall_mem (s : Finset ι) (A : ∀ i, Set (κ i)) :
    (pi μ).prob {f | ∀ i ∈ s, f i ∈ A i} = ∏ i ∈ s, (μ i).prob (A i) := by
  classical
  simp only [prob_eq_expect]
  rw [← expect_pi_prod_finset]
  congr 1
  funext f
  by_cases h : ∀ i ∈ s, f i ∈ A i
  · rw [Set.indicator_of_mem (show f ∈ {f | ∀ i ∈ s, f i ∈ A i} from h), Pi.one_apply]
    exact (prod_eq_one fun i hi => by simp [h i hi]).symm
  · simp only [not_forall] at h
    obtain ⟨i, hi, hA⟩ := h
    rw [Set.indicator_of_notMem (show f ∉ {f | ∀ i ∈ s, f i ∈ A i} from fun h' => hA (h' i hi))]
    exact (prod_eq_zero hi (by simp [hA])).symm

theorem prob_pi_univ_pi (A : ∀ i, Set (κ i)) :
    (pi μ).prob (Set.univ.pi A) = ∏ i, (μ i).prob (A i) := by
  rw [← prob_pi_forall_mem]
  congr 1
  ext f
  simp

/-- The `i`-th coordinate has law `μ i` (expectation form). -/
theorem expect_pi_eval (i : ι) (X : κ i → ℝ) :
    (pi μ).expect (fun f => X (f i)) = (μ i).expect X := by
  classical
  have h1 : (fun f : ∀ j, κ j =>
      ∏ j, Function.update (fun j (_ : κ j) => (1 : ℝ)) i X j (f j)) = fun f => X (f i) := by
    funext f
    rw [Fintype.prod_eq_single i fun j hj => by simp [Function.update_of_ne hj]]
    simp
  have h2 : ∏ j, (μ j).expect (Function.update (fun j (_ : κ j) => (1 : ℝ)) i X j) =
      (μ i).expect X := by
    rw [Fintype.prod_eq_single i fun j hj => by simp [Function.update_of_ne hj]]
    simp
  rw [← h1, ← h2, expect_pi_prod]

/-- The `i`-th coordinate has law `μ i`. -/
theorem prob_pi_eval (i : ι) (A : Set (κ i)) : (pi μ).prob {f | f i ∈ A} = (μ i).prob A := by
  classical
  rw [prob_eq_expect, prob_eq_expect, ← expect_pi_eval μ i]
  congr 1

@[simp] theorem map_eval_pi (i : ι) : (pi μ).map (fun f => f i) = μ i := by
  ext x
  rw [map_w, ← prob_singleton (μ i), ← prob_pi_eval μ i]
  rfl

/-- Coordinatewise maps of independent coordinates are independent: the image of `pi μ` under
`ω ↦ (i ↦ f i (ω i))` is `pi (i ↦ (f i)_* (μ i))`. This is how a random object defined
coordinate by coordinate from independent labels is identified (e.g. [s5:lemZones] proof of
(ii): "The event {v ∈ Zone} is a function of the pair (choice(v), sublabel of v), and these pairs
are independent over v"). -/
theorem map_pi {κ' : ι → Type*} (f : ∀ i, κ i → κ' i) :
    (pi μ).map (fun ω i => f i (ω i)) = pi fun i => (μ i).map (f i) := by
  ext g
  rw [map_w, pi_w]
  simp only [map_w]
  have : (fun (ω : ∀ i, κ i) i => f i (ω i)) ⁻¹' {g} =
      {ω : ∀ i, κ i | ∀ i ∈ univ, ω i ∈ f i ⁻¹' {g i}} := by
    ext ω; simp [funext_iff]
  rw [this, prob_pi_forall_mem]

/-- Splitting the coordinates into those satisfying `p` and the others: the product over all
coordinates is the image of the product of the two partial products. -/
theorem pi_eq_map_prod (p : ι → Prop) [DecidablePred p] :
    pi μ = ((pi fun i : {i // p i} => μ i).prod (pi fun i : {i // ¬p i} => μ i)).map
      (Equiv.piEquivPiSubtypeProd p κ).symm := by
  ext f
  rw [map_equiv_w, Equiv.symm_symm, pi_w, prod_w', pi_w, pi_w]
  exact (Fintype.prod_subtype_mul_prod_subtype p fun i => (μ i).w (f i)).symm

/-- [PLAN §3 decision 3] Conditioning on the coordinates in `p` ("fixing a prefix"):
`P(A) = E_x P_y(A_x)` where `x` ranges over the coordinates in `p`, `y` over the others. -/
theorem prob_pi_split (p : ι → Prop) [DecidablePred p] (A : Set (∀ i, κ i)) :
    (pi μ).prob A = (pi fun i : {i // p i} => μ i).expect fun x =>
      (pi fun i : {i // ¬p i} => μ i).prob
        {y | (Equiv.piEquivPiSubtypeProd p κ).symm (x, y) ∈ A} := by
  conv_lhs => rw [pi_eq_map_prod μ p]
  rw [prob_map, prob_prod]
  rfl

/-- Independence of functions of disjoint sets of coordinates: if `X` depends only on the
coordinates in `p` and `Y` only on the others, then `E[X Y] = E X · E Y`. -/
theorem expect_pi_mul_of_dependsOn (p : ι → Prop) {X Y : (∀ i, κ i) → ℝ}
    (hX : ∀ f g, (∀ i, p i → f i = g i) → X f = X g)
    (hY : ∀ f g, (∀ i, ¬p i → f i = g i) → Y f = Y g) :
    (pi μ).expect (fun f => X f * Y f) = (pi μ).expect X * (pi μ).expect Y := by
  classical
  rw [pi_eq_map_prod μ p]
  simp only [expect_map]
  exact expect_prod_mul_of_dependsOn _ _
    (fun a b b' => hX _ _ fun i hi => by simp [Equiv.piEquivPiSubtypeProd_symm_apply, hi])
    (fun a a' b => hY _ _ fun i hi => by simp [Equiv.piEquivPiSubtypeProd_symm_apply, hi])

/-- Independence of events depending on disjoint sets of coordinates: if `A` depends only on
the coordinates in `p` and `B` only on the others, then `P(A ∩ B) = P(A) · P(B)`. -/
theorem prob_pi_inter_of_dependsOn (p : ι → Prop) {A B : Set (∀ i, κ i)}
    (hA : ∀ f g, (∀ i, p i → f i = g i) → f ∈ A → g ∈ A)
    (hB : ∀ f g, (∀ i, ¬p i → f i = g i) → f ∈ B → g ∈ B) :
    (pi μ).prob (A ∩ B) = (pi μ).prob A * (pi μ).prob B := by
  classical
  simp only [prob_eq_expect]
  rw [← expect_pi_mul_of_dependsOn μ p (X := A.indicator 1) (Y := B.indicator 1)]
  · congr 1
    funext f
    by_cases hfa : f ∈ A <;> by_cases hfb : f ∈ B <;> simp [hfa, hfb]
  · intro f g h
    by_cases hf : f ∈ A
    · simp [hf, hA f g h hf]
    · have : g ∉ A := fun hg => hf (hA g f (fun i hi => (h i hi).symm) hg)
      simp [hf, this]
  · intro f g h
    by_cases hf : f ∈ B
    · simp [hf, hB f g h hf]
    · have : g ∉ B := fun hg => hf (hB g f (fun i hi => (h i hi).symm) hg)
      simp [hf, this]

/-- Mutual independence of events depending on pairwise disjoint blocks of coordinates: if each
`A u` (`u ∈ s`) depends only on the coordinates in `B u`, and the blocks `B u` are pairwise
disjoint, then `P(⋂_{u ∈ s} A u) = ∏_{u ∈ s} P(A u)`. Example: [s4:lemTPV] proof, item (G4):
"the variables I_u depend on pairwise distinct edges wu and distinct vertices u, so they are
independent". -/
theorem prob_pi_forall_of_dependsOn {U : Type*} (s : Finset U) (B : U → Set ι)
    (hB : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (B u) (B v)) (A : U → Set (∀ i, κ i))
    (hA : ∀ u ∈ s, ∀ f g, (∀ i ∈ B u, f i = g i) → f ∈ A u → g ∈ A u) :
    (pi μ).prob {f | ∀ u ∈ s, f ∈ A u} = ∏ u ∈ s, (pi μ).prob (A u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert u₀ s hu₀ ih =>
    have e : {f : ∀ i, κ i | ∀ u ∈ insert u₀ s, f ∈ A u} = A u₀ ∩ {f | ∀ u ∈ s, f ∈ A u} := by
      ext f; simp
    rw [e, prod_insert hu₀, prob_pi_inter_of_dependsOn μ (· ∈ B u₀), ih]
    · exact fun u hu v hv => hB u (mem_insert_of_mem hu) v (mem_insert_of_mem hv)
    · exact fun u hu => hA u (mem_insert_of_mem hu)
    · exact hA u₀ (mem_insert_self _ _)
    · intro f g h hf u hu
      refine hA u (mem_insert_of_mem hu) f g (fun i hi => h i fun hi₀ => ?_) (hf u hu)
      exact Set.disjoint_left.1 (hB u (mem_insert_of_mem hu) u₀ (mem_insert_self _ _)
        (fun h' => hu₀ (h' ▸ hu))) hi hi₀

/-- Expectation form of `prob_pi_forall_of_dependsOn`: functions of pairwise disjoint blocks of
coordinates are independent, so the expectation of their product is the product of the
expectations. -/
theorem expect_pi_prod_of_dependsOn {U : Type*} (s : Finset U) (B : U → Set ι)
    (hB : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (B u) (B v)) (X : U → (∀ i, κ i) → ℝ)
    (hX : ∀ u ∈ s, ∀ f g, (∀ i ∈ B u, f i = g i) → X u f = X u g) :
    (pi μ).expect (fun f => ∏ u ∈ s, X u f) = ∏ u ∈ s, (pi μ).expect (X u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert u₀ s hu₀ ih =>
    simp only [prod_insert hu₀]
    rw [expect_pi_mul_of_dependsOn μ (· ∈ B u₀) (X := X u₀) (Y := fun f => ∏ u ∈ s, X u f), ih]
    · exact fun u hu v hv => hB u (mem_insert_of_mem hu) v (mem_insert_of_mem hv)
    · exact fun u hu => hX u (mem_insert_of_mem hu)
    · exact hX u₀ (mem_insert_self _ _)
    · intro f g h
      refine prod_congr rfl fun u hu =>
        hX u (mem_insert_of_mem hu) f g fun i hi => h i fun hi₀ => ?_
      exact Set.disjoint_left.1 (hB u (mem_insert_of_mem hu) u₀ (mem_insert_self _ _)
        (fun h' => hu₀ (h' ▸ hu))) hi hi₀

/-- Law form of `prob_pi_forall_of_dependsOn`: if each `g u` depends only on the coordinates in
`B u`, and the blocks `B u` are pairwise disjoint, then the family `(g u)_u` has the product law
`pi (u ↦ law of g u)`. (See also `FinDist.iIndepFun_pi_of_dependsOn`.) -/
theorem map_pi_of_dependsOn {U : Type*} [Fintype U] {β : U → Type*} (B : U → Set ι)
    (hB : Pairwise fun u v => Disjoint (B u) (B v)) (g : ∀ u, (∀ i, κ i) → β u)
    (hg : ∀ u f f', (∀ i ∈ B u, f i = f' i) → g u f = g u f') :
    (pi μ).map (fun f u => g u f) = pi fun u => (pi μ).map (g u) := by
  ext y
  rw [map_w, pi_w]
  simp only [map_w]
  have : (fun f u => g u f) ⁻¹' {y} = {f | ∀ u ∈ univ, f ∈ g u ⁻¹' {y u}} := by
    ext f; simp [funext_iff]
  rw [this, prob_pi_forall_of_dependsOn μ univ B (fun u _ v _ h => hB h)]
  intro u _ f f' h hf
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hf ⊢
  rw [← hg u f f' h, hf]

end Pi

end FinDist

end EG
