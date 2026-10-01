module

public import EG.Lib.Prob.Basic

/-!
# Named finite distributions: uniform, Bernoulli, random colourings, random subsets

Characterisation lemmas for the named constructions of `EG/Defs/Prob/FinDist.lean`:

* `uniform`: `uniform_w_eq`, `prob_uniform` (`|A| / |Ω|`), `expect_uniform`;
* `bernoulli`: `bernoulli_w_true/false`, `expect_bernoulli`, `prob_bernoulli_true`;
* `randColouring` ([s3:lemL15p]): `randColouring_w`, `randColouring_eq_uniform`,
  `prob_randColouring_apply` (each element gets a given colour with probability `1/k`),
  `prob_randColouring_forall_mem` (independence), `map_colourClass_randColouring` and, for the
  elements of a `Finset E` of the ambient type, `map_selectSet_randColouring` (a colour class is
  a `(1/k)`-random subset);
* `indepSubset` / `rsubset` (the ρ-random subsets of s3): the joint law
  `prob_indepSubset_superset_disjoint` (`P(A ⊆ T, B ∩ T = ∅) = ∏_A p · ∏_B (1 - p)`), the weight
  formula `indepSubset_w` / `rsubset_w` (`ρ^|T| (1-ρ)^|S \ T|` for `T ⊆ S`), the marginals
  `prob_mem_indepSubset` / `prob_mem_rsubset`, the first moment `expect_card_inter_indepSubset`
  / `expect_card_inter_rsubset`, and the product representation `prob_indepSubset` /
  `expect_indepSubset` (for Chernoff-type bounds);
* random subsets defined element by element from independent labels: `map_selectSet_pi`,
  `map_selectSet_pi_rsubset`; indicators: `map_eq_bernoulli`, `map_decide_eq_uniform`,
  `selectSet_decide_mem`, `decide_mem_selectSet`.
-/

public section


namespace EG

namespace FinDist

open Finset

variable {Ω α ι : Type*}

/-! ### Uniform distribution -/

section Uniform

variable [Finite Ω] [Nonempty Ω]

theorem uniform_w (ω : Ω) : (uniform Ω).w ω = (Nat.card Ω : ℝ)⁻¹ := rfl

theorem uniform_w_eq [Fintype Ω] (ω : Ω) : (uniform Ω).w ω = 1 / Fintype.card Ω := by
  rw [uniform_w, Nat.card_eq_fintype_card, one_div]

theorem uniform_w_pos (ω : Ω) : 0 < (uniform Ω).w ω := by
  have := Fintype.ofFinite Ω
  rw [uniform_w_eq]
  have : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  positivity

/-- Under the uniform distribution, `P(A) = |A| / |Ω|`. -/
theorem prob_uniform [Fintype Ω] (A : Set Ω) [DecidablePred (· ∈ A)] :
    (uniform Ω).prob A = (univ.filter (· ∈ A)).card / Fintype.card Ω := by
  rw [prob_eq_sum_filter]
  simp only [uniform_w_eq, sum_const, nsmul_eq_mul]
  ring

theorem expect_uniform [Fintype Ω] (X : Ω → ℝ) :
    (uniform Ω).expect X = (∑ ω, X ω) / Fintype.card Ω := by
  rw [expect_eq_sum, sum_div]
  exact sum_congr rfl fun ω _ => by rw [uniform_w_eq]; ring

end Uniform

/-! ### Bernoulli distribution -/

section Bernoulli

variable {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)

@[simp] theorem bernoulli_w_true : (bernoulli p h0 h1).w true = p := rfl

@[simp] theorem bernoulli_w_false : (bernoulli p h0 h1).w false = 1 - p := rfl

theorem expect_bernoulli (X : Bool → ℝ) :
    (bernoulli p h0 h1).expect X = p * X true + (1 - p) * X false := by
  rw [expect_eq_sum, Fintype.sum_bool, bernoulli_w_true, bernoulli_w_false]

theorem prob_bernoulli_true : (bernoulli p h0 h1).prob {true} = p := by
  rw [prob_singleton, bernoulli_w_true]

theorem prob_bernoulli_false : (bernoulli p h0 h1).prob {false} = 1 - p := by
  rw [prob_singleton, bernoulli_w_false]

theorem prob_bernoulli_eq_true : (bernoulli p h0 h1).prob {b | b = true} = p :=
  prob_bernoulli_true h0 h1

/-- A `Bool`-valued random variable (an indicator) that is `true` with probability `p` has law
`bernoulli p`. -/
theorem map_eq_bernoulli (μ : FinDist Ω) (f : Ω → Bool) (h : μ.prob {ω | f ω = true} = p) :
    μ.map f = bernoulli p h0 h1 := by
  ext b
  cases b
  · rw [map_w, bernoulli_w_false, ← h, ← prob_compl]
    congr 1
    ext ω
    simp
  · rw [map_w, bernoulli_w_true, ← h]
    rfl

end Bernoulli

/-! ### Uniform random colourings -/

section Colouring

variable [Fintype ι] {k : ℕ} [NeZero k]

theorem randColouring_w (c : ι → Fin k) :
    (randColouring ι k).w c = (k : ℝ)⁻¹ ^ Fintype.card ι := by
  simp [randColouring, pi_w, uniform_w, prod_const]

/-- The random colouring is the uniform distribution on all colourings `ι → Fin k`. -/
theorem randColouring_eq_uniform : randColouring ι k = uniform (ι → Fin k) := by
  ext c
  rw [randColouring_w, uniform_w, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
  simp [inv_pow]

/-- [s3:lemL15p] Each element receives a given colour with probability `1/k`. -/
theorem prob_randColouring_apply (e : ι) (j : Fin k) :
    (randColouring ι k).prob {c | c e = j} = 1 / k := by
  have h := prob_pi_eval (fun _ : ι => uniform (Fin k)) e {j}
  rw [prob_singleton, uniform_w] at h
  simp only [Set.mem_singleton_iff] at h
  rw [randColouring, h]
  simp

/-- [s3:lemL15p] The colours of distinct elements are independent. -/
theorem prob_randColouring_forall_mem (s : Finset ι) (A : ι → Set (Fin k)) :
    (randColouring ι k).prob {c | ∀ e ∈ s, c e ∈ A e} =
      ∏ e ∈ s, (uniform (Fin k)).prob (A e) :=
  prob_pi_forall_mem (fun _ : ι => uniform (Fin k)) s A

omit [Fintype ι] in
/-- The indicator of one colour under a uniform colour is a Bernoulli(`1/k`) variable. -/
theorem map_decide_eq_uniform (j : Fin k) (h0 : (0 : ℝ) ≤ 1 / k) (h1 : (1 : ℝ) / k ≤ 1) :
    (uniform (Fin k)).map (fun c => decide (c = j)) = bernoulli (1 / k) h0 h1 := by
  refine map_eq_bernoulli h0 h1 _ _ ?_
  simp only [decide_eq_true_eq, Set.ofPred_eq_eq_singleton, prob_singleton, uniform_w_eq,
    Fintype.card_fin]

end Colouring

/-! ### Independent random subsets -/

section Subsets

theorem mem_selectSet {S : Finset α} {f : S → Bool} {a : α} :
    a ∈ selectSet S f ↔ ∃ h : a ∈ S, f ⟨a, h⟩ = true := by
  simp [selectSet]

theorem mem_selectSet_coe {S : Finset α} {f : S → Bool} (i : S) :
    (i : α) ∈ selectSet S f ↔ f i = true := by
  simp [mem_selectSet]

theorem selectSet_subset (S : Finset α) (f : S → Bool) : selectSet S f ⊆ S :=
  fun _ h => (mem_selectSet.1 h).1

variable {S : Finset α} {p : α → ℝ} (h0 : ∀ a ∈ S, 0 ≤ p a) (h1 : ∀ a ∈ S, p a ≤ 1)

theorem expect_indepSubset (Y : Finset α → ℝ) :
    (indepSubset S p h0 h1).expect Y =
      (pi fun a : S => bernoulli (p a) (h0 a a.2) (h1 a a.2)).expect fun f => Y (selectSet S f) :=
  expect_map _ _ _

theorem prob_indepSubset (B : Set (Finset α)) :
    (indepSubset S p h0 h1).prob B =
      (pi fun a : S => bernoulli (p a) (h0 a a.2) (h1 a a.2)).prob {f | selectSet S f ∈ B} :=
  prob_map _ _ _

/-- The random subset is almost surely contained in `S`. -/
theorem prob_indepSubset_subset : (indepSubset S p h0 h1).prob {T | T ⊆ S} = 1 := by
  rw [prob_indepSubset]
  convert prob_univ _
  ext f
  simp [selectSet_subset]

theorem subset_of_indepSubset_w_pos {T : Finset α} (hT : 0 < (indepSubset S p h0 h1).w T) :
    T ⊆ S :=
  (prob_eq_one_iff _ _).1 (prob_indepSubset_subset h0 h1) T hT

/-- The joint law of the random subset `T` ("each element of `S` independently"): for disjoint
`A, B ⊆ S`, `P(A ⊆ T and B ∩ T = ∅) = ∏_{a ∈ A} p a · ∏_{b ∈ B} (1 - p b)`. -/
theorem prob_indepSubset_superset_disjoint [DecidableEq α] {A B : Finset α} (hA : A ⊆ S)
    (hB : B ⊆ S) (hAB : Disjoint A B) :
    (indepSubset S p h0 h1).prob {T | A ⊆ T ∧ Disjoint B T} =
      (∏ a ∈ A, p a) * ∏ b ∈ B, (1 - p b) := by
  classical
  rw [prob_indepSubset]
  have hev : {f : S → Bool | selectSet S f ∈ {T : Finset α | A ⊆ T ∧ Disjoint B T}} =
      {f | ∀ i ∈ (univ : Finset S),
        f i ∈ ({b | ((i : α) ∈ A → b = true) ∧ ((i : α) ∈ B → b = false)} : Set Bool)} := by
    ext f
    simp only [Set.mem_ofPred_eq, mem_univ, true_implies]
    constructor
    · rintro ⟨hsub, hdisj⟩ i
      refine ⟨fun hi => (mem_selectSet_coe i).1 (hsub hi), fun hi => ?_⟩
      have : (i : α) ∉ selectSet S f := Finset.disjoint_left.1 hdisj hi
      rw [mem_selectSet_coe] at this
      simpa using this
    · intro h
      refine ⟨fun a ha => (mem_selectSet_coe ⟨a, hA ha⟩).2 ((h ⟨a, hA ha⟩).1 ha),
        Finset.disjoint_left.2 fun b hb hbT => ?_⟩
      obtain ⟨hbS, hf⟩ := mem_selectSet.1 hbT
      rw [(h ⟨b, hbS⟩).2 hb] at hf
      exact Bool.false_ne_true hf
  have hE : ∀ i : S, (bernoulli (p i) (h0 i i.2) (h1 i i.2)).prob
      {b | ((i : α) ∈ A → b = true) ∧ ((i : α) ∈ B → b = false)} =
      if (i : α) ∈ A then p i else if (i : α) ∈ B then 1 - p i else 1 := by
    intro i
    rw [prob_eq_sum, Fintype.sum_bool]
    by_cases hiA : (i : α) ∈ A
    · have hiB : (i : α) ∉ B := Finset.disjoint_left.1 hAB hiA
      simp [hiA, hiB]
    · by_cases hiB : (i : α) ∈ B
      · simp [hiA, hiB]
      · simp [hiA, hiB]
  have e₁ : S ∩ A = A := inter_eq_right.2 hA
  have e₂ : (S.filter fun a => a ∉ A) ∩ B = B := by
    ext b
    simp only [mem_inter, mem_filter]
    exact ⟨fun h => h.2, fun hb => ⟨⟨hB hb, Finset.disjoint_right.1 hAB hb⟩, hb⟩⟩
  rw [hev, prob_pi_forall_mem]
  simp only [hE]
  rw [Finset.prod_coe_sort S fun a => if a ∈ A then p a else if a ∈ B then 1 - p a else 1,
    prod_ite, filter_mem_eq_inter, e₁, prod_ite_mem, e₂]

/-- Weight formula for the independent random subset: for `T ⊆ S`,
`P(T) = ∏_{a ∈ T} p a · ∏_{a ∈ S \ T} (1 - p a)`; subsets not contained in `S` have weight `0`. -/
theorem indepSubset_w [DecidableEq α] (T : Finset α) :
    (indepSubset S p h0 h1).w T =
      if T ⊆ S then (∏ a ∈ T, p a) * ∏ a ∈ S \ T, (1 - p a) else 0 := by
  split_ifs with hT
  · rw [← prob_singleton, ← prob_indepSubset_superset_disjoint h0 h1 hT sdiff_subset
      disjoint_sdiff]
    refine prob_congr _ fun T' hT' => ?_
    have hT'S := subset_of_indepSubset_w_pos h0 h1 hT'
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      exact ⟨subset_refl _, sdiff_disjoint⟩
    · rintro ⟨hsub, hdisj⟩
      refine Subset.antisymm (fun a ha => ?_) hsub
      by_contra haT
      exact Finset.disjoint_left.1 hdisj (mem_sdiff.2 ⟨hT'S ha, haT⟩) ha
  · by_contra hne
    exact hT (subset_of_indepSubset_w_pos h0 h1 (lt_of_le_of_ne (w_nonneg _ _) (Ne.symm hne)))

/-- `P(A ⊆ T) = ∏_{a ∈ A} p a` for `A ⊆ S`. -/
theorem prob_superset_indepSubset [DecidableEq α] {A : Finset α} (hA : A ⊆ S) :
    (indepSubset S p h0 h1).prob {T | A ⊆ T} = ∏ a ∈ A, p a := by
  have := prob_indepSubset_superset_disjoint h0 h1 hA (empty_subset S) (disjoint_empty_right A)
  simpa using this

/-- `P(B ∩ T = ∅) = ∏_{b ∈ B} (1 - p b)` for `B ⊆ S`. -/
theorem prob_disjoint_indepSubset [DecidableEq α] {B : Finset α} (hB : B ⊆ S) :
    (indepSubset S p h0 h1).prob {T | Disjoint B T} = ∏ b ∈ B, (1 - p b) := by
  have := prob_indepSubset_superset_disjoint h0 h1 (empty_subset S) hB (disjoint_empty_left B)
  simpa using this

/-- Each element `a ∈ S` lies in the random subset with probability `p a`. -/
theorem prob_mem_indepSubset {a : α} (ha : a ∈ S) :
    (indepSubset S p h0 h1).prob {T | a ∈ T} = p a := by
  classical
  have := prob_superset_indepSubset h0 h1 (singleton_subset_iff.2 ha)
  simpa using this

theorem prob_notMem_indepSubset {a : α} (ha : a ∈ S) :
    (indepSubset S p h0 h1).prob {T | a ∉ T} = 1 - p a := by
  rw [← prob_mem_indepSubset h0 h1 ha, ← prob_compl]
  rfl

/-- First moment: `E |T ∩ U| = ∑_{a ∈ S ∩ U} p a`. -/
theorem expect_card_inter_indepSubset [DecidableEq α] (U : Finset α) :
    (indepSubset S p h0 h1).expect (fun T => ((T ∩ U).card : ℝ)) = ∑ a ∈ S ∩ U, p a := by
  have h : ∀ T : Finset α, 0 < (indepSubset S p h0 h1).w T →
      ((T ∩ U).card : ℝ) =
        ∑ a ∈ S ∩ U, ({T' : Finset α | a ∈ T'} : Set (Finset α)).indicator 1 T := by
    intro T hT
    have hTS := subset_of_indepSubset_w_pos h0 h1 hT
    have hind : ∀ a, ({T' : Finset α | a ∈ T'} : Set (Finset α)).indicator (1 : Finset α → ℝ) T =
        if a ∈ T then 1 else 0 := fun a => by
      by_cases ha : a ∈ T <;> simp [ha]
    simp only [hind]
    rw [sum_boole]
    congr 2
    ext a
    simp only [mem_inter, mem_filter]
    exact ⟨fun ⟨haT, haU⟩ => ⟨⟨hTS haT, haU⟩, haT⟩, fun ⟨⟨_, haU⟩, haT⟩ => ⟨haT, haU⟩⟩
  rw [expect_congr _ h, expect_sum_indicator]
  exact sum_congr rfl fun a ha => prob_mem_indepSubset h0 h1 (mem_inter.1 ha).1

end Subsets

/-! ### ρ-random subsets -/

section RSubset

variable {S : Finset α} {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)

/-- Weight formula for the ρ-random subset: `P(T) = ρ^|T| (1-ρ)^|S \ T|` for `T ⊆ S`. -/
theorem rsubset_w [DecidableEq α] (T : Finset α) :
    (rsubset S ρ h0 h1).w T = if T ⊆ S then ρ ^ T.card * (1 - ρ) ^ (S \ T).card else 0 := by
  rw [rsubset, indepSubset_w]
  simp [prod_const]

theorem prob_rsubset_subset : (rsubset S ρ h0 h1).prob {T | T ⊆ S} = 1 :=
  prob_indepSubset_subset _ _

/-- Each element of `S` lies in the ρ-random subset with probability `ρ`. -/
theorem prob_mem_rsubset {a : α} (ha : a ∈ S) : (rsubset S ρ h0 h1).prob {T | a ∈ T} = ρ :=
  prob_mem_indepSubset _ _ ha

/-- `P(A ⊆ T) = ρ^|A|` for `A ⊆ S`. -/
theorem prob_superset_rsubset [DecidableEq α] {A : Finset α} (hA : A ⊆ S) :
    (rsubset S ρ h0 h1).prob {T | A ⊆ T} = ρ ^ A.card := by
  rw [rsubset, prob_superset_indepSubset _ _ hA, prod_const]

/-- `P(B ∩ T = ∅) = (1 - ρ)^|B|` for `B ⊆ S`. -/
theorem prob_disjoint_rsubset [DecidableEq α] {B : Finset α} (hB : B ⊆ S) :
    (rsubset S ρ h0 h1).prob {T | Disjoint B T} = (1 - ρ) ^ B.card := by
  rw [rsubset, prob_disjoint_indepSubset _ _ hB, prod_const]

/-- The joint law of the ρ-random subset: for disjoint `A, B ⊆ S`,
`P(A ⊆ T and B ∩ T = ∅) = ρ^|A| (1-ρ)^|B|`. -/
theorem prob_rsubset_superset_disjoint [DecidableEq α] {A B : Finset α} (hA : A ⊆ S)
    (hB : B ⊆ S) (hAB : Disjoint A B) :
    (rsubset S ρ h0 h1).prob {T | A ⊆ T ∧ Disjoint B T} = ρ ^ A.card * (1 - ρ) ^ B.card := by
  rw [rsubset, prob_indepSubset_superset_disjoint _ _ hA hB hAB, prod_const, prod_const]

/-- First moment: `E |T ∩ U| = ρ |S ∩ U|`. -/
theorem expect_card_inter_rsubset [DecidableEq α] (U : Finset α) :
    (rsubset S ρ h0 h1).expect (fun T => ((T ∩ U).card : ℝ)) = ρ * (S ∩ U).card := by
  rw [rsubset, expect_card_inter_indepSubset, sum_const, nsmul_eq_mul, mul_comm]

/-- `E |T| = ρ |S|`. -/
theorem expect_card_rsubset [DecidableEq α] :
    (rsubset S ρ h0 h1).expect (fun T => (T.card : ℝ)) = ρ * S.card := by
  have h := expect_card_inter_rsubset h0 h1 (S := S) S
  rw [inter_self] at h
  rw [← h]
  refine expect_congr _ fun T hT => ?_
  rw [inter_eq_left.2 (subset_of_indepSubset_w_pos _ _ hT)]

end RSubset

/-! ### Random subsets defined elementwise from independent labels -/

section SelectSetPi

variable {S : Finset α}

/-- A subset of `S` is recovered from its membership indicators. -/
theorem selectSet_decide_mem [DecidableEq α] {T : Finset α} (hT : T ⊆ S) :
    selectSet S (fun a => decide ((a : α) ∈ T)) = T := by
  ext x
  rw [mem_selectSet]
  exact ⟨fun ⟨_, hx⟩ => of_decide_eq_true hx, fun hx => ⟨hT hx, decide_eq_true hx⟩⟩

/-- The membership indicators of `selectSet S f` are `f`. -/
theorem decide_mem_selectSet [DecidableEq α] (f : S → Bool) (a : S) :
    decide ((a : α) ∈ selectSet S f) = f a := by
  by_cases h : f a = true
  · rw [h, decide_eq_true_iff, mem_selectSet_coe]
    exact h
  · rw [Bool.not_eq_true] at h
    rw [h, decide_eq_false_iff_not, mem_selectSet_coe, h]
    exact Bool.false_ne_true

/-- A random subset of `S` defined element by element from independent labels: if every
`a ∈ S` carries an independent label `ω a ~ μ a`, and `a` is selected when `f a (ω a) = true`,
an event of probability `p a`, then the selected set is the independent random subset
`indepSubset S p`. Example: [s5:lemZones] proof of (ii), "The event {v ∈ Zone} is a function of
the pair (choice(v), sublabel of v), and these pairs are independent over v. So Zone contains
each vertex of Y independently with probability exactly ρ_Y." -/
theorem map_selectSet_pi {p : α → ℝ} (h0 : ∀ a ∈ S, 0 ≤ p a) (h1 : ∀ a ∈ S, p a ≤ 1)
    {κ : S → Type*} (μ : ∀ a : S, FinDist (κ a)) (f : ∀ a : S, κ a → Bool)
    (hf : ∀ a : S, (μ a).map (f a) = bernoulli (p a) (h0 a a.2) (h1 a a.2)) :
    (pi μ).map (fun ω => selectSet S fun a => f a (ω a)) = indepSubset S p h0 h1 := by
  have e : (fun ω : ∀ a : S, κ a => selectSet S fun a => f a (ω a)) =
      selectSet S ∘ fun ω a => f a (ω a) := rfl
  rw [e, ← FinDist.map_map, map_pi]
  simp only [hf]
  rfl

/-- `map_selectSet_pi` with a constant selection probability `ρ`: the selected set is a
`ρ`-random subset of `S`. -/
theorem map_selectSet_pi_rsubset {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {κ : S → Type*}
    (μ : ∀ a : S, FinDist (κ a)) (f : ∀ a : S, κ a → Bool)
    (hf : ∀ a : S, (μ a).map (f a) = bernoulli ρ h0 h1) :
    (pi μ).map (fun ω => selectSet S fun a => f a (ω a)) = rsubset S ρ h0 h1 :=
  map_selectSet_pi _ _ μ f hf

end SelectSetPi

/-! ### Colour classes of a random colouring -/

section ColourClass

variable [Fintype ι] {k : ℕ} [NeZero k]

/-- [s3:lemL15p] "for i ∈ [k] let X_i be the graph with vertex set V(X) whose edges are the edges
of colour i": in a uniformly random `k`-colouring, the colour class of `j` is a `(1/k)`-random
subset of all elements. -/
theorem map_colourClass_randColouring (j : Fin k) (h0 : (0 : ℝ) ≤ 1 / k) (h1 : (1 : ℝ) / k ≤ 1) :
    (randColouring ι k).map (fun c => univ.filter fun e => c e = j) =
      rsubset univ (1 / k) h0 h1 := by
  classical
  ext T
  rw [map_w, rsubset_w, if_pos (subset_univ T)]
  have hev : (fun c : ι → Fin k => univ.filter fun e => c e = j) ⁻¹' {T} =
      {c | ∀ e ∈ (univ : Finset ι), c e ∈ (if e ∈ T then {j} else {j}ᶜ : Set (Fin k))} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, mem_univ,
      true_implies]
    constructor
    · rintro rfl e
      by_cases he : c e = j <;> simp [he]
    · intro h
      ext e
      have := h e
      by_cases he : e ∈ T <;> simp_all
  have hp : ∀ e : ι, (uniform (Fin k)).prob (if e ∈ T then {j} else {j}ᶜ) =
      if e ∈ T then 1 / (k : ℝ) else 1 - 1 / k := by
    intro e
    split_ifs
    · rw [prob_singleton, uniform_w_eq, Fintype.card_fin]
    · rw [prob_compl, prob_singleton, uniform_w_eq, Fintype.card_fin]
  rw [hev, prob_randColouring_forall_mem]
  simp only [hp]
  rw [prod_ite, filter_mem_eq_inter, univ_inter, prod_const, prod_const]
  congr 3
  ext e
  simp

omit [Fintype ι] in
/-- [s3:lemL15p] The colour class as a subset of the ambient type: for a uniformly random
`k`-colouring `c` of the elements of a finite set `E` (for edges, `E : Finset (Sym2 V)`), the set
`X_j = {e ∈ E | c e = j}` of elements of colour `j` is a `(1/k)`-random subset of `E`. -/
theorem map_selectSet_randColouring (E : Finset α) (j : Fin k) (h0 : (0 : ℝ) ≤ 1 / k)
    (h1 : (1 : ℝ) / k ≤ 1) :
    (randColouring E k).map (fun c => selectSet E fun e => decide (c e = j)) =
      rsubset E (1 / k) h0 h1 :=
  map_selectSet_pi_rsubset h0 h1 _ (fun _ c => decide (c = j))
    fun _ => map_decide_eq_uniform j h0 h1

end ColourClass

end FinDist

end EG
