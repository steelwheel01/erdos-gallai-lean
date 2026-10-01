module

public import EG.Lib.Prob.Named
public import EG.Lib.Prob.Chernoff
public import EG.Lib.Prob.Indep

/-!
# Label laws of the vortex runs and observation (MC) (manuscript s4, "Monotone comparison",
Lemma TPV (b), (c), Theorem VX⁺)

Unit P3-s4.
* `EG.VortexLaw.levLaw J`: the truncated level law on `{0,1,…,J}`:
  "`P(lev(v) ≥ j) = 2^{-j}` for `0 ≤ j ≤ J` (that is, `P(lev(v) = j) = 2^{-(j+1)}` for
  `0 ≤ j < J` and `P(lev(v) = J) = 2^{-J}`)" (`levLaw_tail`).
* `EG.VortexLaw.kapLaw`: "`κ(v) ∈ {0,1,2,3}` with `P(κ(v) = 0) = 1/2` and `P(κ(v) = c) = 1/6`".
* `EG.VortexLaw.prob_indepSubset_mono`: observation (MC): for an upward closed family `𝒦` of
  subsets of `S`, `P(V ∈ 𝒦)` is non-decreasing in the element probabilities of the independent
  random subset `V` ("If `p, q ∈ [0,1]^S` satisfy `p_x ≤ q_x` for every `x ∈ S`, then
  `Ψ_𝒦(p) ≤ Ψ_𝒦(q)` … `P(V ∈ 𝒦) = Ψ_𝒦(q^V)`").
* `EG.VortexLaw.IndepEvents.prod`: rectangle events of two independent experiments are
  independent when their components are.
-/

public section

namespace EG

namespace VortexLaw

open Finset FinDist

/-! ### The truncated level law -/

/-- The weights of the truncated level law on `Fin (J+1)`. -/
@[expose] noncomputable def levW (J : ℕ) (i : Fin (J + 1)) : ℝ :=
  if (i : ℕ) < J then (1 / 2 : ℝ) ^ ((i : ℕ) + 1) else (1 / 2 : ℝ) ^ J

theorem levW_nonneg (J : ℕ) (i : Fin (J + 1)) : 0 ≤ levW J i := by
  unfold levW; split_ifs <;> positivity

theorem geom_sum_half (j : ℕ) : ∑ i ∈ range j, (1 / 2 : ℝ) ^ (i + 1) = 1 - (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [sum_range_succ, ih]; ring

theorem sum_levW (J : ℕ) : ∑ i, levW J i = 1 := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∑ i : Fin J, levW J (Fin.castSucc i) = ∑ i ∈ range J, (1 / 2 : ℝ) ^ (i + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun i _ => ?_
    simp [levW, i.2]
  have h2 : levW J (Fin.last J) = (1 / 2 : ℝ) ^ J := by simp [levW]
  rw [h1, h2, geom_sum_half]
  ring

/-- The truncated level law. -/
@[expose] noncomputable def levLaw (J : ℕ) : FinDist (Fin (J + 1)) :=
  ofFintype (levW J) (levW_nonneg J) (sum_levW J)

theorem levLaw_w (J : ℕ) (i : Fin (J + 1)) : (levLaw J).w i = levW J i := rfl

/-- "`P(lev(v) ≥ j) = 2^{-j}` for `0 ≤ j ≤ J`". -/
theorem levLaw_tail {J j : ℕ} (hj : j ≤ J) :
    (levLaw J).prob {i | j ≤ (i : ℕ)} = (1 / 2 : ℝ) ^ j := by
  classical
  have hc := (levLaw J).prob_add_prob_compl {i | j ≤ (i : ℕ)}
  have hlow : (levLaw J).prob {i | j ≤ (i : ℕ)}ᶜ = 1 - (1 / 2 : ℝ) ^ j := by
    rw [prob_eq_sum]
    have e : ∀ i : Fin (J + 1), ({i | j ≤ (i : ℕ)}ᶜ : Set (Fin (J + 1))).indicator
        (levLaw J).w i = if (i : ℕ) < j then (1 / 2 : ℝ) ^ ((i : ℕ) + 1) else 0 := by
      intro i
      by_cases h : (i : ℕ) < j
      · rw [Set.indicator_of_mem (by simp; omega), levLaw_w, levW, if_pos (by omega), if_pos h]
      · rw [Set.indicator_of_notMem (by simp; omega), if_neg h]
    simp only [e]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then (1 / 2 : ℝ) ^ (i + 1) else 0),
      ← sum_filter]
    have hf : (range (J + 1)).filter (· < j) = range j := by
      ext i; simp; omega
    rw [hf, geom_sum_half]
  linarith

/-! ### The law of `κ` -/

/-- The weights of `κ`: `1/2` at `0`, `1/6` elsewhere. -/
@[expose] noncomputable def kapW (i : Fin 4) : ℝ := if i = 0 then 1 / 2 else 1 / 6

/-- The law of `κ` (Lemma TPV (c), Theorem VX⁺). -/
@[expose] noncomputable def kapLaw : FinDist (Fin 4) :=
  ofFintype kapW (fun i => by unfold kapW; split_ifs <;> norm_num)
    (by simp [Fin.sum_univ_four, kapW]; norm_num)

theorem kapLaw_zero : kapLaw.prob {x | x = 0} = 1 / 2 := by
  rw [Set.ofPred_eq_eq_singleton, prob_singleton]
  rfl

theorem kapLaw_succ (c : Fin 3) : kapLaw.prob {x | x = c.succ} = 1 / 6 := by
  rw [Set.ofPred_eq_eq_singleton, prob_singleton]
  show kapW c.succ = 1 / 6
  simp [kapW, Fin.succ_ne_zero]

/-! ### Observation (MC) -/

section MC

variable {α : Type*} [DecidableEq α]

/-- `Ψ_𝒦(r) = ∑_{T ∈ 𝒦} ∏_{x ∈ T} r_x ∏_{x ∈ S \ T} (1 - r_x)` (over subsets `T ⊆ S`). -/
@[expose] noncomputable def Psi (S : Finset α) (r : α → ℝ) (K : Set (Finset α)) : ℝ := by
  classical
  exact ∑ T ∈ S.powerset, if T ∈ K then (∏ a ∈ T, r a) * ∏ a ∈ S \ T, (1 - r a) else 0

theorem Psi_nonneg (S : Finset α) {r : α → ℝ} (h0 : ∀ a ∈ S, 0 ≤ r a) (h1 : ∀ a ∈ S, r a ≤ 1)
    (K : Set (Finset α)) : 0 ≤ Psi S r K := by
  classical
  unfold Psi
  refine sum_nonneg fun T hT => ?_
  split_ifs
  · refine mul_nonneg (prod_nonneg fun a ha => h0 a (mem_powerset.1 hT ha))
      (prod_nonneg fun a ha => ?_)
    linarith [h1 a (mem_sdiff.1 ha).1]
  · exact le_rfl

theorem Psi_mono_K (S : Finset α) {r : α → ℝ} (h0 : ∀ a ∈ S, 0 ≤ r a) (h1 : ∀ a ∈ S, r a ≤ 1)
    {K K' : Set (Finset α)} (hK : ∀ T ⊆ S, T ∈ K → T ∈ K') : Psi S r K ≤ Psi S r K' := by
  classical
  unfold Psi
  refine sum_le_sum fun T hT => ?_
  have hw : 0 ≤ (∏ a ∈ T, r a) * ∏ a ∈ S \ T, (1 - r a) :=
    mul_nonneg (prod_nonneg fun a ha => h0 a (mem_powerset.1 hT ha))
      (prod_nonneg fun a ha => by linarith [h1 a (mem_sdiff.1 ha).1])
  by_cases h : T ∈ K
  · rw [if_pos h, if_pos (hK T (mem_powerset.1 hT) h)]
  · rw [if_neg h]; split_ifs <;> linarith

theorem Psi_insert {S : Finset α} {y : α} (hy : y ∉ S) (r : α → ℝ) (K : Set (Finset α)) :
    Psi (insert y S) r K = (1 - r y) * Psi S r K + r y * Psi S r {T | insert y T ∈ K} := by
  classical
  unfold Psi
  rw [sum_powerset_insert hy, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have hyT : y ∉ T := fun h => hy (mem_powerset.1 hT h)
    have e : insert y S \ T = insert y (S \ T) := by
      ext a; simp only [mem_sdiff, mem_insert]; constructor
      · rintro ⟨h | h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, h'⟩
      · rintro (rfl | ⟨h, h'⟩)
        · exact ⟨Or.inl rfl, hyT⟩
        · exact ⟨Or.inr h, h'⟩
    rw [e, prod_insert (fun h => hy (mem_sdiff.1 h).1)]
    split_ifs <;> ring
  · refine sum_congr rfl fun T hT => ?_
    have hyT : y ∉ T := fun h => hy (mem_powerset.1 hT h)
    have e : insert y S \ insert y T = S \ T := by
      ext a; simp only [mem_sdiff, mem_insert]; constructor
      · rintro ⟨h | h, h'⟩
        · exact absurd (Or.inl h) h'
        · exact ⟨h, fun h'' => h' (Or.inr h'')⟩
      · rintro ⟨h, h'⟩
        refine ⟨Or.inr h, ?_⟩
        rintro (rfl | h'')
        · exact hy h
        · exact h' h''
    rw [e, prod_insert hyT]
    simp only [Set.mem_ofPred_eq]
    split_ifs <;> ring

/-- (MC), the comparison: `Ψ_𝒦` is non-decreasing on `[0,1]^S` for an upward closed `𝒦`. -/
theorem Psi_mono : ∀ (S : Finset α) {p q : α → ℝ}, (∀ a ∈ S, 0 ≤ p a) → (∀ a ∈ S, q a ≤ 1) →
    (∀ a ∈ S, p a ≤ q a) → ∀ K : Set (Finset α),
    (∀ T T', T ⊆ T' → T' ⊆ S → T ∈ K → T' ∈ K) → Psi S p K ≤ Psi S q K := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro p q _ _ _ K _
    unfold Psi
    simp
  | insert y S hy ih =>
    intro p q hp0 hq1 hpq K hK
    have hp0' : ∀ a ∈ S, 0 ≤ p a := fun a ha => hp0 a (mem_insert_of_mem ha)
    have hq1' : ∀ a ∈ S, q a ≤ 1 := fun a ha => hq1 a (mem_insert_of_mem ha)
    have hpq' : ∀ a ∈ S, p a ≤ q a := fun a ha => hpq a (mem_insert_of_mem ha)
    have hq0' : ∀ a ∈ S, 0 ≤ q a := fun a ha => le_trans (hp0' a ha) (hpq' a ha)
    have hK0 : ∀ T T', T ⊆ T' → T' ⊆ S → T ∈ K → T' ∈ K :=
      fun T T' h h' => hK T T' h (h'.trans (subset_insert _ _))
    have hK1 : ∀ T T', T ⊆ T' → T' ⊆ S → T ∈ {T | insert y T ∈ K} →
        T' ∈ {T | insert y T ∈ K} := by
      intro T T' h h' hT
      exact hK _ _ (insert_subset_insert y h) (insert_subset_insert y h') hT
    have a0 := ih hp0' hq1' hpq' K hK0
    have a1 := ih hp0' hq1' hpq' _ hK1
    have b01 : Psi S q K ≤ Psi S q {T | insert y T ∈ K} :=
      Psi_mono_K S hq0' hq1' fun T hT h =>
        hK T (insert y T) (subset_insert _ _) (insert_subset_insert y hT) h
    rw [Psi_insert hy, Psi_insert hy]
    have hpy0 := hp0 y (mem_insert_self _ _)
    have hqy1 := hq1 y (mem_insert_self _ _)
    have hpqy := hpq y (mem_insert_self _ _)
    nlinarith

/-- (MC), the formula: `P(V ∈ 𝒦) = Ψ_𝒦(p)` for the independent random subset `V` of `S` with
element probabilities `p`. -/
theorem prob_indepSubset_eq_Psi (S : Finset α) {p : α → ℝ} (h0 : ∀ a ∈ S, 0 ≤ p a)
    (h1 : ∀ a ∈ S, p a ≤ 1) (K : Set (Finset α)) :
    (indepSubset S p h0 h1).prob K = Psi S p K := by
  classical
  have hs : (indepSubset S p h0 h1).supp ⊆ S.powerset := by
    intro T hT
    rw [mem_powerset]
    exact subset_of_indepSubset_w_pos h0 h1 ((mem_supp_iff_pos _).1 hT)
  rw [prob_eq_sum_of_supp_subset _ hs, Psi]
  refine sum_congr rfl fun T hT => ?_
  by_cases h : T ∈ K
  · rw [Set.indicator_of_mem h, if_pos h, indepSubset_w, if_pos (mem_powerset.1 hT)]
  · rw [Set.indicator_of_notMem h, if_neg h]

/-- Observation (MC): for an upward closed family `𝒦` of subsets of `S` and element
probabilities `p ≤ q`, `P(V_p ∈ 𝒦) ≤ P(V_q ∈ 𝒦)`. -/
theorem prob_indepSubset_mono (S : Finset α) {p q : α → ℝ} (hp0 : ∀ a ∈ S, 0 ≤ p a)
    (hp1 : ∀ a ∈ S, p a ≤ 1) (hq0 : ∀ a ∈ S, 0 ≤ q a) (hq1 : ∀ a ∈ S, q a ≤ 1)
    (hpq : ∀ a ∈ S, p a ≤ q a) (K : Set (Finset α))
    (hK : ∀ T T', T ⊆ T' → T' ⊆ S → T ∈ K → T' ∈ K) :
    (indepSubset S p hp0 hp1).prob K ≤ (indepSubset S q hq0 hq1).prob K := by
  rw [prob_indepSubset_eq_Psi, prob_indepSubset_eq_Psi]
  exact Psi_mono S hp0 hq1 hpq K hK

end MC

/-! ### Rectangle events of a product experiment -/

/-- Rectangle events `A i × B i` under `μ ⊗ ν` are independent when the `A i` are independent
under `μ` and the `B i` under `ν`. -/
theorem IndepEvents.prod {α β ι : Type*} {μ : FinDist α} {ν : FinDist β} {s : Finset ι}
    {A : ι → Set α} {B : ι → Set β} (hA : μ.IndepEvents s A) (hB : ν.IndepEvents s B) :
    (μ.prod ν).IndepEvents s (fun i => A i ×ˢ B i) := by
  intro T hT
  have e : {ω : α × β | ∀ i ∈ T, ω ∈ A i ×ˢ B i} =
      {a | ∀ i ∈ T, a ∈ A i} ×ˢ {b | ∀ i ∈ T, b ∈ B i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_prod]
    exact ⟨fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩,
      fun h i hi => ⟨h.1 i hi, h.2 i hi⟩⟩
  rw [e, prob_prod_set_prod, hA T hT, hB T hT, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => (prob_prod_set_prod μ ν (A i) (B i)).symm

end VortexLaw

end EG
