module

public import EG.Lib.Prob.Indep

/-!
# The union of independent random subsets is a random subset — P3-s3

Used for the union law of (S2) (manuscript s3:eqS2): "If `V_1,…,V_{ℓ_*}` are independent random
subsets of a set `S`, where `V_i` is `p_*`-random for `i < ℓ_*` and `V_{ℓ_*}` is `q_*`-random, then
`V_1 ∪ ⋯ ∪ V_{ℓ_*}` is a `ρ`-random subset of `S`."

* `FinDist.iIndepFun_of_univ`: for a finite index type, the product formula for the full index
  set (all events) implies mutual independence.
* `FinDist.iIndepFun_mem_pair`: for independent layers `V_i`, each an `r_i`-random subset of `S`,
  the indicators of `a ∈ V_i` over all pairs `(i, a)` are mutually independent.
* `FinDist.isRSubset_biUnion`: the union of independent `r_i`-random subsets of `S` is a
  `ρ`-random subset of `S` whenever `∏ (1 - r_i) = 1 - ρ` and `ρ ∈ [0,1]`.
-/

public section

namespace EG

namespace FinDist

open Finset

variable {Ω α : Type*}

/-- For a finite index type, the product formula for the full index set implies mutual
independence (events on the indices outside `s` are taken to be `univ`). -/
theorem iIndepFun_of_univ {U : Type*} [Fintype U] {β : U → Type*} {μ : FinDist Ω}
    {X : ∀ u, Ω → β u}
    (h : ∀ A : ∀ u, Set (β u),
      μ.prob {ω | ∀ u ∈ (univ : Finset U), X u ω ∈ A u} = ∏ u, μ.prob (X u ⁻¹' A u)) :
    μ.iIndepFun X := by
  classical
  intro s A
  set A' : ∀ u, Set (β u) := fun u => if u ∈ s then A u else Set.univ with hA'
  have e : {ω | ∀ u ∈ s, X u ω ∈ A u} = {ω | ∀ u ∈ (univ : Finset U), X u ω ∈ A' u} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_univ, true_implies, hA']
    constructor
    · intro hω u
      split_ifs with hu
      · exact hω u hu
      · exact Set.mem_univ _
    · intro hω u hu
      have := hω u
      rwa [if_pos hu] at this
  rw [e, h A']
  have e2 : ∀ u, μ.prob (X u ⁻¹' A' u) = if u ∈ s then μ.prob (X u ⁻¹' A u) else 1 := by
    intro u
    simp only [hA']
    split_ifs
    · rfl
    · rw [Set.preimage_univ, prob_univ]
  simp only [e2]
  rw [prod_ite_mem univ s, univ_inter]

variable [DecidableEq α] {ι : Type*} [Fintype ι]

/-- The indicators of `a ∈ V_i`, over all pairs `(i, a)` with `a ∈ S`, are mutually independent
when the layers `V_i` are independent and each is a random subset of `S`. -/
theorem iIndepFun_mem_pair {μ : FinDist Ω} {S : Finset α} (Vs : Ω → ι → Finset α) (r : ι → ℝ)
    (hind : μ.iIndepFun (fun i ω => Vs ω i))
    (hR : ∀ i, μ.IsRSubset (fun ω => Vs ω i) S (r i)) :
    μ.iIndepFun (fun (x : ι × S) ω => decide ((x.2 : α) ∈ Vs ω x.1)) := by
  classical
  apply iIndepFun_of_univ
  intro A
  set B : ι → Set (Finset α) := fun i => {T | ∀ a : S, decide ((a : α) ∈ T) ∈ A (i, a)} with hB
  have e : {ω | ∀ x ∈ (univ : Finset (ι × S)), decide ((x.2 : α) ∈ Vs ω x.1) ∈ A x} =
      {ω | ∀ i ∈ (univ : Finset ι), Vs ω i ∈ B i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_univ, true_implies, hB, Prod.forall]
  rw [e, hind univ B, Fintype.prod_prod_type]
  refine prod_congr rfl fun i _ => ?_
  have := (hR i).iIndepFun_mem univ (fun a => A (i, a))
  rw [← this]
  congr 1
  ext ω
  simp [hB]

/-- The union of independent random subsets `V_i` of `S`, `V_i` being `r_i`-random, is a
`ρ`-random subset of `S` when `∏_i (1 - r_i) = 1 - ρ` (and `ρ ∈ [0,1]`). -/
theorem isRSubset_biUnion {μ : FinDist Ω} {S : Finset α} (Vs : Ω → ι → Finset α) (r : ι → ℝ)
    {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hind : μ.iIndepFun (fun i ω => Vs ω i))
    (hR : ∀ i, μ.IsRSubset (fun ω => Vs ω i) S (r i))
    (hρ : ∏ i, (1 - r i) = 1 - ρ) :
    μ.IsRSubset (fun ω => univ.biUnion (Vs ω)) S ρ := by
  classical
  rw [isRSubset_iff]
  refine ⟨h0, h1, ?_, ?_, ?_⟩
  · intro ω hω
    exact biUnion_subset.2 fun i _ => (hR i).subset_ae ω hω
  · -- indicators of the union: functions of disjoint blocks of the pair indicators
    have hpair := iIndepFun_mem_pair Vs r hind hR
    rw [iIndepFun_iff_map_eq_pi] at hpair
    have hblk := iIndepFun_pi_of_dependsOn
      (fun x : ι × S => μ.map (fun ω => decide ((x.2 : α) ∈ Vs ω x.1)))
      (fun a : S => {x : ι × S | x.2 = a})
      (fun a b hab => Set.disjoint_left.2 fun x hxa hxb => hab (hxa.symm.trans hxb))
      (fun (a : S) (f : ι × S → Bool) => decide (∃ i, f (i, a) = true))
      (fun a f f' hff' => by
        have : ∀ i, f (i, a) = f' (i, a) := fun i => hff' (i, a) rfl
        simp only [this])
    rw [← hpair, iIndepFun_map_iff] at hblk
    convert hblk using 2 with a ω
    simp
  · intro a ha
    have hc : {ω | a ∈ univ.biUnion (Vs ω)} = {ω | ∀ i ∈ (univ : Finset ι),
        Vs ω i ∈ ({T | a ∉ T} : Set (Finset α))}ᶜ := by
      ext ω; simp
    rw [hc, prob_compl, hind univ (fun _ => {T | a ∉ T})]
    have hi : ∀ i, μ.prob ((fun ω => Vs ω i) ⁻¹' {T | a ∉ T}) = 1 - r i := by
      intro i
      have e : (fun ω => Vs ω i) ⁻¹' {T | a ∉ T} = {ω | a ∈ Vs ω i}ᶜ := by ext ω; simp
      rw [e, prob_compl, (hR i).prob_mem ha]
    simp only [hi]
    rw [hρ]; ring

end FinDist

end EG
