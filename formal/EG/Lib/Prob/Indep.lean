module

public import EG.Lib.Prob.Named

/-!
# Independence and ρ-random subsets: API for the shared vocabulary

The predicates `FinDist.IndepFun`, `FinDist.iIndepFun` and `FinDist.IsRSubset` are defined in
`EG/Defs/Prob/FinDist.lean`. They are the fixed idioms for the manuscript's "X is independent of
Y", "the X_u are independent" and "V is a ρ-random subset of S" (see the conventions in the
header of `EG/Lib/Prob/Basic.lean`). This file relates them to laws and gives the standard
consequences.

* `IndepFun`: `indepFun_iff_map_eq_prod` (law form), `IndepFun.symm`, `IndepFun.comp`,
  `IndepFun.expect_mul`, `IndepFun.map_cond` (conditioning on a value of `X` does not change the
  law of `Y`: [s1:citMarkov](c)), `indepFun_map_iff` (transport), `indepFun_fst_snd`.
* `iIndepFun`: `iIndepFun_iff_map_eq_pi` (law form for a `Fintype` index),
  `iIndepFun.map_eq_pi_subtype` (law of a finite subfamily), `iIndepFun.comp`,
  `iIndepFun.indepFun` (pairwise independence), `iIndepFun.expect_prod`, `iIndepFun_map_iff`
  (transport), `iIndepFun_eval_pi` (the coordinates of `pi μ`), `iIndepFun_pi_of_dependsOn`
  (functions of pairwise disjoint blocks of coordinates).
* `IsRSubset`: `IsRSubset.map_eq` (law form), `isRSubset_iff` (the elementwise reading of the
  s3 convention), `isRSubset_selectSet` (a set selected element by element by independent
  Bernoulli(ρ) indicators), `isRSubset_map_iff` (transport), `isRSubset_rsubset`, and the
  consequences `IsRSubset.subset_ae`, `prob_mem`, `prob_superset`, `prob_disjoint`,
  `expect_card`, `expect_card_inter`, `prob_preimage`, `expect_comp`, `iIndepFun_mem`.
* A ρ-random subset `V` independent of a random variable `c` ("independent of the colouring"):
  `IsRSubset.cond_of_indepFun` (conditioned on `c = x`, `V` is still ρ-random) and
  `IsRSubset.map_pair_eq_prod` (the joint law of `(c, V)` is `law c ⊗ rsubset S ρ`).
-/

public section


namespace EG

namespace FinDist

open Finset

variable {Ω Ω' α γ δ : Type*}

/-! ### Independence of two random variables -/

section IndepFun

variable (μ : FinDist Ω) {X : Ω → γ} {Y : Ω → δ}

/-- Law form of independence: the joint law is the product of the marginal laws. -/
theorem indepFun_iff_map_eq_prod :
    μ.IndepFun X Y ↔ μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y) := by
  constructor
  · intro h
    ext ⟨c, d⟩
    rw [map_w, prod_w, map_w, map_w, ← h]
    congr 1
    ext ω
    simp
  · intro h A B
    have e : X ⁻¹' A ∩ Y ⁻¹' B = (fun ω => (X ω, Y ω)) ⁻¹' (A ×ˢ B) := rfl
    rw [e, ← prob_map, h, prob_prod_set_prod, prob_map, prob_map]

/-- Transport of independence along a pushforward. -/
theorem indepFun_map_iff (φ : Ω' → Ω) (ν : FinDist Ω') :
    (ν.map φ).IndepFun X Y ↔ ν.IndepFun (fun ω => X (φ ω)) (fun ω => Y (φ ω)) := by
  simp only [IndepFun, prob_map]
  rfl

/-- The two coordinates of a product distribution are independent. -/
theorem indepFun_fst_snd {β : Type*} (μ : FinDist α) (ν : FinDist β) :
    (μ.prod ν).IndepFun Prod.fst Prod.snd :=
  (indepFun_iff_map_eq_prod _).2 (by simp)

variable {μ}

theorem IndepFun.symm (h : μ.IndepFun X Y) : μ.IndepFun Y X :=
  fun A B => by rw [Set.inter_comm, h, mul_comm]

/-- Functions of independent variables are independent. -/
theorem IndepFun.comp {γ' δ' : Type*} (h : μ.IndepFun X Y) (f : γ → γ') (g : δ → δ') :
    μ.IndepFun (fun ω => f (X ω)) (fun ω => g (Y ω)) :=
  fun A B => h (f ⁻¹' A) (g ⁻¹' B)

/-- `E[F(X) G(Y)] = E[F(X)] · E[G(Y)]` for independent `X` and `Y`. -/
theorem IndepFun.expect_mul (h : μ.IndepFun X Y) (F : γ → ℝ) (G : δ → ℝ) :
    μ.expect (fun ω => F (X ω) * G (Y ω)) =
      μ.expect (fun ω => F (X ω)) * μ.expect (fun ω => G (Y ω)) := by
  have := congrArg (fun ν => ν.expect fun p => F p.1 * G p.2) ((indepFun_iff_map_eq_prod μ).1 h)
  simp only [expect_map, expect_prod_mul] at this
  exact this

/-- [s1:citMarkov](c) "given any fixed outcome of variables that are independent of the
variables being drawn … the conditional law of the latter is their unconditional law": if `X`
and `Y` are independent, then conditioned on `X = x` (an event of positive probability), `Y`
has its unconditional law. -/
theorem IndepFun.map_cond (h : μ.IndepFun X Y) (x : γ) (hx : 0 < μ.prob (X ⁻¹' {x})) :
    (μ.cond (X ⁻¹' {x}) hx).map Y = μ.map Y := by
  ext y
  rw [map_w, map_w, prob_cond, Set.inter_comm, h, mul_div_cancel_left₀ _ hx.ne']

end IndepFun

/-! ### Mutual independence of a family -/

section iIndepFun

variable (μ : FinDist Ω) {U : Type*} {β : U → Type*} {X : ∀ u, Ω → β u}

/-- Law form of mutual independence for a finite index type: the joint law is the product of
the marginal laws. -/
theorem iIndepFun_iff_map_eq_pi [Fintype U] :
    μ.iIndepFun X ↔ μ.map (fun ω u => X u ω) = pi fun u => μ.map (X u) := by
  constructor
  · intro h
    ext y
    rw [map_w, pi_w]
    simp only [map_w]
    have e : (fun ω u => X u ω) ⁻¹' {y} = {ω | ∀ u ∈ univ, X u ω ∈ ({y u} : Set (β u))} := by
      ext ω; simp [funext_iff]
    rw [e, h]
  · intro h s A
    classical
    have e : {ω | ∀ u ∈ s, X u ω ∈ A u} =
        (fun ω u => X u ω) ⁻¹' {g : ∀ u, β u | ∀ u ∈ s, g u ∈ A u} := rfl
    rw [e, ← prob_map, h, prob_pi_forall_mem]
    simp only [prob_map]

/-- Transport of mutual independence along a pushforward. -/
theorem iIndepFun_map_iff (φ : Ω' → Ω) (ν : FinDist Ω') :
    (ν.map φ).iIndepFun X ↔ ν.iIndepFun (fun u ω => X u (φ ω)) := by
  simp only [iIndepFun, prob_map]
  rfl

/-- The coordinates of a finite product are mutually independent. -/
theorem iIndepFun_eval_pi {ι : Type*} [Fintype ι] {κ : ι → Type*} (μ : ∀ i, FinDist (κ i)) :
    (pi μ).iIndepFun fun i f => f i :=
  fun s A => (prob_pi_forall_mem μ s A).trans
    (prod_congr rfl fun i _ => (prob_pi_eval μ i (A i)).symm)

/-- Functions of pairwise disjoint blocks of coordinates of a finite product are mutually
independent. Example: [s4:lemTPV] proof, item (G4): "the variables I_u (u ∈ A_w(w)) depend on
pairwise distinct edges wu and distinct vertices u, so they are independent". The law form is
`FinDist.map_pi_of_dependsOn`. -/
theorem iIndepFun_pi_of_dependsOn {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (μ : ∀ i, FinDist (κ i)) (B : U → Set ι) (hB : Pairwise fun u v => Disjoint (B u) (B v))
    (g : ∀ u, (∀ i, κ i) → β u) (hg : ∀ u f f', (∀ i ∈ B u, f i = f' i) → g u f = g u f') :
    (pi μ).iIndepFun g := by
  intro s A
  refine prob_pi_forall_of_dependsOn μ s B (fun u _ v _ h => hB h) _ fun u _ f f' h hf => ?_
  show g u f' ∈ A u
  rw [← hg u f f' h]
  exact hf

variable {μ}

/-- Functions of mutually independent variables are mutually independent. -/
theorem iIndepFun.comp {γ : U → Type*} (h : μ.iIndepFun X) (f : ∀ u, β u → γ u) :
    μ.iIndepFun fun u ω => f u (X u ω) :=
  fun s A => h s fun u => f u ⁻¹' A u

/-- Mutually independent variables are pairwise independent. -/
theorem iIndepFun.indepFun (h : μ.iIndepFun X) {u v : U} (huv : u ≠ v) :
    μ.IndepFun (X u) (X v) := by
  classical
  intro A B
  have key := h {u, v} fun w =>
    {b | (∀ hw : w = u, (hw ▸ b : β u) ∈ A) ∧ ∀ hw : w = v, (hw ▸ b : β v) ∈ B}
  have hu : {b : β u | (∀ hw : u = u, (hw ▸ b : β u) ∈ A) ∧ ∀ hw : u = v, (hw ▸ b : β v) ∈ B}
      = A := by
    ext b; simp [huv]
  have hv : {b : β v | (∀ hw : v = u, (hw ▸ b : β u) ∈ A) ∧ ∀ hw : v = v, (hw ▸ b : β v) ∈ B}
      = B := by
    ext b; simp [Ne.symm huv]
  rw [prod_pair huv, hu, hv] at key
  rw [← key]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, mem_insert, mem_singleton,
    forall_eq_or_imp, forall_eq]
  simp [huv, Ne.symm huv]

/-- The law of a finite subfamily of mutually independent variables is the product of the
marginal laws. -/
theorem iIndepFun.map_eq_pi_subtype (h : μ.iIndepFun X) (s : Finset U) :
    μ.map (fun ω (u : s) => X u ω) = pi fun u : s => μ.map (X u) := by
  ext y
  rw [map_w, pi_w]
  simp only [map_w]
  have e : (fun ω (u : s) => X u ω) ⁻¹' {y} =
      {ω | ∀ u ∈ s, X u ω ∈ {b : β u | ∀ hu : u ∈ s, b = y ⟨u, hu⟩}} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_ofPred_eq,
      Subtype.forall]
    exact ⟨fun h u hu _ => h u hu, fun h u hu => h u hu hu⟩
  rw [e, h, ← prod_coe_sort]
  refine prod_congr rfl fun u _ => ?_
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun h => h u.2, fun h _ => h⟩

/-- The expectation of a product of functions of mutually independent variables is the product
of the expectations. -/
theorem iIndepFun.expect_prod (h : μ.iIndepFun X) (s : Finset U) (F : ∀ u, β u → ℝ) :
    μ.expect (fun ω => ∏ u ∈ s, F u (X u ω)) = ∏ u ∈ s, μ.expect (fun ω => F u (X u ω)) := by
  have h1 : (fun ω => ∏ u ∈ s, F u (X u ω)) = fun ω => ∏ u : s, F u (X u ω) :=
    funext fun ω => (prod_coe_sort s fun u => F u (X u ω)).symm
  rw [h1, ← prod_coe_sort s fun u => μ.expect (fun ω => F u (X u ω))]
  have h2 := congrArg (fun ν => ν.expect fun g => ∏ u : s, F u (g u)) (h.map_eq_pi_subtype s)
  simp only [expect_map, expect_pi_prod] at h2
  exact h2

end iIndepFun

/-! ### ρ-random subsets -/

section IsRSubset

variable (μ : FinDist Ω) {V : Ω → Finset α} {S : Finset α} {ρ : ℝ}

/-- The identity on `rsubset S ρ` is a ρ-random subset of `S`. -/
theorem isRSubset_rsubset (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (rsubset S ρ h0 h1).IsRSubset (fun T => T) S ρ :=
  ⟨h0, h1, map_id' _⟩

/-- Transport along a pushforward. -/
theorem isRSubset_map_iff (φ : Ω' → Ω) (ν : FinDist Ω') :
    (ν.map φ).IsRSubset V S ρ ↔ ν.IsRSubset (fun ω => V (φ ω)) S ρ := by
  simp only [IsRSubset, FinDist.map_map]
  rfl

variable {μ}

theorem IsRSubset.nonneg (h : μ.IsRSubset V S ρ) : 0 ≤ ρ :=
  let ⟨h0, _, _⟩ := h
  h0

theorem IsRSubset.le_one (h : μ.IsRSubset V S ρ) : ρ ≤ 1 :=
  let ⟨_, h1, _⟩ := h
  h1

/-- Law form: the law of `V` is `rsubset S ρ`. -/
theorem IsRSubset.map_eq (h : μ.IsRSubset V S ρ) : μ.map V = rsubset S ρ h.nonneg h.le_one :=
  let ⟨_, _, hV⟩ := h
  hV

theorem IsRSubset.prob_preimage (h : μ.IsRSubset V S ρ) (B : Set (Finset α)) :
    μ.prob (V ⁻¹' B) = (rsubset S ρ h.nonneg h.le_one).prob B := by
  rw [← prob_map, h.map_eq]

theorem IsRSubset.expect_comp (h : μ.IsRSubset V S ρ) (Y : Finset α → ℝ) :
    μ.expect (fun ω => Y (V ω)) = (rsubset S ρ h.nonneg h.le_one).expect Y := by
  rw [← expect_map, h.map_eq]

/-- A ρ-random subset of `S` is almost surely contained in `S`. -/
theorem IsRSubset.subset_ae (h : μ.IsRSubset V S ρ) : ∀ ω, 0 < μ.w ω → V ω ⊆ S := by
  have := h.prob_preimage {T | T ⊆ S}
  rw [prob_rsubset_subset] at this
  exact (prob_eq_one_iff _ _).1 this

/-- Each element of `S` lies in a ρ-random subset of `S` with probability `ρ`. -/
theorem IsRSubset.prob_mem (h : μ.IsRSubset V S ρ) {a : α} (ha : a ∈ S) :
    μ.prob {ω | a ∈ V ω} = ρ :=
  (h.prob_preimage {T | a ∈ T}).trans (prob_mem_rsubset _ _ ha)

theorem IsRSubset.prob_superset [DecidableEq α] (h : μ.IsRSubset V S ρ) {A : Finset α}
    (hA : A ⊆ S) : μ.prob {ω | A ⊆ V ω} = ρ ^ A.card :=
  (h.prob_preimage {T | A ⊆ T}).trans (prob_superset_rsubset _ _ hA)

theorem IsRSubset.prob_disjoint [DecidableEq α] (h : μ.IsRSubset V S ρ) {B : Finset α}
    (hB : B ⊆ S) : μ.prob {ω | Disjoint B (V ω)} = (1 - ρ) ^ B.card :=
  (h.prob_preimage {T | Disjoint B T}).trans (prob_disjoint_rsubset _ _ hB)

theorem IsRSubset.expect_card_inter [DecidableEq α] (h : μ.IsRSubset V S ρ) (U : Finset α) :
    μ.expect (fun ω => ((V ω ∩ U).card : ℝ)) = ρ * (S ∩ U).card :=
  (h.expect_comp fun T => ((T ∩ U).card : ℝ)).trans (expect_card_inter_rsubset _ _ U)

theorem IsRSubset.expect_card [DecidableEq α] (h : μ.IsRSubset V S ρ) :
    μ.expect (fun ω => ((V ω).card : ℝ)) = ρ * S.card :=
  (h.expect_comp fun T => (T.card : ℝ)).trans (expect_card_rsubset _ _)

/-- A set selected element by element by mutually independent Bernoulli(ρ) indicators is a
ρ-random subset. This is the form in which the manuscript establishes the convention, e.g.
[s5:lemZones] proof of (ii): "these pairs are independent over v. So Zone contains each vertex of
Y independently with probability exactly ρ_Y". -/
theorem isRSubset_selectSet (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {b : S → Ω → Bool}
    (hind : μ.iIndepFun b) (hp : ∀ a : S, μ.prob {ω | b a ω = true} = ρ) :
    μ.IsRSubset (fun ω => selectSet S fun a => b a ω) S ρ := by
  refine ⟨h0, h1, ?_⟩
  have e : (fun ω => selectSet S fun a => b a ω) = selectSet S ∘ fun ω a => b a ω := rfl
  have hb : ∀ a : S, μ.map (b a) = bernoulli ρ h0 h1 := fun a =>
    map_eq_bernoulli h0 h1 μ _ (hp a)
  rw [e, ← FinDist.map_map, (iIndepFun_iff_map_eq_pi μ).1 hind]
  simp only [hb]
  rfl

/-- The membership indicators of a ρ-random subset of `S` are mutually independent. -/
theorem IsRSubset.iIndepFun_mem [DecidableEq α] (h : μ.IsRSubset V S ρ) :
    μ.iIndepFun fun (a : S) ω => decide ((a : α) ∈ V ω) := by
  rw [iIndepFun_iff_map_eq_pi]
  have hb : ∀ a : S, μ.map (fun ω => decide ((a : α) ∈ V ω)) = bernoulli ρ h.nonneg h.le_one :=
    fun a => map_eq_bernoulli _ _ μ _ (by simpa using h.prob_mem a.2)
  simp only [hb]
  have e : (fun ω (a : S) => decide ((a : α) ∈ V ω)) =
      (fun T (a : S) => decide ((a : α) ∈ T)) ∘ V := rfl
  rw [e, ← FinDist.map_map, h.map_eq, rsubset, indepSubset, FinDist.map_map]
  have e' : ((fun T (a : S) => decide ((a : α) ∈ T)) ∘ selectSet S) = id :=
    funext fun f => funext fun a => decide_mem_selectSet f a
  rw [e', map_id]

/-- [s3, "Conventions for this section"] The elementwise reading of `IsRSubset`: `V` is a
ρ-random subset of `S` iff `ρ ∈ [0, 1]`, `V ⊆ S` almost surely, the indicators of the events
`a ∈ V` (`a ∈ S`) are mutually independent, and each of these events has probability `ρ`
("a random subset of S that contains each element of S independently with probability ρ"). -/
theorem isRSubset_iff [DecidableEq α] :
    μ.IsRSubset V S ρ ↔ 0 ≤ ρ ∧ ρ ≤ 1 ∧ (∀ ω, 0 < μ.w ω → V ω ⊆ S) ∧
      μ.iIndepFun (fun (a : S) ω => decide ((a : α) ∈ V ω)) ∧
      ∀ a ∈ S, μ.prob {ω | a ∈ V ω} = ρ := by
  constructor
  · intro h
    exact ⟨h.nonneg, h.le_one, h.subset_ae, h.iIndepFun_mem, fun a ha => h.prob_mem ha⟩
  · rintro ⟨h0, h1, hsub, hind, hp⟩
    obtain ⟨_, _, hV⟩ := isRSubset_selectSet h0 h1 hind fun a => by simpa using hp a a.2
    refine ⟨h0, h1, ?_⟩
    rw [← hV]
    exact map_congr_ae μ fun ω hω => (selectSet_decide_mem (hsub ω hω)).symm

/-! #### A ρ-random subset independent of another random variable

The manuscript pattern "V is a ρ-random subset of S, independent of the colouring c" is written
`μ.IsRSubset V S ρ ∧ μ.IndepFun c V`. The two lemmas below are the forms in which it is used:
conditioning on a value of `c`, and the joint law of `(c, V)`. -/

/-- [s5:lemE1] proof of (c): "the set V_{l,c,ς} … contains each vertex of Y independently with
probability ρ_Y ≥ 1/(12 L_Y^5), independently of the colouring of Y", used through
[s3:lemCOL](c) ("random subsets of V(Y), independent of the stage-1 lending data of Y"). If `V`
is a ρ-random subset of `S` and `V` is independent of `c`, then `V` is still a ρ-random subset of
`S` conditioned on `c = x`, for every value `x` of positive probability. -/
theorem IsRSubset.cond_of_indepFun {c : Ω → γ} (hV : μ.IsRSubset V S ρ) (hi : μ.IndepFun c V)
    (x : γ) (hx : 0 < μ.prob (c ⁻¹' {x})) : (μ.cond (c ⁻¹' {x}) hx).IsRSubset V S ρ :=
  ⟨hV.nonneg, hV.le_one, (hi.map_cond x hx).trans hV.map_eq⟩

/-- The joint law of a random variable `c` and a ρ-random subset `V` of `S` independent of `c`
is the product of the law of `c` and `rsubset S ρ`. -/
theorem IsRSubset.map_pair_eq_prod {c : Ω → γ} (hV : μ.IsRSubset V S ρ) (hi : μ.IndepFun c V) :
    μ.map (fun ω => (c ω, V ω)) = (μ.map c).prod (rsubset S ρ hV.nonneg hV.le_one) := by
  rw [(indepFun_iff_map_eq_prod μ).1 hi, hV.map_eq]

end IsRSubset

end FinDist

end EG
