module

public import EG.Lib.Vortex.TPVProbG2

/-!
# The good event (G4) of the TPV run (manuscript s4:lemTPV, proof, item (G4))

Unit P3-s4. "For every `0 ≤ j < J` and every `w ∈ P` the set
`C^j_w := {wu : u ∈ A(w), wu ∈ M, u ∈ Z_j}` has at least `6` elements. For `u ∈ A(w)` let
`I_u := 1[wu ∈ M and u ∈ Z_j]`. Since `u ≠ w`, the variables `I_u` (`u ∈ A(w)`) depend on
pairwise distinct edges `wu` and distinct vertices `u`, so they are independent; and
`P(I_u = 1) = (1/k)·P(u ∈ U_{j+1})·(1/2) ≥ (1/L)·2^{-J}·(1/2) ≥ 3/L^2` … As `m·3/L^2 ≥ 3L^4 ≥ 12`,
observation (B) gives `P(|C^j_w| < 6) ≤ e^{-3L^4/8}`."

(Observation (B) is used in its Chernoff form: the lower tail of `EG.FinDist.IndepEvents` at
`δ = 1/2` with the mean bound `∑ P(I_u = 1) ≥ 3L^4`.)
-/

public section

namespace EG

namespace TPVProb

open Finset FinDist VortexLaw

variable {V : Type*} [DecidableEq V]

/-- The joint label law of a TPV run: colouring and vertex labels, independent. -/
@[expose] noncomputable def runLaw (O : FGraph V) (Z : Finset V) (J : ℕ) :
    FinDist ((O.edges → Fin (3 * J + 1)) × (Z → Fin (J + 1) × Fin 4)) :=
  (randColouring O.edges (3 * J + 1)).prod (labLaw Z J)

/-- The probability that a vertex `u ∈ Z` lies in `Z_j`. -/
theorem prob_mem_Zr {Z P : Finset V} {J j : ℕ} (hj : j + 1 ≤ J) {u : V} (hu : u ∈ Z) :
    (labLaw Z J).prob {lab | u ∈ TPVRun.Zr Z P (levOf lab) (kapOf lab) j} =
      (if u ∈ P then (1 / 2 : ℝ) ^ (j + 1) else 1) * (1 / 2) := by
  have e : {lab : Z → Fin (J + 1) × Fin 4 | u ∈ TPVRun.Zr Z P (levOf lab) (kapOf lab) j} =
      {lab | lab ⟨u, hu⟩ ∈ {x : Fin (J + 1) × Fin 4 |
        x.1 ∈ {i : Fin (J + 1) | u ∉ P ∨ j + 1 ≤ (i : ℕ)} ∧ x.2 ∈ {y : Fin 4 | y = 0}}} := by
    ext lab
    simp [TPVRun.Zr, TPVRun.U, levOf_of_mem lab hu, kapOf_of_mem lab hu, hu]
  rw [e, labLaw, prob_pi_eval, vLaw_prob_rect, kapLaw_zero]
  congr 1
  by_cases hP : u ∈ P
  · rw [if_pos hP]
    have : {i : Fin (J + 1) | u ∉ P ∨ j + 1 ≤ (i : ℕ)} = {i : Fin (J + 1) | j + 1 ≤ (i : ℕ)} := by
      ext i; simp [hP]
    rw [this, levLaw_tail hj]
  · rw [if_neg hP]
    have : {i : Fin (J + 1) | u ∉ P ∨ j + 1 ≤ (i : ℕ)} = Set.univ := by
      ext i; simp [hP]
    rw [this, prob_univ]

/-- [s4:lemTPV] proof, item (G4), for one pair `(w, j)`. -/
theorem G4_single {Z P : Finset V} {O : FGraph V} {J j : ℕ} (hj : j + 1 ≤ J) {w : V}
    {A : Finset V} (hA : ∀ u ∈ A, s(w, u) ∈ O.edges ∧ u ∈ Z)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card) (hJ : 6 * (2 : ℝ) ^ J ≤ Vortex.L Z.card)
    (hk : ((3 * J + 1 : ℕ) : ℝ) ≤ Vortex.L Z.card)
    (hm : Vortex.L Z.card ^ 6 ≤ (A.card : ℝ)) :
    (runLaw O Z J).prob {ω | (A.filter fun u => s(w, u) ∈ Mof ω.1 ∧
      u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j).card < 6} ≤
      Real.exp (-(3 * Vortex.L Z.card ^ 4 / 8)) := by
  classical
  set L := Vortex.L Z.card with hLdef
  set k := 3 * J + 1 with hkdef
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  let Au : V → Set (O.edges → Fin k) := fun u => {χ | s(w, u) ∈ Mof χ}
  let Bu : V → Set (Z → Fin (J + 1) × Fin 4) :=
    fun u => {lab | u ∈ TPVRun.Zr Z P (levOf lab) (kapOf lab) j}
  -- independence
  have hIndA : (randColouring O.edges k).IndepEvents A Au := by
    refine indepEvents_pi_of_dependsOn (fun _ : O.edges => uniform (Fin k)) A
      (fun u => {e : O.edges | (e : Sym2 V) = s(w, u)}) ?_ Au ?_
    · intro u _ v _ huv
      rw [Set.disjoint_left]
      intro e he he'
      simp only [Set.mem_ofPred_eq] at he he'
      exact huv (Sym2.congr_right.1 (he.symm.trans he'))
    · intro u _ f g hfg hf
      simp only [Au, Set.mem_ofPred_eq, mem_Mof] at hf ⊢
      obtain ⟨h, hf⟩ := hf
      refine ⟨h, ?_⟩
      rw [← hfg ⟨s(w, u), h⟩ rfl]
      exact hf
  have hIndB : (labLaw Z J).IndepEvents A Bu := by
    refine indepEvents_pi_of_dependsOn (fun _ : Z => vLaw J) A
      (fun u => {a : Z | (a : V) = u}) ?_ Bu ?_
    · intro u _ v _ huv
      rw [Set.disjoint_left]
      intro a ha ha'
      simp only [Set.mem_ofPred_eq] at ha ha'
      exact huv (ha.symm.trans ha')
    · intro u hu f g hfg hf
      have huZ := (hA u hu).2
      have hfg' : f ⟨u, huZ⟩ = g ⟨u, huZ⟩ := hfg ⟨u, huZ⟩ rfl
      simp only [Bu, Set.mem_ofPred_eq, TPVRun.Zr, TPVRun.U, Finset.mem_filter] at hf ⊢
      rw [levOf_of_mem f huZ, kapOf_of_mem f huZ] at hf
      rw [levOf_of_mem g huZ, kapOf_of_mem g huZ, ← hfg']
      exact hf
  have hInd := IndepEvents.prod hIndA hIndB
  -- the probabilities
  have hpA : ∀ u ∈ A, (randColouring O.edges k).prob (Au u) = 1 / k := by
    intro u hu
    have h := (hA u hu).1
    have e : Au u = {χ | χ ⟨s(w, u), h⟩ = (0 : Fin k)} := by
      ext χ
      simp only [Au, Set.mem_ofPred_eq, mem_Mof]
      constructor
      · rintro ⟨_, h'⟩; exact Fin.ext h'
      · intro h'; exact ⟨h, by rw [h']; rfl⟩
    rw [e, prob_randColouring_apply]
  have h2J : 6 / L ≤ (1 / 2 : ℝ) ^ J := by
    rw [one_div_pow, div_le_div_iff₀ hLpos (by positivity)]
    linarith
  have hpB : ∀ u ∈ A, 3 / L ≤ (labLaw Z J).prob (Bu u) := by
    intro u hu
    rw [show (labLaw Z J).prob (Bu u) = _ from prob_mem_Zr hj (hA u hu).2]
    have hJj : (1 / 2 : ℝ) ^ J ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have h1 : (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : 3 / L = 6 / L * (1 / 2) := by ring
    rw [this]
    split_ifs
    · exact mul_le_mul_of_nonneg_right (h2J.trans hJj) (by norm_num)
    · exact mul_le_mul_of_nonneg_right (h2J.trans h1) (by norm_num)
  have hkpos : (0 : ℝ) < k := by positivity
  have hpI : ∀ u ∈ A, 3 / L ^ 2 ≤ (runLaw O Z J).prob (Au u ×ˢ Bu u) := by
    intro u hu
    rw [runLaw, prob_prod_set_prod, hpA u hu]
    have hB := hpB u hu
    have : 3 / L ^ 2 = 1 / L * (3 / L) := by field_simp
    rw [this]
    refine mul_le_mul ?_ hB (by positivity) (by positivity)
    rw [div_le_div_iff₀ hLpos hkpos]
    linarith
  have hsum : 3 * L ^ 4 ≤ ∑ u ∈ A, (runLaw O Z J).prob (Au u ×ˢ Bu u) := by
    have h1 := Finset.sum_le_sum hpI
    rw [sum_const, nsmul_eq_mul] at h1
    refine le_trans ?_ h1
    have hL2 : 0 < L ^ 2 := by positivity
    rw [mul_div_assoc']
    rw [le_div_iff₀ hL2]
    nlinarith
  -- Chernoff
  have hch := IndepEvents.chernoff_lower_half hInd
    (X := fun ω => ((A.filter fun u => s(w, u) ∈ Mof ω.1 ∧
      u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j).card : ℝ))
    (fun ω _ => by
      rw [sum_indicator_one_eq_card A _ ω (fun u => s(w, u) ∈ Mof ω.1 ∧
        u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j)]
      intro u _
      simp [Au, Bu, Set.mem_prod])
    (by positivity) hsum
  refine le_trans (prob_mono _ fun ω hω => ?_) hch
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have h6 : ((A.filter fun u => s(w, u) ∈ Mof ω.1 ∧
      u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j).card : ℝ) < 6 := by exact_mod_cast hω
  have hL4 : (2 : ℝ) ^ 10 ≤ L ^ 4 := by
    have : (1 : ℝ) ≤ L := by linarith [show (1 : ℝ) ≤ 2 ^ 10 by norm_num]
    nlinarith [pow_le_pow_left₀ (by norm_num) this 3]
  have hfin : ((A.filter fun u => s(w, u) ∈ Mof ω.1 ∧
      u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) j).card : ℝ) < 3 * L ^ 4 / 2 := by linarith
  exact hfin

end TPVProb

end EG
