module

public import EG.Lib.Vortex.VXProbEvents
public import EG.Lib.Vortex.VXRun

/-!
# The good event of the VX⁺ run is non-empty (manuscript s4:thmVXp, proof, "Parameters",
"Good events" (G1)–(G4), and (s4:eqVXprob))

Unit P3-s4. `EG.VXProb.exists_good`: under the hypotheses of Theorem VX⁺ there are labels in
`𝒢_VX = (G1) ∩ (G2) ∩ (G3) ∩ (G4)`, with the family `A(w)` of Lemma HB (`m = ⌈L^3⌉`); their
deterministic consequences are the hypotheses of `EG.VXRun.core`. The failure probabilities are
the manuscript's: `2LN^{-5}` ((G1), Lemma 15⁺), `2^{95}L^{28}N^{-3}` ((G2), Theorem 16* and (MC)),
`NLe^{-3L^2/(32 log₂ L)}` ((G4)), `Le^{-N/(5000L)}` ((G3)); their sum is `η_VX(N) ≤ 1/100`.

The multiplicity is `t = 8L^5/ε_O` (that is `2^8L^5` for `ε_O = 2^{-5}` and `2^9L^5` for
`ε_O = 2^{-6}`, the manuscript's values).
-/

public section

namespace EG

namespace VXProb

open Finset FinDist VortexLaw TPVProb

variable {V : Type*} [DecidableEq V]

/-- `log₂ L < 2L` for `L ≥ 1`. -/
theorem logb_lt_two_mul {L : ℝ} (hL : 1 ≤ L) : Real.logb 2 L < 2 * L := by
  have h1 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [Real.logb, div_lt_iff₀ (by linarith)]
  nlinarith

/-- `1 ≤ log₂ L` for `L ≥ 2`. -/
theorem one_le_logb {L : ℝ} (hL : 2 ≤ L) : 1 ≤ Real.logb 2 L := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  exact hL

/-- [s4:thmVXp] proof, item (G2), union bound: if every class that is an expander fails (G2)
with probability at most `q` (over the vertex labels), then (G1) holds and (G2) fails with
probability at most `3Jq`. -/
theorem B2 {Z P : Finset V} {O : FGraph V} {J : ℕ} {εO s t : ℝ} (hOZ : O.verts = Z)
    (hε7 : (2 : ℝ) ^ (-7 : ℤ) ≤ εO) (hε1 : εO ≤ 1)
    (hL : (2 : ℝ) ^ 10 ≤ Vortex.L Z.card) (hN3 : Vortex.L Z.card ^ 3 ≤ (Z.card : ℝ))
    (hJ : 6 * (2 : ℝ) ^ J ≤ Vortex.L Z.card) (ht1 : 1 ≤ t)
    (hsT : (2 : ℝ) ^ 135 * t * Vortex.L Z.card ^ 33 ≤ s / (2 * ((3 * J + 1 : ℕ) : ℝ)))
    {q : ℝ} (hq : (2 : ℝ) ^ 86 * t * Vortex.L Z.card ^ 22 * (Z.card : ℝ) ^ (-3 : ℤ) ≤ q) :
    (runLaw O Z J).prob
      ({p | ∀ i : Fin (3 * J + 1), (O.colourClass p.1 i).IsExpander εO
          (s / (2 * ((3 * J + 1 : ℕ) : ℝ)))} ∩
        {p | ∀ j < J, ∀ c : Fin 3, (O.restrictEdges (Rof p.1 j c)).IsPathConnected
          ((2 : ℝ) ^ 12 * Vortex.L Z.card ^ 4) t
          (TPVRun.Vc Z P (levOf p.2) (kapOf p.2) j c)}ᶜ) ≤ 3 * J * q := by
  classical
  set k := 3 * J + 1
  set ℓ := (2 : ℝ) ^ 12 * Vortex.L Z.card ^ 4
  refine prob_compProd_le_of_forall _ _ fun χ _ => ?_
  by_cases hχ : ∀ i : Fin k, (O.colourClass χ i).IsExpander εO (s / (2 * (k : ℝ)))
  · have hsub : Prod.mk χ ⁻¹' ({p : (O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4) |
          ∀ i : Fin k, (O.colourClass p.1 i).IsExpander εO (s / (2 * (k : ℝ)))} ∩
        {p | ∀ j < J, ∀ c : Fin 3, (O.restrictEdges (Rof p.1 j c)).IsPathConnected ℓ t
          (TPVRun.Vc Z P (levOf p.2) (kapOf p.2) j c)}ᶜ) ⊆
        ⋃ p ∈ (range J ×ˢ (univ : Finset (Fin 3))),
        {lab : Z → Fin (J + 1) × Fin 4 | ¬ (O.restrictEdges (Rof χ p.1 p.2)).IsPathConnected ℓ t
          (TPVRun.Vc Z P (levOf lab) (kapOf lab) p.1 p.2)} := by
      intro lab hlab
      have h2 : ¬ ∀ j < J, ∀ c : Fin 3, (O.restrictEdges (Rof χ j c)).IsPathConnected ℓ t
          (TPVRun.Vc Z P (levOf lab) (kapOf lab) j c) := hlab.2
      push Not at h2
      obtain ⟨j, hj, c, hc⟩ := h2
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Finset.mem_product,
        Finset.mem_range, Finset.mem_univ, and_true]
      exact ⟨(j, c), hj, hc⟩
    refine le_trans (prob_mono _ hsub) (le_trans (prob_biUnion_le _ _ _) ?_)
    have hterm : ∀ p ∈ (range J ×ˢ (univ : Finset (Fin 3))),
        (labLaw Z J).prob {lab : Z → Fin (J + 1) × Fin 4 |
          ¬ (O.restrictEdges (Rof χ p.1 p.2)).IsPathConnected ℓ t
            (TPVRun.Vc Z P (levOf lab) (kapOf lab) p.1 p.2)} ≤ q := by
      intro p hp
      obtain ⟨hj, _⟩ := Finset.mem_product.1 hp
      have hj' : p.1 < J := Finset.mem_range.1 hj
      have hXe : (O.restrictEdges (Rof χ p.1 p.2)).IsExpander εO (s / (2 * (k : ℝ))) := by
        have := hχ ⟨3 * p.1 + p.2 + 1, by have := p.2.2; omega⟩
        rw [FGraph.colourClass_eq] at this
        rw [Rof_eq χ hj' p.2]
        exact this
      exact le_trans (G2_class_gen (by omega) p.2 (by rw [FGraph.restrictEdges_verts, hOZ])
        hε7 hε1 hXe hL hN3 hJ ht1 hsT) hq
    refine le_trans (sum_le_sum hterm) (le_of_eq ?_)
    rw [sum_const, Finset.card_product, card_range, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · have : Prod.mk χ ⁻¹' ({p : (O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4) |
          ∀ i : Fin k, (O.colourClass p.1 i).IsExpander εO (s / (2 * (k : ℝ)))} ∩
        {p | ∀ j < J, ∀ c : Fin 3, (O.restrictEdges (Rof p.1 j c)).IsPathConnected ℓ t
          (TPVRun.Vc Z P (levOf p.2) (kapOf p.2) j c)}ᶜ) = ∅ := by
      ext lab
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      exact fun h' => absurd h' hχ
    rw [this, prob_empty]
    have : 0 ≤ q := le_trans (by positivity) hq
    positivity

/-- [s4:thmVXp] proof, item (G4), union bound over the pairs `(w, j)`. -/
theorem B4 {Z : Finset V} {O : FGraph V} {J : ℕ} {A : V → Finset V} {p₀ M₀ : ℝ}
    (hAnb : ∀ w ∈ Z, ∀ u ∈ A w, s(w, u) ∈ O.edges ∧ u ∈ Z)
    (hp : ∀ j, j + 1 ≤ J → ∀ u ∈ Z, p₀ ≤ 1 / ((3 * J + 1 : ℕ) : ℝ) *
      ((if u ∈ Z then (1 / 2 : ℝ) ^ (j + 1) else 1) * (1 / 2)))
    (hM : ∀ w ∈ Z, M₀ ≤ ((A w).card : ℝ) * p₀) (hM0 : 0 ≤ M₀) (ha : 2 * (9 : ℝ) ≤ M₀) :
    (runLaw O Z J).prob {p | ∀ j < J, ∀ w ∈ Z, 9 ≤ ((A w).filter fun u => s(w, u) ∈ Mof p.1 ∧
      u ∈ TPVRun.Zr Z Z (levOf p.2) (kapOf p.2) j).card}ᶜ ≤
      Z.card * J * Real.exp (-(M₀ / 8)) := by
  classical
  have hsub : {p : (O.edges → Fin (3 * J + 1)) × (Z → Fin (J + 1) × Fin 4) |
      ∀ j < J, ∀ w ∈ Z, 9 ≤ ((A w).filter fun u => s(w, u) ∈ Mof p.1 ∧
      u ∈ TPVRun.Zr Z Z (levOf p.2) (kapOf p.2) j).card}ᶜ ⊆ ⋃ p ∈ Z ×ˢ range J,
      {ω : (O.edges → Fin (3 * J + 1)) × (Z → Fin (J + 1) × Fin 4) | ((((A p.1).filter fun u =>
        s(p.1, u) ∈ Mof ω.1 ∧ u ∈ TPVRun.Zr Z Z (levOf ω.2) (kapOf ω.2) p.2).card : ℕ) : ℝ)
          < 9} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨j, hj, w, hw, h9⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Finset.mem_product,
      Finset.mem_range]
    exact ⟨(w, j), ⟨hw, hj⟩, by exact_mod_cast h9⟩
  refine le_trans (prob_mono _ hsub) (le_trans (prob_biUnion_le _ _ _) ?_)
  have hterm : ∀ p ∈ Z ×ˢ range J, (runLaw O Z J).prob
      {ω : (O.edges → Fin (3 * J + 1)) × (Z → Fin (J + 1) × Fin 4) | ((((A p.1).filter fun u =>
        s(p.1, u) ∈ Mof ω.1 ∧ u ∈ TPVRun.Zr Z Z (levOf ω.2) (kapOf ω.2) p.2).card : ℕ) : ℝ)
          < 9} ≤ Real.exp (-(M₀ / 8)) := by
    intro p hpm
    obtain ⟨hw, hj⟩ := Finset.mem_product.1 hpm
    have hj' := Finset.mem_range.1 hj
    exact G4_gen (P := Z) (by omega) (hAnb p.1 hw)
      (fun u hu => hp p.2 (by omega) u (hAnb p.1 hw u hu).2) (hM p.1 hw) hM0 ha
  refine le_trans (sum_le_sum hterm) (le_of_eq ?_)
  rw [sum_const, Finset.card_product, card_range, nsmul_eq_mul]
  push_cast
  ring

/-- [s4:thmVXp] proof, item (G3), union bound over `j ≤ J`. -/
theorem B3 {Z : Finset V} {O : FGraph V} {J : ℕ}
    (hL : (0 : ℝ) < Vortex.L Z.card) (hJ : 6 * (2 : ℝ) ^ J ≤ Vortex.L Z.card) :
    (runLaw O Z J).prob {p | ∀ j ∈ range (J + 1), ((Z.filter fun v => j ≤ levOf p.2 v).card : ℝ)
      < 1.01 * ((1 / 2 : ℝ) ^ j * Z.card)}ᶜ ≤
      (J + 1) * Real.exp (-((Z.card : ℝ) / (5000 * Vortex.L Z.card))) := by
  classical
  have hsub : {p : (O.edges → Fin (3 * J + 1)) × (Z → Fin (J + 1) × Fin 4) |
      ∀ j ∈ range (J + 1), ((Z.filter fun v => j ≤ levOf p.2 v).card : ℝ)
      < 1.01 * ((1 / 2 : ℝ) ^ j * Z.card)}ᶜ ⊆ ⋃ j ∈ range (J + 1),
      Prod.snd ⁻¹' {lab : Z → Fin (J + 1) × Fin 4 | 1.01 * ((1 / 2 : ℝ) ^ j * Z.card) ≤
        ((Z.filter fun v => j ≤ levOf lab v).card : ℝ)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hω
    obtain ⟨j, hj, h⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq, exists_prop]
    exact ⟨j, hj, h⟩
  refine le_trans (prob_mono _ hsub) (le_trans (prob_biUnion_le _ _ _) ?_)
  have hterm : ∀ j ∈ range (J + 1), (runLaw O Z J).prob (Prod.snd ⁻¹'
      {lab : Z → Fin (J + 1) × Fin 4 | 1.01 * ((1 / 2 : ℝ) ^ j * Z.card) ≤
        ((Z.filter fun v => j ≤ levOf lab v).card : ℝ)}) ≤
      Real.exp (-((Z.card : ℝ) / (5000 * Vortex.L Z.card))) := by
    intro j hj
    rw [runLaw, prob_prod_snd]
    exact G3_single (by have := Finset.mem_range.1 hj; omega) hL hJ
  refine le_trans (sum_le_sum hterm) (le_of_eq ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
-- the assembly of the four good events and the final numerics are long
/-- [s4:thmVXp] proof, "Good events" and (s4:eqVXprob): labels in `𝒢_VX` exist, given with
their deterministic consequences (the hypotheses of `EG.VXRun.core`). -/
theorem exists_good {Z : Finset V} {O : FGraph V} {εO s : ℝ} (hsize : Vortex.VXSize Z.card)
    (hOZ : O.verts = Z) (hX : O.IsExpander εO s)
    (hcase : (εO = (2 : ℝ) ^ (-5 : ℤ) ∧
        (2 : ℝ) ^ 146 * Vortex.L Z.card ^ 38 * Real.logb 2 (Vortex.L Z.card) ≤ s) ∨
      (εO = (2 : ℝ) ^ (-6 : ℤ) ∧
        (2 : ℝ) ^ 151 * Vortex.L Z.card ^ 38 * Real.logb 2 (Vortex.L Z.card) ≤ s)) :
    ∃ (J : ℕ) (R : ℕ → Fin 3 → Finset (Sym2 V)) (M : Finset (Sym2 V)) (lev : V → ℕ)
      (kap : V → Fin 4) (A : V → Finset V) (ℓ t : ℝ),
      TPVRun.Good Z Z O J R M lev kap A ℓ t ∧
      (∀ j < J, ∀ w ∈ Z,
        9 ≤ ((A w).filter fun u => s(w, u) ∈ M ∧ u ∈ TPVRun.Zr Z Z lev kap j).card) ∧
      (∀ j < J, ((Z.filter fun v => j ≤ lev v).card : ℝ) ≤ 1.01 * (1 / 2) ^ j * Z.card) ∧
      ((Z.filter fun v => J ≤ lev v).card : ℝ) ≤ 13 * Z.card / Vortex.L Z.card := by
  classical
  set N := Z.card with hNdef
  set L := Vortex.L N with hLdef
  set J := Vortex.tpvJ N with hJdef
  set lam := Real.logb 2 L with hlamdef
  have hL : (2 : ℝ) ^ 10 ≤ L := hsize.cond_i
  have hN3 : L ^ 3 ≤ (N : ℝ) := hsize.cond_ii
  have hη : Vortex.etaVX N ≤ 1 / 100 := hsize.cond_iv
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  have hL1 : 1 ≤ L := by linarith [show (1 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hL6 : 6 ≤ L := by linarith [show (6 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hL48 : 48 ≤ L := by linarith [show (48 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hJb := Vortex.tpvJ_bounds hL6
  have hkL := k_le_L hL6
  rw [← hJdef, ← hLdef] at hkL hJb
  have hJlam : (J : ℝ) ≤ lam := Vortex.tpvJ_le_logb hL6
  have hlam1 : 1 ≤ lam := one_le_logb (by linarith)
  have hlamL : lam < 2 * L := logb_lt_two_mul hL1
  have hlampos : 0 < lam := by linarith
  have hk4 : ((3 * J + 1 : ℕ) : ℝ) ≤ 4 * lam := by push_cast; linarith
  have hJL : (J : ℝ) ≤ L := by push_cast at hkL; linarith [show (0 : ℝ) ≤ J by positivity]
  have h3JL : (3 * J : ℝ) ≤ L := by push_cast at hkL; linarith
  have hJ1L : (J : ℝ) + 1 ≤ L := by push_cast at hkL; linarith [show (0 : ℝ) ≤ J by positivity]
  have hN2 : 2 ≤ N := hsize.one_lt
  have hNpos : (0 : ℝ) < N := by positivity
  have hOc : O.card = N := by rw [FGraph.card, hOZ]
  -- the two regimes
  have hε : (2 : ℝ) ^ (-6 : ℤ) ≤ εO ∧ εO ≤ (2 : ℝ) ^ (-5 : ℤ) ∧
      (2 : ℝ) ^ 141 * L ^ 38 * lam ≤ s * εO := by
    have hL38 : 0 ≤ L ^ 38 * lam := by positivity
    rcases hcase with ⟨rfl, hs⟩ | ⟨rfl, hs⟩
    · refine ⟨by norm_num, le_rfl, ?_⟩
      have e : (2 : ℝ) ^ (-5 : ℤ) = 1 / 2 ^ 5 := by norm_num
      rw [e]
      have : (2 : ℝ) ^ 141 * L ^ 38 * lam = (2 ^ 146 * L ^ 38 * lam) * (1 / 2 ^ 5) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hs (by norm_num)
    · refine ⟨le_rfl, by norm_num, ?_⟩
      have e : (2 : ℝ) ^ (-6 : ℤ) = 1 / 2 ^ 6 := by norm_num
      rw [e]
      have h1 : (2 : ℝ) ^ 141 * L ^ 38 * lam ≤ (2 ^ 151 * L ^ 38 * lam) * (1 / 2 ^ 6) := by
        have : (2 : ℝ) ^ 141 * L ^ 38 * lam * 2 ^ 4 = (2 ^ 151 * L ^ 38 * lam) * (1 / 2 ^ 6) := by
          ring
        rw [← this]
        nlinarith
      exact le_trans h1 (mul_le_mul_of_nonneg_right hs (by norm_num))
  obtain ⟨hε6, hε5, hsε⟩ := hε
  have hε0 : 0 < εO := lt_of_lt_of_le (by positivity) hε6
  have hε1 : εO ≤ 1 := le_trans hε5 (by norm_num)
  have hε7 : (2 : ℝ) ^ (-7 : ℤ) ≤ εO := le_trans (by norm_num) hε6
  have hinvε : 1 / εO ≤ 2 ^ 6 := by
    rw [div_le_iff₀ hε0]
    have : (2 : ℝ) ^ (-6 : ℤ) = 1 / 2 ^ 6 := by norm_num
    rw [this] at hε6
    have := mul_le_mul_of_nonneg_left hε6 (show (0 : ℝ) ≤ 2 ^ 6 by norm_num)
    rw [mul_one_div_cancel (by norm_num)] at this
    linarith
  have hinvε1 : 1 ≤ 1 / εO := by rw [le_div_iff₀ hε0]; linarith
  have hs0 : (2 : ℝ) ^ 141 * L ^ 38 * lam ≤ s := by
    have : s * εO ≤ s := by
      have hs' : 0 ≤ s := by
        have : 0 ≤ (2 : ℝ) ^ 141 * L ^ 38 * lam := by positivity
        by_contra h
        push Not at h
        nlinarith
      nlinarith
    linarith
  have hL38 : (1 : ℝ) ≤ L ^ 38 := one_le_pow₀ hL1
  -- Lemma HB
  set m : ℕ := ⌈L ^ 3⌉₊ with hmdef
  have hm3 : L ^ 3 ≤ (m : ℝ) := Nat.le_ceil _
  have hm3' : (m : ℝ) < L ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
    exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hms : 2 * (m : ℝ) ≤ s := by
    have h3 : L ^ 3 ≤ L ^ 38 := pow_le_pow_right₀ hL1 (by norm_num)
    have : 2 * (m : ℝ) ≤ 2 * (L ^ 3 + 1) := by linarith
    nlinarith
  obtain ⟨A, hA1, hA2⟩ := EG.Todo.HB V O εO s m hX (by rw [hOc]; exact hN2) hε7 hε1 hm1 hms
  rw [hOc] at hA2
  set b : ℕ := ⌈2 * (m : ℝ) * Real.logb 2 (N : ℝ) ^ 2 / εO⌉₊ with hbdef
  have hlogN : Real.logb 2 (N : ℝ) = L := rfl
  set t : ℝ := 8 * L ^ 5 / εO with htdef
  have hb : (b : ℝ) + 2 ≤ t := by
    have h1 : (b : ℝ) < 2 * m * L ^ 2 / εO + 1 := by
      rw [← hlogN]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : 2 * (m : ℝ) * L ^ 2 / εO ≤ 2 * (L ^ 3 + 1) * L ^ 2 / εO := by
      apply div_le_div_of_nonneg_right _ hε0.le
      have : 0 ≤ L ^ 2 := by positivity
      nlinarith
    have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
    have hL25 : L ^ 2 ≤ L ^ 5 := pow_le_pow_right₀ hL1 (by norm_num)
    have hL5 : (1 : ℝ) ≤ L ^ 5 := one_le_pow₀ hL1
    have e1 : 2 * (L ^ 3 + 1) * L ^ 2 / εO = (2 * L ^ 5 + 2 * L ^ 2) * (1 / εO) := by
      ring
    have e2 : t = 8 * L ^ 5 * (1 / εO) := by rw [htdef]; field_simp
    rw [e1] at h2
    rw [e2]
    nlinarith
  have hAnb : ∀ w ∈ Z, ∀ u ∈ A w, s(w, u) ∈ O.edges ∧ u ∈ Z := by
    intro w hw u hu
    have := (hA1 w (by rw [hOZ]; exact hw)).1 hu
    simp only [FGraph.nbrs, Finset.mem_filter] at this
    rw [hOZ] at this
    exact ⟨this.2, this.1⟩
  have hAcard : ∀ w ∈ Z, (A w).card = m := fun w hw => (hA1 w (by rw [hOZ]; exact hw)).2
  -- parameters
  set k : ℕ := 3 * J + 1 with hkdef
  set ℓ : ℝ := (2 : ℝ) ^ 12 * L ^ 4 with hℓdef
  have hkpos : (0 : ℝ) < k := by positivity
  set μ := runLaw O Z J with hμdef
  -- (G1)
  let G1 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | ∀ i : Fin k, (O.colourClass p.1 i).IsExpander εO (s / (2 * (k : ℝ)))}
  have hs40 : 40 * (k : ℝ) * Real.logb 2 (O.card : ℝ) ≤ s := by
    rw [hOc]
    change 40 * (k : ℝ) * L ≤ s
    have : 40 * (k : ℝ) * L ≤ 40 * L * L := by nlinarith
    have hL2 : L * L ≤ L ^ 38 := by
      rw [← pow_two]; exact pow_le_pow_right₀ hL1 (by norm_num)
    have : (2 : ℝ) ^ 141 * L ^ 38 ≤ 2 ^ 141 * L ^ 38 * lam := by nlinarith
    nlinarith
  have hG1 : 1 - 2 * (k : ℝ) * (N : ℝ) ^ (-5 : ℤ) ≤ μ.prob G1 := by
    have := (l15p_prod_fst (ε' := εO) hε0 hε1 hs40 hX (labLaw Z J)).2
    rw [hOc] at this
    exact this
  -- (G2)
  let G2 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | ∀ j < J, ∀ c : Fin 3, (O.restrictEdges (Rof p.1 j c)).IsPathConnected ℓ t
      (TPVRun.Vc Z Z (levOf p.2) (kapOf p.2) j c)}
  have ht1 : (1 : ℝ) ≤ t := by
    have hL5 : (1 : ℝ) ≤ L ^ 5 := one_le_pow₀ hL1
    rw [htdef, le_div_iff₀ hε0]
    nlinarith
  have hsT : (2 : ℝ) ^ 135 * t * L ^ 33 ≤ s / (2 * (k : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have e : (2 : ℝ) ^ 135 * t * L ^ 33 * (2 * k) = 2 ^ 138 * L ^ 38 * (2 * k) / εO := by
      rw [htdef]; field_simp; ring
    rw [e, div_le_iff₀ hε0]
    have : (2 : ℝ) ^ 138 * L ^ 38 * (2 * k) ≤ 2 ^ 138 * L ^ 38 * (8 * lam) := by
      have : (0 : ℝ) ≤ 2 ^ 138 * L ^ 38 := by positivity
      nlinarith
    nlinarith
  have hq : (2 : ℝ) ^ 86 * t * L ^ 22 * (N : ℝ) ^ (-3 : ℤ) ≤
      (2 : ℝ) ^ 95 * L ^ 27 * (N : ℝ) ^ (-3 : ℤ) := by
    have e : (2 : ℝ) ^ 86 * t * L ^ 22 * (N : ℝ) ^ (-3 : ℤ) =
        (2 ^ 89 * L ^ 27 * (N : ℝ) ^ (-3 : ℤ)) * (1 / εO) := by
      rw [htdef]; field_simp; ring
    rw [e]
    have h0 : (0 : ℝ) ≤ 2 ^ 89 * L ^ 27 * (N : ℝ) ^ (-3 : ℤ) := by positivity
    have := mul_le_mul_of_nonneg_left hinvε h0
    linarith
  have hB2 : μ.prob (G1 ∩ G2ᶜ) ≤ 3 * J * ((2 : ℝ) ^ 95 * L ^ 27 * (N : ℝ) ^ (-3 : ℤ)) :=
    B2 (P := Z) hOZ hε7 hε1 hL hN3 hJb.1 ht1 hsT hq
  -- (G4)
  let G4 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | ∀ j < J, ∀ w ∈ Z, 9 ≤ ((A w).filter fun u => s(w, u) ∈ Mof p.1 ∧
      u ∈ TPVRun.Zr Z Z (levOf p.2) (kapOf p.2) j).card}
  have hp0 : ∀ j, j + 1 ≤ J → ∀ u ∈ Z, 3 / (4 * lam * L) ≤ 1 / ((3 * J + 1 : ℕ) : ℝ) *
      ((if u ∈ Z then (1 / 2 : ℝ) ^ (j + 1) else 1) * (1 / 2)) := by
    intro j hj u hu
    rw [if_pos hu]
    have h2J : 6 / L ≤ (1 / 2 : ℝ) ^ (j + 1) := by
      have : (1 / 2 : ℝ) ^ J ≤ (1 / 2 : ℝ) ^ (j + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
      refine le_trans ?_ this
      rw [one_div_pow, div_le_div_iff₀ hLpos (by positivity)]
      linarith
    have hk1 : 1 / (4 * lam) ≤ 1 / ((3 * J + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hk4
    have e : 3 / (4 * lam * L) = 1 / (4 * lam) * (6 / L * (1 / 2)) := by
      field_simp; ring
    rw [e]
    exact mul_le_mul hk1 (mul_le_mul_of_nonneg_right h2J (by norm_num)) (by positivity)
      (by positivity)
  have hB4 : μ.prob G4ᶜ ≤ N * J * Real.exp (-(3 * L ^ 2 / (32 * lam))) := by
    have hM : ∀ w ∈ Z, 3 * L ^ 2 / (4 * lam) ≤ ((A w).card : ℝ) * (3 / (4 * lam * L)) := by
      intro w hw
      rw [hAcard w hw]
      have e : (m : ℝ) * (3 / (4 * lam * L)) = 3 * m / (4 * lam * L) := by ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      have : L ^ 3 * (4 * lam) ≤ m * (4 * lam) :=
        mul_le_mul_of_nonneg_right hm3 (by positivity)
      nlinarith
    have ha : 2 * (9 : ℝ) ≤ 3 * L ^ 2 / (4 * lam) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h := B4 (O := O) (J := J) hAnb hp0 hM (by positivity) ha
    have e : 3 * L ^ 2 / (4 * lam) / 8 = 3 * L ^ 2 / (32 * lam) := by field_simp; ring
    rw [e] at h
    exact h
  -- (G3)
  let G3 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | ∀ j ∈ range (J + 1), ((Z.filter fun v => j ≤ levOf p.2 v).card : ℝ) <
      1.01 * ((1 / 2 : ℝ) ^ j * N)}
  have hB3 : μ.prob G3ᶜ ≤ (J + 1) * Real.exp (-((N : ℝ) / (5000 * L))) :=
    B3 hLpos hJb.1
  -- the good event has positive probability
  have hB1 : μ.prob G1ᶜ ≤ 2 * (k : ℝ) * (N : ℝ) ^ (-5 : ℤ) := by
    rw [prob_compl]; linarith
  have hsub : (G1ᶜ ∪ (G1 ∩ G2ᶜ) ∪ G4ᶜ ∪ G3ᶜ)ᶜ ⊆ G1 ∩ G2 ∩ G4 ∩ G3 := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, not_or, not_and,
      not_not] at hω
    exact ⟨⟨⟨hω.1.1.1, hω.1.1.2 hω.1.1.1⟩, hω.1.2⟩, hω.2⟩
  have hbad : μ.prob (G1ᶜ ∪ (G1 ∩ G2ᶜ) ∪ G4ᶜ ∪ G3ᶜ) ≤ Vortex.etaVX N := by
    refine le_trans (prob_union_le _ _ _) ?_
    refine le_trans (add_le_add (prob_union_le _ _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (prob_union_le _ _ _) le_rfl) le_rfl) ?_
    have hN5 : (0 : ℝ) ≤ (N : ℝ) ^ (-5 : ℤ) := by positivity
    have hN3' : (0 : ℝ) ≤ (N : ℝ) ^ (-3 : ℤ) := by positivity
    have hexp : 0 ≤ Real.exp (-(3 * L ^ 2 / (32 * lam))) := (Real.exp_pos _).le
    have hexp' : 0 ≤ Real.exp (-((N : ℝ) / (5000 * L))) := (Real.exp_pos _).le
    have t1 : 2 * (k : ℝ) * (N : ℝ) ^ (-5 : ℤ) ≤ 2 * L * (N : ℝ) ^ (-5 : ℤ) :=
      mul_le_mul_of_nonneg_right (by linarith) hN5
    have t2 : 3 * J * ((2 : ℝ) ^ 95 * L ^ 27 * (N : ℝ) ^ (-3 : ℤ)) ≤
        (2 : ℝ) ^ 95 * L ^ 28 * (N : ℝ) ^ (-3 : ℤ) := by
      have : (0 : ℝ) ≤ 2 ^ 95 * L ^ 27 * (N : ℝ) ^ (-3 : ℤ) := by positivity
      have e : (2 : ℝ) ^ 95 * L ^ 28 * (N : ℝ) ^ (-3 : ℤ) =
          L * ((2 : ℝ) ^ 95 * L ^ 27 * (N : ℝ) ^ (-3 : ℤ)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h3JL this
    have t3 : (N : ℝ) * J * Real.exp (-(3 * L ^ 2 / (32 * lam))) ≤
        N * L * Real.exp (-(3 * L ^ 2 / (32 * lam))) := by
      have : (N : ℝ) * J ≤ N * L := mul_le_mul_of_nonneg_left hJL hNpos.le
      exact mul_le_mul_of_nonneg_right this hexp
    have t4 : ((J : ℝ) + 1) * Real.exp (-((N : ℝ) / (5000 * L))) ≤
        L * Real.exp (-((N : ℝ) / (5000 * L))) := mul_le_mul_of_nonneg_right hJ1L hexp'
    have e : Vortex.etaVX N = 2 * L * (N : ℝ) ^ (-5 : ℤ) +
        (2 : ℝ) ^ 95 * L ^ 28 * (N : ℝ) ^ (-3 : ℤ) +
        N * L * Real.exp (-(3 * L ^ 2 / (32 * lam))) +
        L * Real.exp (-((N : ℝ) / (5000 * L))) := rfl
    rw [e]
    linarith
  have hpos : 0 < μ.prob (G1 ∩ G2 ∩ G4 ∩ G3) := by
    have h1 := μ.prob_compl (G1ᶜ ∪ (G1 ∩ G2ᶜ) ∪ G4ᶜ ∪ G3ᶜ)
    have h2 := prob_mono μ hsub
    linarith
  obtain ⟨ω, ⟨⟨⟨_, hω2⟩, hω4⟩, hω3⟩, _⟩ := μ.exists_of_prob_pos hpos
  refine ⟨J, Rof ω.1, Mof ω.1, levOf ω.2, kapOf ω.2, A, ℓ, t,
    ⟨subset_refl _, hOZ, Mof_subset ω.1, ?_, ?_, hω2, ?_, ?_⟩, hω4, ?_, ?_⟩
  · intro j _ j' _ c c' hne
    exact Rof_disjoint ω.1 hne
  · intro j _ c
    exact Rof_disjoint_Mof ω.1 j c
  · intro j hj w hw
    exact le_trans (by norm_num) (hω4 j hj w hw)
  · intro v
    have h1 : ((Z.filter fun w => v ∈ A w).card : ℝ) ≤ b := by
      have := hA2 v
      rw [hOZ] at this
      exact_mod_cast this
    linarith
  · intro j hj
    have := hω3 j (Finset.mem_range.2 (by omega))
    linarith
  · have h := hω3 J (Finset.mem_range.2 (by omega))
    have h12 : (1 / 2 : ℝ) ^ J ≤ 12 / L := by
      rw [one_div_pow, div_le_div_iff₀ (by positivity) hLpos]
      linarith
    rw [le_div_iff₀ hLpos]
    have h0 : (1 / 2 : ℝ) ^ J * N ≤ 12 / L * N := mul_le_mul_of_nonneg_right h12 hNpos.le
    have h1 : 1.01 * ((1 / 2 : ℝ) ^ J * N) * L ≤ 1.01 * (12 / L * N) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h0 (by norm_num)) hLpos.le
    have e : 1.01 * (12 / L * N) * L = 12.12 * N := by field_simp; ring
    have h2 : ((Z.filter fun v => J ≤ levOf ω.2 v).card : ℝ) * L ≤
        1.01 * ((1 / 2 : ℝ) ^ J * N) * L := mul_le_mul_of_nonneg_right h.le hLpos.le
    have hN0 : (0 : ℝ) ≤ N := hNpos.le
    linarith

end VXProb

end EG
