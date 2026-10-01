module

public import EG.Lib.Vortex.TPVProbG4
public import EG.Proof.Todo.HB

/-!
# The good event of the TPV run is non-empty (manuscript s4:lemTPV, proof, "Parameters",
"Good events" (G1), (G2), (G4), (G5), and (s4:eqTPVprob))

Unit P3-s4. `EG.TPVProb.exists_good`: under the hypotheses of Lemma TPV there are labels in the
good event `𝒢_TPV = (G1) ∩ (G2) ∩ (G4) ∩ (G5)`, with the family `A(w)` of Lemma HB; their
deterministic consequences are the hypotheses of `EG.TPVRun.core`. The probability bound is the
manuscript's: `P(𝒢_TPV) ≥ 1/2 − η_TPV(N) ≥ 1/2 − 1/100 > 0` (`(G5)` has probability at least
`1/2` by Markov's inequality; (G1), (G2), (G4) fail with probability at most `2LN^{-5}`,
`2^{96}L^{31}N^{-3}` and `NLe^{-3L^4/8}`).
-/

public section

namespace EG

namespace TPVProb

open Finset FinDist VortexLaw

variable {V : Type*} [DecidableEq V]

/-! ### Item (G5) -/

theorem prob_le_levOf {Z : Finset V} {J j : ℕ} (hj : j ≤ J) {v : V} (hv : v ∈ Z) :
    (labLaw Z J).prob {lab | j ≤ levOf lab v} = (1 / 2 : ℝ) ^ j := by
  have e : {lab : Z → Fin (J + 1) × Fin 4 | j ≤ levOf lab v} =
      {lab | lab ⟨v, hv⟩ ∈ {x : Fin (J + 1) × Fin 4 |
        x.1 ∈ {i : Fin (J + 1) | j ≤ (i : ℕ)} ∧ x.2 ∈ (Set.univ : Set (Fin 4))}} := by
    ext lab
    simp [levOf_of_mem lab hv]
  rw [e, labLaw, prob_pi_eval, vLaw_prob_rect, levLaw_tail hj, prob_univ, mul_one]

theorem expect_card_levOf {Z P : Finset V} (hPZ : P ⊆ Z) {J j : ℕ} (hj : j ≤ J) :
    (labLaw Z J).expect (fun lab => ((P.filter fun v => j ≤ levOf lab v).card : ℝ)) =
      P.card * (1 / 2 : ℝ) ^ j := by
  classical
  have h := (labLaw Z J).expect_card_filter P (fun v => {lab | j ≤ levOf lab v})
  simp only [Set.mem_ofPred_eq] at h
  rw [h]
  rw [sum_congr rfl fun v hv => prob_le_levOf hj (hPZ hv), sum_const, nsmul_eq_mul]

/-- [s4:lemTPV] proof, item (G5): "`Σ_{j<J} |P ∩ U_j| ≤ 8|P|` and `|P ∩ U_J| ≤ 48|P|/L`" hold
with probability at least `1/2` (Markov's inequality, s1:citMarkov (b)). -/
theorem G5_prob {Z P : Finset V} (hPZ : P ⊆ Z) {J : ℕ} {L : ℝ} (hLpos : 0 < L)
    (hJ : L < 12 * (2 : ℝ) ^ J) :
    1 / 2 ≤ (labLaw Z J).prob {lab |
      (∑ j ∈ range J, ((P.filter fun v => j ≤ levOf lab v).card : ℝ)) ≤ 8 * P.card ∧
      ((P.filter fun v => J ≤ levOf lab v).card : ℝ) ≤ 48 * P.card / L} := by
  classical
  have hM := (labLaw Z J).half_le_prob_le_four_mul_expect_and
    (X₁ := fun lab => ∑ j ∈ range J, ((P.filter fun v => j ≤ levOf lab v).card : ℝ))
    (X₂ := fun lab => ((P.filter fun v => J ≤ levOf lab v).card : ℝ))
    (fun _ => sum_nonneg fun _ _ => by positivity) (fun _ => by positivity)
  refine le_trans hM (prob_mono _ fun lab hlab => ?_)
  simp only [Set.mem_ofPred_eq] at hlab ⊢
  have e1 : (labLaw Z J).expect (fun lab => ∑ j ∈ range J,
      ((P.filter fun v => j ≤ levOf lab v).card : ℝ)) = P.card * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j := by
    rw [expect_sum, mul_sum]
    exact sum_congr rfl fun j hj => expect_card_levOf hPZ (mem_range.1 hj).le
  have e2 := expect_card_levOf (Z := Z) (P := P) hPZ (le_refl J)
  have hg : ∑ j ∈ range J, (1 / 2 : ℝ) ^ j ≤ 2 := by
    have h := geom_sum_half J
    have : ∑ j ∈ range J, (1 / 2 : ℝ) ^ j = 2 * ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [this, h]
    have : (0 : ℝ) ≤ (1 / 2) ^ J := by positivity
    linarith
  have hP0 : (0 : ℝ) ≤ P.card := by positivity
  have h2J : (1 / 2 : ℝ) ^ J ≤ 12 / L := by
    rw [one_div_pow, div_le_div_iff₀ (by positivity) hLpos]
    linarith
  rw [e1] at hlab
  rw [e2] at hlab
  refine ⟨le_trans hlab.1 (by nlinarith), le_trans hlab.2 ?_⟩
  rw [le_div_iff₀ hLpos]
  have : (P.card : ℝ) * (1 / 2) ^ J * L ≤ P.card * 12 := by
    have := mul_le_mul_of_nonneg_left h2J hP0
    rw [mul_div_assoc'] at this
    rw [le_div_iff₀ hLpos] at this
    linarith
  nlinarith

/-! ### Numerics of the run -/

theorem k_le_L {N : ℕ} (h : 6 ≤ Vortex.L N) : ((3 * Vortex.tpvJ N + 1 : ℕ) : ℝ) ≤ Vortex.L N := by
  have hb := (Vortex.tpvJ_bounds h).1
  have hJ : (Vortex.tpvJ N : ℝ) + 1 ≤ (2 : ℝ) ^ Vortex.tpvJ N := by
    have := Nat.lt_two_pow_self (n := Vortex.tpvJ N)
    exact_mod_cast this
  push_cast
  linarith

/-! ### The good labels exist -/

set_option maxHeartbeats 1000000 in
-- the assembly of the four good events and the final numerics are long
/-- [s4:lemTPV] proof, "Good events" and (s4:eqTPVprob): labels in `𝒢_TPV` exist. They are
given with their deterministic consequences, the hypotheses of `EG.TPVRun.core`. -/
theorem exists_good {Z P : Finset V} {O : FGraph V} {εO s : ℝ} (h : Vortex.TPVHyp Z O P εO s) :
    ∃ (J : ℕ) (R : ℕ → Fin 3 → Finset (Sym2 V)) (M : Finset (Sym2 V)) (lev : V → ℕ)
      (kap : V → Fin 4) (A : V → Finset V) (ℓ t : ℝ),
      TPVRun.Good Z P O J R M lev kap A ℓ t ∧
      ∑ i ∈ range J, (P.filter fun v => i ≤ lev v).card ≤ 8 * P.card ∧
      ((P.filter fun v => J ≤ lev v).card : ℝ) ≤ 48 * P.card / Vortex.L Z.card := by
  classical
  obtain ⟨hsize, hOZ, hX, h7, h5, hs, hPZ⟩ := h
  set N := Z.card with hNdef
  set L := Vortex.L N with hLdef
  set J := Vortex.tpvJ N with hJdef
  have hL : (2 : ℝ) ^ 10 ≤ L := hsize.cond_i
  have hN3 : L ^ 3 ≤ (N : ℝ) := hsize.cond_ii
  have hη : Vortex.etaTPV N ≤ 1 / 100 := hsize.cond_iv
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  have hL1 : 1 ≤ L := by linarith [show (1 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hL6 : 6 ≤ L := by linarith [show (6 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hJb := Vortex.tpvJ_bounds hL6
  have hkL := k_le_L hL6
  rw [← hJdef, ← hLdef] at hkL hJb
  have hJL : (J : ℝ) ≤ L := by push_cast at hkL; linarith [show (0 : ℝ) ≤ J by positivity]
  have h3JL : (3 * J : ℝ) ≤ L := by push_cast at hkL; linarith
  have hN2 : 2 ≤ N := hsize.one_lt
  have hNpos : (0 : ℝ) < N := by positivity
  have hOc : O.card = N := by rw [FGraph.card, hOZ]
  have hε1 : εO ≤ 1 := le_trans h5 (by norm_num)
  have hε0 : 0 < εO := lt_of_lt_of_le (by positivity) h7
  have hinvε : 1 / εO ≤ 2 ^ 7 := by
    rw [div_le_iff₀ hε0]
    have : (2 : ℝ) ^ (-7 : ℤ) = 1 / 2 ^ 7 := by norm_num
    rw [this] at h7
    have := mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ 2 ^ 7 by norm_num)
    rw [mul_one_div_cancel (by norm_num)] at this
    linarith
  have hL42 : (1 : ℝ) ≤ L ^ 42 := one_le_pow₀ hL1
  -- Lemma HB
  set m : ℕ := ⌈L ^ 6⌉₊ with hmdef
  have hm6 : L ^ 6 ≤ (m : ℝ) := Nat.le_ceil _
  have hm6' : (m : ℝ) < L ^ 6 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ L ^ 6 := one_le_pow₀ hL1
    exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hms : 2 * (m : ℝ) ≤ s := by
    have h6 : L ^ 6 ≤ L ^ 42 := pow_le_pow_right₀ hL1 (by norm_num)
    have : 2 * (m : ℝ) ≤ 2 * (L ^ 6 + 1) := by linarith
    nlinarith
  obtain ⟨A, hA1, hA2⟩ := EG.Todo.HB V O εO s m hX (by rw [hOc]; exact hN2) h7 hε1 hm1 hms
  rw [hOc] at hA2
  set b : ℕ := ⌈2 * (m : ℝ) * Real.logb 2 (N : ℝ) ^ 2 / εO⌉₊ with hbdef
  have hlogN : Real.logb 2 (N : ℝ) = L := rfl
  have hb : (b : ℝ) + 2 ≤ 2 ^ 10 * L ^ 8 := by
    have h1 : (b : ℝ) < 2 * m * L ^ 2 / εO + 1 := by
      rw [← hlogN]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : 2 * (m : ℝ) * L ^ 2 / εO ≤ 2 ^ 8 * m * L ^ 2 := by
      rw [div_eq_mul_one_div]
      have : 0 ≤ 2 * (m : ℝ) * L ^ 2 := by positivity
      nlinarith
    have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
    have hL8 : L ^ 6 * L ^ 2 = L ^ 8 := by ring
    have hL28 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    have : (2 : ℝ) ^ 8 * m * L ^ 2 ≤ 2 ^ 8 * (L ^ 6 + 1) * L ^ 2 := by nlinarith
    nlinarith
  have hAnb : ∀ w ∈ Z, ∀ u ∈ A w, s(w, u) ∈ O.edges ∧ u ∈ Z := by
    intro w hw u hu
    have := (hA1 w (by rw [hOZ]; exact hw)).1 hu
    simp only [FGraph.nbrs, Finset.mem_filter] at this
    rw [hOZ] at this
    exact ⟨this.2, this.1⟩
  have hAcard : ∀ w ∈ Z, L ^ 6 ≤ ((A w).card : ℝ) := by
    intro w hw
    rw [(hA1 w (by rw [hOZ]; exact hw)).2]
    exact hm6
  -- parameters
  set k : ℕ := 3 * J + 1 with hkdef
  set ℓ : ℝ := (2 : ℝ) ^ 12 * L ^ 4 with hℓdef
  set t : ℝ := (2 : ℝ) ^ 10 * L ^ 8 with htdef
  have hkpos : (0 : ℝ) < k := by positivity
  set μ := runLaw O Z J with hμdef
  -- (G1)
  let G1 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | ∀ i : Fin k, (O.colourClass p.1 i).IsExpander εO (s / (2 * (k : ℝ)))}
  have hs40 : 40 * (k : ℝ) * Real.logb 2 (O.card : ℝ) ≤ s := by
    rw [hOc]
    change 40 * (k : ℝ) * L ≤ s
    have : 40 * (k : ℝ) * L ≤ 40 * L * L := by nlinarith
    have hL2 : L * L ≤ L ^ 42 := by
      rw [← pow_two]; exact pow_le_pow_right₀ hL1 (by norm_num)
    nlinarith
  have hG1 : 1 - 2 * (k : ℝ) * (N : ℝ) ^ (-5 : ℤ) ≤ μ.prob G1 := by
    have := (l15p_prod_fst hε0 hε1 hs40 hX (labLaw Z J)).2
    rw [hOc] at this
    exact this
  -- (G2)
  let G2 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | ∀ j < J, ∀ c : Fin 3, (O.restrictEdges (Rof p.1 j c)).IsPathConnected ℓ t
      (TPVRun.Vc Z P (levOf p.2) (kapOf p.2) j c)}
  have hs145 : (2 : ℝ) ^ 145 * L ^ 41 ≤ s / (2 * (k : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have : (2 : ℝ) ^ 145 * L ^ 41 * (2 * k) ≤ 2 ^ 145 * L ^ 41 * (2 * L) := by
      have : (0 : ℝ) ≤ 2 ^ 145 * L ^ 41 := by positivity
      nlinarith
    have e : (2 : ℝ) ^ 145 * L ^ 41 * (2 * L) = 2 ^ 146 * L ^ 42 := by ring
    have : (2 : ℝ) ^ 146 * L ^ 42 ≤ 2 ^ 150 * L ^ 42 := by
      have : (0 : ℝ) ≤ L ^ 42 := by positivity
      nlinarith
    linarith
  have hB2 : μ.prob (G1 ∩ G2ᶜ) ≤ 3 * J * ((2 : ℝ) ^ 96 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ)) := by
    refine prob_compProd_le_of_forall _ _ fun χ _ => ?_
    by_cases hχ : ∀ i : Fin k, (O.colourClass χ i).IsExpander εO (s / (2 * (k : ℝ)))
    · have hsub : Prod.mk χ ⁻¹' (G1 ∩ G2ᶜ) ⊆ ⋃ p ∈ (range J ×ˢ (univ : Finset (Fin 3))),
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
              (TPVRun.Vc Z P (levOf lab) (kapOf lab) p.1 p.2)} ≤
            (2 : ℝ) ^ 96 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ) := by
        intro p hp
        obtain ⟨hj, _⟩ := Finset.mem_product.1 hp
        have hj' : p.1 < J := Finset.mem_range.1 hj
        have hXe : (O.restrictEdges (Rof χ p.1 p.2)).IsExpander εO (s / (2 * (k : ℝ))) := by
          have := hχ ⟨3 * p.1 + p.2 + 1, by have := p.2.2; omega⟩
          rw [FGraph.colourClass_eq] at this
          rw [Rof_eq χ hj' p.2]
          exact this
        exact G2_class (by omega) p.2 (by rw [FGraph.restrictEdges_verts, hOZ]) h7 hε1 hXe
          hL hN3 hJb.1 hs145
      refine le_trans (sum_le_sum hterm) (le_of_eq ?_)
      rw [sum_const, Finset.card_product, card_range, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    · have : Prod.mk χ ⁻¹' (G1 ∩ G2ᶜ) = ∅ := by
        ext lab
        simp only [Set.mem_preimage, Set.mem_inter_iff, G1,
          Set.mem_empty_iff_false, iff_false, not_and]
        exact fun h' => absurd h' hχ
      rw [this, prob_empty]
      positivity
  -- (G4)
  let G4 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | ∀ j < J, ∀ w ∈ P, 6 ≤ ((A w).filter fun u => s(w, u) ∈ Mof p.1 ∧
      u ∈ TPVRun.Zr Z P (levOf p.2) (kapOf p.2) j).card}
  have hB4 : μ.prob G4ᶜ ≤ P.card * J * Real.exp (-(3 * L ^ 4 / 8)) := by
    have hsub : G4ᶜ ⊆ ⋃ p ∈ P ×ˢ range J,
        {ω : (O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4) | ((A p.1).filter fun u =>
          s(p.1, u) ∈ Mof ω.1 ∧ u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) p.2).card < 6} := by
      intro ω hω
      simp only [Set.mem_compl_iff, G4, Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨j, hj, w, hw, h6⟩ := hω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Finset.mem_product,
        Finset.mem_range]
      exact ⟨(w, j), ⟨hw, hj⟩, h6⟩
    refine le_trans (prob_mono _ hsub) (le_trans (prob_biUnion_le _ _ _) ?_)
    have hterm : ∀ p ∈ P ×ˢ range J, μ.prob
        {ω : (O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4) | ((A p.1).filter fun u =>
          s(p.1, u) ∈ Mof ω.1 ∧ u ∈ TPVRun.Zr Z P (levOf ω.2) (kapOf ω.2) p.2).card < 6} ≤
        Real.exp (-(3 * L ^ 4 / 8)) := by
      intro p hp
      obtain ⟨hw, hj⟩ := Finset.mem_product.1 hp
      have hj' := Finset.mem_range.1 hj
      exact G4_single (by omega) (hAnb p.1 (hPZ hw)) hL hJb.1 hkL (hAcard p.1 (hPZ hw))
    refine le_trans (sum_le_sum hterm) (le_of_eq ?_)
    rw [sum_const, Finset.card_product, card_range, nsmul_eq_mul]
    push_cast
    ring
  -- (G5)
  let G5 : Set ((O.edges → Fin k) × (Z → Fin (J + 1) × Fin 4)) :=
    {p | (∑ j ∈ range J, ((P.filter fun v => j ≤ levOf p.2 v).card : ℝ)) ≤ 8 * P.card ∧
      ((P.filter fun v => J ≤ levOf p.2 v).card : ℝ) ≤ 48 * P.card / L}
  have hG5 : 1 / 2 ≤ μ.prob G5 := by
    have h := G5_prob (Z := Z) (P := P) hPZ hLpos hJb.2
    have e : G5 = Prod.snd ⁻¹' {lab : Z → Fin (J + 1) × Fin 4 |
        (∑ j ∈ range J, ((P.filter fun v => j ≤ levOf lab v).card : ℝ)) ≤ 8 * P.card ∧
        ((P.filter fun v => J ≤ levOf lab v).card : ℝ) ≤ 48 * P.card / L} := rfl
    rw [e, hμdef, runLaw, prob_prod_snd]
    exact h
  -- the good event has positive probability
  have hB1 : μ.prob G1ᶜ ≤ 2 * (k : ℝ) * (N : ℝ) ^ (-5 : ℤ) := by
    rw [prob_compl]; linarith
  have hsub : G5 \ (G1ᶜ ∪ (G1 ∩ G2ᶜ) ∪ G4ᶜ) ⊆ G1 ∩ G2 ∩ G4 ∩ G5 := by
    intro ω hω
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
      not_or, not_and, not_not] at hω
    exact ⟨⟨⟨hω.2.1.1, hω.2.1.2 hω.2.1.1⟩, hω.2.2⟩, hω.1⟩
  have hbad : μ.prob (G1ᶜ ∪ (G1 ∩ G2ᶜ) ∪ G4ᶜ) ≤ Vortex.etaTPV N := by
    refine le_trans (prob_union_le _ _ _) ?_
    refine le_trans (add_le_add (prob_union_le _ _ _) le_rfl) ?_
    have hN5 : (0 : ℝ) ≤ (N : ℝ) ^ (-5 : ℤ) := by positivity
    have hN3' : (0 : ℝ) ≤ (N : ℝ) ^ (-3 : ℤ) := by positivity
    have hexp : 0 ≤ Real.exp (-(3 * L ^ 4 / 8)) := (Real.exp_pos _).le
    have hPN : (P.card : ℝ) ≤ N := by exact_mod_cast Finset.card_le_card hPZ
    have t1 : 2 * (k : ℝ) * (N : ℝ) ^ (-5 : ℤ) ≤ 2 * L * (N : ℝ) ^ (-5 : ℤ) := by nlinarith
    have t2 : 3 * J * ((2 : ℝ) ^ 96 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ)) ≤
        (2 : ℝ) ^ 96 * L ^ 31 * (N : ℝ) ^ (-3 : ℤ) := by
      have : (0 : ℝ) ≤ 2 ^ 96 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ) := by positivity
      have e : (2 : ℝ) ^ 96 * L ^ 31 * (N : ℝ) ^ (-3 : ℤ) =
          L * ((2 : ℝ) ^ 96 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h3JL this
    have t3 : (P.card : ℝ) * J * Real.exp (-(3 * L ^ 4 / 8)) ≤
        N * L * Real.exp (-(3 * L ^ 4 / 8)) := by
      have hJ0 : (0 : ℝ) ≤ J := by positivity
      have : (P.card : ℝ) * J ≤ N * L := mul_le_mul hPN hJL hJ0 (by positivity)
      exact mul_le_mul_of_nonneg_right this hexp
    have e : Vortex.etaTPV N = 2 * L * (N : ℝ) ^ (-5 : ℤ) +
        (2 : ℝ) ^ 96 * L ^ 31 * (N : ℝ) ^ (-3 : ℤ) + N * L * Real.exp (-(3 * L ^ 4 / 8)) := rfl
    rw [e]
    linarith
  have hpos : 0 < μ.prob (G1 ∩ G2 ∩ G4 ∩ G5) := by
    have := μ.prob_diff_ge G5 (G1ᶜ ∪ (G1 ∩ G2ᶜ) ∪ G4ᶜ)
    have := prob_mono μ hsub
    linarith
  obtain ⟨ω, ⟨⟨⟨_, hω2⟩, hω4⟩, hω5⟩, _⟩ := μ.exists_of_prob_pos hpos
  refine ⟨J, Rof ω.1, Mof ω.1, levOf ω.2, kapOf ω.2, A, ℓ, t, ⟨hPZ, hOZ, ?_, ?_, ?_, hω2, hω4,
    ?_⟩, ?_, hω5.2⟩
  · exact Mof_subset ω.1
  · intro j _ j' _ c c' hne
    exact Rof_disjoint ω.1 hne
  · intro j _ c
    exact Rof_disjoint_Mof ω.1 j c
  · intro v
    have h1 : ((Z.filter fun w => v ∈ A w).card : ℝ) ≤ b := by
      have := hA2 v
      rw [hOZ] at this
      exact_mod_cast this
    linarith
  · have h := hω5.1
    have : ((∑ i ∈ range J, (P.filter fun v => i ≤ levOf ω.2 v).card : ℕ) : ℝ) ≤
        ((8 * P.card : ℕ) : ℝ) := by
      push_cast
      exact h
    exact_mod_cast this

end TPVProb

end EG
