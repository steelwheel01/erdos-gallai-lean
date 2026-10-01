module

public import EG.Lib.Vortex.PVProbEvents

/-!
# The good event of the PV run is non-empty (manuscript s4:lemPV, proof, "Parameters",
"Probability of `𝒢_PV`", (s4:eqPVprob))

Unit P3-s4. `EG.PVProb.exists_good`: under the hypotheses of Lemma PV there are labels in the good
event `𝒢_PV = (G2) ∩ (G4) ∩ (G5)`; they are given with their deterministic consequences, the
hypotheses of `EG.PVRun.core`. The probability bound is the manuscript's:
`P(𝒢_PV) ≥ 1/2 − η_PV(N) ≥ 1/2 − 1/100 > 0` ((G5) has probability at least `1/2` by Markov's
inequality; (G2) and (G4) fail with probability at most `4J·2^{95}L^{30}N^{-3} ≤ 2^{95}L^{31}N^{-3}`
and `|Pl|·J·e^{-L^4/16} ≤ NLe^{-L^4/16}`). The multiplicity bound `2 + b ≤ t` of the sets
`A(w)` is (s4:eqPVt) (`EG.pvT`).
-/

public section

namespace EG

namespace PVProb

open Finset FinDist VortexLaw

variable {V : Type*} [DecidableEq V]

set_option maxHeartbeats 1000000 in
-- the assembly of the three good events and the final numerics are long
/-- [s4:lemPV] proof, "Probability of `𝒢_PV`" and (s4:eqPVprob): labels in `𝒢_PV` exist. They
are given with their deterministic consequences, the hypotheses of `EG.PVRun.core`. -/
theorem exists_good {D : Vortex.PVData V} (h : Vortex.PVHyp D) :
    ∃ (lev : V → ℕ) (kap : V → Fin 5),
      PVRun.Good D lev kap ((2 : ℝ) ^ 12 * Vortex.L D.Z.card ^ 4)
        ((2 : ℝ) ^ 9 * Vortex.L D.Z.card ^ 8) ∧
      ∑ i ∈ range (Vortex.pvJ D.Z.card), (D.Pl.filter fun v => i ≤ lev v).card ≤
        8 * D.Pl.card ∧
      ((D.Pl.filter fun v => Vortex.pvJ D.Z.card ≤ lev v).card : ℝ) ≤
        64 * D.Pl.card / Vortex.L D.Z.card := by
  classical
  have h' := h
  obtain ⟨hsize, hOZ, _, _, hHB, hRexp, hMZ, _, hsOwn, _, _, _, hZ, hE1⟩ := h'
  set N := D.Z.card with hNdef
  set L := Vortex.L N with hLdef
  set J := Vortex.pvJ N with hJdef
  have hL : (2 : ℝ) ^ 10 ≤ L := hsize.cond_i
  have hN3 : L ^ 3 ≤ (N : ℝ) := hsize.cond_ii
  have hη : Vortex.etaPV N ≤ 1 / 100 := hsize.cond_iv
  have hLpos : 0 < L := by linarith [show (0 : ℝ) < 2 ^ 10 by norm_num]
  have hL8 : 8 ≤ L := by linarith [show (8 : ℝ) ≤ 2 ^ 10 by norm_num]
  have hJb := Vortex.pvJ_bounds hL8
  rw [← hJdef, ← hLdef] at hJb
  have hJ2 : (J : ℝ) + 1 ≤ (2 : ℝ) ^ J := by
    have := Nat.lt_two_pow_self (n := J)
    exact_mod_cast this
  have h4JL : (4 * J : ℝ) ≤ L := by nlinarith
  have hJL : (J : ℝ) ≤ L := by nlinarith
  have hPlZ : D.Pl ⊆ D.Z := hZ ▸ Finset.subset_union_right
  set ℓ : ℝ := (2 : ℝ) ^ 12 * L ^ 4 with hℓdef
  set t : ℝ := (2 : ℝ) ^ 9 * L ^ 8 with htdef
  set μ := labLaw D.Z J with hμdef
  -- (G2)
  let G2 : Set (D.Z → Fin (J + 1) × Fin 5) :=
    {lab | ∀ i : Fin J × Fin 4, (D.R i).IsPathConnected ℓ t
      (PVRun.Vc D.Z D.Pl (levOf lab) (kapOf lab) i.1 i.2)}
  have hB2 : μ.prob G2ᶜ ≤ 4 * J * ((2 : ℝ) ^ 95 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ)) := by
    have hsub : G2ᶜ ⊆ ⋃ i ∈ (univ : Finset (Fin J × Fin 4)),
        {lab : D.Z → Fin (J + 1) × Fin 5 | ¬ (D.R i).IsPathConnected ℓ t
          (PVRun.Vc D.Z D.Pl (levOf lab) (kapOf lab) i.1 i.2)} := by
      intro lab hlab
      simp only [Set.mem_compl_iff, G2, Set.mem_ofPred_eq, not_forall] at hlab
      obtain ⟨i, hi⟩ := hlab
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Finset.mem_univ, true_and]
      exact ⟨i, hi⟩
    refine le_trans (prob_mono _ hsub) (le_trans (prob_biUnion_le _ _ _) ?_)
    have hterm : ∀ i ∈ (univ : Finset (Fin J × Fin 4)),
        μ.prob {lab : D.Z → Fin (J + 1) × Fin 5 | ¬ (D.R i).IsPathConnected ℓ t
          (PVRun.Vc D.Z D.Pl (levOf lab) (kapOf lab) i.1 i.2)} ≤
          (2 : ℝ) ^ 95 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ) := by
      intro i _
      exact G2_class (by have := i.1.2; omega) i.2 (hRexp i).1 (hRexp i).2 hL hN3 hJb.1 hsOwn
    refine le_trans (sum_le_sum hterm) (le_of_eq ?_)
    rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  -- (G4)
  have hCwZ : ∀ w, PVRun.Cw D w ⊆ D.Z := by
    intro w u hu
    have hM := (Finset.mem_filter.1 hu).2.1
    rw [← hMZ]
    exact D.M.edge_verts _ hM u (Sym2.mem_mk_right _ _)
  let G4 : Set (D.Z → Fin (J + 1) × Fin 5) :=
    {lab | ∀ j < J, ∀ w ∈ D.Pl, 8 ≤ ((PVRun.Cw D w).filter fun u =>
      u ∈ PVRun.Zr D.Z D.Pl (levOf lab) (kapOf lab) j).card}
  have hB4 : μ.prob G4ᶜ ≤ D.Pl.card * J * Real.exp (-(L ^ 4 / 16)) := by
    have hsub : G4ᶜ ⊆ ⋃ p ∈ D.Pl ×ˢ range J,
        {lab : D.Z → Fin (J + 1) × Fin 5 | ((PVRun.Cw D p.1).filter fun u =>
          u ∈ PVRun.Zr D.Z D.Pl (levOf lab) (kapOf lab) p.2).card < 8} := by
      intro lab hlab
      simp only [Set.mem_compl_iff, G4, Set.mem_ofPred_eq, not_forall, not_le] at hlab
      obtain ⟨j, hj, w, hw, h8⟩ := hlab
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, Finset.mem_product,
        Finset.mem_range]
      exact ⟨(w, j), ⟨hw, hj⟩, h8⟩
    refine le_trans (prob_mono _ hsub) (le_trans (prob_biUnion_le _ _ _) ?_)
    have hterm : ∀ p ∈ D.Pl ×ˢ range J, μ.prob
        {lab : D.Z → Fin (J + 1) × Fin 5 | ((PVRun.Cw D p.1).filter fun u =>
          u ∈ PVRun.Zr D.Z D.Pl (levOf lab) (kapOf lab) p.2).card < 8} ≤
        Real.exp (-(L ^ 4 / 16)) := by
      intro p hp
      obtain ⟨hw, hj⟩ := Finset.mem_product.1 hp
      have hj' := Finset.mem_range.1 hj
      exact G4_single (by omega) (hCwZ p.1) hL hJb.1 (hE1 p.1 hw)
    refine le_trans (sum_le_sum hterm) (le_of_eq ?_)
    rw [sum_const, Finset.card_product, card_range, nsmul_eq_mul]
    push_cast
    ring
  -- (G5)
  let G5 : Set (D.Z → Fin (J + 1) × Fin 5) :=
    {lab | (∑ j ∈ range J, ((D.Pl.filter fun v => j ≤ levOf lab v).card : ℝ)) ≤
        8 * D.Pl.card ∧
      ((D.Pl.filter fun v => J ≤ levOf lab v).card : ℝ) ≤ 64 * D.Pl.card / L}
  have hG5 : 1 / 2 ≤ μ.prob G5 := G5_prob hPlZ hLpos hJb.2
  -- the good event has positive probability
  have hsub : G5 \ (G2ᶜ ∪ G4ᶜ) ⊆ G2 ∩ G4 ∩ G5 := by
    intro ω hω
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hω
    exact ⟨⟨hω.2.1, hω.2.2⟩, hω.1⟩
  have hbad : μ.prob (G2ᶜ ∪ G4ᶜ) ≤ Vortex.etaPV N := by
    refine le_trans (prob_union_le _ _ _) ?_
    have hN3' : (0 : ℝ) ≤ (N : ℝ) ^ (-3 : ℤ) := by positivity
    have hexp : 0 ≤ Real.exp (-(L ^ 4 / 16)) := (Real.exp_pos _).le
    have hPN : (D.Pl.card : ℝ) ≤ N := by exact_mod_cast Finset.card_le_card hPlZ
    have t2 : 4 * J * ((2 : ℝ) ^ 95 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ)) ≤
        (2 : ℝ) ^ 95 * L ^ 31 * (N : ℝ) ^ (-3 : ℤ) := by
      have : (0 : ℝ) ≤ 2 ^ 95 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ) := by positivity
      have e : (2 : ℝ) ^ 95 * L ^ 31 * (N : ℝ) ^ (-3 : ℤ) =
          L * ((2 : ℝ) ^ 95 * L ^ 30 * (N : ℝ) ^ (-3 : ℤ)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h4JL this
    have t3 : (D.Pl.card : ℝ) * J * Real.exp (-(L ^ 4 / 16)) ≤
        N * L * Real.exp (-(L ^ 4 / 16)) := by
      have hJ0 : (0 : ℝ) ≤ J := by positivity
      have : (D.Pl.card : ℝ) * J ≤ N * L := mul_le_mul hPN hJL hJ0 (by positivity)
      exact mul_le_mul_of_nonneg_right this hexp
    have e : Vortex.etaPV N = (2 : ℝ) ^ 95 * L ^ 31 * (N : ℝ) ^ (-3 : ℤ) +
        N * L * Real.exp (-(L ^ 4 / 16)) := rfl
    rw [e]
    linarith
  have hpos : 0 < μ.prob (G2 ∩ G4 ∩ G5) := by
    have := μ.prob_diff_ge G5 (G2ᶜ ∪ G4ᶜ)
    have := prob_mono μ hsub
    linarith
  obtain ⟨lab, ⟨⟨hω2, hω4⟩, hω5⟩, _⟩ := μ.exists_of_prob_pos hpos
  refine ⟨levOf lab, kapOf lab, ⟨h, hω2, hω4, fun v => ?_⟩, ?_, hω5.2⟩
  · have h1 : ((D.Z.filter fun w => v ∈ D.A w).card : ℝ) ≤ Vortex.pvB N := by
      have := hHB.2 v
      rw [hOZ] at this
      exact_mod_cast this
    have h2 := EG.pvT N hL
    linarith [h2.1, h2.2]
  · have h5 := hω5.1
    have : ((∑ i ∈ range J, (D.Pl.filter fun v => i ≤ levOf lab v).card : ℕ) : ℝ) ≤
        ((8 * D.Pl.card : ℕ) : ℝ) := by
      push_cast
      exact h5
    exact_mod_cast this

end PVProb

end EG
