module

public import EG.Spec.HB.OVRun
public import EG.Lib.HB.OVRound
public import EG.Lib.HB.CapAux
public import EG.Proof.Todo.CapRound
public import EG.Proof.HB.Lemma14Tau
public import EG.Proof.HB.Overlap

/-!
# P3 stub: `EG.Spec.OVRoundStatement` (s2:propOV)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.OVRound`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propOV] see `EG.Spec.OVRoundStatement`. -/
theorem OVRound : EG.Spec.OVRoundStatement := by
  classical
  intro V _ H c Dstar hD hdD hv
  have hd : (2 : ℝ) ^ 117 ≤ EG.HB.Round.d H := le_trans hD hdD
  have hε := EG.epsC_eq
  have hεp := EG.epsC_pos
  -- `n ≥ 1`
  have hn1 : (1 : ℝ) ≤ H.card := by
    rcases Nat.eq_zero_or_pos H.card with h0 | h0
    · exfalso
      have : EG.HB.Round.d H = 0 := by unfold EG.HB.Round.d; rw [h0]; simp
      rw [this] at hd; linarith [show (0 : ℝ) < 2 ^ 117 by positivity]
    · exact_mod_cast h0
  have hn0 : (0 : ℝ) ≤ H.card := by linarith
  have hcard' : (EG.HB.Round.graph' H c).card = H.card := rfl
  have hP11 := EG.HB.eleven_le_POf hd
  have hP2 : (2 : ℝ) ≤ (EG.HB.POf (EG.HB.Round.d H) : ℝ) := by
    have : (11 : ℝ) ≤ EG.HB.POf (EG.HB.Round.d H) := by exact_mod_cast hP11
    linarith
  have hlogP : 1 ≤ Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ) :=
    EG.HB.one_le_logb_of_two_le hP2
  -- the first level: an `s = 0` recursion
  obtain ⟨-, -, hOV1, hS0, hS0'⟩ := EG.ovInstance V (EG.HB.Round.graph' H c) c.tree0 hv.2.1
  -- the two-level recursion satisfies the hypotheses of Lemma OV with `c = 1.6`
  obtain ⟨-, -, hτ, hs1, -⟩ := EG.Todo.CapRound V H c Dstar hD hdD hv
  have hOV : (EG.HB.Round.twoLevel H c).OVHyp EG.epsC 1.6 (EG.HB.Round.graph' H c) := by
    unfold EG.HB.Round.twoLevel
    refine EG.HB.STree.ovHyp_graft ⟨hOV1.1, fun a ha => ⟨(hOV1.2 a ha).1, (hOV1.2 a ha).2.1,
      le_trans (hOV1.2 a ha).2.2 ?_⟩⟩ ?_
    · apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ EG.epsC * ((c.tree0.labelU a).card : ℝ) := by positivity
      nlinarith
    · intro a ha
      by_cases hbig : EG.HB.POf (EG.HB.Round.d H) ≤ (EG.HB.Round.piece H c a).card
      · simp only [if_pos hbig]
        exact (EG.l14OV V (EG.HB.Round.piece H c a) _ _ _ hs1 (hτ a ha)
          (hv.2.2.2.1 a ha hbig)).2.1
      · simp only [if_neg hbig]
        exact ⟨EG.HB.STree.wf_nil _, by simp⟩
  have hS : ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) ≤
      1.21 * H.card := by
    have h := EG.HB.STree.ov_c (c := 1.6) (by norm_num) hεp.le (by rw [hε]; norm_num) hOV
    rw [hcard'] at h
    refine h.trans ?_
    rw [hε, div_le_iff₀ (by norm_num)]; nlinarith
  have hΔ : ∀ M : ℝ, 2 ≤ M →
      (((EG.HB.Round.twoLevel H c).DeltaGe (EG.HB.Round.graph' H c) M : ℕ) : ℝ) ≤
        5.46 * EG.epsC *
          (((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℕ) : ℝ) /
            Real.logb 2 M := by
    intro M hM
    have ha := EG.HB.STree.ov_a (c := 1.6) (by norm_num) hεp.le hM _ hOV
    have hC := EG.HB.ovC_le_sharp hM
    have hL := EG.HB.one_le_logb_of_two_le hM
    have hSn : (0 : ℝ) ≤ (EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) :=
      Nat.cast_nonneg _
    have h1 : 1.6 * EG.epsC * EG.HB.ovC M *
          ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) ≤
        1.6 * EG.epsC * (58 / 17 / Real.logb 2 M) *
          ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hSn
      exact mul_le_mul_of_nonneg_left hC (by positivity)
    have h2 : 1.6 * EG.epsC * (58 / 17 / Real.logb 2 M) *
          ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) ≤
        5.46 * EG.epsC *
          ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) / Real.logb 2 M := by
      rw [show 1.6 * EG.epsC * (58 / 17 / Real.logb 2 M) *
          ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) =
        (1.6 * (58 / 17)) * EG.epsC *
          ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) / Real.logb 2 M by
        ring]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ EG.epsC *
          ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) := by positivity
      nlinarith
    linarith
  have hΔn : ∀ M : ℝ, 2 ≤ M →
      5.46 * EG.epsC *
          (((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℕ) : ℝ) /
            Real.logb 2 M ≤ 6.61 * EG.epsC * (H.card : ℝ) / Real.logb 2 M := by
    intro M hM
    have hL := EG.HB.one_le_logb_of_two_le hM
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  -- `Δ_{≥P} ≤ 6.61 ε n / log P`
  have hΔP := (hΔ _ hP2).trans (hΔn _ hP2)
  have hmu := EG.HB.Round.sum_mu_sub_one_le H c hv
  have hmuR : ((∑ w ∈ H.verts, (EG.HB.Round.mu H c w - 1) : ℕ) : ℝ) ≤
      6.61 * EG.epsC * (H.card : ℝ) / Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ) :=
    le_trans (by exact_mod_cast hmu) hΔP
  have hZ := EG.HB.Round.sum_Z0_le_leafMass H c
  have hZR : ((∑ a ∈ EG.HB.Round.prePartAddrs H c, (EG.HB.Round.Z0 H c a).card : ℕ) : ℝ) ≤
      1.37 * H.card := by
    have : ((∑ a ∈ EG.HB.Round.prePartAddrs H c, (EG.HB.Round.Z0 H c a).card : ℕ) : ℝ) ≤
        ((EG.HB.Round.twoLevel H c).leafMass (EG.HB.Round.graph' H c) : ℝ) := by
      exact_mod_cast hZ
    linarith
  have hPpos : (0 : ℝ) < EG.HB.POf (EG.HB.Round.d H) := by linarith
  have hPp : ((EG.HB.Round.prePartAddrs H c).card : ℝ) ≤
      1.37 * (H.card : ℝ) / (EG.HB.POf (EG.HB.Round.d H) : ℝ) := by
    rw [le_div_iff₀ hPpos]
    have := EG.HB.Round.card_mul_P_le H c
    have : ((EG.HB.Round.prePartAddrs H c).card : ℝ) * (EG.HB.POf (EG.HB.Round.d H) : ℝ) ≤
        ((∑ a ∈ EG.HB.Round.prePartAddrs H c, (EG.HB.Round.Z0 H c a).card : ℕ) : ℝ) := by
      exact_mod_cast this
    linarith
  have hStd : ((EG.HB.Round.Std H c).card : ℝ) ≤ (EG.HB.Round.prePartAddrs H c).card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hlogPpos : 0 < Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ) := by linarith
  have hεn : 0 ≤ EG.epsC * (H.card : ℝ) := by positivity
  have hD2 := EG.HB.Round.sum_inter_D_le H c
  have hfail := EG.HB.Round.sum_failL1_le H c
  have hdupS := EG.HB.Round.sum_inter_DupStar_le H c hv
  refine ⟨?_, hS, fun M hM => ⟨hΔ M hM, hΔn M hM⟩, hZR, hStd.trans hPp, hPp,
    EG.HB.Round.card_D_le H c, ?_, ?_, hD2, ?_, ?_, ?_, EG.HB.Round.sum_mult_eq H c, ?_,
    EG.HB.Round.mult_le_mu H c⟩
  · rw [← hcard']; exact hS0.trans hS0'
  · refine hmuR.trans ?_
    apply div_le_div_of_nonneg_right _ hlogPpos.le; nlinarith
  · exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  · push_cast
    have : 2 * (6.61 * EG.epsC * (H.card : ℝ) / Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ)) ≤
        15.2 * EG.epsC * (H.card : ℝ) / Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hlogPpos]; nlinarith
    push_cast at hmuR
    linarith
  · have h1 : ((∑ a ∈ (EG.HB.Round.prePartAddrs H c).filter (fun a => ¬ EG.HB.Round.isL1 H c a),
        (EG.HB.Round.Z0 H c a).card : ℕ) : ℝ) ≤
        4 * ((∑ w ∈ H.verts, (EG.HB.Round.mu H c w - 1) : ℕ) : ℝ) := by
      have := hfail.trans (Nat.mul_le_mul_left 2 hD2)
      have h' : ((∑ a ∈ (EG.HB.Round.prePartAddrs H c).filter
          (fun a => ¬ EG.HB.Round.isL1 H c a), (EG.HB.Round.Z0 H c a).card : ℕ) : ℝ) ≤
          ((2 * (2 * ∑ w ∈ H.verts, (EG.HB.Round.mu H c w - 1)) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h' ⊢; linarith
    have : 4 * (6.61 * EG.epsC * (H.card : ℝ) / Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ)) ≤
        30.4 * EG.epsC * (H.card : ℝ) / Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hlogPpos]; nlinarith
    linarith
  · have h1 : ((∑ a ∈ EG.HB.Round.prePartAddrs H c,
        (EG.HB.Round.Z0 H c a ∩ EG.HB.Round.DupStar H c).card : ℕ) : ℝ) ≤
        2 * (((EG.HB.Round.twoLevel H c).DeltaGe (EG.HB.Round.graph' H c)
          (EG.HB.POf (EG.HB.Round.d H) : ℝ) : ℕ) : ℝ) := by
      exact_mod_cast hdupS
    have : 2 * (6.61 * EG.epsC * (H.card : ℝ) / Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ)) ≤
        16 * EG.epsC * (H.card : ℝ) / Real.logb 2 (EG.HB.POf (EG.HB.Round.d H) : ℝ) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hlogPpos]; nlinarith
    linarith
  · have := EG.HB.Round.sum_partVerts_le H c
    have : ((∑ a ∈ EG.HB.Round.prePartAddrs H c, (EG.HB.Round.partVerts H c a).card : ℕ) : ℝ) ≤
        ((∑ a ∈ EG.HB.Round.prePartAddrs H c, (EG.HB.Round.Z0 H c a).card : ℕ) : ℝ) := by
      exact_mod_cast this
    linarith

end EG.Todo
