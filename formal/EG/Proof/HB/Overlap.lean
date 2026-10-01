module

public import EG.Spec.HB.Overlap
public import EG.Lib.HB.OVPotential
public import EG.Lib.Found.Constants

/-!
# Proof of Lemma OV (manuscript s2:lemOVgeneric)

Unit P3A, proof round 1. Design note `formal/work/p2b/P3A.md`. The potential argument is in
`EG.Lib.HB.OVPotential`.

* `EG.ov : EG.Spec.OVStatement` ((a) sharp, the identity, (b) and its consequence, (c));
* `EG.ovInstance : EG.Spec.OVInstanceStatement` (the instance `c = 1`, the `s = 0` recursion).
-/

public section

namespace EG

open EG.HB EG.HB.STree

/-- [s2:lemOVgeneric] (a), (b), (c) and the identity `Σ_v dup_{≥M}(v) = Δ_{≥M}`. -/
theorem ov : EG.Spec.OVStatement := by
  intro V _ H t c hc h342 _ ht
  have hε : (0 : ℝ) ≤ epsC := epsC_pos.le
  refine ⟨fun M hM => ⟨?_, ?_⟩, fun M _ => sum_dupGe M t ht.1, fun M _ v => ov_b M t H v,
    fun M _ => ov_b_sum M t ht.1, ?_⟩
  · exact ov_a hc.le hε hM t ht
  · have hC : ovC M ≤ 3.42 / Real.logb 2 M := ovC_le hM
    have hce : 0 ≤ c * epsC * t.leafMass H :=
      mul_nonneg (mul_nonneg hc.le hε) (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left hC hce
    calc c * epsC * (1 / Real.logb 2 M ^ 2 + 1 / (cOV * Real.logb 2 M)) * t.leafMass H
        = c * epsC * t.leafMass H * ovC M := by unfold ovC; ring
      _ ≤ c * epsC * t.leafMass H * (3.42 / Real.logb 2 M) := this
      _ = 3.42 * c * epsC * t.leafMass H / Real.logb 2 M := by ring
  · have h342' : 3.42 * c * epsC < 1 := h342
    exact ov_c hc.le hε h342' ht

namespace HB

variable {V : Type*} [DecidableEq V]

/-- The second child of the B-M split: `H \ U - E(H[U ∪ N]) = H[V(H) \ U] - E(H[N])`. -/
theorem bm_second_child (K : FGraph V) (U N : Finset V) :
    (K.deleteVerts U).deleteEdges (K.induce (U ∪ N)).edges =
      (K.induce (K.verts \ U)).deleteEdges (K.induce N).edges := by
  apply FGraph.ext
  · simp only [FGraph.deleteEdges_verts, FGraph.deleteVerts_verts, FGraph.induce_verts]
    exact (Finset.inter_eq_right.2 Finset.sdiff_subset).symm
  · ext e
    simp only [FGraph.deleteEdges_edges, Finset.mem_sdiff, FGraph.deleteVerts,
      FGraph.mem_induce_edges]
    constructor
    · rintro ⟨⟨he, hv⟩, hn⟩
      refine ⟨⟨he, hv⟩, fun h => hn ⟨he, fun v hve => Finset.mem_union_right _ (h.2 v hve)⟩⟩
    · rintro ⟨⟨he, hv⟩, hn⟩
      refine ⟨⟨he, hv⟩, fun h => hn ⟨he, fun v hve => ?_⟩⟩
      rcases Finset.mem_union.1 (h.2 v hve) with h' | h'
      · exact absurd h' (hv v hve).2
      · exact h'

/-- At `N = Nbr_K(U)` nothing leaves `U ∪ N` from `U`: `F_0 = ∅`. -/
theorem witF0_nbrSet (K : FGraph V) (U : Finset V) : witF0 K U (K.nbrSet U) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  obtain ⟨he, a, ha, b, hb, rfl⟩ := FGraph.mem_edgesBetween.1 he
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hb
  exact hb.2.2 (FGraph.mem_nbrSet.2 ⟨hb.1, hb.2.1, a, ha, he⟩)

/-- The `τ`-rules at `τ > 0` with `F_0 = ∅` are idle. -/
theorem tau_idle {K : FGraph V} {U N : Finset V} {τ : ℝ} (hτ : 0 < τ) (h0 : witF0 K U N = ∅) :
    tauHout K U N τ = ∅ ∧ tauU1 K U N τ = U ∧ tauN1 K U N τ = N ∧ tauF1 K U N τ = ∅ ∧
      tauHin K U N τ = ∅ ∧ tauN2 K U N τ = N := by
  have hout : tauHout K U N τ = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    have := (Finset.mem_filter.1 hv).2
    rw [h0] at this
    simp [degE, edgesAt] at this
    linarith
  have hF1 : tauF1 K U N τ = ∅ := Finset.subset_empty.1 (h0 ▸ tauF1_subset_witF0 K U N τ)
  have hin : tauHin K U N τ = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    have := (Finset.mem_filter.1 hv).2
    rw [hF1] at this
    simp [degE, edgesAt] at this
    linarith
  refine ⟨hout, ?_, ?_, hF1, hin, ?_⟩
  · simp [tauU1, hout]
  · simp [tauN1, hout]
  · simp [tauN2, tauN1, hout, hin]

end HB

/-- [s2:lemOVgeneric] (Instance `c = 1`, the `s = 0` recursion): the three formulas, the idle
`τ`-rules, and "every `s = 0` recursion satisfies the hypotheses with `c = 1`; hence its total
leaf size is at most `n_0/(1 - 3.42ε) ≤ 1.12 n_0`." -/
theorem ovInstance : EG.Spec.OVInstanceStatement := by
  intro V _ H t ht
  have hε := epsC_eq
  refine ⟨fun a ha K U N F hK hw hN hlab => ?_, fun τ hτ => ?_, ?_, ?_, ?_⟩
  · have hF : F = ∅ := HB.eq_empty_of_isWitness_zero hw
    subst hF
    have hU : t.labelU a = U := labelU_of_labelAt hlab
    have hNl : t.labelN a = N := labelN_of_labelAt hlab
    refine ⟨rfl, by rw [hN]; simp [witN], ?_, ?_, HB.bm_second_child K U N,
      delAt_eq_empty_of_isS0Rec ht ha, fun τ hτ => ?_⟩
    · rw [graphAtD_append_false ha, hU, hNl, ← hK]
      rfl
    · rw [graphAtD_append_true ha, hU, hNl, ← hK, HB.bm_second_child]
      rfl
    · have h0 : witF0 K U N = ∅ := by rw [hN]; exact HB.witF0_nbrSet K U
      obtain ⟨h1, h2, -, -, h5, h6⟩ := HB.tau_idle hτ h0
      exact ⟨h0, h1, h5, h2, h6⟩
  · refine ⟨ht.1, fun a ha => ?_⟩
    obtain ⟨U, F, hw, hlab⟩ := ht.2 a ha
    have hF : F = ∅ := HB.eq_empty_of_isWitness_zero hw
    subst hF
    have hwN : witN (t.graphAtD H a) U ∅ = (t.graphAtD H a).nbrSet U := by simp [witN]
    obtain ⟨-, h2, -, -, -, h6⟩ := HB.tau_idle (N := (t.graphAtD H a).nbrSet U) hτ
      (HB.witF0_nbrSet _ U)
    refine ⟨0, U, ∅, hτ, hw, ?_⟩
    rw [hwN, h2, h6]
    exact hlab
  · refine ⟨ht.1, fun a ha => ?_⟩
    obtain ⟨U, F, hw, hlab⟩ := ht.2 a ha
    have hF : F = ∅ := HB.eq_empty_of_isWitness_zero hw
    subst hF
    set K := t.graphAtD H a with hK
    have hU : t.labelU a = U := labelU_of_labelAt hlab
    have hNl : t.labelN a = K.nbrSet U := labelN_of_labelAt hlab
    have h2 := HB.two_le_card_of_isWitness hw
    obtain ⟨hUK, -, h1, h23, -, hNb⟩ := hw
    simp only [FGraph.deleteEdges_empty] at hNb
    have hL : 1 ≤ Real.logb 2 K.card := one_le_logb_of_two_le (by exact_mod_cast h2)
    have hL2 : 1 ≤ Real.logb 2 K.card ^ 2 := by nlinarith
    have hNε : ((K.nbrSet U).card : ℝ) ≤ epsC * U.card := by
      have : epsC * U.card / Real.logb 2 K.card ^ 2 ≤ epsC * U.card :=
        div_le_self (mul_nonneg epsC_pos.le (Nat.cast_nonneg _)) hL2
      linarith
    refine ⟨h2, ?_, ?_⟩
    · rw [graphAtD_append_false ha, hU, hNl, card_splitFst hUK (K.nbrSet_subset_verts U)]
      have hc : ((U ∪ K.nbrSet U).card : ℝ) ≤ U.card + (K.nbrSet U).card := by
        exact_mod_cast Finset.card_union_le _ _
      rw [hε] at hNε
      have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
      nlinarith
    · rw [hU, hNl]
      rw [one_mul]
      exact hNb.le
  · have hovh : t.OVHyp epsC 1 H := by
      -- the same argument as the previous bullet, restated for `ov_c`
      refine ⟨ht.1, fun a ha => ?_⟩
      obtain ⟨U, F, hw, hlab⟩ := ht.2 a ha
      have hF : F = ∅ := HB.eq_empty_of_isWitness_zero hw
      subst hF
      set K := t.graphAtD H a with hK
      have hU : t.labelU a = U := labelU_of_labelAt hlab
      have hNl : t.labelN a = K.nbrSet U := labelN_of_labelAt hlab
      have h2 := HB.two_le_card_of_isWitness hw
      obtain ⟨hUK, -, h1, h23, -, hNb⟩ := hw
      simp only [FGraph.deleteEdges_empty] at hNb
      have hL : 1 ≤ Real.logb 2 K.card := one_le_logb_of_two_le (by exact_mod_cast h2)
      have hL2 : 1 ≤ Real.logb 2 K.card ^ 2 := by nlinarith
      have hNε : ((K.nbrSet U).card : ℝ) ≤ epsC * U.card := by
        have : epsC * U.card / Real.logb 2 K.card ^ 2 ≤ epsC * U.card :=
          div_le_self (mul_nonneg epsC_pos.le (Nat.cast_nonneg _)) hL2
        linarith
      refine ⟨h2, ?_, ?_⟩
      · rw [graphAtD_append_false ha, hU, hNl, card_splitFst hUK (K.nbrSet_subset_verts U)]
        have hc : ((U ∪ K.nbrSet U).card : ℝ) ≤ U.card + (K.nbrSet U).card := by
          exact_mod_cast Finset.card_union_le _ _
        rw [hε] at hNε
        have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
        nlinarith
      · rw [hU, hNl, one_mul]
        exact hNb.le
    have := ov_c (c := 1) (by norm_num) epsC_pos.le (by rw [hε]; norm_num) hovh
    simpa using this
  · rw [hε, div_le_iff₀ (by norm_num)]
    have : (0 : ℝ) ≤ H.card := Nat.cast_nonneg _
    nlinarith

end EG
