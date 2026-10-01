module

public import EG.Spec.HB.DegRec
public import EG.Lib.HB.Params
public import EG.Proof.Todo.DegRecKindsRound

/-!
# P3 stub: `EG.Spec.DegRecRoundStatement` (s2:propDegRec)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.DegRecRound`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propDegRec] see `EG.Spec.DegRecRoundStatement`. -/
theorem DegRecRound : EG.Spec.DegRecRoundStatement := by
  classical
  intro V _ H c Dstar hD hdD hv
  have h := EG.HB.ParamHyp.of_gamma hD hdD
  have hG2 := hD.gamma2a
  have hd : (2 : ℝ) ^ 117 ≤ EG.HB.Round.d H := le_trans hG2 hdD
  have hn1 : (1 : ℝ) ≤ H.card := by
    rcases Nat.eq_zero_or_pos H.card with h0 | h0
    · exfalso
      have : EG.HB.Round.d H = 0 := by unfold EG.HB.Round.d; rw [h0]; simp
      rw [this] at hd; linarith [show (0 : ℝ) < 2 ^ 117 by positivity]
    · exact_mod_cast h0
  obtain ⟨hkind, -, hA, hB, hC, -⟩ := EG.Todo.DegRecKindsRound V H c Dstar hG2 hdD hv
  obtain ⟨-, hS, -⟩ := EG.Todo.OVRound V H c Dstar hG2 hdD hv
  set P := EG.HB.POf (EG.HB.Round.d H) with hPdef
  set s := EG.HB.sOf (EG.HB.Round.d H) with hsdef
  set Λ := Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ) with hΛ
  set T := EG.HB.Round.twoLevel H c with hT
  -- the three kinds
  set A := (EG.HB.Round.bigPieceAddrs H c).biUnion
    (fun q => (c.tauRun q).deleted (EG.HB.Round.piece H c q)) with hAdef
  set Bs := T.leafAddrs.filter (fun b => (EG.HB.Round.X0 H c b).card < P) with hBs
  set Cs := (EG.HB.Round.prePartAddrs H c).filter (fun a => EG.HB.Round.isLight H c a) with hCs
  set B := Bs.biUnion (fun b => (EG.HB.Round.X0 H c b).edges) with hBdef
  set C := Cs.biUnion (fun a => (EG.HB.Round.X0 H c a).edges.filter
    (fun e => ∃ v ∈ EG.HB.Round.guests H c a, v ∈ e)) with hCdef
  have hsub : (EG.HB.Round.next H c).edges ⊆ A ∪ B ∪ C := by
    intro e he
    rcases hkind e he with ⟨q, hq, heq⟩ | ⟨b, hb, hsm, heb⟩ | ⟨a, ha, hla, hea, hg⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨q, hq, heq⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨b, Finset.mem_filter.2 ⟨hb, hsm⟩, heb⟩))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, Finset.mem_filter.2 ⟨ha, hla⟩,
        Finset.mem_filter.2 ⟨hea, hg⟩⟩)
  have hcardE : ((EG.HB.Round.next H c).edges.card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (A ∪ B) C
    have h3 := Finset.card_union_le A B
    have : (EG.HB.Round.next H c).edges.card ≤ A.card + B.card + C.card := by omega
    exact_mod_cast this
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  have hsP : (s : ℝ) ≤ P := by exact_mod_cast h.s_le_P
  have hBc : (B.card : ℝ) ≤ ∑ b ∈ Bs, ((EG.HB.Round.X0 H c b).card : ℝ) * P / 2 := by
    have h1 : (B.card : ℝ) ≤ ∑ b ∈ Bs, ((EG.HB.Round.X0 H c b).edges.card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine h1.trans (Finset.sum_le_sum fun b hb => ?_)
    have := hB b (Finset.mem_filter.1 hb).1 (Finset.mem_filter.1 hb).2
    linarith
  have hCc : (C.card : ℝ) ≤ ∑ a ∈ Cs, ((EG.HB.Round.Z0 H c a).card : ℝ) * P / 2 := by
    have h1 : (C.card : ℝ) ≤ ∑ a ∈ Cs, ((((EG.HB.Round.X0 H c a).edges.filter
        (fun e => ∃ v ∈ EG.HB.Round.guests H c a, v ∈ e)).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine h1.trans (Finset.sum_le_sum fun a ha => ?_)
    have h2 := hC a (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 ha).2
    have hz : (0 : ℝ) ≤ (EG.HB.Round.Z0 H c a).card := Nat.cast_nonneg _
    have : ((EG.HB.Round.Z0 H c a).card : ℝ) * (s : ℝ) / 2 ≤
        ((EG.HB.Round.Z0 H c a).card : ℝ) * P / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hsP hz
    linarith
  -- small leaves and light pre-parts are distinct leaves
  have hmass : ∑ b ∈ Bs, ((EG.HB.Round.X0 H c b).card : ℝ) +
      ∑ a ∈ Cs, ((EG.HB.Round.Z0 H c a).card : ℝ) ≤ 1.21 * (H.card : ℝ) := by
    have hdisj : Disjoint Bs Cs := by
      rw [Finset.disjoint_left]
      intro b hb hc
      have h1 := (Finset.mem_filter.1 hb).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_filter.1 hc).1).2
      change P ≤ (EG.HB.Round.X0 H c b).card at h2
      omega
    have hsubs : Bs ∪ Cs ⊆ T.leafAddrs := Finset.union_subset (Finset.filter_subset _ _)
      ((Finset.filter_subset _ _).trans (EG.HB.Round.prePartAddrs_subset_leafAddrs H c))
    have h1 : ∑ b ∈ Bs ∪ Cs, ((EG.HB.Round.X0 H c b).card : ℝ) ≤
        ((T.leafMass (EG.HB.Round.graph' H c) : ℕ) : ℝ) := by
      unfold EG.HB.STree.leafMass
      push_cast
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubs (fun _ _ _ => Nat.cast_nonneg _)
    rw [Finset.sum_union hdisj] at h1
    have : ∑ a ∈ Cs, ((EG.HB.Round.Z0 H c a).card : ℝ) =
        ∑ a ∈ Cs, ((EG.HB.Round.X0 H c a).card : ℝ) := rfl
    linarith
  have hB2 : (B.card : ℝ) + (C.card : ℝ) ≤ 1.21 * (H.card : ℝ) * P / 2 := by
    have e1 : ∑ b ∈ Bs, ((EG.HB.Round.X0 H c b).card : ℝ) * P / 2 =
        (∑ b ∈ Bs, ((EG.HB.Round.X0 H c b).card : ℝ)) * P / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
    have e2 : ∑ a ∈ Cs, ((EG.HB.Round.Z0 H c a).card : ℝ) * P / 2 =
        (∑ a ∈ Cs, ((EG.HB.Round.Z0 H c a).card : ℝ)) * P / 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
    rw [e1] at hBc; rw [e2] at hCc
    nlinarith
  -- `d_{l+1} ≤ 1.21 P + 9 s log M`
  have hnext : EG.HB.Round.d (EG.HB.Round.next H c) ≤ 1.21 * (P : ℝ) + 9 * (s : ℝ) * Λ := by
    have hcard : (EG.HB.Round.next H c).card = H.card := rfl
    unfold EG.HB.Round.d
    rw [hcard, div_le_iff₀ (by linarith)]
    have hAc : (A.card : ℝ) ≤ 4.5 * (H.card : ℝ) * (s : ℝ) * Λ := hA
    nlinarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  refine ⟨h.M_le_sq, h.Lam_le_two_lam, h.s_le_P, hnext, ?_, h.final_bound,
    h.seven_le_pow_A, h.pow_A_lt_d⟩
  have : (0 : ℝ) ≤ 4.79 * P := mul_nonneg (by norm_num) hP0
  nlinarith

end EG.Todo
