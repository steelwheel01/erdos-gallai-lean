module

public import EG.Spec.HB.DegRec
public import EG.Lib.HB.DegRecAux
public import EG.Lib.HB.SEP
public import EG.Proof.Todo.CapRound
public import EG.Proof.Todo.OVRound
public import EG.Proof.Todo.HBTwoLevel
public import EG.Proof.HB.Lemma14Tau

/-!
# P3 stub: `EG.Spec.DegRecKindsRoundStatement` (s2:propDegRec)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.DegRecKindsRound`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propDegRec] see `EG.Spec.DegRecKindsRoundStatement`. -/
theorem DegRecKindsRound : EG.Spec.DegRecKindsRoundStatement := by
  classical
  intro V _ H c Dstar hD hdD hv
  have hd : (2 : ℝ) ^ 117 ≤ EG.HB.Round.d H := le_trans hD hdD
  -- `n ≥ 1`
  have hn1 : (1 : ℝ) ≤ H.card := by
    rcases Nat.eq_zero_or_pos H.card with h0 | h0
    · exfalso
      have : EG.HB.Round.d H = 0 := by unfold EG.HB.Round.d; rw [h0]; simp
      rw [this] at hd; linarith [show (0 : ℝ) < 2 ^ 117 by positivity]
    · exact_mod_cast h0
  obtain ⟨hpiece, -, hτ, hs1, hIsTau⟩ := EG.Todo.CapRound V H c Dstar hD hdD hv
  obtain ⟨hS0, -⟩ := EG.Todo.OVRound V H c Dstar hD hdD hv
  obtain ⟨hTL1, hTL2, hTL3, -⟩ := EG.Todo.HBTwoLevel V H c
  -- all pieces and all leaves are non-empty
  have hG'ne : (EG.HB.Round.graph' H c).verts.Nonempty := by
    rw [← Finset.card_pos]; change 0 < H.card; exact_mod_cast (show (0 : ℝ) < H.card by linarith)
  have hpiece_ne : ∀ q ∈ EG.HB.Round.pieceAddrs c, (EG.HB.Round.piece H c q).verts.Nonempty :=
    fun q hq => EG.HB.STree.verts_nonempty c.tree0 _ hv.2.1.1 hG'ne
      (fun a ha => EG.HB.STree.split_nonempty_of_isS0Rec hv.2.1 ha) q
      (EG.HB.STree.leafAddrs_subset_nodeAddrs _ hq)
  have htau_ne : ∀ q ∈ EG.HB.Round.bigPieceAddrs H c, ∀ b ∈ (c.tauRun q).leafAddrs,
      ((c.tauRun q).graphAtD (EG.HB.Round.piece H c q) b).verts.Nonempty := by
    intro q hq b hb
    have hq' := (EG.HB.Round.mem_bigPieceAddrs H c).1 hq
    have ht := hIsTau q hq
    refine EG.HB.STree.verts_nonempty _ _ ht.1 (hpiece_ne q hq'.1) (fun a ha =>
      EG.HB.STree.split_nonempty_of_isTauRun ht (fun a' ha' => ?_) ha) b
      (EG.HB.STree.leafAddrs_subset_nodeAddrs _ hb)
    obtain ⟨U, F, hw, hl⟩ := ht.2.2 a' ha'
    have h := (EG.l14Split V _ _ _ _ hs1 (hτ q hq'.1) ht a' ha' _ U _ F rfl hw rfl hl).2.2.2.2.2.2.1
    rw [EG.HB.STree.labelU_of_labelAt hl]
    exact Finset.card_pos.1 h
  have hleaf_ne : ∀ b ∈ (EG.HB.Round.twoLevel H c).leafAddrs, 1 ≤ (EG.HB.Round.X0 H c b).card := by
    intro b hb
    rcases (hTL1 b).1 hb with ⟨hq, hsmall⟩ | ⟨q, hq, b', hb', rfl⟩
    · rw [hTL2 b hq hsmall]
      exact Finset.card_pos.2 (hpiece_ne b hq)
    · rw [hTL3 q hq b' hb']
      exact Finset.card_pos.2 (htau_ne q hq b' hb')
  have hlog0 : ∀ q ∈ EG.HB.Round.pieceAddrs c,
      0 ≤ Real.logb 2 ((EG.HB.Round.piece H c q).card : ℝ) ∧
      Real.logb 2 ((EG.HB.Round.piece H c q).card : ℝ) ≤
        Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ) := by
    intro q hq
    have h1 : (1 : ℝ) ≤ (EG.HB.Round.piece H c q).card := by
      exact_mod_cast Finset.card_pos.2 (hpiece_ne q hq)
    exact ⟨Real.logb_nonneg (by norm_num) h1, Real.logb_le_logb_of_le (by norm_num) (by linarith)
      (by exact_mod_cast hpiece q hq)⟩
  have hdel : ∀ q ∈ EG.HB.Round.bigPieceAddrs H c,
      (((c.tauRun q).deleted (EG.HB.Round.piece H c q)).card : ℝ) ≤
        4 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) * ((EG.HB.Round.piece H c q).card : ℝ) *
          Real.logb 2 ((EG.HB.Round.piece H c q).card : ℝ) := by
    intro q hq
    have hq' := (EG.HB.Round.mem_bigPieceAddrs H c).1 hq
    exact (EG.l14Global V _ _ _ _ hs1 (hτ q hq'.1) (hIsTau q hq)).1
  refine ⟨?_, hdel, ?_, ?_, ?_, ?_⟩
  · -- the classification
    intro e he
    have hp : e ∈ EG.HB.Round.passed H c := he
    rw [EG.HB.Round.mem_passed] at hp
    obtain ⟨heG', hnone⟩ := hp
    have hcount := EG.HB.STree.sep_count (EG.HB.Round.twoLevel H c) heG'
    by_cases hdelC : 0 < ((EG.HB.Round.twoLevel H c).internalAddrs.filter
        (fun a => e ∈ (EG.HB.Round.twoLevel H c).delAt (EG.HB.Round.graph' H c) a)).card
    · -- kind (a)
      left
      obtain ⟨a, ha⟩ := Finset.card_pos.1 hdelC
      rw [Finset.mem_filter] at ha
      have hmem : e ∈ (EG.HB.Round.twoLevel H c).deleted (EG.HB.Round.graph' H c) :=
        EG.HB.STree.mem_deleted_iff.2 ⟨a, ha.1, ha.2⟩
      rw [EG.HB.Round.deleted_twoLevel H c hv.2.1, Finset.mem_biUnion] at hmem
      exact hmem
    · right
      have hL : 0 < ((EG.HB.Round.twoLevel H c).leafAddrs.filter (fun L =>
          e ∈ ((EG.HB.Round.twoLevel H c).graphAtD (EG.HB.Round.graph' H c) L).edges)).card := by
        omega
      obtain ⟨L, hLm⟩ := Finset.card_pos.1 hL
      rw [Finset.mem_filter] at hLm
      have heX : e ∈ (EG.HB.Round.X0 H c L).edges := hLm.2
      by_cases hsmall : (EG.HB.Round.X0 H c L).card < EG.HB.POf (EG.HB.Round.d H)
      · exact Or.inl ⟨L, hLm.1, hsmall, heX⟩
      · right
        have hLP : L ∈ EG.HB.Round.prePartAddrs H c :=
          Finset.mem_filter.2 ⟨hLm.1, not_lt.1 hsmall⟩
        by_cases hlight : EG.HB.Round.isLight H c L
        · refine ⟨L, hLP, hlight, heX, ?_⟩
          by_contra hno
          push Not at hno
          have heXZ := EG.HB.Round.mem_X_edges H c heX hno
          rw [← EG.HB.Round.partGraph_of_isLight H c hlight] at heXZ
          exact EG.HB.Round.assign_ne_none_of_mem_partGraph H c hv hLP heXZ hnone
        · exfalso
          rw [← EG.HB.Round.partGraph_of_not_isLight H c hlight] at heX
          exact EG.HB.Round.assign_ne_none_of_mem_partGraph H c hv hLP heX hnone
  · -- the total count of kind (a)
    have hsum : ((((EG.HB.Round.bigPieceAddrs H c).biUnion
        (fun q => (c.tauRun q).deleted (EG.HB.Round.piece H c q))).card : ℕ) : ℝ) ≤
        ∑ q ∈ EG.HB.Round.bigPieceAddrs H c,
          (((c.tauRun q).deleted (EG.HB.Round.piece H c q)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hs0 : (0 : ℝ) ≤ EG.HB.sOf (EG.HB.Round.d H) := Nat.cast_nonneg _
    have hLM : 0 ≤ Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ) := by
      have := EG.HB.forty_le_LamOf (EG.HB.Round.d H); change 40 ≤ Real.logb 2 _ at this; linarith
    have hterm : ∀ q ∈ EG.HB.Round.bigPieceAddrs H c,
        (((c.tauRun q).deleted (EG.HB.Round.piece H c q)).card : ℝ) ≤
          (4 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) *
            Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ)) *
            ((EG.HB.Round.piece H c q).card : ℝ) := by
      intro q hq
      have hq' := (EG.HB.Round.mem_bigPieceAddrs H c).1 hq
      obtain ⟨hl0, hl1⟩ := hlog0 q hq'.1
      have hc0 : (0 : ℝ) ≤ (EG.HB.Round.piece H c q).card := Nat.cast_nonneg _
      refine (hdel q hq).trans ?_
      have : 4 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) * ((EG.HB.Round.piece H c q).card : ℝ) *
          Real.logb 2 ((EG.HB.Round.piece H c q).card : ℝ) ≤
          4 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) * ((EG.HB.Round.piece H c q).card : ℝ) *
          Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ) :=
        mul_le_mul_of_nonneg_left hl1 (by positivity)
      linarith
    have hmass : ∑ q ∈ EG.HB.Round.bigPieceAddrs H c, ((EG.HB.Round.piece H c q).card : ℝ) ≤
        ((c.tree0.leafMass (EG.HB.Round.graph' H c) : ℕ) : ℝ) := by
      unfold EG.HB.STree.leafMass
      push_cast
      exact Finset.sum_le_sum_of_subset_of_nonneg (EG.HB.Round.bigPieceAddrs_subset H c)
        (fun _ _ _ => Nat.cast_nonneg _)
    calc _ ≤ _ := hsum
      _ ≤ ∑ q ∈ EG.HB.Round.bigPieceAddrs H c, (4 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) *
            Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ)) *
            ((EG.HB.Round.piece H c q).card : ℝ) := Finset.sum_le_sum hterm
      _ = (4 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) *
            Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ)) *
            ∑ q ∈ EG.HB.Round.bigPieceAddrs H c, ((EG.HB.Round.piece H c q).card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (4 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) *
            Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ)) * (1.12 * (H.card : ℝ)) :=
          mul_le_mul_of_nonneg_left (hmass.trans hS0) (by positivity)
      _ ≤ 4.5 * (H.card : ℝ) * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) *
            Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ) := by
          have : (0 : ℝ) ≤ (EG.HB.sOf (EG.HB.Round.d H) : ℝ) *
              Real.logb 2 (EG.HB.MOf (EG.HB.Round.d H) : ℝ) * H.card := by positivity
          nlinarith
  · intro b hb hsmall
    exact EG.HB.two_card_edges_lt _ (hleaf_ne b hb) hsmall
  · intro a _ hl
    exact EG.HB.Round.card_guestEdges_le H c hl.2.1
  · intro a ha
    rw [Finset.disjoint_left]
    intro e heX hen
    have hp : e ∈ EG.HB.Round.passed H c := hen
    rw [EG.HB.Round.mem_passed] at hp
    have haP : a ∈ EG.HB.Round.prePartAddrs H c := (EG.HB.Round.mem_Std H c).1 ha |>.1
    have hnl : ¬ EG.HB.Round.isLight H c a := (EG.HB.Round.mem_Std H c).1 ha |>.2
    rw [← EG.HB.Round.partGraph_of_not_isLight H c hnl] at heX
    exact EG.HB.Round.assign_ne_none_of_mem_partGraph H c hv haP heX hp.2

end EG.Todo
