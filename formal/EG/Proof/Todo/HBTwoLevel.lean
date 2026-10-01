module

public import EG.Spec.HB.HBtpFacts
public import EG.Lib.HB.Run

/-!
# P3 stub: `EG.Spec.HBTwoLevelStatement` (s2:defHBtp)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.HBTwoLevel`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:defHBtp] see `EG.Spec.HBTwoLevelStatement`. -/
theorem HBTwoLevel : EG.Spec.HBTwoLevelStatement := by
  intro V _ H c
  open EG.HB in
  have hsmall : ∀ q ∈ Round.pieceAddrs c, (Round.piece H c q).card < POf (Round.d H) →
      Round.X0 H c q = Round.piece H c q := by
    intro q hq hs
    have h := Round.X0_append H c hq []
    rw [List.append_nil, if_neg (not_le.2 hs), STree.graphAtD_nil] at h
    exact h
  refine ⟨fun a => ?_, hsmall, fun q hq b _ => EG.HB.Round.X0_append_of_mem_bigPieceAddrs H c hq b,
    fun a => ?_⟩
  · unfold EG.HB.Round.twoLevel
    rw [EG.HB.STree.mem_leafAddrs_graft]
    constructor
    · rintro ⟨q, hq, b, hb, rfl⟩
      by_cases hbig : EG.HB.POf (EG.HB.Round.d H) ≤ (EG.HB.Round.piece H c q).card
      · rw [if_pos hbig] at hb
        exact Or.inr ⟨q, (EG.HB.Round.mem_bigPieceAddrs H c).2 ⟨hq, hbig⟩, b, hb, rfl⟩
      · rw [if_neg hbig] at hb
        simp only [EG.HB.STree.leafAddrs_nil, Finset.mem_singleton] at hb
        subst hb
        rw [List.append_nil]
        exact Or.inl ⟨hq, not_le.1 hbig⟩
    · rintro (⟨hq, hs⟩ | ⟨q, hq, b, hb, rfl⟩)
      · refine ⟨a, hq, [], ?_, (List.append_nil a).symm⟩
        rw [if_neg (not_le.2 hs)]; simp
      · have hq' := (EG.HB.Round.mem_bigPieceAddrs H c).1 hq
        exact ⟨q, hq'.1, b, by rw [if_pos hq'.2]; exact hb, rfl⟩
  · constructor
    · intro ha
      have hP := (Finset.mem_filter.1 ha).2
      obtain ⟨hq, b, hb, hab, hX⟩ := EG.HB.Round.exists_tauRun_leaf_of_mem_prePartAddrs H c ha
      refine ⟨_, hq, b, hb, hab, ?_⟩
      rw [← hX]; exact hP
    · rintro ⟨q, hq, b, hb, rfl, hP⟩
      exact EG.HB.Round.append_mem_prePartAddrs H c hq hb hP

end EG.Todo
