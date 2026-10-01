module

public import EG.Spec.Quot.UHsplit
public import EG.Lib.Quot.Copies
public import EG.Lib.Quot.OfPastValid

/-!
# P3 stub: `EG.Spec.UHsplitRoundStatement` (s7:lemUHsplit)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UHsplitRound`; consumers import this module.

Proof (manuscript s7:lemUHsplit (ii)). The past `I = pastOf run G δ ω l J` is a valid round input
(`EG.Quot.pastOf_valid`: Lemma J⁺, s7:lemCand (iv), s2:propStructure (iii)). Then
`EG.Quot.expect_copies_le` (`EG/Lib/Quot/Copies.lean`): the four kinds of vertices of `Q_l` — PAR
copies (s7:lemCC (iii)), copies of non-ultra hubs (s7:lemWellDef (iv), s7:lemMULT: at most `3k_h`),
junction copies in HUB sub-layers (s7:lemMULT: at most `4M_l Σ_w mult_{r(w)}(w)`), copies of ultra
hubs (s7:lemUltra (iv)) — averaged over the lists. The multiplicities read by the round input are
the run's `mult_r(w)` (`EG.Quot.ofPast_multAt`), so the bound is `X_{V,l} + det_l`.
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot Finset

/-- Proved in P3. [s7:lemUHsplit] see `EG.Spec.UHsplitRoundStatement`. -/
theorem UHsplitRound : EG.Spec.UHsplitRoundStatement := by
  intro V _ G N0 Dstar run δ hR hδ ω hω l hl hlR J hJ I hIeq R hRv
  subst hIeq
  have hI := pastOf_valid hω hR hδ hl hlR hJ
  have h := expect_copies_le hI hRv
  have hX : 3 * (pastOf run G δ ω l J).M * (tCC (pastOf run G δ ω l J).M + 1) *
      (pastOf run G δ ω l J).pool.card + 4 * (pastOf run G δ ω l J).M *
      ∑ w ∈ (pastOf run G δ ω l J).pool,
        (pastOf run G δ ω l J).multAt ((pastOf run G δ ω l J).poolRound w) w =
      XVl run G ω.pool l := by
    unfold XVl
    congr 2
    exact sum_congr rfl fun w _ =>
      ofPast_multAt run G δ (stageOf ω) ω.pool l J (Stage1.poolRound ω.pool w) w
  refine h.trans (le_of_eq ?_)
  rw [hX]
  rfl

end EG.Todo
