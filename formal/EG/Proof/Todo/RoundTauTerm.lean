module

public import EG.Spec.HB.Exists
public import EG.Lib.HB.CapAux
public import EG.Proof.HB.Cap
public import EG.Proof.HB.Lemma14Tau

/-!
# P3 stub: `EG.Spec.RoundTauTermStatement` (s2:propExists)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RoundTauTerm`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propExists] see `EG.Spec.RoundTauTermStatement`. -/
theorem RoundTauTerm : EG.Spec.RoundTauTermStatement := by
  intro V _ H c Dstar hD hdD hcyc hs0 hstop q hq
  have hd : (2 : ℝ) ^ 117 ≤ EG.HB.Round.d H := le_trans hD hdD
  have hT := EG.HB.T_ge_of_d_ge hd
  have hq' := (EG.HB.Round.mem_bigPieceAddrs H c).1 hq
  -- the piece has at most `M_l` vertices (s2:lemCap (ii))
  have hpiece : (EG.HB.Round.piece H c q).card ≤ EG.HB.MOf (EG.HB.Round.d H) := by
    have hM40 := EG.HB.ParamHyp.two40_le_M (d := EG.HB.Round.d H)
    by_cases hsmall : ((EG.HB.Round.piece H c q).card : ℝ) < 2 ^ 40
    · have : ((EG.HB.Round.piece H c q).card : ℝ) ≤ EG.HB.MOf (EG.HB.Round.d H) := by linarith
      exact_mod_cast this
    push Not at hsmall
    have hexp : (EG.HB.Round.piece H c q).IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 :=
      (hstop q (EG.HB.STree.leafAddrs_subset_nodeAddrs _ hq'.1)).1 hq'.1
    have hcyc' : ∀ cyc : List V, (EG.Obj.cycle cyc).WF →
        (∀ e ∈ EG.cycleEdges cyc, e ∈ (EG.HB.Round.piece H c q).edges) →
        (cyc.length : ℝ) < EG.HB.TOf (EG.HB.Round.d H) :=
      fun cyc hwf hce => hcyc.2.2 cyc hwf (fun e he =>
        EG.HB.STree.graphAtD_edges_subset _ _ _ (hce e he))
    have h := EG.cap_graph V (EG.HB.Round.piece H c q) _ hT hsmall hexp hcyc'
    have h2 : 2 ^ 16 * EG.HB.TOf (EG.HB.Round.d H) *
        Real.logb 2 (EG.HB.TOf (EG.HB.Round.d H)) ^ 4 ≤ (EG.HB.MOf (EG.HB.Round.d H) : ℝ) :=
      (le_max_right _ _).trans (Nat.le_ceil _)
    exact_mod_cast h.trans h2
  have hs1 := EG.HB.one_le_sOf (EG.HB.Round.d H)
  have hτ := EG.HB.tau_ge_of_card_le (EG.HB.Round.d H) hpiece
  have hterm := EG.l14Term V (EG.HB.Round.piece H c q) _ _ hs1 hτ
  refine ⟨hs1, hτ, fun K U N F h2 hle hw hN => ?_, hterm.2⟩
  obtain ⟨-, hlt1, -, hlt2⟩ := hterm.1 K U N F h2 hle hw hN
  have hτK : 128 * (EG.HB.sOf (EG.HB.Round.d H) : ℝ) * Real.logb 2 (K.card : ℝ) ^ 2 ≤
      (EG.HB.tauOf (EG.HB.Round.d H) : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (EG.HB.logb_sq_natCast_mono hle) (by positivity)) hτ
  have hU := (EG.HB.l14_split hw hs1 hτK).2.2.2.2.2.2.1
  subst hN
  exact ⟨hU, hlt1, hlt2⟩

end EG.Todo
