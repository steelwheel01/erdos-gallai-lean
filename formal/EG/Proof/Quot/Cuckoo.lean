module

public import EG.Spec.Quot.WellDef
public import EG.Lib.Quot.Cuckoo
public import EG.Proof.Num.WellDef
public import EG.Proof.Quot.WellDef

/-!
# Proof of Lemma "The round step is well defined" (iii), the Cuckoo SDR bound
(manuscript s7:lemWellDef (iii)) — probe P-1, proof round 1

Unit P1, design note `formal/work/p2b/P1.md` §5. The probabilistic half is
`EG.Quot.Rules.prob_not_sdr_le` (`EG/Lib/Quot/Cuckoo.lean`: Hall, independence of the lists of
distinct hubs, union bound); the series bound `∑_{s=4}^m T_s ≤ K^{-4}` is the proved
`EG.numWellDefSDRUse` (unit NUM, `EG/Proof/Num/WellDef.lean`); `3k_h ≤ 4M_l` is part (ii),
`EG.wellDefLists`; the move from the round law to the law of the lists is `prob_prod_fst` (the
event reads the lists only).
-/

public section

namespace EG

open EG.Quot

/-- [s7:lemWellDef] (iii) *Cuckoo SDR.* "For every port `u`,
`P(SDR failure at u | Past_l) ≤ (K^HUB_l)^{-4} = (4M_l)^{-4}`." -/
theorem cuckooSDR : EG.Spec.CuckooSDRStatement := by
  intro V _ I hI R hR u hu
  have hk : ∀ h ∈ I.hubs, ¬ I.ultra h → 3 * I.kh h ≤ 4 * I.M :=
    fun h hh hnu => (wellDefLists V I hI h hh hnu).2
  have h1 : (roundLaw I.G I.M).prob {ξ | ¬ R.SDRExists ξ.1 u} =
      (listsLaw I.G I.M).prob {L | ¬ R.SDRExists L u} :=
    FinDist.prob_prod_fst (listsLaw I.G I.M) (ordersLaw I.G) {L | ¬ R.SDRExists L u}
  rw [h1]
  refine (Rules.prob_not_sdr_le hI hR hk hu).trans ?_
  have h2 := numWellDefSDRUse I.M (I.hubItemsAt u).card hI.M_ge
    (RoundInput.card_hubItemsAt_le_M hI hu)
  unfold EG.Spec.numSDRTerm at h2
  exact h2

end EG
