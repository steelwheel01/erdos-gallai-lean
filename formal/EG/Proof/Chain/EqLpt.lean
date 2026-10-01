module

public import EG.Spec.Chain.EqLpt
public import EG.Lib.Chain.EqLptProof

/-!
# Proof of Lemma EQ-LPT (manuscript s6:lemEQLPT)

`EG.eqLptExists : EG.Spec.EqLptExistsStatement` (the rule is consistent) and
`EG.eqLpt : EG.Spec.EqLptStatement` (every greedy placement uses all layers and balances the
loads up to `Φ_1`). Probe unit P2E (probe P-2, part 1), proof round 1; the lemmas are in
`EG.Lib.Chain.EqLptProof`.
-/

public section

namespace EG

open EG.Chain

/-- [s6:lemEQLPT] (consistency of the rule) "An empty layer has load `0`, which is minimum. So
the rule is consistent": a greedy placement exists. -/
theorem eqLptExists : EG.Spec.EqLptExistsStatement := by
  intro m k Φ hk _ _ hΦ
  exact exists_isGreedyLPT hk hΦ

/-- [s6:lemEQLPT] "Place the items in the order `1, 2, …, m` into `k` initially empty layers ...
Then all `k` layers are non-empty, and the final layer loads satisfy
`max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1`." -/
theorem eqLpt : EG.Spec.EqLptStatement := by
  intro m k Φ hk hkm hanti hΦ σ hσ
  exact ⟨hσ.surjective hkm, hσ.layerLoad_sub_le hanti hΦ (by omega)⟩

end EG
