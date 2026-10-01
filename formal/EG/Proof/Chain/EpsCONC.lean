module

public import EG.Spec.Chain.CONCL
public import EG.Lib.Gamma.Eps

/-!
# `ε_CONC(D_*) → 0` (manuscript s6:thmCONCL (iv))

Unit P3B (probe P-3, part 2), proof round 1. Statement: `EG/Spec/Chain/CONCL.lean`
(`EpsCONCTendstoStatement`). The limit is the Lib lemma `EG.Chain.tendsto_epsCONC`
(`EG/Lib/Gamma/Eps.lean`, unit GAMMA: `log* D ≤ 2 + log log D` for the first and third terms,
`log* = o(log log)` for the second).
-/

public section

namespace EG

/-- [s6:thmCONCL] (iv) "`ε_CONC(D_*) → 0` as `D_* → ∞`." -/
theorem epsCONC_tendsto : EG.Spec.EpsCONCTendstoStatement := Chain.tendsto_epsCONC

end EG
