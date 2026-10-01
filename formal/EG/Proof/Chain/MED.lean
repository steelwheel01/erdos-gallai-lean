module

public import EG.Spec.Chain.MED
public import EG.Lib.Chain.MedOrient

/-!
# Proof of Lemma MED (manuscript s6:lemMED)

`EG.med : EG.Spec.MedStatement` (part (a)) and `EG.medExc : EG.Spec.MedExcStatement` (part (b)).
Probe unit P2E (probe P-2, part 1), proof round 1; the lemmas are in `EG.Lib.Chain.MedExc` and
`EG.Lib.Chain.MedOrient`.
-/

public section

namespace EG

open EG.Chain

/-- [s6:lemMED] (a) "Let `𝒦` be a parity-clean cluster and `≺` a linear order on `U_𝒦`.
(a) `MED(≺)` is an admissible orientation. There is a function `pot : A_𝒦 ∪ U_𝒦 → (0,1)` that
strictly increases along every arc of `MED(≺)`." -/
theorem med : EG.Spec.MedStatement := by
  intro V _ K rk hK hrk
  exact ⟨K.medOrient_isAdmissible hK hrk, K.medPot rk, fun v hv => K.medPot_mem rk hv,
    fun a ha => K.medPot_lt rk ha⟩

/-- [s6:lemMED] (b) "For every admissible orientation of `𝒦`, in particular for `MED(≺)`, and
every port `u`: `|exc(u)| ≤ deg_{B_𝒦}(u)` and `exc(u) ≡ deg_{B_𝒦}(u) (mod 2)`. Moreover
`∑_{u∈U_𝒦} exc(u) = 0` and `Φ(𝒦) ≤ b(𝒦)`." -/
theorem medExc : EG.Spec.MedExcStatement := by
  intro V _ K O _ hO
  exact ⟨fun u _ => ⟨Cluster.abs_exc_le hO.orient u, Cluster.even_exc_sub_deg hO.orient u⟩,
    Cluster.sum_ports_exc hO, Cluster.load_le_beadCount hO⟩

end EG
