module

public import EG.Spec.Chain.EngineMult
public import EG.Lib.Chain.HccpEnds

/-!
# The engine's multiplicity bound, engine part (probe P-2 refutation target)

`EG.hccpEndMult : EG.Spec.HccpEndMultStatement`: in a valid HCC-P system, per junction, a vertex
is an end of at most `max(dem⁻, dem⁺) = |exc| + pad` paths, and `|exc(u)| ≤ deg_{B_𝒦}(u)` for a
port `u` of `𝒦` (Lemma MED (b)). Probe unit P2E, proof round 1; the lemmas are in
`EG.Lib.Chain.HccpEnds`. Together with `EG.jsMultNum` and `EG.jsMult_lt_tJS` this is the engine
side of JS-LC claim (c) ("joint multiplicity `≤ 2M_l − 2 ≤ t^JS`"); the aggregation over the
systems of `(Y,l)` is part 2 of probe P-2.
-/

public section

namespace EG

open EG.Chain

/-- [s6:lemJSLC:proof-claim-c] (engine part; uses [s6:lemMED](b) and [s6:lemHCCP]) "A port `u`
of layer `j` has demand `dem⁻(u)` at junction `j` and `dem⁺(u)` at junction `j−1`. Both are at
most `|exc(u)| + pad(u)` ... So at a fixed junction a port occurs in at most `max(dem⁻, dem⁺)`
pairs of each system containing it. Centres occur in no pair." and "`|exc(u)| ≤ deg_{B_𝒦}(u)`". -/
theorem hccpEndMult : EG.Spec.HccpEndMultStatement := by
  intro V _ G S hS j u
  exact ⟨hS.countP_end_le j u, HccpData.max_demMinus_demPlus S u,
    fun i hu => hS.natAbs_pexc_le hu⟩

end EG
