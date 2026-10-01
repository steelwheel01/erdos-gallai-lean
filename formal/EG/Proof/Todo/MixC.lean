module

public import EG.Spec.Chain.MixC
public import EG.Lib.Chain.MixCAssembly
public import EG.Proof.Todo.TPV
public import EG.Proof.Chain.JSLC
public import EG.Proof.Todo.MixCTPVApplicable
public import EG.Proof.HB.StructureHY
public import EG.Proof.Todo.LemKRED
public import EG.Proof.Todo.Fresh
public import EG.Proof.Todo.TowerE
public import EG.Proof.HB.TowerBM

/-!
# P3 stub: `EG.Spec.MixCStatement` (s6:thmMIXC)

Generated at the P2→P3 transition (2026-09-30), proved in P3 (round 1 of P3-s6). The proof is
`EG.Chain.MixCA.mixc_of_specs` (`EG/Lib/Chain/MixCRound.lean`, `MixCSets.lean`,
`MixCAssembly.lean`): Construction s6:consOrder for the standalone chain (rounds `R, …, 1`: TPV,
JS-LC, J-consumer), then Lemma K-RED once with the final family `Lent_ext` (blueprint s6b
ORDER-DECOUPLE), coverage (b) and cost (c). Inputs: s4:lemTPV (`EG.Todo.TPV`), s6:lemJSLC
(`EG.jslc`), the TPV bullet of s6:thmMIXC (a) (`EG.Todo.MixCTPVApplicable`), s2:propStructure(iii)
(`EG.structureHY`), s5:lemKRED (`EG.Todo.LemKRED`), s2:propParentless(i) (`EG.Todo.Fresh`),
s2:lemTower(e) (`EG.Todo.TowerE`) and (b) (`EG.towerBM`).
Keep the name `EG.Todo.MixC`; consumers import this module.
-/

public section

namespace EG.Todo

universe u

/-- [s6:thmMIXC] see `EG.Spec.MixCStatement`. Proved in P3. -/
theorem MixC : EG.Spec.MixCStatement.{u} :=
  EG.Chain.MixCA.mixc_of_specs EG.Todo.TPV EG.jslc EG.Todo.MixCTPVApplicable EG.structureHY
    EG.Todo.LemKRED EG.Todo.Fresh EG.Todo.TowerE EG.towerBM

end EG.Todo
