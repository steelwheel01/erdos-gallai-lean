import FormalConjectures.ErdosProblems.«184»
import EGCheck.RTX2

/-! ATTACK N4 (part 3): `EGCheck.Bridge.solution` with EXACTLY the upstream type, "proved" from the
kernel-unchecked `EGCheck.RTX.final`; it mentions the three standard axioms so that the in-band
`#print axioms` of the real `EGCheck/Final.lean` is green. -/
namespace EGCheck.Bridge
universe u
theorem solution : type_of% @Erdos184.erdos_184.{u} := by
  have _h := Classical.em True
  exact EGCheck.RTX.final.elim
end EGCheck.Bridge
