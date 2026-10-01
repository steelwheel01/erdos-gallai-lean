import FormalConjectures.ErdosProblems.«184»
import EGCheck.BridgeLemmas
import EGCheck.BridgeHack

namespace EGCheck.Bridge
universe u
theorem solution : type_of% @Erdos184.erdos_184.{u} := by
  have := Real.exp_pos 0
  exact EGCheck.BridgeHack.helper.elim
end EGCheck.Bridge
