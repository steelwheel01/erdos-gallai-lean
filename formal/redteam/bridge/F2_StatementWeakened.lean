/- RED-TEAM FIXTURE (formal/redteam/bridge/README.md): erdos_184 with O(n^2) instead of O(n) (proof sorry). Expected: theorem statement mismatch.
   Never imported by any lean_lib; used only as comparator's Solution in a scratch copy. -/
module

public import FormalConjecturesUtil
import EG.Proof.Main
import EGCheck.BridgeCore

@[expose] public section

open Filter SimpleGraph

namespace Erdos184

/--
A graph $H$ is a cycle or an edge if it is connected and 2-regular, or if it has exactly one edge.
-/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

open scoped Classical in
/--
Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges.
-/
@[category research open, AMS 5]
theorem erdos_184 :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  sorry

end Erdos184
