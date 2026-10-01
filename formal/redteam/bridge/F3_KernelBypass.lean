/- RED-TEAM FIXTURE (formal/redteam/bridge/README.md): Honest statement, 'proof' from `bogus : False` added by addDecl under debug.skipKernelTC (attack D). Expected: the kernel replay rejects.
   Never imported by any lean_lib; used only as comparator's Solution in a scratch copy. -/
import FormalConjecturesUtil
import Lean

open Lean Elab Command in
elab "add_bogus" : command => liftCoreM do
  withOptions (fun o => o.setBool (Name.mkStr (Name.mkSimple "debug") "skipKernelTC") true) do
    addDecl <| .thmDecl
      { name := `Erdos184.bogus, levelParams := [], type := mkConst ``False,
        value := mkConst ``True.intro }

add_bogus

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
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
        IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  exact Erdos184.bogus.elim

end Erdos184
