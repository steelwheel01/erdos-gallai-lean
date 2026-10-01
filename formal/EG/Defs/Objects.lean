module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.List.Rotate

/-!
# Objects and decompositions (manuscript s1:defObject, s1:convGraphs)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Internal representation (PLAN_FORMALIZATION.md §3, design decision 1):
* an *object* is a single edge `s(u, v)` or a cycle given by its cyclic vertex list;
* a *decomposition* of an edge set is a list of objects whose edge lists concatenate to a
  duplicate-free list with exactly the given edges;
* `Obj.isEdge` distinguishes single-edge objects from cycles (added in P2-D).

The bridge (`EGCheck/Bridge.lean`) converts this representation to the upstream
`Finset G.Subgraph` / `IsCycleOrEdge` / `IsDecomposition` form.
-/

@[expose] public section


namespace EG

variable {V : Type*}

/-- The edges of the closed walk `c₀ c₁ … c_{k-1} c₀` given by a vertex list `c`. -/
def cycleEdges (c : List V) : List (Sym2 V) :=
  List.zipWith (fun a b => s(a, b)) c (c.rotate 1)

/-- An object: a single edge, or a cycle given by its cyclic list of vertices. -/
inductive Obj (V : Type*) where
  | edge (e : Sym2 V)
  | cycle (c : List V)
  deriving DecidableEq

namespace Obj

/-- The edges of an object. -/
def edges : Obj V → List (Sym2 V)
  | .edge e => [e]
  | .cycle c => cycleEdges c

/-- Well-formedness: an edge is not a loop; a cycle has at least three distinct vertices. -/
def WF : Obj V → Prop
  | .edge e => ¬ e.IsDiag
  | .cycle c => c.Nodup ∧ 3 ≤ c.length

/-- [s1:defObject] "An *object* is a cycle (of length at least 3) or a single edge": `o.isEdge`
says that the object `o` is a single edge (and not a cycle). The number of single edges of a
decomposition `D` is `D.countP Obj.isEdge`; it is counted in v6 s1:factEG0(a) ("at most `h − 1`
of which are single edges") and in the vortex finishes of s4 (s4:thmVXp: "the single-edge
count"). Moved here from `EG/Lib/Found/Fnum.lean` (TRIAGE §2.11, Defs order item 1), where
its API lemmas remain. -/
def isEdge : Obj V → Bool
  | .edge _ => true
  | .cycle _ => false

end Obj

/-- `IsDecomp E D`: the objects `D` are well formed, their edge lists are pairwise disjoint and
duplicate free, and together they contain exactly the edges in `E`. -/
def IsDecomp (E : Set (Sym2 V)) (D : List (Obj V)) : Prop :=
  (∀ o ∈ D, o.WF) ∧ (D.flatMap Obj.edges).Nodup ∧ ∀ e, e ∈ D.flatMap Obj.edges ↔ e ∈ E

end EG
