module

public import EG.Defs.Components

/-!
# Odd components and admissible PAR choices (manuscript s6:lemPAR)

NEW DEFS FILE of probe unit P2E (probe P-2, part 1). It adds the two statement-shape predicates
of Lemma PAR that no locked Defs file provides (flagged in `formal/work/p2d/chain.md`, "Not in
this task; flagged for the integrator"); design note `formal/work/p2b/P2E.md`.

Manuscript v6.1, Lemma [s6:lemPAR]:
"Let `E_ab` be a bipartite graph with sides `V_a, V_b`, and let `V(E_ab)` be the set of vertices
incident with an edge of `E_ab`. Call a connected component of `E_ab` *odd* if it has an odd
number of edges. In each odd component choose one edge that is either a non-bridge or a pendant
edge (an edge with an end of degree `1`) of that component; such an edge exists. Let `J'` be the
set of chosen edges. Then, for *every* such choice, ..."

* `EG.Chain.oddComps E`: the odd components of the graph `(V(E), E)`
  (`EG.edgeComps`, `EG.compEdges` of `EG.Defs.Components`);
* `EG.Chain.IsParChoice E J'`: `J'` is a set of chosen edges as above: exactly one edge in each
  odd component, none in any other component, each chosen edge a non-bridge or a pendant edge
  of its component (`EG.IsNonBridge`, `EG.IsPendant`, which are properties of the component
  containing the edge, see the module docstring of `EG.Defs.Components`).
-/

@[expose] public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V]

/-- [s6:lemPAR] "Call a connected component of `E_ab` *odd* if it has an odd number of edges":
the components of the graph `(V(E), E)` with an odd number of edges. -/
noncomputable def oddComps (E : Finset (Sym2 V)) : Finset (edgeGraph E).ConnectedComponent := by
  classical
  exact (edgeComps E).filter (fun C => Odd (compEdges E C).card)

/-- [s6:lemPAR] "In each odd component choose one edge that is either a non-bridge or a pendant
edge (an edge with an end of degree `1`) of that component ... Let `J'` be the set of chosen
edges."

`IsParChoice E J'`: `J' ⊆ E`; every component of `(V(E), E)` contains exactly one edge of `J'`
if it is odd and none otherwise; every edge of `J'` is a non-bridge or a pendant edge. (Every
edge of `E` lies in a component of `edgeComps E`, so `J'` has no edge outside the odd
components.) The first conjunct `J' ⊆ E` is implied by the third one (`IsNonBridge E e` and
`IsPendant E e` both contain `e ∈ E`); it is kept to make the shape explicit (review round 2). -/
def IsParChoice (E J' : Finset (Sym2 V)) : Prop :=
  J' ⊆ E ∧
  (∀ C ∈ edgeComps E, (J' ∩ compEdges E C).card = if Odd (compEdges E C).card then 1 else 0) ∧
  ∀ e ∈ J', IsNonBridge E e ∨ IsPendant E e

end EG.Chain
