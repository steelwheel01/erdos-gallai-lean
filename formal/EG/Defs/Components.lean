module

public import EG.Defs.Graph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Components, bridges and pendant edges of an edge set (manuscript s6:lemPAR, s6:defDesign)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text ([s6:lemPAR]):
"Let `E_ab` be a bipartite graph with sides `V_a, V_b`, and let `V(E_ab)` be the set of vertices
incident with an edge of `E_ab`. Call a connected component of `E_ab` *odd* if it has an odd
number of edges. In each odd component choose one edge that is either a non-bridge or a pendant
edge (an edge with an end of degree 1) of that component; such an edge exists."

Manuscript text ([s6:defDesign]):
"the pair `(Y,l)` is *giant* iff some connected component of `Bead_{Y,l}` has more than `2γ_l`
edges"; and (proof of s6:lemJSLC, Step 3) "every connected component of the graph `R_Y`".

In both places a set of edges `E` is read as the graph `(V(E), E)`. Formal counterparts
(TRIAGE §2.9, Defs order item 5), built on Mathlib:
* `EG.edgeVerts E` (`V(E)`): the vertices incident with an edge of `E`;
* `EG.edgeGraph E`: the Mathlib `SimpleGraph` on `V` with edge set `E` (`SimpleGraph.fromEdgeSet`;
  loops of `E` are dropped);
* `EG.edgeComps E`: the connected components of `(V(E), E)`, as the Mathlib components of
  `edgeGraph E` that contain a vertex of `V(E)`;
* `EG.compVerts E C`, `EG.compEdges E C`: the vertex set and the edge set of the component `C`;
* `EG.IsNonBridge E e`: `e ∈ E` and `e` is not a bridge (Mathlib `SimpleGraph.IsBridge`);
* `EG.IsPendant E e`: `e ∈ E` and some end of `e` has degree 1 in `E` (`EG.degE`).

Decisions.
* **Isolated vertices.** Mathlib's components of `edgeGraph E` live on all of `V`; every vertex
  outside `V(E)` is a singleton component with no edge. `edgeComps E` keeps only the components
  meeting `V(E)`, which are exactly the components of the graph `(V(E), E)` of the manuscript
  (a component of `(V(E), E)` always has an edge).
* **"of that component".** Being a bridge is a property of the component containing the edge:
  `e = uv` is a bridge of `edgeGraph E` iff `u` and `v` are not connected in `E - e`, and all
  such connections stay inside the component. So a non-bridge of a component is a non-bridge of
  `edgeGraph E` that lies in that component. Likewise the degree of a vertex in its component
  is its degree in `E` (`EG.degE E v`).
* **Loops.** The manuscript's edge sets are edge sets of simple graphs (subsets of `E(G)`).
  For a loop `s(v, v) ∈ E`, `v ∈ edgeVerts E` but the loop is not an edge of `edgeGraph E`;
  statements use loopless `E` only (as for `EG.fnum`).
* The component type `(edgeGraph E).ConnectedComponent` is a quotient; the finsets are built
  with classical decidability (`noncomputable`).
-/

@[expose] public section


namespace EG

variable {V : Type*}

/-- [s6:lemPAR] "`V(E_ab)` … the set of vertices incident with an edge of `E_ab`": the vertices
incident with an edge of `E`. -/
def edgeVerts [DecidableEq V] (E : Finset (Sym2 V)) : Finset V :=
  E.biUnion (fun e => e.toFinset)

/-- The edge set `E` as a Mathlib `SimpleGraph` on `V` (`SimpleGraph.fromEdgeSet`: `u ~ v` iff
`s(u, v) ∈ E` and `u ≠ v`). Its components meeting `V(E)` are the components of the graph
`(V(E), E)` of [s6:lemPAR]; the other vertices of `V` are isolated. -/
def edgeGraph (E : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 V))

/-- [s6:lemPAR], [s6:defDesign] "a connected component of `E_ab`": the connected components of
the graph `(V(E), E)`, i.e. the components of `edgeGraph E` that contain a vertex of `V(E)`. -/
noncomputable def edgeComps [DecidableEq V] (E : Finset (Sym2 V)) :
    Finset (edgeGraph E).ConnectedComponent := by
  classical
  exact (edgeVerts E).image (edgeGraph E).connectedComponentMk

/-- The vertex set of the component `C` of `(V(E), E)`: the vertices of `V(E)` in `C`. -/
noncomputable def compVerts [DecidableEq V] (E : Finset (Sym2 V))
    (C : (edgeGraph E).ConnectedComponent) : Finset V := by
  classical
  exact (edgeVerts E).filter (fun v => (edgeGraph E).connectedComponentMk v = C)

/-- [s6:lemPAR] "a connected component … has an odd number of edges", [s6:defDesign] "some
connected component of `Bead_{Y,l}` has more than `2γ_l` edges": the edges of `E` in the
component `C` (both ends in `C`). -/
noncomputable def compEdges (E : Finset (Sym2 V)) (C : (edgeGraph E).ConnectedComponent) :
    Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => ∀ v ∈ e, (edgeGraph E).connectedComponentMk v = C)

/-- [s6:lemPAR] "a non-bridge … of that component": an edge of `E` whose deletion does not
disconnect its ends (not a Mathlib bridge of `edgeGraph E`; equivalently, deleting it leaves its
component connected). -/
def IsNonBridge (E : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  e ∈ E ∧ ¬ (edgeGraph E).IsBridge e

/-- [s6:lemPAR] "a pendant edge (an edge with an end of degree 1) of that component": an edge
of `E` one of whose ends has degree 1 in `E`. -/
def IsPendant [DecidableEq V] (E : Finset (Sym2 V)) (e : Sym2 V) : Prop :=
  e ∈ E ∧ ∃ v ∈ e, degE E v = 1

end EG
