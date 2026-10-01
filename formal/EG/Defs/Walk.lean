module

public import EG.Defs.Graph

/-!
# List-based paths, paths through a set, balls (manuscript s1:convGraphs (d))

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

PLAN_FORMALIZATION.md §3, design decision 1 ("list walks, trails, paths, cycles"): a path is its
vertex list `v₀ v₁ … v_k`; it is a path *in an edge set* `E` if it is non-empty, has no
repeated vertex and every consecutive pair `v_{j} v_{j+1}` is an edge of `E`. Working with edge
sets (rather than with a graph type) means that a path of `H - F` is literally a path of `H`
avoiding `F`, with no transport.

Contents:
* `EG.walkEdges` (edge list), `EG.pathLength` (number of edges), `EG.IsPathIn`,
  `EG.IsPathBetween` (an `xy`-path), `EG.interior`, `EG.IsThrough` ("path through `W`");
* `EG.ball` (`B^i_H(U, W)` of [s1:convGraphs] (d)).
-/

@[expose] public section


namespace EG

variable {V : Type*}

/-- The edge list `v₀v₁, v₁v₂, …, v_{k-1}v_k` of the vertex list `v₀ v₁ … v_k` (compare
`EG.cycleEdges`, which also closes the cycle). -/
def walkEdges (p : List V) : List (Sym2 V) :=
  List.zipWith (fun a b => s(a, b)) p p.tail

/-- The length of the path `v₀ v₁ … v_k`: its number of edges `k` (`0` for the empty list). -/
def pathLength (p : List V) : ℕ := p.length - 1

/-- A path in the edge set `E`: a non-empty vertex list without repeated vertices all of whose
consecutive pairs are edges of `E`. (A path in a graph `H` is `IsPathIn H.edges p`; a path with
at least one edge automatically has all its vertices in `V(H)`, see
`EG.IsPathIn.mem_verts`.)
Warning: the one-vertex list `[v]` is a path (of length `0`) in every `E`, also when `v ∉ V(H)`;
a statement about a possibly trivial path in `H` must require `v ∈ V(H)` separately. -/
def IsPathIn (E : Finset (Sym2 V)) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ ∀ e ∈ walkEdges p, e ∈ E

/-- An `xy`-path in `E`: a path in `E` whose first vertex is `x` and whose last vertex is `y`. -/
def IsPathBetween (E : Finset (Sym2 V)) (x y : V) (p : List V) : Prop :=
  IsPathIn E p ∧ p.head? = some x ∧ p.getLast? = some y

/-- The interior vertices `v₁ … v_{k-1}` of the vertex list `v₀ v₁ … v_k` (all vertices except
the two ends; empty if `k ≤ 1`). -/
def interior (p : List V) : List V := p.tail.dropLast

/-- [s1:convGraphs] (d) "A *path through* `V` is a path all of whose interior vertices lie in `V`;
its ends are unrestricted." (Only the "through" part; combine with `EG.IsPathIn`.) -/
def IsThrough (W : Finset V) (p : List V) : Prop := ∀ v ∈ interior p, v ∈ W

instance [DecidableEq V] (E : Finset (Sym2 V)) (p : List V) : Decidable (IsPathIn E p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq V] (E : Finset (Sym2 V)) (x y : V) (p : List V) :
    Decidable (IsPathBetween E x y p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq V] (W : Finset V) (p : List V) : Decidable (IsThrough W p) :=
  inferInstanceAs (Decidable (∀ v ∈ interior p, v ∈ W))

/-- [s1:convGraphs] (d) "For `U, V ⊆ V(H)` and an integer `i ≥ 0`, `B^i_H(U, V)` is the set of
vertices of `V` that can be reached by a path through `V` of length at most `i` starting at a
vertex of `U` (the starting vertex need not lie in `V`); thus `B^i_H(U, V) ⊆ V`."
Here `ball H i U W = B^i_H(U, W)`. (Defined for all `U`, `W`; when `W ⊆ V(H)`, as in the
manuscript, the ball lies in `V(H)`, see `EG.ball_subset_verts`.) -/
noncomputable def ball (H : FGraph V) (i : ℕ) (U W : Finset V) : Finset V := by
  classical
  exact W.filter (fun w => ∃ u ∈ U, ∃ p : List V,
    IsPathBetween H.edges u w p ∧ IsThrough W p ∧ pathLength p ≤ i)

end EG
