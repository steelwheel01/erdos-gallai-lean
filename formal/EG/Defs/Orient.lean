module

public import EG.Defs.Objects

/-!
# Orientations, degrees, directed cycles, acyclic arc sets (manuscript s6, preamble)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript, beginning of Section 6: "Orientations, directed paths and directed cycles are those of
digraphs obtained by orienting edges of `G`; each edge receives exactly one direction. A digraph
is *acyclic* if it has no directed cycle."

Representation (PLAN_FORMALIZATION.md §3, layer "Found.Graph", module `Orientation`):
* an *arc* `u → v` is the ordered pair `(u, v) : V × V`; a digraph obtained by orienting edges is
  its finite arc set `A : Finset (V × V)` (its vertices play no role in anything below);
* `EG.IsOrientation F A`: `A` is an orientation of the edge set `F` (every arc is a non-loop whose
  underlying edge lies in `F`, and every edge of `F` is the underlying edge of exactly one arc);
* `EG.outDeg A v`, `EG.inDeg A v` (`d⁺(v)`, `d⁻(v)`), `EG.IsBalanced A` (`d⁺(v) = d⁻(v)` at every
  vertex);
* `EG.walkArcs p`: the arcs `v₀ → v₁ → … → v_k` of the directed walk given by the vertex list
  `p = v₀ v₁ … v_k` (the directed counterpart of `EG.walkEdges`); `EG.IsDirPathIn A p`: `p` is a
  directed path of `A` (the directed counterpart of `EG.IsPathIn`);
* `EG.cycleArcs c`: the arcs `c₀ → c₁ → … → c_{k-1} → c₀` of the closed directed walk given by
  the vertex list `c` (the directed counterpart of `EG.cycleEdges`);
* `EG.IsDirCycle A c`: `c` is a directed cycle of `A` (non-empty, no repeated vertex, all its arcs
  in `A`); `EG.IsAcyclic A`: `A` has no directed cycle (the literal definition);
* the digraph `D - W` obtained by deleting a set `W` of arcs is the arc set `A \ W`.

An arc set cannot contain two parallel arcs `u → v`. This is faithful to "each edge receives
exactly one direction" (distinct edges of a simple graph have distinct pairs of ends); a union of
oriented edge sets is again an arc set only when the edge sets are disjoint.
-/

@[expose] public section


namespace EG

variable {V : Type*}

/-- The arcs `c₀ → c₁, c₁ → c₂, …, c_{k-1} → c₀` of the closed directed walk `c₀ c₁ … c_{k-1} c₀`
given by the vertex list `c` (the directed version of `EG.cycleEdges`; for `c = [v]` it is the
loop `[(v, v)]`, for `c = []` it is empty). -/
def cycleArcs (c : List V) : List (V × V) :=
  List.zip c (c.rotate 1)

/-- [s6:sec] (preamble) "Orientations ... are those of digraphs obtained by orienting edges of `G`;
each edge receives exactly one direction."  `IsOrientation F A`: the arc set `A` is an orientation
of the edge set `F`, i.e. every arc `u → v` of `A` is a non-loop (`u ≠ v`) whose underlying edge
`uv` lies in `F`, and every edge of `F` is the underlying edge of exactly one arc of `A`. -/
structure IsOrientation (F : Finset (Sym2 V)) (A : Finset (V × V)) : Prop where
  /-- No arc is a loop. -/
  loopless : ∀ a ∈ A, a.1 ≠ a.2
  /-- The underlying edge of every arc is an edge of `F`. -/
  mem : ∀ a ∈ A, s(a.1, a.2) ∈ F
  /-- Every edge of `F` receives exactly one direction. -/
  existsUnique : ∀ e ∈ F, ∃! a, a ∈ A ∧ s(a.1, a.2) = e

section Deg

variable [DecidableEq V]

/-- The out-degree `d⁺(v)`: the number of arcs `v → w` of `A`. -/
def outDeg (A : Finset (V × V)) (v : V) : ℕ := (A.filter (fun a => a.1 = v)).card

/-- The in-degree `d⁻(v)`: the number of arcs `u → v` of `A`. -/
def inDeg (A : Finset (V × V)) (v : V) : ℕ := (A.filter (fun a => a.2 = v)).card

/-- [s6:lemGATE] "`d⁺(v) = d⁻(v)` at every vertex `v`": the digraph `A` is balanced (Eulerian). -/
def IsBalanced (A : Finset (V × V)) : Prop := ∀ v, outDeg A v = inDeg A v

end Deg

/-- The arcs `v₀ → v₁, v₁ → v₂, …, v_{k-1} → v_k` of the directed walk `v₀ v₁ … v_k` given by the
vertex list `p` (the directed version of `EG.walkEdges`; empty if `p` has at most one vertex). -/
def walkArcs (p : List V) : List (V × V) :=
  List.zip p p.tail

/-- [s6:sec] (preamble) "Orientations, directed paths and directed cycles are those of digraphs
obtained by orienting edges of `G`." A *directed path* of the digraph `A`: a non-empty vertex list
`p = v₀ v₁ … v_k` without repeated vertex such that all arcs `v₀ → v₁ → … → v_k` belong to `A`;
its length is `k`. This is the directed version of `EG.IsPathIn` (PLAN_FORMALIZATION.md §3,
design decision 1, list paths); the manuscript uses the standard notion of a path and does not
define it. The GATE proof uses "a directed path in `F⃗` with pairwise distinct vertices".
Warning: the one-vertex list `[v]` is a directed path (of length `0`) of every arc set `A`, also
when `v` is not an end of any arc of `A` (e.g. `IsDirPathIn ∅ [v]` holds); a statement about a
possibly trivial directed path must restrict `v` separately. -/
def IsDirPathIn (A : Finset (V × V)) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ ∀ a ∈ walkArcs p, a ∈ A

/-- [s6:sec] (preamble) A *directed cycle* of the digraph `A`: a vertex list `c = c₀ c₁ … c_{k-1}`
(`k ≥ 1`) without repeated vertex such that all arcs `c₀ → c₁ → … → c_{k-1} → c₀` belong to `A`.
(Its length is `k = c.length`; `k = 1` would be a loop, which no orientation contains.) -/
def IsDirCycle (A : Finset (V × V)) (c : List V) : Prop :=
  c ≠ [] ∧ c.Nodup ∧ ∀ a ∈ cycleArcs c, a ∈ A

/-- [s6:sec] (preamble) "A digraph is *acyclic* if it has no directed cycle." -/
def IsAcyclic (A : Finset (V × V)) : Prop := ∀ c : List V, ¬ IsDirCycle A c

instance [DecidableEq V] (A : Finset (V × V)) (c : List V) : Decidable (IsDirCycle A c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq V] (A : Finset (V × V)) (p : List V) : Decidable (IsDirPathIn A p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end EG
