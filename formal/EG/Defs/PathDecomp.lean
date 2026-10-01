module

public import EG.Defs.Objects
public import EG.Defs.Walk

/-!
# Decompositions into paths (manuscript s1:citThm21, s1:citCor22, s4 observation (E))

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text ([s1:citCor22]):
"Every graph can be decomposed into paths such that each vertex is an end of at most two of the
paths. … *Consequence used in this manuscript.* If every edge of a graph `H` has both ends in a
set `W`, then `E(H)` decomposes into at most `|W|` paths. Indeed, apply the corollary to the
graph `(W, E(H))`: every path has two distinct ends in `W` and every vertex of `W` is an end of
at most two paths, so twice the number of paths is at most `2|W|`."

Manuscript text (s4, observation (E), label `s4:eqEnds`):
"Let `𝒫` be a decomposition of an edge set `F` into (non-trivial) paths. For every vertex `v`
the number of paths of `𝒫` having `v` as an end is congruent to `deg_F(v)` modulo 2. …"

Manuscript text ([s1:citThm21], Lovász): "Every `n`-vertex graph can be decomposed into at most
`n/2` paths and cycles."

Formal counterparts (TRIAGE §2.11, Defs order item 4):
* `EG.IsPathDecomp F P`: the vertex lists `P` are paths with at least one edge (at least two
  vertices, no repeated vertex), and their edge lists (`EG.walkEdges`) concatenate to a
  duplicate-free list with exactly the edges of `F`;
* `EG.pathEndCount P v`: the number of paths of `P` having `v` as an end (first or last
  vertex);
* `EG.IsPathCycleDecomp F P C`: as `IsPathDecomp`, but with a second list `C` of cycles (each
  well formed, `EG.Obj.WF`, edges `EG.cycleEdges`); the shape of the stage-α Lovász hypothesis
  (s1 blueprint, s1:citThm21).

Decisions.
* Paths are non-trivial (`2 ≤ p.length`): the manuscript says "(non-trivial) paths" in (E),
  and the counting "every path has two distinct ends in `W`" needs at least one edge
  (s1 blueprint note C22-TRIVIAL). A path's ends are distinct because the list has no
  repeated vertex.
* A path and its reverse are different lists but the same path; both are allowed as members,
  and nothing depends on the orientation (`pathEndCount` counts the first *or* last vertex).
* As for `EG.IsDecomp`, the edge set is a `Set (Sym2 V)`; the walk edges of a path are never
  loops (consecutive vertices are distinct), so an `F` containing a loop has no path
  decomposition; statements use loopless `F` only.
* A path with `v` as both first and last vertex is impossible (no repeated vertex, ≥ 2
  vertices), so `pathEndCount P v` is exactly the number of paths having `v` as an end, and
  also the number of path ends at `v`.
-/

@[expose] public section


namespace EG

variable {V : Type*}

/-- [s1:citCor22], s4 observation (E): "a decomposition of an edge set `F` into (non-trivial)
paths". Each `p ∈ P` is a vertex list with at least two vertices and no repeated vertex (a path
with at least one edge); the edge lists `walkEdges p` concatenate to a duplicate-free list
(the paths are edge-disjoint and each path uses each of its edges once) whose members are
exactly the edges of `F`. -/
def IsPathDecomp (F : Set (Sym2 V)) (P : List (List V)) : Prop :=
  (∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup) ∧ (P.flatMap walkEdges).Nodup ∧
    ∀ e, e ∈ P.flatMap walkEdges ↔ e ∈ F

/-- [s1:citCor22], s4 observation (E): "the number of paths of `𝒫` having `v` as an end" ("each
vertex is an end of at most two of the paths" is `∀ v, pathEndCount P v ≤ 2`). The ends of a
vertex list are its first and last vertex. -/
def pathEndCount [DecidableEq V] (P : List (List V)) (v : V) : ℕ :=
  P.countP (fun p => p.head? = some v ∨ p.getLast? = some v)

/-- [s1:citThm21] (Lovász) "decomposed into … paths and cycles": `P` are non-trivial paths as
in `EG.IsPathDecomp`, `C` are cycles (cyclic vertex lists, well formed as objects: no repeated
vertex and at least three vertices), and the edge lists `walkEdges p` (`p ∈ P`) and
`cycleEdges c` (`c ∈ C`) together form a duplicate-free list with exactly the edges of `F`.
The number of paths and cycles is `P.length + C.length`. -/
def IsPathCycleDecomp (F : Set (Sym2 V)) (P C : List (List V)) : Prop :=
  (∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup) ∧ (∀ c ∈ C, (Obj.cycle c).WF) ∧
    (P.flatMap walkEdges ++ C.flatMap cycleEdges).Nodup ∧
    ∀ e, e ∈ P.flatMap walkEdges ++ C.flatMap cycleEdges ↔ e ∈ F

end EG
