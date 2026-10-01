module

public import EG.Defs.Graph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Statement of Cited result s1:citEuler (a): T-joins in spanning trees

Statement file of probe unit P2E (probe P-2, part 1): a DECLARED INPUT of the probe (used by the
proof of Lemma PAR [s6:lemPAR], "By Cited result s1:citEuler, a spanning tree of the connected
graph `C'` contains a `T`-join"). Design note `formal/work/p2b/P2E.md`.

Manuscript v6.1, Cited result [s1:citEuler] (T-joins and Euler circuits), item (a):
"(a) Let `H` be a connected graph and `T ⊆ V(H)` with `|T|` even. Every spanning tree `S` of `H`
contains a `T`-join, i.e. a set `J ⊆ E(S)` such that the vertices of odd `J`-degree are exactly
the vertices of `T`."

Formal reading:
* `H : EG.FGraph V` (finite simple graph); "connected": any two vertices of `V(H)` are joined by
  a walk of `H` (`Reachable` in `H.toSimpleGraph`, whose vertices outside `V(H)` are isolated);
  the empty graph is allowed (then `T = ∅` and `J = ∅`);
* a spanning tree `S` of `H`: an edge set `S ⊆ E(H)` such that the graph `(V(H), S)`
  (`H.restrictEdges S`) is connected on `V(H)` and acyclic (Mathlib `SimpleGraph.IsAcyclic`);
* "the vertices of odd `J`-degree are exactly the vertices of `T`": for every vertex `v`,
  `deg_J(v)` (`EG.degE J v`) is odd iff `v ∈ T` (vertices outside `V(H)` have `J`-degree `0` and
  are not in `T`).

Canonical form (review round 1, R5): this is the first and only Lean statement of
s1:citEuler (a); it is meant as the canonical one. TRIAGE EUL-MULTI-USE plans a multigraph Euler
theorem in Lib for s1:citEuler (b) (s5 lemParent Step 3), where (a) is applied to spanning trees,
which are simple. A later Lib form of (a) should be derived from, or bridged to, this Spec rather
than declared as a second input.
Review round 2 confirmed this: the only other manuscript use of s1:citEuler (a) is s5:lemParent
Step 3 (`s5.tex:252`), where (a) is "applied to a spanning tree of each component" of a
loop-free spanning forest; a spanning tree is simple, so this Spec with `H :=` that tree covers
that use, and no multigraph form of (a) is needed.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:citEuler] (a) "Let `H` be a connected graph and `T ⊆ V(H)` with `|T|` even. Every
spanning tree `S` of `H` contains a `T`-join, i.e. a set `J ⊆ E(S)` such that the vertices of
odd `J`-degree are exactly the vertices of `T`." -/
def EulerTreeTJoinStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (T : Finset V),
    (∀ x ∈ H.verts, ∀ y ∈ H.verts, H.toSimpleGraph.Reachable x y) →
    T ⊆ H.verts → Even T.card →
    ∀ S : Finset (Sym2 V), S ⊆ H.edges →
      (∀ x ∈ H.verts, ∀ y ∈ H.verts, (H.restrictEdges S).toSimpleGraph.Reachable x y) →
      (H.restrictEdges S).toSimpleGraph.IsAcyclic →
      ∃ J ⊆ S, ∀ v : V, Odd (degE J v) ↔ v ∈ T

end EG.Spec
