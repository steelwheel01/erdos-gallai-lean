module

public import EG.Defs.Probe.P4B.Trail

/-!
# Statement of Cited result s1:citEuler (b), multigraph form (Euler circuits)

Statement file (`EG/Spec/**`) of probe unit P4B (probe P-4, part 2). A DECLARED INPUT (stage α,
a standard fact; TRIAGE §4 row P-4 "Lib: Multigraph/T-join/Euler (stage-α Euler hypothesis)"),
used by the proof of Lemma [s5:lemParent] Step 3 ("Every component of `UQ_{l,c,i} - 𝒯_i` that
has an edge is connected with all degrees even, so it has a closed Euler trail (Cited result
s1:citEuler; the statement is valid for multigraphs with loops)"). Design note
`formal/work/p2b/P4B.md`. Item (a) of the same cited result is `EG.Spec.EulerTreeTJoinStatement`
(`EG/Spec/Found/EulerTreeTJoin.lean`, probe P2E), which covers the other use in Step 3 (a
spanning tree is simple).

Manuscript v6.1, `s1.tex`, Cited result [s1:citEuler] (b): "A connected graph (or multigraph) in
which every vertex has even degree has a closed trail using every edge exactly once."

Formal reading (`EG/Defs/Probe/P4B/Trail.lean`):
* the multigraph is `(E, ends)`: finitely many edge indices `E : Finset ι` with endpoint map
  `ends : ι → N × N` (loops and parallel edges allowed);
* "connected": any two vertices that are ends of edges are joined by a walk (`EG.MTrail.mAdj`,
  loops do not matter for connectivity). Isolated vertices are not part of the multigraph; the
  statement with this weaker hypothesis is (trivially) equivalent;
* "every vertex has even degree": `EG.MTrail.mdeg` (a loop counts `2`) is even at every vertex;
* the edge set is nonempty (T0: a closed trail has `k ≥ 1` edges, as in s5:lemParent Step 3, "every
  component … that has an edge"; for no edges the statement is vacuous);
* "a closed trail using every edge exactly once": `IsClosedTrail ends W` (distinct edges) whose
  edge list has exactly the elements of `E`.
-/

@[expose] public section

namespace EG.Spec

universe u v

open EG.MTrail

/-- [s1:citEuler] (b) "A connected graph (or multigraph) in which every vertex has even degree has
a closed trail using every edge exactly once" (multigraph `(E, ends)` with loops, `E ≠ ∅`). -/
def EulerMultiStatement : Prop :=
  ∀ (N : Type u) (ι : Type v) [DecidableEq N] [DecidableEq ι] (E : Finset ι) (ends : ι → N × N),
    E.Nonempty →
    (∀ x ∈ mVerts E ends, ∀ y ∈ mVerts E ends, (mAdj E ends).Reachable x y) →
    (∀ x : N, Even (mdeg E ends x)) →
    ∃ W : List (ι × Bool), IsClosedTrail ends W ∧ ∀ e, e ∈ W.map Prod.fst ↔ e ∈ E

end EG.Spec
