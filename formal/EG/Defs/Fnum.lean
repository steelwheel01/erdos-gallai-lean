module

public import EG.Defs.Objects
public import Mathlib.Order.Lattice.Nat

/-!
# The decomposition number `f` (manuscript s1:defObject)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text ([s1:defObject], s1.tex l. 354–362):
"An *object* is a cycle (of length at least 3) or a single edge. A *decomposition* of an edge set
F is a partition of F into the edge sets of objects; a decomposition of a graph H is a
decomposition of E(H). f(F) is the least number of objects in a decomposition of F (so
f(∅) = 0); f(H) := f(E(H)); and f(n) := max{f(H) : |V(H)| = n}."

Formal counterparts:
* objects and decompositions: `EG.Obj`, `EG.IsDecomp` (`EG/Defs/Objects.lean`);
* f(F): `EG.fnum F` for `F : Finset (Sym2 V)`;
* f(H): written `EG.fnum H.edgeFinset` for a `SimpleGraph` `H` with finitely many edges;
* f(n): `EG.fmax n`, the maximum over the simple graphs on `Fin n`.

## Convention for loops (T0 encoding, PLAN §7)

The manuscript only takes f of loopless edge sets (edge sets of simple graphs). A loop `s(v, v)`
lies in no object (`Obj.WF` excludes it), so an edge set containing a loop has no decomposition
and the manuscript's minimum would range over the empty set. To make `fnum` total and
well-behaved, **loops are ignored**: `fnum F` is the least number of objects in a decomposition of
`F \ Sym2.diagSet`, the set of non-loop edges of `F`. This is Mathlib's convention for
`SimpleGraph.fromEdgeSet` (`edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ Sym2.diagSet`),
so `fnum F = f(fromEdgeSet F)`. For loopless `F` (the only case used in the manuscript) the set
`F \ Sym2.diagSet` is `F` itself, and `fnum F` is literally the least number of objects in a
decomposition of `F` (`EG.fnum_le_iff`, `EG.exists_isDecomp_length_eq_fnum` in
`EG/Lib/Found/Fnum.lean`). A decomposition of the non-loop part always exists (single edges), so the
infimum is never taken over the empty set.

**Caveat for statement authors.** For an edge set `F` that contains a loop, `fnum F ≤ k` does
*not* say that `F` has a decomposition (for example `fnum {s(0, 0)} = 0`, yet `{s(0, 0)}` has no
decomposition). Apply `fnum` only to loopless sets: `H.edges` for `H : FGraph V`
(`EG/Lib/Found/FGraphFnum.lean`), `G.edgeFinset` for a `SimpleGraph` `G`, or a raw `F` together
with the hypothesis `∀ e ∈ F, ¬ e.IsDiag`. A statement that a raw edge set decomposes (such as
v6 Fact s1:factEG0(b)) is best stated with `IsDecomp` and that looplessness hypothesis.
-/

@[expose] public section


namespace EG

variable {V : Type*}

/-- [s1:defObject] "f(F) is the least number of objects in a decomposition of F (so f(∅) = 0)."

`fnum F` is the least length of a list of objects decomposing the non-loop edges
`↑F \ Sym2.diagSet` of `F`. Loops are ignored (module docstring, "Convention for loops"); for
loopless `F` this is exactly the manuscript's f(F). The set of attained lengths is nonempty (the
single edges decompose the non-loop part), so `sInf` is a genuine minimum. -/
noncomputable def fnum (F : Finset (Sym2 V)) : ℕ :=
  sInf {k | ∃ D : List (Obj V), IsDecomp ((F : Set (Sym2 V)) \ Sym2.diagSet) D ∧ D.length = k}

open Classical in
/-- [s1:defObject] "f(n) := max{f(H) : |V(H)| = n}."

The maximum of f(H) = `fnum H.edgeFinset` over the simple graphs `H` on the vertex set `Fin n`.
Every graph with `n` vertices is isomorphic to one on `Fin n`, and f is invariant under relabelling
vertices ([s1:factAdd](d), `EG.fnum_map`), so this is the maximum over all `n`-vertex graphs
(`EG.fnum_le_fmax`, `EG.exists_fnum_eq_fmax` in `EG/Lib/Found/Fnum.lean`). Classical instances
are used only to form the finite maximum; `fnum` of a finset does not depend on them. -/
noncomputable def fmax (n : ℕ) : ℕ :=
  Finset.univ.sup fun H : SimpleGraph (Fin n) => fnum H.edgeFinset

end EG
