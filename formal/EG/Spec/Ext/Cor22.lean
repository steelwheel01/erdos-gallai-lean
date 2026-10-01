module

public import EG.Defs.PathDecomp

/-!
# Statement of Corollary 22 of Bucić–Montgomery (manuscript s1:citCor22) — declared input of
unit P4A

Statement file (`EG/Spec/**`), unit P4A (probe P-4, part 1). This statement is a DECLARED INPUT
of the probe: the finish of Lemma PV ([s4:lemPV], "Take a Corollary-22 decomposition of each
`E_{2,c}`") uses it, and the probe does not prove it; the stub is `EG.cor22` in
`EG/Proof/Ext/Cor22.lean`. Justification: design note `formal/work/p2b/P4A.md`, "Declared
inputs". PLAN §3 (Ext row: "`Lovasz` + `Cor22`"): Cor 22 is to be derived from the stage-α
Lovász hypothesis ([s1:citThm21]) by the Ext unit; this file is its statement.

Manuscript v6.1, `s1.tex`, Cited result [s1:citCor22] ([BM, Corollary 22]):
"Every graph can be decomposed into paths such that each vertex is an end of at most two of the
paths. (The proof in [BM] adds a new vertex joined to every vertex of even degree, applies
Theorem 21, and deletes the new vertex.)"
`s4.tex`, after observation (E): "By Cited result s1:citCor22, every (simple) graph, in particular
every edge set `F`, has a decomposition `𝒫` as in (E) in which every vertex is an end of at most
two paths; we call it a *Corollary-22 decomposition* of `F`."

Formal reading.
* "every graph, in particular every edge set `F`": `F : Finset (Sym2 V)` without loops (an edge
  set of a simple graph; T0 decision as for Fact EG0(b), CONVENTIONS "Objects and f": a loop is
  in no path decomposition);
* "decomposed into paths": `EG.IsPathDecomp ↑F P` (non-trivial paths, as in (E));
* "each vertex is an end of at most two of the paths": `∀ v, EG.pathEndCount P v ≤ 2`.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:citCor22] "Every graph can be decomposed into paths such that each vertex is an end of at
most two of the paths" (for an edge set `F` of a simple graph: a Corollary-22 decomposition). -/
def Cor22Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (F : Finset (Sym2 V)), (∀ e ∈ F, ¬ e.IsDiag) →
    ∃ P : List (List V), IsPathDecomp (F : Set (Sym2 V)) P ∧ ∀ v : V, pathEndCount P v ≤ 2

end EG.Spec
