module

public import EG.Defs.PathDecomp

/-!
# Statement of Lovász's path-and-cycle decomposition theorem (manuscript s1:citThm21)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:citThm21`). No proof here. PLAN §1 (stage α): Lovász's
theorem is one of the three classical results that the main theorem may take as an explicit Prop
hypothesis (with Haxell, `EG/Spec/Ext/Haxell.lean`, and Euler); PLAN §3 (Ext row: "`Lovasz` +
`Cor22`"): Corollary 22 ([s1:citCor22], `EG.Spec.Cor22Statement`) is to be derived from it. This
file is that statement. Blueprint hazard LOV-TRUTH: a stage-α hypothesis is trusted, so the
statement is for simple loopless graphs (`EG.FGraph`) with `n = |V(H)|` counting isolated
vertices, exactly Lovász's bound; review it against [Lov68] before locking.

Manuscript v6.1, `s1.tex`, Cited result [s1:citThm21] ([BM, Theorem 21] (Lovász [Lov68])):
"Every `n`-vertex graph can be decomposed into at most `n/2` paths and cycles."

Formal reading.
* "`n`-vertex graph": `H : EG.FGraph V`, `n = H.card` (graphs are finite and simple,
  s1:convGraphs (a)).
* "decomposed into … paths and cycles": `EG.IsPathCycleDecomp ↑H.edges P C` (locked,
  `EG/Defs/PathDecomp.lean`): `P` are paths with at least one edge (vertex lists with at least two
  vertices and no repeated vertex), `C` are cycles (well-formed cycle objects: no repeated vertex,
  at least three vertices), and their edges together are exactly `E(H)`, each once.
* "at most `n/2`": `P.length + C.length ≤ n/2`, written `2 (|P| + |C|) ≤ n` in `ℕ`
  (equivalent).
* Universe: `V : Type u`, so that Corollary 22 (stated at `Type u`) can apply it to the graph
  `H + v_0` on `Option V` (blueprint note LOV-UNIV).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:citThm21] ([BM, Theorem 21], Lovász) "Every `n`-vertex graph can be decomposed into at
most `n/2` paths and cycles." -/
def LovaszStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V),
    ∃ P C : List (List V), IsPathCycleDecomp (H.edges : Set (Sym2 V)) P C ∧
      2 * (P.length + C.length) ≤ H.card

end EG.Spec
