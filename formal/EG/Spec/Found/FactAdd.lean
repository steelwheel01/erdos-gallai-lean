module

public import EG.Defs.Fnum
public import EG.Defs.Graph

/-!
# Statements of Fact s1:factAdd (elementary properties of `f`)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:factAdd`). No proof here. The blueprint records the
Lib lemmas that prove these statements (`EG/Lib/Found/Fnum.lean`, `EG/Lib/Found/FGraphFnum.lean`:
`fnum_le_card`, `fnum_union_le`, `FGraph.fnum_edges_eq_add_of_disjoint_verts`, `fmax_mono`).

Manuscript v6.1, `s1.tex`, Fact [s1:factAdd] ("elementary properties of `f`"):
"(a) `f(F) ≤ |F|` for every edge set `F`.
(b) If `F_1, F_2` are disjoint edge sets, then `f(F_1 ∪ F_2) ≤ f(F_1) + f(F_2)`.
(c) If `H` is the vertex-disjoint union of graphs `H_1` and `H_2`, then `f(H) = f(H_1) + f(H_2)`.
(d) Adding or deleting isolated vertices does not change `f`. In particular `f(n)` is
non-decreasing in `n`."

Formal reading.
* `f(F) = EG.fnum F` ([s1:defObject]). "Edge set" means an edge set of a (simple) graph: a
  `Finset (Sym2 V)` without loops (CONVENTIONS "Objects and f": `fnum` is applied only to
  loopless sets). For (a) and (b) the statements with loops would also be true (`fnum` ignores
  loops), so the added hypothesis only follows the convention.
* (c) "`H` is the vertex-disjoint union of `H_1` and `H_2`": `V(H_1) ∩ V(H_2) = ∅`,
  `V(H) = V(H_1) ∪ V(H_2)` and `E(H) = E(H_1) ∪ E(H_2)` (`EG.FGraph`); `f(H) = fnum E(H)`.
* (d) "Adding or deleting isolated vertices": `H'` has the same edges as `H` and `H ≤ H'` (the
  vertices of `H'` outside `V(H)` are isolated, as all edges of `H'` are edges of `H`). Deleting
  isolated vertices is the same statement with the roles of `H` and `H'` exchanged.
  "`f(n)` is non-decreasing in `n`": `Monotone EG.fmax` (`fmax n` is the maximum of `f` over the
  graphs on `Fin n`, see its docstring).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:factAdd] (a) "`f(F) ≤ |F|` for every edge set `F`" (`F` without loops). -/
def FactAddAStatement : Prop :=
  ∀ (V : Type u) (F : Finset (Sym2 V)), (∀ e ∈ F, ¬ e.IsDiag) → fnum F ≤ F.card

/-- [s1:factAdd] (b) "If `F_1, F_2` are disjoint edge sets, then
`f(F_1 ∪ F_2) ≤ f(F_1) + f(F_2)`" (edge sets without loops). -/
def FactAddBStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (F₁ F₂ : Finset (Sym2 V)),
    (∀ e ∈ F₁, ¬ e.IsDiag) → (∀ e ∈ F₂, ¬ e.IsDiag) → Disjoint F₁ F₂ →
      fnum (F₁ ∪ F₂) ≤ fnum F₁ + fnum F₂

/-- [s1:factAdd] (c) "If `H` is the vertex-disjoint union of graphs `H_1` and `H_2`, then
`f(H) = f(H_1) + f(H_2)`." -/
def FactAddCStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H H₁ H₂ : FGraph V),
    Disjoint H₁.verts H₂.verts → H.verts = H₁.verts ∪ H₂.verts →
    H.edges = H₁.edges ∪ H₂.edges →
      fnum H.edges = fnum H₁.edges + fnum H₂.edges

/-- [s1:factAdd] (d) "Adding or deleting isolated vertices does not change `f`": if `H ≤ H'`
and `H'` has the same edges as `H` (so every vertex of `V(H') \ V(H)` is isolated in `H'`), then
`f(H') = f(H)`. -/
def FactAddDStatement : Prop :=
  ∀ (V : Type u) (H H' : FGraph V), H ≤ H' → H'.edges = H.edges → fnum H'.edges = fnum H.edges

/-- [s1:factAdd] (d) "In particular `f(n)` is non-decreasing in `n`." -/
def FactAddDMonoStatement : Prop :=
  Monotone fmax

end EG.Spec
