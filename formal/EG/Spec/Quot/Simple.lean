module

public import EG.Defs.Quot.Round

/-!
# Statement of Lemma "`Q_l` is simple" (manuscript s7:lemSimple) — probe P-1

Statement file (`EG/Spec/**`), unit P1 (probe P-1: s7 lift, `Q_l` simple, MULT, WellDef; J⁺
assumed through `RoundInput.Valid`). Design note: `formal/work/p2b/P1.md`. Proof (stage 2):
`EG/Proof/Quot/Simple.lean`.

Manuscript v6.1, `s7.tex`, Lemma [s7:lemSimple]:
"Every sub-layer of Construction s7:consRound(g) is a simple graph: it has no parallel edges, PAR
sub-layers have no loops, and HUB sub-layers are bipartite between hubs and junction copies `[w]`,
where the hub `h` and the junction `w` of any edge `h[w]` are distinct vertices of `G`.
Consequently `Q_l` is a simple graph without isolated vertices."
Construction [s7:consRound] (g): "For `κ ∈ [3M_l]` the *PAR layer* `B^P_κ` is the multigraph on the
vertex set `{[w] : w ∈ Pool_l}` … For `κ ∈ [4M_l]` the *HUB layer* `B^H_κ` is the bipartite
multigraph with sides `D_l` and `{[w] : w ∈ Pool_l}` … *Rank split:* … The *quotient* `Q_l` is the
vertex-disjoint union of all sub-layers `B^{P,(ι)}_κ` (`κ ∈ [3M_l]`, `ι ≥ 1`) and `B^{H,(ι)}_κ`
(`κ ∈ [4M_l]`, `ι ≥ 1`), with the isolated vertices of each sub-layer deleted. Vertices of distinct
sub-layers are distinct vertices of `Q_l`".

Formal reading (TRIAGE §2.10; design note `work/p2d/quot.md` D-Q-11).
* "For every past" is `∀ I : RoundInput V, I.Valid → ∀ R : Rules I, R.Valid → ∀ ξ` (every
  admissible choice of the fixed rules, every round randomness).
* `Q_l = R.Q ξ : FGraph (QVert V)`. A vertex of `Q_l` is a tagged copy `(t, v)`, `t = (kind, κ, ι,
  side)`; the sub-layer of a copy is `(kind, κ, ι)`. `FGraph` is simple by construction (a `Finset`
  of non-diagonal `Sym2`), so "simple" has two substantive parts, stated here:
  - **no parallel edges** = *rank injectivity*: two layer edges (PAR objects / coloured hub items)
    that give the same edge of `Q_l` in their rank sub-layer are equal (the `Finset` of edges would
    otherwise silently merge parallel edges, and an item would be lost);
  - **no loops / bipartite**: an unpaid PAR object has distinct junctions `w₁ ≠ w₂`; a HUB edge
    `h[w]` has `h ∈ D_l`, `w ∈ Pool_l` and `h ≠ w` in `G`; every edge joins two copies of one
    sub-layer (with `ι ≥ 1`, `κ < 3M_l` resp. `κ < 4M_l`), PAR edges join two junction copies, HUB
    edges a hub copy and a junction copy; every hub copy is a copy of a hub `h ∈ D_l` and every
    junction copy (PAR or HUB) a copy `[w]` of a vertex `w ∈ Pool_l` (so the bipartition "between
    hubs and junction copies" is stated in the conjunct itself; fix round 1, review issue C1).
* "without isolated vertices" is `∀ v ∈ V(Q_l), ∃ e ∈ E(Q_l), v ∈ e`.
* Conjuncts (2), (5) and (6) hold for every `I`, `R`, `ξ` by definition, without any validity
  hypothesis (`unpaidPar` = not `Looped`; `FGraph.loopless`; `Q.verts` is the set of ends of
  edges). They are kept because they mirror TeX sentences whose TeX proofs are also one line; they
  carry no proof content. The substantive conjuncts are (1) rank injectivity, (3) the HUB edge
  facts and (4) the sub-layer tags (second review of P1, cosmetic C1).
-/

@[expose] public section

namespace EG.Spec

open EG.Quot

/-- [s7:lemSimple] "Every sub-layer of Construction s7:consRound(g) is a simple graph: it has no
parallel edges, PAR sub-layers have no loops, and HUB sub-layers are bipartite between hubs and
junction copies `[w]`, where the hub `h` and the junction `w` of any edge `h[w]` are distinct
vertices of `G`. Consequently `Q_l` is a simple graph without isolated vertices."
(For every valid past `I`, every valid choice `R` of the fixed rules and every `ξ`.) -/
def QuotSimpleStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
    ∀ ξ : Xi I.G I.M,
      -- no parallel edges (rank injectivity): a `Q_l`-edge comes from exactly one layer edge
      (∀ e ∈ R.layerEdges ξ, ∀ e' ∈ R.layerEdges ξ, ∀ q : Sym2 (QVert V),
          R.qEdge ξ (R.rank ξ e) e = some q → R.qEdge ξ (R.rank ξ e') e' = some q → e = e') ∧
      -- PAR sub-layers have no loops: the two junctions of an unpaid PAR object differ
      -- (definitional: `unpaidPar` keeps exactly the objects that are not `Looped`, i.e. whose
      -- two ends did not receive the same junction; the TeX proof is equally one line, "looped
      -- PAR objects were paid in (e3)"; fix round 1 of the second review, C1)
      (∀ o ∈ R.unpaidPar ξ, ∀ w₁ w₂ : V, R.junction ξ (.par o false) = some w₁ →
          R.junction ξ (.par o true) = some w₂ → w₁ ≠ w₂) ∧
      -- HUB edges `h[w]`: `h ∈ D_l`, `w ∈ Pool_l`, and `h ≠ w` as vertices of `G`
      (∀ it ∈ R.colouredHub ξ.1, ∀ w : V, R.junction ξ (.hub it.1 it.2) = some w →
          it.1 ∈ I.hubs ∧ w ∈ I.pool ∧ it.1 ≠ w) ∧
      -- every edge lies in one sub-layer `(kind, κ, ι)` with `ι ≥ 1` and `κ` in the palette;
      -- PAR edges join junction copies; HUB edges join a hub copy and a junction copy;
      -- a hub copy (side `true`) is a copy of a hub `h ∈ D_l`, a junction copy (side `false`,
      -- PAR or HUB) is a copy `[w]` of a vertex `w ∈ Pool_l` (fix round 1, C1)
      (∀ a b : QVert V, s(a, b) ∈ (R.Q ξ).edges →
          a.1.1 = b.1.1 ∧ a.1.2.1 = b.1.2.1 ∧ a.1.2.2.1 = b.1.2.2.1 ∧ 1 ≤ a.1.2.2.1 ∧
          (a.1.1 = false → a.1.2.1 < 3 * I.M ∧ a.1.2.2.2 = false ∧ b.1.2.2.2 = false) ∧
          (a.1.1 = true → a.1.2.1 < 4 * I.M ∧ a.1.2.2.2 ≠ b.1.2.2.2) ∧
          (∀ x : QVert V, x = a ∨ x = b →
            (x.1.2.2.2 = true → x.2 ∈ I.hubs) ∧ (x.1.2.2.2 = false → x.2 ∈ I.pool))) ∧
      -- `Q_l` is a simple graph (no loops) without isolated vertices (both conjuncts are
      -- definitional: the `FGraph` fields `loopless` and `verts = ⋃ edges` of `R.Q ξ`; they
      -- mirror the TeX's "with their isolated vertices deleted". The substantive content of the
      -- lemma is in conjuncts (1), (3) and (4); fix round 1 of the second review, C1)
      (∀ e ∈ (R.Q ξ).edges, ¬ e.IsDiag) ∧
      (∀ v ∈ (R.Q ξ).verts, ∃ e ∈ (R.Q ξ).edges, v ∈ e)

end EG.Spec
