module

public import EG.Defs.Expander

/-!
# Statement of Proposition 13* (stars or bipartite; manuscript s3:propP13s)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3a (`formal/work/p2s/s3a.md`; blueprint
`formal/work/p2/blueprint_s3a.md`, node `s3:propP13s`). No proof here. Consumer: Lemma 17*
([s3:lemL17s], Step 2, with the (eqStar) values, whose parameter hypotheses are
`EG.Spec.StarP13sParamsStatement`, `EG/Spec/Link/Star.lean`, written in this Spec's form).

Manuscript v6.1, `s3.tex`, Proposition [s3:propP13s]:
"Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, and put
`L := log n`. Let `W ⊆ V(G)` with `1 ≤ |W| ≤ 2n/3`, and let `F ⊆ E(G)` with `|F| ≤ s_1|W|/4`. Let
`σ_* > 0` be real and let `λ_*,d_* ≥ 1` and `Δ_* ≥ λ_*` be integers such that
`σ_* ≥ 24L^2/ε'`, `Δ_*−λ_* ≥ 8d_*λ_*L^2/(ε'σ_*)`, `s_1 ≥ 8d_*λ_*`.
Then `G−F` contains one of the following:
(a) at least `|W|/σ_*` vertex-disjoint stars, each with exactly `λ_*` leaves, its centre in `W`
and all its leaves in `V(G) \ W`; or
(b) a bipartite subgraph `H ⊆ G−F` with sides `W` and `X ⊆ V(G) \ W`, such that
`|X| ≥ ε'|W|/(2L^2)`, every vertex of `X` has degree exactly `d_*` in `H`, and every vertex of
`W` has degree at most `Δ_*` in `H`."

Formal reading (encoding decision P13-STAR-ENCODING of the blueprint).
* `n = G.card`, `L = Real.logb 2 n`; `ε', s₁, σ` real; `λ_*, d_*, Δ_*` are natural numbers
  `lam, d, Δ` (they are positive integers under the hypotheses `1 ≤ lam`, `1 ≤ d`, `lam ≤ Δ`);
  `Δ_*−λ_*` is the real difference. All comparisons are real inequalities.
* `G − F` is `G.deleteEdges F`.
* (a): a set `C ⊆ W` of centres with `|C| ≥ |W|/σ_*` and a leaf map `lv : V → Finset V`; the star
  with centre `c ∈ C` has exactly `λ_*` leaves `lv c ⊆ V(G) \ W`, each adjacent to `c` in `G − F`;
  the leaf sets of distinct centres are disjoint. The stars are then vertex-disjoint (centres are
  distinct elements of `W`, leaves lie outside `W`), and conversely vertex-disjoint stars give such
  data, so this is the manuscript's (a).
* (b): `X ⊆ V(G) \ W` and a graph `H` with `H ≤ G − F`, `V(H) = W ∪ X`, and every edge of `H`
  joining `W` to `X` (`E(H) ⊆ E_G(W,X)`): a bipartite subgraph with sides `W` and `X`. Degrees are
  `H.deg` (neighbours in `H`).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s3:propP13s] Proposition 13*: "Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and
`2^{-7} ≤ ε' ≤ 1`, and put `L := log n`. Let `W ⊆ V(G)` with `1 ≤ |W| ≤ 2n/3`, and let
`F ⊆ E(G)` with `|F| ≤ s_1|W|/4`. Let `σ_* > 0` be real and let `λ_*,d_* ≥ 1` and `Δ_* ≥ λ_*` be
integers such that `σ_* ≥ 24L^2/ε'`, `Δ_*−λ_* ≥ 8d_*λ_*L^2/(ε'σ_*)`, `s_1 ≥ 8d_*λ_*`. Then `G−F`
contains one of the following: (a) at least `|W|/σ_*` vertex-disjoint stars, each with exactly
`λ_*` leaves, its centre in `W` and all its leaves in `V(G) \ W`; or (b) a bipartite subgraph
`H ⊆ G−F` with sides `W` and `X ⊆ V(G) \ W`, such that `|X| ≥ ε'|W|/(2L^2)`, every vertex of `X`
has degree exactly `d_*` in `H`, and every vertex of `W` has degree at most `Δ_*` in `H`." -/
def P13sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (ε' s₁ σ : ℝ) (lam d Δ : ℕ) (W : Finset V)
    (F : Finset (Sym2 V)),
    G.IsExpander ε' s₁ → 2 ≤ G.card → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 →
    W ⊆ G.verts → 1 ≤ W.card → (W.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 →
    F ⊆ G.edges → (F.card : ℝ) ≤ s₁ * (W.card : ℝ) / 4 →
    0 < σ → 1 ≤ lam → 1 ≤ d → lam ≤ Δ →
    24 * Real.logb 2 (G.card : ℝ) ^ 2 / ε' ≤ σ →
    8 * (d : ℝ) * (lam : ℝ) * Real.logb 2 (G.card : ℝ) ^ 2 / (ε' * σ) ≤ (Δ : ℝ) - (lam : ℝ) →
    8 * (d : ℝ) * (lam : ℝ) ≤ s₁ →
    -- (a) vertex-disjoint stars
    (∃ (C : Finset V) (lv : V → Finset V), C ⊆ W ∧ (W.card : ℝ) / σ ≤ (C.card : ℝ) ∧
      (∀ c ∈ C, (lv c).card = lam ∧ lv c ⊆ G.verts \ W ∧
        ∀ x ∈ lv c, (G.deleteEdges F).Adj c x) ∧
      (C : Set V).PairwiseDisjoint lv) ∨
    -- (b) a bipartite subgraph with sides `W` and `X`
    (∃ (X : Finset V) (H : FGraph V), X ⊆ G.verts \ W ∧ H ≤ G.deleteEdges F ∧
      H.verts = W ∪ X ∧ H.edges ⊆ G.edgesBetween W X ∧
      ε' * (W.card : ℝ) / (2 * Real.logb 2 (G.card : ℝ) ^ 2) ≤ (X.card : ℝ) ∧
      (∀ x ∈ X, H.deg x = d) ∧ (∀ w ∈ W, H.deg w ≤ Δ))

end EG.Spec
