module

public import EG.Defs.Walk
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Statement of Bucić–Montgomery Proposition 8 (manuscript s1:citProp8)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:citProp8`). No proof here. PLAN §3 (Ext row) lists
`BMProp8` as a cited result to be proved (from [BM, l. 393–424]); its consumer is the proof of
Lemma 9_ρ ([s3:lemL9rho], applied to `G - F` with `ℓ := ℓ_*` and `t_0 := t_{0*}`).

Manuscript v6.1, `s1.tex`, Cited result [s1:citProp8] ([BM, Proposition 8]):
"Let `1 ≤ ℓ, t ≤ n`, let `G` be an `n`-vertex graph and let `V ⊆ V(G)` satisfy `|V| ≥ 4t-2` and
`|B^ℓ_G(U,V)| > |V|/2` for every `U ⊆ V(G)` with `|U| = t`. If
`x_1, …, x_{2t-1}, y_1, …, y_{2t-1}` are distinct vertices of `G`, then for some `j ∈ [2t-1]`
there is an `x_j y_j`-path in `G` through `V` of length at most `4ℓ log n`."
(The consumer's paraphrase, `s3.tex`: "if `1 ≤ ℓ, t_0 ≤ n`, `|V| ≥ 4t_0-2`, and every set of
`t_0` vertices has a ball of radius `ℓ` in `V` of size greater than `|V|/2`, then among any
`2t_0-1` pairs of vertices, all `4t_0-2` of them distinct, some pair is joined by a path through
`V` of length at most `4ℓ log n`.")

Formal reading.
* `G : EG.FGraph V` with `n = G.card`; the manuscript's vertex set `V` is `W : Finset V` with
  `W ⊆ V(G)` (the letter `V` is the vertex type).
* `ℓ, t : ℕ`: `t` is a set size, and `ℓ` is a ball radius (s1:convGraphs (d): "an integer
  `i ≥ 0`"); the only use takes the integer `ℓ_* = ⌊2^{10}L^3⌋`. `B^ℓ_G(U,V)` is
  `EG.ball G ℓ U W`; "`> |V|/2`" is a real inequality.
* "`|V| ≥ 4t-2`" is written `4t ≤ |W| + 2` (no natural-number subtraction; equivalent).
* The `2t-1` pairs are indexed by `Fin (2t-1)` (exact, as `t ≥ 1`); "distinct vertices of `G`":
  all `x_i`, `y_i` lie in `V(G)` and the map `Sum.elim x y` on `Fin (2t-1) ⊕ Fin (2t-1)` is
  injective.
* "an `x_j y_j`-path in `G` through `V` of length at most `4ℓ log n`": a vertex list `p` with
  `EG.IsPathBetween G.edges (x j) (y j) p`, `EG.IsThrough W p` and
  `pathLength p ≤ 4ℓ log₂ n` (real inequality; `log = log₂`, s1:convGraphs (b)).
* The hypothesis `ℓ ≤ n` is not used by the proof of [BM] (blueprint note P8-UNUSEDHYP); it is
  kept for fidelity.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:citProp8] ([BM, Proposition 8]) "Let `1 ≤ ℓ, t ≤ n`, let `G` be an `n`-vertex graph and
let `V ⊆ V(G)` satisfy `|V| ≥ 4t-2` and `|B^ℓ_G(U,V)| > |V|/2` for every `U ⊆ V(G)` with
`|U| = t`. If `x_1, …, x_{2t-1}, y_1, …, y_{2t-1}` are distinct vertices of `G`, then for some
`j ∈ [2t-1]` there is an `x_j y_j`-path in `G` through `V` of length at most `4ℓ log n`." -/
def BMProp8Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (W : Finset V) (ℓ t : ℕ),
    1 ≤ ℓ → ℓ ≤ G.card → 1 ≤ t → t ≤ G.card → W ⊆ G.verts → 4 * t ≤ W.card + 2 →
    (∀ U : Finset V, U ⊆ G.verts → U.card = t →
      (W.card : ℝ) / 2 < ((ball G ℓ U W).card : ℝ)) →
    ∀ x y : Fin (2 * t - 1) → V, (∀ i, x i ∈ G.verts ∧ y i ∈ G.verts) →
      Function.Injective (Sum.elim x y) →
      ∃ (j : Fin (2 * t - 1)) (p : List V), IsPathBetween G.edges (x j) (y j) p ∧
        IsThrough W p ∧ (pathLength p : ℝ) ≤ 4 * (ℓ : ℝ) * Real.logb 2 (G.card : ℝ)

end EG.Spec
