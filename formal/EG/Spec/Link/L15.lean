module

public import EG.Defs.Expander
public import EG.Defs.Prob.FinDist

/-!
# Statement of Lemma 15⁺, random splitting of expanders (manuscript s3:lemL15p)

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/Link/L15.lean` proves it.

Manuscript, Lemma [s3:lemL15p] ("Lemma 15⁺: random splitting without loss"), s3.tex:
"Let `X` be an `N`-vertex `(ε′,s)`-expander with `0 < ε′ ≤ 1`, put `L := log N`, and let `k ≥ 1`
be an integer with `s ≥ 40kL`. Give every edge of `X` a colour from `[k]`, independently and
uniformly at random, and for `i ∈ [k]` let `X_i` be the graph with vertex set `V(X)` whose edges
are the edges of colour `i`. Then for each `i ∈ [k]`, `X_i` is an `(ε′,s/(2k))`-expander with
probability at least `1 − 2N^{−5}`. Hence all `k` classes are `(ε′,s/(2k))`-expanders with
probability at least `1 − 2kN^{−5}`."

Formal reading.
* "`N`-vertex `(ε′,s)`-expander": `X : EG.FGraph V` with `N = |X| = X.card` and
  `X.IsExpander ε' s` (Definition 11, [s1:citDef11]); `ε' s : ℝ`.
* `L := log N` is `Real.logb 2 N` (logarithms to base 2, [s1:convGraphs] (b)).
* "`k ≥ 1` an integer": `k : ℕ` with `[NeZero k]` (required by `EG.FinDist.randColouring`).
* "Give every edge of `X` a colour from `[k]`, independently and uniformly at random": the sample
  space is `EG.FinDist.randColouring X.edges k`, the uniform product distribution on the
  colourings `c : ↥X.edges → Fin k` of the edge finset (colours `Fin k = {0, …, k-1}` in place of
  `[k]`).
* "`X_i` is the graph with vertex set `V(X)` whose edges are the edges of colour `i`":
  `X.restrictEdges (EG.FinDist.selectSet X.edges fun e => decide (c e = i))`; its vertex set is
  `X.verts` and its edge set is `{e ∈ E(X) | c e = i}` (`EG.FinDist.mem_selectSet`,
  `EG.FGraph.mem_restrictEdges_edges`).
* `N^{−5}` is `(N : ℝ) ^ (-5 : ℤ)`. There is no size condition on `N` in the manuscript (its proof
  treats `N = 1` separately). For `N = 0` Lean reads `0 ^ (-5) = 0`, and the statement holds as
  every graph without vertices is an expander (no `U` has `1 ≤ |U| ≤ 0`).
* Both conclusions are stated: the per-colour bound (first conjunct) and the bound for all `k`
  classes simultaneously (second conjunct).
-/

@[expose] public section


namespace EG.Spec

universe u

/-- [s3:lemL15p] "Let `X` be an `N`-vertex `(ε′,s)`-expander with `0 < ε′ ≤ 1`, put
`L := log N`, and let `k ≥ 1` be an integer with `s ≥ 40kL`. Give every edge of `X` a colour from
`[k]`, independently and uniformly at random, and for `i ∈ [k]` let `X_i` be the graph with vertex
set `V(X)` whose edges are the edges of colour `i`. Then for each `i ∈ [k]`, `X_i` is an
`(ε′,s/(2k))`-expander with probability at least `1 − 2N^{−5}`. Hence all `k` classes are
`(ε′,s/(2k))`-expanders with probability at least `1 − 2kN^{−5}`."
Here `N = X.card`, `L = Real.logb 2 N`, the colouring is `EG.FinDist.randColouring X.edges k`
(colours `Fin k`), and `X_i = X.restrictEdges (selectSet X.edges fun e => decide (c e = i))`. -/
def L15pStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : EG.FGraph V) (ε' s : ℝ) (k : ℕ) [NeZero k],
    0 < ε' → ε' ≤ 1 → 40 * (k : ℝ) * Real.logb 2 (X.card : ℝ) ≤ s → X.IsExpander ε' s →
    (∀ i : Fin k,
      1 - 2 * (X.card : ℝ) ^ (-5 : ℤ) ≤
        (EG.FinDist.randColouring X.edges k).prob
          {c | (X.restrictEdges (EG.FinDist.selectSet X.edges fun e => decide (c e = i))).IsExpander
            ε' (s / (2 * (k : ℝ)))}) ∧
    1 - 2 * (k : ℝ) * (X.card : ℝ) ^ (-5 : ℤ) ≤
      (EG.FinDist.randColouring X.edges k).prob
        {c | ∀ i : Fin k,
          (X.restrictEdges (EG.FinDist.selectSet X.edges fun e => decide (c e = i))).IsExpander
            ε' (s / (2 * (k : ℝ)))}

end EG.Spec
