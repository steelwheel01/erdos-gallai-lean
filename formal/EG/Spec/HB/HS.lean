module

public import EG.Defs.Expander

/-!
# Statement of Lemma HS (manuscript s2:lemHS)

Statement file (`EG/Spec/**`), unit P2 specs chunk s2a. Status note `formal/work/p2s/s2a.md`.
Blueprint `formal/work/p2/blueprint_s2a.md`, node `s2:lemHS`.

Manuscript v6.1, `s2.tex`, Lemma [s2:lemHS] (Lemma HS):
"Let `ε' > 0` and `s ≥ 0`, let `X` be an `(ε',s)`-expander on a vertex set of size `z ≥ 11`, let
`W ⊆ V(X)` with `|W| ≤ z/2`, and suppose every `u ∈ V(X) \ W` has at most `s_W ≤ s` neighbours
in `W` in `X`. Then `X - W` is an `(ε'(log z'/log z)², s - s_W)`-expander on `z' := z - |W|`
vertices, and `ε'(log z'/log z)² ≥ ε'/2`. In particular, if `X` is a `(2^{-5},s)`-expander and
`s_W = s/2`, then `X - W` is a spanning `(2^{-6},s/2)`-expander of `V(X) \ W`."

Formal reading.
* `log = log₂`; `z = X.card`; `X - W = X.deleteVerts W` (`= X[V(X) \ W]`, s1:convGraphs (c));
  "neighbours in `W` in `X`" is `X.nbrs u ∩ W`. `s`, `s_W`, `ε'` are reals.
* "on `z' := z - |W|` vertices" is the conjunct `(X.deleteVerts W).card = X.card - W.card`
  (natural numbers; exact since `W ⊆ V(X)`), and the expansion parameter is written with the real
  number `z' = (X.card : ℝ) - W.card` (Def 11 of `X - W` uses `log₂` of its own vertex count,
  which is this `z'`; blueprint HS-CARD).
* "a spanning `(2^{-6},s/2)`-expander of `V(X) \ W`" is `(X - W).verts = V(X) \ W ∧
  (X - W).IsExpander (2^{-6}) (s/2)` (CONVENTIONS "spanning expander"). The two constants are
  written `(2 : ℝ) ^ (-5 : ℤ)`, `(2 : ℝ) ^ (-6 : ℤ)`, as in `EG.HB.Run.ancEps` (the consumer,
  s2:propStructure (i), applies the corollary to `X = X^0_Z`, `W = S_Z`, `s = s_l`).
* The corollary keeps the standing hypotheses of the lemma (`s ≥ 0`, `z ≥ 11`, `W ⊆ V(X)`,
  `|W| ≤ z/2`) and sets `s_W = s/2`.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s2:lemHS] "Let `ε' > 0` and `s ≥ 0`, let `X` be an `(ε',s)`-expander on a vertex set of size
`z ≥ 11`, let `W ⊆ V(X)` with `|W| ≤ z/2`, and suppose every `u ∈ V(X) \ W` has at most
`s_W ≤ s` neighbours in `W` in `X`. Then `X - W` is an `(ε'(log z'/log z)², s - s_W)`-expander on
`z' := z - |W|` vertices, and `ε'(log z'/log z)² ≥ ε'/2`." -/
def HSStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : FGraph V) (W : Finset V) (ε' s sW : ℝ),
    0 < ε' → 0 ≤ s → 11 ≤ X.card → X.IsExpander ε' s → W ⊆ X.verts →
    (W.card : ℝ) ≤ (X.card : ℝ) / 2 → sW ≤ s →
    (∀ u ∈ X.verts \ W, ((X.nbrs u ∩ W).card : ℝ) ≤ sW) →
      (X.deleteVerts W).card = X.card - W.card ∧
      (X.deleteVerts W).IsExpander
        (ε' * (Real.logb 2 ((X.card : ℝ) - W.card) / Real.logb 2 X.card) ^ 2) (s - sW) ∧
      ε' / 2 ≤ ε' * (Real.logb 2 ((X.card : ℝ) - W.card) / Real.logb 2 X.card) ^ 2

/-- [s2:lemHS] (last sentence) "In particular, if `X` is a `(2^{-5},s)`-expander and
`s_W = s/2`, then `X - W` is a spanning `(2^{-6},s/2)`-expander of `V(X) \ W`" (with the
standing hypotheses `s ≥ 0`, `z ≥ 11`, `W ⊆ V(X)`, `|W| ≤ z/2` of the lemma). -/
def HSCorStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : FGraph V) (W : Finset V) (s : ℝ),
    0 ≤ s → 11 ≤ X.card → X.IsExpander ((2 : ℝ) ^ (-5 : ℤ)) s → W ⊆ X.verts →
    (W.card : ℝ) ≤ (X.card : ℝ) / 2 →
    (∀ u ∈ X.verts \ W, ((X.nbrs u ∩ W).card : ℝ) ≤ s / 2) →
      (X.deleteVerts W).verts = X.verts \ W ∧
      (X.deleteVerts W).IsExpander ((2 : ℝ) ^ (-6 : ℤ)) (s / 2)

end EG.Spec
