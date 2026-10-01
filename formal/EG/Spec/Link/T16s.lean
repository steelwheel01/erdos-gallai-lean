module

public import EG.Defs.Expander
public import EG.Defs.Prob.FinDist

/-!
# Statement of Theorem 16* (linking through random sets, for-all multiset form; s3:thmT16s)

Statement file (`EG/Spec/**`) of probe unit P4B (probe P-4, part 2). A DECLARED INPUT of the probe:
it is applied once per U-index in the proof of Lemma COL (c) ([s3:lemCOL], "For a fixed index,
apply Theorem s3:thmT16s to the fixed class `LU_{Y,l,c,σ}` …"), which is a P4B node
(`EG.Spec.COLcIndexStatement`). Its own proof (about 3000 lines: Lemma 15⁺, Proposition 13*,
Lemma 17*, Proposition 18*, Lemma 9_ρ) is the s3 Theorem-16* unit's job. No Spec of s3:thmT16s
existed before this file. Design note `formal/work/p2b/P4B.md`.

Manuscript v6.1, `s3.tex`, Theorem [s3:thmT16s]:
"Let `X` be an `N`-vertex `(ε′,s)`-expander with `ε′ ∈ [2^{-7},1]`, and put `L := log N`. Let
`ρ ∈ (0,1]` and `t ≥ 1`, and let `V` be a `ρ`-random subset of `V(X)`. Here `X` is fixed; if `X`
was itself produced at random, `V` is independent of that randomness. Suppose that
`ρN ≥ L^2` and `s ≥ 2^{135} t L^{28} ρ^{-5}`.
Then, with probability at least `1 - 2^{86} t L^{19} ρ^{-3} N^{-3}`, the graph `X` is
`(2^{12}L^4, t)`-path connected through `V`. That is, for *every* multiset `𝒫` of pairs of distinct
vertices of `X` (endpoints anywhere, in `V` or not) in which each vertex lies in at most `t`
pairs, there are pairwise edge-disjoint paths of `X`, one for each pair of `𝒫`, each joining its
pair, of length at most `2^{12}L^4`, and with all interior vertices in `V`. …"
Items (a)–(c) (remarks on the constants and on the proof) are not part of the statement.

Formal reading:
* `N = X.card`, `L = log₂ N` (`Real.logb 2`; `log = log₂` throughout the manuscript);
* "`V` is a `ρ`-random subset of `V(X)`": a random set `W : Ω → Finset V` on any finite
  probability space `μ` with `μ.IsRSubset W X.verts ρ` (its law is `rsubset X.verts ρ`); `X` is a
  fixed graph. The conditional use ("if `X` was itself produced at random, `V` is independent of
  that randomness") is the consumer's conditioning step (`COLcIndexStatement`);
* `t` is real with `t ≥ 1` (the path-connectivity predicate `EG.FGraph.IsPathConnected` takes a
  real multiplicity bound and counts occurrences, the multiset clause of s1:citDef7);
* `ρ^{-5}`, `ρ^{-3}`, `N^{-3}` are integer powers (`zpow`).
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s3:thmT16s] Theorem 16*: "Let `X` be an `N`-vertex `(ε′,s)`-expander with `ε′ ∈ [2^{-7},1]`,
and put `L := log N`. Let `ρ ∈ (0,1]` and `t ≥ 1`, and let `V` be a `ρ`-random subset of `V(X)`.
… Suppose that `ρN ≥ L^2` and `s ≥ 2^{135} t L^{28} ρ^{-5}`. Then, with probability at least
`1 - 2^{86} t L^{19} ρ^{-3} N^{-3}`, the graph `X` is `(2^{12}L^4, t)`-path connected through
`V`." -/
def T16sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : FGraph V) (ε' s ρ t : ℝ) (Ω : Type v) (μ : FinDist Ω)
    (W : Ω → Finset V),
    (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → X.IsExpander ε' s →
    0 < ρ → ρ ≤ 1 → 1 ≤ t → μ.IsRSubset W X.verts ρ →
    Real.logb 2 (X.card : ℝ) ^ 2 ≤ ρ * (X.card : ℝ) →
    (2 : ℝ) ^ 135 * t * Real.logb 2 (X.card : ℝ) ^ 28 * ρ ^ (-5 : ℤ) ≤ s →
    1 - (2 : ℝ) ^ 86 * t * Real.logb 2 (X.card : ℝ) ^ 19 * ρ ^ (-3 : ℤ) * (X.card : ℝ) ^ (-3 : ℤ) ≤
      μ.prob {ω | X.IsPathConnected ((2 : ℝ) ^ 12 * Real.logb 2 (X.card : ℝ) ^ 4) t (W ω)}

end EG.Spec
