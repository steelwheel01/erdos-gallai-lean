module

public import EG.Defs.Expander
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Statement of Theorem 16* (b): the hypotheses force `ρN` large (manuscript s3:thmT16s (b))

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3b (`formal/work/p2s/s3b.md`). The main
statement of Theorem 16* is `EG.Spec.T16sStatement` (`EG/Spec/Link/T16s.lean`, written by probe
unit P4B, reused unchanged). This file states item (b), the only item of (a)–(c) with a
mathematical claim of its own; it has no consumer (blueprint s3b, T16-STEP0-NO-RPOW: "optional,
(b) (no consumer)"). Item (a) ("the constant `2^{86}` … is absolute. No lower bound on `N` is
needed") is reflected by `T16sStatement` having no hypothesis on `N`; item (c) is a remark on the
proof (TRIAGE §1a T16-C-META: not formalized).

Manuscript v6.1, `s3.tex`, Theorem [s3:thmT16s]: "Let `X` be an `N`-vertex `(ε′,s)`-expander with
`ε′ ∈ [2^{-7},1]`, and put `L := log N`. Let `ρ ∈ (0,1]` and `t ≥ 1` … Suppose that `ρN ≥ L^2`
and `s ≥ 2^{135}tL^{28}ρ^{-5}`. … Moreover: … (b) If `N ≥ 2`, the hypotheses force
`ρN > 2^{27}L^{5.6}N^{4/5}`, because `s < N`. In particular the hypothesis `ρN ≥ L^2` is implied
by the others; it is kept only for comparison with [BM, Theorem 16]."

Formal reading.
* "the hypotheses" are those of the theorem that concern `X, s, ρ, t`; the `ρ`-random set plays no
  role in (b). Since the item says that `ρN ≥ L^2` "is implied by the others", the statement is
  made **without** the hypothesis `ρN ≥ L^2` and concludes both `ρN > 2^{27}L^{5.6}N^{4/5}` and
  `ρN ≥ L^2` ("In particular"). This is the stronger reading; the weaker one (with `ρN ≥ L^2`
  assumed) follows.
* `L^{5.6}` and `N^{4/5}` are `Real.rpow` with the exact exponents `28/5` and `4/5`; `ρ^{-5}` is
  an integer power, as in `T16sStatement`.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s3:thmT16s] (b) "If `N ≥ 2`, the hypotheses force `ρN > 2^{27}L^{5.6}N^{4/5}`, because
`s < N`. In particular the hypothesis `ρN ≥ L^2` is implied by the others": for an `N`-vertex
`(ε′,s)`-expander `X` with `ε′ ∈ [2^{-7},1]`, `ρ ∈ (0,1]`, `t ≥ 1`,
`s ≥ 2^{135}tL^{28}ρ^{-5}` and `N ≥ 2`. -/
def T16sForcedStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (X : FGraph V) (ε' s ρ t : ℝ),
    (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → X.IsExpander ε' s →
    0 < ρ → ρ ≤ 1 → 1 ≤ t →
    (2 : ℝ) ^ 135 * t * Real.logb 2 (X.card : ℝ) ^ 28 * ρ ^ (-5 : ℤ) ≤ s →
    2 ≤ X.card →
    (2 : ℝ) ^ 27 * Real.logb 2 (X.card : ℝ) ^ (28 / 5 : ℝ) * (X.card : ℝ) ^ (4 / 5 : ℝ) <
        ρ * (X.card : ℝ) ∧
      Real.logb 2 (X.card : ℝ) ^ 2 ≤ ρ * (X.card : ℝ)

end EG.Spec
