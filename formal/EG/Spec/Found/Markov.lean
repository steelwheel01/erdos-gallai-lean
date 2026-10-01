module

public import EG.Defs.Prob.FinDist

/-!
# Statements of Markov's inequality and its two uses (manuscript s1:citMarkov)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:citMarkov`). No proof here. The blueprint records the
Lib theorems that prove these statements (`EG/Lib/Prob/Basic.lean`: `prob_le_expect_div`,
`two_thirds_le_prob_le_three_mul_expect`, `half_le_prob_le_four_mul_expect_and`).

Manuscript v6.1, `s1.tex`, Cited result [s1:citMarkov] ("Markov's inequality and its two uses"):
"If `X ≥ 0` and `a > 0` then `P(X ≥ a) ≤ E X/a`. Consequently:
(a) for `X ≥ 0`, `P(X ≤ 3 E X) ≥ 2/3`;
(b) for `X_1, X_2 ≥ 0`, `P(X_1 ≤ 4 E X_1 and X_2 ≤ 4 E X_2) ≥ 1/2`;
(c) (a) and (b) hold with `P` and `E` replaced by the conditional probability and expectation
given any event of positive probability, or given any fixed outcome of variables that are
independent of the variables being drawn."

Formal reading.
* A finite probability space `P : EG.FinDist Ω`; a random variable is `X : Ω → ℝ`; "`X ≥ 0`" is
  `∀ ω, 0 ≤ X ω` (surely, the literal reading).
* (c) The conditional probability space given an event `A` with `P(A) > 0` is `P.cond A hA`
  (`EG.FinDist.cond`); `MarkovCondStatement` states (a) and (b) for it, with conditional
  probability and conditional expectation. "Given any fixed outcome of variables that are
  independent of the variables being drawn" is the case `A = {ω | Y ω = y}` of an event of
  positive probability, so it is covered by `MarkovCondStatement` (that the conditional law of
  the drawn variables is then their unconditional law, which the derivation mentions, is a Lib
  fact, e.g. `EG.FinDist.map_snd_cond_prod_fst`, and not part of the statement).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:citMarkov] "If `X ≥ 0` and `a > 0` then `P(X ≥ a) ≤ E X/a`." -/
def MarkovStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (X : Ω → ℝ) (a : ℝ),
    (∀ ω, 0 ≤ X ω) → 0 < a → P.prob {ω | a ≤ X ω} ≤ P.expect X / a

/-- [s1:citMarkov] (a) "for `X ≥ 0`, `P(X ≤ 3 E X) ≥ 2/3`". -/
def MarkovAStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (X : Ω → ℝ),
    (∀ ω, 0 ≤ X ω) → 2 / 3 ≤ P.prob {ω | X ω ≤ 3 * P.expect X}

/-- [s1:citMarkov] (b) "for `X_1, X_2 ≥ 0`, `P(X_1 ≤ 4 E X_1 and X_2 ≤ 4 E X_2) ≥ 1/2`". -/
def MarkovBStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (X₁ X₂ : Ω → ℝ),
    (∀ ω, 0 ≤ X₁ ω) → (∀ ω, 0 ≤ X₂ ω) →
      1 / 2 ≤ P.prob {ω | X₁ ω ≤ 4 * P.expect X₁ ∧ X₂ ω ≤ 4 * P.expect X₂}

/-- [s1:citMarkov] (c) "(a) and (b) hold with `P` and `E` replaced by the conditional
probability and expectation given any event of positive probability, or given any fixed outcome
of variables that are independent of the variables being drawn" (the latter is the event
`{Y = y}`, of positive probability). -/
def MarkovCondStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (A : Set Ω) (hA : 0 < P.prob A) (X X₁ X₂ : Ω → ℝ),
    (∀ ω, 0 ≤ X ω) → (∀ ω, 0 ≤ X₁ ω) → (∀ ω, 0 ≤ X₂ ω) →
    2 / 3 ≤ (P.cond A hA).prob {ω | X ω ≤ 3 * (P.cond A hA).expect X} ∧
      1 / 2 ≤ (P.cond A hA).prob
        {ω | X₁ ω ≤ 4 * (P.cond A hA).expect X₁ ∧ X₂ ω ≤ 4 * (P.cond A hA).expect X₂}

end EG.Spec
