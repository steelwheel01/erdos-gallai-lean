module

public import EG.Defs.Prob.FinDist
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Statements of the Chernoff bounds (manuscript s1:citChernoff, s1:citChernoffGen)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, nodes `s1:citChernoff`, `s1:citChernoffGen`). No proof here.
The blueprint records the Lib theorems that prove these statements (`EG/Lib/Prob/Chernoff.lean`:
`chernoffGen_upper`, `chernoffGen_lower`, `chernoffGen_tail_exp`, `chernoff_binomial`); the
statements below use the same indicator encoding as those theorems.

Manuscript v6.1, `s1.tex`, Cited result [s1:citChernoff] ([BM, Theorem 4] (Chernoff)):
"Let `n` be an integer, `0 ≤ δ, p ≤ 1`, `X ∼ Bin(n,p)` and `μ := E X = np`. Then
`P(X > (1+δ)μ) ≤ e^{-δ²μ/3}` and `P(X < (1-δ)μ) ≤ e^{-δ²μ/2}`."

Cited result [s1:citChernoffGen] (Chernoff bounds for sums of independent indicators; [JLR00,
Theorems 2.1 and 2.8]):
"Let `X = ∑_{i=1}^m I_i` be a sum of independent indicator variables with `P(I_i = 1) = p_i` (a
Poisson-binomial variable), and let `0 ≤ δ ≤ 1`.
(a) If `μ ≥ E X` then `P(X ≥ (1+δ)μ) ≤ e^{-δ²μ/3}`; if `0 ≤ μ ≤ E X` then
`P(X ≤ (1-δ)μ) ≤ e^{-δ²μ/2}`. In particular the two bounds of Cited result s1:citChernoff hold
verbatim with `μ = E X`.
(b) If `E X ≤ μ` then for every integer `j ≥ 1`, `P(X ≥ j) ≤ μ^j/j! ≤ (eμ/j)^j`."

Formal reading.
* Probability: a finite probability space `P : EG.FinDist Ω` (the letter `μ` is kept for the
  manuscript's real number `μ`). "Independent indicator variables `I_1, …, I_m`": a family
  `I : ι → Ω → ℝ` over a finite index type `ι` (the index set `[m]`, `m = |ι|`) with values in
  `{0, 1}` that is mutually independent (`P.iIndepFun I`); `X ω = ∑ i, I i ω`. The numbers
  `p_i = P(I_i = 1)` only name the laws; they do not occur in the conclusions, so they are not
  arguments.
* s1:citChernoff: "`X ∼ Bin(n,p)`" is `X = ∑_{i ∈ Fin n} I_i` with independent indicators of
  probability `p` each. The conclusions depend only on the law of `X`, and every law
  `Bin(n,p)` arises this way (on the product space), so this is equivalent to the statement for
  an arbitrary random variable with law `Bin(n,p)` (T0 encoding choice: the binomial law is a
  Lib definition, `FinDist.binomial`, not a Defs one; blueprint hazard CH-BINDEF). The defining
  identity "`μ := E X = np`" is stated as the first conjunct.
* `e^x` is `Real.exp x`, `j!` is `Nat.factorial j`, `e = Real.exp 1`; all comparisons are in `ℝ`.
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s1:citChernoff] ([BM, Theorem 4]) "Let `n` be an integer, `0 ≤ δ, p ≤ 1`, `X ∼ Bin(n,p)`
and `μ := E X = np`. Then `P(X > (1+δ)μ) ≤ e^{-δ²μ/3}` and `P(X < (1-δ)μ) ≤ e^{-δ²μ/2}`."
Here `X = ∑_{i < n} I_i` for independent indicators `I_i` with `P(I_i = 1) = p`. -/
def ChernoffBinomialStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (n : ℕ) (p δ : ℝ) (I : Fin n → Ω → ℝ),
    0 ≤ δ → δ ≤ 1 → 0 ≤ p → p ≤ 1 →
    (∀ i ω, I i ω = 0 ∨ I i ω = 1) → P.iIndepFun I → (∀ i, P.prob {ω | I i ω = 1} = p) →
    P.expect (fun ω => ∑ i, I i ω) = n * p ∧
    P.prob {ω | (1 + δ) * (n * p) < ∑ i, I i ω} ≤ Real.exp (-(δ ^ 2 * (n * p) / 3)) ∧
    P.prob {ω | ∑ i, I i ω < (1 - δ) * (n * p)} ≤ Real.exp (-(δ ^ 2 * (n * p) / 2))

/-- [s1:citChernoffGen] (a) "Let `X = ∑_{i=1}^m I_i` be a sum of independent indicator variables
with `P(I_i = 1) = p_i` …, and let `0 ≤ δ ≤ 1`. (a) If `μ ≥ E X` then
`P(X ≥ (1+δ)μ) ≤ e^{-δ²μ/3}`; if `0 ≤ μ ≤ E X` then `P(X ≤ (1-δ)μ) ≤ e^{-δ²μ/2}`." -/
def ChernoffGenStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (ι : Type v) [Fintype ι] (I : ι → Ω → ℝ) (δ μ : ℝ),
    (∀ i ω, I i ω = 0 ∨ I i ω = 1) → P.iIndepFun I → 0 ≤ δ → δ ≤ 1 →
    (P.expect (fun ω => ∑ i, I i ω) ≤ μ →
      P.prob {ω | (1 + δ) * μ ≤ ∑ i, I i ω} ≤ Real.exp (-(δ ^ 2 * μ / 3))) ∧
    (0 ≤ μ → μ ≤ P.expect (fun ω => ∑ i, I i ω) →
      P.prob {ω | ∑ i, I i ω ≤ (1 - δ) * μ} ≤ Real.exp (-(δ ^ 2 * μ / 2)))

/-- [s1:citChernoffGen] (a) "In particular the two bounds of Cited result s1:citChernoff hold
verbatim with `μ = E X`": `P(X > (1+δ)E X) ≤ e^{-δ² E X/3}` and
`P(X < (1-δ)E X) ≤ e^{-δ² E X/2}` for a sum `X` of independent indicators and `0 ≤ δ ≤ 1`. -/
def ChernoffGenMeanStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (ι : Type v) [Fintype ι] (I : ι → Ω → ℝ) (δ : ℝ),
    (∀ i ω, I i ω = 0 ∨ I i ω = 1) → P.iIndepFun I → 0 ≤ δ → δ ≤ 1 →
    P.prob {ω | (1 + δ) * P.expect (fun ω => ∑ i, I i ω) < ∑ i, I i ω} ≤
        Real.exp (-(δ ^ 2 * P.expect (fun ω => ∑ i, I i ω) / 3)) ∧
    P.prob {ω | ∑ i, I i ω < (1 - δ) * P.expect (fun ω => ∑ i, I i ω)} ≤
        Real.exp (-(δ ^ 2 * P.expect (fun ω => ∑ i, I i ω) / 2))

/-- [s1:citChernoffGen] (b) "If `E X ≤ μ` then for every integer `j ≥ 1`,
`P(X ≥ j) ≤ μ^j/j! ≤ (eμ/j)^j`" (`X` a sum of independent indicator variables). -/
def ChernoffGenTailStatement : Prop :=
  ∀ (Ω : Type u) (P : FinDist Ω) (ι : Type v) [Fintype ι] (I : ι → Ω → ℝ) (μ : ℝ),
    (∀ i ω, I i ω = 0 ∨ I i ω = 1) → P.iIndepFun I →
    P.expect (fun ω => ∑ i, I i ω) ≤ μ →
    ∀ j : ℕ, 1 ≤ j →
      P.prob {ω | (j : ℝ) ≤ ∑ i, I i ω} ≤ μ ^ j / (j.factorial : ℝ) ∧
        μ ^ j / (j.factorial : ℝ) ≤ (Real.exp 1 * μ / j) ^ j

end EG.Spec
