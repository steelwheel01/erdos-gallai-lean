module

public import EG.Defs.Prob.FinDist
public import Mathlib.Analysis.Complex.Exponential

/-!
# Statement of Lemma BBD, a Bernstein inequality for bounded differences (manuscript s1:lemBBD)

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/Found/BBD.lean` proves it.

Manuscript, Lemma [s1:lemBBD] ("Lemma BBD: Bernstein inequality for bounded differences",
new in v6), s1.tex:
"Let `m ≥ 0` be an integer, let `p_1, …, p_m ∈ [0,1]`, and let `I_1, …, I_m` be independent
random variables with `P(I_k = 1) = p_k` and `P(I_k = 0) = 1 − p_k`; write
`I := (I_1, …, I_m)`. Let `Ψ : {0,1}^m → ℝ`, and let `b ≥ 0` and `c_1, …, c_m ∈ [0,b]` be such
that `|Ψ(x) − Ψ(x')| ≤ c_k` whenever `x, x' ∈ {0,1}^m` differ only in the `k`-th coordinate.
Let `β > 0` with `β ≥ ∑_{k=1}^m p_k(1 − p_k)c_k²`. Then for every `a ≥ 0`,
`P(Ψ(I) ≥ EΨ(I) + a) ≤ exp(−a²/(2(β + ba/3)))` and
`P(Ψ(I) ≤ EΨ(I) − a) ≤ exp(−a²/(2(β + ba/3)))`."

Formal reading.
* The coordinates `1, …, m` are the elements of an arbitrary finite index type `ι` (`Fintype ι`);
  `ι = Fin m` is the manuscript's case. `{0,1}^m` is `ι → Bool`, with `true` for `1` and `false`
  for `0`.
* `BBDStatement`: the canonical sample space. `I` is the identity of `ι → Bool` under the
  product law `EG.FinDist.pi (fun k => EG.FinDist.bernoulli (p k) _ _)` (the coordinates are
  independent and `P(I_k = true) = p_k`, `P(I_k = false) = 1 − p_k`, by definition of
  `bernoulli` and `pi`).
* `BBDRVStatement`: the same conclusion for random variables `I : Ω → (ι → Bool)` on an arbitrary
  finite probability space `μ : EG.FinDist Ω`, with "independent" the shared vocabulary
  `μ.iIndepFun (fun k ω => I ω k)` and `P(I_k = 1) = p_k` as `μ.prob {ω | I ω k = true} = p k`
  (then `P(I_k = 0) = 1 − p_k` holds automatically, as `I_k` is `Bool`-valued). This is the form
  used in s3:lemL17s (the indicator vector of a random subset).
* "`x, x'` differ only in the `k`-th coordinate": `∀ j, j ≠ k → x j = x' j` (this includes
  `x = x'`, for which the bound is trivial as `c_k ≥ 0`). Equivalently (given `c_k ≥ 0`, and
  up to swapping `x, x'`): `|Ψ(Function.update x k v) − Ψ(x)| ≤ c_k` for all `x` and `v`, since
  `x'` agrees with `x` off `k` exactly when `x' = Function.update x k (x' k)`. The proof uses
  this `Function.update` form (blueprint BBD-COORDS).
* The bound `exp(−a²/(2(β + ba/3)))` is `Real.exp (-(a ^ 2 / (2 * (β + b * a / 3))))`; its
  denominator is positive as `β > 0`, `a, b ≥ 0`.
-/

@[expose] public section


namespace EG.Spec

universe u v

/-- [s1:lemBBD] "Let `m ≥ 0` be an integer, let `p_1, …, p_m ∈ [0,1]`, and let `I_1, …, I_m` be
independent random variables with `P(I_k = 1) = p_k` and `P(I_k = 0) = 1 − p_k` […]. Let
`Ψ : {0,1}^m → ℝ`, and let `b ≥ 0` and `c_1, …, c_m ∈ [0,b]` be such that
`|Ψ(x) − Ψ(x')| ≤ c_k` whenever `x, x' ∈ {0,1}^m` differ only in the `k`-th coordinate. Let
`β > 0` with `β ≥ ∑_{k=1}^m p_k(1 − p_k)c_k²`. Then for every `a ≥ 0`,
`P(Ψ(I) ≥ EΨ(I) + a) ≤ exp(−a²/(2(β + ba/3)))` and
`P(Ψ(I) ≤ EΨ(I) − a) ≤ exp(−a²/(2(β + ba/3)))`."

Canonical form: the coordinates are indexed by a finite type `ι`, and `I` is the identity of
`ι → Bool` under the product of the Bernoulli laws `bernoulli (p k)`. -/
def BBDStatement : Prop :=
  ∀ (ι : Type v) [Fintype ι] (p : ι → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (Ψ : (ι → Bool) → ℝ) (b : ℝ) (c : ι → ℝ) (β a : ℝ),
    0 ≤ b → (∀ k, 0 ≤ c k ∧ c k ≤ b) →
    (∀ (k : ι) (x x' : ι → Bool), (∀ j, j ≠ k → x j = x' j) → |Ψ x - Ψ x'| ≤ c k) →
    0 < β → ∑ k, p k * (1 - p k) * c k ^ 2 ≤ β → 0 ≤ a →
    let μ := EG.FinDist.pi fun k => EG.FinDist.bernoulli (p k) (hp0 k) (hp1 k)
    μ.prob {x | μ.expect Ψ + a ≤ Ψ x} ≤ Real.exp (-(a ^ 2 / (2 * (β + b * a / 3)))) ∧
    μ.prob {x | Ψ x ≤ μ.expect Ψ - a} ≤ Real.exp (-(a ^ 2 / (2 * (β + b * a / 3))))

/-- [s1:lemBBD] (same statement as `BBDStatement`) "let `I_1, …, I_m` be independent random
variables with `P(I_k = 1) = p_k` and `P(I_k = 0) = 1 − p_k`; write `I := (I_1, …, I_m)`. […]
Then for every `a ≥ 0`, `P(Ψ(I) ≥ EΨ(I) + a) ≤ exp(−a²/(2(β + ba/3)))` and
`P(Ψ(I) ≤ EΨ(I) − a) ≤ exp(−a²/(2(β + ba/3)))`."

Random-variable form: `I : Ω → (ι → Bool)` on a finite probability space `μ`, with mutually
independent coordinates `I · k` and `P(I_k = true) = p_k`. -/
def BBDRVStatement : Prop :=
  ∀ (Ω : Type u) (μ : EG.FinDist Ω) (ι : Type v) [Fintype ι] (p : ι → ℝ) (I : Ω → ι → Bool)
    (Ψ : (ι → Bool) → ℝ) (b : ℝ) (c : ι → ℝ) (β a : ℝ),
    (∀ k, 0 ≤ p k ∧ p k ≤ 1) →
    μ.iIndepFun (fun k ω => I ω k) → (∀ k, μ.prob {ω | I ω k = true} = p k) →
    0 ≤ b → (∀ k, 0 ≤ c k ∧ c k ≤ b) →
    (∀ (k : ι) (x x' : ι → Bool), (∀ j, j ≠ k → x j = x' j) → |Ψ x - Ψ x'| ≤ c k) →
    0 < β → ∑ k, p k * (1 - p k) * c k ^ 2 ≤ β → 0 ≤ a →
    μ.prob {ω | μ.expect (fun ω => Ψ (I ω)) + a ≤ Ψ (I ω)} ≤
        Real.exp (-(a ^ 2 / (2 * (β + b * a / 3)))) ∧
      μ.prob {ω | Ψ (I ω) ≤ μ.expect (fun ω => Ψ (I ω)) - a} ≤
        Real.exp (-(a ^ 2 / (2 * (β + b * a / 3))))

end EG.Spec
