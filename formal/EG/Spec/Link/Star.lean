module

public import EG.Defs.Link.Star
public import EG.Defs.Prob.FinDist

/-!
# Statements of the facts (S1), (S2), (S4)–(S6) about the (eqStar) parameters (manuscript s3:eqStar)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3a (`formal/work/p2s/s3a.md`; blueprint
`formal/work/p2/blueprint_s3a.md`, supporting node `s3:eqStar`, namedlabels `s3:eqS1`–`s3:eqS6`).
No proofs here. The parameters are the locked Defs `EG.Star.*` of `EG/Defs/Link/Star.lean`.

Already stated elsewhere (unit NUM, `EG/Spec/Num/StarInputs.lean`, reused, not restated):
the numeric part of (S2) (`StarS2NumStatement`: `p_* ≥ 0.1ρ/ℓ_*`, `p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`)
and (S3) (`StarS3Statement`). The blueprint's single `StarFactsStatement` is split here into one
statement per fact, so that no fact is stated twice.

Manuscript v6.1, `s3.tex`, paragraph "Local parameters":
"Let `n ≥ 2` be the number of vertices of the graph at hand, `L := log n`, `ε' ∈ [2^{-7},1]` its
expansion parameter, `ρ ∈ (0,1]` a density and `t ≥ 1` a multiplicity. […] We record six
elementary facts, each with its proof. Write `p := p_*`.
(S1) `2^{10}L^3−1 < ℓ_* ≤ 2^{10}L^3` and `ℓ_* ≥ 2^{10}`.
(S2) The number `p_*` exists, is unique, and satisfies `p_* ≥ 0.1ρ/ℓ_*`, so
`p_*^{-2} ≤ 100ℓ_*^2ρ^{-2}`. If `V_1,…,V_{ℓ_*}` are independent random subsets of a set `S`, where
`V_i` is `p_*`-random for `i < ℓ_*` and `V_{ℓ_*}` is `q_*`-random, then `V_1 ∪ ⋯ ∪ V_{ℓ_*}` is a
`ρ`-random subset of `S`.
(S3) […]
(S4) `8d_*λ_* ≤ 112p^{-2} ≤ θ_*` and `θ_* ≤ 2^{39}L^9/(ε'ρ^2) ≤ 2^{46}L^9ρ^{-2}`.
(S5) `K_* ≥ s̄_*/μ_*`; `K_* ≤ (6·2^{81}+1)tL^{19}ρ^{-3} ≤ 2^{83.6}tL^{19}ρ^{-3}`;
`2K_*(θ_*+1) ≤ 2^{130.6}tL^{28}ρ^{-5}`; and `40K_*L ≤ 2K_*(θ_*+1)`.
(S6) `σ_* ≥ 24`, `λ_*p ≥ 6` and `1 ≤ d_*p ≤ 1+p ≤ 2`.
The values `σ_*,λ_*,Δ_*,d_*` of (eqStar) satisfy the parameter hypotheses of Proposition 13*
below: `σ_* = 24L^2/ε'` holds with equality, and
`Δ_*−λ_* = ⌈d_*λ_*/3⌉ ≥ d_*λ_*/3 = 8d_*λ_*L^2/(ε'σ_*)`."

Formal reading.
* Each statement quantifies exactly the inputs among `n, ε', ρ, t` that its fact mentions, with the
  domain hypotheses of (eqStar) on them (`2 ≤ n`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`, `1 ≤ t`;
  CONVENTIONS "Parameters of s3/s4"). `L = EG.Star.L n = log₂ n`.
* Decimals are exact rationals in `ℝ`. `ρ^{-k}` is the integer power `ρ ^ (-k : ℤ)` (as in the
  Spec of Theorem 16*, `EG/Spec/Link/T16s.lean`); `p^{-2}` is `(Star.p n ρ)⁻¹ ^ 2` (as in
  `StarInputs`). `2^{83.6}` and `2^{130.6}` are real powers (`Real.rpow`).
* (S2), existence and uniqueness: `EG.Star.p` is an explicit closed form (decision
  STAR-PSTAR-IMPLICIT); the statement says it lies in `(0,1]`, solves the defining equation
  `(1−p)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)` (natural power, `ℓ_* − 1` in `ℕ`, `ℓ_* ≥ 2^{10}`), and is the
  only solution in `(0,1]`.
* (S2), union law: the layers are `Vs ω : Fin ℓ_* → Finset α` on any finite space; the manuscript's
  `V_i` (`i ∈ [ℓ_*]`) is `Vs ω ⟨i-1, _⟩`, so "`i < ℓ_*`" is `(i : ℕ) + 1 < ℓ_*`; "independent" is
  `FinDist.iIndepFun` of the layers, "`p`-random subset of `S`" is `FinDist.IsRSubset`.
* (S5): the TeX chain for `2K_*(θ_*+1)` goes through the exact product
  `2(6·2^{81}+1)(2^{46}+1)` ("`log(2(6·2^{81}+1)(2^{46}+1)) < 130.6`"); that intermediate bound is
  stated as an extra conjunct next to the `2^{130.6}` one (Theorem 16* compares with `2^{135}`;
  blueprint note STAR-S5-RPOW). Likewise `K_* ≤ (6·2^{81}+1)tL^{19}ρ^{-3}` is kept separately from
  `(6·2^{81}+1)tL^{19}ρ^{-3} ≤ 2^{83.6}tL^{19}ρ^{-3}`.
* The last paragraph (the parameter hypotheses of Proposition 13*) is `StarP13sParamsStatement`,
  written in the exact form of the hypotheses of `EG.Spec.P13sStatement`
  (`EG/Spec/Link/P13s.lean`, with `L = Real.logb 2 n`) so that Lemma 17*'s proof can pass them.
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s3:eqS1] "(S1) `2^{10}L^3−1 < ℓ_* ≤ 2^{10}L^3` and `ℓ_* ≥ 2^{10}`. *Proof:* `L ≥ 1` because
`n ≥ 2`." -/
def StarS1Statement : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (2 : ℝ) ^ 10 * Star.L n ^ 3 - 1 < (Star.ell n : ℝ) ∧
    (Star.ell n : ℝ) ≤ (2 : ℝ) ^ 10 * Star.L n ^ 3 ∧
    2 ^ 10 ≤ Star.ell n

/-- [s3:eqS2] (existence and uniqueness) "The number `p_*` exists, is unique, […]", where
"`p_* ∈ (0,1]` given by `(1−p_*)^{ℓ_*−1} = (1−ρ)/(1−0.9ρ)`" (eqStar): the explicit `EG.Star.p`
lies in `(0,1]`, solves the defining equation, and is its only solution in `(0,1]`. -/
def StarS2PStatement : Prop :=
  ∀ (n : ℕ) (ρ : ℝ), 2 ≤ n → 0 < ρ → ρ ≤ 1 →
    (0 < Star.p n ρ ∧ Star.p n ρ ≤ 1 ∧
      (1 - Star.p n ρ) ^ (Star.ell n - 1) = (1 - ρ) / (1 - 0.9 * ρ)) ∧
    ∀ x : ℝ, 0 < x → x ≤ 1 → (1 - x) ^ (Star.ell n - 1) = (1 - ρ) / (1 - 0.9 * ρ) →
      x = Star.p n ρ

/-- [s3:eqS2] (union law) "If `V_1,…,V_{ℓ_*}` are independent random subsets of a set `S`, where
`V_i` is `p_*`-random for `i < ℓ_*` and `V_{ℓ_*}` is `q_*`-random, then `V_1 ∪ ⋯ ∪ V_{ℓ_*}` is a
`ρ`-random subset of `S`." (Layer `i : Fin ℓ_*` is the manuscript's `V_{i+1}`.) -/
def StarUnionLawStatement : Prop :=
  ∀ (α : Type u) [DecidableEq α] (Ω : Type v) (μ : FinDist Ω) (S : Finset α) (n : ℕ) (ρ : ℝ)
    (Vs : Ω → Fin (Star.ell n) → Finset α),
    2 ≤ n → 0 < ρ → ρ ≤ 1 →
    μ.iIndepFun (fun i ω => Vs ω i) →
    (∀ i : Fin (Star.ell n), μ.IsRSubset (fun ω => Vs ω i) S
      (if (i : ℕ) + 1 < Star.ell n then Star.p n ρ else Star.q ρ)) →
    μ.IsRSubset (fun ω => Finset.univ.biUnion (Vs ω)) S ρ

/-- [s3:eqS4] "(S4) `8d_*λ_* ≤ 112p^{-2} ≤ θ_*` and
`θ_* ≤ 2^{39}L^9/(ε'ρ^2) ≤ 2^{46}L^9ρ^{-2}`." -/
def StarS4Statement : Prop :=
  ∀ (n : ℕ) (ε' ρ : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    8 * (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) ≤ 112 * (Star.p n ρ)⁻¹ ^ 2 ∧
    112 * (Star.p n ρ)⁻¹ ^ 2 ≤ Star.theta n ε' ρ ∧
    Star.theta n ε' ρ ≤ (2 : ℝ) ^ 39 * Star.L n ^ 9 / (ε' * ρ ^ 2) ∧
    (2 : ℝ) ^ 39 * Star.L n ^ 9 / (ε' * ρ ^ 2) ≤ (2 : ℝ) ^ 46 * Star.L n ^ 9 * ρ ^ (-2 : ℤ)

/-- [s3:eqS5] "(S5) `K_* ≥ s̄_*/μ_*`; `K_* ≤ (6·2^{81}+1)tL^{19}ρ^{-3} ≤ 2^{83.6}tL^{19}ρ^{-3}`;
`2K_*(θ_*+1) ≤ 2^{130.6}tL^{28}ρ^{-5}`; and `40K_*L ≤ 2K_*(θ_*+1)`." The proof's intermediate
bound `2K_*(θ_*+1) ≤ 2(6·2^{81}+1)(2^{46}+1)tL^{28}ρ^{-5}` ("`θ_*+1 ≤ (2^{46}+1)L^9ρ^{-2}`, and
`log(2(6·2^{81}+1)(2^{46}+1)) < 130.6`") is the fourth conjunct. -/
def StarS5Statement : Prop :=
  ∀ (n : ℕ) (ε' ρ t : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 → 1 ≤ t →
    Star.sbar n ρ t / Star.mu n ε' ρ ≤ (Star.K n ε' ρ t : ℝ) ∧
    (Star.K n ε' ρ t : ℝ) ≤ (6 * 2 ^ 81 + 1) * t * Star.L n ^ 19 * ρ ^ (-3 : ℤ) ∧
    (6 * 2 ^ 81 + 1) * t * Star.L n ^ 19 * ρ ^ (-3 : ℤ) ≤
      (2 : ℝ) ^ (83.6 : ℝ) * t * Star.L n ^ 19 * ρ ^ (-3 : ℤ) ∧
    2 * (Star.K n ε' ρ t : ℝ) * (Star.theta n ε' ρ + 1) ≤
      2 * (6 * 2 ^ 81 + 1) * (2 ^ 46 + 1) * t * Star.L n ^ 28 * ρ ^ (-5 : ℤ) ∧
    2 * (Star.K n ε' ρ t : ℝ) * (Star.theta n ε' ρ + 1) ≤
      (2 : ℝ) ^ (130.6 : ℝ) * t * Star.L n ^ 28 * ρ ^ (-5 : ℤ) ∧
    40 * (Star.K n ε' ρ t : ℝ) * Star.L n ≤ 2 * (Star.K n ε' ρ t : ℝ) * (Star.theta n ε' ρ + 1)

/-- [s3:eqS6] "(S6) `σ_* ≥ 24`, `λ_*p ≥ 6` and `1 ≤ d_*p ≤ 1+p ≤ 2`. *Proof:* immediate from
(eqStar), since `ε' ≤ 1 ≤ L`." -/
def StarS6Statement : Prop :=
  ∀ (n : ℕ) (ε' ρ : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    24 ≤ Star.sigma n ε' ∧
    6 ≤ (Star.lam n ρ : ℝ) * Star.p n ρ ∧
    1 ≤ (Star.d n ρ : ℝ) * Star.p n ρ ∧
    (Star.d n ρ : ℝ) * Star.p n ρ ≤ 1 + Star.p n ρ ∧
    1 + Star.p n ρ ≤ 2

/-- [s3:eqStar] "The values `σ_*,λ_*,Δ_*,d_*` of (eqStar) satisfy the parameter hypotheses of
Proposition 13* below: `σ_* = 24L^2/ε'` holds with equality, and
`Δ_*−λ_* = ⌈d_*λ_*/3⌉ ≥ d_*λ_*/3 = 8d_*λ_*L^2/(ε'σ_*)`." The parameter hypotheses of
Proposition 13* ("Let `σ_* > 0` be real and let `λ_*,d_* ≥ 1` and `Δ_* ≥ λ_*` be integers such
that `σ_* ≥ 24L^2/ε'`, `Δ_*−λ_* ≥ 8d_*λ_*L^2/(ε'σ_*)`") are written exactly as in
`EG.Spec.P13sStatement`, with `L = log₂ n`. -/
def StarP13sParamsStatement : Prop :=
  ∀ (n : ℕ) (ε' ρ : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    Star.sigma n ε' = 24 * Real.logb 2 (n : ℝ) ^ 2 / ε' ∧
    (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) / 3 ≤ (Star.Delta n ρ : ℝ) - (Star.lam n ρ : ℝ) ∧
    (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) / 3 =
      8 * (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) * Real.logb 2 (n : ℝ) ^ 2 /
        (ε' * Star.sigma n ε') ∧
    -- the hypotheses of `P13sStatement`, in its form
    0 < Star.sigma n ε' ∧ 1 ≤ Star.lam n ρ ∧ 1 ≤ Star.d n ρ ∧ Star.lam n ρ ≤ Star.Delta n ρ ∧
    24 * Real.logb 2 (n : ℝ) ^ 2 / ε' ≤ Star.sigma n ε' ∧
    8 * (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) * Real.logb 2 (n : ℝ) ^ 2 / (ε' * Star.sigma n ε') ≤
      (Star.Delta n ρ : ℝ) - (Star.lam n ρ : ℝ)

end EG.Spec
