module

public import EG.Defs.Link.Star

/-!
# The numeric facts used in the proof of Lemma 17* (manuscript s3:lemL17s)

Statement file (`EG/Spec/**`), unit NUM (cheap numeric probes, TRIAGE §4). Proofs:
`EG/Proof/Num/L17s.lean`. Design note: `formal/work/p2b/NUM.md`.

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemL17s] ("Lemma 17*: sprinkling at density ρ").
Each statement below is one numeric step of that proof, quoted in its docstring, with the
parameters of (eqStar) (`EG.Star.*`, `EG/Defs/Link/Star.lean`) where the step is about them.
The steps are:
* Step 0 (`NumL17sStep0Statement`): `ρn > 2^{39}` and `7uL ≤ 2^{-36}ρn`;
* Step 2 case (a) (`NumL17sCaseAConstStatement`, `NumL17sCaseASigmaStatement`,
  `NumL17sCaseAExponentStatement`): `3|W|/σ_* = g_*|W|` and the exponent
  `p_*|Cen|/8 ≥ 273ℓ_*uL ≥ 18uL`;
* Step 2 case (b) (`NumL17sBernsteinMarginStatement` (`0.09/4.2 > 1/47`),
  `NumL17sBernsteinExponentStatement`, `NumL17sCaseBMeanStatement`,
  `NumL17sCaseBGrowthStatement`, `NumL17sCaseBSmallPConstStatement` (`2^{19}/28200 > 18.59`),
  `NumL17sCaseBLargePConstStatement`, `NumL17sCaseBExponentStatement`): the Bernstein exponent
  and the bound `|X|/(47Δ_*) ≥ 18uL` in both regimes of `p_*`;
* Step 3 (`NumL17sStep3Statement`): `(ℓ_*−1)e^{−18uL} ≤ 0.02e^{−7uL}`;
* Step 4 (`NumL17sStep4Statement`): `(1+g_*)^{ℓ_*−1} ≥ n`;
* Step 5 (`NumL17sStep5Statement`): the Chernoff exponents `0.00243 ≥ 1/412`, `0.0027 ≥ 1/412`
  and `2e^{−ρn/412} ≤ 0.01e^{−7uL}`.

Conventions. `log = log₂` (`EG.Star.L n = logb 2 n`); `e^x` and `ln` are `Real.exp` and
`Real.log`. Decimal literals are exact rationals in `ℝ` (`0.09 = 9/100`). Cardinalities
(`u = |U|`, `|W|`, `|X|`, `|Cen|`) are real numbers here, with exactly the bounds the manuscript
uses; the statements are therefore at least as strong as the uses. The parameter statements carry
the domain hypotheses of (eqStar) (`n ≥ 2`, `2^{-7} ≤ ε' ≤ 1`, `0 < ρ ≤ 1`; CONVENTIONS
"Parameters of s3/s4"); a hypothesis the step does not need is still stated when the manuscript
has it, so each statement is the step exactly as used.

The numeric part of (S2) (`p_* ≥ 0.1ρ/ℓ_*`) and (S3) (`Δ_* ≤ 3p_*^{-2}` for `p_* ≤ 0.11`,
`Δ_* ≤ 13p_*^{-2}`), used by case (a) and by `NumL17sCaseBExponentStatement`, are the statements
of `EG/Spec/Num/StarInputs.lean` (declared inputs in stage 1, proved in fix round 1).
-/

@[expose] public section


namespace EG.Spec

open Real

/-! ### Step 0 -/

/-- [s3:lemL17s] Step 0: "Since `U` is well-expanding, `θ_*u ≤ |N_G(U)| < n`. Hence
`n > θ_* ≥ 2^{19}ℓ_*^2L^3/ρ^2`, and so `ρn ≥ ρ^2n > 2^{19}ℓ_*^2L^3 ≥ 2^{39}` by (S1). Also
`7uL < 7nL/θ_* ≤ 7ρ^2n/(2^{19}ℓ_*^2L^2) ≤ 2^{-36}ρn`."
Here `u = |U| ≥ 1` and the hypothesis is `θ_* u < n`. -/
def NumL17sStep0Statement : Prop :=
  ∀ (n : ℕ) (ε' ρ u : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    1 ≤ u → Star.theta n ε' ρ * u < (n : ℝ) →
    (2 : ℝ) ^ 39 < ρ * n ∧ 7 * u * Star.L n ≤ (2 : ℝ) ^ (-36 : ℤ) * (ρ * n)

/-! ### Step 2, case (a): stars -/

/-- [s3:lemL17s] Step 2, case (a), the constant in
"`(0.1ρ/ℓ_*)·(2^{19}ℓ_*^2L^3u/(192ρ^2L^2)) ≥ 273ℓ_*uL`": `0.1·2^{19}/192 ≥ 273`
(the value is `273.07…`; slack 0.02%). -/
def NumL17sCaseAConstStatement : Prop :=
  (273 : ℝ) ≤ 0.1 * 2 ^ 19 / 192

/-- [s3:lemL17s] Step 2, case (a): "Outside this event, by (S6),
`|A_i(W)| ≥ λ_*p_*|Cen|/2 ≥ 3|Cen| ≥ 3|W|/σ_* = g_*|W|`." The last equality (`3/σ_* = g_*`, i.e.
`3ε'/(24L^2) = ε'/(8L^2)`), for `n ≥ 2` and `ε' > 0`, with `W = |W|` real. (Added in fix round 1,
review I-4.) -/
def NumL17sCaseASigmaStatement : Prop :=
  ∀ (n : ℕ) (ε' : ℝ), 2 ≤ n → 0 < ε' → ∀ W : ℝ, 3 * W / Star.sigma n ε' = Star.g n ε' * W

/-- [s3:lemL17s] Step 2, case (a): "For the exponent, (S2) and `|W| ≥ θ_*u` give
`p_*|Cen|/8 ≥ p_*ε'|W|/(192L^2) ≥ (0.1ρ/ℓ_*)·(2^{19}ℓ_*^2L^3u/(192ρ^2L^2)) ≥ 273ℓ_*uL ≥ 18uL`."
Here `C = |Cen| ≥ |W|/σ_*` (the number of stars, case (a) of Proposition 13*), `W = |W|` and
`u = |U| ≥ 1`. -/
def NumL17sCaseAExponentStatement : Prop :=
  ∀ (n : ℕ) (ε' ρ : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    ∀ u W C : ℝ, 1 ≤ u → Star.theta n ε' ρ * u ≤ W → W / Star.sigma n ε' ≤ C →
      273 * (Star.ell n : ℝ) * u * Star.L n ≤ Star.p n ρ * C / 8 ∧
      18 * u * Star.L n ≤ 273 * (Star.ell n : ℝ) * u * Star.L n

/-! ### Step 2, case (b): a bipartite graph -/

/-- [s3:lemL17s] Step 2, case (b): "Since `2(β+Δ_*a/3)=4Δ_*|X|+0.2Δ_*|X|` and
`0.09/4.2>1/47`, it gives …". The margin `0.09/4.2 > 1/47` (`0.021428… > 0.021276…`; slack
0.7%). -/
def NumL17sBernsteinMarginStatement : Prop :=
  (1 : ℝ) / 47 < 0.09 / 4.2

/-- [s3:lemL17s] Step 2, case (b): "Apply the second bound of Lemma BBD with […] `Δ_*` in the
role of the bound `b` of that lemma, this `β` and `a:=0.3|X|`. Since
`2(β+Δ_*a/3)=4Δ_*|X|+0.2Δ_*|X|` and `0.09/4.2>1/47`, it gives
`P(Z ≤ EZ−0.3|X|) ≤ exp(−0.09|X|^2/(4Δ_*|X|+0.2Δ_*|X|)) ≤ exp(−|X|/(47Δ_*))`."
Here `β := 2Δ_*|X|` (the displayed definition `… ≤ 2Δ_*|X| =: β`), `X = |X| > 0` and
`Δ = Δ_* > 0`. The three conjuncts are the identity for the denominator, `a^2 = 0.09|X|^2`,
and the final comparison of exponentials. -/
def NumL17sBernsteinExponentStatement : Prop :=
  ∀ X Δ : ℝ, 0 < X → 0 < Δ →
    2 * (2 * Δ * X + Δ * (0.3 * X) / 3) = 4 * Δ * X + 0.2 * Δ * X ∧
    (0.3 * X) ^ 2 = 0.09 * X ^ 2 ∧
    exp (-(0.09 * X ^ 2 / (4 * Δ * X + 0.2 * Δ * X))) ≤ exp (-(X / (47 * Δ)))

/-- [s3:lemL17s] Step 2, case (b): "`P(N_H(x) ∩ V_i = ∅) = (1−p_*)^{d_*} ≤ e^{−p_*d_*} ≤ e^{−1}`,
so `EZ ≥ (1−e^{−1})|X| ≥ 0.63|X|`" and "Since `EZ−0.3|X| ≥ 0.33|X|`". The two constants:
`1 − e^{−1} ≥ 0.63` (`0.632…`) and `0.63 − 0.3 = 0.33`. -/
def NumL17sCaseBMeanStatement : Prop :=
  (0.63 : ℝ) ≤ 1 - exp (-1) ∧ (0.63 : ℝ) - 0.3 = 0.33

/-- [s3:lemL17s] Step 2, case (b): "Outside this event,
`|A_i(W)| ≥ Z ≥ 0.33|X| ≥ 0.165ε'|W|/L^2 ≥ g_*|W|`", using `|X| ≥ ε'|W|/(2L^2)`
(Proposition 13*(b)). Here `W = |W| ≥ 0` and `X = |X|`. -/
def NumL17sCaseBGrowthStatement : Prop :=
  ∀ (n : ℕ) (ε' : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 →
    ∀ W X : ℝ, 0 ≤ W → ε' * W / (2 * Star.L n ^ 2) ≤ X →
      0.165 * ε' * W / Star.L n ^ 2 ≤ 0.33 * X ∧
      Star.g n ε' * W ≤ 0.165 * ε' * W / Star.L n ^ 2

/-- [s3:lemL17s] Step 2, case (b), regime `p_* ≤ 0.11`: "`Δ_* ≤ 3p_*^{-2} ≤ 300ℓ_*^2ρ^{-2}`, and
the exponent is at least `2^{19}uL/28200 ≥ 18uL` (indeed `2^{19}/28200 > 18.59`; this is the
tightest inequality of the lemma)." The constants: `94·300 = 28200` (the `94` of the displayed
exponent, the `300` of `Δ_*`), `2^{19}/28200 > 18.59` (the value is `18.5917…`) and
`18.59 ≥ 18` (slack 3.3%). -/
def NumL17sCaseBSmallPConstStatement : Prop :=
  (94 : ℝ) * 300 = 28200 ∧ (18.59 : ℝ) < 2 ^ 19 / 28200 ∧ (18 : ℝ) ≤ 18.59

/-- [s3:lemL17s] Step 2, case (b), regime `p_* > 0.11`: "`Δ_* ≤ 13p_*^{-2} < 13/0.0121 < 1075`,
and the exponent is at least `2^{19}ℓ_*^2uL/(94·1075) ≥ 5ℓ_*^2uL ≥ 18uL`." The constants:
`0.11^2 = 0.0121`, `13/0.0121 < 1075` (`1074.38…`), `2^{19}/(94·1075) ≥ 5` (`5.188…`) and
`5ℓ_*^2 ≥ 18` for `ℓ_* ≥ 2^{10}` ((S1)). -/
def NumL17sCaseBLargePConstStatement : Prop :=
  (0.11 : ℝ) ^ 2 = 0.0121 ∧ (13 : ℝ) / 0.0121 < 1075 ∧ (5 : ℝ) ≤ 2 ^ 19 / (94 * 1075) ∧
    ∀ ℓ : ℝ, 2 ^ 10 ≤ ℓ → (18 : ℝ) ≤ 5 * ℓ ^ 2

/-- [s3:lemL17s] Step 2, case (b): "For the exponent, `|X| ≥ ε'|W|/(2L^2)` and `|W| ≥ θ_*u`
give `|X|/(47Δ_*) ≥ ε'θ_*u/(94Δ_*L^2) = 2^{19}ℓ_*^2Lu/(94Δ_*ρ^2)`.
* If `p_* ≤ 0.11`, then (S3) and (S2) give `Δ_* ≤ 3p_*^{-2} ≤ 300ℓ_*^2ρ^{-2}`, and the exponent is
  at least `2^{19}uL/28200 ≥ 18uL` […].
* If `p_* > 0.11`, then (S3) gives `Δ_* ≤ 13p_*^{-2} < 13/0.0121 < 1075`, and the exponent is at
  least `2^{19}ℓ_*^2uL/(94·1075) ≥ 5ℓ_*^2uL ≥ 18uL`."
Here `u = |U| ≥ 1`, `W = |W|`, `X = |X|`; the conclusion is the chain
`|X|/(47Δ_*) ≥ ε'θ_*u/(94Δ_*L^2) = 2^{19}ℓ_*^2Lu/(94Δ_*ρ^2) ≥ 18uL` (both regimes). -/
def NumL17sCaseBExponentStatement : Prop :=
  ∀ (n : ℕ) (ε' ρ : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    ∀ u W X : ℝ, 1 ≤ u → Star.theta n ε' ρ * u ≤ W → ε' * W / (2 * Star.L n ^ 2) ≤ X →
      ε' * Star.theta n ε' ρ * u / (94 * (Star.Delta n ρ : ℝ) * Star.L n ^ 2) ≤
          X / (47 * (Star.Delta n ρ : ℝ)) ∧
      ε' * Star.theta n ε' ρ * u / (94 * (Star.Delta n ρ : ℝ) * Star.L n ^ 2) =
          2 ^ 19 * (Star.ell n : ℝ) ^ 2 * Star.L n * u / (94 * (Star.Delta n ρ : ℝ) * ρ ^ 2) ∧
      18 * u * Star.L n ≤
          2 ^ 19 * (Star.ell n : ℝ) ^ 2 * Star.L n * u / (94 * (Star.Delta n ρ : ℝ) * ρ ^ 2)

/-! ### Steps 3–5 -/

/-- [s3:lemL17s] Step 3: "Hence, using `u ≥ 1`, (S1), and the fact that `L^3e^{−11L} ≤ e^{−11}`
for `L ≥ 1`, `P(⋃_{i<ℓ_*} E_i^c) ≤ (ℓ_*−1)e^{−18uL} ≤ 2^{10}L^3e^{−11L}e^{−7uL} ≤ 0.02e^{−7uL}`."
The numeric part: the last two inequalities of the chain, with the auxiliary fact
`L^3e^{−11L} ≤ e^{−11}` (`L ≥ 1`) and `2^{10}e^{−11} ≤ 0.02` (`0.0171…`). -/
def NumL17sStep3Statement : Prop :=
  (∀ x : ℝ, 1 ≤ x → x ^ 3 * exp (-(11 * x)) ≤ exp (-11)) ∧
    (2 : ℝ) ^ 10 * exp (-11) ≤ 0.02 ∧
    ∀ (n : ℕ) (u : ℝ), 2 ≤ n → 1 ≤ u →
      ((Star.ell n : ℝ) - 1) * exp (-(18 * u * Star.L n)) ≤
          2 ^ 10 * Star.L n ^ 3 * exp (-(11 * Star.L n)) * exp (-(7 * u * Star.L n)) ∧
      2 ^ 10 * Star.L n ^ 3 * exp (-(11 * Star.L n)) * exp (-(7 * u * Star.L n)) ≤
          0.02 * exp (-(7 * u * Star.L n))

/-- [s3:lemL17s] Step 4: "Since `g_* ≤ 1/8`, we have `ln(1+g_*) ≥ g_*−g_*^2/2 ≥ 15g_*/16`.
By (S1) and `ε' ≥ 2^{-7}`, `(ℓ_*−1)g_* > (2^{10}L^3−2)2^{-10}L^{-2} ≥ L−2^{-9}`. Hence
`ln((1+g_*)^{ℓ_*−1}) ≥ (15/16)(L−2^{-9}) ≥ L ln 2 = ln n`, so `|B_{ℓ_*}| ≥ n`" (the lower bound
`|B_{ℓ_*}| ≥ (1+g_*)^{ℓ_*−1}` is the preceding sentence). The numeric content: the intermediate
bounds and the conclusion `(1+g_*)^{ℓ_*−1} ≥ n` (`ℓ_* − 1` in `ℕ`; `ℓ_* ≥ 2^{10}` by (S1)). -/
def NumL17sStep4Statement : Prop :=
  ∀ (n : ℕ) (ε' : ℝ), 2 ≤ n → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 →
    Star.g n ε' ≤ 1 / 8 ∧
    15 * Star.g n ε' / 16 ≤ Real.log (1 + Star.g n ε') ∧
    Star.L n - (2 : ℝ) ^ (-9 : ℤ) < ((Star.ell n : ℝ) - 1) * Star.g n ε' ∧
    Star.L n * Real.log 2 ≤ 15 / 16 * (Star.L n - (2 : ℝ) ^ (-9 : ℤ)) ∧
    (n : ℝ) ≤ (1 + Star.g n ε') ^ (Star.ell n - 1)

/-- [s3:lemL17s] Step 5: "The lower-tail Chernoff bound for a mean bound `μ:=0.6ρn` […] with
`δ=0.09` gives `P(|B_{ℓ_*}∩V_{ℓ_*}| < 0.546ρn) ≤ exp(−0.0081·0.6ρn/2) ≤ exp(−0.00243ρn)`. Since
`V` is `ρ`-random, `|V|∼Bin(n,ρ)`, and `P(|V| > 1.09ρn) ≤ exp(−0.0081ρn/3) = exp(−0.0027ρn)`.
Outside both events, `|B_{ℓ_*}∩V_{ℓ_*}| ≥ 0.546ρn > 0.545ρn ≥ |V|/2` […]. The probability of the
two events is at most `2e^{−ρn/412} ≤ 2e^{−ρn/413}e^{−7uL} ≤ 0.01e^{−7uL}`. Here we used Step 0:
`7uL ≤ 2^{-36}ρn ≤ ρn(1/412−1/413)` and `ρn > 2^{39}`." With the mean `0.9ρ·(2n/3) = 0.6ρn`
("mean at least `0.6ρn`") and the conclusion "The total probability is at most
`0.03e^{−7uL} ≤ e^{−7uL}`". Conjuncts, in order: the mean and threshold constants; the two
Chernoff exponents against `1/412` (`0.00243 ≥ 0.0024271…`: slack 0.1%, the thinnest of the
lemma; `0.0027 ≥ 1/412`); `1.09/2 < 0.546`; `2^{-36} ≤ 1/412 − 1/413`; the final bound for
`x = ρn > 2^{39}` and `y = 7uL ≤ 2^{-36}x`; `0.02 + 0.01 ≤ 1`. -/
def NumL17sStep5Statement : Prop :=
  (0.9 : ℝ) * (2 / 3) = 0.6 ∧ (1 - 0.09 : ℝ) * 0.6 = 0.546 ∧
    (0.09 : ℝ) ^ 2 = 0.0081 ∧ (0.0081 : ℝ) * 0.6 / 2 = 0.00243 ∧ (0.0081 : ℝ) / 3 = 0.0027 ∧
    (1 : ℝ) / 412 ≤ 0.00243 ∧ (1 : ℝ) / 412 ≤ 0.0027 ∧
    (1.09 : ℝ) / 2 < 0.546 ∧
    (2 : ℝ) ^ (-36 : ℤ) ≤ 1 / 412 - 1 / 413 ∧
    (∀ x y : ℝ, 2 ^ 39 < x → y ≤ (2 : ℝ) ^ (-36 : ℤ) * x →
      2 * exp (-(x / 412)) ≤ 2 * exp (-(x / 413)) * exp (-y) ∧
      2 * exp (-(x / 413)) * exp (-y) ≤ 0.01 * exp (-y)) ∧
    (0.02 : ℝ) + 0.01 ≤ 1

end EG.Spec
