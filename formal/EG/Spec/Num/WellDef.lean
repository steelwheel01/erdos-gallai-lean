module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The SDR union bound of Lemma WellDef (iii) (manuscript s7:lemWellDef)

Statement file (`EG/Spec/**`), unit NUM (cheap numeric probes, TRIAGE §4). Proofs:
`EG/Proof/Num/WellDef.lean`. Design note: `formal/work/p2b/NUM.md`.

Manuscript v6.1, `s7.tex`, proof of Lemma [s7:lemWellDef] (iii) (after the Hall / union-bound
reduction, which is probabilistic and not part of this unit):
"`P(SDR failure at u | Past_l) ≤ ∑_{s=4}^{m} T_s`,
`T_s := C(m,s) C(K,s−1) (C(s−1,3)/C(K,3))^s`.
We use `C(m,s) ≤ (em/s)^s ≤ (eK/(4s))^s`, `C(K,s−1) ≤ (eK/(s−1))^{s−1}`, and
`C(s−1,3)/C(K,3) = (s−1)(s−2)(s−3)/(K(K−1)(K−2)) ≤ ((s−1)/K)^3` […]. Multiplying, and using
`(s−1)^{2s+1} ≤ s^{2s+1}`,
`T_s ≤ e^{2s−1}4^{−s}s^{−s}(s−1)^{2s+1}K^{−s−1} ≤ a_s := (1/e)·(s/K)·(e^2s/(4K))^s`.
First, `a_4 = 4e^7K^{−5} < 4400K^{−5}`. Second, for `s ≥ 4`,
`a_{s+1}/a_s = … ≤ (5e^3/16)·(s+1)/K`, which is at most `(5e^3/16)(1/13+1/K) < 0.49` when
`4 ≤ s < K/13` and `K ≥ 10^4`. Hence `a_s ≤ 2^{4−s}a_4` for `4 ≤ s ≤ ⌈K/13⌉`, and the sum of these
terms is at most `2a_4 < 8800K^{−5}`. Third, for `K/13 < s ≤ m ≤ K/4` we have `s/K ≤ 1/4`, so
`a_s ≤ (1/(4e))(e^2/16)^s ≤ 0.47^s`, and the sum of these terms is at most
`0.47^{K/13}/0.53 ≤ 2·0.47^{K/13}`. Altogether
`P(SDR failure at u | Past_l) ≤ 8800K^{−5} + 2·0.47^{K/13} ≤ K^{−4}  (K ≥ 10^4)`,
since `8800K^{−5} ≤ 0.88K^{−4}` and `2·0.47^{K/13} ≤ 0.1K^{−4}` for `K ≥ 10^4`. Here
`K = 4M_l ≥ 2^{42}`."
The context: "`m ≤ M_l−1 ≤ K/4` with `K := K^{HUB}_l = 4M_l`", and `M_l ≥ 2^{40}` (Γ-free: the
remark after the proof says "it holds since `M_l ≥ 2^{40}`").

Formal reading. `K, m, s` are natural numbers; binomial coefficients are `Nat.choose` cast to `ℝ`
(so `C(m,s) = 0` for `s > m`, as in the manuscript); `s − 1` is natural subtraction, harmless as
`s ≥ 4`; the sum `∑_{s=4}^m` is over `Finset.Icc 4 m` (empty for `m < 4`, where the bound is
trivial). `K^{−5}` is a `zpow`, `0.47^{K/13}` a real power (`Real.rpow`, base `0.47 > 0`).
The general statement takes `m ≤ K/4` (real division), exactly the hypothesis the proof uses;
the use form takes `K = 4M` and `m ≤ M − 1` with `M ≥ 2^{40}`.
-/

@[expose] public section


namespace EG.Spec

open Finset

/-- [s7:lemWellDef] (iii): "`T_s := C(m,s) C(K,s−1) (C(s−1,3)/C(K,3))^s`" as a function of
`K`, `m` and `s` (real-valued). An abbreviation for the statements below. -/
noncomputable def numSDRTerm (K m s : ℕ) : ℝ :=
  (m.choose s : ℝ) * (K.choose (s - 1) : ℝ) * (((s - 1).choose 3 : ℝ) / (K.choose 3 : ℝ)) ^ s

/-- [s7:lemWellDef] (iii): "Altogether
`P(SDR failure at u | Past_l) ≤ 8800K^{−5} + 2·0.47^{K/13} ≤ K^{−4}  (K ≥ 10^4)`", for the
union bound `∑_{s=4}^m T_s` with `m ≤ K/4`. Both inequalities of the display. -/
def NumWellDefSDRSeriesStatement : Prop :=
  ∀ K m : ℕ, 10 ^ 4 ≤ K → (m : ℝ) ≤ (K : ℝ) / 4 →
    ∑ s ∈ Icc 4 m, numSDRTerm K m s ≤
        8800 * (K : ℝ) ^ (-5 : ℤ) + 2 * (0.47 : ℝ) ^ ((K : ℝ) / 13) ∧
    8800 * (K : ℝ) ^ (-5 : ℤ) + 2 * (0.47 : ℝ) ^ ((K : ℝ) / 13) ≤ (K : ℝ) ^ (-4 : ℤ)

/-- [s7:lemWellDef] (iii), the form in which it is used: "`m ≤ M_l−1 ≤ K/4` with
`K := K^{HUB}_l = 4M_l`" and "Here `K = 4M_l ≥ 2^{42}`": for `M = M_l ≥ 2^{40}` and
`m ≤ M − 1`, `∑_{s=4}^m T_s ≤ K^{−4}` with `K = 4M`. -/
def NumWellDefSDRUseStatement : Prop :=
  ∀ M m : ℕ, 2 ^ 40 ≤ M → m ≤ M - 1 →
    ∑ s ∈ Icc 4 m, numSDRTerm (4 * M) m s ≤ ((4 * M : ℕ) : ℝ) ^ (-4 : ℤ)

/-- [s7:lemWellDef] (iii): "`a_{s+1}/a_s ≤ … < 0.49` […]. Hence `a_s ≤ 2^{4−s}a_4`": the ratio
bound `0.49` is at most `1/2`. (Added in fix round 1, review I-4.) -/
def NumWellDefSDRRatioStatement : Prop :=
  (0.49 : ℝ) ≤ 1 / 2

/-- [s7:lemWellDef] (iii), the constants of the proof: "`a_4 = 4e^7K^{−5} < 4400K^{−5}`";
"`(5e^3/16)(1/13+1/K) < 0.49` when […] `K ≥ 10^4`"; "`a_s ≤ (1/(4e))(e^2/16)^s ≤ 0.47^s`"
(`1/(4e) ≤ 1` and `e^2/16 ≤ 0.47`);
"`0.47^{K/13}/0.53 ≤ 2·0.47^{K/13}`" (`1/0.53 ≤ 2`); "`2a_4 < 8800K^{−5}`" (`2·4400 = 8800`);
"`8800K^{−5} ≤ 0.88K^{−4}` and `2·0.47^{K/13} ≤ 0.1K^{−4}` for `K ≥ 10^4`" and
`0.88 + 0.1 ≤ 1`; "`K = 4M_l ≥ 2^{42}`" (so `K ≥ 10^4`). Values: `4e^7 = 4386.5…`,
`(5e^3/16)(1/13+10^{−4}) = 0.4834…`, `e^2/16 = 0.4618…`. -/
def NumWellDefSDRConstStatement : Prop :=
  4 * Real.exp 7 < 4400 ∧
    (∀ K : ℝ, 10 ^ 4 ≤ K → 5 * Real.exp 3 / 16 * (1 / 13 + 1 / K) < 0.49) ∧
    1 / (4 * Real.exp 1) ≤ 1 ∧ Real.exp 2 / 16 ≤ 0.47 ∧
    (1 : ℝ) / 0.53 ≤ 2 ∧ (2 : ℝ) * 4400 = 8800 ∧
    (∀ K : ℝ, 10 ^ 4 ≤ K →
      8800 * K ^ (-5 : ℤ) ≤ 0.88 * K ^ (-4 : ℤ) ∧
      2 * (0.47 : ℝ) ^ (K / 13) ≤ 0.1 * K ^ (-4 : ℤ)) ∧
    (0.88 : ℝ) + 0.1 ≤ 1 ∧
    (∀ M : ℕ, 2 ^ 40 ≤ M → 2 ^ 42 ≤ 4 * M ∧ 10 ^ 4 ≤ 4 * M)

end EG.Spec
