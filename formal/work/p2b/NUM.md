# Unit NUM: cheap numeric probes (P2b, stage 1: Specs; fix round 1: all proved)

Scope (TRIAGE §4 row "Cheap numeric probes", §1c): the numeric facts used at
- the L17\* margins (s3:lemL17s: `0.09/4.2` vs `1/47`; `2^19/28200 ≥ 18`), with the other numeric
  steps of the same proof (Steps 0, 3, 4, 5, case (a));
- the WellDef(iii) SDR series `Σ_{s=4}^m T_s ≤ K^-4` for `K ≥ 10^4` (s7:lemWellDef);
- the OV constants and the rational bound `log₂(4/3) ≥ 17/41` (s2:lemOVgeneric, s2:lem14tau,
  s2:propOV), with the "OV potential" (the charge-sum estimate of OV(a));
- the CC constants `44.7`, `29.8` (s7:lemCC(iii), needs `e < 2.71898`), with the UH\*-split
  constants that consume them (s7:lemUHsplit(ii)).

Cap(i) (Lemma 25 constant 18) is not in this unit (`EG.bmLemma25`, its own unit).

The manuscript is a CANDIDATE proof (AI-reviewed only). Every number below was re-evaluated in
double precision (scratch computation, not committed) before it was stated.

## Files

| File | Content |
|---|---|
| `EG/Spec/Num/L17s.lean` | 14 statements of s3:lemL17s (fix round 1 added `NumL17sCaseASigmaStatement`) |
| `EG/Spec/Num/StarInputs.lean` | [s3:eqS2] numeric part, [s3:eqS3], and (fix round 1) `NumStarS3MarginStatement`; declared inputs in stage 1, all proved since fix round 1 |
| `EG/Spec/Num/WellDef.lean` | `numSDRTerm` (abbreviation for `T_s`) and 4 statements of s7:lemWellDef(iii) (fix round 1 added `NumWellDefSDRRatioStatement`) |
| `EG/Spec/Num/OV.lean` | 7 statements of s2:lemOVgeneric / s2:lem14tau / s2:propOV (fix round 1 added `NumOVRearrangeStatement`, `NumOVInstanceStatement`) |
| `EG/Spec/Num/CC.lean` | 4 statements of s7:lemCC(iii) / s7:lemUHsplit(ii) |
| `EG/Proof/Num/StarInputs.lean` | 3 proofs (`starS2Num`, `starS3`, `numStarS3Margin`); no `sorry` since fix round 1 |
| `EG/Proof/Num/L17s.lean` | 14 proofs (all of L17s.lean) |
| `EG/Proof/Num/OV.lean` | 7 proofs (all of OV.lean) |
| `EG/Proof/Num/CC.lean` | 4 proofs (all of CC.lean) |
| `EG/Proof/Num/WellDef.lean` | 4 proofs (all of WellDef.lean; new in fix round 1) |
| `EGTest/ProbeNUM.lean` | non-vacuity checks (fix round 1: Step 0 witness `n = 2^128`) |

No new Defs file. Every file compiles (`scripts/check.sh`, `lake build` of the modules); lint 0
findings; `scripts/Axioms.lean` on `EG.Proof.Num.{StarInputs,L17s,OV,CC,WellDef}`: 0 `sorryAx`
(fix round 1). The unit has no declared inputs and no `sorry` left. `EG.Proof.Num.WellDef` is a
new module: the integrator adds it to the root import files if wanted (root files not edited).

## Defs used

- `EG.Star.{L, ell, g, p, Delta, sigma, theta}` (`EG/Defs/Link/Star.lean`, locked) and the Lib API
  `EG/Lib/Link/Star.lean` (`one_le_L`, `ell_le`, `lt_ell`, `two_pow_ten_le_ell`, `p_one`, …).
- `EG.epsC = 2^-5` (`EG/Defs/Constants.lean`).
- `EG.Quot.tCC M = ⌈2 log₂ M⌉₊` (`EG/Defs/Quot/Xprime.lean`): the shared `t^CC` constant (TRIAGE
  §2.10). Importing Xprime pulls the s7 Defs chain into `EG.Spec.Num.CC`; it is already built.
- Mathlib: `Real.exp`, `Real.log`, `Real.logb`, `Real.rpow`, `Nat.choose`,
  `Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`, `Real.exp_neg_one_lt_d9`.

## Nodes: label → Lean name, status, back-translation

Conventions of every statement: `log = log₂` (`Star.L n = logb 2 n`), `e^x = Real.exp x`,
`ln = Real.log`; decimals are exact rationals in ℝ; cardinalities are real variables with exactly
the bounds the manuscript uses (so each statement implies its use). Status: **P** = proved in
stage 1 (0 sorry), **S2** = stage 2 (Spec only, no proof yet).

### s3:lemL17s (Lemma 17\*), `EG/Spec/Num/L17s.lean`

| Lean name (`EG.Spec.…`) | Proof (`EG.…`) | Status |
|---|---|---|
| `NumL17sStep0Statement` | `numL17sStep0` | P (fix round 1) |
| `NumL17sCaseAConstStatement` | `numL17sCaseAConst` | P |
| `NumL17sCaseASigmaStatement` | `numL17sCaseASigma` | P (added in fix round 1) |
| `NumL17sCaseAExponentStatement` | `numL17sCaseAExponent` | P (fix round 1; uses `starS2Num`) |
| `NumL17sBernsteinMarginStatement` | `numL17sBernsteinMargin` | P |
| `NumL17sBernsteinExponentStatement` | `numL17sBernsteinExponent` | P |
| `NumL17sCaseBMeanStatement` | `numL17sCaseBMean` | P |
| `NumL17sCaseBGrowthStatement` | `numL17sCaseBGrowth` | P (fix round 1) |
| `NumL17sCaseBSmallPConstStatement` | `numL17sCaseBSmallPConst` | P |
| `NumL17sCaseBLargePConstStatement` | `numL17sCaseBLargePConst` | P |
| `NumL17sCaseBExponentStatement` | `numL17sCaseBExponent` | P (fix round 1; uses `starS2Num`, `starS3`) |
| `NumL17sStep3Statement` | `numL17sStep3` | P (fix round 1) |
| `NumL17sStep4Statement` | `numL17sStep4` | P (fix round 1) |
| `NumL17sStep5Statement` | `numL17sStep5` | P |

Back-translation (domain hypotheses of (eqStar) abbreviated "dom": `n ≥ 2`, `2^-7 ≤ ε' ≤ 1`,
`0 < ρ ≤ 1`; quoted TeX in the docstrings of the Spec file):

- **Step0.** TeX: "`n > θ_* ≥ 2^19ℓ_*²L³/ρ²`, and so `ρn ≥ ρ²n > 2^19ℓ_*²L³ ≥ 2^39` … Also
  `7uL < 7nL/θ_* ≤ 7ρ²n/(2^19ℓ_*²L²) ≤ 2^-36ρn`." Lean: for dom, `u ≥ 1` and `θ_*·u < n`:
  `2^39 < ρn` and `7uL ≤ 2^-36·ρn`. (TeX's `<` in the middle of the second chain is only used as
  `≤`.)
- **CaseAConst.** TeX: "`(0.1ρ/ℓ_*)·(2^19ℓ_*²L³u/(192ρ²L²)) ≥ 273ℓ_*uL`". Lean: `273 ≤ 0.1·2^19/192`.
- **CaseAExponent.** TeX: "`p_*|Cen|/8 ≥ p_*ε'|W|/(192L²) ≥ … ≥ 273ℓ_*uL ≥ 18uL`". Lean: for dom,
  reals `u ≥ 1`, `W ≥ θ_*u`, `C ≥ W/σ_*`: `273ℓ_*uL ≤ p_*C/8` and `18uL ≤ 273ℓ_*uL`.
- **BernsteinMargin.** TeX: "`0.09/4.2>1/47`". Lean: `1/47 < 0.09/4.2`.
- **BernsteinExponent.** TeX: "Since `2(β+Δ_*a/3)=4Δ_*|X|+0.2Δ_*|X|` and `0.09/4.2>1/47`, it gives
  `… ≤ exp(−0.09|X|²/(4Δ_*|X|+0.2Δ_*|X|)) ≤ exp(−|X|/(47Δ_*))`", with `β = 2Δ_*|X|`,
  `a = 0.3|X|`. Lean: for `X, Δ > 0`: `2(2ΔX + Δ(0.3X)/3) = 4ΔX + 0.2ΔX`, `(0.3X)² = 0.09X²`, and
  `exp(−0.09X²/(4ΔX+0.2ΔX)) ≤ exp(−X/(47Δ))`.
- **CaseBMean.** TeX: "`EZ ≥ (1−e^-1)|X| ≥ 0.63|X|`", "`EZ−0.3|X| ≥ 0.33|X|`". Lean:
  `0.63 ≤ 1 − e^-1` and `0.63 − 0.3 = 0.33`.
- **CaseBGrowth.** TeX: "`|A_i(W)| ≥ Z ≥ 0.33|X| ≥ 0.165ε'|W|/L² ≥ g_*|W|`" (with
  `|X| ≥ ε'|W|/(2L²)`). Lean: for `n ≥ 2`, `2^-7 ≤ ε' ≤ 1`, `W ≥ 0`, `X ≥ ε'W/(2L²)`:
  `0.165ε'W/L² ≤ 0.33X` and `g_*W ≤ 0.165ε'W/L²`.
- **CaseBSmallPConst.** TeX: "the exponent is at least `2^19uL/28200 ≥ 18uL` (indeed
  `2^19/28200 > 18.59`…)". Lean: `94·300 = 28200`, `18.59 < 2^19/28200`, `18 ≤ 18.59`.
- **CaseBLargePConst.** TeX: "`Δ_* ≤ 13p_*^-2 < 13/0.0121 < 1075`, … `2^19ℓ_*²uL/(94·1075) ≥
  5ℓ_*²uL ≥ 18uL`". Lean: `0.11² = 0.0121`, `13/0.0121 < 1075`, `5 ≤ 2^19/(94·1075)`, and
  `∀ ℓ ≥ 2^10, 18 ≤ 5ℓ²`.
- **CaseBExponent.** TeX: "`|X|/(47Δ_*) ≥ ε'θ_*u/(94Δ_*L²) = 2^19ℓ_*²Lu/(94Δ_*ρ²)`" and both
  regimes "`≥ 18uL`". Lean: for dom, `u ≥ 1`, `W ≥ θ_*u`, `X ≥ ε'W/(2L²)`: the inequality, the
  equality, and `18uL ≤ 2^19ℓ_*²Lu/(94Δ_*ρ²)` (the case split on `p_* ≤ 0.11` is in the proof).
- **Step3.** TeX: "using `u ≥ 1`, (S1), and … `L³e^-11L ≤ e^-11` for `L ≥ 1`,
  `(ℓ_*−1)e^-18uL ≤ 2^10L³e^-11L e^-7uL ≤ 0.02e^-7uL`". Lean: `∀ x ≥ 1, x³e^-11x ≤ e^-11`;
  `2^10e^-11 ≤ 0.02`; and for `n ≥ 2`, `u ≥ 1` both inequalities of the chain.
- **Step4.** TeX: "`g_* ≤ 1/8`, … `ln(1+g_*) ≥ g_*−g_*²/2 ≥ 15g_*/16`. … `(ℓ_*−1)g_* > … ≥
  L−2^-9`. Hence `ln((1+g_*)^{ℓ_*−1}) ≥ (15/16)(L−2^-9) ≥ L ln2 = ln n`". Lean: for `n ≥ 2`,
  `2^-7 ≤ ε' ≤ 1`: `g_* ≤ 1/8`, `15g_*/16 ≤ ln(1+g_*)`, `L−2^-9 < (ℓ_*−1)g_*`,
  `L ln2 ≤ (15/16)(L−2^-9)`, and `n ≤ (1+g_*)^{ℓ_*−1}`.
- **Step5.** TeX: "mean at least `0.6ρn`", "`exp(−0.0081·0.6ρn/2) ≤ exp(−0.00243ρn)`",
  "`exp(−0.0081ρn/3) = exp(−0.0027ρn)`", "`0.546ρn > 0.545ρn ≥ |V|/2`",
  "`2e^-ρn/412 ≤ 2e^-ρn/413 e^-7uL ≤ 0.01e^-7uL`. Here we used Step 0: `7uL ≤ 2^-36ρn ≤
  ρn(1/412−1/413)` and `ρn > 2^39`", "`0.03e^-7uL ≤ e^-7uL`". Lean: `0.9·(2/3) = 0.6`,
  `(1−0.09)·0.6 = 0.546`, `0.09² = 0.0081`, `0.0081·0.6/2 = 0.00243`, `0.0081/3 = 0.0027`,
  `1/412 ≤ 0.00243`, `1/412 ≤ 0.0027`, `1.09/2 < 0.546`, `2^-36 ≤ 1/412 − 1/413`,
  `∀ x y, 2^39 < x → y ≤ 2^-36x → 2e^{-x/412} ≤ 2e^{-x/413}e^{-y} ∧ 2e^{-x/413}e^{-y} ≤ 0.01e^{-y}`,
  and `0.02 + 0.01 ≤ 1`.

### (S2), (S3), `EG/Spec/Num/StarInputs.lean` (declared inputs in stage 1; proved in fix round 1, `EG/Proof/Num/StarInputs.lean`)

| Label | Lean Spec | Proof | Used by |
|---|---|---|---|
| [s3:eqS2] (numeric part) | `StarS2NumStatement` | `EG.starS2Num` | CaseAExponent, CaseBExponent (p ≤ 0.11) |
| [s3:eqS3] | `StarS3Statement` | `EG.starS3` | CaseBExponent (both regimes) |
| [s3:eqS3] (margins) | `NumStarS3MarginStatement` | `EG.numStarS3Margin` | `starS3` |

- **S2.** TeX: "`p_* ≥ 0.1ρ/ℓ_*`, so `p_*^-2 ≤ 100ℓ_*²ρ^-2`". Lean: for `n ≥ 2`, `0 < ρ ≤ 1`:
  `0.1ρ/ℓ_* ≤ p_*` and `(p_*)⁻¹² ≤ 100ℓ_*²ρ⁻²`.
- **S3.** TeX: "`Δ_* ≤ 2p^-2+8.34p^-1+2.34`. Hence `Δ_* ≤ 3p^-2` if `p ≤ 0.11`, and
  `Δ_* ≤ 13p^-2` for every `p ∈ (0,1]`." Lean: for `n ≥ 2`, `0 < ρ ≤ 1`: the three bounds, with
  `p = Star.p n ρ`, identical to the S3 conjunct of the blueprint's `StarFactsStatement`.

Stage-1 justification (superseded by fix round 1, which proves both): both are facts of the parameter block (eqStar), which blueprint s3a assigns to the
s3 unit (`EG/Spec/Link/Star.lean`, `StarFactsStatement`, not yet written). They are not numeric
margins but properties of `p_*` (Bernoulli's inequality on the rpow closed form) and of the
ceilings in `d_*, λ_*, Δ_*`; proving them here would duplicate the s3 unit's work. Both are
re-derived in the TeX with ample slack except `8.34·0.11 = 0.9174 ≤ 0.92` (0.3%) and
`2.34·0.0121 = 0.0283 ≤ 0.03` (6%), both checked numerically; they are cheap and can be proved in
stage 2 of this unit if the s3 unit prefers.

### s7:lemWellDef (iii), `EG/Spec/Num/WellDef.lean`

| Lean name | Status |
|---|---|
| `numSDRTerm K m s` (abbreviation: `C(m,s)C(K,s−1)(C(s−1,3)/C(K,3))^s`) | def |
| `NumWellDefSDRSeriesStatement` | P (fix round 1, `numWellDefSDRSeries`) |
| `NumWellDefSDRUseStatement` | P (fix round 1, `numWellDefSDRUse`, corollary of Series) |
| `NumWellDefSDRConstStatement` | P (fix round 1, `numWellDefSDRConst`; `2·0.47^{K/13} ≤ 0.1K^-4` via `0.47 ≤ 1/2` and `e^z ≥ z^10/10!`) |
| `NumWellDefSDRRatioStatement` | P (added in fix round 1, `numWellDefSDRRatio`: `0.49 ≤ 1/2`) |

- **Series.** TeX: "`P(SDR failure) ≤ Σ_{s=4}^m T_s`, `T_s := C(m,s)C(K,s−1)(C(s−1,3)/C(K,3))^s` …
  Altogether `P(SDR failure at u | Past_l) ≤ 8800K^-5 + 2·0.47^{K/13} ≤ K^-4 (K ≥ 10^4)`", with
  "`m ≤ M_l−1 ≤ K/4`". Lean: for naturals `K ≥ 10^4`, `m` with `(m:ℝ) ≤ K/4`:
  `Σ_{s∈[4,m]} T_s ≤ 8800K^-5 + 2·0.47^{K/13}` and `8800K^-5 + 2·0.47^{K/13} ≤ K^-4`.
- **Use.** TeX: "`m ≤ M_l−1 ≤ K/4` with `K := 4M_l`", "`K = 4M_l ≥ 2^42`". Lean: for naturals
  `M ≥ 2^40`, `m ≤ M − 1`: `Σ_{s∈[4,m]} T_s(4M) ≤ (4M)^-4`.
- **Const.** TeX constants: `a_4 = 4e^7K^-5 < 4400K^-5`; `(5e^3/16)(1/13+1/K) < 0.49` for
  `K ≥ 10^4`; `1/(4e) ≤ 1`, `e²/16 ≤ 0.47`; `1/0.53 ≤ 2`; `2·4400 = 8800`; for `K ≥ 10^4`:
  `8800K^-5 ≤ 0.88K^-4` and `2·0.47^{K/13} ≤ 0.1K^-4`; `0.88 + 0.1 ≤ 1`; `M ≥ 2^40 ⇒ 4M ≥ 2^42 ≥
  10^4`. Lean: exactly these.

Numerical re-evaluation (exact union bound via log-gamma): `K^5 Σ T_s` = 0.0354 at `K = 10^4`,
`m = 2500`; 0.0353 at `K = 2·10^4`; 0.0352 at `K = 10^5`; with `m = M−1`, `K = 4M`: 0.0502 at
`M = 19`, 0.0392 at `M = 100`, 0.0353 at `M = 2500` (the manuscript's remark "maximum about 0.0502
near `M_l=19`, tends to 9/256" is confirmed). So `Σ T_s ≤ 0.0354K^-5`, far below both
`8800K^-5 + …` and `K^-4`. The analytic chain has slack: `4e^7 = 4386.5` vs 4400 (0.3%); ratio
`0.4835` vs `0.49` (1.3%); `e²/16 = 0.4618` vs `0.47`; `8800K^-5 ≤ 0.88K^-4` is an equality at
`K = 10^4` (non-strict, as stated).

### s2 overlap constants, `EG/Spec/Num/OV.lean`

| Lean name | Label | Proof | Status |
|---|---|---|---|
| `NumOVChargeSumStatement` | [s2:lemOVgeneric] (a) | `numOVChargeSum` | P (fix round 1, telescoping) |
| `NumOVRearrangeStatement` | [s2:lemOVgeneric] (c) | `numOVRearrange` | P (added in fix round 1) |
| `NumOVInstanceStatement` | [s2:lemOVgeneric] instance c=1 | `numOVInstance` | P (added in fix round 1) |
| `NumOVLogFourThirdsStatement` | [s2:lemOVgeneric] helper (TRIAGE OV-CONST-546) | `numOVLogFourThirds` | P |
| `NumOVConstStatement` | [s2:lemOVgeneric] (a),(c), instance c=1 | `numOVConst` | P |
| `NumLem14tauConstStatement` | [s2:lem14tau] (b) | `numLem14tauConst` | P |
| `NumPropOVConstStatement` | [s2:propOV] | `numPropOVConst` | P |

- **ChargeSum ("OV potential").** TeX: "`cε Σ_{j≥0} 1/(log M + jc_OV)² ≤ cε(1/log²M +
  ∫_0^∞ dx/(log M + xc_OV)²) = cε(1/log²M + 1/(c_OV log M))`, because the summand is decreasing
  in `j`". Lean: for reals `x, c > 0` and every `k`: `Σ_{j<k} 1/(x+jc)² ≤ 1/x² + 1/(cx)` (the
  factor `cε` and the choice `x = log M`, `c = c_OV` are applied by the consumer; the finite
  partial sums are equivalent to the series bound and are what the proof uses).
- **LogFourThirds.** Not a TeX sentence. Lean: `17/41 ≤ log₂(4/3)` and `3^41 ≤ 2^65`.
- **Const.** TeX: "(a) `Δ_{≥M} ≤ cε(1/log²M + 1/(c_OV log M))S ≤ 3.42cεS/log M`", "For `M ≥ 2` we
  have `log M ≥ 1`, so `1/log²M ≤ 1/log M`, and `1+1/c_OV=3.4095… ≤ 3.42`", "`n_0/(1−3.42ε) ≤
  1.12n_0`", "`1/(1−3.42/32)=1.1196… ≤ 1.12`". Lean: `1 + 1/log₂(4/3) ≤ 3.42`; for `c > 0`, real
  `M ≥ 2`: `cε(1/log²M + 1/(log₂(4/3)·log M)) ≤ 3.42cε/log M`; `3.42ε < 1`;
  `1/(1−3.42ε) ≤ 1.12` (`ε = epsC = 2^-5`).
- **Lem14tauConst.** TeX: "`1.5·(128/127) … < 1.52`", "`1.25·(128/127) … < 1.26`", "the looser
  constant `1.6` suffices", "`3.42·1.6ε = 0.171 < 1`", "`n_0/(1−5.472ε) ≤ n_0/(1−5.5ε) = 1.2075…n_0
  ≤ 1.21n_0`", "`1.6(1+1/c_OV) = 5.455…`" (`≤ 5.46`). Lean: exactly these nine facts, with
  `3.42·1.6 = 5.472`.
- **PropOVConst.** TeX: "`5.46εS_r/log M ≤ 6.61εn/log M`" (with `S_r ≤ 1.21n`), "`1.21n ≤ 1.37n`",
  "`6.61εn/log P_r ≤ 7.6εn/log P_r`", "`2dup_r ≤ 15.2εn/log P_r`", "`4dup_r ≤ 30.4εn/log P_r`",
  "`2Δ_{≥P_r} ≤ 13.3εn/log P_r ≤ 16εn/log P_r`". Lean: `5.46·1.21 ≤ 6.61`, `6.61 ≤ 7.6`,
  `1.21 ≤ 1.37`, `2·7.6 = 15.2`, `4·7.6 = 30.4`, `2·6.61 ≤ 13.3`, `13.3 ≤ 16`.

"s5 OV": s5 uses Proposition OV only through (K1) (`1.37n/P_r` ancestors) and Lemma 2.lemTower
(`2.74n/P_{l−2}`); it has no OV constant of its own. Its nearby constant `1.37·898 ≤ 1231`
(s5.tex:156, `1230.26`) is not an OV fact and is left to the s5 unit.

### s7:lemCC (iii) and s7:lemUHsplit (ii), `EG/Spec/Num/CC.lean` (all proved)

| Lean name | Label | Proof |
|---|---|---|
| `NumCCConstStatement` | [s7:lemCC] (iii) | `numCCConst` |
| `NumCCTwoPowStatement` | [s7:lemCC] (iii) | `numCCTwoPow` |
| `NumCCCombineStatement` | [s7:lemCC] (iii) | `numCCCombine` |
| `NumUHsplitConstStatement` | [s7:lemUHsplit] (ii) | `numUHsplitConst` |

- **Const.** TeX: "`Σ|S_w| ≤ 2·1.37nM_l = 2.74nM_l`", "`6e·2.74 < 44.7` and `4e·2.74 < 29.8`".
  Lean: `2·1.37 = 2.74`, `6e·2.74 < 44.7`, `4e·2.74 < 29.8`.
- **TwoPow.** TeX: "With `t = t^CC_l` we have `2^-t ≤ M_l^-2`". Lean: for natural `M ≥ 1`,
  `2^{−tCC M} ≤ M^-2`.
- **Combine.** TeX: "`3M_l t|Pool_l| + (6e/H^cd_l + 4e2^-t)EΣ|S_w|`" … "Finally `t ≤ t+1`" giving
  "`3M_l(t^CC_l+1)|Pool_l| + 44.7nM_l/H^cd_l + 29.8n/M_l`". Lean: for natural `M ≥ 1`, reals
  `H > 0`, `P ≥ 0`, `0 ≤ S ≤ 2.74nM`, with `t = tCC M`:
  `3MtP + (6e/H + 4e·2^-t)S ≤ 3M(t+1)P + 44.7nM/H + 29.8n/M`.
- **UHsplitConst.** TeX: "`24·1.37 = 32.88 < 32.9`", "`44.7+32.9 ≤ 78` and `29.8 ≤ 30`". Lean: the
  same four facts.

## Recorded slacks (actual values)

| Fact | Value | Bound | Relative slack |
|---|---|---|---|
| `0.09/4.2` vs `1/47` | 0.0214286 | 0.0212766 | 0.71% |
| `2^19/28200` vs `18` (and vs `18.59`) | 18.59177 | 18 (18.59) | 3.3% (0.01%) |
| `0.1·2^19/192` vs `273` | 273.0667 | 273 | 0.02% |
| `13/0.0121` vs `1075` | 1074.38 | 1075 | 0.06% |
| `2^19/(94·1075)` vs `5` | 5.1884 | 5 | 3.8% |
| `1 − e^-1` vs `0.63` | 0.63212 | 0.63 | 0.34% |
| `2^10e^-11` vs `0.02` | 0.017103 | 0.02 | 14% |
| `0.00243` vs `1/412` | 0.00243 | 0.0024272 | 0.12% |
| `1 + 1/c_OV` vs `3.42` | 3.409421 | 3.42 | 0.31% |
| `1.6(1+1/c_OV)` vs `5.46` | 5.455073 | 5.46 | 0.09% (via 17/41: 5.458824, 0.02%) |
| `1/(1−3.42/32)` vs `1.12` | 1.119664 | 1.12 | 0.03% |
| `1/(1−5.5/32)` vs `1.21` | 1.207547 | 1.21 | 0.2% |
| `5.46·1.21` vs `6.61` | 6.6066 | 6.61 | 0.05% |
| `3^41` vs `2^65` | 3.6472e19 | 3.6893e19 | 1.2% |
| `6e·2.74` vs `44.7` | 44.68855 | 44.7 | 0.026% (needs `e < 2.718978`) |
| `4e·2.74` vs `29.8` | 29.79237 | 29.8 | 0.026% (same) |
| `24·1.37` vs `32.9` | 32.88 | 32.9 | 0.06% |
| `4e^7` vs `4400` | 4386.53 | 4400 | 0.31% |
| `(5e^3/16)(1/13+10^-4)` vs `0.49` | 0.48345 | 0.49 | 1.3% |
| `e²/16` vs `0.47` | 0.46182 | 0.47 | 1.7% |
| `8800K^-5` vs `0.88K^-4` at `K = 10^4` | equal | – | 0 (non-strict, true) |

## Findings

- **NUM-F1 (T1, wording only).** s2.tex:349 (proof of s2:lemOVgeneric (a)) writes
  "`1+1/c_OV=3.4095…`". The value is `1 + 1/log₂(4/3) = 3.409420…`, so the truncated decimal is
  `3.4094…`, not `3.4095…` (the blueprint s2a already has 3.4094). The inequality `≤ 3.42` it
  supports is true and is proved (`numOVConst`). Manuscript action: replace `3.4095\ldots` by
  `3.4094\ldots`.
- No inequality failed. Every statement was checked numerically; the proved ones are proved.

## Hazards

- **NUM-H1 (duplicate statements).** `StarS2NumStatement` and `StarS3Statement` restate
  conjuncts of the s3 unit's future `StarFactsStatement`. Since fix round 1 both are proved here
  (no stubs), so the s3 unit can reuse `EG.starS2Num` / `EG.starS3`; the integrator should check
  that the two texts agree when that Spec lands (they are copied from the blueprint s3a text, same
  parameters and literals; `0.1 * ρ / ℓ` here vs `1/10 * ρ / ℓ` there, equal by `norm_num`).
- **NUM-H2 (thin margins for stage 2; CLOSED in fix round 1: all proved).** Step 5's `1/412 ≤ 0.00243` (0.12%) is proved.
  The WellDef Series proof must follow the TeX's `a_s` chain with exact `e` bounds; `4e^7 < 4400`
  needs `e < 2.7196` (fine with `exp_one_lt_d9`); the ratio step needs `(s+1)/s)^s ≤ e`, i.e.
  `(1+1/s)^s ≤ e` (Mathlib: `Real.add_one_le_exp` / `one_add_div_pow_le_exp`-style lemmas), and
  the binomial bounds `C(m,s) ≤ (em/s)^s` (Mathlib has `Nat.choose_le_pow_div` and
  `Nat.pow_le_choose`-type lemmas; `(em/s)^s` needs `s^s/s! ≤ e^s`).
- **NUM-H3 (Step 0 non-vacuity; CLOSED in fix round 1).** The hypothesis `θ_*u < n` of Step 0
  needs `n > 2^39`; `EGTest/ProbeNUM.lean` now shows it at `n = 2^128`, `ε' = ρ = u = 1`
  (`Star.L = 128`, `Star.ell = 2^31`, `Star.theta = 2^102`), as the reviewer suggested.
- **NUM-H4 (heavier import).** `EG.Spec.Num.CC` imports `EG.Defs.Quot.Xprime` only for
  `EG.Quot.tCC`. If `tCC` ever moves to a lighter Defs file, the import can shrink.

## Open questions

- Should the stage-2 proofs of the parameter statements (Step 0, Step 4, cases (a)/(b)) be the
  ones the s3 unit's L17\* proof calls? They are stated so that L17\* can use them directly; the
  s3 unit should confirm the shapes (reals for cardinalities, `θ_*u < n` for Step 0).
- The WellDef use form takes `m ≤ M − 1` (ℕ subtraction; `M ≥ 2^40` so it is the manuscript's
  value). The s7 consumer (Lemma WellDef (iii) Spec, P-1 probe) must match `K^{HUB}_l = 4M_l` to
  `4 * M` with `M = run.M G l`.

## Fix round 1 (2026-09-29; review `work/p2b/NUM.review1.md`)

Each reviewer item was re-checked before it was acted on.

| Item | Verdict | Action |
|---|---|---|
| I-1 (minor) (S3) margins only inside a declared input; `p^-2 ≤ 100ℓ²ρ^-2` declared though it follows from `p ≥ 0.1ρ/ℓ` | valid | **fixed**, going further than suggested: `NumStarS3MarginStatement` (new, `[s3:eqS3]`) states the margins for every real `p > 0` (`p ≤ 0.11 ⇒ 2p⁻²+8.34p⁻¹+2.34 ≤ 3p⁻²`; `p ≤ 1 ⇒ … ≤ 13p⁻²`) and is proved (`numStarS3Margin`). The two former declared inputs are now **proved** from the locked Defs and the Lib API, so no inputs remain: `starS2Num` by Bernoulli (`one_add_mul_le_pow`) on `(1-p_*)^{ℓ_*-1} = (1-ρ)/(1-0.9ρ)` (`Star.one_sub_p_pow`), giving `(ℓ_*-1)p_* ≥ 0.1ρ/(1-0.9ρ) ≥ 0.1ρ`, and its second conjunct is derived from the first; `starS3` from `d_* < 1/p+1`, `λ_* < 6/p+1`, `⌈x⌉ < x+1` (exact bound `2p⁻²+(25/3)p⁻¹+7/3`) plus the margins. The Spec texts of `StarS2NumStatement` / `StarS3Statement` are unchanged; only the file docstring changed (no longer "declared inputs"). |
| I-2 (minor) ten statements unproved | valid (status) | **fixed**: all ten proved, 0 sorry: `numL17sStep0`, `numL17sCaseAExponent`, `numL17sCaseBGrowth`, `numL17sCaseBExponent`, `numL17sStep3`, `numL17sStep4` (`EG/Proof/Num/L17s.lean`), `numWellDefSDRSeries`, `numWellDefSDRUse`, `numWellDefSDRConst` (`EG/Proof/Num/WellDef.lean`, new), `numOVChargeSum` (`EG/Proof/Num/OV.lean`). No statement was changed to make a proof go through. |
| I-3 (cosmetic) WellDef docstring names a missing proof file | valid | **fixed** by creating `EG/Proof/Num/WellDef.lean` (the docstring is now correct). |
| I-4 (cosmetic) small facts not stated | valid | **fixed** with new statements (existing statements untouched): `NumL17sCaseASigmaStatement` (`3|W|/σ_* = g_*|W|`), `NumOVInstanceStatement` (`(1+ε)(2/3) < 3/4`, value 0.6875), `NumWellDefSDRRatioStatement` (`0.49 ≤ 1/2`), `NumOVRearrangeStatement` (OV(c): `S ≤ n_0 + 3.42cεS ⇒ S ≤ n_0/(1−3.42cε)` for `3.42cε < 1`); all proved. |
| I-5 (cosmetic) Step 0 witness | valid | **fixed**: witness in `EGTest/ProbeNUM.lean` (`L_two_pow`, `ell_two_pow`, `theta_two_pow`, and the full hypothesis list of Step 0 at `n = 2^128`); NUM-H3 closed. |
| I-6 (cosmetic) TRIAGE "needs e < 2.7188" | not an issue for this unit | `e < 2.7188` is a correct *sufficient* condition (stricter than the exact threshold `e < 2.718978`); `work/p2/TRIAGE.md` is integrator-owned, so it was not edited. This file and `EG/Proof/Num/CC.lean` record the exact threshold. Integrator may change the TRIAGE wording to `e < 2.71897`. |

Proof notes (fix round 1).
- Step 4: the TeX's `ln(1+g) ≥ g − g²/2` is not in Mathlib; the proof uses the third-order
  bound `Real.abs_log_sub_add_sum_range_le` (`ln(1+g) ≥ g − g²/2 + g³/3 − g⁴/(1−g)`), which gives
  `15g/16` for `g ≤ 1/8`. The fact is thin at `g = 1/8` (`ln 1.125 = 0.11778` vs `15/128 = 0.11719`,
  0.5%) but true; `g_* = 1/8` needs `n = 2`, `ε' = 1`.
- WellDef: the formal split is `13s ≤ K` (geometric group, `a_s ≤ 2^{4−s}a_4`) versus `13s > K`
  (tail, `a_s ≤ 0.47^s`, sum `≤ 0.47^{⌊K/13⌋+1}/0.53 ≤ 2·0.47^{K/13}`); the TeX's first group is
  `4 ≤ s ≤ ⌈K/13⌉`. Both cover `[4,m]`; the ratio step is applied only for `13s < K`, as in the TeX.
- The TeX's `(s−1)^{2s+1} ≤ s^{2s+1}` step is used as `((s−1)/K)^{2s+1} ≤ (s/K)^{2s+1}`.
- `2·0.47^{K/13} ≤ 0.1K^{−4}` for all real `K ≥ 10^4` (the "short analysis argument" of stage 1):
  `0.47^{K/13} ≤ 2^{−K/13} = e^{−z}` with `z = (K/13)ln 2 ≥ 500`, `e^{−z} ≤ 10!/z^{10}`,
  `K ≤ 19z`, and `20·10!·19^4 ≤ 500^6`.

Math findings (unchanged by the fixes; no inequality failed):
- NUM-F1 / MF-1 (T1): s2.tex:349 `3.4095…` should read `3.4094…`.
- MF-2 (T1, confirmed by the proofs): L17* case (b), `p_* > 0.11`, drops the factor `ρ^{-2} ≥ 1`
  silently (`numL17sCaseBExponent` uses `ρ² ≤ 1`); Step 0's `n > θ_* ≥ 2^19ℓ_*²L³/ρ²` silently
  uses `ε' ≤ 1` (`numL17sStep0` uses `ε'ρ ≤ 1`). Suggested wording: "(using ρ ≤ 1)",
  "(using ε' ≤ 1)".

Checks: `scripts/check.sh` on the five proof files and `EGTest/ProbeNUM.lean`: rc=0, 0 errors,
0 sorry, no warnings; `lake build EG.Proof.Num.{StarInputs,L17s,OV,CC,WellDef}` succeeds;
`scripts/Axioms.lean --prefix EG` on each: 0 `sorryAx`, 0 violations; `python3 -I scripts/lint.py`:
0 findings.

## Proof round 1 (stage 3, 2026-09-29; re-run after an interrupted attempt)

Specs frozen (review round 2: approve); no Spec, Defs, root or integrator-owned file was edited in
this round. Every probe node was already proved in fix round 1; this round re-verified the proofs
against the frozen Specs from a clean build rather than re-writing them.

- **Proved (32/32, 0 sorry):** every `def …Statement` of `EG/Spec/Num/{L17s,StarInputs,WellDef,OV,CC}.lean`
  (14 + 3 + 4 + 7 + 4) has exactly one `theorem … : EG.Spec.<Name>Statement` in
  `EG/Proof/Num/{L17s,StarInputs,WellDef,OV,CC}.lean` (checked by a script matching Spec names to
  theorem types). 1190 lines of proof, 50 theorems/lemmas (helpers private, plus the public
  `inv_logb_four_thirds_le`).
- **Declared inputs:** none (the unit has no stubs; (S2)/(S3) are proved by `starS2Num`/`starS3`).
- **Checks run this round:** `lake build EG.Proof.Num.{StarInputs,L17s,OV,CC,WellDef} EGTest.ProbeNUM`:
  success (no errors); `python3 -I scripts/lint.py`: 0 findings; `lake env lean --run scripts/Axioms.lean
  --prefix EG` on the five proof modules: 984 constants, 0 `sorryAx`, 0 meta-scan hits, 0 violations.
  `scripts/lock.py check`: the five `EG/Spec/Num/*` files are PENDING (not yet locked; integrator
  action); its single violation is `CONVENTIONS.md` changed, which is not a file of this unit.
- **What remains:** nothing for this unit. Integrator actions only: add `EG.Proof.Num.WellDef` to the
  root import files, lock the five Spec files.
- **Stuck goals:** none.
- **Slack:** unchanged from the table "Recorded slacks" above; the thinnest are `6e·2.74 < 44.7` and
  `4e·2.74 < 29.8` (0.026%; the proof uses `Real.exp_one_lt_d9`, `e < 2.7182818286`, well below the
  threshold 2.718978), `0.1·2^19/192 ≥ 273` (0.02%), `13/0.0121 < 1075` (0.06%), `1/412 ≤ 0.00243`
  (0.12%), `8800K^-5 ≤ 0.88K^-4` (equality at `K = 10^4`, non-strict as stated).
- **Math findings:** unchanged: MF-1 (T1, s2.tex:349 `3.4095…` → `3.4094…`) and MF-2 (T1, three silent
  uses of `ρ ≤ 1` / `ε' ≤ 1` in the L17* proof). No inequality failed.

Re-verification (stage 3, proof round 1, second re-run, 2026-09-29): no file edited.
`lake build EG.Proof.Num.{StarInputs,L17s,OV,CC,WellDef} EGTest.ProbeNUM`: success;
`python3 -I scripts/lint.py`: 0 findings; `scripts/Axioms.lean --prefix EG` on the five proof
modules: 984 constants, 0 `sorryAx`, 0 violations; every `…Statement` of `EG/Spec/Num/*.lean` has
exactly one proof theorem in `EG/Proof/Num/*.lean`. State unchanged: 32/32 proved, no declared
inputs, no stuck goals.

Re-verification (stage 3, proof round 1, third re-run, 2026-09-30): no Lean file edited.
`lake build EG.Proof.Num.{StarInputs,L17s,OV,CC,WellDef} EGTest.ProbeNUM`: success (2261 jobs);
`python3 -I scripts/lint.py`: 0 findings; `scripts/Axioms.lean --prefix EG` on the five proof
modules: 984 constants, 0 `sorryAx`, 0 meta-scan hits, 0 violations; each of the 32 `…Statement`s of
`EG/Spec/Num/*.lean` is the type of a theorem in `EG/Proof/Num/*.lean`. State unchanged: 32/32
proved, no declared inputs, no stuck goals, math findings MF-1/MF-2 (T1) unchanged.
