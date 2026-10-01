# Review round 1 of unit NUM (cheap numeric probes): Specs

Reviewer: clean-room statement reviewer, round 1 (2026-09-29). Scope: `EG/Spec/Num/{L17s,StarInputs,WellDef,OV,CC}.lean`,
the stubs `EG/Proof/Num/StarInputs.lean`, the test file `EGTest/ProbeNUM.lean`, design note `work/p2b/NUM.md`.
No Lean file was edited. The manuscript is a CANDIDATE proof (AI-reviewed only).

**Verdict: approve**, with the minor and cosmetic items below. No statement is false, none is vacuous, and none is
weaker than its use. No inequality of the manuscript failed.

## Checks run

- `python3 -I scripts/lint.py`: 0 findings.
- `scripts/check.sh EGTest/ProbeNUM.lean`: rc=0, 0 errors, 0 sorry. `scripts/check.sh EG/Proof/Num/StarInputs.lean`:
  rc=0, exactly 2 sorry warnings (the two declared-input stubs). The Spec and Proof oleans of the unit exist.
- A scratch file (`/tmp/NumReview.lean`, not committed) compiles and shows:
  - **Step 0 is not vacuous** (this closes hazard NUM-H3): `Star.L (2^128) = 128`, `Star.ell (2^128) = 2^31`, and
    `Star.theta (2^128) 1 1 * 1 < 2^128` (θ = 2^102). The hypotheses of `NumL17sStep0Statement` therefore hold at
    `n = 2^128`, `ε' = ρ = u = 1`.
  - The parse checks: `1 / Real.logb 2 M ^ 2 = 1 / (logb 2 M)^2` (rfl), and `numSDRTerm` unfolds to
    `C(m,s)·C(K,s−1)·(C(s−1,3)/C(K,3))^s`.
- An independent floating-point re-evaluation of every constant (values below).

## (1) Fidelity: back-translation against the TeX

### s3:lemL17s (`L17s.lean`), checked against s3.tex:402–597, eqStar s3.tex:227–279, BBD s1.tex:1161

| Spec | Back-translation | TeX | OK? |
|---|---|---|---|
| Step0 | n ≥ 2, ε' ∈ [2^-7,1], ρ ∈ (0,1], u ≥ 1, θ_*u < n ⇒ 2^39 < ρn ∧ 7uL ≤ 2^-36ρn | "θ_*u ≤ \|N_G(U)\| < n … ρn ≥ ρ²n > 2^19ℓ_*²L³ ≥ 2^39 … 7uL < … ≤ 2^-36ρn" | yes. The second conclusion is non-strict, which is exactly how Step 5 uses it. True: 7ρ/(2^19ℓ²L²) ≤ 7/2^39 ≤ 2^-36. |
| CaseAConst | 273 ≤ 0.1·2^19/192 | "(0.1ρ/ℓ_*)·(2^19ℓ_*²L³u/(192ρ²L²)) ≥ 273ℓ_*uL" | yes (273.0667) |
| CaseAExponent | dom, u ≥ 1, θu ≤ W, W/σ ≤ C ⇒ 273ℓuL ≤ pC/8 ∧ 18uL ≤ 273ℓuL | "p_*\|Cen\|/8 ≥ p_*ε'\|W\|/(192L²) ≥ … ≥ 273ℓ_*uL ≥ 18uL", with \|Cen\| ≥ \|W\|/σ_* and \|W\| ≥ θ_*u | yes. True given (S2): pC/8 ≥ 0.1·2^19ℓLu/(192ρ) ≥ 273ℓuL. |
| BernsteinMargin | 1/47 < 0.09/4.2 | "0.09/4.2 > 1/47" | yes |
| BernsteinExponent | X, Δ > 0: 2(2ΔX + Δ(0.3X)/3) = 4ΔX + 0.2ΔX, (0.3X)² = 0.09X², exp(−0.09X²/(4ΔX+0.2ΔX)) ≤ exp(−X/(47Δ)) | BBD exponent a²/(2(β+ba/3)) with β = 2Δ_*\|X\|, b = Δ_*, a = 0.3\|X\| | yes |
| CaseBMean | 0.63 ≤ 1 − e^-1, 0.63 − 0.3 = 0.33 | "EZ ≥ (1−e^-1)\|X\| ≥ 0.63\|X\|", "EZ − 0.3\|X\| ≥ 0.33\|X\|" | yes |
| CaseBGrowth | n ≥ 2, ε' ∈ [2^-7,1], W ≥ 0, X ≥ ε'W/(2L²) ⇒ 0.165ε'W/L² ≤ 0.33X ∧ gW ≤ 0.165ε'W/L² | "\|A_i(W)\| ≥ Z ≥ 0.33\|X\| ≥ 0.165ε'\|W\|/L² ≥ g_*\|W\|" | yes (1/8 ≤ 0.165) |
| CaseBSmallPConst | 94·300 = 28200, 18.59 < 2^19/28200, 18 ≤ 18.59 | "2^19uL/28200 ≥ 18uL (indeed 2^19/28200 > 18.59)" | yes (18.5918) |
| CaseBLargePConst | 0.11² = 0.0121, 13/0.0121 < 1075, 5 ≤ 2^19/(94·1075), ∀ℓ ≥ 2^10, 18 ≤ 5ℓ² | "Δ_* ≤ 13p_*^-2 < 13/0.0121 < 1075 … ≥ 5ℓ_*²uL ≥ 18uL" | yes |
| CaseBExponent | dom, u ≥ 1, θu ≤ W, X ≥ ε'W/(2L²) ⇒ ε'θu/(94ΔL²) ≤ X/(47Δ), = 2^19ℓ²Lu/(94Δρ²), 18uL ≤ that | "\|X\|/(47Δ_*) ≥ ε'θ_*u/(94Δ_*L²) = 2^19ℓ_*²Lu/(94Δ_*ρ²)" + both regimes | yes. True given (S2), (S3); the large-p regime also uses ρ^-2 ≥ 1 (see math finding MF-2). |
| Step3 | ∀x ≥ 1, x³e^{-11x} ≤ e^{-11}; 2^10e^{-11} ≤ 0.02; n ≥ 2, u ≥ 1 ⇒ (ℓ−1)e^{-18uL} ≤ 2^10L³e^{-11L}e^{-7uL} ≤ 0.02e^{-7uL} | Step 3 display | yes. x³e^{-11x} is decreasing on [1,∞). 2^10e^-11 = 0.0171. |
| Step4 | n ≥ 2, ε' ∈ [2^-7,1] ⇒ g ≤ 1/8, 15g/16 ≤ ln(1+g), L − 2^-9 < (ℓ−1)g, L ln2 ≤ (15/16)(L − 2^-9), n ≤ (1+g)^(ℓ−1) | Step 4 | yes. Strictness matches the TeX (">" in the third item). ℓ − 1 in ℕ is harmless since ℓ ≥ 2^10. |
| Step5 | the eleven conjuncts listed in NUM.md | Step 5 + Conclusion | yes (the two Chernoff exponents vs 1/412 imply e^{-0.00243x} + e^{-0.0027x} ≤ 2e^{-x/412}) |

Declared inputs (`StarInputs.lean`), checked against s3.tex:246–262:
- `StarS2NumStatement`: n ≥ 2, 0 < ρ ≤ 1 ⇒ 0.1ρ/ℓ ≤ p ∧ p^-2 ≤ 100ℓ²ρ^-2. Matches (S2)'s numeric sentence, and it
  is true (Bernoulli: (ℓ−1)p ≥ 0.1ρ/(1−0.9ρ) ≥ 0.1ρ).
- `StarS3Statement`: the three bounds of (S3) with p = Star.p n ρ. Matches, and it is true: 25/3 ≤ 8.34, 7/3 ≤ 2.34;
  p ≤ 0.11 gives 8.34p ≤ 0.9174 ≤ 0.92 and 2.34p² ≤ 0.0283 ≤ 0.03; p ≤ 1 gives 12.68 ≤ 13. The ceilings are ℕ-ceilings
  of positive reals, as in the TeX.
- Both agree with the blueprint's `StarFactsStatement` conjuncts (blueprint_s3a.md:304–307), up to literals:
  `0.1 * ρ / ℓ` here vs `1/10 * ρ / ℓ` there, which are equal (norm_num) but not syntactically identical (see NUM-H1).

### s7:lemWellDef (iii) (`WellDef.lean`), checked against s7.tex:432–556

- `numSDRTerm K m s` = C(m,s)·C(K,s−1)·(C(s−1,3)/C(K,3))^s, all Nat.choose cast to ℝ. This is exactly T_s.
- `Series`: ∀ K, m ∈ ℕ, K ≥ 10^4, m ≤ K/4 (real) ⇒ Σ_{s=4}^m T_s ≤ 8800K^-5 + 2·0.47^{K/13} ∧ 8800K^-5 + 2·0.47^{K/13} ≤ K^-4.
  This is the displayed "Altogether" chain, under the hypothesis "m ≤ K/4" that the proof uses. It is more general
  than the use (it does not need 4 | K) and it is true: I re-checked every step of the analytic chain (T_s ≤ a_s,
  a_4 = 4e^7K^-5, ratio ≤ (5e³/16)(s+1)/K < 0.49 < 1/2 for s < K/13, the tail a_s ≤ 0.47^s for s > K/13, and the
  two groups cover [4,m]). Numerically K^5·ΣT_s = 0.03537 (K = 10^4, m = 2500), 0.03533 (K = 10003, m = 2500),
  0.03527 (K = 2·10^4), 0.03518 (K = 10^5), 0.05017 (K = 76, m = 18, i.e. M = 19): the TeX remark "about 0.0502
  near M_l = 19" is confirmed.
- `Use`: M ≥ 2^40, m ≤ M − 1 ⇒ Σ_{s=4}^m T_s(4M) ≤ (4M)^-4. This is (iii)'s numeric content, "m ≤ M_l − 1 ≤ K/4, K = 4M_l".
- `Const`: all nine conjuncts are quoted from the proof and are true. 4e^7 = 4386.53; (5e³/16)(1/13 + 10^-4) = 0.48345;
  e²/16 = 0.46182; log(2·0.47^{10^4/13}) = −580.1 vs log(0.1·10^-16) = −39.1; 8800K^-5 ≤ 0.88K^-4 is an equality at
  K = 10^4 (non-strict, as stated).
- `0.47^{K/13}` is rpow with a positive base, and K^-5 is zpow. Correct.

### s2 OV (`OV.lean`), checked against s2.tex:278–374, 470–495, 839–944

- `ChargeSum`: x, c > 0, ∀k: Σ_{j<k} 1/(x+jc)² ≤ 1/x² + 1/(cx). This is the series bound in partial-sum form
  (equivalent for non-negative terms). It is true (integral comparison for j ≥ 1). It is more general than the use
  (x = log M ≥ 1, c = c_OV).
- `LogFourThirds`: 17/41 ≤ log₂(4/3) ∧ 3^41 ≤ 2^65. These are equivalent, and true (3^41/2^65 = 0.9886). This is a
  helper, labelled as such.
- `Const`: 1 + 1/c_OV ≤ 3.42 (3.40942); ∀c > 0, M ≥ 2 (real): cε(1/log²M + 1/(c_OV log M)) ≤ 3.42cε/log M;
  3.42ε < 1; 1/(1 − 3.42ε) ≤ 1.12 (1.11966). This matches (a) (second inequality), its proof, and the instance c = 1.
- `Lem14tauConst`: the nine facts of the proof of (b), all true. The thin one is 1.6(1 + 1/c_OV) = 5.45507 ≤ 5.46.
- `PropOVConst`: the seven constants of the proof of Prop OV, all true (5.46·1.21 = 6.6066 ≤ 6.61).
- `ε = epsC = 2^-5` and `log = logb 2` are as in the manuscript.

### s7 CC (`CC.lean`), checked against s7.tex:757–847, 1096–1154

- `Const`: 2·1.37 = 2.74; 6e·2.74 < 44.7 (44.6886); 4e·2.74 < 29.8 (29.7924). Both need e < 2.718978.
- `TwoPow`: M ≥ 1 ⇒ 2^{−tCC M} ≤ M^-2, with tCC M = ⌈2 log₂ M⌉₊ (the locked `EG.Quot.tCC`). Matches, and is more
  general than M_l ≥ 2^40.
- `Combine`: M ≥ 1, H > 0, P ≥ 0, 0 ≤ S ≤ 2.74nM ⇒ 3MtP + (6e/H + 4e·2^-t)S ≤ 3M(t+1)P + 44.7nM/H + 29.8n/M.
  This is the final computation of (iii), including "t ≤ t+1". It is true (n ≥ 0 follows from 0 ≤ S ≤ 2.74nM).
- `UHsplitConst`: 24·1.37 = 32.88 < 32.9, 44.7 + 32.9 ≤ 78, 29.8 ≤ 30. Matches.

Every Spec docstring starts with the manuscript label and quotes the TeX. No new Defs items: `numSDRTerm` is a Spec
abbreviation, and it is faithful.

## (2) Vacuity

- The closed numeric statements are the manuscript's numeric facts themselves (not vacuous by design).
- The parameter statements have satisfiable hypotheses. The small instance is in `EGTest/ProbeNUM.lean`. For Step 0,
  `n = 2^128` works (reviewer scratch above). Every parameter conclusion has a positive left side (18uL > 0), so none
  is trivial.
- No hypothesis contradicts another. Division-by-zero junk cannot make a conclusion trivially true: under the domain
  hypotheses L ≥ 1, ℓ ≥ 2^10, ε' > 0, and Δ_* ≥ 1 (λ_* ≥ 1). Even with Δ_* = 0 the third conjunct of CaseBExponent
  would read 18uL ≤ 0, which is false, not trivial.
- WellDef: the sums are non-empty for m ≥ 4 and have a positive term (ProbeNUM).

## (3) Declared inputs

- Only two inputs: [s3:eqS2] (numeric part) and [s3:eqS3]. Both are cited by the L17* proof ("\ref{s3:eqS2} and
  |W| ≥ θ_*u give", "\ref{s3:eqS3} and \ref{s3:eqS2} give"). Both are stated as in the TeX, and both are owned by the
  s3 unit's `StarFactsStatement` (TRIAGE §2, blueprint s3a). The stubs have the required `[DECLARED INPUT] [label]`
  form, and they are the only sorries.
- Nothing that the probe must prove is hidden among the inputs, with one reservation (issue I-1): (S3) contains the
  L17* margin `8.34·0.11 = 0.9174 ≤ 0.92` (0.3%), which is a "cheap numeric" fact. Its real-arithmetic core is not
  proved by this unit.

## (4) Hygiene

Lint: 0 findings. The modules follow the module-system header rules. The sorries are only in the stubs.

## Issues

- **I-1 (minor).** The (S3) real-arithmetic margins (`2p^-2 + 8.34p^-1 + 2.34 ≤ 3p^-2` for 0 < p ≤ 0.11, and
  `≤ 13p^-2` for 0 < p ≤ 1) sit only inside the declared input `StarS3Statement`. `p^-2 ≤ 100ℓ²ρ^-2` is a two-line
  consequence of `0.1ρ/ℓ ≤ p`, and it is also declared rather than derived. Fix: add a proved in-unit lemma (e.g.
  `NumStarS3MarginStatement : ∀ p : ℝ, 0 < p → (p ≤ 0.11 → 2p⁻¹² + 8.34p⁻¹ + 2.34 ≤ 3p⁻²) ∧ (p ≤ 1 → … ≤ 13p⁻²)`),
  and derive the second S2 conjunct from the first. The thin 0.3% margin would then be covered by the probe.
- **I-2 (minor, status, not a Spec defect).** Ten statements have no proof yet: Step0, CaseAExponent, CaseBGrowth,
  CaseBExponent, Step3, Step4, the three WellDef statements and ChargeSum. They include the WellDef(iii) series,
  which the task names explicitly. All ten were checked true above (see NUM-H2 for the proof plan).
- **I-3 (cosmetic).** `EG/Spec/Num/WellDef.lean`'s header says "Proofs: `EG/Proof/Num/WellDef.lean`", but that file
  does not exist yet. State "(stage 2)".
- **I-4 (cosmetic, completeness).** Some small numeric facts at the same places are not stated: case (a)
  `3/σ_* = g_*` (3ε'/(24L²) = ε'/(8L²)); the OV instance c = 1 `(1+ε)(2/3) < 3/4` (0.6875); WellDef `0.49 ≤ 1/2`
  (the ratio used for `a_s ≤ 2^{4−s}a_4`); the rearrangement of OV(c). Add them to the Const statements, or say in
  NUM.md that they are left to the consumers.
- **I-5 (cosmetic).** Add the Step 0 witness `n = 2^128` (reviewer scratch, compiles) to `EGTest/ProbeNUM.lean`, and
  close NUM-H3.
- **I-6 (cosmetic, docs).** TRIAGE §4 says the CC constants "need e < 2.7188". The actual threshold is e < 2.718978
  (44.7/16.44). The TRIAGE value is a stricter sufficient condition, so it is harmless. NUM.md has the right value.

## Math findings (manuscript)

- **MF-1 (T1, wording; confirms NUM-F1).** s2.tex:349: "1 + 1/c_OV = 3.4095…" should read "3.4094…" (value
  3.4094208…). The inequality ≤ 3.42 it supports is true.
- **MF-2 (T1, wording/tiny gap; statement true).** s3.tex, L17* case (b), bullet p_* > 0.11: "the exponent is at least
  2^19ℓ_*²uL/(94·1075)" silently drops the factor ρ^-2 ≥ 1 (it uses ρ ≤ 1). Similarly Step 0 "n > θ_* ≥
  2^19ℓ_*²L³/ρ²" silently uses ε' ≤ 1. Suggested wording: "(using ρ ≤ 1)" and "(using ε' ≤ 1)".
- No inequality failed. Every constant was re-evaluated; the slacks agree with the table in NUM.md.
