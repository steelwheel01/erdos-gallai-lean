# Audit of unit NUM (cheap numeric probes)

Independent auditor, 2026-09-30 (third audit pass; supersedes the 2026-09-29 text that stood in
this file, and was re-run from scratch against the state after the stage-3 re-verification of
2026-09-30 recorded in `NUM.md`). Scope: `work/p2b/NUM.md` and every file it lists:
`EG/Spec/Num/{L17s,StarInputs,WellDef,OV,CC}.lean` (32 `def …Statement : Prop`),
`EG/Proof/Num/{L17s,StarInputs,WellDef,OV,CC}.lean`, `EGTest/ProbeNUM.lean`, the reviews
`NUM.review1.md` / `NUM.review2.md`, the locked Defs the unit reads (`EG/Defs/Link/Star.lean`,
`EG/Defs/Constants.lean`, `EG/Defs/Quot/Xprime.lean`), `work/p2/TRIAGE.md` §1b–§1c and §4.
Manuscript v6.1 passages re-read in full: s3.tex 220–285 (eqStar, (S1)–(S6)) and 402–597
(Lemma 17\*), s7.tex 455–470 and 486–550 (WellDef (iii)), 757–847 (CC (iii)), 1124–1158
(UH\*-split (ii)), s2.tex 278–374 (Lemma OV), 470–497 (14^τ (b)), 862–920 (Prop OV), s1.tex
1103–1118 (Chernoff), 1161–1175 (Lemma BBD). No Lean file was edited (the auditor writes only
this file). The manuscript is a CANDIDATE proof (AI-reviewed only).

**Verdict: approve.**
(1) The sorry frontier of the unit's five proof modules is empty and the unit declares no
inputs: the frontier equals the set of declared-input stubs (both empty).
(2) No Spec statement was changed after its review: the only Spec edits after review round 1
are five added statements and docstring text (fix round 1), all written before review round 2;
nothing in `EG/Spec/Num/` changed after 21:31:55 on 2026-09-29 (round 2 final text 22:48,
commit `41e8a4e` 22:27, worktree = HEAD for every Lean file of the unit).
(3) No hidden weakening: every hypothesis beyond the (eqStar) domain is supplied by the TeX at
the quoted point; cardinalities are free reals with exactly the manuscript's bounds; the one
auxiliary definition (`numSDRTerm`) is `T_s` verbatim; several statements are strictly stronger
than their use.
(4) Every refutation target of TRIAGE §4 row "Cheap numeric probes" and §1b OV-CONST-546 is a
proved statement; the one target the unit excludes (Cap(i)) is proved elsewhere
(`EG.bmLemma25`, axiom scan 0 `sorryAx`).
(5) The math findings of the author and reviewers (MF-1, MF-2) are T1 wording items, confirmed
with my own values; the earlier audit's AUD-1 is a T1 wording item. Nothing of class T2/T3 and
nothing "suspect": every inequality of the five manuscript passages re-evaluates as true, and the
WellDef (iii) analytic chain was re-derived and numerically cross-checked step by step.

## Checks run (all read-only; 2026-09-30, 00:06–00:20)

| Check | Command / method | Result |
|---|---|---|
| Olean freshness | mtime `.olean` vs `.lean` for the 10 modules and `EGTest/ProbeNUM` | all FRESH (sources 21:08–21:36 on 09-29, oleans later); no build started by me |
| Axiom / sorry scan | `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Num.{StarInputs,L17s,OV,CC,WellDef}` | `inspected 984 constants under [EG]; 0 use sorryAx; 0 meta-scan hits; 0 violations`, rc = 0 |
| Cap(i) lock | same scan on `EG.Proof.Ext.BMLemma25` (olean fresh) | `584 constants; 0 use sorryAx; 0 violations` |
| Token scan | `grep -in "sorry\|axiom\|admit\|native_decide\|maxHeartbeats\|set_option\|unsafe\|opaque\|implemented_by\|decide"` over the 11 files | one hit: the historical docstring sentence `EG/Proof/Num/StarInputs.lean:10` ("(`sorry` stubs)"); no code token, no `set_option`, no `decide` |
| Lint | `python3 -I scripts/lint.py` | `lint (development): 0 findings` |
| Spec ↔ theorem | script: each `def (\w+Statement) : Prop` in `EG/Spec/Num/*` has exactly one `theorem … : EG.Spec.<Name>` in `EG/Proof/Num/*`, and no theorem has a Statement type absent from the Specs | 32 specs, 32 proved, 0 multiple, 0 missing, 0 extra |
| Git | `git status`, `git log --date=iso`, `git diff HEAD`, `git diff 41e8a4e HEAD` on the unit's files | worktree clean for all 11 Lean files (only `work/p2b/NUM.md` modified: the 09-30 re-verification paragraph); Spec history = commits `3a26761` (21:17) and `41e8a4e` (22:27) only; `fc84210` (23:17) touches no file of this unit |
| Spec diff across reviews | `git diff 3a26761 41e8a4e -- EG/Spec/Num/` (every `+`/`−` line read) | additions only: 5 new `def …Statement` (`NumL17sCaseASigma`, `NumStarS3Margin`, `NumWellDefSDRRatio`, `NumOVRearrange`, `NumOVInstance`) and module-docstring text; no existing `def` line removed or altered; `CC.lean` untouched |
| Root imports | `grep -n Num EG.lean EGTest.lean EGCheck.lean` | no match (issue I-1) |
| Load | `uptime`, `ps` | load 1.1; no `lake build` of mine; the axiom scan ran on prebuilt oleans |
| Numerics | independent double-precision re-evaluation of every constant; exact rationals for the identities; exact log-gamma evaluation of `K^5 Σ_{s=4}^m T_s`; log-space check of the `a_s` chain | table at the end; all agree with `NUM.md` and both reviews |

## (1) Sorry frontier = declared-input stubs

The unit declares no inputs. The stage-1 stubs (`starS2Num`, `starS3`) were replaced in fix round
1 by proofs from the locked Defs and the Lib API `EG/Lib/Link/Star.lean` (`Star.one_sub_p_pow`,
`Star.two_le_ell`, `Star.cast_ell_sub_one`, `Star.p_pos`, `Star.p_le_one`, `Star.d_lt`,
`Star.lam_lt`, `Star.Delta_eq`, `Star.one_le_lam`, `Star.lam_le_Delta`, …). The axiom scan over
the five proof modules inspects 984 constants under the `EG` prefix, which covers the Lib and Defs
closure, and finds 0 `sorryAx`. So the frontier is empty and equals the (empty) stub set. Each of
the 32 Spec statements is the type of exactly one theorem, so nothing is proved under a different
name or left out; `EGTest/ProbeNUM.lean` compiles against the same oleans (fresh).

The proofs use only `Real.exp_one_lt_d9`, `Real.exp_one_gt_d9`, `Real.exp_neg_one_lt_d9`,
`Real.log_two_lt_d9`, `Real.log_two_gt_d9`, `Real.add_one_le_exp`, `Real.pow_div_factorial_le_exp`,
`Real.abs_log_sub_add_sum_range_le`, `Nat.choose_le_pow_div`, `one_add_mul_le_pow`,
`sum_geometric_two_le`, `geom_sum_Ico_le_of_lt_one` and `norm_num`/`nlinarith`/`linarith`
arithmetic; no `decide`, no `maxHeartbeats`.

## (2) No Spec changed after its review

Timeline (2026-09-29 unless stated; `git log --date=iso`, file mtimes, review headers):

| Time | Event |
|---|---|
| 21:08–21:17 | stage-1 Specs written; committed in `3a26761` (21:17:31) |
| 21:20 | `NUM.review1.md` (approve, I-1…I-6), against the `3a26761` text |
| 21:24 | commit `3278dd4`: adds `NUM.review1.md` only |
| 21:25:02–21:31:55 | fix round 1 edits to `StarInputs.lean`, `L17s.lean`, `OV.lean`, `WellDef.lean` (`CC.lean` untouched since 21:08) |
| 21:29–21:36 | proof files and `EGTest/ProbeNUM.lean` written |
| 22:27 | commit `41e8a4e` (all 11 Lean files as they are now) |
| 22:48 | `NUM.review2.md` final text (approve); its 32 back-translations match the current files |
| 22:49, 09-30 00:05 | `NUM.md` stage-3 re-verification paragraphs (documentation only) |
| 23:17 | commit `fc84210`: other units' files only |

The diff between the two review commits is additive on `EG/Spec/Num/` (listed above); I read every
changed line. Since no Spec file was written after 21:31:55, the text reviewed in round 2 and
re-verified in the stage-3 rounds is the current text, and it is the text audited here. I also
compared review 2's per-statement back-translations with the current Spec bodies statement by
statement: they agree.

## (3) No hidden weakening (my own back-translation)

Locked Defs read (`EG/Defs/Link/Star.lean:58–103`, `Constants.lean:40`, `Xprime.lean:35`):
`Star.L n = logb 2 n`, `ell n = ⌊2^10 L³⌋₊`, `g = ε'/(8L²)`,
`p = 1 − ((1−ρ)/(1−0.9ρ))^{1/(ℓ−1)}` (the explicit solution of `(1−p)^{ℓ−1} = (1−ρ)/(1−0.9ρ)`),
`d = ⌈1/p⌉₊`, `lam = ⌈6/p⌉₊`, `Delta = lam + ⌈d·lam/3⌉₊`, `sigma = 24L²/ε'`,
`theta = 2^19 ℓ² L³/(ε'ρ²)`, `epsC = 2^-5`, `Quot.tCC M = ⌈2 logb 2 M⌉₊`: the manuscript's
(eqStar), ε and t^CC verbatim. The only auxiliary definition of the unit is
`EG.Spec.numSDRTerm K m s = C(m,s)·C(K,s−1)·(C(s−1,3)/C(K,3))^s` (`Nat.choose` cast to ℝ), which
is `T_s` verbatim; the majorant `aS` is private to the proof file and occurs in no statement.

Parsing hazards checked on the source text: `Real.logb 2 M ^ 2` is `(logb 2 M)^2`; `(Star.p n ρ)⁻¹ ^ 2`
is `p^-2`; `(2:ℝ)^(-7:ℤ)`, `^(-36:ℤ)`, `^(-9:ℤ)`, `K^(-5:ℤ)`, `M^(-2:ℤ)` are zpows;
`(0.47:ℝ)^((K:ℝ)/13)` is `rpow` with positive base; `(1 + Star.g n ε')^(Star.ell n - 1)` has an ℕ
exponent with `ℓ_* ≥ 2^10`; decimals are exact rationals (the identities `0.9·(2/3) = 0.6`,
`(1−0.09)·0.6 = 0.546`, `0.0081·0.6/2 = 0.00243`, `0.0081/3 = 0.0027`, `3.42·1.6 = 5.472`,
`3.42·1.6/32 = 0.171`, `24·1.37 = 32.88` re-checked as exact fractions); no `open` of `EG.Star` /
`Vortex` / `COLTable` (qualified names throughout).

A hypothesis counts as a weakening only if the TeX does not supply it at the quoted point.

| Statement | Hypotheses beyond the (eqStar) domain `n ≥ 2, 2^-7 ≤ ε' ≤ 1, 0 < ρ ≤ 1` | Supplied by the TeX? | Conclusion vs TeX; my re-derivation |
|---|---|---|---|
| Step0 | `1 ≤ u`, `θ_*u < n` | yes ("let u := \|U\| ≥ 1", "θ_*u ≤ \|N_G(U)\| < n") | `2^39 < ρn` (strict, as TeX) ∧ `7uL ≤ 2^-36ρn` (TeX's `<` used as `≤` in Step 5). True: `2^19ℓ²L³u < ε'ρ²n ≤ ρn`, `2^19ℓ²L³u ≥ 2^39Lu ≥ 2^39`; `7uL ≤ 8uL = 2^-36·2^39Lu < 2^-36ρn` |
| CaseAConst / CaseASigma | – / `0 < ε'`, free real `W` | – | `273 ≤ 0.1·2^19/192` (273.067); `3W/σ_* = g_*W` (`3ε'/(24L²) = ε'/(8L²)`) |
| CaseAExponent | `1 ≤ u`, `θ_*u ≤ W`, `W/σ_* ≤ C` | yes ((O3); Prop 13\*(a) "at least \|W\|/σ_* stars") | `273ℓ_*uL ≤ p_*C/8 ∧ 18uL ≤ 273ℓ_*uL`: the ends of the displayed chain. `pC/8 ≥ pε'W/(192L²) ≥ (0.1ρ/ℓ)(2^19ℓ²Lu/(192ρ²)) = 273.07ℓLu/ρ ≥ 273ℓuL` (uses `ρ ≤ 1`, MF-2) |
| BernsteinMargin / BernsteinExponent | `0 < X`, `0 < Δ` | yes ("β > 0" paragraph: `\|X\| > 0`, `Δ_* ≥ 1`) | `1/47 < 0.09/4.2` strict as TeX; `2(2ΔX + Δ(0.3X)/3) = 4.2ΔX`, `(0.3X)² = 0.09X²`, `exp(−0.09X²/(4.2ΔX)) ≤ exp(−X/(47Δ))` ⇔ `0.09/4.2 ≥ 1/47`; matches Lemma BBD's exponent `a²/(2(β+ba/3))` with `β = 2Δ_*\|X\|`, `b = Δ_*`, `a = 0.3\|X\|` |
| CaseBMean / CaseBGrowth | – / `0 ≤ W`, `ε'W/(2L²) ≤ X` | yes (Prop 13\*(b)) | `0.63 ≤ 1−e^-1`, `0.63−0.3 = 0.33`; `0.165ε'W/L² ≤ 0.33X`, `g_*W ≤ 0.165ε'W/L²` (`1/8 ≤ 0.165`) |
| CaseBSmallPConst / CaseBLargePConst | – | – | the constants with the TeX's strictness (`18.59 < 2^19/28200`, `13/0.0121 < 1075`); `∀ ℓ ≥ 2^10, 18 ≤ 5ℓ²` |
| CaseBExponent | `1 ≤ u`, `θ_*u ≤ W`, `ε'W/(2L²) ≤ X` | yes | the display `ε'θu/(94Δ_*L²) ≤ X/(47Δ_*)`, the identity `= 2^19ℓ²Lu/(94Δ_*ρ²)`, and `18uL ≤ 2^19ℓ²Lu/(94Δ_*ρ²)` with `Δ_* = Star.Delta n ρ` (the actual value, ≥ 1). True in both regimes: `p ≤ 0.11 ⇒ Δρ² ≤ 300ℓ²` (via (S3), (S2)), `2^19/28200 ≥ 18`; `p > 0.11 ⇒ Δρ² ≤ Δ < 1075`, `2^19/(94·1075) ≥ 5`, `5ℓ² ≥ 18` |
| Step3 | `1 ≤ u` | yes | `∀ x ≥ 1, x³e^{-11x} ≤ e^{-11}` (`3 ln x − 11x` decreasing for `x > 3/11`); `2^10e^{-11} ≤ 0.02` (0.0171); `(ℓ−1)e^{-18uL} ≤ 2^10L³e^{-11L}e^{-7uL}` (needs `ℓ−1 ≤ 2^10L³`, `18uL ≥ 11L+7uL`); `≤ 0.02e^{-7uL}` |
| Step4 | – | – | `g_* ≤ 1/8`; `15g_*/16 ≤ ln(1+g_*)`; `L − 2^-9 < (ℓ−1)g_*` (strict, as TeX: `(ℓ−1)/(2^10L²) > (2^10L³−2)/(2^10L²) = L − 2^-9/L² ≥ L − 2^-9`); `L ln 2 ≤ (15/16)(L − 2^-9)` (at `L = 1`: 0.6931 ≤ 0.9357, slope 15/16 > ln 2); `n ≤ (1+g_*)^{ℓ−1}` |
| Step5 | `2^39 < x`, `y ≤ 2^-36x` (the Step 0 outputs) | yes ("Here we used Step 0") | nine constants of the Chernoff/threshold arithmetic, `2e^{-x/412} ≤ 2e^{-x/413}e^{-y} ≤ 0.01e^{-y}`, `0.02 + 0.01 ≤ 1`. Chernoff forms match s1:citChernoffGen(a): lower tail `e^{-δ²μ/2}` with `μ = 0.6ρn ≤ EX`, `(1−δ)μ = 0.546ρn`; upper tail `e^{-δ²μ/3}` with `μ = ρn = E\|V\|`, `(1+δ)μ = 1.09ρn`; `\|V\|/2 ≤ 0.545ρn < 0.546ρn` |
| StarS2Num / StarS3 / NumStarS3Margin | none (`p = Star.p n ρ`); Margin: free real `p > 0` | – | verbatim (S2) numeric sentence and (S3). True: Bernoulli gives `(ℓ−1)p ≥ 0.1ρ/(1−0.9ρ) ≥ 0.1ρ`; `Δ_* < 2p^-2 + (25/3)p^-1 + 7/3 ≤ 2p^-2 + 8.34p^-1 + 2.34`; Margin merges the TeX's two sub-steps (`8.34p + 2.34p² ≤ 1` at `p ≤ 0.11`: 0.9457; `12.68 ≤ 13` at `p ≤ 1`) and is at least as strong |
| WellDef Series | `10^4 ≤ K`, `(m:ℝ) ≤ K/4` | yes ("m ≤ M_l−1 ≤ K/4", "(K ≥ 10^4)") | both inequalities of the "Altogether" display over `Icc 4 m`; stronger than the use (no `4 ∣ K`) |
| WellDef Use | `2^40 ≤ M`, `m ≤ M − 1` (ℕ) | yes ("K = 4M_l ≥ 2^42", "m ≤ M_l−1") | `Σ T_s ≤ (4M)^-4` |
| WellDef Ratio / Const | `K ≥ 10^4` where the TeX says so; `M ≥ 2^40` | yes | the quoted constants; `8800K^-5 ≤ 0.88K^-4` non-strict as in the TeX (equality at `K = 10^4`) |
| OV ChargeSum | `0 < x`, `0 < c`, every `k : ℕ` | yes (`log M ≥ 1`, `c_OV > 0`; finitely many ancestors) | `Σ_{j<k} 1/(x+jc)² ≤ 1/x² + 1/(cx)`: the partial-sum form of the series bound, equivalent for non-negative terms; true by `1/(x+jc)² ≤ (1/c)(1/(x+(j−1)c) − 1/(x+jc))` |
| OV LogFourThirds | – | (helper, labelled as such) | `17/41 ≤ log₂(4/3) ∧ 3^41 ≤ 2^65` (equivalent; ratio 0.9886) |
| OV Const / Rearrange / Instance | `0 < c`, `2 ≤ M` (real); `3.42cε < 1`, `S ≤ n₀ + 3.42cεS` | yes (lemma hypotheses; "(a) with M = 2") | (a)'s second inequality in the sharp `c_OV` form without the factor `S ≥ 0` (applied by the consumer); `1 + 1/c_OV ≤ 3.42`; `3.42ε < 1`; `1/(1−3.42ε) ≤ 1.12`; the rearrangement of (c); `(1+ε)(2/3) < 3/4` |
| Lem14tauConst / PropOVConst | – | – | the nine / seven quoted constants (re-evaluated below; each located in the TeX at s2.tex:491–495 and 874–911) |
| CC Const / TwoPow | – / `1 ≤ M` (ℕ) | TeX has `M_l ≥ 2^40`: the statement is stronger | `2·1.37 = 2.74`, `6e·2.74 < 44.7`, `4e·2.74 < 29.8` (both ⇔ `e < 2.7189781`); `2^{-⌈2log₂M⌉} ≤ M^-2` |
| CC Combine | `1 ≤ M`, `0 < H`, `0 ≤ P`, `0 ≤ S ≤ 2.74nM` | yes (`H^cd > 0`; `Σ\|S_w\| ≤ 2·1.37nM_l` is the TeX's own premise, so the s7 counting fact is a hypothesis here, not hidden) | the last four sentences of (iii)'s proof including "t ≤ t+1"; `n ≥ 0` is forced by the hypotheses |
| UHsplitConst | – | – | `24·1.37 = 32.88 < 32.9`, `44.7 + 32.9 ≤ 78`, `29.8 ≤ 30` |

Non-vacuity (`EGTest/ProbeNUM.lean`, compiled): domain instance `n = 2, ε' = ρ = u = 1`
(`Star.L 2 = 1`; `p_*(2,1) = 1 > 0.11` so the large-`p_*` regime occurs); Step 0 at `n = 2^128`
(`L = 128`, `ℓ_* = 2^31`, `θ_* = 2^102 < 2^128`); `T_4 > 0` at `K = 10^4, m = 2500`; the use form
at `M = 2^40`; the OV negative control `1.6(1 + 29/12) = 5.4667 > 5.46` (12/29 too weak) and
`1.6(1 + 41/17) ≤ 5.46`; CC hypotheses with `S > 0`; `tCC 4 = 4`. Conclusions are non-trivial
(`18uL > 0`, `Δ_* ≥ 1`, `L ≥ 1`), so no statement is true by a degenerate denominator.

Coverage remark (not a weakening; for the s3 consumer). Three numeric facts of the L17\* proof are
outside the unit's scope as stated in `NUM.md` and are not among the 32 statements: the Chernoff
instance of case (a) (`δ = 1/2` gives exponent `μ/8`), the (S6)-based steps (`λ_*p_* ≥ 6`;
`d_*p_* ≥ 1` for `e^{-p_*d_*} ≤ e^{-1}`; `d_*p_* ≤ 2` for `β = 2Δ_*\|X\|`), and the preamble
"`s_1 ≥ 8d_*λ_* ≥ 48`". All are properties of (eqStar)/(S6) or a Chernoff instance, all are true,
and blueprint s3a assigns (S6) to the s3 unit. No refutation target is affected.

Conclusion: no statement is weaker than its TeX sentence; CC TwoPow/Combine (all `M ≥ 1`), WellDef
Series (all `K ≥ 10^4`, real `m ≤ K/4`) and NumStarS3Margin (all real `p > 0`) are strictly
stronger.

## (4) Refutation targets covered by proved statements

TRIAGE §4 row "Cheap numeric probes" (TRIAGE.md:332) and §1b OV-CONST-546 / LEM14-CONST-546 /
OV-CONST-TIGHT (TRIAGE.md:88):

| Target | Proved statement(s) (0 `sorryAx`) |
|---|---|
| L17\* margin `0.09/4.2` vs `1/47` | `numL17sBernsteinMargin`; consumed by `numL17sBernsteinExponent` |
| L17\* margin `2^19/28200 ≥ 18` | `numL17sCaseBSmallPConst`; consumed by `numL17sCaseBExponent` (regime `p_* ≤ 0.11`) |
| the other numeric steps of the L17\* proof (Steps 0, 3, 4, 5; cases (a)/(b)) | the remaining 12 `numL17s*` theorems, `starS2Num`, `starS3`, `numStarS3Margin` |
| WellDef (iii) series `Σ T_s ≤ K^-4` for `K ≥ 10^4` | `numWellDefSDRSeries` (both inequalities of the display), `numWellDefSDRUse` (`K = 4M_l`, `m ≤ M_l−1`), with `numWellDefSDRConst`, `numWellDefSDRRatio` |
| OV `17/41` ("use 17/41; 12/29 is not enough; prove OV(a) in its sharp c_OV form") | `numOVLogFourThirds` (17/41 ⇔ `3^41 ≤ 2^65`), `numOVConst` (sharp `c_OV` form of (a), `3.42`), `numLem14tauConst` (`5.46` via 17/41), `numPropOVConst`; negative control 12/29 in `ProbeNUM` |
| OV potential (charge sum of OV(a)) | `numOVChargeSum` |
| CC `44.7`, `29.8` ("needs e < 2.7188") | `numCCConst`, `numCCCombine` (via `Real.exp_one_lt_d9`; exact threshold `e < 2.7189781`, of which TRIAGE's `2.7188` is a sufficient condition) |
| UH\*-split constants consuming them | `numUHsplitConst` |
| Cap(i) (Lemma 25 with constant 18) | not in this unit, by `NUM.md`'s scope; covered elsewhere: `EG.bmLemma25 : EG.Spec.BMLemma25Statement` in `EG/Proof/Ext/BMLemma25.lean`, axiom scan `584 constants; 0 sorryAx` (run today). TRIAGE §1c still says "The lock is still `sorry`"; out of date, integrator-owned. |

"s5 OV": s5 uses Prop OV only through (K1) and Lemma Tower; its constant `1.37·898 ≤ 1231` is an
s5 fact. The author's reading is correct and no OV constant is missing.

## (5) Math findings, classified with my own evidence

| ID | Class | Evidence |
|---|---|---|
| MF-1 / NUM-F1 (s2.tex:349, proof of OV(a): "1+1/c_OV = 3.4095… ≤ 3.42") | **T1** (wording) | `c_OV = ln(4/3)/ln 2 = 0.415037499`, `1 + 1/c_OV = 3.409420840`; the truncated decimal is `3.4094…`. The inequality `≤ 3.42` is true (slack 0.31%) and proved (`numOVConst`, through `17/41`: `1 + 41/17 = 3.41176 ≤ 3.42`). Manuscript action: `3.4095\ldots` → `3.4094\ldots`. |
| MF-2 (s3.tex, proof of L17\*: three silent uses of `ε' ≤ 1` / `ρ ≤ 1`) | **T1** (wording) | (i) Step 0, "n > θ_* ≥ 2^19ℓ_*²L³/ρ²": `θ_* = 2^19ℓ_*²L³/(ε'ρ²) ≥ 2^19ℓ_*²L³/ρ²` iff `ε' ≤ 1`. (ii) Case (a), "(0.1ρ/ℓ_*)·(2^19ℓ_*²L³u/(192ρ²L²)) ≥ 273ℓ_*uL": the left side equals `273.067·ℓ_*Lu/ρ`, so the step needs `ρ ≤ 1`. (iii) Case (b), `p_* > 0.11`, "the exponent is at least 2^19ℓ_*²uL/(94·1075)": `2^19ℓ_*²Lu/(94Δ_*ρ²) ≥ 2^19ℓ_*²Lu/(94·1075)` needs `Δ_*ρ² ≤ 1075`, i.e. `ρ² ≤ 1` on top of `Δ_* < 1075`. All three are hypotheses of the lemma (`ε' ≤ 1`, `ρ ∈ (0,1]`), the statements are true, and `numL17sStep0`, `numL17sCaseAExponent`, `numL17sCaseBExponent` use exactly these hypotheses. Suggested wording: "(using ε' ≤ 1)", "(using ρ ≤ 1)". |
| AUD-1 (s3.tex, case (b) small-`p_*` bullet: "indeed 2^19/28200 > 18.59; this is the tightest inequality of the lemma") | **T1** (wording, cosmetic) | The inequality is true (`2^19/28200 = 18.59177`). As a bound on `18` its slack is 3.3%; within the same proof `0.1·2^19/192 ≥ 273` (273.067, 0.02%), `13/0.0121 < 1075` (1074.38, 0.06%) and `0.00243 ≥ 1/412` (0.0024272, 0.12%) are tighter, so "tightest inequality of the lemma" is not accurate as written. Defensible reading: tightest of the three routes to `18uL`. Suggested wording: drop the clause or write "(the thinnest of the three bounds by 18uL)". Review 2 recorded the same fact as docstring issue I-2. |
| WellDef (iii) "Remark on numerics (not used)": "maximum about 0.0502 near M_l = 19; tends to 9/256" | confirmed, not a finding | exact log-gamma evaluation: `K^5 Σ T_s = 0.050166` at `K = 76, m = 18`; `0.039170` at `K = 400, m = 99`; `0.035374` at `K = 10^4, m = 2500`; `0.035178` at `K = 10^5` (→ `9/256 = 0.035156`). |
| Review 1 I-6 (TRIAGE "needs e < 2.7188") | documentation, not manuscript | exact threshold `e < 44.7/(6·2.74) = 29.8/(4·2.74) = 2.7189781`; `2.7188` is a stricter sufficient condition; harmless. Integrator may correct TRIAGE. |

No T2/T3 and nothing "suspect". Independent evidence for the analytic chain of WellDef (iii) at
`K = 10^4` (log space): `a_4K^5 = 4e^7 = 4386.53 < 4400`; `max_{4 ≤ s < K/13} a_{s+1}/a_s = 0.3864
< 0.49`, and the TeX bound `(5e³/16)((s+1)/K)` is never exceeded over `4 ≤ s < 2500` (max
ratio/bound 0.898); `K^5 Σ_{s ≤ 769} a_s = 4398.9 < 2a_4 = 8773 < 8800`; `T_s ≤ a_s` spot-checked
at `s ∈ {4, 5, 10, 100, 769, 770, 771, 1000, 2500}`; `a_s ≤ 0.47^s` for every `770 ≤ s ≤ 2500`; the
tail `0.47^{770}/0.53` is `e^{-580.7}` against `2·0.47^{K/13} = e^{-580.1}` and `0.1K^-4 = e^{-39.1}`;
`(K/13)ln 0.47 + 4 ln K` is decreasing in `K` (derivative −0.0577 at 10^4), so
`2·0.47^{K/13} ≤ 0.1K^-4` for all `K ≥ 10^4`. The two groups `13s ≤ K` and `13s > K` partition
`[4, m]`, so the Lean split covers the TeX's `4 ≤ s ≤ ⌈K/13⌉` / `K/13 < s ≤ m` (the TeX's groups may
overlap in one term, harmless for an upper bound; the Lean's do not overlap; the Lean proof adds
the non-negative geometric term to every `s`, which only loosens its own bound).

Encoding decisions of this unit with no manuscript consequence (T0, for the record):
cardinalities are real variables carrying exactly the manuscript's bounds; the charge series is
stated for every finite partial sum; `T_s` uses `Nat.choose` (`C(m,s) = 0` for `s > m`, as in the
TeX); `m ≤ M − 1` is ℕ-subtraction (harmless, `M ≥ 2^40`); `ℓ_* − 1` is ℕ-subtraction in the Step 4
exponent (harmless, `ℓ_* ≥ 2^10`); Step 0's second conclusion is non-strict (the TeX's `<` is used
as `≤`).

## Issues (none blocks approval)

- **I-1 (minor, integration; open since review 2).** None of `EG.Spec.Num.*`, `EG.Proof.Num.*`
  or `EGTest.ProbeNUM` is imported by `EG.lean`, `EGTest.lean` or `EGCheck.lean` (`grep Num`: no
  match), so CI's root build does not compile the unit and the non-vacuity file is not run by CI.
  `NUM.md` names only `EG.Proof.Num.WellDef` as missing; the gap is the whole unit. Integrator
  action: add the ten modules and the test to the root files; lock the five Spec files
  (`scripts/lock.py` reports them PENDING per `NUM.md`).
- **I-2 (cosmetic, docs).** `EG/Proof/Num/StarInputs.lean:10` still says "(`sorry` stubs)" in a
  historical sentence; it is the only `sorry` token in the unit and is inert. Could read "(stubs)".
- **I-3 (cosmetic, consumer note).** `NumCCCombineStatement` / `NumCCTwoPowStatement` hold for all
  `M ≥ 1` with `t = tCC M`; Lemma CC (ii) itself needs `t ≥ 1`, i.e. `M_l ≥ 2` (`tCC 1 = 0`). True in
  the manuscript (`M_l ≥ 2^40`); the s7 consumer must supply it. No change to the unit.
- **I-4 (cosmetic, docs).** The docstring of `NumL17sCaseBSmallPConstStatement` repeats the TeX's
  "tightest inequality of the lemma" (AUD-1) and `NumL17sStep5Statement`'s docstring calls
  `0.00243 ≥ 1/412` "the thinnest of the lemma"; by relative slack the thinnest L17\* facts are
  `0.1·2^19/192 ≥ 273` and `13/0.0121 < 1075` (review 2, I-2). Documentation only.
- **I-5 (cosmetic, TRIAGE).** TRIAGE §1c CAP-L25-CONST still says "The lock is still `sorry`
  (`EG.bmLemma25`)"; the lock is proved (`EG/Proof/Ext/BMLemma25.lean`, axiom scan 0 `sorryAx`).
  TRIAGE is integrator-owned; recorded because the unit's exclusion of Cap(i) relies on it.
- **I-6 (cosmetic, hazard NUM-H1 stays open).** `StarS2NumStatement` / `StarS3Statement` restate
  conjuncts of the s3 unit's future `StarFactsStatement` (`0.1 * ρ / ℓ` here vs `1/10 * ρ / ℓ` in
  the blueprint). When that Spec lands the integrator should diff the texts and have the s3 unit
  reuse `EG.starS2Num` / `EG.starS3`.

## Re-evaluated constants (double precision; agree with `NUM.md` and both reviews)

| Fact | Value | Bound | Slack |
|---|---|---|---|
| 0.09/4.2 vs 1/47 | 0.0214286 vs 0.0212766 | strict | 0.71% |
| 2^19/28200 | 18.59177 | 18.59 / 18 | 0.01% / 3.3% |
| 0.1·2^19/192 | 273.0667 | 273 | 0.02% |
| 13/0.0121 | 1074.380 | 1075 | 0.06% |
| 2^19/(94·1075) | 5.18840 | 5 | 3.8% |
| 1 − e^-1 | 0.632121 | 0.63 | 0.34% |
| 2^10 e^-11 | 0.0171025 | 0.02 | 14% |
| 1/412 | 0.00242718 | 0.00243 | 0.12% |
| 1/412 − 1/413 vs 2^-36 | 5.877e-6 vs 1.455e-11 | | huge |
| 7/2^39 vs 2^-36 (Step 0) | 1.273e-11 vs 1.455e-11 | | 12.5% |
| ln 2 vs (15/16)(1 − 2^-9) (Step 4, L = 1) | 0.69315 vs 0.93567 | | 26% |
| ln 1.125 vs 15/128 (Step 4, g = 1/8) | 0.117783 vs 0.117188 | | 0.5% |
| 8.34p + 2.34p² at p = 0.11 | 0.945714 | 1 | 5.4% |
| e^-6 vs 1/200 (Step 5, `2e^{-x/413} ≤ 0.01`) | 0.002479 vs 0.005 | | large (x/413 > 1.3·10^9) |
| c_OV = log₂(4/3); 17/41; 12/29 | 0.4150375; 0.4146341; 0.4137931 | | 0.10% (17/41) |
| 1 + 1/c_OV | 3.4094208 | 3.42 | 0.31% |
| 1.6(1 + 1/c_OV) (via 17/41; via 12/29) | 5.4550733 (5.4588235; 5.4666667) | 5.46 | 0.09% (0.02%; fails) |
| 3^41 vs 2^65 | ratio 0.988603 | | 1.2% |
| 1/(1 − 3.42/32), 1/(1 − 5.5/32), 1/(1 − 5.472/32) | 1.119664, 1.207547, 1.206273 | 1.12, 1.21 | 0.03%, 0.2% |
| 5.46·1.21 | 6.6066 | 6.61 | 0.05% |
| 1.5·128/127, 1.25·128/127 | 1.511811, 1.259843 | 1.52, 1.26 | 0.5%, 0.012% |
| (1 + 1/32)(2/3) | 0.6875 | 0.75 | 8% |
| 6e·2.74, 4e·2.74 | 44.68855, 29.79237 | 44.7, 29.8 | 0.026% (need e < 2.7189781; `exp_one_lt_d9` gives 2.7182818286) |
| 4e^7 | 4386.53 | 4400 | 0.31% |
| (5e³/16)(1/13 + 10^-4) | 0.483453 | 0.49 | 1.3% |
| e²/16; 1/(4e) | 0.461816; 0.09197 | 0.47; 1 | 1.7%; large |
| 2·0.47^{K/13} vs 0.1K^-4 at K = 10^4 (ln) | −580.09 vs −39.14 | | huge |
| 8800K^-5 vs 0.88K^-4 at K = 10^4 | equal | non-strict | 0 |
| 24·1.37 | 32.88 | 32.9 | 0.06% |
| K^5 Σ_{s=4}^m T_s (exact) | 0.035374 (10^4, 2500); 0.035331 (10003, 2500); 0.035265 (2·10^4, 5000); 0.035178 (10^5, 25000); 0.050166 (76, 18); 0.039170 (400, 99) | 8800 (+ tail); 10^4 | huge; TeX remark confirmed |
