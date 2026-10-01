# Review round 2 of unit NUM (cheap numeric probes): Specs after fix round 1

Reviewer: clean-room statement reviewer, round 2 (2026-09-29; this text supersedes the earlier round-2 draft in
this file — every check below was re-run from scratch). Scope: `EG/Spec/Num/{L17s,StarInputs,WellDef,OV,CC}.lean`
(32 `def …Statement : Prop`), the proof files `EG/Proof/Num/*.lean` (inspected only for sorries, axioms, and that
each theorem's type is a Spec name), `EGTest/ProbeNUM.lean`, and `work/p2b/NUM.md`. Manuscript v6.1 passages
re-read in full: s3.tex 220–285 (eqStar, (S1)–(S6)) and 402–597 (Lemma 17\*), s7.tex 432–550 (WellDef (iii)),
757–847 (CC (iii)), 1124–1156 (UH\*-split (ii)), s2.tex 278–374 (Lemma OV), 376–408 and 470–497 (14^τ (b)),
839–918 (Prop OV), s1.tex 1103–1118 (Chernoff, cited) and 1161–1175 (Lemma BBD). No Lean file was edited. The
manuscript is a CANDIDATE proof (AI-reviewed only).

**Verdict: approve.** Every Spec is a faithful back-translation of the TeX sentence it quotes (or is at least as
strong as the use where a TeX chain is collapsed to its ends); none is vacuous; the unit has no declared inputs
(all 32 statements are proved, 0 `sorryAx`); lint 0 findings. No inequality of the manuscript failed. The items
below are cosmetic. The two known math findings (T1 wording) are confirmed with my own values; nothing new of
class T2/T3 was found.

## Checks run

| Check | Method | Result |
|---|---|---|
| Hygiene | `python3 -I scripts/lint.py` | 0 findings |
| Sorry / forbidden tokens | `grep` over the 11 files | one docstring mention of the word `sorry` in `EG/Proof/Num/StarInputs.lean:10` (history), no code token; no `set_option maxHeartbeats` |
| Axioms | `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Num.{StarInputs,L17s,OV,CC,WellDef}` | 79/153/29/744/63 constants inspected, 0 `sorryAx`, 0 meta-scan hits, 0 violations |
| Olean freshness | mtime `.olean` vs `.lean`, 10 modules | all fresh (no build started) |
| Spec ↔ proof | script: every `def (\w+Statement) : Prop` in `EG/Spec/Num/*` has exactly one `theorem … : EG.Spec.<Name> := by` in `EG/Proof/Num/*`, and no theorem has a Statement type absent from the Specs | 32/32, 0 extra; one public auxiliary lemma `inv_logb_four_thirds_le`, the rest private helpers |
| Git | `git ls-files`, `git status`, `git log` on the unit's files | all 10 Lean files tracked and clean (commit `41e8a4e`); nothing of this unit is uncommitted |
| Scratch Lean (`scratchpad/NumReview2b.lean`, not committed; rc=0, 0 errors) | parse and non-vacuity probes, listed below | all pass |
| Numerics | independent double-precision re-evaluation of every constant; exact log-gamma evaluation of `K^5 Σ_{s=4}^m T_s` | table at the end; all agree with NUM.md |

Scratch probes that passed: `Real.logb 2 M ^ 2 = (logb 2 M)^2` (rfl); `x⁻¹ ^ 2 = 1/x^2`; `(2:ℝ)^(-7:ℤ) = 1/128`,
`^(-36:ℤ) = 1/2^36`, `^(-9:ℤ) = 1/512`; `0.09 = 9/100`, `0.0121 = 121/10000`, `0.47 = 47/100`, `3.42·epsC = 3.42/32`;
the Bernstein exponent `0.09X²/(4ΔX+0.2ΔX) = (0.09/4.2)·(X/Δ)` (field_simp; ring), so the third conjunct of
`NumL17sBernsteinExponentStatement` is literally the TeX's `0.09/4.2 > 1/47`; Step 4's exponent `Star.ell n - 1`
is ℕ-subtraction under a Monoid power (rfl); `numSDRTerm` unfolds to `T_s` (rfl); `0.47^(K/13)` is `Real.rpow`
(rfl); `1 ≤ Star.Delta n ρ` and `1 ≤ Star.L n` under the domain hypotheses (no division-by-zero junk in
`NumL17sCaseBExponentStatement`); `0 < logb 2 M` for `M ≥ 2`; the `∀ x y` conjunct of Step 5 has a witness
(`x = 2^40`, `y = 0`); `Quot.tCC 1 = 0` (TwoPow at `M = 1` is `1 ≤ 1`, a true edge case); the hypotheses of
`NumCCCombineStatement` force `0 ≤ n`; `3^41 ≤ 2^65` in ℕ; `1.25·128/127 < 1.26` (thin, true).

## (1) Fidelity: back-translation against the TeX (v6.1)

Conventions checked: `log = log₂` (`Star.L n = logb 2 n`, `Quot.tCC M = ⌈2 logb 2 M⌉₊`, `c_OV = logb 2 (4/3)`);
`e^x = Real.exp`, `ln = Real.log`; `ε = epsC = 2^-5`; decimals exact; `Star.*` names qualified (no `open` of the
s3/s4 namespaces); every parameter statement carries the (eqStar) domain `n ≥ 2`, `2^-7 ≤ ε' ≤ 1`, `0 < ρ ≤ 1`
(abbreviated "dom" below). The locked Defs read (`Star.L, ell, g, p, d, lam, Delta, sigma, theta`, `epsC`,
`Quot.tCC`) are the manuscript's (eqStar)/ε/t^CC verbatim (re-read `EG/Defs/Link/Star.lean`).

### s3:lemL17s (`L17s.lean`, 14 statements) vs s3.tex 402–597

| Spec | Back-translation | TeX (quoted) | Verdict |
|---|---|---|---|
| `Step0` | dom, `u ≥ 1`, `θ_*u < n` ⇒ `2^39 < ρn` ∧ `7uL ≤ 2^-36ρn` | "θ_*u ≤ \|N_G(U)\| < n. Hence n > θ_* ≥ 2^19ℓ_*²L³/ρ², and so ρn ≥ ρ²n > 2^19ℓ_*²L³ ≥ 2^39 by (S1). Also 7uL < 7nL/θ_* ≤ 7ρ²n/(2^19ℓ_*²L²) ≤ 2^-36ρn" | faithful; hypothesis exactly the TeX's (`u := \|U\| ≥ 1`); second conclusion non-strict, which is how Step 5 uses it ("7uL ≤ 2^-36ρn"). The TeX step `θ_* ≥ 2^19ℓ_*²L³/ρ²` silently uses `ε' ≤ 1` (MF-2). Re-derived: `7ρ²n/(2^19ℓ²L²) ≤ 7ρn/2^39 ≤ 2^-36ρn` (ℓ ≥ 2^10, L ≥ 1, ρ ≤ 1). |
| `CaseAConst` | `273 ≤ 0.1·2^19/192` | "(0.1ρ/ℓ_*)·(2^19ℓ_*²L³u/(192ρ²L²)) ≥ 273ℓ_*uL" | faithful (273.067; the left side is `0.1·2^19ℓ_*Lu/(192ρ)`, so the TeX step uses `ρ ≤ 1`, MF-2) |
| `CaseASigma` (new) | `n ≥ 2`, `0 < ε'`, real `W`: `3W/σ_* = g_*W` | "≥ 3\|W\|/σ_* = g_*\|W\|" | faithful identity: `3ε'/(24L²) = ε'/(8L²)` |
| `CaseAExponent` | dom, `u ≥ 1`, `θ_*u ≤ W`, `W/σ_* ≤ C` ⇒ `273ℓ_*uL ≤ p_*C/8` ∧ `18uL ≤ 273ℓ_*uL` | "p_*\|Cen\|/8 ≥ p_*ε'\|W\|/(192L²) ≥ (0.1ρ/ℓ_*)·(…) ≥ 273ℓ_*uL ≥ 18uL" | faithful (chain collapsed to its ends; middle terms are `σ_*`'s definition and (S2)). `\|Cen\| ≥ \|W\|/σ_*` is Prop 13\*(a) and `\|W\| ≥ θ_*u` is (O3), both hypotheses here, as in the TeX. |
| `BernsteinMargin` | `1/47 < 0.09/4.2` | "0.09/4.2 > 1/47" | faithful, strict as in the TeX (0.0214286 vs 0.0212766) |
| `BernsteinExponent` | `X, Δ > 0`: `2(2ΔX + Δ(0.3X)/3) = 4ΔX + 0.2ΔX`, `(0.3X)² = 0.09X²`, `exp(−0.09X²/(4ΔX+0.2ΔX)) ≤ exp(−X/(47Δ))` | Lemma BBD (s1.tex:1161) second bound `exp(−a²/(2(β+ba/3)))` with `β = 2Δ_*\|X\|`, `b = Δ_*`, `a = 0.3\|X\|`; "Since 2(β+Δ_*a/3) = 4Δ_*\|X\|+0.2Δ_*\|X\| and 0.09/4.2 > 1/47, it gives … ≤ exp(−\|X\|/(47Δ_*))" | faithful; the identity and the exponent comparison verified symbolically (scratch). `X > 0`, `Δ > 0` are the TeX's "β > 0" paragraph. |
| `CaseBMean` | `0.63 ≤ 1 − e^-1`, `0.63 − 0.3 = 0.33` | "EZ ≥ (1−e^-1)\|X\| ≥ 0.63\|X\|", "EZ − 0.3\|X\| ≥ 0.33\|X\|" | faithful (0.63212) |
| `CaseBGrowth` | `n ≥ 2`, `2^-7 ≤ ε' ≤ 1`, `W ≥ 0`, `ε'W/(2L²) ≤ X` ⇒ `0.165ε'W/L² ≤ 0.33X` ∧ `g_*W ≤ 0.165ε'W/L²` | "Z ≥ 0.33\|X\| ≥ 0.165ε'\|W\|/L² ≥ g_*\|W\|" with `\|X\| ≥ ε'\|W\|/(2L²)` (Prop 13\*(b)) | faithful (`1/8 ≤ 0.165`) |
| `CaseBSmallPConst` | `94·300 = 28200`, `18.59 < 2^19/28200`, `18 ≤ 18.59` | "the exponent is at least 2^19uL/28200 ≥ 18uL (indeed 2^19/28200 > 18.59 …)" | faithful (18.59177) |
| `CaseBLargePConst` | `0.11² = 0.0121`, `13/0.0121 < 1075`, `5 ≤ 2^19/(94·1075)`, `∀ ℓ ≥ 2^10, 18 ≤ 5ℓ²` | "Δ_* ≤ 13p_*^-2 < 13/0.0121 < 1075, and the exponent is at least 2^19ℓ_*²uL/(94·1075) ≥ 5ℓ_*²uL ≥ 18uL" | faithful, strictness as in the TeX (1074.38; 5.1884) |
| `CaseBExponent` | dom, `u ≥ 1`, `θ_*u ≤ W`, `ε'W/(2L²) ≤ X` ⇒ `ε'θ_*u/(94Δ_*L²) ≤ X/(47Δ_*)` ∧ `ε'θ_*u/(94Δ_*L²) = 2^19ℓ_*²Lu/(94Δ_*ρ²)` ∧ `18uL ≤ 2^19ℓ_*²Lu/(94Δ_*ρ²)` | the display "\|X\|/(47Δ_*) ≥ ε'θ_*u/(94Δ_*L²) = 2^19ℓ_*²Lu/(94Δ_*ρ²)" and the two bullets, both ending in "≥ 18uL" | faithful; `Δ_* = Star.Delta n ρ` (the actual value, ≥ 1), the regime split `p_* ≤ 0.11` is inside the proof; the large-`p_*` bullet silently drops `ρ^-2 ≥ 1` (MF-2). Re-derived both regimes (see numerics). |
| `Step3` | `∀ x ≥ 1, x³e^{-11x} ≤ e^{-11}`; `2^10e^{-11} ≤ 0.02`; `n ≥ 2`, `u ≥ 1` ⇒ `(ℓ_*−1)e^{-18uL} ≤ 2^10L³e^{-11L}e^{-7uL}` ∧ `… ≤ 0.02e^{-7uL}` | "using u ≥ 1, (S1), and the fact that L³e^{-11L} ≤ e^{-11} for L ≥ 1, … ≤ (ℓ_*−1)e^{-18uL} ≤ 2^10L³e^{-11L}e^{-7uL} ≤ 0.02e^{-7uL}" | faithful (the union-bound step is probabilistic and is correctly not here); `x³e^{-11x}` is decreasing for `x > 3/11`; 0.017103 |
| `Step4` | `n ≥ 2`, `2^-7 ≤ ε' ≤ 1` ⇒ `g_* ≤ 1/8`, `15g_*/16 ≤ ln(1+g_*)`, `L − 2^-9 < (ℓ_*−1)g_*`, `L ln 2 ≤ (15/16)(L − 2^-9)`, `n ≤ (1+g_*)^{ℓ_*−1}` | "Since g_* ≤ 1/8, ln(1+g_*) ≥ g_*−g_*²/2 ≥ 15g_*/16. By (S1) and ε' ≥ 2^-7, (ℓ_*−1)g_* > (2^10L³−2)2^-10L^-2 ≥ L−2^-9. Hence ln((1+g_*)^{ℓ_*−1}) ≥ (15/16)(L−2^-9) ≥ L ln 2 = ln n" | faithful; the TeX's intermediate `g − g²/2` and `(2^10L³−2)2^-10L^-2` are not stated separately (endpoints are), harmless; `<` matches the TeX's `>` (strict because `ℓ_* > 2^10L³−1` and `g_* > 0`). `15g/16 ≤ ln(1+g)` on `[0,1/8]` is true but thin at `g = 1/8` (0.5%). |
| `Step5` | 11 conjuncts: `0.9·(2/3) = 0.6`, `(1−0.09)·0.6 = 0.546`, `0.09² = 0.0081`, `0.0081·0.6/2 = 0.00243`, `0.0081/3 = 0.0027`, `1/412 ≤ 0.00243`, `1/412 ≤ 0.0027`, `1.09/2 < 0.546`, `2^-36 ≤ 1/412 − 1/413`, `∀ x y, 2^39 < x → y ≤ 2^-36x → 2e^{-x/412} ≤ 2e^{-x/413}e^{-y} ∧ 2e^{-x/413}e^{-y} ≤ 0.01e^{-y}`, `0.02 + 0.01 ≤ 1` | Step 5 and Conclusion (quoted in the docstring); Chernoff forms are s1:citChernoffGen (a): lower tail `e^{-δ²μ/2}` for a mean bound `μ ≤ EX`, upper tail `e^{-δ²μ/3}` for `μ ≥ EX`, `δ = 0.09` | faithful; `0.546 > 0.545 = 1.09/2` is the TeX's "0.546ρn > 0.545ρn ≥ \|V\|/2"; the `∀ x y` conjunct is exactly "2e^{-ρn/412} ≤ 2e^{-ρn/413}e^{-7uL} ≤ 0.01e^{-7uL}. Here we used Step 0: 7uL ≤ 2^-36ρn ≤ ρn(1/412−1/413) and ρn > 2^39". |

### (S2), (S3) (`StarInputs.lean`, 3 statements) vs s3.tex 246–262

- `StarS2NumStatement`: `n ≥ 2`, `0 < ρ ≤ 1` ⇒ `0.1ρ/ℓ_* ≤ p_*` ∧ `p_*^-2 ≤ 100ℓ_*²ρ^-2`. Verbatim "(S2) … satisfies
  p_* ≥ 0.1ρ/ℓ_*, so p_*^-2 ≤ 100ℓ_*²ρ^-2". `Star.p` is the explicit solution and `p_spec`/`p_unique` (Lib) identify it
  with the manuscript's `p_*`.
- `StarS3Statement`: dom(n, ρ) ⇒ `Δ_* ≤ 2p^-2+8.34p^-1+2.34` ∧ (`p ≤ 0.11 → Δ_* ≤ 3p^-2`) ∧ `Δ_* ≤ 13p^-2`, `p = p_*`.
  Verbatim (S3); "for every p ∈ (0,1]" is supplied by `p_pos`/`p_le_one`. The TeX's own derivation gives
  `2p^-2 + (25/3)p^-1 + 7/3 ≤ 2p^-2 + 8.34p^-1 + 2.34` (8.333… ≤ 8.34, 2.333… ≤ 2.34), consistent.
- `NumStarS3MarginStatement` (new): `∀ p > 0`: (`p ≤ 0.11 → 2p^-2+8.34p^-1+2.34 ≤ 3p^-2`) ∧ (`p ≤ 1 → … ≤ 13p^-2`).
  This merges the TeX's "If p ≤ 0.11, then 8.34p^-1 ≤ 0.92p^-2 and 2.34 ≤ 0.03p^-2. If p ≤ 1, then
  8.34p^-1+2.34 ≤ 10.68p^-2": at `p = 0.11`, `8.34p + 2.34p² = 0.9174 + 0.0283 = 0.9457 ≤ 1`; at `p = 1`, `12.68 ≤ 13`.
  At least as strong as the TeX's two sub-steps.

### s7:lemWellDef (iii) (`WellDef.lean`, 1 def + 4 statements) vs s7.tex 480–550

- `numSDRTerm K m s = C(m,s)·C(K,s−1)·(C(s−1,3)/C(K,3))^s` (Nat.choose cast to ℝ): exactly `T_s`; ℕ-subtraction
  `s−1` is harmless on `Icc 4 m`; `C(m,s) = 0` for `s > m` as in the manuscript.
- `Series`: `∀ K m : ℕ, 10^4 ≤ K → (m:ℝ) ≤ K/4 → Σ_{s∈Icc 4 m} T_s ≤ 8800K^-5 + 2·0.47^{K/13} ∧ … ≤ K^-4`. This is the
  "Altogether" display under the hypotheses the proof uses ("m ≤ M_l−1 ≤ K/4", "(K ≥ 10^4)"). I re-derived the
  analytic chain independently: `T_s ≤ (eK/(4s))^s (eK/(s−1))^{s−1} ((s−1)/K)^{3s} = e^{2s−1}4^{-s}s^{-s}(s−1)^{2s+1}K^{-s-1}
  ≤ a_s := e^{-1}(s/K)(e²s/(4K))^s`; `a_4 = 4e^7K^-5`; `a_{s+1}/a_s = ((s+1)/s)^{s+1}·e²(s+1)/(4K) ≤ (5/4)·e·e²(s+1)/(4K)
  = 5e³(s+1)/(16K) < 0.49` for `s < K/13`, `K ≥ 10^4` (0.48345 at the boundary); so `a_s ≤ 2^{4−s}a_4` for all
  `4 ≤ s ≤ ⌈K/13⌉` (for `s ≤ ⌈K/13⌉−1 < K/13` the halving applies), first group ≤ `2a_4 < 8800K^-5`; tail
  `s > K/13`, `s ≤ K/4`: `a_s ≤ (1/(4e))(e²/16)^s ≤ 0.47^s`, sum ≤ `0.47^{⌊K/13⌋+1}/0.53 ≤ 0.47^{K/13}/0.53 ≤ 2·0.47^{K/13}`.
  The two groups cover `[4, m]` (possibly overlapping in one term, harmless for an upper bound). All correct.
- `Use`: `∀ M m : ℕ, 2^40 ≤ M → m ≤ M−1 → Σ_{s∈Icc 4 m} T_s(4M) ≤ (4M)^-4`. This is (iii) with "m ≤ M_l−1 ≤ K/4 with
  K := K^HUB_l = 4M_l" (s7.tex:467) and "M_l ≥ 2^40" (s7.tex:455); `4M ≥ 2^42 ≥ 10^4`.
- `Ratio` (new): `0.49 ≤ 1/2` — the "Hence a_s ≤ 2^{4−s}a_4" step. Correct.
- `Const`: the nine quoted constants (`4e^7 < 4400`; `(5e³/16)(1/13+1/K) < 0.49` for real `K ≥ 10^4`; `1/(4e) ≤ 1`;
  `e²/16 ≤ 0.47`; `1/0.53 ≤ 2`; `2·4400 = 8800`; `8800K^-5 ≤ 0.88K^-4` and `2·0.47^{K/13} ≤ 0.1K^-4` for `K ≥ 10^4`;
  `0.88+0.1 ≤ 1`; `M ≥ 2^40 ⇒ 4M ≥ 2^42 ∧ 4M ≥ 10^4`). All true; `8800K^-5 ≤ 0.88K^-4` is an equality at `K = 10^4`
  (non-strict in the TeX, correctly non-strict here); `2·0.47^{K/13} = e^{-580.1}` vs `0.1K^-4 = e^{-39.1}` at `K = 10^4`.

### s2 OV (`OV.lean`, 7 statements) vs s2.tex 278–374, 491–495, 868–918

- `ChargeSum`: `x, c > 0`, `∀ k`: `Σ_{j<k} 1/(x+jc)² ≤ 1/x² + 1/(cx)`. The TeX's "cε Σ_{j≥0} 1/(log M + jc_OV)² ≤
  cε(1/log²M + ∫_0^∞ dx/(log M + xc_OV)²) = cε(1/log²M + 1/(c_OV log M)), because the summand is decreasing in j",
  in partial-sum form (equivalent for non-negative terms; the charges come from finitely many ancestors). The factor
  `cε` and the instance `x = log M ≥ 1`, `c = c_OV` are the consumer's. True (integral comparison for `j ≥ 1`).
- `LogFourThirds`: `17/41 ≤ log₂(4/3)` ∧ `3^41 ≤ 2^65` (ℕ). Labelled as a helper, not a TeX sentence; true
  (3^41/2^65 = 0.9886). Exactly TRIAGE §1b OV-CONST-546.
- `Const`: `1 + 1/c_OV ≤ 3.42`; `∀ c > 0, M ≥ 2` (real): `cε(1/log²M + 1/(c_OV log M)) ≤ 3.42cε/log M`; `3.42ε < 1`;
  `1/(1−3.42ε) ≤ 1.12`. The second conjunct is OV(a)'s second inequality in its sharp `c_OV` form (TRIAGE: "Prove
  OV(a) in its sharp c_OV form"), without the factor `S ≥ 0` (the consumer multiplies through). The other three are
  "1+1/c_OV = 3.4095… ≤ 3.42" (misprint, MF-1), the lemma's hypothesis at `c = 1`, and "1/(1−3.42/32) = 1.1196… ≤ 1.12".
- `Rearrange` (new): `c > 0`, `3.42cε < 1`, `S ≤ n₀ + 3.42cεS ⇒ S ≤ n₀/(1−3.42cε)`: exactly "(c) … Rearranging".
- `Instance` (new): `(1+ε)(2/3) < 3/4` (0.6875): exactly "|ν_1| … < (1+ε)(2/3)m < (3/4)m".
- `Lem14tauConst`: the nine facts of the proof of 14^τ(b) (`1.5·128/127 < 1.52`, `1.25·128/127 < 1.26`, `1.52 ≤ 1.6`,
  `3.42·1.6ε = 0.171`, `0.171 < 1`, `3.42·1.6 = 5.472`, `1/(1−5.472ε) ≤ 1/(1−5.5ε)`, `1/(1−5.5ε) ≤ 1.21`,
  `1.6(1+1/c_OV) ≤ 5.46`); all quoted, all true (`0.171` is exact; 5.45507 ≤ 5.46).
- `PropOVConst`: `5.46·1.21 ≤ 6.61`, `6.61 ≤ 7.6`, `1.21 ≤ 1.37`, `2·7.6 = 15.2`, `4·7.6 = 30.4`, `2·6.61 ≤ 13.3`,
  `13.3 ≤ 16`; each appears in Prop OV's proof / (K1)–(K3) (s2.tex:877, 882, 894, 901, 910–911). All true.
- "s5 OV" of the task: s5 uses Prop OV only through (K1)/Lemma Tower and has no OV constant of its own (checked by
  NUM.md; not re-derived here beyond confirming Prop OV's constants above).

### s7 CC / UH\*-split (`CC.lean`, 4 statements) vs s7.tex 757–847, 1124–1156

- `Const`: `2·1.37 = 2.74`, `6e·2.74 < 44.7`, `4e·2.74 < 29.8`. Verbatim. Both inequalities are the same fact
  `e·2.74 < 7.45` (44.7 = 6·7.45, 29.8 = 4·7.45), i.e. `e < 2.7189781`; true (e = 2.7182818, 0.026%); TRIAGE's
  "needs e < 2.7188" is a sufficient condition, not the threshold.
- `TwoPow`: `∀ M ≥ 1 (ℕ)`: `2^{-tCC M} ≤ M^-2`, `tCC M = ⌈2log₂M⌉₊`. Verbatim "With t = t^CC_l we have 2^-t ≤ M_l^-2";
  stated for all `M ≥ 1` (manuscript `M_l ≥ 2^40`), stronger; `⌈2log₂M⌉ ≥ 2log₂M` gives it. Edge `M = 1`: `1 ≤ 1`.
- `Combine`: `M ≥ 1`, `H > 0`, `P ≥ 0`, `0 ≤ S ≤ 2.74nM` ⇒ `3MtP + (6e/H + 4e·2^-t)S ≤ 3M(t+1)P + 44.7nM/H + 29.8n/M`
  with `t = tCC M`. Exactly the last four sentences of (iii)'s proof including "Finally t ≤ t+1". The premise
  `Σ|S_w| ≤ 2·1.37nM_l` is a hypothesis, so the s7 counting fact ("every PAR object lies in at most two of the sets
  S_w") is not hidden here. `n ≥ 0` follows from the hypotheses (scratch).
- `UHsplitConst`: `24·1.37 = 32.88`, `32.88 < 32.9`, `44.7+32.9 ≤ 78`, `29.8 ≤ 30`. Verbatim (s7.tex:1141, 1154).

Every docstring starts with the manuscript label and quotes the TeX. No new Defs item; `numSDRTerm` is a Spec
abbreviation, faithful.

## (2) Vacuity

- Closed numeric statements are the manuscript's facts themselves (no hypotheses).
- Parameter statements: `EGTest/ProbeNUM.lean` exhibits satisfying instances (`n = 2`, `ε' = ρ = u = 1` for cases
  (a)/(b), Steps 3–4; `n = 2^128` for Step 0, with `Star.theta (2^128) 1 1 = 2^102 < 2^128`; both regimes of `p_*`
  occur, `p_*(2,1) = 1 > 0.11`); conclusions are non-trivial (`18uL > 0`, `Δ_* ≥ 1`, `L ≥ 1`, `ℓ_* ≥ 2^10`, scratch);
  no hypothesis contradicts another (the domain is the manuscript's).
- WellDef: sums non-empty with `T_4 > 0` at `K = 10^4`, `m = 2500` (ProbeNUM); the use form is satisfiable at
  `M = 2^40`, `m = M−1`. The bound is not trivially loose in the wrong direction: exact `K^5 Σ T_s = 0.03537` at
  `K = 10^4`, `m = 2500`, i.e. the true sum is far below both `8800K^-5` and `K^-4`, so the statement is true with the
  manuscript's constants and not by accident of an empty sum.
- OV/CC: hypotheses satisfiable (ProbeNUM; scratch: `logb 2 M > 0` for `M ≥ 2`, Step-5 `∀ x y` witness, CC Combine
  witness); the negative control `12/29` (too weak for 5.46) is recorded in ProbeNUM.

## (3) Declared inputs

None. The stage-1 inputs ((S2) numeric part, (S3)) are proved from the locked Defs and the Lib API (`starS2Num`,
`starS3`, 0 `sorryAx`). Nothing the probe should prove is hidden among hypotheses: every non-numeric premise
(`|Cen| ≥ |W|/σ_*`, `|X| ≥ ε'|W|/(2L²)`, `|W| ≥ θ_*u`, `Σ|S_w| ≤ 2.74nM_l`, `m ≤ K/4`, `m ≤ M_l−1`) is a hypothesis of
the statement that uses it and is supplied by the TeX at that point. Every target of TRIAGE §4 row "Cheap numeric
probes" and §1b OV-CONST-546 is a proved statement: `0.09/4.2` vs `1/47` (`numL17sBernsteinMargin`), `2^19/28200 ≥ 18`
(`numL17sCaseBSmallPConst`), WellDef series (`numWellDefSDRSeries`, `numWellDefSDRUse`), OV 17/41 and the sharp
form (`numOVLogFourThirds`, `numOVConst`, `numLem14tauConst`), the OV charge sum (`numOVChargeSum`), CC 44.7/29.8
(`numCCConst`, `numCCCombine`). Cap(i) is correctly excluded (TRIAGE assigns it to `EG.bmLemma25`).

## (4) Hygiene

Lint 0 findings; module headers as required (`@[expose] public section` in Spec, `public section` in Proof); no
`maxHeartbeats`; no Defs, root or integrator-owned file touched by this unit (git). All 10 Lean files are committed
and clean.

## Issues (all cosmetic; none blocks approval)

- **I-1 (cosmetic, integration).** None of the ten modules `EG.Spec.Num.*` / `EG.Proof.Num.*`, nor
  `EGTest.ProbeNUM`, is imported by `EG.lean` / `EGTest.lean` / `EGCheck.lean` (grep: no match), so CI does not build
  them; NUM.md mentions only `EG.Proof.Num.WellDef` as missing. Integrator action (root files are not the author's to
  edit): add the ten modules and the test to the root import files, and lock the five Spec files.
- **I-2 (cosmetic, docs).** Two docstrings each call a different inequality "the thinnest/tightest of the lemma":
  `NumL17sCaseBSmallPConstStatement` repeats the TeX's "this is the tightest inequality of the lemma"
  (`2^19/28200 > 18`, 3.3%), and `NumL17sStep5Statement` says `0.00243 ≥ 1/412` is "the thinnest of the lemma"
  (0.12%). By relative slack the thinnest L17\* facts are `0.1·2^19/192 ≥ 273` (0.02%) and `13/0.0121 < 1075`
  (0.06%). Suggest "tightest of the three routes to 18uL" for the first and dropping the superlative in the second.
- **I-3 (cosmetic, hazard NUM-H1 stays open).** `StarInputs.lean` says its (S2)/(S3) texts are "identical to the S3
  conjunct of the blueprint's `StarFactsStatement`", a Spec that does not exist yet. When the s3 unit writes it, the
  integrator should diff the two texts (`0.1 * ρ / ℓ` vs `1/10 * ρ / ℓ`) and have the s3 unit reuse `EG.starS2Num`
  / `EG.starS3` rather than restate them.

## Math findings (manuscript; PLAN §7 classes)

- **MF-1 (T1, wording; confirms NUM-F1).** s2.tex:349 "1+1/c_OV = 3.4095… ≤ 3.42": the value is `3.4094208…`, so the
  truncation should read "3.4094…". The inequality is true and proved (`numOVConst`).
- **MF-2 (T1, wording; confirms the author's and round-1's finding, three instances).** The L17\* proof uses
  `ε' ≤ 1` or `ρ ≤ 1` silently at: Step 0 "n > θ_* ≥ 2^19ℓ_*²L³/ρ²" (`ε' ≤ 1`); case (a) "(0.1ρ/ℓ_*)·(2^19ℓ_*²L³u/
  (192ρ²L²)) ≥ 273ℓ_*uL" (the left side is `0.1·2^19ℓ_*Lu/(192ρ)`, so `ρ ≤ 1`); case (b), `p_* > 0.11`, "the exponent is
  at least 2^19ℓ_*²uL/(94·1075)" (drops `ρ^-2 ≥ 1`). All true under the lemma's hypotheses and proved with them.
  Suggested wording: "(using ε' ≤ 1)", "(using ρ ≤ 1)".
- No inequality failed; no statement is suspect. The thinnest true margins are recorded below; none is within
  floating-point doubt (the thinnest, `6e·2.74 < 44.7`, has absolute slack 0.0114 and is proved from
  `Real.exp_one_lt_d9`).

## Re-evaluated constants (double precision; agree with NUM.md)

| Fact | Value | Bound | Slack |
|---|---|---|---|
| 0.09/4.2 vs 1/47 | 0.0214286 vs 0.0212766 | strict | 0.71% |
| 2^19/28200 | 18.59177 | 18.59 / 18 | 0.01% / 3.3% |
| 0.1·2^19/192 | 273.0667 | 273 | 0.02% |
| 13/0.0121 | 1074.380 | 1075 | 0.06% |
| 2^19/(94·1075) | 5.18840 | 5 | 3.8% |
| 1 − e^-1 | 0.632121 | 0.63 | 0.34% |
| 2^10e^-11 | 0.0171025 | 0.02 | 14% |
| 1/412 | 0.00242718 | 0.00243 | 0.12% |
| 1/412 − 1/413 | 5.877e-6 | 2^-36 = 1.455e-11 | huge |
| ln(1.125) vs 15/128 | 0.117783 vs 0.117188 | | 0.5% |
| (15/16)(1−2^-9) vs ln 2 (L = 1) | 0.93567 vs 0.69315 | | 35% |
| 8.34p + 2.34p² at p = 0.11 | 0.94571 | 1 | 5.4% |
| c_OV = log₂(4/3); 17/41 | 0.4150375; 0.4146341 | | 0.10% |
| 1 + 1/c_OV | 3.4094208 | 3.42 | 0.31% |
| 1.6(1 + 1/c_OV) (via 17/41) | 5.4550733 (5.4588235) | 5.46 | 0.09% (0.02%) |
| 3^41 vs 2^65 | 3.6473e19 vs 3.6893e19 | | 1.2% |
| 1/(1−3.42/32), 1/(1−5.5/32) | 1.119664, 1.207547 | 1.12, 1.21 | 0.03%, 0.2% |
| 5.46·1.21 | 6.6066 | 6.61 | 0.05% |
| 1.5·128/127, 1.25·128/127 | 1.511811, 1.259843 | 1.52, 1.26 | 0.5%, 0.012% |
| (1+ε)(2/3) | 0.6875 | 0.75 | 9% |
| 6e·2.74, 4e·2.74 | 44.68855, 29.79237 | 44.7, 29.8 | 0.026% (e < 2.7189781) |
| 4e^7 | 4386.53 | 4400 | 0.31% |
| (5e³/16)(1/13 + 10^-4) | 0.483453 | 0.49 | 1.3% |
| e²/16; 1/(4e) | 0.461816; 0.09197 | 0.47; 1 | 1.7%; large |
| 8800K^-5 vs 0.88K^-4 at K = 10^4 | equal | non-strict | 0 |
| 2·0.47^{K/13} vs 0.1K^-4 at K = 10^4 | e^-580.1 vs e^-39.1 | | huge |
| K^5 Σ_{s=4}^m T_s (exact, log-gamma) | 0.035374 (K=10^4, m=2500); 0.035265 (2·10^4, 5000); 0.050166 (76, 18); 0.039170 (400, 99) | 8800 (+ tail) | huge; the TeX remark "about 0.0502 near M_l = 19, tends to 9/256 = 0.0352" is confirmed |
