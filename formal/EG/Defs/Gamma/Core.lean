module

public import EG.Defs.Constants
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The galactic conditions Γ1 (a)–(e) and Γ2 (a) (manuscript s1:condGamma)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text ([s1:condGamma], item Γ1, label `s1:condG1`):
"(*Tower condition.*) `D_* > 2`, so that `log₂log₂D_*` is defined and positive; and for every
real `μ ≥ log₂log₂D_*`, with `λ := 2^μ`, the following hold:
(a) `μ ≥ 2^8`;
(b) `2^μ ≥ 2^{14} A μ^3`;
(c) `2A log₂(Aμ) ≤ 1.6 μ`;
(d) `2 log₂μ + 8 ≤ μ` (this follows from (a) and (b), and is listed separately for direct
citation);
(e) (the condition G*) `λ^{36} ≥ 2^{240} (Aμ)^{46A}`;
(f) for every row of the COL-JV table (Table s3:tabCOLJV), every inequality in column 3 of that
row holds at `λ`, …
Each item consists of explicit inequalities in the single real variable `μ`, and each of them
holds for all sufficiently large `μ` (Lemma s7:lemGammaSat); Γ1 asks that all of them hold on
the whole ray `μ ≥ log₂log₂D_*`. So Γ1 is upward closed in `D_*`."

Manuscript text ([s1:condGamma], item Γ2 (a), label `s1:condG2`):
"(a) `D_* ≥ 2^{117}`; …" and "Each of (a)–(c) is implied by Γ1: (a) is immediate from Γ1".

Manuscript text ([s1:tabOrder], step 3): "`D_*`: Γ1, i.e. `D_* > 2` and (a)–(f) … | eventual in
`μ`, on the ray `μ ≥ log₂log₂D_*`; hence `D_*` | absolute constants only"; "Γ2(a):
`D_* ≥ 2^{117}` | `D_*` | absolute constants only".

Formal counterparts (TRIAGE §2.4, Defs order item 6):
* `EG.Gamma1a μ` … `EG.Gamma1e μ`: the items (a)–(e) at a real `μ` (with `λ = 2^μ`, `Real.rpow`,
  and `A = EG.Aexp`), and `EG.Gamma1Items μ`, their conjunction;
* `EG.Gamma1core D`: `2 < D` and `Gamma1Items μ` for every real `μ ≥ log₂ log₂ D`;
* `EG.Gamma2a D`: `2^{117} ≤ D`.

Layering. Item (f) points forward to the COL-JV table of s3; it is `EG.Gamma1f` in
`EG/Defs/Gamma/Full.lean` (TRIAGE §3 item 14), with `EG.Gamma1 := Gamma1core ∧ Gamma1f`.
Γ2 (b), (c) are consequences of Γ1 about runs and failure probabilities, proved as lemmas
(s2:lemTower(b), s3:lemCOL, s5:lemE1); they are not conditions (TRIAGE §2.4).
Γ3 and Γ4 are in the later Gamma files.

Eventualities. Γ1 is a condition on a whole ray of `μ`, so it is upward closed in `D`
(`EG.Gamma1core.mono`), and Γ2(a) is a lower bound (`EG.Gamma2a.mono`); Γ2(a) follows from Γ1
(`EG.Gamma1core.gamma2a`). That every sufficiently large `D` satisfies Γ1 is part of
s7:lemGammaSat and is not proved here. Never evaluate these inequalities numerically at `D_*`:
(a) at `μ = log₂log₂D_*` already forces `D_* ≥ 2^{2^{256}}`.

Encoding. `1.6` is the exact rational `16/10` (a real literal). In (b) the product `2^{14} A μ^3`
and in (e) the power `(Aμ)^{46A}` use the natural-number exponents `3` and `46·A = 4830`
(`Monoid.npow`); `2^μ` and hence `λ^{36}` use `Real.rpow` in `μ` (the exponent 36 of `λ` is a
natural number). `log₂` is `Real.logb 2`.
-/

@[expose] public section


namespace EG

open Real

/-- [s1:condG1] (a) "`μ ≥ 2^8`". -/
def Gamma1a (μ : ℝ) : Prop := (2 : ℝ) ^ 8 ≤ μ

/-- [s1:condG1] (b) "`2^μ ≥ 2^{14} A μ^3`" (`2^μ` is `Real.rpow`). -/
def Gamma1b (μ : ℝ) : Prop := (2 : ℝ) ^ 14 * (Aexp : ℝ) * μ ^ 3 ≤ (2 : ℝ) ^ μ

/-- [s1:condG1] (c) "`2A log₂(Aμ) ≤ 1.6 μ`". -/
def Gamma1c (μ : ℝ) : Prop := 2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * μ) ≤ 1.6 * μ

/-- [s1:condG1] (d) "`2 log₂μ + 8 ≤ μ`". -/
def Gamma1d (μ : ℝ) : Prop := 2 * logb 2 μ + 8 ≤ μ

/-- [s1:condG1] (e), [s1:condGstar] (the condition G*) "`λ^{36} ≥ 2^{240} (Aμ)^{46A}`" with
"`λ := 2^μ`" (`2^μ` is `Real.rpow`; the exponents `36` and `46A` are natural numbers). -/
def Gamma1e (μ : ℝ) : Prop :=
  (2 : ℝ) ^ 240 * ((Aexp : ℝ) * μ) ^ (46 * Aexp) ≤ ((2 : ℝ) ^ μ) ^ 36

/-- [s1:condG1] items (a)–(e) at a single real `μ` (item (f), the COL-JV column 3, is
`EG.Gamma1f`, in the s3 layer). -/
def Gamma1Items (μ : ℝ) : Prop :=
  Gamma1a μ ∧ Gamma1b μ ∧ Gamma1c μ ∧ Gamma1d μ ∧ Gamma1e μ

/-- [s1:condG1] Γ1 without item (f): "`D_* > 2` …; and for every real `μ ≥ log₂log₂D_*`,
with `λ := 2^μ`, the following hold: (a) … (e)". -/
def Gamma1core (D : ℝ) : Prop :=
  2 < D ∧ ∀ μ : ℝ, logb 2 (logb 2 D) ≤ μ → Gamma1Items μ

/-- [s1:condG2] (a) "`D_* ≥ 2^{117}`". -/
def Gamma2a (D : ℝ) : Prop := (2 : ℝ) ^ 117 ≤ D

end EG
