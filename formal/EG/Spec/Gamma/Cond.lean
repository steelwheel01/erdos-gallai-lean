module

public import EG.Defs.Gamma.Full

/-!
# Statements: consequences of Γ1 recorded in Condition s1:condGamma

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:condGamma`). No proof here. The Lib lemmas of
`EG/Lib/Found/Gamma.lean` and `EG/Lib/Gamma/Full.lean` (`Gamma1core.two_pow_256_le_logb`,
`Gamma1core.items_loglog`, `Gamma1core.items_logb`, `Gamma1.mono`, `Gamma1core.gamma2a`) are the
intended proofs. The conditions themselves are the locked Defs `EG.Gamma1a` … `EG.Gamma1e`,
`EG.Gamma1Items`, `EG.Gamma1core`, `EG.Gamma1f`, `EG.Gamma1`, `EG.Gamma2a` (TRIAGE §2.4); the
eventuality statements (Remark (1)) are `EG/Spec/Gamma/Sat.lean` (s7:lemGammaSat), and Γ2(b),(c)
are consequences proved in s2:lemTower (b), s3:lemCOL and s5:lemE1 (their own Specs), never
conditions.

Manuscript v6.1, `s1.tex`, Condition [s1:condGamma], item Γ1 ([s1:condG1]):
"`D_* > 2`, so that `log₂log₂D_*` is defined and positive; and for every real
`μ ≥ log₂log₂D_*`, with `λ := 2^μ`, the following hold: (a) `μ ≥ 2^8`; (b) `2^μ ≥ 2^{14}Aμ^3`;
(c) …; (d) `2 log₂μ + 8 ≤ μ` (this follows from (a) and (b), and is listed separately for
direct citation); (e) …; (f) …
Each item consists of explicit inequalities in the single real variable `μ`, … Γ1 asks that all
of them hold on the whole ray `μ ≥ log₂log₂D_*`. So Γ1 is upward closed in `D_*`. (The
requirement `D_* > 2` only makes the ray well defined: whenever `log₂log₂D_*` is defined, (a) at
`μ = log₂log₂D_*` already gives `D_* ≥ 2^{2^{256}}`.)
Every round `r ≤ R` of the hierarchy has average degree `d_r ≥ D_*` …, so `λ_r := log₂d_r`
satisfies `log₂λ_r ≥ log₂log₂D_*`, and (a)–(f) hold at `μ = log₂λ_r`. They also hold at
`μ = log₂log₂d` for every `d ≥ D_*`, and at `μ = log₂D_*` (as `t ≥ log₂t` for `t > 0`). By (a)
at `μ = log₂log₂D_*`, `log₂D_* ≥ 2^{256}`."
Item Γ2 ([s1:condG2]): "Each of (a)–(c) is implied by Γ1: (a) is immediate from Γ1".

Formal reading.
* `log₂` is `Real.logb 2`; `2^{2^{256}}` is `(2:ℝ) ^ ((2:ℝ) ^ 256)` (`Real.rpow` outside).
* Where a claim needs only items (a)–(e), it is stated with `Gamma1core` (a weaker hypothesis
  than `Gamma1`, so a stronger statement); where it concerns (f) as well, with `Gamma1`.
* "(a)–(f) hold at `μ = log₂λ_r`" is the case `d = d_r` of "at `μ = log₂log₂d` for every
  `d ≥ D_*`", so it is not stated separately (the run data are s2 objects).
-/

@[expose] public section

namespace EG.Spec

open Real

/-- [s1:condGamma] Γ1 ([s1:condG1]) (d) "`2 log₂μ + 8 ≤ μ` (this follows from (a) and
(b) …)". -/
def Gamma1dOfABStatement : Prop :=
  ∀ μ : ℝ, Gamma1a μ → Gamma1b μ → Gamma1d μ

/-- [s1:condGamma] Γ1 ([s1:condG1]) "Γ1 asks that all of them hold on the whole ray
`μ ≥ log₂log₂D_*`. So Γ1 is upward closed in `D_*`." -/
def Gamma1UpwardStatement : Prop :=
  ∀ D D' : ℝ, Gamma1 D → D ≤ D' → Gamma1 D'

/-- [s1:condGamma] Γ1 ([s1:condG1]) "whenever `log₂log₂D_*` is defined, (a) at
`μ = log₂log₂D_*` already gives `D_* ≥ 2^{2^{256}}`" and "By (a) at `μ = log₂log₂D_*`,
`log₂D_* ≥ 2^{256}`" (from items (a)–(e) with `D_* > 2`). -/
def Gamma1LogbStatement : Prop :=
  ∀ D : ℝ, Gamma1core D → (2 : ℝ) ^ 256 ≤ logb 2 D ∧ (2 : ℝ) ^ ((2 : ℝ) ^ 256) ≤ D

/-- [s1:condGamma] Γ1 ([s1:condG1]) "(a)–(f) … also hold at `μ = log₂log₂d` for every
`d ≥ D_*`, and at `μ = log₂D_*` (as `t ≥ log₂t` for `t > 0`)." -/
def Gamma1TransferStatement : Prop :=
  ∀ D : ℝ, Gamma1 D →
    (∀ d : ℝ, D ≤ d →
      Gamma1Items (logb 2 (logb 2 d)) ∧ COLTable.col3 (logb 2 (logb 2 d))) ∧
    Gamma1Items (logb 2 D) ∧ COLTable.col3 (logb 2 D)

/-- [s1:condGamma] Γ2 ([s1:condG2]) "Each of (a)–(c) is implied by Γ1: (a) is immediate from
Γ1" (Γ2(a): `D_* ≥ 2^{117}`; from items (a)–(e) with `D_* > 2`). -/
def Gamma2aOfGamma1Statement : Prop :=
  ∀ D : ℝ, Gamma1core D → Gamma2a D

end EG.Spec
