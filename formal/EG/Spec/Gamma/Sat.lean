module

public import EG.Defs.Main.GammaCond
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Statements: the galactic conditions are satisfiable (manuscript s3:lemCOLJVev (iii), s7:lemGammaSat)

PROTECTED FILE (`EG/Spec/**`): statement file, unit GAMMA. Proofs: `EG/Proof/Gamma/Sat.lean`
(with `EG/Lib/Gamma/Col3.lean` and `EG/Lib/Gamma/Eps.lean`).
Design note: `formal/work/p2b/GAMMA.md`. The blueprint (s7b, node `s7:lemGammaSat`) proposed
`EG/Spec/Main/GammaSat.lean` with the table predicate `EG.S3.COLJVcol3`; TRIAGE §2.4 replaced that
name by `EG.COLTable.col3`, and the file lives in the Gamma area of this unit.

Manuscript v6.1, `s3.tex`, Lemma [s3:lemCOLJVev] (iii): "Consequently, for each row of
Table s3:tabCOLJV, every inequality in column 3 holds at `λ = 2^μ` for all sufficiently large
real `μ`." (The lemma "concerns explicit functions of the real variable `μ` only. It involves no
graph, no run of the hierarchy and no condition on `D_*`.")

Manuscript v6.1, `s7.tex`, Lemma [s7:lemGammaSat] ("The galactic conditions are satisfiable"):
"Let `N_0` be as in Definition s1:defConstants(ii). Then:
(i) each item (a)–(f) of Γ1 (Condition s1:condG1) holds for all sufficiently large real `μ`;
hence there is `μ_1 ≥ 1` such that all of them hold for every `μ ≥ μ_1`, and Γ1 holds for every
`D_* > 2` with `log₂log₂D_* ≥ μ_1`;
(ii) `ε_1(D_*) → 0` and `ε_2(D_*) → 0` as `D_* → ∞`;
(iii) there is `D_0` such that every `D_* ≥ D_0` satisfies Γ1–Γ4 simultaneously.
In particular a constant `D_*` as in Definition s1:defConstants(iii) exists. Only this existence
is used: neither `μ_1` nor `D_0` is computed."

Encoding.
* "for all sufficiently large real `μ`" is `∀ᶠ μ in atTop` on `ℝ`; "there is `D_0` such that
  every `D_* ≥ D_0` …" is `∀ᶠ D in atTop` on `ℝ` (`Filter.eventually_atTop`).
* Items (a)–(e) are `EG.Gamma1Items μ`, item (f) is `EG.COLTable.col3 μ` (rows `1 … 13`, 18
  inequalities); Γ1 is `EG.Gamma1 D`, Γ1–Γ4 is `EG.GammaCond N0 D` (Γ2(b),(c) are consequences
  of Γ1, not conditions: `EG/Defs/Main/GammaCond.lean`).
* (iii) is stated for every real `N_0`, without the hypothesis `N0Cond N0`: this is a
  strengthening (the manuscript's proof of (iii) uses only that `N_0` is fixed before `D_*`, in
  "Γ3 holds for every `D_* ≥ 2^{(2N_0)^{1/C'}}`"), as in the blueprint ("in Lean: any real
  `N0`"). Nothing is weakened.
* "a constant `D_*` as in Definition s1:defConstants(iii) exists", together with the `N_0` of
  s1:defConstants (ii) that Γ3 refers to, is `GammaCondExistsStatement`: the non-vacuity of the
  standing hypotheses `N0Cond N0 ∧ GammaCond N0 D` of the main theorem.
-/

@[expose] public section

namespace EG.Spec

open Filter Topology

/-- [s3:lemCOLJVev] (iii) "Consequently, for each row of Table s3:tabCOLJV, every inequality in
column 3 holds at `λ = 2^μ` for all sufficiently large real `μ`." (All rows at once: a finite
conjunction of eventualities is an eventuality.) -/
def Col3EventuallyStatement : Prop :=
  ∀ᶠ μ : ℝ in atTop, COLTable.col3 μ

/-- [s7:lemGammaSat] (i) "each item (a)–(f) of Γ1 (Condition s1:condG1) holds for all
sufficiently large real `μ`; hence there is `μ_1 ≥ 1` such that all of them hold for every
`μ ≥ μ_1`, and Γ1 holds for every `D_* > 2` with `log₂log₂D_* ≥ μ_1`". -/
def GammaSatItemsStatement : Prop :=
  (∀ᶠ μ : ℝ in atTop, Gamma1Items μ ∧ COLTable.col3 μ) ∧
    ∃ μ₁ : ℝ, 1 ≤ μ₁ ∧ (∀ μ : ℝ, μ₁ ≤ μ → Gamma1Items μ ∧ COLTable.col3 μ) ∧
      ∀ D : ℝ, 2 < D → μ₁ ≤ Real.logb 2 (Real.logb 2 D) → Gamma1 D

/-- [s7:lemGammaSat] (ii) "`ε_1(D_*) → 0` and `ε_2(D_*) → 0` as `D_* → ∞`" (`ε_1 = EG.Quot.eps1`
of s7:propCost, `ε_2 = EG.Quot.eps2` of s7:lemUHsplit). -/
def GammaSatEpsStatement : Prop :=
  Tendsto Quot.eps1 atTop (𝓝 0) ∧ Tendsto Quot.eps2 atTop (𝓝 0)

/-- [s7:lemGammaSat] (iii) "there is `D_0` such that every `D_* ≥ D_0` satisfies Γ1–Γ4
simultaneously" (for every real `N_0`, which Γ3 refers to; the manuscript's "Let `N_0` be as in
Definition s1:defConstants(ii)" is not needed, see the module docstring). -/
def GammaSatStatement : Prop :=
  ∀ N0 : ℝ, ∀ᶠ D : ℝ in atTop, GammaCond N0 D

/-- [s7:lemGammaSat] "In particular a constant `D_*` as in Definition s1:defConstants(iii)
exists", with [s1:defConstants] (ii) "So such an `N_0` exists": there are `N_0` and `D_*` with
`N_0` as in s1:defConstants (ii) and `D_*` satisfying Γ1–Γ4 (s1:defConstants (iii)). -/
def GammaCondExistsStatement : Prop :=
  ∃ N0 D : ℝ, N0Cond N0 ∧ GammaCond N0 D

end EG.Spec
