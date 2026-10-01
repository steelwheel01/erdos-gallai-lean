module

public import EG.Defs.Lend.COLTable
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Statement of the eventual form of the COL-JV table, parts (i) and (ii)
(manuscript s3:lemCOLJVev)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3b (`formal/work/p2s/s3b.md`; blueprint
`formal/work/p2/blueprint_s3b.md`, node `s3:lemCOLJVev`). No proof here. Part (iii) is the
existing `EG.Spec.Col3EventuallyStatement` (`EG/Spec/Gamma/Sat.lean`, unit GAMMA, reused
unchanged; its proof `EG/Proof/Gamma/Sat.lean` does not go through (i), (ii)). The lemma as a
whole is `COLJVevStatement` below.

Manuscript v6.1, `s3.tex`, Lemma [s3:lemCOLJVev]:
"Call an inequality in a real variable `μ` *of type (E)* if it reads `aμ - b - c log(Aμ) ≥ 0`
with reals `a > 0` and `b, c ≥ 0` (here `A = 105` and `log = log₂`).
(i) An inequality of type (E) holds for every `μ ≥ max{1, v_0^2}`, where
`v_0 := (c + (c^2 + a(b + c log A))^{1/2})/a`. In particular, it holds for all sufficiently large
`μ`.
(ii) Let `μ ≥ 6` be real, and put `λ := 2^μ`, `M̄ := (Aμ)^{2A}` and `k̄ := 192λ^3 + (4/3)M̄^2`.
Let `1 ≤ i ≤ 13`, and let `(a_i,b_i,c_i)` be the triple in column 4 of row `i` of Table
s3:tabCOLJV. If `a_iμ - b_i - c_i log(Aμ) ≥ 0`, then every inequality in column 3 of row `i` holds
at `λ`.
(iii) Consequently, for each row of Table s3:tabCOLJV, every inequality in column 3 holds at
`λ = 2^μ` for all sufficiently large real `μ`.
The lemma concerns explicit functions of the real variable `μ` only. It involves no graph, no run
of the hierarchy and no condition on `D_*`."

Formal reading (the locked Defs `EG/Defs/Lend/COLTable.lean`).
* The type-(E) inequality `aμ - b - c log(Aμ) ≥ 0` is `EG.COLTable.TypeE a b c μ`
  (`A = EG.Aexp = 105`, `log = Real.logb 2`); `v_0` is `EG.COLTable.v0 a b c` (`Real.sqrt`). The
  side conditions `a > 0`, `b, c ≥ 0` are hypotheses of (i).
* "for all sufficiently large `μ`" is `∀ᶠ μ in Filter.atTop` (real `μ`).
* In (ii), `λ`, `M̄`, `k̄` are `COLTable.lam μ`, `COLTable.Mbar μ`, `COLTable.kbar μ`, which the
  table rows `COLTable.row i μ` use; "every inequality in column 3 of row `i` holds at `λ`" is
  `COLTable.row i μ`; the triple of row `i` is `COLTable.triple i`; the row index is bounded,
  `1 ≤ i ≤ 13` (CONVENTIONS: rows `0` and `≥ 14` are junk).
-/

@[expose] public section

namespace EG.Spec

open Filter

/-- [s3:lemCOLJVev] (i) "An inequality of type (E) holds for every `μ ≥ max{1, v_0^2}`, where
`v_0 := (c + (c^2 + a(b + c log A))^{1/2})/a`. In particular, it holds for all sufficiently large
`μ`" (reals `a > 0`, `b, c ≥ 0`). -/
def COLJVevTypeEStatement : Prop :=
  ∀ a b c : ℝ, 0 < a → 0 ≤ b → 0 ≤ c →
    (∀ μ : ℝ, max 1 (COLTable.v0 a b c ^ 2) ≤ μ → COLTable.TypeE a b c μ) ∧
      ∀ᶠ μ : ℝ in atTop, COLTable.TypeE a b c μ

/-- [s3:lemCOLJVev] (ii) "Let `μ ≥ 6` be real, and put `λ := 2^μ`, `M̄ := (Aμ)^{2A}` and
`k̄ := 192λ^3 + (4/3)M̄^2`. Let `1 ≤ i ≤ 13`, and let `(a_i,b_i,c_i)` be the triple in column 4 of
row `i` of Table s3:tabCOLJV. If `a_iμ - b_i - c_i log(Aμ) ≥ 0`, then every inequality in
column 3 of row `i` holds at `λ`." -/
def COLJVevRowsStatement : Prop :=
  ∀ μ : ℝ, 6 ≤ μ → ∀ i : ℕ, 1 ≤ i → i ≤ 13 →
    COLTable.TypeE (COLTable.triple i).1 (COLTable.triple i).2.1 (COLTable.triple i).2.2 μ →
      COLTable.row i μ

/-- [s3:lemCOLJVev] (iii) per row: "Consequently, for each row of Table s3:tabCOLJV, every
inequality in column 3 holds at `λ = 2^μ` for all sufficiently large real `μ`." (The all-rows
form is `EG.Spec.Col3EventuallyStatement`; the two are equivalent, there being 13 rows.) -/
def COLJVevEventuallyRowStatement : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ 13 → ∀ᶠ μ : ℝ in atTop, COLTable.row i μ

/-- [s3:lemCOLJVev] the whole lemma: (i), (ii) and (iii) (per row). -/
def COLJVevStatement : Prop :=
  COLJVevTypeEStatement ∧ COLJVevRowsStatement ∧ COLJVevEventuallyRowStatement

end EG.Spec
