module

public import EG.Defs.Constants
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The COL-JV table: column 3 (item (f) of Γ1) and column 4 (manuscript s3:tabCOLJV)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text (caption of Table s3:tabCOLJV): "Here `λ := λ_r` and `μ := log λ`, except in rows
2, 11 and 12, where `λ := λ_{l-2}` for a round `3 ≤ l ≤ R`. We write `M̄ := (Aμ)^{2A}`, with
`A = 105`, and `k̄ := 192λ^3 + (4/3)M̄^2`. Column 3 is a sufficient form of the requirement …
Column 4 gives, for row `i`, reals `a_i > 0` and `b_i, c_i ≥ 0` such that, for `μ ≥ 6`, the
inequality `a_iμ - b_i - c_i log(Aμ) ≥ 0` implies every inequality in column 3 of row `i`
(Lemma s3:lemCOLJVev …). The inequalities `a_iμ - b_i - c_i log(Aμ) ≥ 0` defined by column 4 are
cruder than column 3; they are not part of Γ1, are not asserted in Lemma COL-JV, and may fail at
some `μ ≥ log log D_*` although Γ1 holds."

Manuscript text ([s1:condG1] (f)): "for every row of the COL-JV table (Table s3:tabCOLJV), every
inequality in column 3 of that row holds at `λ`, where `M̄ := (Aμ)^{2A}` and
`k̄ := 192λ^3 + (4/3)M̄^2` as in the caption of that table. (Row 13 is G*, and the inequality of
row 12 is item (c). … column 3 consists of 18 explicit inequalities, two in row 1, five in row 8
and one in each other row, and they involve only `μ`, `λ = 2^μ`, `M̄` and `k̄`.)"

Column 3 of the table, verbatim (row: inequality):
 1: `λ^{102.5} > 257(λ+6μ+20)^{102}`; crude form `λ^{1/2} > 2^{111}`
 2: `λ^{103} ≥ M̄^{13}`
 3: `λ^{99} ≥ 640 k̄`
 4: `λ^{42.1} ≥ 2^{193}·12^5`
 5: `λ^{72} ≥ 3·2^{167}·k̄ M̄^{21}`
 6: `λ^{84} ≥ 2^{110} M̄^{15}`
 7: `λ^{64.4} ≥ 2^{127}·12^4`
 8: (a) `λ^{58} ≥ 2^{194}`; (b) `λ^{62} ≥ 2^{186}(μ+1)`; (c) `λ^{62} ≥ 2^{190}(μ+1)`;
    (d) `λ^{58} ≥ 2^{191}` and `λ^{99} ≥ 64((2λ)^6+1)`
 9: `k̄ ≤ λ^{3.3}`
10: `2k̄ ≤ λ^4`
11: `λ^{95} ≥ 2^{13} M̄^{12}`
12: `M̄ ≤ λ^{1.6}`
13: `λ^{36} ≥ 2^{240}(Aμ)^{46A}`
Column 4 (`(a_i,b_i,c_i)`): (0.5,112,0), (103,0,26A), (96,19,4A), (42.1,211,0), (69,178,46A),
(84,110,30A), (64.4,142,0), (58,194,1), (0.3,9,4A), (1,10,4A), (95,13,24A), (1.6,0,2A),
(36,240,46A).

Manuscript text ([s3:lemCOLJVev]): "Call an inequality in a real variable `μ` *of type (E)* if
it reads `aμ - b - c log(Aμ) ≥ 0` with reals `a > 0` and `b, c ≥ 0` (here `A = 105` and
`log = log₂`). (i) An inequality of type (E) holds for every `μ ≥ max{1, v_0^2}`, where
`v_0 := (c + (c^2 + a(b + c log A))^{1/2})/a`."

Formal counterparts (TRIAGE §2.4 "One table predicate"; blueprint s3b node `s3:tabCOLJV`),
namespace `EG.COLTable`:
* `lam μ = 2^μ`, `Mbar μ = (Aμ)^{2A}`, `kbar μ = 192λ^3 + (4/3)M̄^2` (`A = EG.Aexp = 105`);
* `row i μ` for `1 ≤ i ≤ 13`: the column-3 inequalities of row `i` (numbered as in the
  manuscript), and `col3 μ`: all rows `1 ≤ i ≤ 13`, i.e. item (f) of Γ1 at `μ`;
* `triple i`: column 4 of row `i`; `TypeE a b c μ`: the type-(E) inequality; `v0 a b c`.

Decisions.
* Rows are numbered `1 … 13` as in the manuscript (`row : ℕ → ℝ → Prop`); for `i = 0` and
  `i ≥ 14` there is no row, and `row i μ := True`, `triple i := (0,0,0)` (junk, and
  `TypeE 0 0 0 μ` is true as well). `col3 μ` quantifies over `1 ≤ i ≤ 13` only; the Lib lemma
  `EG.COLTable.col3_iff` spells it out as the conjunction of the 13 rows (18 inequalities).
* Decimal exponents are exact rationals and real powers of `λ = 2^μ > 0` (`Real.rpow`):
  `102.5 = 205/2`, `1/2`, `42.1 = 421/10`, `64.4 = 322/5`, `3.3 = 33/10`, `1.6 = 8/5`. Integer
  exponents are natural-number powers (`Monoid.npow`); for `λ > 0` the two agree
  (`Real.rpow_natCast`). `M̄` has the natural exponent `2A = 210`; row 13 has `46A = 4830`.
* Row 13 is written exactly as `EG.Gamma1e` (G*, [s1:condG1] (e)), so `row 13 μ ↔ Gamma1e μ`
  holds by `Iff.rfl` (Lib: `EG.COLTable.row13_iff_gamma1e`).
* Column 2 of the table (the requirements) is not defined here: it is asserted, in precise form,
  by the Spec of s3:lemCOLJV (blueprint s3b, hazard TAB-COL2-INFORMAL).
-/

@[expose] public section


namespace EG.COLTable

open Real

/-- [s3:tabCOLJV] (caption) "`λ = 2^μ`" (`Real.rpow`). -/
noncomputable def lam (μ : ℝ) : ℝ := (2 : ℝ) ^ μ

/-- [s3:tabCOLJV] (caption) "`M̄ := (Aμ)^{2A}`, with `A = 105`". -/
noncomputable def Mbar (μ : ℝ) : ℝ := ((Aexp : ℝ) * μ) ^ (2 * Aexp)

/-- [s3:tabCOLJV] (caption) "`k̄ := 192λ^3 + (4/3)M̄^2`". -/
noncomputable def kbar (μ : ℝ) : ℝ := 192 * lam μ ^ 3 + 4 / 3 * Mbar μ ^ 2

/-- [s3:tabCOLJV] column 3, "Sufficient inequality in `λ = 2^μ`", row `i` (`1 ≤ i ≤ 13`,
numbered as in the manuscript; `True` for other `i`, where there is no row). -/
noncomputable def row : ℕ → ℝ → Prop
  -- row 1: "`λ^{102.5} > 257(λ+6μ+20)^{102}`; crude form `λ^{1/2} > 2^{111}`"
  | 1, μ => 257 * (lam μ + 6 * μ + 20) ^ 102 < lam μ ^ (205 / 2 : ℝ) ∧
      (2 : ℝ) ^ 111 < lam μ ^ (1 / 2 : ℝ)
  -- row 2: "`λ^{103} ≥ M̄^{13}`"
  | 2, μ => Mbar μ ^ 13 ≤ lam μ ^ 103
  -- row 3: "`λ^{99} ≥ 640 k̄`"
  | 3, μ => 640 * kbar μ ≤ lam μ ^ 99
  -- row 4: "`λ^{42.1} ≥ 2^{193}·12^5`"
  | 4, μ => (2 : ℝ) ^ 193 * 12 ^ 5 ≤ lam μ ^ (421 / 10 : ℝ)
  -- row 5: "`λ^{72} ≥ 3·2^{167}·k̄ M̄^{21}`"
  | 5, μ => 3 * (2 : ℝ) ^ 167 * kbar μ * Mbar μ ^ 21 ≤ lam μ ^ 72
  -- row 6: "`λ^{84} ≥ 2^{110} M̄^{15}`"
  | 6, μ => (2 : ℝ) ^ 110 * Mbar μ ^ 15 ≤ lam μ ^ 84
  -- row 7: "`λ^{64.4} ≥ 2^{127}·12^4`"
  | 7, μ => (2 : ℝ) ^ 127 * 12 ^ 4 ≤ lam μ ^ (322 / 5 : ℝ)
  -- row 8: "(a) `λ^{58} ≥ 2^{194}`; (b) `λ^{62} ≥ 2^{186}(μ+1)`; (c) `λ^{62} ≥ 2^{190}(μ+1)`;
  -- (d) `λ^{58} ≥ 2^{191}` and `λ^{99} ≥ 64((2λ)^6+1)`"
  | 8, μ => (2 : ℝ) ^ 194 ≤ lam μ ^ 58 ∧ (2 : ℝ) ^ 186 * (μ + 1) ≤ lam μ ^ 62 ∧
      (2 : ℝ) ^ 190 * (μ + 1) ≤ lam μ ^ 62 ∧ (2 : ℝ) ^ 191 ≤ lam μ ^ 58 ∧
      64 * ((2 * lam μ) ^ 6 + 1) ≤ lam μ ^ 99
  -- row 9: "`k̄ ≤ λ^{3.3}`"
  | 9, μ => kbar μ ≤ lam μ ^ (33 / 10 : ℝ)
  -- row 10: "`2k̄ ≤ λ^4`"
  | 10, μ => 2 * kbar μ ≤ lam μ ^ 4
  -- row 11: "`λ^{95} ≥ 2^{13} M̄^{12}`"
  | 11, μ => (2 : ℝ) ^ 13 * Mbar μ ^ 12 ≤ lam μ ^ 95
  -- row 12: "`M̄ ≤ λ^{1.6}`"
  | 12, μ => Mbar μ ≤ lam μ ^ (8 / 5 : ℝ)
  -- row 13: "`λ^{36} ≥ 2^{240}(Aμ)^{46A}`" (G*; written exactly as `EG.Gamma1e`)
  | 13, μ => (2 : ℝ) ^ 240 * ((Aexp : ℝ) * μ) ^ (46 * Aexp) ≤ lam μ ^ 36
  | _, _ => True

/-- [s1:condG1] (f) "for every row of the COL-JV table (Table s3:tabCOLJV), every inequality in
column 3 of that row holds at `λ`" (with `λ = 2^μ`): the 18 column-3 inequalities of rows
`1 … 13` at `μ`. -/
def col3 (μ : ℝ) : Prop := ∀ i : ℕ, 1 ≤ i → i ≤ 13 → row i μ

/-- [s3:tabCOLJV] column 4, "`(a_i, b_i, c_i)`" of row `i` (`1 ≤ i ≤ 13`; `(0,0,0)` for other
`i`). Decimals are exact rationals: `0.5 = 1/2`, `42.1 = 421/10`, `64.4 = 322/5`,
`0.3 = 3/10`, `1.6 = 8/5`; `A = 105`. -/
noncomputable def triple : ℕ → ℝ × ℝ × ℝ
  | 1 => (1 / 2, 112, 0)
  | 2 => (103, 0, 26 * Aexp)
  | 3 => (96, 19, 4 * Aexp)
  | 4 => (421 / 10, 211, 0)
  | 5 => (69, 178, 46 * Aexp)
  | 6 => (84, 110, 30 * Aexp)
  | 7 => (322 / 5, 142, 0)
  | 8 => (58, 194, 1)
  | 9 => (3 / 10, 9, 4 * Aexp)
  | 10 => (1, 10, 4 * Aexp)
  | 11 => (95, 13, 24 * Aexp)
  | 12 => (8 / 5, 0, 2 * Aexp)
  | 13 => (36, 240, 46 * Aexp)
  | _ => (0, 0, 0)

/-- [s3:lemCOLJVev] "an inequality in a real variable `μ` *of type (E)* … reads
`aμ - b - c log(Aμ) ≥ 0`" (`A = 105`, `log = log₂`). The side conditions `a > 0`, `b, c ≥ 0`
are hypotheses of the statements that use it. -/
noncomputable def TypeE (a b c μ : ℝ) : Prop :=
  0 ≤ a * μ - b - c * logb 2 ((Aexp : ℝ) * μ)

/-- [s3:lemCOLJVev] (i) "`v_0 := (c + (c^2 + a(b + c log A))^{1/2})/a`". -/
noncomputable def v0 (a b c : ℝ) : ℝ :=
  (c + sqrt (c ^ 2 + a * (b + c * logb 2 (Aexp : ℝ)))) / a

end EG.COLTable
