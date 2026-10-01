module

public import EG.Defs.Lend.COLTable
public import EG.Defs.Gamma.Core

/-!
# API for the COL-JV table (manuscript s3:tabCOLJV)

* the rows, one by one, as explicit inequalities: `row1_iff` … `row13_iff` (all `Iff.rfl`),
  `row_of_lt_one`, `row_of_gt`;
* `col3`: `col3_iff` (the conjunction of the 13 rows), `col3.row`;
* the links to Γ1 stated in [s1:condG1] (f), "Row 13 is G*, and the inequality of row 12 is
  item (c)": `row13_iff_gamma1e` (`Iff.rfl`), `row12_iff_gamma1c` (for `μ > 0`);
* `lam_pos`, `lam_eq`, `Mbar_nonneg'` (every `μ`), `Mbar_nonneg`, `kbar_pos`;
* column 4: `triple_spec` ("reals `a_i > 0` and `b_i, c_i ≥ 0`").
-/

public section


namespace EG.COLTable

open Real

theorem lam_eq (μ : ℝ) : lam μ = (2 : ℝ) ^ μ := rfl

theorem lam_pos (μ : ℝ) : 0 < lam μ := Real.rpow_pos_of_pos (by norm_num) μ

theorem Mbar_eq (μ : ℝ) : Mbar μ = ((Aexp : ℝ) * μ) ^ (2 * Aexp) := rfl

/-- `M̄(μ) = (Aμ)^{2A} ≥ 0` for every real `μ` (the exponent `2A` is even). -/
theorem Mbar_nonneg' (μ : ℝ) : 0 ≤ Mbar μ :=
  (even_two_mul Aexp).pow_nonneg _

/-- The form with a (redundant) hypothesis `0 ≤ μ`; kept for existing callers. Prefer
`Mbar_nonneg'`. -/
theorem Mbar_nonneg {μ : ℝ} (_hμ : 0 ≤ μ) : 0 ≤ Mbar μ := Mbar_nonneg' μ

theorem kbar_eq (μ : ℝ) : kbar μ = 192 * lam μ ^ 3 + 4 / 3 * Mbar μ ^ 2 := rfl

theorem kbar_pos (μ : ℝ) : 0 < kbar μ := by
  have := lam_pos μ; unfold kbar; positivity

/-! ## The rows -/

theorem row1_iff (μ : ℝ) : row 1 μ ↔ 257 * (lam μ + 6 * μ + 20) ^ 102 < lam μ ^ (205 / 2 : ℝ) ∧
    (2 : ℝ) ^ 111 < lam μ ^ (1 / 2 : ℝ) := Iff.rfl
theorem row2_iff (μ : ℝ) : row 2 μ ↔ Mbar μ ^ 13 ≤ lam μ ^ 103 := Iff.rfl
theorem row3_iff (μ : ℝ) : row 3 μ ↔ 640 * kbar μ ≤ lam μ ^ 99 := Iff.rfl
theorem row4_iff (μ : ℝ) : row 4 μ ↔ (2 : ℝ) ^ 193 * 12 ^ 5 ≤ lam μ ^ (421 / 10 : ℝ) := Iff.rfl
theorem row5_iff (μ : ℝ) :
    row 5 μ ↔ 3 * (2 : ℝ) ^ 167 * kbar μ * Mbar μ ^ 21 ≤ lam μ ^ 72 := Iff.rfl
theorem row6_iff (μ : ℝ) : row 6 μ ↔ (2 : ℝ) ^ 110 * Mbar μ ^ 15 ≤ lam μ ^ 84 := Iff.rfl
theorem row7_iff (μ : ℝ) : row 7 μ ↔ (2 : ℝ) ^ 127 * 12 ^ 4 ≤ lam μ ^ (322 / 5 : ℝ) := Iff.rfl
theorem row8_iff (μ : ℝ) : row 8 μ ↔ (2 : ℝ) ^ 194 ≤ lam μ ^ 58 ∧
    (2 : ℝ) ^ 186 * (μ + 1) ≤ lam μ ^ 62 ∧ (2 : ℝ) ^ 190 * (μ + 1) ≤ lam μ ^ 62 ∧
    (2 : ℝ) ^ 191 ≤ lam μ ^ 58 ∧ 64 * ((2 * lam μ) ^ 6 + 1) ≤ lam μ ^ 99 := Iff.rfl
theorem row9_iff (μ : ℝ) : row 9 μ ↔ kbar μ ≤ lam μ ^ (33 / 10 : ℝ) := Iff.rfl
theorem row10_iff (μ : ℝ) : row 10 μ ↔ 2 * kbar μ ≤ lam μ ^ 4 := Iff.rfl
theorem row11_iff (μ : ℝ) : row 11 μ ↔ (2 : ℝ) ^ 13 * Mbar μ ^ 12 ≤ lam μ ^ 95 := Iff.rfl
theorem row12_iff (μ : ℝ) : row 12 μ ↔ Mbar μ ≤ lam μ ^ (8 / 5 : ℝ) := Iff.rfl
theorem row13_iff (μ : ℝ) :
    row 13 μ ↔ (2 : ℝ) ^ 240 * ((Aexp : ℝ) * μ) ^ (46 * Aexp) ≤ lam μ ^ 36 := Iff.rfl

/-- There is no row `0`. -/
theorem row_zero (μ : ℝ) : row 0 μ := trivial

/-- There are no rows after row `13`. -/
theorem row_of_gt {i : ℕ} (hi : 13 < i) (μ : ℝ) : row i μ := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 14 := ⟨i - 14, by omega⟩
  trivial

/-! ## Column 3 = item (f) of Γ1 -/

theorem col3.row {μ : ℝ} (h : col3 μ) {i : ℕ} (h1 : 1 ≤ i) (h13 : i ≤ 13) : row i μ :=
  h i h1 h13

/-- `col3 μ` is the conjunction of the 13 rows (18 inequalities). -/
theorem col3_iff (μ : ℝ) : col3 μ ↔
    row 1 μ ∧ row 2 μ ∧ row 3 μ ∧ row 4 μ ∧ row 5 μ ∧ row 6 μ ∧ row 7 μ ∧ row 8 μ ∧
      row 9 μ ∧ row 10 μ ∧ row 11 μ ∧ row 12 μ ∧ row 13 μ := by
  constructor
  · intro h
    exact ⟨h 1 (by norm_num) (by norm_num), h 2 (by norm_num) (by norm_num),
      h 3 (by norm_num) (by norm_num), h 4 (by norm_num) (by norm_num),
      h 5 (by norm_num) (by norm_num), h 6 (by norm_num) (by norm_num),
      h 7 (by norm_num) (by norm_num), h 8 (by norm_num) (by norm_num),
      h 9 (by norm_num) (by norm_num), h 10 (by norm_num) (by norm_num),
      h 11 (by norm_num) (by norm_num), h 12 (by norm_num) (by norm_num),
      h 13 (by norm_num) (by norm_num)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ i hi1 hi13
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
        i = 11 ∨ i = 12 ∨ i = 13 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

/-- [s1:condG1] (f) "Row 13 is G*": row 13 is `EG.Gamma1e` (item (e)), definitionally. -/
theorem row13_iff_gamma1e (μ : ℝ) : row 13 μ ↔ Gamma1e μ := Iff.rfl

/-- [s1:condG1] (f) "the inequality of row 12 is item (c)": for `μ > 0`,
`M̄ ≤ λ^{1.6}` iff `2A log₂(Aμ) ≤ 1.6μ`. -/
theorem row12_iff_gamma1c {μ : ℝ} (hμ : 0 < μ) : row 12 μ ↔ Gamma1c μ := by
  have hA : (0 : ℝ) < (Aexp : ℝ) * μ := by
    have : (0 : ℝ) < (Aexp : ℝ) := by norm_num [Aexp]
    positivity
  rw [row12_iff, Gamma1c, Mbar, lam, ← Real.rpow_mul (by norm_num),
    ← Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity),
    Real.logb_pow, Real.logb_rpow (by norm_num) (by norm_num)]
  push_cast
  constructor <;> intro h <;> linarith

/-! ## Column 4 -/

/-- [s3:tabCOLJV] (caption) "Column 4 gives, for row `i`, reals `a_i > 0` and `b_i, c_i ≥ 0`". -/
theorem triple_spec {i : ℕ} (h1 : 1 ≤ i) (h13 : i ≤ 13) :
    0 < (triple i).1 ∧ 0 ≤ (triple i).2.1 ∧ 0 ≤ (triple i).2.2 := by
  have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [triple, Aexp]

end EG.COLTable
