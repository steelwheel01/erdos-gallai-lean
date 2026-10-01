module

public import EG.Lib.Lend.COLTable
public import EG.Lib.Found.Gamma

/-!
# Column 3 of the COL-JV table holds for all large `μ` (manuscript s3:lemCOLJVev (iii))

Manuscript v6.1, `s3.tex`, Lemma [s3:lemCOLJVev] (iii): "Consequently, for each row of
Table s3:tabCOLJV, every inequality in column 3 holds at `λ = 2^μ` for all sufficiently large
real `μ`." Unit GAMMA (design note `formal/work/p2b/GAMMA.md`, §8 step 2).

Route (a direct one, not the type-(E) route of the TeX; the statement is the same eventuality):
for `μ ≥ 2^{40}` put `s := 7 + log₂ μ`. Then `s ≥ 47`, `μ ≥ 2^{18} s` (Bernoulli), `Aμ ≤ 2^s`
(`A = 105 ≤ 2^7`), hence `M̄ ≤ 2^{210 s}`, `M̄^2 ≤ λ^3` and `k̄ ≤ 2^{8 + 3μ}`. Every inequality
of column 3 is then a comparison `2^a ≤ 2^b` of powers of two with `a ≤ b` linear in `μ` and `s`.
Row 13 is item (e) of Γ1 (`row13_iff_gamma1e`), already proved for `μ ≥ 2^{20}`
(`EG.gamma1Items_of_le`).

Main results: `EG.COLTable.col3_of_le` (`col3 μ` for every real `μ ≥ 2^{40}`) and
`EG.COLTable.eventually_col3`. No `sorry`.
-/

public section

namespace EG.COLTable

open Real Filter

/-- `2^a ≤ 2^b` for `a ≤ b` (real exponents). -/
theorem rp {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem two_rpow_natCast (n : ℕ) : (2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ n := Real.rpow_natCast 2 n

/-- `c · x ≤ 2^e` from `0 ≤ c ≤ 2^a`, `x ≤ 2^b` and `a + b ≤ e`. -/
theorem cmul_le {c x a b e : ℝ} (hc : 0 ≤ c) (hca : c ≤ (2 : ℝ) ^ a) (hx : x ≤ (2 : ℝ) ^ b)
    (he : a + b ≤ e) : c * x ≤ (2 : ℝ) ^ e :=
  calc c * x ≤ c * (2 : ℝ) ^ b := mul_le_mul_of_nonneg_left hx hc
    _ ≤ (2 : ℝ) ^ a * (2 : ℝ) ^ b := mul_le_mul_of_nonneg_right hca (by positivity)
    _ = (2 : ℝ) ^ (a + b) := (Real.rpow_add two_pos a b).symm
    _ ≤ (2 : ℝ) ^ e := rp he

theorem lam_pow (μ : ℝ) (n : ℕ) : lam μ ^ n = (2 : ℝ) ^ (μ * n) := by
  rw [lam, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

theorem lam_rpow (μ r : ℝ) : lam μ ^ r = (2 : ℝ) ^ (μ * r) := by
  rw [lam, ← Real.rpow_mul (by norm_num)]

/-- For `μ ≥ 2^{40}` and `s = 7 + log₂ μ`: `s ≥ 47` and `2^{18} s ≤ μ`. -/
theorem s_bounds {μ : ℝ} (hμ : (2 : ℝ) ^ 40 ≤ μ) :
    47 ≤ 7 + logb 2 μ ∧ (2 : ℝ) ^ 18 * (7 + logb 2 μ) ≤ μ := by
  have hμ0 : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  have ht : (40 : ℝ) ≤ logb 2 μ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hμ0]
    rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, two_rpow_natCast]; exact hμ
  refine ⟨by linarith, ?_⟩
  have h1 := add_one_le_two_rpow (y := logb 2 μ - 20) (by linarith)
  have h2 : (2 : ℝ) ^ (logb 2 μ - 20) = μ / 2 ^ 20 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hμ0,
      show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, two_rpow_natCast]
  rw [h2, le_div_iff₀ (by norm_num)] at h1
  norm_num at h1 ⊢
  nlinarith

/-- `M̄^n ≤ 2^{(7 + log₂ μ)·210 n}` for `μ > 0` (`Aμ ≤ 2^{7 + log₂ μ}`). -/
theorem Mbar_pow_le {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    Mbar μ ^ n ≤ (2 : ℝ) ^ ((7 + logb 2 μ) * (210 * n)) := by
  have hA := logb_Aexp_mul_le hμ
  have hAμ : 0 < (Aexp : ℝ) * μ := by rw [cast_Aexp]; positivity
  have hAμle : (Aexp : ℝ) * μ ≤ (2 : ℝ) ^ (7 + logb 2 μ) := by
    rw [← Real.logb_le_iff_le_rpow (by norm_num) hAμ]; exact hA
  rw [Mbar, ← pow_mul, show 2 * Aexp * n = 210 * n by rw [Aexp_eq]]
  calc ((Aexp : ℝ) * μ) ^ (210 * n) ≤ ((2 : ℝ) ^ (7 + logb 2 μ)) ^ (210 * n) := by
        gcongr
    _ = (2 : ℝ) ^ ((7 + logb 2 μ) * (210 * n)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf

/-- `k̄ ≤ 2^{8 + 3μ}` for `μ ≥ 2^{40}`. -/
theorem kbar_le {μ : ℝ} (hμ : (2 : ℝ) ^ 40 ≤ μ) : kbar μ ≤ (2 : ℝ) ^ (8 + 3 * μ) := by
  have hμ0 : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  obtain ⟨hs1, hs2⟩ := s_bounds hμ
  have hM : Mbar μ ^ 2 ≤ (2 : ℝ) ^ (3 * μ) := by
    refine (Mbar_pow_le hμ0 2).trans (rp ?_)
    push_cast; nlinarith
  have hl : lam μ ^ 3 = (2 : ℝ) ^ (3 * μ) := by rw [lam_pow]; push_cast; ring_nf
  rw [kbar, hl, Real.rpow_add two_pos, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num,
    two_rpow_natCast]
  have : (0 : ℝ) < 2 ^ (3 * μ) := by positivity
  nlinarith

/-- Column 3 of the COL-JV table holds at every real `μ ≥ 2^{40}` (all 13 rows, 18
inequalities). -/
theorem col3_of_le {μ : ℝ} (hμ : (2 : ℝ) ^ 40 ≤ μ) : col3 μ := by
  have hμ0 : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  obtain ⟨hs1, hs2⟩ := s_bounds hμ
  set s := 7 + logb 2 μ with hs
  have hk := kbar_le hμ
  have hk0 := kbar_pos μ
  have hM0 := Mbar_nonneg' μ
  have hμ1 : (1 : ℝ) ≤ μ := le_trans (by norm_num) hμ
  have n2 : ∀ n : ℕ, (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) := fun n => (two_rpow_natCast n).symm
  -- `μ + 1 ≤ 2^μ`
  have hμexp : μ + 1 ≤ (2 : ℝ) ^ μ := add_one_le_two_rpow hμ1
  rw [col3_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- row 1
    rw [row1_iff, lam_rpow, lam_rpow]
    constructor
    · have hb : lam μ + 6 * μ + 20 ≤ (2 : ℝ) ^ (1 + μ) := by
        have h5 := add_one_le_two_rpow (y := μ - 5) (by linarith)
        rw [Real.rpow_sub two_pos, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
          two_rpow_natCast] at h5
        rw [Real.rpow_add two_pos, Real.rpow_one, lam]
        norm_num at h5
        linarith
      have hpos : 0 < lam μ + 6 * μ + 20 := by have := lam_pos μ; linarith
      calc 257 * (lam μ + 6 * μ + 20) ^ 102 ≤ 257 * ((2 : ℝ) ^ (1 + μ)) ^ 102 := by gcongr
        _ < (2 : ℝ) ^ (9 : ℝ) * ((2 : ℝ) ^ (1 + μ)) ^ 102 := by
            gcongr
            rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, two_rpow_natCast]; norm_num
        _ = (2 : ℝ) ^ (9 + (1 + μ) * 102) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add two_pos]
            push_cast; ring_nf
        _ ≤ (2 : ℝ) ^ (μ * (205 / 2)) := rp (by nlinarith)
    · rw [n2]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by push_cast; nlinarith)
  · -- row 2
    rw [row2_iff, lam_pow]
    exact (Mbar_pow_le hμ0 13).trans (rp (by push_cast; nlinarith))
  · -- row 3
    rw [row3_iff, lam_pow]
    exact cmul_le (a := 10) (by norm_num)
      (by rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, two_rpow_natCast]; norm_num) hk
      (by push_cast; nlinarith)
  · -- row 4
    rw [row4_iff, lam_rpow]
    calc (2 : ℝ) ^ 193 * 12 ^ 5 ≤ (2 : ℝ) ^ 213 := by norm_num
      _ = (2 : ℝ) ^ (213 : ℝ) := by rw [n2]; norm_num
      _ ≤ _ := rp (by nlinarith)
  · -- row 5
    rw [row5_iff, lam_pow]
    have hc : 3 * (2 : ℝ) ^ 167 ≤ (2 : ℝ) ^ (169 : ℝ) := by rw [n2]; norm_num
    have h1 : 3 * (2 : ℝ) ^ 167 * kbar μ ≤ (2 : ℝ) ^ (169 + (8 + 3 * μ)) :=
      cmul_le (by positivity) hc hk le_rfl
    rw [mul_comm _ (Mbar μ ^ 21)]
    exact cmul_le (by positivity) (Mbar_pow_le hμ0 21) h1 (by push_cast; nlinarith)
  · -- row 6
    rw [row6_iff, lam_pow]
    exact cmul_le (a := 110) (by positivity) (by rw [n2]; norm_num) (Mbar_pow_le hμ0 15)
      (by push_cast; nlinarith)
  · -- row 7
    rw [row7_iff, lam_rpow]
    calc (2 : ℝ) ^ 127 * 12 ^ 4 ≤ (2 : ℝ) ^ 142 := by norm_num
      _ = (2 : ℝ) ^ (142 : ℝ) := by rw [n2]; norm_num
      _ ≤ _ := rp (by nlinarith)
  · -- row 8
    rw [row8_iff, lam_pow, lam_pow, lam_pow]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [n2]; exact rp (by push_cast; nlinarith)
    · exact cmul_le (a := 186) (by positivity) (by rw [n2]; norm_num) hμexp
        (by push_cast; nlinarith)
    · exact cmul_le (a := 190) (by positivity) (by rw [n2]; norm_num) hμexp
        (by push_cast; nlinarith)
    · rw [n2]; exact rp (by push_cast; nlinarith)
    · have h6 : (2 * lam μ) ^ 6 = (2 : ℝ) ^ (6 + 6 * μ) := by
        rw [mul_pow, lam_pow, n2, ← Real.rpow_add two_pos]; push_cast; ring_nf
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (6 + 6 * μ) := Real.one_le_rpow (by norm_num) (by linarith)
      have h2 : (2 : ℝ) ^ (7 + 6 * μ) = 2 * (2 : ℝ) ^ (6 + 6 * μ) := by
        rw [show (7 : ℝ) + 6 * μ = 1 + (6 + 6 * μ) by ring, Real.rpow_add two_pos,
          Real.rpow_one]
      have h7 : (2 * lam μ) ^ 6 + 1 ≤ (2 : ℝ) ^ (7 + 6 * μ) := by
        rw [h6, h2]
        linarith
      exact cmul_le (a := 6) (by norm_num)
        (by rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, two_rpow_natCast]; norm_num) h7
        (by push_cast; nlinarith)
  · -- row 9
    rw [row9_iff, lam_rpow]
    exact hk.trans (rp (by nlinarith))
  · -- row 10
    rw [row10_iff, lam_pow]
    exact cmul_le (a := 1) (by norm_num) (by norm_num) hk (by push_cast; nlinarith)
  · -- row 11
    rw [row11_iff, lam_pow]
    exact cmul_le (a := 13) (by positivity) (by rw [n2]; norm_num) (Mbar_pow_le hμ0 12)
      (by push_cast; nlinarith)
  · -- row 12
    rw [row12_iff, lam_rpow]
    have := Mbar_pow_le hμ0 1
    rw [pow_one] at this
    exact this.trans (rp (by push_cast; nlinarith))
  · -- row 13 is item (e) of Γ1
    rw [row13_iff_gamma1e]
    exact (gamma1Items_of_le (le_trans (by norm_num) hμ)).e

/-- [s3:lemCOLJVev] (iii) "for each row of Table s3:tabCOLJV, every inequality in column 3
holds at `λ = 2^μ` for all sufficiently large real `μ`" (all rows at once). -/
theorem eventually_col3 : ∀ᶠ μ : ℝ in atTop, col3 μ :=
  (eventually_ge_atTop _).mono fun _ h => col3_of_le h

end EG.COLTable
