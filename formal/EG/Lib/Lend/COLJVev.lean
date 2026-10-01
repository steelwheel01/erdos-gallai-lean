module

public import EG.Lib.Lend.COLTable
public import EG.Lib.Gamma.Col3

/-!
# The eventual form of the COL-JV table, parts (i) and (ii) (manuscript s3:lemCOLJVev) — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemCOLJVev].
(i) "Let `μ ≥ max{1,v_0^2}` and `v := μ^{1/2}` … Hence `log v < v`, and `log μ = 2 log v ≤ 2v`.
As `c ≥ 0`, `aμ-b-c log(Aμ) = av^2-(b+c log A)-c log μ ≥ av^2-2cv-(b+c log A)`. The right side is a
quadratic polynomial in `v` … its larger root is `v_0`."
(ii) "`log M̄ = 2A log(Aμ)`, `log k̄ ≤ 3μ+4A log(Aμ)+9`, `6μ+20 ≤ 2^μ`, `(2λ)^6+1 ≤ 2^7λ^6`,
`log(μ+1) ≤ 1+log(Aμ)`" and the row-by-row lower bounds `φ ≥ a_iμ-b_i-c_i log(Aμ)`.

Here every column-3 inequality is shown as a comparison of powers of two (as in
`EG/Lib/Gamma/Col3.lean`), with `ℓ := log₂(Aμ)`: `M̄^n = 2^{210nℓ}` and `k̄ ≤ 2^{9+3μ+420ℓ}`.

Main results: `EG.COLTable.typeE_of_ge` (part (i)) and `EG.COLTable.row_of_typeE` (part (ii)).
-/

public section

namespace EG.COLTable

open Real

/-- `log₂ v < v` for `v ≥ 1` (from `v + 1 ≤ 2^v`). -/
theorem logb_two_lt_self {v : ℝ} (hv : 1 ≤ v) : logb 2 v < v := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith)]
  have := add_one_le_two_rpow hv
  linarith

theorem logb_Aexp_pos : 0 < logb 2 (Aexp : ℝ) := by
  rw [cast_Aexp]; exact Real.logb_pos (by norm_num) (by norm_num)

/-- [s3:lemCOLJVev] (i) "An inequality of type (E) holds for every `μ ≥ max{1, v_0^2}`". -/
theorem typeE_of_ge {a b c μ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hμ : max 1 (v0 a b c ^ 2) ≤ μ) : TypeE a b c μ := by
  have hμ1 : 1 ≤ μ := le_trans (le_max_left _ _) hμ
  have hμv : v0 a b c ^ 2 ≤ μ := le_trans (le_max_right _ _) hμ
  have hμ0 : 0 < μ := by linarith
  set v := Real.sqrt μ with hvdef
  have hv2 : v ^ 2 = μ := Real.sq_sqrt hμ0.le
  have hv1 : 1 ≤ v := by rw [hvdef]; exact Real.one_le_sqrt.2 hμ1
  have hvv0 : v0 a b c ≤ v := le_trans (le_abs_self _) (Real.abs_le_sqrt hμv)
  have hlA := logb_Aexp_pos
  have hA0 : (0 : ℝ) < Aexp := by rw [cast_Aexp]; norm_num
  have hlog : logb 2 ((Aexp : ℝ) * μ) = logb 2 (Aexp : ℝ) + 2 * logb 2 v := by
    rw [Real.logb_mul hA0.ne' hμ0.ne', ← hv2, Real.logb_pow]; push_cast; ring
  have hlv : logb 2 v ≤ v := (logb_two_lt_self hv1).le
  set K := b + c * logb 2 (Aexp : ℝ) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set s := Real.sqrt (c ^ 2 + a * K) with hsdef
  have hs2 : s ^ 2 = c ^ 2 + a * K := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hv0 : v0 a b c = (c + s) / a := rfl
  -- `a v ≥ c + s`
  have hav : c + s ≤ a * v := by
    rw [hv0, div_le_iff₀ ha] at hvv0; linarith
  have hprod : 0 ≤ (a * v - c - s) * (a * v - c + s) :=
    mul_nonneg (by linarith) (by linarith)
  have hq : 0 ≤ a * v ^ 2 - 2 * c * v - K := by
    by_contra hneg
    push Not at hneg
    have : a * (a * v ^ 2 - 2 * c * v - K) < 0 := mul_neg_of_pos_of_neg ha hneg
    nlinarith
  unfold TypeE
  rw [hlog, ← hv2]
  have : c * logb 2 v ≤ c * v := mul_le_mul_of_nonneg_left hlv hc
  nlinarith

/-! ## Part (ii) -/

section rows

variable {μ : ℝ}

/-- `ℓ := log₂(Aμ) ≥ 0` and `2^ℓ = Aμ` for `μ ≥ 1`. -/
theorem ell_facts (hμ : 1 ≤ μ) :
    0 ≤ logb 2 ((Aexp : ℝ) * μ) ∧ (2 : ℝ) ^ logb 2 ((Aexp : ℝ) * μ) = (Aexp : ℝ) * μ := by
  have hA : (1 : ℝ) ≤ (Aexp : ℝ) * μ := by rw [cast_Aexp]; nlinarith
  exact ⟨Real.logb_nonneg (by norm_num) hA,
    Real.rpow_logb (by norm_num) (by norm_num) (by linarith)⟩

/-- `M̄^n = 2^{ℓ·210n}` (`log M̄ = 2A log(Aμ)`). -/
theorem Mbar_pow_eq (hμ : 1 ≤ μ) (n : ℕ) :
    Mbar μ ^ n = (2 : ℝ) ^ (logb 2 ((Aexp : ℝ) * μ) * (210 * n)) := by
  have e := (ell_facts hμ).2
  rw [Mbar, ← pow_mul, show 2 * Aexp * n = 210 * n by rw [Aexp_eq]]
  conv_lhs => rw [← e]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  push_cast; ring_nf

/-- `k̄ ≤ 2^{9+3μ+420ℓ}` ("`log k̄ ≤ 3μ+4A log(Aμ)+9`"). -/
theorem kbar_le_ell (hμ : 1 ≤ μ) :
    kbar μ ≤ (2 : ℝ) ^ (9 + 3 * μ + 420 * logb 2 ((Aexp : ℝ) * μ)) := by
  obtain ⟨hℓ, -⟩ := ell_facts hμ
  have hl3 : lam μ ^ 3 = (2 : ℝ) ^ (3 * μ) := by rw [lam_pow]; push_cast; ring_nf
  have hM2 : Mbar μ ^ 2 = (2 : ℝ) ^ (420 * logb 2 ((Aexp : ℝ) * μ)) := by
    rw [Mbar_pow_eq hμ]; push_cast; ring_nf
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (3 * μ) := Real.one_le_rpow (by norm_num) (by linarith)
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (420 * logb 2 ((Aexp : ℝ) * μ)) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have e : (2 : ℝ) ^ (9 + 3 * μ + 420 * logb 2 ((Aexp : ℝ) * μ)) =
      2 ^ 9 * ((2 : ℝ) ^ (3 * μ) * (2 : ℝ) ^ (420 * logb 2 ((Aexp : ℝ) * μ))) := by
    rw [Real.rpow_add two_pos, Real.rpow_add two_pos,
      show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, two_rpow_natCast]; ring
  rw [kbar, hl3, hM2, e]
  nlinarith

theorem mulA (k : ℝ) : k * (Aexp : ℝ) = k * 105 := by rw [cast_Aexp]

theorem n2 (n : ℕ) : (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) := (two_rpow_natCast n).symm

theorem rowE1 (h : TypeE (1 / 2) 112 0 μ) : row 1 μ := by
  unfold TypeE at h
  have hμ : 224 ≤ μ := by linarith
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

theorem rowE2 (hμ : 1 ≤ μ) (h : TypeE 103 0 (26 * Aexp) μ) : row 2 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row2_iff, lam_pow, Mbar_pow_eq hμ]
  exact rp (by push_cast; linarith)

theorem rowE3 (hμ : 1 ≤ μ) (h : TypeE 96 19 (4 * Aexp) μ) : row 3 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row3_iff, lam_pow]
  refine cmul_le (a := 10) (by norm_num)
    (by rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, two_rpow_natCast]; norm_num)
    (kbar_le_ell hμ) ?_
  push_cast; linarith

theorem rowE4 (h : TypeE (421 / 10) 211 0 μ) : row 4 μ := by
  unfold TypeE at h
  rw [row4_iff, lam_rpow]
  calc (2 : ℝ) ^ 193 * 12 ^ 5 ≤ (2 : ℝ) ^ 211 := by norm_num
    _ = (2 : ℝ) ^ (211 : ℝ) := by rw [n2]; norm_num
    _ ≤ _ := rp (by linarith)

theorem rowE5 (hμ : 1 ≤ μ) (h : TypeE 69 178 (46 * Aexp) μ) : row 5 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row5_iff, lam_pow]
  have hc : 3 * (2 : ℝ) ^ 167 ≤ (2 : ℝ) ^ (169 : ℝ) := by rw [n2]; norm_num
  have h1 := cmul_le (by positivity) hc (kbar_le_ell hμ) le_rfl
  rw [mul_comm _ (Mbar μ ^ 21)]
  refine cmul_le (pow_nonneg (Mbar_nonneg' μ) 21) (le_of_eq (Mbar_pow_eq hμ 21)) h1 ?_
  push_cast; linarith

theorem rowE6 (hμ : 1 ≤ μ) (h : TypeE 84 110 (30 * Aexp) μ) : row 6 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row6_iff, lam_pow]
  refine cmul_le (a := 110) (by positivity) (by rw [n2]; norm_num)
    (le_of_eq (Mbar_pow_eq hμ 15)) ?_
  push_cast; linarith

theorem rowE7 (h : TypeE (322 / 5) 142 0 μ) : row 7 μ := by
  unfold TypeE at h
  rw [row7_iff, lam_rpow]
  calc (2 : ℝ) ^ 127 * 12 ^ 4 ≤ (2 : ℝ) ^ 142 := by norm_num
    _ = (2 : ℝ) ^ (142 : ℝ) := by rw [n2]; norm_num
    _ ≤ _ := rp (by linarith)

theorem rowE8 (hμ : 6 ≤ μ) (h : TypeE 58 194 1 μ) : row 8 μ := by
  unfold TypeE at h
  obtain ⟨hℓ, h2ℓ⟩ := ell_facts (by linarith : (1 : ℝ) ≤ μ)
  -- `μ + 1 ≤ 2^{1+ℓ} = 2Aμ`
  have hμ1 : μ + 1 ≤ (2 : ℝ) ^ (1 + logb 2 ((Aexp : ℝ) * μ)) := by
    rw [Real.rpow_add two_pos, Real.rpow_one, h2ℓ, cast_Aexp]; linarith
  rw [row8_iff, lam_pow, lam_pow, lam_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [n2]; exact rp (by push_cast; linarith)
  · exact cmul_le (a := 186) (by positivity) (by rw [n2]; norm_num) hμ1
      (by push_cast; linarith)
  · exact cmul_le (a := 190) (by positivity) (by rw [n2]; norm_num) hμ1
      (by push_cast; linarith)
  · rw [n2]; exact rp (by push_cast; linarith)
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
      (by push_cast; linarith)

theorem rowE9 (hμ : 1 ≤ μ) (h : TypeE (3 / 10) 9 (4 * Aexp) μ) : row 9 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row9_iff, lam_rpow]
  exact (kbar_le_ell hμ).trans (rp (by linarith))

theorem rowE10 (hμ : 1 ≤ μ) (h : TypeE 1 10 (4 * Aexp) μ) : row 10 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row10_iff, lam_pow]
  exact cmul_le (a := 1) (by norm_num) (by norm_num) (kbar_le_ell hμ) (by push_cast; linarith)

theorem rowE11 (hμ : 1 ≤ μ) (h : TypeE 95 13 (24 * Aexp) μ) : row 11 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row11_iff, lam_pow]
  exact cmul_le (a := 13) (by positivity) (by rw [n2]; norm_num)
    (le_of_eq (Mbar_pow_eq hμ 12)) (by push_cast; linarith)

theorem rowE12 (hμ : 1 ≤ μ) (h : TypeE (8 / 5) 0 (2 * Aexp) μ) : row 12 μ := by
  unfold TypeE at h; rw [mulA] at h
  rw [row12_iff, lam_rpow]
  have := Mbar_pow_eq hμ 1
  rw [pow_one] at this
  rw [this]
  exact rp (by push_cast; linarith)

theorem rowE13 (hμ : 1 ≤ μ) (h : TypeE 36 240 (46 * Aexp) μ) : row 13 μ := by
  unfold TypeE at h; rw [mulA] at h
  have hM : ((Aexp : ℝ) * μ) ^ (46 * Aexp) =
      (2 : ℝ) ^ (logb 2 ((Aexp : ℝ) * μ) * (46 * 105)) := by
    have e := (ell_facts hμ).2
    conv_lhs => rw [← e]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Aexp_eq]
    push_cast; ring_nf
  rw [row13_iff, lam_pow, hM]
  exact cmul_le (a := 240) (by positivity) (by rw [n2]; norm_num) le_rfl
    (by push_cast; linarith)

/-- [s3:lemCOLJVev] (ii) "Let `μ ≥ 6` … If `a_iμ-b_i-c_i log(Aμ) ≥ 0`, then every inequality
in column 3 of row `i` holds at `λ`." -/
theorem row_of_typeE (hμ : 6 ≤ μ) {i : ℕ} (h1 : 1 ≤ i) (h13 : i ≤ 13)
    (h : TypeE (triple i).1 (triple i).2.1 (triple i).2.2 μ) : row i μ := by
  have hμ1 : (1 : ℝ) ≤ μ := by linarith
  have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowE1 h
  · exact rowE2 hμ1 h
  · exact rowE3 hμ1 h
  · exact rowE4 h
  · exact rowE5 hμ1 h
  · exact rowE6 hμ1 h
  · exact rowE7 h
  · exact rowE8 hμ h
  · exact rowE9 hμ1 h
  · exact rowE10 hμ1 h
  · exact rowE11 hμ1 h
  · exact rowE12 hμ1 h
  · exact rowE13 hμ1 h

end rows

end EG.COLTable
