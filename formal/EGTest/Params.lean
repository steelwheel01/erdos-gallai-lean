import EG.Lib.Link.Star
import EG.Lib.Vortex.Params
import EG.Lib.Lend.COLTable

/-! Unit tests for the parameter definitions of s3/s4 (TRIAGE §3 items 11–13):
the (eqStar) parameters `EG.Star.*`, the vortex parameters and size predicates `EG.Vortex.*`,
and the COL-JV table `EG.COLTable.*`. Numeric values are checked where this is cheap. -/

namespace EGTest.Params

open EG Real

/-! ## (eqStar) at `n = 2` (so `L = 1`, `ℓ_* = 2^{10}`) and `ρ = ε' = t = 1` -/

theorem L2 : Star.L 2 = 1 := by
  rw [Star.L]; norm_num

theorem ell2 : Star.ell 2 = 1024 := by
  rw [Star.ell, L2]; norm_num

example : Star.ell 4 = 8192 := by
  rw [Star.ell, Star.L, show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

-- `ρ = 1`: the base `(1-ρ)/(1-0.9ρ)` is `0`, so `p_* = 1`
theorem p21 : Star.p 2 1 = 1 := Star.p_one le_rfl

theorem d21 : Star.d 2 1 = 1 := by rw [Star.d, p21]; norm_num
theorem lam21 : Star.lam 2 1 = 6 := by rw [Star.lam, p21]; norm_num
-- `Δ_* = λ_* + ⌈d_*λ_*/3⌉ = 6 + 2`
example : Star.Delta 2 1 = 8 := by rw [Star.Delta, d21, lam21]; norm_num
example : Star.sigma 2 1 = 24 := by rw [Star.sigma, L2]; norm_num
example : Star.g 2 1 = 1 / 8 := by rw [Star.g, L2]; norm_num
example : Star.q 1 = 9 / 10 := by rw [Star.q]; norm_num

-- `θ_* = 2^{19}·2^{20}·1 = 2^{39}` (the upper bound of (S4) is attained here)
theorem theta211 : Star.theta 2 1 1 = 2 ^ 39 := by rw [Star.theta, ell2, L2]; norm_num
example : Star.mu 2 1 1 = 1 / (6 * 2 ^ 39) := by rw [Star.mu, theta211, L2]; norm_num
theorem sbar211 : Star.sbar 2 1 1 = 2 ^ 28 := by rw [Star.sbar, L2]; norm_num
-- `K_* = ⌈6·2^{28}·2^{39}⌉ = 6·2^{67}` (compare (S5): `K_* ≤ (6·2^{81}+1) t L^{19} ρ^{-3}`)
example : Star.K 2 1 1 1 = 6 * 2 ^ 67 := by
  rw [Star.K, sbar211, theta211, L2]; norm_num
-- `(S5)`: `K_* ≥ s̄_*/μ_*`, with equality before rounding
example : Star.sbar 2 1 1 / Star.mu 2 1 1 = Star.K 2 1 1 1 := by
  rw [Star.K, Star.mu, sbar211, theta211, L2]; norm_num

-- `M_* = ⌈2.1/ρ⌉`
example : Star.M 1 = 3 := by rw [Star.M, Nat.ceil_eq_iff (by norm_num)]; norm_num
example : Star.M (1 / 2) = 5 := by rw [Star.M, Nat.ceil_eq_iff (by norm_num)]; norm_num
example : Star.M (1 / 10) = 21 := by rw [Star.M]; norm_num

-- `ρ = 1/2`: `(1-p_*)^{1023} = (1/2)/(1-0.45) = 10/11`, and `p_* ∈ (0,1)`
example : (1 - Star.p 2 (1 / 2)) ^ (Star.ell 2 - 1) = 10 / 11 := by
  rw [Star.one_sub_p_pow le_rfl (by norm_num)]; norm_num
example : (1 - Star.p 2 (1 / 2)) ^ 1023 = 10 / 11 := by
  have := Star.one_sub_p_pow (n := 2) (ρ := 1 / 2) le_rfl (by norm_num)
  rw [ell2] at this; norm_num at this ⊢; exact this
example : 0 < Star.p 2 (1 / 2) ∧ Star.p 2 (1 / 2) < 1 := by
  refine ⟨Star.p_pos le_rfl (by norm_num) (by norm_num), ?_⟩
  by_contra h
  have h1 : Star.p 2 (1 / 2) = 1 := le_antisymm (Star.p_le_one (by norm_num)) (not_lt.1 h)
  have := Star.one_sub_p_pow (n := 2) (ρ := 1 / 2) le_rfl (by norm_num)
  rw [h1, ell2] at this; norm_num at this
-- uniqueness: a number with the defining property is `p_*`
example (x : ℝ) (hx : x ≤ 1) (h : (1 - x) ^ (Star.ell 2 - 1) = 10 / 11) : x = Star.p 2 (1 / 2) :=
  Star.p_unique le_rfl (by norm_num) hx (by rw [h]; norm_num)

-- `K_* > 0` in the domain (T16* colours with `Fin K_*`), and `ℓ_* > 0`
example : 0 < Star.K 2 1 1 1 := Star.K_pos le_rfl one_pos one_pos one_pos
example : NeZero (Star.K 2 (1 / 2) (1 / 2) 1) :=
  ⟨Star.K_ne_zero le_rfl (by norm_num) (by norm_num) one_pos⟩
example : 0 < Star.ell 2 := Star.ell_pos le_rfl

-- the (S6)/P13* facts in the degenerate case `p_* = 1`
example : (6 : ℝ) ≤ Star.lam 2 1 * Star.p 2 1 := by rw [lam21, p21]; norm_num
example : ((Star.d 2 1 : ℝ) * Star.lam 2 1) / 3 ≤ (Star.Delta 2 1 : ℝ) - Star.lam 2 1 :=
  Star.dlam_div_three_le 2 1

/-! ## Vortex parameters at `N = 2^{1024}` (so `L = 1024`) -/

section Vortex

open Vortex

theorem L1024 : Vortex.L (2 ^ 1024) = 1024 := by rw [L_pow]; norm_num

-- `J_TPV = ⌊log₂(1024/6)⌋ = 7`
theorem tpvJ1024 : tpvJ (2 ^ 1024) = 7 := by
  rw [tpvJ, L1024, Nat.floor_eq_iff (Real.logb_nonneg (by norm_num) (by norm_num))]
  constructor
  · rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num),
      show ((7 : ℕ) : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    norm_num
  · rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num),
      show ((7 : ℕ) : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
example : vxJ (2 ^ 1024) = 7 := tpvJ1024
-- `J_PV = ⌊log₂(1024/8)⌋ = ⌊log₂ 128⌋ = 7`
theorem pvJ1024 : pvJ (2 ^ 1024) = 7 := by
  rw [pvJ, L1024, show (1024 : ℝ) / 8 = 2 ^ (7 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num
-- the bounds (s4:eqTPVJ), (s4:eqPVJ) at this `N`
example : 6 * (2 : ℝ) ^ tpvJ (2 ^ 1024) ≤ 1024 ∧ (1024 : ℝ) < 12 * 2 ^ tpvJ (2 ^ 1024) := by
  rw [tpvJ1024]; norm_num
example : 8 * (2 : ℝ) ^ pvJ (2 ^ 1024) ≤ 1024 ∧ (1024 : ℝ) < 16 * 2 ^ pvJ (2 ^ 1024) := by
  rw [pvJ1024]; norm_num
-- `m = ⌈L^6⌉ = 2^{60}` and `b = ⌈2^7 L^2 m⌉ = 2^{87}`
theorem pvM1024 : pvM (2 ^ 1024) = 2 ^ 60 := by
  rw [pvM, L1024, show (1024 : ℝ) ^ 6 = ((2 ^ 60 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
example : pvB (2 ^ 1024) = 2 ^ 87 := by
  rw [pvB, L1024, pvM1024,
    show (2 : ℝ) ^ 7 * 1024 ^ 2 * ((2 ^ 60 : ℕ) : ℝ) = ((2 ^ 87 : ℕ) : ℝ) by norm_num,
    Nat.ceil_natCast]

/-- `2^k e^{-x} ≤ 2^{-20}` once `x ≥ k + 20`. -/
theorem tail (k : ℕ) (x : ℝ) (hx : (k : ℝ) + 20 ≤ x) : (2 : ℝ) ^ k * exp (-x) ≤ 1 / 2 ^ 20 := by
  have h0 : (0 : ℝ) ≤ x := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have := two_pow_mul_exp_neg_le k (y := 20) h0 hx
  rwa [Real.rpow_neg (by norm_num), show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, inv_eq_one_div] at this

/-- `2^a / 2^m ≤ 2^{-20}` once `a + 20 ≤ m` (no large numeral is evaluated). -/
theorem small (a m : ℕ) (h : a + 20 ≤ m) : (2 : ℝ) ^ a * ((2 : ℝ) ^ m)⁻¹ ≤ 1 / 2 ^ 20 := by
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem cast1024 : ((2 ^ 1024 : ℕ) : ℝ) = (2 : ℝ) ^ 1024 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]

theorem cond_ii_1024 : Vortex.L (2 ^ 1024) ^ 3 ≤ ((2 ^ 1024 : ℕ) : ℝ) := by
  rw [L1024, cast1024]
  exact le_trans (by norm_num : (1024 : ℝ) ^ 3 ≤ 2 ^ 30) (pow_le_pow_right₀ (by norm_num) (by norm_num))

theorem zpow1024 (k : ℕ) : ((2 : ℝ) ^ 1024) ^ (-(k : ℤ)) = ((2 : ℝ) ^ (1024 * k))⁻¹ := by
  rw [zpow_neg, zpow_natCast, ← pow_mul]

theorem mul1024 : (2 : ℝ) ^ 1024 * 1024 = 2 ^ 1034 := by
  rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, ← pow_add]

/-- Size conditions (i), (ii), (iv) of Lemma TPV hold at `N = 2^{1024}` (non-vacuity of
`TPVSize`; the manuscript notes that (i) forces `N_0 ≥ 2^{1024}`). -/
theorem tpvSize1024 : TPVSize (2 ^ 1024) := by
  refine ⟨by rw [L1024]; norm_num, cond_ii_1024, ?_⟩
  rw [etaTPV, L1024, cast1024, mul1024,
    show (-5 : ℤ) = -((5 : ℕ) : ℤ) from rfl, show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl,
    zpow1024, zpow1024, show (2 : ℝ) * 1024 = 2 ^ 11 by norm_num,
    show (2 : ℝ) ^ 96 * 1024 ^ 31 = 2 ^ 406 by
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, ← pow_mul, ← pow_add]]
  have h1 := small 11 (1024 * 5) (by norm_num)
  have h2 := small 406 (1024 * 3) (by norm_num)
  have h3 := tail 1034 (3 * 1024 ^ 4 / 8) (by norm_num)
  exact le_trans (add_le_add (add_le_add h1 h2) h3) (by norm_num)

theorem pvSize1024 : PVSize (2 ^ 1024) := by
  refine ⟨by rw [L1024]; norm_num, cond_ii_1024, ?_⟩
  rw [etaPV, L1024, cast1024, mul1024, show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, zpow1024,
    show (2 : ℝ) ^ 95 * 1024 ^ 31 = 2 ^ 405 by
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, ← pow_mul, ← pow_add]]
  have h1 := small 405 (1024 * 3) (by norm_num)
  have h3 := tail 1034 (1024 ^ 4 / 16) (by norm_num)
  exact le_trans (add_le_add h1 h3) (by norm_num)

theorem vxSize1024 : VXSize (2 ^ 1024) := by
  refine ⟨by rw [L1024]; norm_num, cond_ii_1024, ?_⟩
  have hlog : logb 2 (1024 : ℝ) = 10 := by
    rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [etaVX, L1024, hlog, cast1024, mul1024,
    show (-5 : ℤ) = -((5 : ℕ) : ℤ) from rfl, show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl,
    zpow1024, zpow1024, show (2 : ℝ) * 1024 = 2 ^ 11 by norm_num,
    show (2 : ℝ) ^ 95 * 1024 ^ 28 = 2 ^ 375 by
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, ← pow_mul, ← pow_add],
    show (1024 : ℝ) * exp (-((2 : ℝ) ^ 1024 / (5000 * 1024))) =
      2 ^ 10 * exp (-((2 : ℝ) ^ 1024 / (5000 * 1024))) by norm_num]
  have h1 := small 11 (1024 * 5) (by norm_num)
  have h2 := small 375 (1024 * 3) (by norm_num)
  have h3 := tail 1034 (3 * 1024 ^ 2 / (32 * 10)) (by norm_num)
  have h4 := tail 10 ((2 : ℝ) ^ 1024 / (5000 * 1024)) (by
    rw [le_div_iff₀ (by norm_num)]
    have : ((10 : ℕ) : ℝ) + 20 ≤ 2 ^ 30 / (5000 * 1024) := by norm_num
    rw [le_div_iff₀ (by norm_num)] at this
    exact this.trans (by gcongr <;> norm_num))
  exact le_trans (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) (by norm_num)

example : TPVSize (2 ^ 1024) ∧ PVSize (2 ^ 1024) ∧ VXSize (2 ^ 1024) :=
  ⟨tpvSize1024, pvSize1024, vxSize1024⟩

-- negative tests: small `N` fails size condition (i)
example : ¬ TPVSize 2 := by
  rintro ⟨h, -⟩
  rw [Vortex.L] at h; norm_num at h
example : ¬ VXSize (2 ^ 1023) := by
  rintro ⟨h, -⟩
  rw [L_pow] at h; norm_num at h

-- size condition (iii) is derived from (i)
example {N : ℕ} (h : TPVSize N) : (4 * 48 : ℝ) ≤ Vortex.L N := h.cond_iii

end Vortex

/-! ## The COL-JV table -/

section COLTable

open COLTable

example : lam 0 = 1 := by rw [lam]; norm_num
example : lam 10 = 1024 := by
  rw [lam, show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
example : Mbar 0 = 0 := by rw [Mbar]; norm_num [Aexp]
example : kbar 0 = 192 := by rw [kbar, Mbar, lam]; norm_num [Aexp]

-- rows are numbered 1 … 13; there is no row 0 or 14
example (μ : ℝ) : row 0 μ := row_zero μ
example (μ : ℝ) : row 14 μ := row_of_gt (by norm_num) μ
example (μ : ℝ) : row 13 μ ↔ Gamma1e μ := row13_iff_gamma1e μ
example : row 12 1 ↔ Gamma1c 1 := row12_iff_gamma1c one_pos

-- row 1 fails at `μ = 0` (`λ = 1`), hence so does `col3`
theorem not_row1_zero : ¬ row 1 0 := by
  rw [row1_iff, lam, Real.rpow_zero, Real.one_rpow]
  rintro ⟨h, -⟩
  norm_num at h
example : ¬ col3 0 := fun h => not_row1_zero (h.row le_rfl (by norm_num))

-- row 4 holds at `μ = 20` (`λ^{42.1} = 2^{842} ≥ 2^{193}·12^5`)
example : row 4 20 := by
  rw [row4_iff, lam, ← Real.rpow_mul (by norm_num),
    show (20 : ℝ) * (421 / 10) = ((842 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (2 : ℝ) ^ 193 * 12 ^ 5 ≤ 2 ^ 193 * 2 ^ 20 := by gcongr; norm_num
    _ = 2 ^ 213 := by rw [← pow_add]
    _ ≤ 2 ^ 842 := pow_le_pow_right₀ (by norm_num) (by norm_num)

-- column 4
example : triple 1 = (1 / 2, 112, 0) := rfl
example : triple 8 = (58, 194, 1) := rfl
example : triple 13 = (36, 240, 4830) := by simp [triple, Aexp]; norm_num
example : triple 14 = (0, 0, 0) := rfl
example : 0 < (triple 5).1 ∧ 0 ≤ (triple 5).2.1 ∧ 0 ≤ (triple 5).2.2 :=
  triple_spec (by norm_num) (by norm_num)
-- row 1: `(0.5, 112, 0)`, i.e. `μ/2 - 112 ≥ 0`; `v_0^2 = 224`
example : TypeE (1 / 2) 112 0 224 := by rw [TypeE]; norm_num
example : ¬ TypeE (1 / 2) 112 0 223 := by rw [TypeE]; norm_num
example : v0 (1 / 2) 112 0 ^ 2 = 224 := by
  have h : (0 : ℝ) ^ 2 + 1 / 2 * (112 + 0 * logb 2 (Aexp : ℝ)) = 56 := by norm_num
  rw [v0, h, zero_add, div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-! ### Non-vacuity of Γ1(f): `col3` holds at `μ = 2^{13}` (`λ = 2^{8192}`)

All 13 rows (18 inequalities). Large powers of two are compared through their exponents
(`tp`); no large numeral is evaluated. Witness from the round-1 review
(`work/p2d/params.review1.md`, appendix). -/

namespace Col3Witness

theorem tp {a b : ℕ} (h : a ≤ b) : (2:ℝ)^a ≤ 2^b := pow_le_pow_right₀ (by norm_num) h

theorem hL : lam 8192 = (2:ℝ)^(8192:ℕ) := by
  rw [lam, show (8192:ℝ) = ((8192:ℕ):ℝ) by norm_num, Real.rpow_natCast]

theorem hR (q : ℝ) (k : ℕ) (h : 8192 * q = k) : lam 8192 ^ q = (2:ℝ)^k := by
  rw [lam, ← Real.rpow_mul (by norm_num), h, Real.rpow_natCast]

theorem hN (k : ℕ) : lam 8192 ^ k = (2:ℝ)^(8192*k) := by rw [hL, ← pow_mul]

theorem lam_ge_one : 1 ≤ lam 8192 := by rw [hL]; exact one_le_pow₀ (by norm_num)

theorem hRle (q q' : ℝ) (k : ℕ) (h : 8192 * q' = k) (hq : q' ≤ q) : (2:ℝ)^k ≤ lam 8192 ^ q := by
  rw [← hR q' k h]; exact Real.rpow_le_rpow_of_exponent_le lam_ge_one hq

theorem hA : (Aexp:ℝ) * 8192 ≤ 2^20 := by norm_num [Aexp]

theorem hM : Mbar 8192 ≤ 2^4200 := by
  rw [Mbar]
  calc ((Aexp:ℝ) * 8192) ^ (2 * Aexp) ≤ ((2:ℝ)^20) ^ (2 * Aexp) :=
        pow_le_pow_left₀ (by positivity) hA _
    _ = 2^4200 := by rw [← pow_mul, show 20 * (2 * Aexp) = 4200 by norm_num [Aexp]]

theorem hMp (k : ℕ) : Mbar 8192 ^ k ≤ 2^(4200*k) := by
  rw [pow_mul]; exact pow_le_pow_left₀ (Mbar_nonneg' _) hM k

theorem hK : kbar 8192 ≤ 2^24585 := by
  rw [kbar, hN 3]
  have h1 : (192:ℝ) * 2^(8192*3) ≤ 2^24584 := by
    rw [show (24584:ℕ) = 8 + 8192*3 by norm_num, pow_add]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have h2 : (4/3:ℝ) * Mbar 8192 ^ 2 ≤ 2^24584 := by
    calc (4/3:ℝ) * Mbar 8192 ^ 2 ≤ 2 * 2^(4200*2) :=
          mul_le_mul (by norm_num) (hMp 2) (pow_nonneg (Mbar_nonneg' _) 2) (by norm_num)
      _ = 2^(1 + 4200*2) := by rw [pow_add, pow_one]
      _ ≤ 2^24584 := tp (by norm_num)
  calc _ ≤ (2:ℝ)^24584 + 2^24584 := add_le_add h1 h2
    _ = 2^24585 := by rw [← two_mul, ← pow_succ']

theorem col3_8192 : col3 8192 := by
  rw [col3_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- row 1
    rw [row1_iff]
    constructor
    · have hb : lam 8192 + 6 * 8192 + 20 ≤ (2:ℝ)^8193 := by
        have h2 : (2:ℝ)^8193 = 2^8192 * 2 := pow_succ 2 8192
        rw [hL, h2]
        have : (6 * 8192 + 20 : ℝ) ≤ 2^8192 := by
          calc (6 * 8192 + 20 : ℝ) ≤ 2^16 := by norm_num
            _ ≤ 2^8192 := tp (by norm_num)
        clear h2
        generalize (2:ℝ)^8192 = x at *
        linarith
      have hpos : 0 ≤ lam 8192 + 6 * 8192 + 20 := by linarith [lam_pos 8192]
      calc 257 * (lam 8192 + 6 * 8192 + 20) ^ 102 ≤ 257 * ((2:ℝ)^8193)^102 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hb 102) (by norm_num)
        _ < 2^9 * ((2:ℝ)^8193)^102 := mul_lt_mul_of_pos_right (by norm_num) (by positivity)
        _ = 2^(9 + 8193*102) := by rw [pow_add, pow_mul]
        _ ≤ 2^839680 := tp (by norm_num)
        _ = lam 8192 ^ (205/2 : ℝ) := (hR _ _ (by norm_num)).symm
    · rw [hR (1/2) 4096 (by norm_num)]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
  · -- row 2
    rw [row2_iff, hN]; exact (hMp 13).trans (tp (by norm_num))
  · -- row 3
    rw [row3_iff, hN]
    calc 640 * kbar 8192 ≤ 2^10 * 2^24585 :=
          mul_le_mul (by norm_num) hK (by linarith [kbar_pos 8192]) (by positivity)
      _ = 2^(10 + 24585) := by rw [pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 4
    rw [row4_iff]
    calc (2:ℝ)^193 * 12^5 ≤ 2^193 * 2^20 := by gcongr; norm_num
      _ = 2^(193+20) := by rw [pow_add]
      _ ≤ 2^(8192*42) := tp (by norm_num)
      _ ≤ _ := hRle _ 42 _ (by norm_num) (by norm_num)
  · -- row 5
    rw [row5_iff, hN]
    calc 3 * (2:ℝ)^167 * kbar 8192 * Mbar 8192 ^ 21 ≤ 2^2 * 2^167 * 2^24585 * 2^(4200*21) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hK
            (kbar_pos _).le (by positivity)) (hMp 21) (pow_nonneg (Mbar_nonneg' _) _)
            (by positivity)
      _ = 2^(2 + 167 + 24585 + 4200*21) := by rw [pow_add, pow_add, pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 6
    rw [row6_iff, hN]
    calc (2:ℝ)^110 * Mbar 8192 ^ 15 ≤ 2^110 * 2^(4200*15) := by gcongr; exact hMp 15
      _ = 2^(110 + 4200*15) := by rw [pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 7
    rw [row7_iff]
    calc (2:ℝ)^127 * 12^4 ≤ 2^127 * 2^15 := by gcongr; norm_num
      _ = 2^(127+15) := by rw [pow_add]
      _ ≤ 2^(8192*64) := tp (by norm_num)
      _ ≤ _ := hRle _ 64 _ (by norm_num) (by norm_num)
  · -- row 8
    rw [row8_iff, hN, hN]
    refine ⟨tp (by norm_num), ?_, ?_, tp (by norm_num), ?_⟩
    · calc (2:ℝ)^186 * (8192 + 1) ≤ 2^186 * 2^14 := by gcongr; norm_num
        _ = 2^(186+14) := by rw [pow_add]
        _ ≤ _ := tp (by norm_num)
    · calc (2:ℝ)^190 * (8192 + 1) ≤ 2^190 * 2^14 := by gcongr; norm_num
        _ = 2^(190+14) := by rw [pow_add]
        _ ≤ _ := tp (by norm_num)
    · rw [hN]
      have h1 : (1:ℝ) ≤ (2 * lam 8192) ^ 6 := one_le_pow₀ (by linarith [lam_ge_one])
      calc 64 * ((2 * lam 8192) ^ 6 + 1) ≤ 64 * (2 * (2 * lam 8192) ^ 6) := by gcongr; linarith
        _ = 2^(7 + 8193*6) := by
          have h2l : 2 * lam 8192 = (2:ℝ)^8193 := by rw [hL]; exact (pow_succ' 2 8192).symm
          rw [h2l, ← pow_mul, pow_add]
          generalize (2:ℝ)^(8193*6) = x
          norm_num; ring
        _ ≤ _ := tp (by norm_num)
  · -- row 9
    rw [row9_iff]
    exact hK.trans ((tp (by norm_num : 24585 ≤ 26624)).trans (hRle _ (13/4) _ (by norm_num) (by norm_num)))
  · -- row 10
    rw [row10_iff, hN]
    calc 2 * kbar 8192 ≤ 2 * 2^24585 := by gcongr; exact hK
      _ = 2^(24585+1) := by rw [pow_succ 2 24585, mul_comm]
      _ ≤ _ := tp (by norm_num)
  · -- row 11
    rw [row11_iff, hN]
    calc (2:ℝ)^13 * Mbar 8192 ^ 12 ≤ 2^13 * 2^(4200*12) := by gcongr; exact hMp 12
      _ = 2^(13 + 4200*12) := by rw [pow_add]
      _ ≤ _ := tp (by norm_num)
  · -- row 12
    rw [row12_iff]
    exact hM.trans ((tp (by norm_num : 4200 ≤ 12288)).trans (hRle _ (3/2) _ (by norm_num) (by norm_num)))
  · -- row 13
    rw [row13_iff, hN]
    calc (2:ℝ)^240 * ((Aexp:ℝ) * 8192) ^ (46 * Aexp) ≤ 2^240 * ((2:ℝ)^20) ^ (46 * Aexp) := by
          gcongr; exact hA
      _ = 2^(240 + 20 * (46*Aexp)) := by rw [pow_add, ← pow_mul]
      _ ≤ _ := tp (by norm_num [Aexp])

end Col3Witness

example : col3 8192 := Col3Witness.col3_8192

end COLTable

end EGTest.Params
