module

public import EG.Defs.Vortex

/-!
# API for the vortex-run parameters and size predicates (manuscript s4)

Elementary lemmas about the definitions of `EG/Defs/Vortex.lean`.

* `L`: `L_eq`, `L_nonneg`, `L_pow`;
* the size predicates: `TPVSize.cond_i`, `.cond_ii`, `.cond_iii` (size condition (iii),
  "a consequence of (i)"), `.cond_iv`, `.one_lt`; the same for `PVSize` and `VXSize`;
* the numbers of steps: `two_pow_floor_logb_le`, `lt_two_pow_floor_logb_succ` (the floor of a
  base-2 logarithm), and the manuscript's parameter bounds (s4:eqTPVJ), (s4:eqPVJ):
  `tpvJ_bounds` (`6·2^J ≤ L < 12·2^J`), `pvJ_bounds` (`8·2^J ≤ L < 16·2^J`), `vxJ_bounds`,
  `one_le_tpvJ`, `one_le_pvJ`, `one_le_vxJ`, `tpvJ_le_logb`, `pvJ_le_logb`, `vxJ_le_logb`,
  `vxJ_eq_tpvJ`;
* `pvM`, `pvB`: the ceiling bounds `le_pvM`, `pvM_lt`, `le_pvB`, `pvB_lt`;
* exponential tails: `exp_neg_le_two_rpow_neg`, `two_pow_mul_exp_neg_le`.
-/

public section


namespace EG.Vortex

open Real

theorem L_eq (N : ℕ) : L N = logb 2 (N : ℝ) := rfl

theorem L_nonneg (N : ℕ) : 0 ≤ L N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [L]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

/-- `L (2^k) = k`. -/
theorem L_pow (k : ℕ) : L (2 ^ k) = k := by
  rw [L]; push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- `L N > 0` forces `N ≥ 2`. -/
theorem one_lt_of_L_pos {N : ℕ} (h : 0 < L N) : 1 < N := by
  rcases Nat.lt_or_ge 1 N with h' | h'
  · exact h'
  · exfalso
    obtain rfl | rfl : N = 0 ∨ N = 1 := by omega
    all_goals simp [L] at h

/-! ## Size predicates -/

theorem TPVSize.cond_i {N : ℕ} (h : TPVSize N) : (2 : ℝ) ^ 10 ≤ L N := h.1
theorem TPVSize.cond_ii {N : ℕ} (h : TPVSize N) : L N ^ 3 ≤ (N : ℝ) := h.2.1
theorem TPVSize.cond_iv {N : ℕ} (h : TPVSize N) : etaTPV N ≤ 1 / 100 := h.2.2
/-- [s4:lemTPV] size condition "(iii) `4·48 ≤ L` (a consequence of (i))". -/
theorem TPVSize.cond_iii {N : ℕ} (h : TPVSize N) : (4 * 48 : ℝ) ≤ L N := by
  have := h.cond_i; norm_num at this ⊢; linarith
theorem TPVSize.one_lt {N : ℕ} (h : TPVSize N) : 1 < N :=
  one_lt_of_L_pos (lt_of_lt_of_le (by norm_num) h.cond_i)

theorem PVSize.cond_i {N : ℕ} (h : PVSize N) : (2 : ℝ) ^ 10 ≤ L N := h.1
theorem PVSize.cond_ii {N : ℕ} (h : PVSize N) : L N ^ 3 ≤ (N : ℝ) := h.2.1
theorem PVSize.cond_iv {N : ℕ} (h : PVSize N) : etaPV N ≤ 1 / 100 := h.2.2
/-- [s4:lemPV] size condition "(iii) `4·64 ≤ L` (a consequence of (i))". -/
theorem PVSize.cond_iii {N : ℕ} (h : PVSize N) : (4 * 64 : ℝ) ≤ L N := by
  have := h.cond_i; norm_num at this ⊢; linarith
theorem PVSize.one_lt {N : ℕ} (h : PVSize N) : 1 < N :=
  one_lt_of_L_pos (lt_of_lt_of_le (by norm_num) h.cond_i)

theorem VXSize.cond_i {N : ℕ} (h : VXSize N) : (2 : ℝ) ^ 10 ≤ L N := h.1
theorem VXSize.cond_ii {N : ℕ} (h : VXSize N) : L N ^ 3 ≤ (N : ℝ) := h.2.1
theorem VXSize.cond_iv {N : ℕ} (h : VXSize N) : etaVX N ≤ 1 / 100 := h.2.2
/-- [s4:thmVXp] size condition "(iii) `4·13 ≤ L` (a consequence of (i))". -/
theorem VXSize.cond_iii {N : ℕ} (h : VXSize N) : (4 * 13 : ℝ) ≤ L N := by
  have := h.cond_i; norm_num at this ⊢; linarith
theorem VXSize.one_lt {N : ℕ} (h : VXSize N) : 1 < N :=
  one_lt_of_L_pos (lt_of_lt_of_le (by norm_num) h.cond_i)

/-! ## Floors of base-2 logarithms and the numbers of steps -/

/-- `2^{⌊log₂ x⌋} ≤ x` for `x ≥ 1`. -/
theorem two_pow_floor_logb_le {x : ℝ} (hx : 1 ≤ x) : (2 : ℝ) ^ ⌊logb 2 x⌋₊ ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hl : 0 ≤ logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hk : (⌊logb 2 x⌋₊ : ℝ) ≤ logb 2 x := Nat.floor_le hl
  rw [← Real.rpow_natCast]
  exact (Real.le_logb_iff_rpow_le (by norm_num) hx0).1 hk

/-- `x < 2^{⌊log₂ x⌋ + 1}` for `x > 0`. -/
theorem lt_two_pow_floor_logb_succ {x : ℝ} (hx : 0 < x) :
    x < (2 : ℝ) ^ (⌊logb 2 x⌋₊ + 1) := by
  have hk : logb 2 x < ((⌊logb 2 x⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  rw [← Real.rpow_natCast]
  exact (Real.logb_lt_iff_lt_rpow (by norm_num) hx).1 hk

/-- `⌊log₂ x⌋ ≥ 1` for `x ≥ 2`. -/
theorem one_le_floor_logb {x : ℝ} (hx : 2 ≤ x) : 1 ≤ ⌊logb 2 x⌋₊ := by
  apply Nat.le_floor
  rw [Nat.cast_one, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
  simpa using hx

/-- A generic form of (s4:eqTPVJ)/(s4:eqPVJ): for `c > 0` and `L ≥ c`,
`c·2^J ≤ L < 2c·2^J` with `J = ⌊log₂(L/c)⌋`. -/
theorem floor_logb_div_bounds {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    c * 2 ^ ⌊logb 2 (x / c)⌋₊ ≤ x ∧ x < 2 * c * 2 ^ ⌊logb 2 (x / c)⌋₊ := by
  have h1 : 1 ≤ x / c := by rw [le_div_iff₀ hc]; linarith
  have a := two_pow_floor_logb_le h1
  have b := lt_two_pow_floor_logb_succ (lt_of_lt_of_le one_pos h1)
  rw [pow_succ] at b
  constructor
  · rw [le_div_iff₀ hc] at a; linarith
  · rw [div_lt_iff₀ hc] at b; linarith

theorem floor_logb_div_le_logb {c x : ℝ} (hc : 1 ≤ c) (hx : c ≤ x) :
    (⌊logb 2 (x / c)⌋₊ : ℝ) ≤ logb 2 x := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have h1 : 1 ≤ x / c := by rw [le_div_iff₀ hc0]; linarith
  refine le_trans (Nat.floor_le (Real.logb_nonneg (by norm_num) h1)) ?_
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  exact div_le_self (by linarith) hc

/-- [s4:lemTPV] (s4:eqTPVJ) "By the definition of `J`, `6·2^J ≤ L < 12·2^J`" (for `L ≥ 6`). -/
theorem tpvJ_bounds {N : ℕ} (h : 6 ≤ L N) :
    6 * (2 : ℝ) ^ tpvJ N ≤ L N ∧ L N < 12 * (2 : ℝ) ^ tpvJ N := by
  have := floor_logb_div_bounds (by norm_num : (0 : ℝ) < 6) h
  rw [tpvJ]; constructor
  · exact this.1
  · linarith [this.2]

/-- [s4:lemPV] (s4:eqPVJ) "By the definition of `J`, `8·2^J ≤ L < 16·2^J`" (for `L ≥ 8`). -/
theorem pvJ_bounds {N : ℕ} (h : 8 ≤ L N) :
    8 * (2 : ℝ) ^ pvJ N ≤ L N ∧ L N < 16 * (2 : ℝ) ^ pvJ N := by
  have := floor_logb_div_bounds (by norm_num : (0 : ℝ) < 8) h
  rw [pvJ]; constructor
  · exact this.1
  · linarith [this.2]

theorem vxJ_eq_tpvJ (N : ℕ) : vxJ N = tpvJ N := rfl

/-- [s4:thmVXp] (proof, "Parameters") "By the definition of `J`, `6·2^J ≤ L < 12·2^J`". -/
theorem vxJ_bounds {N : ℕ} (h : 6 ≤ L N) :
    6 * (2 : ℝ) ^ vxJ N ≤ L N ∧ L N < 12 * (2 : ℝ) ^ vxJ N := tpvJ_bounds h

theorem one_le_tpvJ {N : ℕ} (h : 12 ≤ L N) : 1 ≤ tpvJ N :=
  one_le_floor_logb (by rw [le_div_iff₀ (by norm_num)]; linarith)

theorem one_le_pvJ {N : ℕ} (h : 16 ≤ L N) : 1 ≤ pvJ N :=
  one_le_floor_logb (by rw [le_div_iff₀ (by norm_num)]; linarith)

theorem one_le_vxJ {N : ℕ} (h : 12 ≤ L N) : 1 ≤ vxJ N := one_le_tpvJ h

theorem tpvJ_le_logb {N : ℕ} (h : 6 ≤ L N) : (tpvJ N : ℝ) ≤ logb 2 (L N) :=
  floor_logb_div_le_logb (by norm_num) h

theorem pvJ_le_logb {N : ℕ} (h : 8 ≤ L N) : (pvJ N : ℝ) ≤ logb 2 (L N) :=
  floor_logb_div_le_logb (by norm_num) h

theorem vxJ_le_logb {N : ℕ} (h : 6 ≤ L N) : (vxJ N : ℝ) ≤ logb 2 (L N) := tpvJ_le_logb h

/-! ## `m` and `b` of Lemma PV -/

theorem le_pvM (N : ℕ) : L N ^ 6 ≤ pvM N := Nat.le_ceil _

theorem pvM_lt (N : ℕ) : (pvM N : ℝ) < L N ^ 6 + 1 :=
  Nat.ceil_lt_add_one (by have := L_nonneg N; positivity)

theorem le_pvB (N : ℕ) : (2 : ℝ) ^ 7 * L N ^ 2 * (pvM N : ℝ) ≤ pvB N := Nat.le_ceil _

theorem pvB_lt (N : ℕ) : (pvB N : ℝ) < (2 : ℝ) ^ 7 * L N ^ 2 * (pvM N : ℝ) + 1 :=
  Nat.ceil_lt_add_one (by have := L_nonneg N; positivity)

/-! ## Exponential tails (used to evaluate the `η`'s) -/

/-- `e^{-x} ≤ 2^{-x}` for `x ≥ 0`. -/
theorem exp_neg_le_two_rpow_neg {x : ℝ} (hx : 0 ≤ x) : exp (-x) ≤ (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  nlinarith

/-- `2^k e^{-x} ≤ 2^{-y}` whenever `k + y ≤ x` and `x ≥ 0`. -/
theorem two_pow_mul_exp_neg_le (k : ℕ) {x y : ℝ} (hx : 0 ≤ x) (h : (k : ℝ) + y ≤ x) :
    (2 : ℝ) ^ k * exp (-x) ≤ (2 : ℝ) ^ (-y) :=
  calc (2 : ℝ) ^ k * exp (-x) ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ (-x) := by
        gcongr; exact exp_neg_le_two_rpow_neg hx
    _ = (2 : ℝ) ^ ((k : ℝ) + -x) := by rw [Real.rpow_add two_pos, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (-y) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end EG.Vortex
