module

public import EG.Lib.Found.Gamma
public import EG.Defs.Probe.P3B.TowerFns
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Real-analysis lemmas for the tower facts (manuscript s6, text before s6:thmCONC)

Unit P3B (probe P-3, part 2), proof round 1. Used by `EG.Proof.Chain.ConcTower`
((s6:eqTowerHalf), (s6:eqTowerEnd), `k_* ≥ 6`).

The manuscript uses that `t ↦ (2 log t + 6)/t`, `(7 + 2 log t)/t`, `(2 log t + 5)/t^{1/2}` are
decreasing for `t ≥ 4`. Instead of monotonicity we use the growth lemma `grow`: if
`K(αw + β) ≤ 2^w` and `2Kα ≤ 2^w` (with `Kα ≥ 0`), then `K(αX + β) ≤ 2^X` for every `X ≥ w`
(since `2^{X-w} ≥ 1 + (X-w)/2`). The "middle inequalities" of the manuscript are the hypotheses
of `grow` at the base point.
-/

public section

namespace EG.Chain

open Real

/-- `2^t ≥ 1 + t/2` for `t ≥ 0` (`2^t = e^{t log 2}`, `log 2 > 1/2`). -/
theorem one_add_half_le_two_rpow {t : ℝ} (ht : 0 ≤ t) : 1 + t / 2 ≤ (2 : ℝ) ^ t := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have h1 := Real.add_one_le_exp (Real.log 2 * t)
  have h2 := Real.log_two_gt_d9
  nlinarith

/-- The growth lemma: `K(αw + β) ≤ 2^w`, `2Kα ≤ 2^w`, `Kα ≥ 0`, `w ≤ X` give
`K(αX + β) ≤ 2^X`. -/
theorem grow {K α β w X : ℝ} (_hKα : 0 ≤ K * α) (hwX : w ≤ X)
    (h1 : K * (α * w + β) ≤ (2 : ℝ) ^ w) (h2 : 2 * (K * α) ≤ (2 : ℝ) ^ w) :
    K * (α * X + β) ≤ (2 : ℝ) ^ X := by
  have e : (2 : ℝ) ^ X = (2 : ℝ) ^ w * (2 : ℝ) ^ (X - w) := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  have h3 := one_add_half_le_two_rpow (sub_nonneg.2 hwX)
  have hw : 0 < (2 : ℝ) ^ w := by positivity
  rw [e]
  have h4 := mul_le_mul_of_nonneg_left h3 hw.le
  have h5 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hwX)
  nlinarith

theorem two_rpow_add (a b : ℝ) : (2 : ℝ) ^ (a + b) = (2 : ℝ) ^ a * (2 : ℝ) ^ b :=
  Real.rpow_add (by norm_num) a b

/-- `(y^{1/2})^2 = y` for `y ≥ 0`. -/
theorem rpow_half_sq {y : ℝ} (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 2)) ^ 2 = y := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hy]

theorem rpow_half_nonneg (y : ℝ) : 0 ≤ y ^ ((1 : ℝ) / 2) := by
  rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_nonneg y

/-- `(2^X)^{1/2} = 2^{X/2}`. -/
theorem two_rpow_rpow_half (X : ℝ) : ((2 : ℝ) ^ X) ^ ((1 : ℝ) / 2) = (2 : ℝ) ^ (X / 2) := by
  rw [← Real.rpow_mul (by norm_num)]; ring_nf

/-- `2^{w} = (2^{w/2})^2`. -/
theorem two_rpow_eq_sq_half (w : ℝ) : (2 : ℝ) ^ w = ((2 : ℝ) ^ (w / 2)) ^ 2 := by
  rw [sq, ← two_rpow_add]; ring_nf

/-- The core of (s6:eqTowerHalf): with `v = log y ≥ 2^8`, `y = 2^v ≥ 2^{14} A v^3` and
`x ≥ 2^{y/A}` (`A = 105`): `y(2 log x + 6) ≤ x`, `2 log y (7 + 2 log log x) ≤ log x` and
`2 y^{1/2}(2 log x + 5) ≤ x^{1/2}`. -/
theorem half_core {x y : ℝ} (hy : 0 < y) (hv8 : (2 : ℝ) ^ 8 ≤ logb 2 y)
    (hvb : (2 : ℝ) ^ 14 * 105 * (logb 2 y) ^ 3 ≤ y) (hx : (2 : ℝ) ^ (y / 105) ≤ x) :
    y * (2 * logb 2 x + 6) ≤ x ∧
    2 * logb 2 y * (7 + 2 * logb 2 (logb 2 x)) ≤ logb 2 x ∧
    2 * y ^ ((1 : ℝ) / 2) * (2 * logb 2 x + 5) ≤ x ^ ((1 : ℝ) / 2) := by
  set v := logb 2 y with hvdef
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv8
  have hyv : (2 : ℝ) ^ v = y := Real.rpow_logb (by norm_num) (by norm_num) hy
  have hv3 : (2 : ℝ) ^ 24 ≤ v ^ 3 := by
    have : ((2 : ℝ) ^ 8) ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ (by norm_num) hv8 3
    nlinarith
  norm_num at hv8 hvb hv3
  have hvv : v ≤ v ^ 3 := by
    have h1 : 1 ≤ v ^ 2 := by nlinarith
    have h2 : v * 1 ≤ v * v ^ 2 := mul_le_mul_of_nonneg_left h1 hv0.le
    nlinarith
  have hy1 : 1 ≤ y := by nlinarith
  -- `Q = 2^{y/210} ≥ 16 y^2`
  have hexp : 4 + 2 * v ≤ y / 210 := by nlinarith
  have hQ : 16 * y ^ 2 ≤ (2 : ℝ) ^ (y / 210) := by
    have e : (2 : ℝ) ^ (4 + 2 * v) = 16 * y ^ 2 := by
      rw [two_rpow_add, show (2 : ℝ) * v = v + v by ring, two_rpow_add, hyv]
      norm_num; ring
    rw [← e]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  set Q := (2 : ℝ) ^ (y / 210) with hQdef
  have hQ2 : (2 : ℝ) ^ (y / 105) = Q ^ 2 := by
    rw [hQdef, two_rpow_eq_sq_half]; ring_nf
  have hQ0 : 0 ≤ Q := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  set X := logb 2 x with hXdef
  have hxX : (2 : ℝ) ^ X = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  have hXw : y / 105 ≤ X := (Real.le_logb_iff_rpow_le (by norm_num) hx0).2 hx
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    rw [← hxX]
    have hQQ : (16 * y ^ 2) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by positivity) hQ 2
    have hy2 : 1 ≤ y ^ 2 := by nlinarith
    have hy4 : y ^ 2 ≤ (y ^ 2) ^ 2 := by nlinarith
    refine grow (by positivity) hXw ?_ ?_
    · rw [hQ2]; nlinarith
    · rw [hQ2]; nlinarith
  · -- (b)
    have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXw
    set M := logb 2 X with hMdef
    have hXM : (2 : ℝ) ^ M = X := Real.rpow_logb (by norm_num) (by norm_num) hX0
    have hyA : 0 < y / 105 := by positivity
    set w := logb 2 (y / 105) with hwdef
    have hw2 : (2 : ℝ) ^ w = y / 105 := Real.rpow_logb (by norm_num) (by norm_num) hyA
    have hwM : w ≤ M := Real.logb_le_logb_of_le (by norm_num) hyA hXw
    have hwv : w ≤ v := Real.logb_le_logb_of_le (by norm_num) hyA (by linarith)
    have hv2 : 256 * v ≤ v ^ 2 := by nlinarith
    have hv3' : 256 * v ^ 2 ≤ v ^ 3 := by nlinarith
    have hA : 16384 * v ^ 3 ≤ y / 105 := by nlinarith
    have key := grow (K := 2 * v) (α := 2) (β := 7) (by positivity) hwM
      (by rw [hw2]; nlinarith) (by rw [hw2]; nlinarith)
    rw [hXM] at key
    linarith
  · -- (c)
    set s := y ^ ((1 : ℝ) / 2) with hsdef
    have hs0 : 0 ≤ s := rpow_half_nonneg y
    have hs2 : s ^ 2 = y := rpow_half_sq hy.le
    have hs1 : 1 ≤ s := by nlinarith
    have hsy : s ≤ y := by nlinarith
    rw [← hxX, two_rpow_rpow_half]
    have hXw' : y / 210 ≤ X / 2 := by linarith
    have key := grow (K := 2 * s) (α := 4) (β := 5) (by positivity) hXw'
      (by rw [← hQdef]; nlinarith) (by rw [← hQdef]; nlinarith)
    linarith

/-- The core of (s6:eqTowerEnd), case `log d > 𝖳_{k_*}`: for `t = log D ≥ 2^8` with
`2^t ≥ 2^{14} A t^3`, `t' = log t ≥ 2^8` with `2^{t'} ≥ 2^{14} A t'^3`, and `x ≥ D`:
`t(2 log x + 6) ≤ x`, `t'(7 + 2 log log x) ≤ log x`, `t^{1/2}(2 log x + 5) ≤ x^{1/2}`. -/
theorem end_core {D x : ℝ} (hD : 0 < D) (ht8 : (2 : ℝ) ^ 8 ≤ logb 2 D)
    (htb : (2 : ℝ) ^ 14 * 105 * (logb 2 D) ^ 3 ≤ D)
    (ht'8 : (2 : ℝ) ^ 8 ≤ logb 2 (logb 2 D))
    (ht'b : (2 : ℝ) ^ 14 * 105 * (logb 2 (logb 2 D)) ^ 3 ≤ logb 2 D) (hx : D ≤ x) :
    logb 2 D * (2 * logb 2 x + 6) ≤ x ∧
    logb 2 (logb 2 D) * (7 + 2 * logb 2 (logb 2 x)) ≤ logb 2 x ∧
    (logb 2 D) ^ ((1 : ℝ) / 2) * (2 * logb 2 x + 5) ≤ x ^ ((1 : ℝ) / 2) := by
  set t := logb 2 D with htdef
  set t' := logb 2 t with ht'def
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht8
  have ht'0 : 0 < t' := lt_of_lt_of_le (by norm_num) ht'8
  have hDt : (2 : ℝ) ^ t = D := Real.rpow_logb (by norm_num) (by norm_num) hD
  have htt' : (2 : ℝ) ^ t' = t := Real.rpow_logb (by norm_num) (by norm_num) ht0
  have hx0 : 0 < x := lt_of_lt_of_le hD hx
  set X := logb 2 x with hXdef
  have hxX : (2 : ℝ) ^ X = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  have htX : t ≤ X := Real.logb_le_logb_of_le (by norm_num) hD hx
  have ht3 : (2 : ℝ) ^ 24 ≤ t ^ 3 := by
    have : ((2 : ℝ) ^ 8) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht8 3
    nlinarith
  have ht'3 : (2 : ℝ) ^ 24 ≤ t' ^ 3 := by
    have : ((2 : ℝ) ^ 8) ^ 3 ≤ t' ^ 3 := pow_le_pow_left₀ (by norm_num) ht'8 3
    nlinarith
  norm_num at ht8 htb ht'8 ht'b
  have ht2 : 256 * t ≤ t ^ 2 := by nlinarith
  have ht3' : 256 * t ^ 2 ≤ t ^ 3 := by nlinarith
  have ht'2 : 256 * t' ≤ t' ^ 2 := by nlinarith
  have ht'3' : 256 * t' ^ 2 ≤ t' ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← hxX]
    refine grow (by positivity) htX ?_ ?_
    · rw [hDt]; nlinarith
    · rw [hDt]; nlinarith
  · have hX0 : 0 < X := lt_of_lt_of_le ht0 htX
    set M := logb 2 X with hMdef
    have hXM : (2 : ℝ) ^ M = X := Real.rpow_logb (by norm_num) (by norm_num) hX0
    have ht'M : t' ≤ M := Real.logb_le_logb_of_le (by norm_num) ht0 htX
    have key := grow (K := t') (α := 2) (β := 7) (by positivity) ht'M
      (by rw [htt']; nlinarith) (by rw [htt']; nlinarith)
    rw [hXM] at key
    linarith
  · set s := t ^ ((1 : ℝ) / 2) with hsdef
    have hs0 : 0 ≤ s := rpow_half_nonneg t
    have hs2 : s ^ 2 = t := rpow_half_sq ht0.le
    rw [← hxX, two_rpow_rpow_half]
    have hXw' : t / 2 ≤ X / 2 := by linarith
    set q := (2 : ℝ) ^ (t / 2) with hqdef
    have hq0 : 0 ≤ q := by positivity
    have hq2 : q ^ 2 = D := by rw [hqdef, ← two_rpow_eq_sq_half, hDt]
    have hc : (4 * (t / 2) + 5) ^ 2 ≤ 49 * t ^ 2 := by nlinarith
    have hb1 : s * (4 * (t / 2) + 5) ≤ q := by
      have h : (s * (4 * (t / 2) + 5)) ^ 2 ≤ q ^ 2 := by
        rw [hq2, mul_pow, hs2]
        have := mul_le_mul_of_nonneg_left hc ht0.le
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) hq0 (by norm_num)).1 h
    have hb2 : 2 * (s * 4) ≤ q := by
      have h : (2 * (s * 4)) ^ 2 ≤ q ^ 2 := by
        rw [hq2]
        have : (2 * (s * 4)) ^ 2 = 64 * s ^ 2 := by ring
        rw [this, hs2]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) hq0 (by norm_num)).1 h
    have key := grow (K := s) (α := 4) (β := 5) (by positivity) hXw' hb1 hb2
    linarith

/-- `𝖳_4 = 65536`. -/
theorem tower_four : tower 4 = 65536 := by
  have h1 : tower 1 = 2 := by rw [tower_succ]; simp [tower]
  have h2 : tower 2 = 4 := by
    rw [tower_succ, h1]; norm_num
  have h3 : tower 3 = 16 := by
    rw [tower_succ, h2]; norm_num
  rw [tower_succ, h3]; norm_num

end EG.Chain
