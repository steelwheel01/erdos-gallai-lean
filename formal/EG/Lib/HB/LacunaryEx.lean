module

public import EG.Lib.HB.Lacunary
public import EG.Lib.HB.Psi

/-!
# Tower-lacunary sums, the examples of part (iv) (manuscript s2:lemLacunary (iv))

Helper lemmas for `EG.Todo.LacunaryExamples` (unit P3-s2). Proof of (iv): "Let `x ≥ x_0` and
`y ≥ 2^{x/A}`, and put `μ := log x ≥ log log D_*`. By Γ1 (a), (b) at `μ`, `μ ≥ 2^8` and
`x = 2^μ ≥ 2^{14} A μ^3`; hence `x ≥ 2^{256}`, `x/A ≥ 101 log x`, `x ≥ 2A log x`,
`x ≥ A log² x/4` and `x/A ≥ 2^{12}` … Then `log y ≥ x/A`, and `2^{x/A} ≥ x^{101}` …; so
`y ≥ x^{101} ≥ 2^{32}`."
* `LacX x`: the facts at `x ≥ x_0` (`LacX.of_gamma`);
* `hypH_inv_logb`, `antitoneOn_inv_logb`: the example `F(x) = 1/log x`.
-/

public section

namespace EG.HB

open Real

/-- The facts at a point `x ≥ x_0 = log D_*` (proof of s2:lemLacunary (iv)). -/
structure LacX (x : ℝ) : Prop where
  pos : 0 < x
  mu_ge : 256 ≤ logb 2 x
  cube_le : (2 : ℝ) ^ 14 * 105 * logb 2 x ^ 3 ≤ x

theorem LacX.of_gamma {Dstar x : ℝ} (hD : Gamma1core Dstar) (hx : logb 2 Dstar ≤ x) : LacX x := by
  have hI := hD.items_logb_of_le hx
  have hxpos : 0 < x := lt_of_lt_of_le (zero_lt_one.trans hD.one_lt_logb) hx
  have hxμ : (2 : ℝ) ^ logb 2 x = x := Real.rpow_logb (by norm_num) (by norm_num) hxpos
  refine ⟨hxpos, ?_, ?_⟩
  · have := hI.a; unfold Gamma1a at this; norm_num at this; linarith
  · have := hI.b; unfold Gamma1b at this; rw [hxμ, cast_Aexp] at this; exact this

namespace LacX

variable {x : ℝ} (h : LacX x)
include h

theorem two_rpow_logb : (2 : ℝ) ^ logb 2 x = x := Real.rpow_logb (by norm_num) (by norm_num) h.pos

/-- `a + b log x ≤ x` for `a + b ≤ 2^{14}·105·256²` (from `x ≥ 2^{14} A μ³`, `μ ≥ 256`). -/
theorem lin_le {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b ≤ 2 ^ 14 * 105 * 256 ^ 2) :
    a + b * logb 2 x ≤ x := by
  have h1 := h.cube_le
  have h2 := h.mu_ge
  set μ := logb 2 x
  have hμ2 : (256 : ℝ) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
  have : (a + b) * μ ≤ 2 ^ 14 * 105 * μ ^ 3 := by
    have e : μ ^ 3 = μ ^ 2 * μ := by ring
    rw [e]
    have hμ0 : 0 ≤ μ := by linarith
    nlinarith
  nlinarith

/-- `x ≥ 2A log x`. -/
theorem twoA_logb_le : 2 * 105 * logb 2 x ≤ x := by
  have := h.lin_le (a := 0) (b := 210) le_rfl (by norm_num) (by norm_num); linarith

/-- `x/A ≥ 101 log x`. -/
theorem logb_mul_le : 101 * logb 2 x ≤ x / 105 := by
  rw [le_div_iff₀ (by norm_num)]
  have := h.lin_le (a := 0) (b := 101 * 105) le_rfl (by norm_num) (by norm_num); linarith

/-- `x ≥ A log² x / 4`. -/
theorem logb_sq_le : 105 * logb 2 x ^ 2 / 4 ≤ x := by
  have h1 := h.cube_le
  have h2 := h.mu_ge
  have : logb 2 x ^ 2 ≤ logb 2 x ^ 3 := by
    have e : logb 2 x ^ 3 = logb 2 x ^ 2 * logb 2 x := by ring
    rw [e]; nlinarith [sq_nonneg (logb 2 x)]
  nlinarith [sq_nonneg (logb 2 x)]

theorem one_lt : 1 < x := by
  have := h.lin_le (a := 1) (b := 0) (by norm_num) le_rfl (by norm_num)
  have := h.twoA_logb_le; nlinarith [h.mu_ge]

theorem two_le : 2 ≤ x := by
  have := h.lin_le (a := 2) (b := 0) (by norm_num) le_rfl (by norm_num); linarith

theorem logb_pos : 0 < logb 2 x := by linarith [h.mu_ge]

/-- For `y ≥ 2^{x/A}`: `log y ≥ x/A`. -/
theorem le_logb_of_le {y : ℝ} (hy : (2 : ℝ) ^ (x / 105) ≤ y) : x / 105 ≤ logb 2 y := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  rw [Real.le_logb_iff_rpow_le (by norm_num) hy0]; exact hy

end LacX

/-- (iv): (H) for `F(x) = 1/log x`: "`F(y) = 1/log y ≤ A/x ≤ 1/(2 log x) = F(x)/2`, as
`x ≥ 2A log x`". -/
theorem hypH_inv_logb {Dstar : ℝ} (hD : Gamma1core Dstar) :
    HypH (logb 2 Dstar) (fun x => 1 / logb 2 x) := by
  intro x y hx _ hxy
  have h := LacX.of_gamma hD hx
  rw [cast_Aexp] at hxy
  have h1 := h.le_logb_of_le hxy
  have h2 := h.twoA_logb_le
  have hL := h.logb_pos
  have hLy : 0 < logb 2 y := lt_of_lt_of_le (by linarith) h1
  simp only
  rw [div_div, div_le_div_iff₀ hLy (by positivity)]
  have : 2 * logb 2 x ≤ x / 105 := by rw [le_div_iff₀ (by norm_num)]; linarith
  linarith

/-- (iv): `F(x) = 1/log x` is non-increasing on `[x_0,∞)`. -/
theorem antitoneOn_inv_logb {Dstar : ℝ} (hD : Gamma1core Dstar) :
    AntitoneOn (fun x : ℝ => 1 / logb 2 x) (Set.Ici (logb 2 Dstar)) := by
  intro x hx y _ hxy
  have h := LacX.of_gamma hD hx
  have hy0 : 0 < y := lt_of_lt_of_le h.pos hxy
  have hL := h.logb_pos
  have hLy : logb 2 x ≤ logb 2 y := Real.logb_le_logb_of_le (by norm_num) h.pos hxy
  simp only
  exact one_div_le_one_div_of_le hL hLy

theorem inv_logb_nonneg {Dstar : ℝ} (hD : Gamma1core Dstar) :
    ∀ x : ℝ, logb 2 Dstar ≤ x → 0 ≤ 1 / logb 2 x := by
  intro x hx
  exact (one_div_pos.2 (LacX.of_gamma hD hx).logb_pos).le

/-! ### Growth of `2^t` -/

/-- `2^t ≥ 1 + t/2` for `t ≥ 0` (`2^t = e^{t ln 2}`, `ln 2 > 1/2`). -/
theorem one_add_half_le_two_rpow' {t : ℝ} (ht : 0 ≤ t) : 1 + t / 2 ≤ (2 : ℝ) ^ t := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have h1 := Real.add_one_le_exp (Real.log 2 * t)
  have h2 := Real.log_two_gt_d9
  nlinarith

/-- Shifted growth: `2^t ≥ 2^{t_0} (1 + (t - t_0)/2)` for `t ≥ t_0`. -/
theorem two_rpow_ge_shift {t t0 : ℝ} (ht : t0 ≤ t) :
    (2 : ℝ) ^ t0 * (1 + (t - t0) / 2) ≤ (2 : ℝ) ^ t := by
  have h := one_add_half_le_two_rpow' (t := t - t0) (by linarith)
  have e : (2 : ℝ) ^ t = (2 : ℝ) ^ t0 * (2 : ℝ) ^ (t - t0) := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem two_rpow_mul_two (a : ℝ) : (2 : ℝ) ^ a * 2 = (2 : ℝ) ^ (a + 1) := by
  rw [Real.rpow_add (by norm_num), Real.rpow_one]

/-- `x^r = 2^{(log x) r}` for `x > 0`. -/
theorem rpow_eq_two_rpow {x : ℝ} (hx : 0 < x) (r : ℝ) : x ^ r = (2 : ℝ) ^ (logb 2 x * r) := by
  conv_lhs => rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hx]
  rw [← Real.rpow_mul (by norm_num)]

/-- For `x ≥ x_0` and `y ≥ 2^{x/A}` (with `x_0 ≤ x`): `log y ≥ 101 log x`, `log y ≥ 2^{12}`. -/
theorem LacX.logb_y {x y : ℝ} (h : LacX x) (hy : (2 : ℝ) ^ (x / 105) ≤ y) :
    101 * logb 2 x ≤ logb 2 y ∧ (2 : ℝ) ^ 12 ≤ logb 2 y ∧ 0 < y := by
  have h1 := h.le_logb_of_le hy
  have h2 := h.logb_mul_le
  have h3 : (2 : ℝ) ^ 12 * 105 ≤ x := by
    have := h.lin_le (a := 2 ^ 12 * 105) (b := 0) (by norm_num) le_rfl (by norm_num); linarith
  refine ⟨h2.trans h1, le_trans ?_ h1, lt_of_lt_of_le (by positivity) hy⟩
  rw [le_div_iff₀ (by norm_num)]; exact h3

/-! ### (iv): `F(x) = x^{-a}` -/

theorem hypH_rpow_neg {Dstar a : ℝ} (hD : Gamma1core Dstar) (ha : 1 / 100 ≤ a) :
    HypH (logb 2 Dstar) (fun x => x ^ (-a)) := by
  intro x y hx _ hxy
  have h := LacX.of_gamma hD hx
  rw [cast_Aexp] at hxy
  obtain ⟨hu, -, hy0⟩ := h.logb_y hxy
  have hv := h.mu_ge
  simp only
  rw [rpow_eq_two_rpow hy0, rpow_eq_two_rpow h.pos, le_div_iff₀ (by norm_num),
    two_rpow_mul_two]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

theorem antitoneOn_rpow_neg {Dstar a : ℝ} (hD : Gamma1core Dstar) (ha : 1 / 100 ≤ a) :
    AntitoneOn (fun x : ℝ => x ^ (-a)) (Set.Ici (logb 2 Dstar)) := by
  intro x hx y _ hxy
  exact Real.rpow_le_rpow_of_nonpos (LacX.of_gamma hD hx).pos hxy (by linarith)

theorem rpow_neg_nonneg' {Dstar a : ℝ} (hD : Gamma1core Dstar) :
    ∀ x : ℝ, logb 2 Dstar ≤ x → 0 ≤ x ^ (-a) :=
  fun x hx => Real.rpow_nonneg (LacX.of_gamma hD hx).pos.le _

/-! ### (iv): `F(x) = (95 log x + 8) x^{-b}` -/

/-- `95 u + 8 ≤ 2^{u/2}` for `u ≥ 32`. -/
theorem lin95_le {u : ℝ} (hu : 32 ≤ u) : 95 * u + 8 ≤ (2 : ℝ) ^ (u / 2) := by
  have h := two_rpow_ge_shift (t := u / 2) (t0 := 16) (by linarith)
  have e : (2 : ℝ) ^ (16 : ℝ) = 65536 := by norm_num
  rw [e] at h
  nlinarith

theorem hypH_log95 {Dstar b : ℝ} (hD : Gamma1core Dstar) (hb : 1 ≤ b) :
    HypH (logb 2 Dstar) (fun x => (95 * logb 2 x + 8) * x ^ (-b)) := by
  intro x y hx _ hxy
  have h := LacX.of_gamma hD hx
  rw [cast_Aexp] at hxy
  obtain ⟨hu, hu12, hy0⟩ := h.logb_y hxy
  have hv := h.mu_ge
  set u := logb 2 y
  set v := logb 2 x
  simp only
  rw [rpow_eq_two_rpow hy0, rpow_eq_two_rpow h.pos]
  have h1 : 95 * u + 8 ≤ (2 : ℝ) ^ (u / 2) := lin95_le (by linarith)
  have h2 : (95 * u + 8) * (2 : ℝ) ^ (u * -b) ≤ (2 : ℝ) ^ (u / 2) * (2 : ℝ) ^ (u * -b) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : (2 : ℝ) ^ (u / 2) * (2 : ℝ) ^ (u * -b) ≤ (2 : ℝ) ^ (v * -b) / 2 := by
    rw [← Real.rpow_add (by norm_num), le_div_iff₀ (by norm_num), two_rpow_mul_two]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have h4 : (2 : ℝ) ^ (v * -b) / 2 ≤ (95 * v + 8) * (2 : ℝ) ^ (v * -b) / 2 := by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (v * -b) := by positivity
    have : 1 ≤ 95 * v + 8 := by linarith
    nlinarith
  linarith

theorem antitoneOn_log95 {Dstar b : ℝ} (hD : Gamma1core Dstar) (hb : 1 ≤ b) :
    AntitoneOn (fun x : ℝ => (95 * logb 2 x + 8) * x ^ (-b)) (Set.Ici (logb 2 Dstar)) := by
  intro x hx y _ hxy
  have h := LacX.of_gamma hD hx
  have hx0 := h.pos
  have hv := h.mu_ge
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  set t := y / x with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hx0]; linarith
  have hyt : y = t * x := by rw [ht]; field_simp
  simp only
  rw [hyt, Real.logb_mul (by linarith) hx0.ne', Real.mul_rpow (by linarith) hx0.le]
  have hLt := logb_le_two_mul_sub_one ht1
  have hLt0 : 0 ≤ logb 2 t := Real.logb_nonneg (by norm_num) ht1
  have htb : t ≤ t ^ b := Real.self_le_rpow_of_one_le ht1 hb
  have htb0 : 0 < t ^ b := Real.rpow_pos_of_pos (by linarith) b
  have hxb : 0 < x ^ (-b) := Real.rpow_pos_of_pos hx0 _
  rw [Real.rpow_neg (by linarith)]
  have key : (95 * (logb 2 t + logb 2 x) + 8) ≤ (95 * logb 2 x + 8) * t ^ b := by nlinarith
  have : (95 * (logb 2 t + logb 2 x) + 8) * ((t ^ b)⁻¹ * x ^ (-b)) =
      ((95 * (logb 2 t + logb 2 x) + 8) / t ^ b) * x ^ (-b) := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_right _ hxb.le
  rw [div_le_iff₀ htb0]; exact key

theorem log95_nonneg {Dstar b : ℝ} (hD : Gamma1core Dstar) :
    ∀ x : ℝ, logb 2 Dstar ≤ x → 0 ≤ (95 * logb 2 x + 8) * x ^ (-b) := by
  intro x hx
  have h := LacX.of_gamma hD hx
  have := h.mu_ge
  exact mul_nonneg (by linarith) (Real.rpow_nonneg h.pos.le _)

/-! ### (iv): `log*` -/

/-- "`2 log*(2^x) + 2 = 2 log* x + 4` for `x > 1`" (valid for `x > 0`). -/
theorem logStar_identity {x : ℝ} (hx : 0 < x) :
    2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2 = 2 * (logStar x : ℝ) + 4 := by
  rw [logStar_two_rpow hx]; push_cast; ring

/-! ### (iv): the three `log*` functions, (H) -/

/-- `t + 3 ≤ 2^{t/2}` for `t ≥ 12`. -/
theorem lin3_le_half {u : ℝ} (hu : 12 ≤ u) : u + 3 ≤ (2 : ℝ) ^ (u / 2) := by
  have h := two_rpow_ge_shift (t := u / 2) (t0 := 6) (by linarith)
  have e : (2 : ℝ) ^ (6 : ℝ) = 64 := by norm_num
  rw [e] at h; nlinarith

/-- `t + 3 ≤ 2^{t/4}` for `t ≥ 32`. -/
theorem lin3_le_quarter {u : ℝ} (hu : 32 ≤ u) : u + 3 ≤ (2 : ℝ) ^ (u / 4) := by
  have h := two_rpow_ge_shift (t := u / 4) (t0 := 8) (by linarith)
  have e : (2 : ℝ) ^ (8 : ℝ) = 256 := by norm_num
  rw [e] at h; nlinarith

/-- `w + 7 ≤ 2^{w/2}` for `w ≥ 12`. -/
theorem lin7_le_half {w : ℝ} (hw : 12 ≤ w) : w + 7 ≤ (2 : ℝ) ^ (w / 2) := by
  have h := two_rpow_ge_shift (t := w / 2) (t0 := 6) (by linarith)
  have e : (2 : ℝ) ^ (6 : ℝ) = 64 := by norm_num
  rw [e] at h; nlinarith

/-- `log* y ≤ 1 + log y` for `y ≥ 1`, so `2 log*(2^y) + 2 ≤ 2 log y + 6` for `y ≥ 1`. -/
theorem numer_le {y : ℝ} (hy : 1 ≤ y) :
    2 * (logStar ((2 : ℝ) ^ y) : ℝ) + 2 ≤ 2 * logb 2 y + 6 := by
  rw [logStar_identity (by linarith)]
  have := logStar_le_one_add_logb hy; linarith

theorem four_le_numer {x : ℝ} (hx : 0 < x) : 4 ≤ 2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2 := by
  rw [logStar_identity hx]
  have : (0 : ℝ) ≤ logStar x := Nat.cast_nonneg _
  linarith

theorem two_rpow_half_mul (u : ℝ) : (2 : ℝ) ^ (u / 2) * (2 : ℝ) ^ (u / 2) = (2 : ℝ) ^ u := by
  rw [← Real.rpow_add (by norm_num)]; ring_nf

/-- (iv), `η(x) = x`: "`F(y) ≤ (2 log y + 6)/y ≤ y^{-1/2}` …, and `y^{1/2} ≥ x^{50} ≥ x/2`". -/
theorem hypH_logStar_id {Dstar : ℝ} (hD : Gamma1core Dstar) :
    HypH (logb 2 Dstar) (fun x => (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / x) := by
  intro x y hx _ hxy
  have h := LacX.of_gamma hD hx
  rw [cast_Aexp] at hxy
  obtain ⟨hu, hu12, hy0⟩ := h.logb_y hxy
  have hv := h.mu_ge
  have hy1 : 1 ≤ y := le_trans (Real.one_le_rpow (by norm_num) (by linarith [h.pos])) hxy
  have hNy := numer_le hy1
  have hNx := four_le_numer h.pos
  simp only
  have hyu : (2 : ℝ) ^ logb 2 y = y := Real.rpow_logb (by norm_num) (by norm_num) hy0
  have hxv : (2 : ℝ) ^ logb 2 x = x := h.two_rpow_logb
  set u := logb 2 y
  set v := logb 2 x
  have h1 : u + 3 ≤ (2 : ℝ) ^ (u / 2) := lin3_le_half (by linarith)
  have h2 : x ≤ (2 : ℝ) ^ (u / 2) := by
    rw [← hxv]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (u + 3) * x ≤ y := by
    rw [← hyu, ← two_rpow_half_mul]
    exact mul_le_mul h1 h2 h.pos.le (by positivity)
  have hx0 := h.pos
  rw [div_div, div_le_div_iff₀ hy0 (by positivity)]
  nlinarith

/-- (iv), `η(x) = x^{1/2}`: "`F(y) ≤ (2 log y + 6)/y^{1/2} ≤ y^{-1/4}` …, and
`y^{1/4} ≥ x^{25} ≥ x^{1/2}/2`". -/
theorem hypH_logStar_sqrt {Dstar : ℝ} (hD : Gamma1core Dstar) :
    HypH (logb 2 Dstar) (fun x => (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / x ^ (1 / 2 : ℝ)) := by
  intro x y hx _ hxy
  have h := LacX.of_gamma hD hx
  rw [cast_Aexp] at hxy
  obtain ⟨hu, hu12, hy0⟩ := h.logb_y hxy
  have hv := h.mu_ge
  have hy1 : 1 ≤ y := le_trans (Real.one_le_rpow (by norm_num) (by linarith [h.pos])) hxy
  have hNy := numer_le hy1
  have hNx := four_le_numer h.pos
  simp only
  rw [rpow_eq_two_rpow hy0, rpow_eq_two_rpow h.pos]
  set u := logb 2 y
  set v := logb 2 x
  have h1 : u + 3 ≤ (2 : ℝ) ^ (u / 4) := lin3_le_quarter (by linarith)
  have h2 : (2 : ℝ) ^ (v * (1 / 2)) ≤ (2 : ℝ) ^ (u / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (u + 3) * (2 : ℝ) ^ (v * (1 / 2)) ≤ (2 : ℝ) ^ (u * (1 / 2)) := by
    have e : (2 : ℝ) ^ (u * (1 / 2)) = (2 : ℝ) ^ (u / 4) * (2 : ℝ) ^ (u / 4) := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf
    rw [e]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hA : (0 : ℝ) < (2 : ℝ) ^ (u * (1 / 2)) := by positivity
  have hB : (0 : ℝ) < (2 : ℝ) ^ (v * (1 / 2)) := by positivity
  rw [div_div, div_le_div_iff₀ hA (by positivity)]
  nlinarith

/-- `log₂ 105 ≤ 7`. -/
theorem logb_105_le : logb 2 (105 : ℝ) ≤ 7 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num

/-- (iv), `η(x) = log x`: "with `u := log y ≥ x/A`, `F(y) ≤ (2 log u + 8)/u ≤ u^{-1/2}` …, and
`u^{-1/2} ≤ (A/x)^{1/2} ≤ 2/log x`". Here in the form `(log u + 4) log x ≤ u`, with
`log x ≤ log u + 7` (`u ≥ x/A`, `log A ≤ 7`). -/
theorem hypH_logStar_log {Dstar : ℝ} (hD : Gamma1core Dstar) :
    HypH (logb 2 Dstar) (fun x => (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / logb 2 x) := by
  intro x y hx _ hxy
  have h := LacX.of_gamma hD hx
  rw [cast_Aexp] at hxy
  obtain ⟨hu, hu12, hy0⟩ := h.logb_y hxy
  have hv := h.mu_ge
  have hxu := h.le_logb_of_le hxy
  have hNx := four_le_numer h.pos
  simp only
  set u := logb 2 y with hudef
  set v := logb 2 x with hvdef
  have hu0 : 0 < u := by linarith
  -- the numerator at `y`: `2 log* y + 4 = 2 log* u + 6 ≤ 2 log u + 8`
  have hyu : (2 : ℝ) ^ u = y := Real.rpow_logb (by norm_num) (by norm_num) hy0
  have hNy : 2 * (logStar ((2 : ℝ) ^ y) : ℝ) + 2 ≤ 2 * logb 2 u + 8 := by
    rw [logStar_identity hy0, ← hyu, logStar_two_rpow hu0]
    have := logStar_le_one_add_logb (x := u) (by linarith)
    push_cast; linarith
  -- `w := log u ≥ 12` and `v ≤ w + 7`
  set w := logb 2 u with hwdef
  have hw12 : 12 ≤ w := by
    rw [hwdef, Real.le_logb_iff_rpow_le (by norm_num) hu0]
    calc (2 : ℝ) ^ (12 : ℝ) = (2 : ℝ) ^ (12 : ℕ) := by norm_num
      _ ≤ u := hu12
  have hvw : v ≤ w + 7 := by
    have h1 : logb 2 (x / 105) ≤ w :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith [h.pos]) hxu
    rw [Real.logb_div h.pos.ne' (by norm_num)] at h1
    linarith [logb_105_le]
  have huw : (2 : ℝ) ^ w = u := Real.rpow_logb (by norm_num) (by norm_num) hu0
  have h7 : w + 7 ≤ (2 : ℝ) ^ (w / 2) := lin7_le_half hw12
  have hkey : (w + 4) * v ≤ u := by
    rw [← huw, ← two_rpow_half_mul]
    have hv0 : 0 ≤ v := by linarith
    calc (w + 4) * v ≤ (w + 7) * (w + 7) := by nlinarith
      _ ≤ (2 : ℝ) ^ (w / 2) * (2 : ℝ) ^ (w / 2) :=
        mul_le_mul h7 h7 (by linarith) (by positivity)
  have hv0 : 0 < v := by linarith
  rw [div_div, div_le_div_iff₀ hu0 (by positivity)]
  nlinarith

theorem logStar_fn_nonneg {Dstar : ℝ} (hD : Gamma1core Dstar) (η : ℝ → ℝ)
    (hη : η = (fun x => x) ∨ η = (fun x => x ^ (1 / 2 : ℝ)) ∨ η = (fun x => logb 2 x)) :
    ∀ x : ℝ, logb 2 Dstar ≤ x → 0 < η x := by
  intro x hx
  have h := LacX.of_gamma hD hx
  rcases hη with rfl | rfl | rfl
  · exact h.pos
  · exact Real.rpow_pos_of_pos h.pos _
  · exact h.logb_pos

/-! ### (iv): `F(x) ≤ 2F(x_0)` for the three `log*` functions -/

/-- `4t ≤ 2^t` for `t ≥ 4`. -/
theorem four_mul_le_two_rpow {t : ℝ} (ht : 4 ≤ t) : 4 * t ≤ (2 : ℝ) ^ t := by
  have h := two_rpow_ge_shift (t := t) (t0 := 4) ht
  have e : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
  rw [e] at h; nlinarith

/-- `16t ≤ 2^t` for `t ≥ 8`. -/
theorem sixteen_mul_le_two_rpow {t : ℝ} (ht : 8 ≤ t) : 16 * t ≤ (2 : ℝ) ^ t := by
  have h := two_rpow_ge_shift (t := t) (t0 := 8) ht
  have e : (2 : ℝ) ^ (8 : ℝ) = 256 := by norm_num
  rw [e] at h; nlinarith

/-- "`tw(k_0+1) = 2^{tw(k_0)} ≥ 2^{x_0}`, and `tw(j+1) = 2^{tw(j)} ≥ 4 tw(j)` whenever
`tw(j) ≥ 4`": `tw(k_0 + 1 + i) ≥ 4^i 2^{x_0}` for `x_0 ≤ tw(k_0)`, `x_0 ≥ 2`. -/
theorem tower_ge_aux {x0 : ℝ} {k0 : ℕ} (hx0 : x0 ≤ tower k0) (h2 : 2 ≤ x0) :
    ∀ i : ℕ, (4 : ℝ) ^ i * (2 : ℝ) ^ x0 ≤ tower (k0 + 1 + i) := by
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ x0 := by
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ x0 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
  intro i
  induction i with
  | zero =>
    simp only [pow_zero, one_mul, add_zero, tower_succ]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hx0
  | succ i ih =>
    have hT4 : 4 ≤ tower (k0 + 1 + i) := by
      have : (1 : ℝ) ≤ (4 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    rw [show k0 + 1 + (i + 1) = (k0 + 1 + i) + 1 by ring, tower_succ, pow_succ]
    have := four_mul_le_two_rpow hT4
    nlinarith

/-- The case analysis of the proof: if `η > 0` is non-decreasing on `[x_0,∞)` and
`η(x) ≥ 2^k η(x_0)` whenever `log* x = log* x_0 + k` with `k ≥ 2` (in the form
`tw(log* x_0 + k - 1) < x`), then `F(x) ≤ 2F(x_0)` for `F(x) = (2 log*(2^x) + 2)/η(x)`
("If `k = 0` … If `k = 1` … Let `k ≥ 2` … `F(x) ≤ (2k_0+2k+4)/(2^k η(x_0)) ≤ F(x_0)`"). -/
theorem logStar_fn_le_two {x0 : ℝ} (hx0 : 0 < x0) (η : ℝ → ℝ) (hpos : ∀ x, x0 ≤ x → 0 < η x)
    (hmono : ∀ x, x0 ≤ x → η x0 ≤ η x)
    (hclaim : ∀ x, x0 ≤ x → ∀ k : ℕ, 2 ≤ k → tower (logStar x0 + k - 1) < x →
      (2 : ℝ) ^ k * η x0 ≤ η x) :
    ∀ x, x0 ≤ x → (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / η x ≤
      2 * ((2 * (logStar ((2 : ℝ) ^ x0) : ℝ) + 2) / η x0) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  rw [logStar_identity hxpos, logStar_identity hx0]
  have hK : logStar x0 ≤ logStar x := logStar_mono hx
  have hη0 := hpos x0 le_rfl
  have hηx := hpos x hx
  set K := logStar x with hKdef
  set k0 := logStar x0
  have hk0 : (0 : ℝ) ≤ k0 := Nat.cast_nonneg _
  by_cases hsmall : K ≤ k0 + 1
  · have hKr : (K : ℝ) ≤ k0 + 1 := by exact_mod_cast hsmall
    calc (2 * (K : ℝ) + 4) / η x ≤ (2 * (K : ℝ) + 4) / η x0 :=
          div_le_div_of_nonneg_left (by positivity) hη0 (hmono x hx)
      _ ≤ 2 * ((2 * (k0 : ℝ) + 4) / η x0) := by
          rw [mul_div_assoc']
          apply div_le_div_of_nonneg_right _ hη0.le
          linarith
  · push Not at hsmall
    obtain ⟨k, hk⟩ : ∃ k, K = k0 + k := ⟨K - k0, by omega⟩
    have hk2 : 2 ≤ k := by omega
    have hlt : tower (k0 + k - 1) < x := by
      rw [← lt_logStar_iff_tower_lt, ← hKdef]; omega
    have hcl := hclaim x hx k hk2 hlt
    have h2k : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
      have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      exact_mod_cast this
    have hKr : (K : ℝ) = k0 + k := by rw [hk]; push_cast; ring
    have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    calc (2 * (K : ℝ) + 4) / η x ≤ (2 * (K : ℝ) + 4) / ((2 : ℝ) ^ k * η x0) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hcl
      _ ≤ (2 * (k0 : ℝ) + 4) / η x0 := by
          rw [div_le_div_iff₀ (by positivity) hη0, hKr]
          have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          have : 2 * ((k0 : ℝ) + k) + 4 ≤ (2 : ℝ) ^ k * (2 * k0 + 4) := by nlinarith
          nlinarith
      _ ≤ 2 * ((2 * (k0 : ℝ) + 4) / η x0) := by
          have : 0 ≤ (2 * (k0 : ℝ) + 4) / η x0 := by positivity
          linarith

/-- The claim for `η(x) = x`: "`x > tw(k_0+k-1) ≥ 4^{k-2} 2^{x_0}` … `4^{k-2} 2^{x_0} ≥ 2^k x_0`". -/
theorem claim_id {x0 : ℝ} (h8 : 8 ≤ x0) :
    ∀ x, x0 ≤ x → ∀ k : ℕ, 2 ≤ k → tower (logStar x0 + k - 1) < x →
      (2 : ℝ) ^ k * x0 ≤ x := by
  intro x _ k hk hlt
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have ht := tower_ge_aux (k0 := logStar x0) ((logStar_le_iff_le_tower _ x0).1 le_rfl)
    (by linarith) j
  rw [show logStar x0 + 1 + j = logStar x0 + (j + 2) - 1 by omega] at ht
  have h4 := four_mul_le_two_rpow (t := x0) (by linarith)
  have hj : (2 : ℝ) ^ j ≤ (4 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hj1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have e : (2 : ℝ) ^ (j + 2) * x0 = (2 : ℝ) ^ j * (4 * x0) := by ring
  rw [e]
  have : (2 : ℝ) ^ j * (4 * x0) ≤ (4 : ℝ) ^ j * (2 : ℝ) ^ x0 :=
    mul_le_mul hj h4 (by linarith) (by positivity)
  linarith

/-- The claim for `η(x) = x^{1/2}` (squared: `x ≥ 4^k x_0`). -/
theorem claim_sqrt {x0 : ℝ} (h8 : 8 ≤ x0) :
    ∀ x, x0 ≤ x → ∀ k : ℕ, 2 ≤ k → tower (logStar x0 + k - 1) < x →
      (2 : ℝ) ^ k * x0 ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
  intro x hx k hk hlt
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have ht := tower_ge_aux (k0 := logStar x0) ((logStar_le_iff_le_tower _ x0).1 le_rfl)
    (by linarith) j
  rw [show logStar x0 + 1 + j = logStar x0 + (j + 2) - 1 by omega] at ht
  have h16 := sixteen_mul_le_two_rpow (t := x0) h8
  have hx0 : 0 ≤ x0 := by linarith
  have hsq : (4 : ℝ) ^ (j + 2) * x0 ≤ x := by
    have e : (4 : ℝ) ^ (j + 2) * x0 = (4 : ℝ) ^ j * (16 * x0) := by ring
    rw [e]
    have : (4 : ℝ) ^ j * (16 * x0) ≤ (4 : ℝ) ^ j * (2 : ℝ) ^ x0 :=
      mul_le_mul_of_nonneg_left h16 (by positivity)
    linarith
  have ha : 0 ≤ (2 : ℝ) ^ (j + 2) * x0 ^ (1 / 2 : ℝ) := by positivity
  have hb : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsq2 : ∀ z : ℝ, 0 ≤ z → (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
    intro z hz
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz]; norm_num
  rw [← pow_le_pow_iff_left₀ ha hb (two_ne_zero), mul_pow, hsq2 x0 hx0, hsq2 x (by linarith),
    show ((2 : ℝ) ^ (j + 2)) ^ 2 = (4 : ℝ) ^ (j + 2) by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  exact hsq

/-- The claim for `η(x) = log x`: "`log x > tw(k_0+k-2)`, which is at least `tw(k_0) ≥ x_0 ≥
4 log x_0` if `k = 2`, and at least `4^{k-3} 2^{x_0} ≥ 2^k log x_0` if `k ≥ 3`". -/
theorem claim_log {x0 : ℝ} (h8 : 8 ≤ x0) (hlog : 4 * logb 2 x0 ≤ x0) :
    ∀ x, x0 ≤ x → ∀ k : ℕ, 2 ≤ k → tower (logStar x0 + k - 1) < x →
      (2 : ℝ) ^ k * logb 2 x0 ≤ logb 2 x := by
  intro x hx k hk hlt
  have hxpos : 0 < x := by linarith
  have htx0 : x0 ≤ tower (logStar x0) := (logStar_le_iff_le_tower _ x0).1 le_rfl
  have hL : tower (logStar x0 + k - 2) < logb 2 x := by
    rw [show logStar x0 + k - 1 = (logStar x0 + k - 2) + 1 by omega, tower_succ] at hlt
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hxpos]; exact hlt
  have hl0 : 0 ≤ logb 2 x0 := Real.logb_nonneg (by norm_num) (by linarith)
  rcases Nat.eq_or_lt_of_le hk with rfl | hk3
  · rw [show logStar x0 + 2 - 2 = logStar x0 by omega] at hL
    norm_num; linarith
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have ht := tower_ge_aux (k0 := logStar x0) htx0 (by linarith) j
    rw [show logStar x0 + 1 + j = logStar x0 + (j + 3) - 2 by omega] at ht
    have h16 := sixteen_mul_le_two_rpow (t := x0) h8
    have hj : (2 : ℝ) ^ j ≤ (4 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have e : (2 : ℝ) ^ (j + 3) * logb 2 x0 = (2 : ℝ) ^ j * (8 * logb 2 x0) := by ring
    rw [e]
    have h8l : 8 * logb 2 x0 ≤ (2 : ℝ) ^ x0 := by linarith
    have : (2 : ℝ) ^ j * (8 * logb 2 x0) ≤ (4 : ℝ) ^ j * (2 : ℝ) ^ x0 :=
      mul_le_mul hj h8l (by positivity) (by positivity)
    linarith

end EG.HB
