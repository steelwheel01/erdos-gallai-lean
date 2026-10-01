module

public import EG.Defs.HB.Round
public import EG.Lib.Found.Gamma
public import EG.Lib.Found.Constants

/-!
# The (R2) parameter algebra of a round (manuscript s2:defHBtp (R2), s2:propDegRec, s2:lemTower)

Helper lemmas for the P3 stubs of s2:lemTower (unit P3-s2). Throughout `d ≥ D_*` with Γ1
(a)–(e) at `D_*`; `λ = log d`, `μ = log λ` (`log = log₂`), so that `d = 2^λ`, `λ = 2^μ`,
`μ ≥ 2^8` and Γ1 (a)–(e) hold at `μ` ([s2:lemTower] proof: "the items of Γ1 hold at
`μ = log λ_r`"). The parameters are those of `EG.HB` (`TOf`, `MOf`, `LamOf`, `sOf`, `POf`,
`tauOf`, `thetaGC`).

* `ParamHyp d`: the standing facts `2 < d`, `2^{256} ≤ λ`, `Gamma1Items μ`
  (`ParamHyp.of_gamma`);
* `d ≤ M`, `M ≤ d²`, `2^{40} ≤ M`, `λ ≤ Λ ≤ 2λ`, `40 ≤ Λ`;
* `Λ^σ ≤ s ≤ 2Λ^σ`, `λ^{100} ≤ s`, `λ^{C'} ≤ P ≤ λ^{C'} + 1`, `s ≤ P`;
* `τ ≤ 257 Λ^{σ+2}`;
* `(Aμ)^A ≤ λ` and `(Aμ)^{2A} ≤ λ^{1.6}` (Γ1 (c) at `μ`).
-/

public section

namespace EG.HB

open Real

/-- `(2^a)^n = 2^{a n}` (real `a`, natural `n`). -/
theorem two_rpow_pow (a : ℝ) (n : ℕ) : ((2 : ℝ) ^ a) ^ n = (2 : ℝ) ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- The standing facts at a real `d` (a round degree `d_l ≥ D_*` under Γ1). -/
structure ParamHyp (d : ℝ) : Prop where
  two_lt : 2 < d
  lam_ge : (2 : ℝ) ^ 256 ≤ logb 2 d
  items : Gamma1Items (logb 2 (logb 2 d))

theorem ParamHyp.of_gamma {Dstar d : ℝ} (hD : Gamma1core Dstar) (hd : Dstar ≤ d) :
    ParamHyp d where
  two_lt := hD.two_lt.trans_le hd
  lam_ge := hD.two_pow_256_le_logb.trans
    (Real.logb_le_logb_of_le (by norm_num) (by linarith [hD.two_lt]) hd)
  items := hD.items_loglog hd

namespace ParamHyp

variable {d : ℝ} (h : ParamHyp d)
include h

theorem d_pos : 0 < d := by linarith [h.two_lt]

theorem lam_pos : 0 < logb 2 d := lt_of_lt_of_le (by positivity) h.lam_ge

theorem d_eq : (2 : ℝ) ^ (logb 2 d) = d := Real.rpow_logb (by norm_num) (by norm_num) h.d_pos

theorem lam_eq : (2 : ℝ) ^ (logb 2 (logb 2 d)) = logb 2 d :=
  Real.rpow_logb (by norm_num) (by norm_num) h.lam_pos

theorem mu_ge : 256 ≤ logb 2 (logb 2 d) := by
  have := h.items.a; unfold Gamma1a at this; norm_num at this; linarith

/-- Γ1 (b) at `μ`: `2^{14} A μ³ ≤ λ`. -/
theorem mu_cube_le : (2 : ℝ) ^ 14 * 105 * logb 2 (logb 2 d) ^ 3 ≤ logb 2 d := by
  have hb := h.items.b; unfold Gamma1b at hb; rw [h.lam_eq, cast_Aexp] at hb; exact hb

theorem lin_mu_le {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b ≤ 2 ^ 14 * 105 * 256 ^ 2) :
    a + b * logb 2 (logb 2 d) ≤ logb 2 d := by
  have h1 := h.mu_cube_le
  have h2 := h.mu_ge
  set μ := logb 2 (logb 2 d)
  have hμ2 : (256 : ℝ) ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
  have : (a + b) * μ ≤ 2 ^ 14 * 105 * μ ^ 3 := by
    have e : μ ^ 3 = μ ^ 2 * μ := by ring
    rw [e]
    have hμ0 : 0 ≤ μ := by linarith
    nlinarith
  nlinarith

theorem d_ge : (2 : ℝ) ^ 256 ≤ d := by
  rw [← h.d_eq]
  calc (2 : ℝ) ^ (256 : ℕ) = (2 : ℝ) ^ ((256 : ℕ) : ℝ) := (Real.rpow_natCast 2 256).symm
    _ ≤ (2 : ℝ) ^ (logb 2 d) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have := h.lam_ge; push_cast; linarith [show (256 : ℝ) ≤ 2 ^ 256 by norm_num])

omit h in
theorem T_eq : TOf d = logb 2 d ^ 2 * d := rfl

theorem logb_T : logb 2 (TOf d) = 2 * logb 2 (logb 2 d) + logb 2 d := by
  rw [T_eq, Real.logb_mul (by positivity [h.lam_pos.ne']) h.d_pos.ne', Real.logb_pow]
  push_cast; ring

theorem logb_T_le : logb 2 (TOf d) ≤ 2 * logb 2 d := by
  rw [h.logb_T]; linarith [h.lin_mu_le (a := 0) (b := 2) le_rfl (by norm_num) (by norm_num)]

theorem one_le_logb_T : 1 ≤ logb 2 (TOf d) := by
  rw [h.logb_T]; linarith [h.mu_ge, h.lam_ge, show (1 : ℝ) ≤ 2 ^ 256 by norm_num]

theorem d_le_T : d ≤ TOf d := by
  rw [T_eq]
  have : 1 ≤ logb 2 d ^ 2 := one_le_pow₀ (by linarith [h.lam_ge, show (1 : ℝ) ≤ 2 ^ 256 by norm_num])
  nlinarith [h.d_pos]

omit h in
theorem max_nonneg : 0 ≤ max (2 ^ 40) (2 ^ 16 * TOf d * logb 2 (TOf d) ^ 4) :=
  le_trans (by norm_num) (le_max_left _ _)

theorem d_le_max : d ≤ max (2 ^ 40) (2 ^ 16 * TOf d * logb 2 (TOf d) ^ 4) := by
  refine le_trans ?_ (le_max_right _ _)
  have h1 := h.d_le_T
  have h2 : 1 ≤ logb 2 (TOf d) ^ 4 := one_le_pow₀ h.one_le_logb_T
  have hT : 0 ≤ TOf d := by linarith [h.d_pos]
  nlinarith

/-- `M ≥ d` ("`M_{l-1} ≥ d_{l-1}` (as in Proposition s2:propStructure(i))"). -/
theorem d_le_M : d ≤ (MOf d : ℝ) := h.d_le_max.trans (Nat.le_ceil _)

omit h in
theorem two40_le_M : (2 : ℝ) ^ 40 ≤ (MOf d : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)

theorem M_pos : (0 : ℝ) < MOf d := lt_of_lt_of_le (by norm_num) two40_le_M

theorem M_le_max_add_one :
    (MOf d : ℝ) ≤ max (2 ^ 40) (2 ^ 16 * TOf d * logb 2 (TOf d) ^ 4) + 1 :=
  (Nat.ceil_lt_add_one max_nonneg).le

/-- `2^{21} λ^6 ≤ d`. -/
theorem lam6_le_d : (2 : ℝ) ^ 21 * logb 2 d ^ 6 ≤ d := by
  have hl : logb 2 d ^ 6 = (2 : ℝ) ^ (logb 2 (logb 2 d) * 6) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ← two_rpow_pow, h.lam_eq]
  rw [hl, show (2 : ℝ) ^ 21 = (2 : ℝ) ^ ((21 : ℕ) : ℝ) by rw [Real.rpow_natCast],
    ← Real.rpow_add (by norm_num)]
  conv_rhs => rw [← h.d_eq]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := h.lin_mu_le (a := 21) (b := 6) (by norm_num) (by norm_num) (by norm_num)
  push_cast; linarith

/-- [s2:propDegRec] "`M_l ≤ d_l^2`". -/
theorem M_le_sq : (MOf d : ℝ) ≤ d ^ 2 := by
  refine h.M_le_max_add_one.trans ?_
  have hd1 : 1 ≤ d := by linarith [h.two_lt]
  have hdg := h.d_ge
  rcases max_cases (2 ^ 40 : ℝ) (2 ^ 16 * TOf d * logb 2 (TOf d) ^ 4) with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; nlinarith
  · rw [hm]
    have hL := h.logb_T_le
    have hL0 : 0 ≤ logb 2 (TOf d) := by linarith [h.one_le_logb_T]
    have hL4 : logb 2 (TOf d) ^ 4 ≤ (2 * logb 2 d) ^ 4 := pow_le_pow_left₀ hL0 hL 4
    have h6 := h.lam6_le_d
    have hl0 : 0 ≤ logb 2 d := h.lam_pos.le
    have hl1 : 1 ≤ logb 2 d ^ 6 :=
      one_le_pow₀ (by linarith [h.lam_ge, show (1 : ℝ) ≤ 2 ^ 256 by norm_num])
    have key : 2 ^ 16 * TOf d * logb 2 (TOf d) ^ 4 ≤ 2 ^ 20 * logb 2 d ^ 6 * d := by
      have e : (2 * logb 2 d) ^ 4 = 16 * logb 2 d ^ 4 := by ring
      rw [e] at hL4
      have : 0 ≤ 2 ^ 16 * TOf d := mul_nonneg (by norm_num) (by linarith [h.d_le_T, h.d_pos])
      calc 2 ^ 16 * TOf d * logb 2 (TOf d) ^ 4
          ≤ 2 ^ 16 * TOf d * (16 * logb 2 d ^ 4) := mul_le_mul_of_nonneg_left hL4 this
        _ = 2 ^ 20 * logb 2 d ^ 6 * d := by rw [T_eq]; ring
    have h7 := mul_le_mul_of_nonneg_right h6 h.d_pos.le
    nlinarith

omit h in
theorem Lam_def : LamOf d = logb 2 (MOf d : ℝ) := rfl

theorem lam_le_Lam : logb 2 d ≤ LamOf d :=
  Real.logb_le_logb_of_le (by norm_num) h.d_pos h.d_le_M

theorem Lam_le_two_lam : LamOf d ≤ 2 * logb 2 d := by
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) h.M_pos h.M_le_sq
  rw [Real.logb_pow] at this
  rw [Lam_def]; push_cast at this; linarith

theorem forty_le_Lam : 40 ≤ LamOf d := by
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) (two40_le_M (d := d))
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
  rw [Lam_def]; push_cast at this; linarith

theorem Lam_pos : 0 < LamOf d := by linarith [h.forty_le_Lam]

omit h in
theorem s_ge : LamOf d ^ sigmaC ≤ (sOf d : ℝ) := Nat.le_ceil _

theorem s_le_add_one : (sOf d : ℝ) ≤ LamOf d ^ sigmaC + 1 :=
  (Nat.ceil_lt_add_one (pow_nonneg h.Lam_pos.le _)).le

theorem one_le_Lam_pow (n : ℕ) : 1 ≤ LamOf d ^ n := one_le_pow₀ (by linarith [h.forty_le_Lam])

theorem s_le_two : (sOf d : ℝ) ≤ 2 * LamOf d ^ sigmaC := by
  linarith [h.s_le_add_one, h.one_le_Lam_pow sigmaC]

theorem lam100_le_s : logb 2 d ^ 100 ≤ (sOf d : ℝ) := by
  refine le_trans ?_ s_ge
  rw [sigmaC_eq]
  exact pow_le_pow_left₀ h.lam_pos.le h.lam_le_Lam 100

omit h in
theorem P_ge : logb 2 d ^ Cp ≤ (POf d : ℝ) := Nat.le_ceil _

theorem P_le_add_one : (POf d : ℝ) ≤ logb 2 d ^ Cp + 1 :=
  (Nat.ceil_lt_add_one (pow_nonneg h.lam_pos.le _)).le

theorem s_le_lam103 : (sOf d : ℝ) ≤ logb 2 d ^ 103 := by
  refine h.s_le_two.trans ?_
  have h1 : LamOf d ^ sigmaC ≤ (2 * logb 2 d) ^ 100 := by
    rw [sigmaC_eq]; exact pow_le_pow_left₀ h.Lam_pos.le h.Lam_le_two_lam 100
  have h3 : (2 : ℝ) ^ 101 ≤ logb 2 d ^ 3 := by
    have : (2 : ℝ) ^ 101 ≤ logb 2 d := le_trans (by norm_num) h.lam_ge
    have h1l : 1 ≤ logb 2 d := le_trans (by norm_num) h.lam_ge
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h1l 2, one_le_pow₀ h1l (n := 2)]
  have e : (2 * logb 2 d) ^ 100 = 2 ^ 100 * logb 2 d ^ 100 := by ring
  have e2 : logb 2 d ^ 103 = logb 2 d ^ 3 * logb 2 d ^ 100 := by ring
  rw [e2]
  have hp : 0 ≤ logb 2 d ^ 100 := pow_nonneg h.lam_pos.le _
  nlinarith

/-- [s2:propDegRec] "`s_l ≤ P_l`". -/
theorem s_le_P : sOf d ≤ POf d := by
  have hP := P_ge (d := d)
  rw [Cp_eq] at hP
  have : (sOf d : ℝ) ≤ POf d := h.s_le_lam103.trans hP
  exact_mod_cast this

theorem tau_le : (tauOf d : ℝ) ≤ 257 * LamOf d ^ (sigmaC + 2) := by
  have h0 : 0 ≤ 128 * (sOf d : ℝ) * logb 2 (MOf d : ℝ) ^ 2 := by positivity
  refine (Nat.ceil_lt_add_one h0).le.trans ?_
  rw [← Lam_def]
  have hs := h.s_le_two
  have hL2 : 0 ≤ LamOf d ^ 2 := by positivity
  have e : LamOf d ^ (sigmaC + 2) = LamOf d ^ sigmaC * LamOf d ^ 2 := pow_add _ _ _
  rw [e]
  have h1 := h.one_le_Lam_pow (sigmaC + 2)
  rw [e] at h1
  nlinarith [mul_le_mul_of_nonneg_right hs hL2]

/-- Γ1 (c) at `μ`: `(Aμ)^A ≤ 2^{0.8 μ}`, as `2^{A log(Aμ)}`. -/
theorem Amu_pow_A : ((Aexp : ℝ) * logb 2 (logb 2 d)) ^ Aexp ≤
    (2 : ℝ) ^ ((0.8 : ℝ) * logb 2 (logb 2 d)) := by
  have hc := h.items.c; unfold Gamma1c at hc
  have hμ := h.mu_ge
  have hpos : 0 < (Aexp : ℝ) * logb 2 (logb 2 d) := by rw [cast_Aexp]; positivity
  rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hpos, two_rpow_pow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-- Γ1 (c) at `μ`: `(Aμ)^{2A} ≤ 2^{1.6 μ}`. -/
theorem Amu_pow_2A : ((Aexp : ℝ) * logb 2 (logb 2 d)) ^ (2 * Aexp) ≤
    (2 : ℝ) ^ ((1.6 : ℝ) * logb 2 (logb 2 d)) := by
  have hc := h.items.c; unfold Gamma1c at hc
  have hμ := h.mu_ge
  have hpos : 0 < (Aexp : ℝ) * logb 2 (logb 2 d) := by rw [cast_Aexp]; positivity
  rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hpos, two_rpow_pow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast; linarith

/-- "`(A log λ)^A ≤ λ`" (proof of s2:lemTower (a)). -/
theorem Amu_pow_A_le_lam : ((Aexp : ℝ) * logb 2 (logb 2 d)) ^ Aexp ≤ logb 2 d := by
  refine h.Amu_pow_A.trans ?_
  conv_rhs => rw [← h.lam_eq]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := h.mu_ge; linarith

/-- "`(A log λ)^{2A} ≤ λ^{1.6}`" (proof of s2:lemTower (b)). -/
theorem Amu_pow_2A_le_lam : ((Aexp : ℝ) * logb 2 (logb 2 d)) ^ (2 * Aexp) ≤
    logb 2 d ^ (1.6 : ℝ) := by
  refine h.Amu_pow_2A.trans (le_of_eq ?_)
  conv_rhs => rw [← h.lam_eq]
  rw [← Real.rpow_mul (by norm_num)]; ring_nf


/-- Proof of [s2:lemTower] (d): "`log* d_r = 2 + log* μ` … `2 log* d_r + 2 = 6 + 2 log* μ ≤
8 + 2 log μ ≤ μ`", so `λ = 2^μ ≥ 2^{2 log* d + 2}` (Γ1 (d) at `μ`). -/
theorem logStar_le_mu : ((2 * logStar d + 2 : ℕ) : ℝ) ≤ logb 2 (logb 2 d) := by
  have hμ := h.mu_ge
  have hdd := h.items.d; unfold Gamma1d at hdd
  have e1 : logStar d = logStar (logb 2 (logb 2 d)) + 2 := by
    conv_lhs => rw [← h.d_eq]
    rw [logStar_two_rpow h.lam_pos]
    conv_lhs => rw [← h.lam_eq]
    rw [logStar_two_rpow (by linarith)]
  have e2 := logStar_le_one_add_logb (x := logb 2 (logb 2 d)) (by linarith)
  rw [e1]; push_cast; linarith

theorem two_pow_logStar_le : (2 : ℝ) ^ (2 * logStar d + 2) ≤ logb 2 d := by
  rw [← Real.rpow_natCast]
  conv_rhs => rw [← h.lam_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h.logStar_le_mu


/-- "`2^y ≥ 2 y^{2A}`" with `y = λ` (proof of s2:lemTower (b), Γ1 (a), (b) at `μ`):
`2 λ^{2A} ≤ d`. -/
theorem two_lam_pow_le_d : 2 * logb 2 d ^ (2 * Aexp) ≤ d := by
  have hl : logb 2 d ^ (2 * Aexp) = (2 : ℝ) ^ (logb 2 (logb 2 d) * ((2 * Aexp : ℕ) : ℝ)) := by
    rw [← two_rpow_pow, h.lam_eq]
  rw [hl, show (2 : ℝ) * (2 : ℝ) ^ (logb 2 (logb 2 d) * ((2 * Aexp : ℕ) : ℝ)) =
      (2 : ℝ) ^ (1 + logb 2 (logb 2 d) * ((2 * Aexp : ℕ) : ℝ)) by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]]
  conv_rhs => rw [← h.d_eq]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := h.lin_mu_le (a := 1) (b := 210) (by norm_num) (by norm_num) (by norm_num)
  rw [Aexp_eq]; push_cast; linarith

theorem one_le_Amu : 1 ≤ (Aexp : ℝ) * logb 2 (logb 2 d) := by
  rw [cast_Aexp]; nlinarith [h.mu_ge]

theorem one_le_lam : 1 ≤ logb 2 d := le_trans (by norm_num) h.lam_ge

/-- `λ + 1 ≤ λ^{103}/2` (`λ ≥ 2`). -/
theorem lam_add_one_le : logb 2 d + 1 ≤ logb 2 d ^ 103 / 2 := by
  have h1 := h.one_le_lam
  have h2 : (2 : ℝ) ^ 256 ≤ logb 2 d := h.lam_ge
  have h3 : logb 2 d ≤ logb 2 d ^ 102 := le_self_pow₀ h1 (by norm_num)
  have e : logb 2 d ^ 103 = logb 2 d * logb 2 d ^ 102 := by ring
  rw [e]
  nlinarith

/-- `Λ^4 ≤ d` (so `log⁴ M ≤ M`): `Λ^4 ≤ 16 λ^4 ≤ 2^{21} λ^6 ≤ d`. -/
theorem Lam4_le_d : LamOf d ^ 4 ≤ d := by
  have h1 : LamOf d ^ 4 ≤ (2 * logb 2 d) ^ 4 := pow_le_pow_left₀ h.Lam_pos.le h.Lam_le_two_lam 4
  have h2 := h.lam6_le_d
  have h3 := h.one_le_lam
  have h4 : logb 2 d ^ 4 ≤ logb 2 d ^ 6 := pow_le_pow_right₀ h3 (by norm_num)
  have h5 : 0 ≤ logb 2 d ^ 4 := by positivity
  nlinarith


/-- Proof of s2:propDegRec, final bounds: `6P + 9 s log M + 1.2 s ≤ 7x^{103}` (`x = λ`), using
`P ≤ x^{103} + 1`, `s ≤ 2^{101} x^{100}`, `log M ≤ 2x` and `x² ≥ 2^{107}`. -/
theorem final_bound : 6 * (POf d : ℝ) + 9 * (sOf d : ℝ) * logb 2 (MOf d : ℝ) +
    1.2 * (sOf d : ℝ) ≤ 7 * logb 2 d ^ 103 := by
  set x := logb 2 d with hx
  have hxg : (2 : ℝ) ^ 256 ≤ x := h.lam_ge
  have hx1 : 1 ≤ x := h.one_le_lam
  have hP := h.P_le_add_one
  rw [Cp_eq] at hP
  have hs : (sOf d : ℝ) ≤ 2 ^ 101 * x ^ 100 := by
    have h1 := h.s_le_two
    have h2 : LamOf d ^ sigmaC ≤ (2 * x) ^ 100 := by
      rw [sigmaC_eq]; exact pow_le_pow_left₀ h.Lam_pos.le h.Lam_le_two_lam 100
    have e : (2 * x) ^ 100 = 2 ^ 100 * x ^ 100 := by ring
    rw [e] at h2
    linarith
  have hL : logb 2 (MOf d : ℝ) ≤ 2 * x := h.Lam_le_two_lam
  have hL0 : 0 ≤ logb 2 (MOf d : ℝ) := h.Lam_pos.le
  have hs0 : (0 : ℝ) ≤ sOf d := Nat.cast_nonneg _
  set y := x ^ 100 with hy
  have hy1 : 1 ≤ y := one_le_pow₀ hx1
  have hx2 : (2 : ℝ) ^ 107 ≤ x ^ 2 := by
    have : (2 : ℝ) ^ 107 ≤ x := le_trans (by norm_num) hxg
    nlinarith
  have e103 : x ^ 103 = x ^ 2 * x * y := by rw [hy]; ring
  -- `9 s log M ≤ 9 · 2^{102} x y`
  have h1 : 9 * (sOf d : ℝ) * logb 2 (MOf d : ℝ) ≤ 9 * (2 ^ 101 * y) * (2 * x) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hL hL0 (by positivity)
  have h2 : 1.2 * (sOf d : ℝ) ≤ 1.2 * (2 ^ 101 * y) := mul_le_mul_of_nonneg_left hs (by norm_num)
  -- `2^{107} x y ≤ x^{103}`
  have h3 : (2 : ℝ) ^ 107 * x * y ≤ x ^ 103 := by
    rw [e103]
    have : 0 ≤ x * y := by positivity
    nlinarith
  have h4 : (2 : ℝ) ^ 107 * y ≤ x ^ 103 := by
    have : (2 : ℝ) ^ 107 * y ≤ 2 ^ 107 * x * y := by
      have : 0 ≤ (2 : ℝ) ^ 107 * y := by positivity
      nlinarith
    linarith
  have h5 : (6 : ℝ) ≤ 2 ^ 107 * y := by nlinarith
  rw [e103] at h3 h4 ⊢
  nlinarith

/-- `7x^{103} ≤ x^A` (`x ≥ 7`). -/
theorem seven_le_pow_A : 7 * logb 2 d ^ 103 ≤ logb 2 d ^ Aexp := by
  have hx1 := h.one_le_lam
  have hx7 : (7 : ℝ) ≤ logb 2 d := le_trans (by norm_num) h.lam_ge
  rw [Aexp_eq, show (105 : ℕ) = 103 + 2 by rfl, pow_add]
  have : (0 : ℝ) ≤ logb 2 d ^ 103 := by positivity
  have : (7 : ℝ) ≤ logb 2 d ^ 2 := by nlinarith
  nlinarith

/-- `x^A < 2^x = d` ("`x^{105} < 2^x = d_l` as `105 log x < x`"). -/
theorem pow_A_lt_d : logb 2 d ^ Aexp < d := by
  have hl := h.lam_eq
  rw [← hl, two_rpow_pow]
  conv_rhs => rw [← h.d_eq, ← hl]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  have := h.lin_mu_le (a := 1) (b := 105) (by norm_num) (by norm_num) (by norm_num)
  rw [h.lam_eq, Aexp_eq]; push_cast; linarith

end ParamHyp

end EG.HB
