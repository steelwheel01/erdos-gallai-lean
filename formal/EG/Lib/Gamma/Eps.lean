module

public import EG.Defs.Quot.Constants
public import EG.Lib.Light.Constants
public import EG.Lib.Found.Log
public import EG.Lib.Found.Constants
public import EG.Lib.Chain.Constants
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# `ε_1(D_*) → 0` and `ε_2(D_*) → 0` (manuscript s7:lemGammaSat (ii))

Manuscript v6.1, `s7.tex`, Lemma [s7:lemGammaSat] (ii): "`ε_1(D_*) → 0` and `ε_2(D_*) → 0` as
`D_* → ∞`", with the proof: "every summand of `ε_1` and of `ε_2` tends to 0". Unit GAMMA
(design note `formal/work/p2b/GAMMA.md`, §8 step 3).

The summands (all functions of `D_*` alone):
* `ε_K = ε_ch`: `EG.Light.tendsto_epsChain` (already proved);
* `ε_A = 31ε/(C' log₂log₂D_*)`: a constant over a function tending to `∞` (`tendsto_epsA`);
* `c/D_*`;
* `ε_CONC`: `log*D_* ≤ 2 + log₂log₂D_*` bounds the first and third terms by multiples of
  `g(log₂D_*)`, `g(y) = (6 + 2 log₂ y)/y^{1/2} → 0`; the second term is
  `(200ε/C')·log*D_*/log₂log₂D_*`, which tends to `0` by `log* = o(log log)`
  (`EG.logStar_isLittleO_loglog`) (`tendsto_epsCONC`);
* `ε_X = ε_U + 10.3/D_* + 2.1ψ(D_*)` with `ε_U → 0` (`EG.Light.tendsto_epsU`) and
  `log₂D_*/D_* → 0` (`tendsto_epsX`);
* `F(log₂D_*)`, `F(x) = (3184 + 30400 log₂x) x^{-90.2} ≤ (3184 + 60800x) x^{-90.2}` (`tendsto_FQ`).
No `sorry`.
-/

public section

namespace EG

open Filter Topology Real Asymptotics

/-- `log₂ D → ∞`. -/
theorem tendsto_logb_two_atTop : Tendsto (fun D : ℝ => logb 2 D) atTop atTop :=
  Real.tendsto_logb_atTop (by norm_num)

/-- `c / f → 0` when `f → ∞`. -/
theorem tendsto_const_div_of_tendsto_atTop {f : ℝ → ℝ} (c : ℝ) (hf : Tendsto f atTop atTop) :
    Tendsto (fun x => c / f x) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop hf

/-- `ε_A(D_*) = 31ε/(C' log₂log₂D_*) → 0`. -/
theorem tendsto_epsA : Tendsto HB.epsA atTop (𝓝 0) := by
  have h : Tendsto (fun D : ℝ => (Cp : ℝ) * logb 2 (logb 2 D)) atTop atTop :=
    (tendsto_logb_two_atTop.comp tendsto_logb_two_atTop).const_mul_atTop (by norm_num [Cp])
  exact tendsto_const_div_of_tendsto_atTop _ h

/-- `log₂ x / x → 0`. -/
theorem tendsto_logb_div_self : Tendsto (fun x : ℝ => logb 2 x / x) atTop (𝓝 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.tendsto_pow_log_div_mul_add_atTop (Real.log 2) 0 1 hl2.ne'
  refine h.congr fun x => ?_
  rw [Real.logb, pow_one, add_zero, div_div, mul_comm]

/-- `g(y) = (6 + 2 log₂ y)/y^{1/2} → 0`. -/
theorem tendsto_logb_div_sqrt :
    Tendsto (fun y : ℝ => (6 + 2 * logb 2 y) / y ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : Tendsto (fun y : ℝ => y ^ ((1 : ℝ) / 2)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h1 : Tendsto (fun y : ℝ => 6 / y ^ ((1 : ℝ) / 2)) atTop (𝓝 0) :=
    tendsto_const_div_of_tendsto_atTop 6 hr
  have h2 : Tendsto (fun y : ℝ => Real.log y / y ^ ((1 : ℝ) / 2)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have := h1.add (h2.const_mul (2 / Real.log 2))
  rw [mul_zero, add_zero] at this
  refine this.congr fun y => ?_
  rw [Real.logb]
  field_simp

/-- `ε_CONC(D_*) → 0` ([s6:thmCONCL] (iv); summand of `ε_1`). -/
theorem Chain.tendsto_epsCONC : Tendsto Chain.epsCONC atTop (𝓝 0) := by
  have hL := tendsto_logb_two_atTop
  have hg := tendsto_logb_div_sqrt.comp hL
  -- the first and third terms, bounded by `2^{115} g` and `4 g`
  have t1 : Tendsto (fun D : ℝ => (2 : ℝ) ^ (sigmaC + 15) * (logStar D : ℝ) / logb 2 D)
      atTop (𝓝 0) := by
    have hup := hg.const_mul ((2 : ℝ) ^ (sigmaC + 15))
    rw [mul_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with D hD
      have := Chain.two_le_logb_of_four_le hD
      positivity
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with D hD
      have hy := Chain.two_le_logb_of_four_le hD
      have hls := logStar_le_two_add_loglog hD
      have hll : 0 ≤ logb 2 (logb 2 D) := Real.logb_nonneg (by norm_num) (by linarith)
      have hsq : (logb 2 D) ^ ((1 : ℝ) / 2) ≤ logb 2 D := by
        conv_rhs => rw [← Real.rpow_one (logb 2 D)]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hsq0 : 0 < (logb 2 D) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
      simp only [Function.comp]
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (logStar D : ℝ) / logb 2 D ≤ (6 + 2 * logb 2 (logb 2 D)) / logb 2 D :=
            div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ (6 + 2 * logb 2 (logb 2 D)) / logb 2 D ^ ((1 : ℝ) / 2) :=
            div_le_div_of_nonneg_left (by linarith) hsq0 hsq
  have t3 : Tendsto (fun D : ℝ => 4 * (2 * (logStar D : ℝ) + 2) / logb 2 D ^ ((1 : ℝ) / 2))
      atTop (𝓝 0) := by
    have hup := hg.const_mul 4
    rw [mul_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with D hD
      have := Chain.two_le_logb_of_four_le hD
      positivity
    · filter_upwards [eventually_ge_atTop (4 : ℝ)] with D hD
      have hy := Chain.two_le_logb_of_four_le hD
      have hls := logStar_le_two_add_loglog hD
      have hsq0 : 0 < (logb 2 D) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
      simp only [Function.comp]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith) hsq0.le) (by norm_num)
  have t2 : Tendsto (fun D : ℝ => 200 * epsC * (logStar D : ℝ) /
      ((Cp : ℝ) * logb 2 (logb 2 D))) atTop (𝓝 0) := by
    have h := logStar_isLittleO_loglog.tendsto_div_nhds_zero.const_mul (200 * epsC / (Cp : ℝ))
    rw [mul_zero] at h
    refine h.congr fun D => ?_
    have : (Cp : ℝ) ≠ 0 := by norm_num [Cp]
    field_simp
  have := (t1.add t2).add t3
  rw [add_zero, add_zero] at this
  exact this

/-- `ε_X(D_*) = ε_U + 10.3/D_* + 2.1(6 log₂D_* + 12)/D_* → 0` ([s7:lemEXprime]). -/
theorem Quot.tendsto_epsX : Tendsto Quot.epsX atTop (𝓝 0) := by
  have h1 := Light.tendsto_epsU
  have h2 : Tendsto (fun D : ℝ => 10.3 / D) atTop (𝓝 0) :=
    tendsto_const_div_of_tendsto_atTop _ tendsto_id
  have h3 : Tendsto (fun D : ℝ => 2.1 * (6 * logb 2 D + 12) / D) atTop (𝓝 0) := by
    have a := (tendsto_logb_div_self.const_mul (2.1 * 6)).add
      (tendsto_const_div_of_tendsto_atTop (2.1 * 12) tendsto_id)
    rw [mul_zero, add_zero] at a
    refine a.congr fun D => ?_
    simp only [id]; ring
  have := (h1.add h2).add h3
  rw [add_zero, add_zero] at this
  exact this

/-- `F(x) = (3184 + 30400 log₂ x) x^{-90.2} → 0` as `x → ∞` ([s7:lemUHsplit] (iv)). -/
theorem Quot.tendsto_FQ : Tendsto Quot.FQ atTop (𝓝 0) := by
  have ha : Tendsto (fun x : ℝ => x ^ (-(90.2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hb : Tendsto (fun x : ℝ => x ^ (-(89.2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hup := (ha.const_mul 3184).add (hb.const_mul 60800)
  rw [mul_zero, mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have := Real.logb_nonneg (b := 2) (by norm_num) hx
    unfold Quot.FQ
    have : 0 < x := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog := Light.logb_two_le_two_mul hx0
    have hp : 0 < x ^ (-(90.2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have he : x ^ (-(89.2 : ℝ)) = x ^ (-(90.2 : ℝ)) * x := by
      rw [show (-(89.2 : ℝ)) = -(90.2 : ℝ) + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    unfold Quot.FQ
    rw [he]
    nlinarith

/-- `F(log₂ D_*) → 0` as `D_* → ∞`. -/
theorem Quot.tendsto_FQ_logb : Tendsto (fun D : ℝ => Quot.FQ (logb 2 D)) atTop (𝓝 0) :=
  Quot.tendsto_FQ.comp tendsto_logb_two_atTop

/-- [s7:lemGammaSat] (ii) "`ε_1(D_*) → 0` … as `D_* → ∞`" (`ε_1 = ε_K + 169ε_A + 252/D_* +
1.5ε_CONC + 3ε_X + 9/D_*`, [s7:propCost]). -/
theorem Quot.tendsto_eps1 : Tendsto Quot.eps1 atTop (𝓝 0) := by
  have hK : Tendsto Chain.epsK atTop (𝓝 0) := Light.tendsto_epsChain
  have h := ((((hK.add (tendsto_epsA.const_mul 169)).add
    (tendsto_const_div_of_tendsto_atTop 252 tendsto_id)).add
    (Chain.tendsto_epsCONC.const_mul 1.5)).add (Quot.tendsto_epsX.const_mul 3)).add
    (tendsto_const_div_of_tendsto_atTop 9 tendsto_id)
  simp only [mul_zero, add_zero] at h
  exact h

/-- [s7:lemGammaSat] (ii) "`ε_2(D_*) → 0` as `D_* → ∞`" (`ε_2 = 12ε_X + 4(3ε_A + 60/D_* +
2F(log₂D_*))`, [s7:lemUHsplit] (iv)). -/
theorem Quot.tendsto_eps2 : Tendsto Quot.eps2 atTop (𝓝 0) := by
  have h := (Quot.tendsto_epsX.const_mul 12).add
    ((((tendsto_epsA.const_mul 3).add (tendsto_const_div_of_tendsto_atTop 60 tendsto_id)).add
      (Quot.tendsto_FQ_logb.const_mul 2)).const_mul 4)
  simp only [mul_zero, add_zero] at h
  exact h

end EG
