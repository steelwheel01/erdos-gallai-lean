module

public import EG.Spec.Light.ParentRun
public import EG.Lib.Found.Gamma
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proof of the `η` claim of Lemma parent side (s5:lemParent, Step 9)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.etaHalving`
(`EtaHalvingStatement`): "`η` is non-increasing on `[log₂D_*, ∞)` and `η(2^{x/A}) ≤ η(x)/2`
there", with `η(x) = log₂(2A log₂(A log₂ x))/(log₂ x)^2`.

The monotonicity is proved without derivatives (the TeX differentiates `ln η` in `x_1 = log₂ x`):
for `2^8 ≤ a ≤ b = a t` one has `log₂(Ab) = u + log₂ t ≤ u t` (`u = log₂(Aa) ≥ 3/2`,
`log₂ t ≤ (3/2)(t − 1)`), hence `g(b) ≤ g(a) + log₂ t ≤ g(a) t` for `g(x_1) = log₂(2A log₂(A x_1))`
(`g(a) ≥ 3/2`), and `g(b)/b^2 ≤ g(a) t/(a^2 t^2) ≤ g(a)/a^2`. The halving follows the TeX:
`η(2^{x/A}) = A^2 log₂(2A x_1)/x^2` and `2A^2 x_1^2 log₂(2A x_1) ≤ (2^{14} A x_1^3)^2 ≤ 2^{2x_1} = x^2`
(Γ1 (b) at `x_1`). Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

namespace EtaAux

open Real

/-- `log₂ t ≤ (3/2)(t − 1)` for `t > 0` (`log t ≤ t − 1`, `log 2 > 2/3`). -/
theorem logb_le_three_halves {t : ℝ} (ht : 0 < t) (h1 : 1 ≤ t) : logb 2 t ≤ 3 / 2 * (t - 1) := by
  have hl2 : (0.6931471803 : ℝ) < log 2 := Real.log_two_gt_d9
  have hlt := Real.log_le_sub_one_of_pos ht
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- `log₂ x ≥ 2` for `x ≥ 4`. -/
theorem two_le_logb {x : ℝ} (hx : 4 ≤ x) : 2 ≤ logb 2 x := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
  norm_num; exact hx

/-- The function `f(x_1) = log₂(2A log₂(A x_1))/x_1^2`; `η(x) = f(log₂ x)`. -/
noncomputable def f (x1 : ℝ) : ℝ :=
  logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * x1)) / x1 ^ 2

theorem etaCh_eq (x : ℝ) : Light.etaCh x = f (logb 2 x) := by
  unfold Light.etaCh f; rfl

theorem A_eq : (Aexp : ℝ) = 105 := by norm_num [Aexp]

/-- `f` is non-increasing on `[2^8, ∞)`. -/
theorem f_anti {a b : ℝ} (ha : (2 : ℝ) ^ 8 ≤ a) (hab : a ≤ b) : f b ≤ f a := by
  have hA := A_eq
  have ha0 : 0 < a := by linarith [show (0 : ℝ) < 2 ^ 8 by norm_num]
  set t := b / a with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ ha0]; linarith
  have ht0 : 0 < t := by linarith
  have hb : b = a * t := by rw [ht]; field_simp
  -- u = log₂(Aa) ≥ 2
  set u := logb 2 ((Aexp : ℝ) * a) with hu
  have hu2 : 2 ≤ u := two_le_logb (by rw [hA]; nlinarith)
  have hAb : logb 2 ((Aexp : ℝ) * b) = u + logb 2 t := by
    rw [hb, ← mul_assoc, Real.logb_mul (by rw [hA]; positivity) ht0.ne']
  have hlt := logb_le_three_halves ht0 ht1
  have hAb' : logb 2 ((Aexp : ℝ) * b) ≤ u * t := by rw [hAb]; nlinarith
  have hAbpos : 0 < logb 2 ((Aexp : ℝ) * b) := by
    rw [hAb]; have := Real.logb_nonneg (b := 2) (by norm_num) ht1; linarith
  -- g(a) = log₂(2Au) ≥ 2
  set g := logb 2 (2 * (Aexp : ℝ) * u) with hg
  have hg2 : 2 ≤ g := two_le_logb (by rw [hA]; nlinarith)
  have hgb : logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * b)) ≤ g * t := by
    calc logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * b))
        ≤ logb 2 (2 * (Aexp : ℝ) * (u * t)) :=
          Real.logb_le_logb_of_le (by norm_num) (by rw [hA]; positivity)
            (mul_le_mul_of_nonneg_left hAb' (by rw [hA]; positivity))
      _ = g + logb 2 t := by
          rw [← mul_assoc, Real.logb_mul (by rw [hA]; positivity) ht0.ne']
      _ ≤ g * t := by nlinarith
  unfold f
  rw [← hu, ← hg, div_le_div_iff₀ (pow_pos (ha0.trans_le hab) 2) (by positivity)]
  have hb2 : b ^ 2 = a ^ 2 * t ^ 2 := by rw [hb]; ring
  have htt : t ≤ t ^ 2 := by nlinarith
  have hga : 0 ≤ g * a ^ 2 := by positivity
  calc logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * b)) * a ^ 2 ≤ g * t * a ^ 2 :=
        mul_le_mul_of_nonneg_right hgb (by positivity)
    _ = g * a ^ 2 * t := by ring
    _ ≤ g * a ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_left htt hga
    _ = g * b ^ 2 := by rw [hb2]; ring

end EtaAux

open EtaAux Real

/-- [s5:lemParent] Step 9: "We claim that `η` is non-increasing on `[log₂D_*, ∞)` and that
`η(2^{x/A}) ≤ η(x)/2` there." -/
theorem etaHalving : EG.Spec.EtaHalvingStatement := by
  intro Dstar hΓ
  have hA := A_eq
  have hL := hΓ.1.two_pow_256_le_logb
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    have ha0 : 0 < a := by linarith [show (0 : ℝ) < 2 ^ 256 by norm_num]
    have h8 : (2 : ℝ) ^ 8 ≤ logb 2 a := (hΓ.1.items_logb_of_le ha).a
    rw [etaCh_eq, etaCh_eq]
    exact f_anti h8 (Real.logb_le_logb_of_le (by norm_num) ha0 hab)
  · intro x hx
    have hx0 : 0 < x := by linarith [show (0 : ℝ) < 2 ^ 256 by norm_num]
    have hit := hΓ.1.items_logb_of_le hx
    have h8 : (2 : ℝ) ^ 8 ≤ logb 2 x := hit.a
    have hb : (2 : ℝ) ^ 14 * (Aexp : ℝ) * logb 2 x ^ 3 ≤ x := by
      have := hit.b
      unfold Gamma1b at this
      rw [Real.rpow_logb (by norm_num) (by norm_num) hx0] at this
      exact this
    have hlog : logb 2 ((2 : ℝ) ^ (x / (Aexp : ℝ))) = x / (Aexp : ℝ) := by
      rw [Real.logb_rpow (by norm_num) (by norm_num)]
    have hAx : (Aexp : ℝ) * (x / (Aexp : ℝ)) = x := by rw [hA]; field_simp
    rw [etaCh_eq, etaCh_eq, hlog]
    unfold f
    rw [hAx]
    rw [hA] at hb ⊢
    generalize logb 2 x = x1 at h8 hb ⊢
    have hx1pos : 0 < x1 := by linarith [show (0 : ℝ) < 2 ^ 8 by norm_num]
    have hu2 : 2 ≤ logb 2 (105 * x1) := two_le_logb (by nlinarith)
    have hg2 : 2 ≤ logb 2 (2 * 105 * logb 2 (105 * x1)) := two_le_logb (by nlinarith)
    have hl : logb 2 (2 * 105 * x1) ≤ 3 / 2 * (2 * 105 * x1 - 1) :=
      logb_le_three_halves (by positivity) (by nlinarith)
    have hxA : 2 ^ 14 * x1 ^ 3 ≤ x / 105 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have hx3 : 0 < x1 ^ 3 := by positivity
    have hsq : (2 ^ 14 * x1 ^ 3) ^ 2 ≤ (x / 105) ^ 2 := pow_le_pow_left₀ (by positivity) hxA 2
    have key : logb 2 (2 * 105 * x1) * (x1 ^ 2 * 2) ≤ (x / 105) ^ 2 := by
      have h1 : logb 2 (2 * 105 * x1) * (x1 ^ 2 * 2) ≤ 315 * x1 * (x1 ^ 2 * 2) :=
        mul_le_mul_of_nonneg_right (hl.trans (by linarith)) (by positivity)
      have h2 : 315 * x1 * (x1 ^ 2 * 2) ≤ (2 ^ 14 * x1 ^ 3) ^ 2 := by
        have h1' : (1 : ℝ) ≤ x1 := by linarith [show (1 : ℝ) ≤ 2 ^ 8 by norm_num]
        have hx13 : 1 ≤ x1 ^ 3 := one_le_pow₀ h1'
        have hsq3 : x1 ^ 3 ≤ x1 ^ 3 * x1 ^ 3 := by nlinarith
        calc 315 * x1 * (x1 ^ 2 * 2) = 630 * x1 ^ 3 := by ring
          _ ≤ 630 * (x1 ^ 3 * x1 ^ 3) := by linarith
          _ ≤ 2 ^ 28 * (x1 ^ 3 * x1 ^ 3) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = (2 ^ 14 * x1 ^ 3) ^ 2 := by ring
      exact h1.trans (h2.trans hsq)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hq : 0 ≤ (x / 105) ^ 2 := sq_nonneg _
    exact key.trans (le_mul_of_one_le_left hq (by linarith))

end EG
