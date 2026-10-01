module

public import EG.Lib.Vortex.Params
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The vortex size conditions hold for all large vertex counts (manuscript s1:defConstants (ii))

Manuscript v6.1, `s1.tex`, Definition [s1:defConstants] (ii): "every other requirement asks that
an explicit inequality in `N`, which holds for all sufficiently large `N`, hold for every
`N ≥ N_0`"; `s4.tex`: "The absolute constant `N_0` … is chosen so large that the finitely many
explicit inequalities listed as *size conditions* in the three proofs of this section hold for
every `N ≥ N_0`".

Required Lib lemma of TRIAGE §3 item 14 (unit GAMMA, design note `formal/work/p2b/GAMMA.md`):
`EG.Vortex.eventually_size : ∀ᶠ N in atTop, TPVSize N ∧ PVSize N ∧ VXSize N`
(the statement `EG.Spec.VortexEventuallySizeStatement`).

Route (asymptotic form of the route of `formal/work/p2d/params.md`): with `L = log₂ N → ∞`,
* (i) `L ≥ 2^{10}` is eventual since `L → ∞`;
* (ii) `L^3 ≤ N` since `L^3/N → 0` (`Real.tendsto_pow_log_div_mul_add_atTop`);
* (iv) every term of each `η` tends to `0`: the terms `L^k N^{-m}` (`m ≥ 1`) are at most `L^k/N`;
  the terms `N L e^{-f}` with `f ≥ 2L` are at most `L e^{-L}`, because `N ≤ e^{L}`
  (`N = 2^L`); the last term of `η_VX`, `L e^{-N/(5000L)}`, is at most `L e^{-L}` once
  `L ≥ 5000` and `N ≥ L^3`. For `η_VX`'s third term, `f = 3L^2/(32 log₂L) ≥ 2L` once
  `log₂ L ≤ 3L/64` (`log = o(id)`). So each `η → 0`, and `η ≤ 1/100` eventually.
No `sorry`.
-/

public section

namespace EG.Vortex

open Filter Topology Real

/-- `L N = log₂ N → ∞`. -/
theorem tendsto_L : Tendsto L atTop atTop :=
  (Real.tendsto_logb_atTop (b := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop

/-- `N ≤ e^{L}` (`N = 2^L` and `log 2 ≤ 1`). -/
theorem natCast_le_exp_L {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) ≤ exp (L N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog : Real.log N = L N * Real.log 2 := by
    rw [L, Real.logb, div_mul_cancel₀ _ hl2.ne']
  have hL := L_nonneg N
  calc (N : ℝ) = exp (Real.log N) := (Real.exp_log hN0).symm
    _ ≤ exp (L N) := by
      apply Real.exp_le_exp.2
      rw [hlog]
      nlinarith

/-- `log₂ᵏ x / x → 0`. -/
theorem tendsto_logb_pow_div (k : ℕ) :
    Tendsto (fun x : ℝ => logb 2 x ^ k / x) atTop (𝓝 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.tendsto_pow_log_div_mul_add_atTop (Real.log 2 ^ k) 0 k (by positivity)
  refine h.congr fun x => ?_
  rw [Real.logb, div_pow, add_zero, div_div, mul_comm]

/-- `L^k / N → 0`. -/
theorem tendsto_L_pow_div (k : ℕ) :
    Tendsto (fun N : ℕ => L N ^ k / (N : ℝ)) atTop (𝓝 0) :=
  (tendsto_logb_pow_div k).comp tendsto_natCast_atTop_atTop

/-- `L^k N^{-m} → 0` for `m ≥ 1`. -/
theorem tendsto_L_pow_mul_zpow (k m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => L N ^ k * (N : ℝ) ^ (-(m : ℤ))) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_L_pow_div k)
    ?_ ?_
  · filter_upwards with N
    have := L_nonneg N
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hLk : 0 ≤ L N ^ k := pow_nonneg (L_nonneg N) k
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    gcongr
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ m := pow_le_pow_right₀ hN1 hm

/-- `L e^{-L} → 0`. -/
theorem tendsto_L_mul_exp_neg_L : Tendsto (fun N : ℕ => L N * exp (-L N)) atTop (𝓝 0) :=
  ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_L).congr fun N => by
    simp [Function.comp]

/-- `N L e^{-f(N)} → 0` whenever eventually `f(N) ≥ 2L`. -/
theorem tendsto_mul_L_mul_exp_neg {f : ℕ → ℝ} (hf : ∀ᶠ N in atTop, 2 * L N ≤ f N) :
    Tendsto (fun N : ℕ => (N : ℝ) * L N * exp (-f N)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_L_mul_exp_neg_L
    ?_ ?_
  · filter_upwards with N
    have := L_nonneg N
    positivity
  · filter_upwards [hf, eventually_ge_atTop 1] with N hfN hN
    have hL := L_nonneg N
    calc (N : ℝ) * L N * exp (-f N) ≤ exp (L N) * L N * exp (-f N) := by
          gcongr; exact natCast_le_exp_L hN
      _ = L N * exp (L N + -f N) := by rw [Real.exp_add]; ring
      _ ≤ L N * exp (-L N) := by gcongr; linarith

/-- Eventually `L ≥ c`. -/
theorem eventually_L_ge (c : ℝ) : ∀ᶠ N : ℕ in atTop, c ≤ L N :=
  tendsto_L.eventually (eventually_ge_atTop c)

/-- Size condition (ii): eventually `L^3 ≤ N`. -/
theorem eventually_L_cube_le : ∀ᶠ N : ℕ in atTop, L N ^ 3 ≤ (N : ℝ) := by
  filter_upwards [(tendsto_L_pow_div 3).eventually (eventually_le_nhds (zero_lt_one' ℝ)),
    eventually_ge_atTop 1] with N h hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rwa [div_le_one hN0] at h

/-- `log₂ y ≤ 3y/64` for all large real `y`. -/
theorem eventually_logb_le : ∀ᶠ y : ℝ in atTop, logb 2 y ≤ 3 * y / 64 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.isLittleO_log_id_atTop.bound (c := 3 * Real.log 2 / 64) (by positivity)
  filter_upwards [hb, eventually_gt_atTop 0] with y h hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hy] at h
  rw [Real.logb, div_le_iff₀ hl2]
  have := le_abs_self (Real.log y)
  nlinarith

/-- `η_TPV(N) → 0`. -/
theorem tendsto_etaTPV : Tendsto etaTPV atTop (𝓝 0) := by
  have t1 := (tendsto_L_pow_mul_zpow 1 5 (by norm_num)).const_mul 2
  have t2 := (tendsto_L_pow_mul_zpow 31 3 (by norm_num)).const_mul ((2 : ℝ) ^ 96)
  have t3 := tendsto_mul_L_mul_exp_neg (f := fun N => 3 * L N ^ 4 / 8) (by
    filter_upwards [eventually_L_ge 2] with N hN
    nlinarith [pow_le_pow_left₀ (by norm_num) hN 3])
  have := (t1.add t2).add t3
  simp only [mul_zero, add_zero] at this
  refine this.congr fun N => ?_
  simp only [etaTPV]
  push_cast
  ring

/-- `η_PV(N) → 0`. -/
theorem tendsto_etaPV : Tendsto etaPV atTop (𝓝 0) := by
  have t2 := (tendsto_L_pow_mul_zpow 31 3 (by norm_num)).const_mul ((2 : ℝ) ^ 95)
  have t3 := tendsto_mul_L_mul_exp_neg (f := fun N => L N ^ 4 / 16) (by
    filter_upwards [eventually_L_ge 4] with N hN
    nlinarith [pow_le_pow_left₀ (by norm_num) hN 3])
  have := t2.add t3
  simp only [mul_zero, add_zero] at this
  refine this.congr fun N => ?_
  simp only [etaPV]
  push_cast
  ring

/-- `η_VX(N) → 0`. -/
theorem tendsto_etaVX : Tendsto etaVX atTop (𝓝 0) := by
  have t1 := (tendsto_L_pow_mul_zpow 1 5 (by norm_num)).const_mul 2
  have t2 := (tendsto_L_pow_mul_zpow 28 3 (by norm_num)).const_mul ((2 : ℝ) ^ 95)
  have t3 := tendsto_mul_L_mul_exp_neg (f := fun N => 3 * L N ^ 2 / (32 * logb 2 (L N))) (by
    filter_upwards [eventually_L_ge 2, tendsto_L.eventually eventually_logb_le] with N hN hlog
    have hl : 1 ≤ logb 2 (L N) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hN
    rw [le_div_iff₀ (by linarith)]
    nlinarith)
  have t4 : Tendsto (fun N : ℕ => L N * exp (-((N : ℝ) / (5000 * L N)))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      tendsto_L_mul_exp_neg_L ?_ ?_
    · filter_upwards with N
      have := L_nonneg N
      positivity
    · filter_upwards [eventually_L_ge 5000, eventually_L_cube_le] with N hN hcube
      have hL0 : 0 < L N := by linarith
      gcongr
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hN (sq_nonneg (L N))]
  have := ((t1.add t2).add t3).add t4
  simp only [mul_zero, add_zero] at this
  refine this.congr fun N => ?_
  simp only [etaVX]
  push_cast
  ring

/-- [s1:defConstants] (ii) "every other requirement asks that an explicit inequality in `N`,
which holds for all sufficiently large `N`, hold for every `N ≥ N_0`": the size conditions (i),
(ii), (iv) of the proofs of Lemma s4:lemTPV, Lemma s4:lemPV and Theorem s4:thmVXp hold for all
sufficiently large vertex counts `N` (TRIAGE §3 item 14, required Lib lemma). -/
theorem eventually_size : ∀ᶠ N : ℕ in atTop, TPVSize N ∧ PVSize N ∧ VXSize N := by
  have e := fun (f : ℕ → ℝ) (h : Tendsto f atTop (𝓝 0)) =>
    h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  filter_upwards [eventually_L_ge ((2 : ℝ) ^ 10), eventually_L_cube_le, e _ tendsto_etaTPV,
    e _ tendsto_etaPV, e _ tendsto_etaVX] with N h1 h2 h3 h4 h5
  exact ⟨⟨h1, h2, h3⟩, ⟨h1, h2, h4⟩, ⟨h1, h2, h5⟩⟩

end EG.Vortex
