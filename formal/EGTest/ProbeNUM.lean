import EG.Spec.Num.L17s
import EG.Spec.Num.StarInputs
import EG.Spec.Num.WellDef
import EG.Spec.Num.OV
import EG.Spec.Num.CC
import EG.Lib.Link.Star

/-!
Non-vacuity checks for the Specs of unit NUM (`EG/Spec/Num/*.lean`, design note
`formal/work/p2b/NUM.md`): the hypotheses of the parameter statements are satisfiable on a small
instance, the sums of the SDR statement are not empty and have a positive term, both regimes of
`p_*` in L17* case (b) occur, and the negative control of TRIAGE OV-CONST-546 (the rational bound
`12/29 ≤ log₂(4/3)` is too weak for `5.46`) holds.

The hypothesis `θ_*u < n` of `NumL17sStep0Statement` needs `n > θ_* ≥ 2^{39}`: it holds at
`n = 2^{128}`, `ε' = ρ = u = 1` (`L = 128`, `ℓ_* = 2^{31}`, `θ_* = 2^{102}`; fix round 1, review
I-5, closing hazard NUM-H3).
-/

namespace EGTest.ProbeNUM

open EG Real Finset

/-! ## L17* parameter statements: hypotheses satisfiable at `n = 2`, `ε' = ρ = u = 1` -/

theorem L2 : Star.L 2 = 1 := by
  rw [Star.L]; norm_num

/-- The domain hypotheses of (eqStar) hold at `n = 2`, `ε' = ρ = 1`. -/
example : 2 ≤ (2 : ℕ) ∧ (2 : ℝ) ^ (-7 : ℤ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 := by
  norm_num

/-- Case (a) and case (b) hypotheses: `W := θ_*u`, `C := W/σ_*`, `X := ε'W/(2L^2)`. -/
example (n : ℕ) (ε' ρ : ℝ) :
    ∃ u W C X : ℝ, 1 ≤ u ∧ Star.theta n ε' ρ * u ≤ W ∧ W / Star.sigma n ε' ≤ C ∧
      ε' * W / (2 * Star.L n ^ 2) ≤ X :=
  ⟨1, Star.theta n ε' ρ, Star.theta n ε' ρ / Star.sigma n ε',
    ε' * Star.theta n ε' ρ / (2 * Star.L n ^ 2), le_rfl, by simp, le_rfl, by simp⟩

/-- The regime `p_* > 0.11` of case (b) occurs (`p_* = 1` at `ρ = 1`). -/
example : 0.11 < Star.p 2 1 := by
  rw [Star.p_one le_rfl]; norm_num

/-- The conclusion `18uL ≤ …` of case (b) is not trivial: its left side is positive for
`n ≥ 2`, `u ≥ 1`. -/
example (n : ℕ) (hn : 2 ≤ n) (u : ℝ) (hu : 1 ≤ u) : 0 < 18 * u * Star.L n := by
  have := Star.L_pos hn
  positivity

/-! ## L17* Step 0: hypotheses satisfiable at `n = 2^{128}`, `ε' = ρ = u = 1` -/

theorem L_two_pow : Star.L (2 ^ 128) = 128 := by
  rw [Star.L, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

theorem ell_two_pow : Star.ell (2 ^ 128) = 2 ^ 31 := by
  rw [Star.ell, L_two_pow]
  have : (2 : ℝ) ^ 10 * 128 ^ 3 = ((2 ^ 31 : ℕ) : ℝ) := by norm_num
  rw [this, Nat.floor_natCast]

theorem theta_two_pow : Star.theta (2 ^ 128) 1 1 = 2 ^ 102 := by
  rw [Star.theta, ell_two_pow, L_two_pow]
  norm_num

/-- All hypotheses of `NumL17sStep0Statement` hold at `n = 2^{128}`, `ε' = ρ = u = 1`. -/
example : 2 ≤ (2 ^ 128 : ℕ) ∧ (2 : ℝ) ^ (-7 : ℤ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 ∧
    (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ Star.theta (2 ^ 128) 1 1 * 1 < ((2 ^ 128 : ℕ) : ℝ) := by
  refine ⟨by norm_num, by norm_num, le_rfl, one_pos, le_rfl, le_rfl, ?_⟩
  rw [theta_two_pow]
  norm_num

/-! ## WellDef (iii): hypotheses satisfiable, the sum has a positive term -/

example : 10 ^ 4 ≤ (10000 : ℕ) ∧ ((2500 : ℕ) : ℝ) ≤ ((10000 : ℕ) : ℝ) / 4 := by norm_num

example : (4 : ℕ) ∈ Icc 4 2500 := by simp

/-- `T_4 > 0` for `K = 10^4`, `m = 2500`: the bound is not about an identically zero sum. -/
example : 0 < EG.Spec.numSDRTerm 10000 2500 4 := by
  unfold EG.Spec.numSDRTerm
  have h1 : (0 : ℝ) < (Nat.choose 2500 4 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by norm_num))
  have h2 : (0 : ℝ) < (Nat.choose 10000 (4 - 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by norm_num))
  have h3 : (0 : ℝ) < (Nat.choose (4 - 1) 3 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by norm_num))
  have h4 : (0 : ℝ) < (Nat.choose 10000 3 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (by norm_num))
  exact mul_pos (mul_pos h1 h2) (pow_pos (div_pos h3 h4) _)

/-- The use form: `M = 2^{40}`, `m = M − 1` satisfy its hypotheses. -/
example : 2 ^ 40 ≤ (2 ^ 40 : ℕ) ∧ (2 ^ 40 - 1 : ℕ) ≤ 2 ^ 40 - 1 := by norm_num

/-! ## OV: negative control and hypotheses -/

/-- TRIAGE OV-CONST-546: through the rational bound `12/29` the constant would be
`1.6(1 + 29/12) = 5.4666… > 5.46`, so `12/29` is not enough (while `17/41` is). -/
example : (5.46 : ℝ) < 1.6 * (1 + 29 / 12) := by norm_num

example : (5.46 : ℝ) ≥ 1.6 * (1 + 41 / 17) := by norm_num

/-- The charge-sum statement has satisfiable hypotheses and a nonempty sum. -/
example : (0 : ℝ) < 1 ∧ (0 : ℝ) < Real.logb 2 (4 / 3) := by
  refine ⟨by norm_num, Real.logb_pos (by norm_num) (by norm_num)⟩

/-! ## CC: hypotheses satisfiable -/

example : ∃ (M : ℕ) (n H P S : ℝ), 1 ≤ M ∧ 0 < H ∧ 0 ≤ P ∧ 0 ≤ S ∧ S ≤ 2.74 * n * M ∧ 0 < S :=
  ⟨1, 1, 1, 0, 2.74, le_rfl, by norm_num, le_rfl, by norm_num, by norm_num, by norm_num⟩

/-- `t^CC` at `M = 4` is `⌈2·2⌉ = 4`. -/
example : EG.Quot.tCC 4 = 4 := by
  unfold EG.Quot.tCC
  have : Real.logb 2 ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]; simp
  rw [this]; norm_num

end EGTest.ProbeNUM
