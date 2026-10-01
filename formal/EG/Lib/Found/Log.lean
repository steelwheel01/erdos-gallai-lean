module

public import EG.Defs.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# API for `logIter`, `tower` and `logStar` (manuscript s1:convGraphs (b), s2:lemLacunary)

* `logIter`: `logIter_zero`, `logIter_succ` (`log^{[k+1]} x = log^{[k]}(log x)`),
  `logIter_succ'` (`= log(log^{[k]} x)`), `logIter_one`;
* `tower`: `tower_zero`, `tower_succ`, `one_le_tower`, `tower_pos`, `logb_tower_succ`,
  `logIter_tower` (`log^{[j]} tw(j) = 1`), `le_tower_self` (`k ≤ tw(k)`),
  `exists_le_tower`;
* `logStar`: `exists_logIter_le_one` (the defining set is non-empty), `logIter_logStar_le_one`,
  `one_lt_logIter_of_lt_logStar`, `logStar_le_of_logIter_le_one`, `logStar_eq_zero_iff`,
  `logStar_of_one_lt` (`log* x = 1 + log*(log x)` for `x > 1`), `logStar_le_iff_le_tower`
  (`log* x ≤ k ↔ x ≤ tw(k)`), `logStar_tower`, `logStar_two_rpow`, `logStar_mono`,
  `logStar_le_self` (`log* z ≤ z` for `z ≥ 1`, proof of s2:lemLacunary(iv)),
  `logStar_le_one_add_logb` (`log* x ≤ 1 + log x` for `x ≥ 1`, s6.tex:262);
* growth: `logStar_eq_two_add`, `logStar_le_two_add_loglog` (`log* y ≤ 2 + log log y` for
  `y ≥ 4`, sharper than `logStar_le_one_add_logb` for large `y`), `logStar_le_three_add_logloglog`,
  `logStar_isLittleO_loglog` (`log* = o(log log)`).
-/

public section


namespace EG

open Real

/-! ### Iterated logarithms -/

@[simp] theorem logIter_zero (x : ℝ) : logIter 0 x = x := rfl

theorem logIter_succ (k : ℕ) (x : ℝ) : logIter (k + 1) x = logIter k (logb 2 x) :=
  Function.iterate_succ_apply _ _ _

theorem logIter_succ' (k : ℕ) (x : ℝ) : logIter (k + 1) x = logb 2 (logIter k x) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem logIter_one (x : ℝ) : logIter 1 x = logb 2 x := rfl

/-! ### The tower function -/

@[simp] theorem tower_zero : tower 0 = 1 := rfl

theorem tower_succ (j : ℕ) : tower (j + 1) = (2 : ℝ) ^ tower j := rfl

theorem one_le_tower : ∀ j, 1 ≤ tower j
  | 0 => le_rfl
  | j + 1 => by
      rw [tower_succ]
      exact Real.one_le_rpow (by norm_num) (zero_le_one.trans (one_le_tower j))

theorem tower_pos (j : ℕ) : 0 < tower j := zero_lt_one.trans_le (one_le_tower j)

theorem logb_tower_succ (j : ℕ) : logb 2 (tower (j + 1)) = tower j := by
  rw [tower_succ, Real.logb_rpow (by norm_num) (by norm_num)]

/-- "`log^{[j]} tw(j) = 1`" (proof of s2:lemLacunary(iv)). -/
theorem logIter_tower : ∀ j, logIter j (tower j) = 1
  | 0 => rfl
  | j + 1 => by rw [logIter_succ, logb_tower_succ, logIter_tower j]

/-- `y + 1 ≤ 2^y` for `y ≥ 1` (Bernoulli). -/
theorem add_one_le_two_rpow {y : ℝ} (hy : 1 ≤ y) : y + 1 ≤ (2 : ℝ) ^ y := by
  have := one_add_mul_self_le_rpow_one_add (s := 1) (by norm_num) hy
  norm_num at this
  linarith

/-- `2^{y-1} ≥ y` for `y ≥ 2`, i.e. `log₂ y ≤ y - 1`. -/
theorem logb_le_sub_one {y : ℝ} (hy : 2 ≤ y) : logb 2 y ≤ y - 1 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]
  have := add_one_le_two_rpow (y := y - 1) (by linarith)
  linarith

theorem le_tower_self : ∀ k : ℕ, (k : ℝ) + 1 ≤ tower k
  | 0 => by simp
  | k + 1 => by
      rw [tower_succ]
      have h := le_tower_self k
      have := add_one_le_two_rpow (y := tower k) (one_le_tower k)
      push_cast
      linarith

theorem exists_le_tower (x : ℝ) : ∃ k, x ≤ tower k := by
  obtain ⟨k, hk⟩ := exists_nat_ge x
  exact ⟨k, hk.trans ((le_add_of_nonneg_right zero_le_one).trans (le_tower_self k))⟩

/-! ### `log*` -/

theorem exists_logIter_le_one_of_le_tower : ∀ (k : ℕ) (x : ℝ), x ≤ tower k →
    ∃ j, logIter j x ≤ 1
  | 0, x, hx => ⟨0, hx⟩
  | k + 1, x, hx => by
      by_cases h1 : x ≤ 1
      · exact ⟨0, h1⟩
      · rw [not_le] at h1
        have hlog : logb 2 x ≤ tower k := by
          rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]
          exact hx
        obtain ⟨j, hj⟩ := exists_logIter_le_one_of_le_tower k _ hlog
        exact ⟨j + 1, by rwa [logIter_succ]⟩

/-- Every real number has an iterated logarithm `≤ 1`: the set in `EG.logStar` is non-empty. -/
theorem exists_logIter_le_one (x : ℝ) : ∃ k, logIter k x ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_le_tower x
  exact exists_logIter_le_one_of_le_tower k x hk

theorem logIter_logStar_le_one (x : ℝ) : logIter (logStar x) x ≤ 1 :=
  Nat.sInf_mem (exists_logIter_le_one x)

theorem logStar_le_of_logIter_le_one {x : ℝ} {k : ℕ} (h : logIter k x ≤ 1) : logStar x ≤ k :=
  Nat.sInf_le h

theorem one_lt_logIter_of_lt_logStar {x : ℝ} {k : ℕ} (h : k < logStar x) : 1 < logIter k x :=
  lt_of_not_ge fun h' => absurd (logStar_le_of_logIter_le_one h') (not_le.2 h)

@[simp] theorem logStar_eq_zero_iff {x : ℝ} : logStar x = 0 ↔ x ≤ 1 := by
  constructor
  · intro h
    have := logIter_logStar_le_one x
    rwa [h] at this
  · intro h
    exact Nat.le_zero.1 (logStar_le_of_logIter_le_one (k := 0) h)

/-- "if `z > 2` then `log* z = 1 + log*(log z)`" (proof of s2:lemLacunary(iv)); valid for every
`x > 1`. -/
theorem logStar_of_one_lt {x : ℝ} (hx : 1 < x) : logStar x = logStar (logb 2 x) + 1 := by
  apply le_antisymm
  · apply logStar_le_of_logIter_le_one
    rw [logIter_succ]
    exact logIter_logStar_le_one _
  · have hne : logStar x ≠ 0 := fun h => absurd (logStar_eq_zero_iff.1 h) (not_le.2 hx)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have h := logIter_logStar_le_one x
    rw [hj, logIter_succ] at h
    rw [hj]
    exact Nat.succ_le_succ (logStar_le_of_logIter_le_one h)

/-- "a real `z > 1` has `log* z = j` iff `tw(j-1) < z ≤ tw(j)`" (proof of s2:lemLacunary(iv)),
in the form `log* x ≤ k ↔ x ≤ tw(k)` (valid for every real `x`). -/
theorem logStar_le_iff_le_tower : ∀ (k : ℕ) (x : ℝ), logStar x ≤ k ↔ x ≤ tower k
  | 0, x => by simp
  | k + 1, x => by
      by_cases h1 : x ≤ 1
      · have : logStar x = 0 := logStar_eq_zero_iff.2 h1
        exact ⟨fun _ => h1.trans (one_le_tower _), fun _ => by omega⟩
      · rw [not_le] at h1
        rw [logStar_of_one_lt h1, Nat.add_le_add_iff_right, logStar_le_iff_le_tower k,
          tower_succ, Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]

theorem lt_logStar_iff_tower_lt (k : ℕ) (x : ℝ) : k < logStar x ↔ tower k < x := by
  rw [← not_le, logStar_le_iff_le_tower, not_le]

theorem logStar_tower (k : ℕ) : logStar (tower k) = k := by
  apply le_antisymm ((logStar_le_iff_le_tower k _).2 le_rfl)
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
      rw [Nat.succ_le_iff, lt_logStar_iff_tower_lt, tower_succ]
      have := add_one_le_two_rpow (one_le_tower k)
      linarith

theorem logStar_mono {x y : ℝ} (h : x ≤ y) : logStar x ≤ logStar y :=
  (logStar_le_iff_le_tower _ x).2 (h.trans ((logStar_le_iff_le_tower _ y).1 le_rfl))

/-- `log*(2^y) = log* y + 1` for `y > 0`. -/
theorem logStar_two_rpow {y : ℝ} (hy : 0 < y) : logStar ((2 : ℝ) ^ y) = logStar y + 1 := by
  rw [logStar_of_one_lt (Real.one_lt_rpow (by norm_num) hy),
    Real.logb_rpow (by norm_num) (by norm_num)]

/-- "`log* z ≤ z` for `z ≥ 1`" (proof of s2:lemLacunary(iv)). -/
theorem logStar_le_self {z : ℝ} (hz : 1 ≤ z) : (logStar z : ℝ) ≤ z := by
  obtain ⟨k, hk⟩ := exists_le_tower z
  induction k generalizing z with
  | zero =>
      have : logStar z = 0 := logStar_eq_zero_iff.2 hk
      simp only [this, Nat.cast_zero]
      linarith
  | succ k ih =>
      by_cases h2 : z ≤ 2
      · have : logStar z ≤ 1 := (logStar_le_iff_le_tower 1 z).2 (by
          rw [tower_succ, tower_zero]; norm_num; exact h2)
        have : (logStar z : ℝ) ≤ 1 := by exact_mod_cast this
        linarith
      · rw [not_le] at h2
        have hl1 : 1 ≤ logb 2 z := by
          rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
          norm_num; linarith
        have hlk : logb 2 z ≤ tower k := by
          rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]
          exact hk
        have := ih hl1 hlk
        rw [logStar_of_one_lt (by linarith)]
        push_cast
        have := logb_le_sub_one h2.le
        linarith

/-- [s6, the `log*` facts after s6:defDesign] "`log* x ≤ 1 + log x` for all `x ≥ 1`"
(`log = log₂`). -/
theorem logStar_le_one_add_logb {x : ℝ} (hx : 1 ≤ x) : (logStar x : ℝ) ≤ 1 + logb 2 x := by
  rcases hx.eq_or_lt with h1 | h1
  · subst h1
    have : logStar 1 = 0 := logStar_eq_zero_iff.2 le_rfl
    simp [this]
  · have hl0 : 0 < logb 2 x := Real.logb_pos (by norm_num) h1
    rw [logStar_of_one_lt h1]
    push_cast
    by_cases hl1 : 1 ≤ logb 2 x
    · linarith [logStar_le_self hl1]
    · have : logStar (logb 2 x) = 0 := logStar_eq_zero_iff.2 (le_of_not_ge hl1)
      rw [this]
      push_cast
      linarith

/-! ### Growth of `log*` -/

section Growth

open Filter Asymptotics

/-- `log* y = log*(log₂log₂ y) + 2` for `y ≥ 4`. -/
theorem logStar_eq_two_add {y : ℝ} (hy : 4 ≤ y) :
    logStar y = logStar (logb 2 (logb 2 y)) + 2 := by
  have h2 : (2 : ℝ) ≤ logb 2 y := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact hy
  rw [logStar_of_one_lt (by linarith), logStar_of_one_lt (by linarith)]

/-- `log* y ≤ 2 + log₂log₂ y` for `y ≥ 4` (sharper form of TRIAGE §2.3 `logStar_le_one_add_log`,
which is `logStar_le_one_add_logb`). -/
theorem logStar_le_two_add_loglog {y : ℝ} (hy : 4 ≤ y) :
    (logStar y : ℝ) ≤ 2 + logb 2 (logb 2 y) := by
  have h2 : (2 : ℝ) ≤ logb 2 y := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact hy
  have h1 : (1 : ℝ) ≤ logb 2 (logb 2 y) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact h2
  rw [logStar_eq_two_add hy]
  push_cast
  linarith [logStar_le_self h1]

/-- `log* y ≤ 3 + log₂log₂log₂ y` for `y ≥ 16`. -/
theorem logStar_le_three_add_logloglog {y : ℝ} (hy : 16 ≤ y) :
    (logStar y : ℝ) ≤ 3 + logb 2 (logb 2 (logb 2 y)) := by
  have h4 : (4 : ℝ) ≤ logb 2 y := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact hy
  have h2 : (2 : ℝ) ≤ logb 2 (logb 2 y) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact h4
  have h := logStar_le_self (z := logb 2 (logb 2 (logb 2 y))) (by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact h2)
  rw [logStar_eq_two_add (by linarith), logStar_of_one_lt (by linarith)]
  push_cast
  linarith

/-- TRIAGE §2.3, the growth fact `log* = o(log log)` (used for s2:lemLacunary(iv), s6 CONC). -/
theorem logStar_isLittleO_loglog :
    (fun y : ℝ => (logStar y : ℝ)) =o[atTop] (fun y => logb 2 (logb 2 y)) := by
  have hL : Tendsto (fun y : ℝ => logb 2 (logb 2 y)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp (Real.tendsto_logb_atTop (by norm_num))
  have hlog : (fun z : ℝ => logb 2 z) =o[atTop] (fun z => z) := by
    have : (fun z : ℝ => logb 2 z) = fun z => (Real.log 2)⁻¹ * Real.log z := by
      funext z; rw [Real.logb, div_eq_inv_mul]
    rw [this]
    exact Real.isLittleO_log_id_atTop.const_mul_left _
  have h3 : (fun z : ℝ => 3 + logb 2 z) =o[atTop] (fun z => z) :=
    (isLittleO_const_id_atTop (3 : ℝ)).add hlog
  have hc := h3.comp_tendsto hL
  refine IsBigO.trans_isLittleO ?_ hc
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with y hy
  have h4 : (4 : ℝ) ≤ logb 2 y := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact hy
  have h2 : (2 : ℝ) ≤ logb 2 (logb 2 y) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; exact h4
  have h0 : (0 : ℝ) ≤ logb 2 (logb 2 (logb 2 y)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  simp only [Function.comp, one_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
  exact logStar_le_three_add_logloglog hy

end Growth

end EG
