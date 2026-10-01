module

public import EG.Spec.HB.Cap
public import EG.Proof.Ext.BMLemma25
public import EG.Lib.Found.LogMono
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Proof of the Lemma-25 size cap (manuscript s2:lemCap, part (i), remark, core of (ii))

* `EG.cap : EG.Spec.CapStatement` ([s2:lemCap] (i)), complete;
* `EG.cap_uniform : EG.Spec.CapUniformStatement` (the remark's uniform form), complete;
* `EG.cap_remark_counterexample` (the remark's numbers `T = 2^{20}`, `m = 2^{55}`);
* `EG.cap_graph : EG.Spec.CapGraphStatement` (graph-level step of (ii)), from (i) and
  `EG.bmLemma25` ([s1:citLem25], currently `sorry`).

Proof of (i), as in the manuscript. Put `χ(y) = y / log⁴ y`; it is non-decreasing for `y ≥ e^4`
(`EG.div_logb_pow_le_div_logb_pow`). With `x = log T ≥ 117` and `B = 2^{16} T x^4` we have
`log B = 16 + x + 4 log x ≤ c x` for `c = 1.37317` (`EG.cap_numeric`; the manuscript's
`0.37317 x ≥ 16 + 4 log x`), and `18432 c^4 ≤ 2^{16}` (`c ≤ (32/9)^{1/4}`), so `χ(B) ≥ 18432 T`.
If `m > B` then `χ(m) ≥ χ(B) ≥ 18432 T`, contradicting `m < 18432 T log⁴ m`
(`EG.cap_core`). The hypothesis `m ≥ 2^{40}` is not needed (`EG.cap_of_T_ge` omits it).
The numerical bound uses `log₂ 117 ≤ 55/8` (`117^8 ≤ 2^{55}`), concavity of `log`
(`EG.logb_sub_logb_le`) and `ln 2 > 0.6931471803` (`Real.log_two_gt_d9`).
-/

public section


namespace EG

universe u

/-- The core of [s2:lemCap] (i): if `B ≥ 2^{16}` satisfies `χ(B) ≥ 18432 T`
(written `18432 T log⁴ B ≤ B`) and `m < 18432 T log⁴ m`, then `m ≤ B`. -/
theorem cap_core {m T B : ℝ} (hB : 2 ^ 16 ≤ B)
    (hχB : 18432 * T * Real.logb 2 B ^ 4 ≤ B) (hm : m < 18432 * T * Real.logb 2 m ^ 4) :
    m ≤ B := by
  by_contra hlt
  rw [not_le] at hlt
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hlogB : ((4 : ℕ) : ℝ) ≤ Real.log B := by
    have h1 : Real.log ((2 : ℝ) ^ 16) ≤ Real.log B := Real.log_le_log (by norm_num) hB
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1 ⊢
    linarith
  have hmono := div_logb_pow_le_div_logb_pow one_lt_two hB0 hlogB hlt.le
  have hlB : 0 < Real.logb 2 B := Real.logb_pos one_lt_two (by linarith)
  have hlm : 0 < Real.logb 2 m := Real.logb_pos one_lt_two (by linarith)
  have h1 : 18432 * T ≤ B / Real.logb 2 B ^ 4 := by
    rw [le_div_iff₀ (pow_pos hlB 4)]; linarith
  have h2 : m / Real.logb 2 m ^ 4 < 18432 * T := by
    rw [div_lt_iff₀ (pow_pos hlm 4)]; linarith
  linarith

/-- `log₂ 117 ≤ 55/8`, since `117^8 ≤ 2^{55}`. -/
theorem logb_two_117_le : Real.logb 2 117 ≤ 55 / 8 := by
  have h : Real.logb 2 ((117 : ℝ) ^ 8) ≤ Real.logb 2 ((2 : ℝ) ^ 55) :=
    Real.logb_le_logb_of_le one_lt_two (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two] at h
  push_cast at h
  linarith

/-- `log₂ 40 ≤ 6`, since `40 ≤ 2^6`. -/
theorem logb_two_40_le : Real.logb 2 40 ≤ 6 := by
  have h : Real.logb 2 (40 : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ 6) :=
    Real.logb_le_logb_of_le one_lt_two (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two] at h
  push_cast at h
  linarith

/-- The numerical inequality of [s2:lemCap] (i): for `x ≥ 117`,
`16 + x + 4 log x ≤ 1.37317 x` (the manuscript's `0.37317 x ≥ 16 + 4 log x`). -/
theorem cap_numeric {x : ℝ} (hx : 117 ≤ x) :
    16 + x + 4 * Real.logb 2 x ≤ 137317 / 100000 * x := by
  have h1 := logb_sub_logb_le (c := 2) one_lt_two (by norm_num : (0 : ℝ) < 117)
    (by linarith : (0 : ℝ) < x)
  have h2 := logb_two_117_le
  have hL := Real.log_two_gt_d9
  have h3 : (x - 117) / (117 * Real.log 2) ≤ (x - 117) / 80 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  linarith

/-- The numerical inequality of the uniform form: for `x ≥ 0`,
`16 + x + 4 log (x + 40) ≤ 1.37317 (x + 40)` (the manuscript's
`0.37317 x + 38.9 ≥ 4 log (x + 40)`). -/
theorem cap_numeric_uniform {x : ℝ} (hx : 0 ≤ x) :
    16 + x + 4 * Real.logb 2 (x + 40) ≤ 137317 / 100000 * (x + 40) := by
  have h1 := logb_sub_logb_le (c := 2) one_lt_two (by norm_num : (0 : ℝ) < 40)
    (by linarith : (0 : ℝ) < x + 40)
  have h2 := logb_two_40_le
  have hL := Real.log_two_gt_d9
  have h3 : (x + 40 - 40) / (40 * Real.log 2) ≤ (x + 40 - 40) / 27 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  linarith

/-- `18432 · 1.37317⁴ ≤ 2^{16}`, i.e. `1.37317 ≤ (32/9)^{1/4}`. -/
theorem cap_const : (18432 : ℝ) * (137317 / 100000) ^ 4 ≤ 2 ^ 16 := by norm_num

/-- If `log B ≤ 1.37317 y` with `0 ≤ log B` and `B = 2^{16} T y^4`, then `χ(B) ≥ 18432 T`. -/
theorem cap_chi_ge {T y B : ℝ} (hT : 0 ≤ T) (hB : B = 2 ^ 16 * T * y ^ 4)
    (h0 : 0 ≤ Real.logb 2 B) (hc : Real.logb 2 B ≤ 137317 / 100000 * y) :
    18432 * T * Real.logb 2 B ^ 4 ≤ B := by
  have h4 : Real.logb 2 B ^ 4 ≤ (137317 / 100000 * y) ^ 4 := pow_le_pow_left₀ h0 hc 4
  have hTy : 0 ≤ T * y ^ 4 := mul_nonneg hT (by positivity)
  calc 18432 * T * Real.logb 2 B ^ 4 ≤ 18432 * T * (137317 / 100000 * y) ^ 4 := by gcongr
    _ = (18432 * (137317 / 100000 : ℝ) ^ 4) * (T * y ^ 4) := by ring
    _ ≤ 2 ^ 16 * (T * y ^ 4) := mul_le_mul_of_nonneg_right cap_const hTy
    _ = B := by rw [hB]; ring

/-- `log (2^{16} T y^4) = 16 + log T + 4 log y` for `T, y ≠ 0`. -/
theorem logb_cap_bound {T y : ℝ} (hT : T ≠ 0) (hy : y ≠ 0) :
    Real.logb 2 (2 ^ 16 * T * y ^ 4) = 16 + Real.logb 2 T + 4 * Real.logb 2 y := by
  rw [Real.logb_mul (by positivity) (pow_ne_zero 4 hy), Real.logb_mul (by positivity) hT,
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
  push_cast
  ring

/-- [s2:lemCap] (i) without the (unused) hypothesis `m ≥ 2^{40}`: if `T ≥ 2^{117}` and
`m < 18432 T log⁴ m`, then `m ≤ 2^{16} T log⁴ T`. -/
theorem cap_of_T_ge {m T : ℝ} (hT : 2 ^ 117 ≤ T) (hm : m < 18432 * T * Real.logb 2 m ^ 4) :
    m ≤ 2 ^ 16 * T * Real.logb 2 T ^ 4 := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hx117 : 117 ≤ Real.logb 2 T := by
    have h := Real.logb_le_logb_of_le one_lt_two (by norm_num : (0 : ℝ) < 2 ^ 117) hT
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two] at h
    push_cast at h
    linarith
  set x := Real.logb 2 T with hx
  have hx0 : 0 < x := by linarith
  apply cap_core _ _ hm
  · have h1 : 1 ≤ T * x ^ 4 :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
    nlinarith
  · have hlogB := logb_cap_bound hT0.ne' hx0.ne'
    rw [← hx] at hlogB
    have hc := cap_numeric hx117
    have hlx : 0 ≤ Real.logb 2 x := Real.logb_nonneg one_lt_two (by linarith)
    exact cap_chi_ge hT0.le rfl (by rw [hlogB]; linarith) (by rw [hlogB]; exact hc)

/-- [s2:lemCap] (i) "If `m ≥ 2^{40}`, `T ≥ 2^{117}` and `m < 18432 T log⁴ m`, then
`m ≤ 2^{16} T log⁴ T`." -/
theorem cap : EG.Spec.CapStatement := fun _ _ _ hT hm => cap_of_T_ge hT hm

/-- [s2:lemCap] (Remark) "The uniform form `m ≤ max(2^{40}, 2^{16} T (log T + 40)^4)` holds for
all `T ≥ 1`." -/
theorem cap_uniform : EG.Spec.CapUniformStatement := by
  intro m T hT hm
  have hT0 : 0 < T := by linarith
  have hx0 : 0 ≤ Real.logb 2 T := Real.logb_nonneg one_lt_two hT
  set x := Real.logb 2 T with hx
  have hmB : m ≤ 2 ^ 16 * T * (x + 40) ^ 4 := by
    apply cap_core _ _ hm
    · have h1 : 1 ≤ T * (x + 40) ^ 4 :=
        one_le_mul_of_one_le_of_one_le hT (one_le_pow₀ (by linarith))
      nlinarith
    · have hlogB := logb_cap_bound hT0.ne' (by linarith : x + 40 ≠ 0)
      rw [← hx] at hlogB
      have hc := cap_numeric_uniform hx0
      have hlx : 0 ≤ Real.logb 2 (x + 40) := Real.logb_nonneg one_lt_two (by linarith)
      exact cap_chi_ge hT0.le rfl (by rw [hlogB]; linarith) (by rw [hlogB]; exact hc)
  exact le_max_of_le_right hmB

/-- [s2:lemCap] (Remark, not used) "Part (i) is false for small `T`: for `T = 2^{20}` and
`m = 2^{55}` we have `m ≥ 2^{40}` and `18432 T log⁴ m = 2^{57.29…} > m`, but
`2^{16} T log⁴ T = 2^{53.28…} < m`." -/
theorem cap_remark_counterexample :
    (2 : ℝ) ^ 40 ≤ 2 ^ 55 ∧
      (2 : ℝ) ^ 55 < 18432 * 2 ^ 20 * Real.logb 2 ((2 : ℝ) ^ 55) ^ 4 ∧
      2 ^ 16 * 2 ^ 20 * Real.logb 2 ((2 : ℝ) ^ 20) ^ 4 < (2 : ℝ) ^ 55 := by
  have h55 : Real.logb 2 ((2 : ℝ) ^ 55) = 55 := by
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two]; norm_num
  have h20 : Real.logb 2 ((2 : ℝ) ^ 20) = 20 := by
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two]; norm_num
  rw [h55, h20]
  norm_num

/-- [s2:lemCap] (ii), graph-level step: an `m`-vertex `(2^{-5},0)`-expander with `m ≥ 2^{40}` and
no cycle of length at least `T ≥ 2^{117}` has `m ≤ 2^{16} T log⁴ T`. From [s1:citLem25]
(`EG.bmLemma25`, currently `sorry`) and part (i). -/
theorem cap_graph : EG.Spec.CapGraphStatement.{u} := by
  intro V _ G T hT hm hexp hcyc
  have hm2 : 2 ≤ G.card := by
    have h : (2 : ℝ) ≤ G.card := le_trans (by norm_num) hm
    exact_mod_cast h
  have hε : (2 : ℝ) ^ 30 / ((2 : ℝ) ^ (-5 : ℤ)) ^ 2 = 2 ^ 40 := by norm_num
  obtain ⟨c, hwf, hce, hlen⟩ :=
    bmLemma25.{u} V G ((2 : ℝ) ^ (-5 : ℤ)) le_rfl (by rw [hε]; exact hm) hm2 hexp
  have hlt := hcyc c hwf hce
  have hlogm : 0 < Real.logb 2 (G.card : ℝ) := Real.logb_pos one_lt_two (by linarith)
  have hε2 : ((2 : ℝ) ^ (-5 : ℤ)) ^ 2 = 1 / 1024 := by norm_num
  rw [hε2] at hlen
  have h := lt_of_le_of_lt hlen hlt
  rw [div_lt_iff₀ (by positivity)] at h
  exact cap _ _ hm hT (by linarith)

end EG
