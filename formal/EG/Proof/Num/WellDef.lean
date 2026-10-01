module

public import EG.Spec.Num.WellDef
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# The SDR union bound of Lemma WellDef (iii) (manuscript s7:lemWellDef)

Proofs of the statements of `EG/Spec/Num/WellDef.lean` (fix round 1, review I-2 and I-4):
`numWellDefSDRRatio`, `numWellDefSDRConst`, `numWellDefSDRSeries`, `numWellDefSDRUse`.

The proof of the series bound follows the TeX step by step, with `e = exp 1` and
`a_s := (1/e)(s/K)(e^2s/(4K))^s` (`aS K s` below):
* `T_s ≤ a_s` for `4 ≤ s ≤ m ≤ K/4` (`numSDRTerm_le_aS`), from `C(n,r) ≤ (en/r)^r`
  (`choose_le_e_pow`: `C(n,r) ≤ n^r/r!` and `r^r/r! ≤ e^r`), `C(s−1,3)/C(K,3) ≤ ((s−1)/K)^3`
  (`choose_three_ratio_le`) and `(s−1)^{2s+1} ≤ s^{2s+1}`;
* `a_{s+1} ≤ (5e^3/16)((s+1)/K)a_s` for `s ≥ 4` (`aS_succ_le`, via `(1+1/s)^s ≤ e`), hence
  `a_s ≤ 2^{4−s}a_4` while `13s ≤ K` (`aS_le_geom`; the TeX's range is `4 ≤ s ≤ ⌈K/13⌉`, the
  formal split is `13s ≤ K` versus `13s > K`, which also covers `[4,m]`);
* `a_s ≤ (1/(4e))(e^2/16)^s ≤ 0.47^s` for `s ≤ K/4` (`aS_le_tail`);
* the two geometric sums: `∑ 2^{4−s} ≤ 2` and `∑_{s > K/13} 0.47^s ≤ 0.47^{K/13}/0.53`.
`a_4 = 4e^7K^{−5} < 4400K^{−5}`. The last constant, `2·0.47^{K/13} ≤ 0.1K^{−4}` for real
`K ≥ 10^4`, goes through `0.47 ≤ 1/2`, `z := (K/13)ln 2 ≥ 500`, `K ≤ 19z` and
`e^z ≥ z^{10}/10!`: it needs `20·10!·19^4 ≤ z^6`, i.e. `z ≥ 145.3` (huge slack).

Recorded slacks: `4e^7 = 4386.53…` vs `4400` (0.31%); `(5e^3/16)(1/13+10^{−4}) = 0.48345…` vs
`0.49` (1.3%); `e^2/16 = 0.46182…` vs `0.47` (1.7%); `1/0.53 = 1.8868…` vs `2`;
`8800K^{−5} ≤ 0.88K^{−4}` is an equality at `K = 10^4`.
-/

public section


namespace EG

open Real Finset

/-! ### Constants -/

/-- [s7:lemWellDef] (iii) `0.49 ≤ 1/2`. -/
theorem numWellDefSDRRatio : EG.Spec.NumWellDefSDRRatioStatement := by
  unfold EG.Spec.NumWellDefSDRRatioStatement; norm_num

private theorem exp_eq_pow (n : ℕ) : Real.exp (n : ℝ) = Real.exp 1 ^ n := (exp_one_pow n).symm

/-- `2·0.47^{K/13} ≤ 0.1K^{−4}` for real `K ≥ 10^4`. -/
private theorem two_mul_rpow_le {K : ℝ} (hK : 10 ^ 4 ≤ K) :
    2 * (0.47 : ℝ) ^ (K / 13) ≤ 0.1 * K ^ (-4 : ℤ) := by
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hl2 := Real.log_two_gt_d9
  set z := K / 13 * Real.log 2 with hzdef
  have hz : 500 ≤ z := by
    have : (500 : ℝ) ≤ 10 ^ 4 / 13 * 0.6931471803 := by norm_num
    have h2 : 10 ^ 4 / 13 * 0.6931471803 ≤ K / 13 * Real.log 2 := by
      apply mul_le_mul (by linarith) hl2.le (by norm_num) (by positivity)
    linarith
  have hz0 : 0 < z := by linarith
  have hK19 : K ≤ 19 * z := by rw [hzdef]; nlinarith
  -- `0.47^{K/13} ≤ (1/2)^{K/13} = e^{−z}`.
  have h1 : (0.47 : ℝ) ^ (K / 13) ≤ (1 / 2 : ℝ) ^ (K / 13) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
  have h2 : (1 / 2 : ℝ) ^ (K / 13) = Real.exp (-z) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv, hzdef]
    ring_nf
  -- `e^{−z} ≤ 10!/z^{10}`.
  have hf : ((Nat.factorial 10 : ℕ) : ℝ) = 3628800 := by norm_num [Nat.factorial]
  have h3 : Real.exp (-z) ≤ 3628800 / z ^ 10 := by
    have := Real.pow_div_factorial_le_exp z hz0.le 10
    rw [hf] at this
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact this
  -- `20·10!·K^4 ≤ z^{10}`.
  have hK4 : K ^ 4 ≤ (19 * z) ^ 4 := pow_le_pow_left₀ hK0.le hK19 4
  have hz6 : (500 : ℝ) ^ 6 ≤ z ^ 6 := pow_le_pow_left₀ (by norm_num) hz 6
  have hz4 : 0 < z ^ 4 := by positivity
  have hkey : 20 * 3628800 * K ^ 4 ≤ z ^ 10 := by
    calc 20 * 3628800 * K ^ 4 ≤ 20 * 3628800 * (19 * z) ^ 4 := by gcongr
      _ = (20 * 3628800 * 19 ^ 4) * z ^ 4 := by ring
      _ ≤ 500 ^ 6 * z ^ 4 := by gcongr; norm_num
      _ ≤ z ^ 6 * z ^ 4 := by gcongr
      _ = z ^ 10 := by ring
  have hKz : 0 < K ^ 4 := by positivity
  rw [zpow_neg, zpow_ofNat]
  calc 2 * (0.47 : ℝ) ^ (K / 13) ≤ 2 * (3628800 / z ^ 10) := by
        rw [h2] at h1; linarith
    _ ≤ 0.1 * (K ^ 4)⁻¹ := by
        rw [← div_eq_mul_inv, mul_div_assoc', div_le_div_iff₀ (by positivity) hKz]
        nlinarith

/-- [s7:lemWellDef] (iii) The constants of the proof. -/
theorem numWellDefSDRConst : EG.Spec.NumWellDefSDRConstStatement := by
  have he1 := Real.exp_one_lt_d9
  have he0 := Real.exp_one_gt_d9
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← exp_eq_pow]; norm_num
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← exp_eq_pow]; norm_num
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← exp_eq_pow]; norm_num
  have e7 : Real.exp 1 ^ 7 < 2.7182818286 ^ 7 := by gcongr
  have e3 : Real.exp 1 ^ 3 < 2.7182818286 ^ 3 := by gcongr
  have e2 : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 := by gcongr
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num, ?_, by norm_num, ?_⟩
  · rw [h7]
    have : (4 : ℝ) * 2.7182818286 ^ 7 < 4400 := by norm_num
    linarith
  · intro K hK
    have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
    have hKi : 1 / K ≤ 1 / 10 ^ 4 := one_div_le_one_div_of_le (by norm_num) hK
    rw [h3]
    calc 5 * Real.exp 1 ^ 3 / 16 * (1 / 13 + 1 / K)
        ≤ 5 * 2.7182818286 ^ 3 / 16 * (1 / 13 + 1 / 10 ^ 4) := by
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      _ < 0.49 := by norm_num
  · rw [div_le_one (by positivity)]; linarith
  · rw [h2]
    have : (2.7182818286 : ℝ) ^ 2 / 16 ≤ 0.47 := by norm_num
    linarith
  · intro K hK
    have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
    refine ⟨?_, two_mul_rpow_le hK⟩
    have hK4 : 0 < K ^ (-4 : ℤ) := zpow_pos hK0 _
    have hKi : K⁻¹ ≤ 1 / 10 ^ 4 := by
      rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hK
    rw [show (-5 : ℤ) = -4 - 1 by norm_num, zpow_sub_one₀ hK0.ne']
    nlinarith
  · intro M hM
    constructor <;> omega

/-! ### Binomial bounds -/

/-- `C(n,r) ≤ (en/r)^r` for `r ≥ 1` (from `C(n,r) ≤ n^r/r!` and `r^r/r! ≤ e^r`). -/
private theorem choose_le_e_pow (n r : ℕ) (hr : 1 ≤ r) :
    (n.choose r : ℝ) ≤ (Real.exp 1 * n / r) ^ r := by
  have h1 := Nat.choose_le_pow_div (α := ℝ) r n
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have h2 := Real.pow_div_factorial_le_exp (r : ℝ) hr0.le r
  rw [exp_eq_pow, div_le_iff₀ hf] at h2
  refine le_trans h1 ?_
  rw [div_pow, mul_pow, div_le_div_iff₀ hf (by positivity)]
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ r := by positivity
  calc (n : ℝ) ^ r * (r : ℝ) ^ r ≤ (n : ℝ) ^ r * (Real.exp 1 ^ r * r.factorial) :=
        mul_le_mul_of_nonneg_left h2 hn
    _ = Real.exp 1 ^ r * (n : ℝ) ^ r * r.factorial := by ring

/-- `C(n,3) = n(n−1)(n−2)/6` in `ℝ`, for `n ≥ 2`. -/
private theorem choose_three_eq (n : ℕ) (hn : 2 ≤ n) :
    (n.choose 3 : ℝ) = n * (n - 1) * (n - 2) / 6 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h := Nat.descFactorial_eq_factorial_mul_choose (j + 2) 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have h' : (((j + 2 - 2) * ((j + 2 - 1) * ((j + 2 - 0) * 1)) : ℕ) : ℝ) =
      ((Nat.factorial 3 * (j + 2).choose 3 : ℕ) : ℝ) := by rw [h]
  simp only [Nat.add_sub_cancel, Nat.sub_zero, mul_one,
    show j + 2 - 1 = j + 1 by omega] at h'
  push_cast [Nat.factorial] at h' ⊢
  linarith

/-- `C(t,3)/C(K,3) ≤ (t/K)^3` for `3 ≤ t ≤ K`. -/
private theorem choose_three_ratio_le (t K : ℕ) (ht : 3 ≤ t) (htK : t ≤ K) :
    (t.choose 3 : ℝ) / (K.choose 3 : ℝ) ≤ ((t : ℝ) / K) ^ 3 := by
  have hK3 : 3 ≤ K := le_trans ht htK
  rw [choose_three_eq t (by omega), choose_three_eq K (by omega)]
  have ht' : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have htK' : (t : ℝ) ≤ K := by exact_mod_cast htK
  have hK0 : (0 : ℝ) < K := by linarith
  have hden : (0 : ℝ) < K * (K - 1) * (K - 2) / 6 := by
    apply div_pos _ (by norm_num); apply mul_pos (mul_pos hK0 (by linarith)) (by linarith)
  rw [div_le_iff₀ hden, div_pow]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  -- `t(t−1)(t−2)K^3 ≤ t^3K(K−1)(K−2)`, factor by factor.
  have a1 : (t - 1) * (K : ℝ) ≤ t * (K - 1) := by nlinarith
  have a2 : (t - 2) * (K : ℝ) ≤ t * (K - 2) := by nlinarith
  have hp : (t - 1) * (K : ℝ) * ((t - 2) * K) ≤ t * (K - 1) * (t * (K - 2)) :=
    mul_le_mul a1 a2 (by nlinarith) (by nlinarith)
  have htK0 : (0 : ℝ) ≤ t * K := by positivity
  have := mul_le_mul_of_nonneg_left hp htK0
  nlinarith

/-! ### The terms `a_s` -/

/-- `a_s := (1/e)(s/K)(e^2s/(4K))^s` (the majorant of `T_s` in the TeX). -/
private noncomputable def aS (K : ℝ) (s : ℕ) : ℝ :=
  1 / Real.exp 1 * ((s : ℝ) / K) * (Real.exp 1 ^ 2 * s / (4 * K)) ^ s

private theorem aS_nonneg {K : ℝ} (hK : 0 < K) (s : ℕ) : 0 ≤ aS K s := by
  unfold aS; positivity

/-- `a_4 = 4e^7/K^5`. -/
private theorem aS_four {K : ℝ} (hK : 0 < K) : aS K 4 = 4 * Real.exp 1 ^ 7 / K ^ 5 := by
  unfold aS
  have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  field_simp
  push_cast
  ring

/-- The identity `(e(K/4)/s)^{k+1} e^k (s/K)^{2k+3} = a_s` with `s = k+1`. -/
private theorem aS_identity {K : ℝ} (hK : 0 < K) (k : ℕ) :
    (Real.exp 1 * (K / 4) / ((k : ℝ) + 1)) ^ (k + 1) * Real.exp 1 ^ k *
        (((k : ℝ) + 1) / K) ^ (2 * k + 3) = aS K (k + 1) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set e := Real.exp 1
  set s : ℝ := (k : ℝ) + 1 with hs
  have hs0 : 0 < s := by positivity
  have h1 : (e * (K / 4) / s) ^ (k + 1) * (s / K) ^ (k + 1) = (e / 4) ^ (k + 1) := by
    rw [← mul_pow]; congr 1; field_simp
  have h2 : (e ^ 2 * s / (4 * K)) ^ (k + 1) = (e / 4) ^ (k + 1) * e ^ (k + 1) * (s / K) ^ (k + 1) := by
    rw [← mul_pow, ← mul_pow]; congr 1; field_simp
  have h3 : 1 / e * e ^ (k + 1) = e ^ k := by rw [pow_succ]; field_simp
  unfold aS
  push_cast
  rw [← hs, h2]
  calc (e * (K / 4) / s) ^ (k + 1) * e ^ k * (s / K) ^ (2 * k + 3)
      = ((e * (K / 4) / s) ^ (k + 1) * (s / K) ^ (k + 1)) * e ^ k * (s / K) ^ (k + 2) := by ring
    _ = (e / 4) ^ (k + 1) * e ^ k * (s / K) ^ (k + 2) := by rw [h1]
    _ = (e / 4) ^ (k + 1) * (1 / e * e ^ (k + 1)) * (s / K) ^ (k + 2) := by rw [h3]
    _ = 1 / e * (s / K) * ((e / 4) ^ (k + 1) * e ^ (k + 1) * (s / K) ^ (k + 1)) := by ring

/-- `T_s ≤ a_s` for `4 ≤ s ≤ m ≤ K/4`. -/
private theorem numSDRTerm_le_aS {K m s : ℕ} (hK : 4 ≤ K) (hm : (m : ℝ) ≤ (K : ℝ) / 4)
    (hs : 4 ≤ s) (hsm : s ≤ m) : EG.Spec.numSDRTerm K m s ≤ aS K s := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hk3 : 3 ≤ k := by omega
  have hkK : k ≤ K := by
    have : ((k + 1 : ℕ) : ℝ) ≤ (K : ℝ) / 4 := le_trans (by exact_mod_cast hsm) hm
    push_cast at this
    have : (k : ℝ) ≤ K := by linarith
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set e := Real.exp 1
  unfold EG.Spec.numSDRTerm
  simp only [Nat.add_sub_cancel]
  -- the three factors
  have hA : ((m.choose (k + 1) : ℕ) : ℝ) ≤ (e * (K / 4) / ((k : ℝ) + 1)) ^ (k + 1) := by
    refine le_trans (choose_le_e_pow m (k + 1) (by omega)) ?_
    push_cast
    gcongr
  have hB : ((K.choose k : ℕ) : ℝ) ≤ (e * K / k) ^ k := choose_le_e_pow K k (by omega)
  have hC0 : (0 : ℝ) ≤ (k.choose 3 : ℝ) / (K.choose 3 : ℝ) := by positivity
  have hC : ((k.choose 3 : ℝ) / (K.choose 3 : ℝ)) ^ (k + 1) ≤ (((k : ℝ) / K) ^ 3) ^ (k + 1) :=
    pow_le_pow_left₀ hC0 (choose_three_ratio_le k K hk3 hkK) _
  have hP : ((m.choose (k + 1) : ℕ) : ℝ) * ((K.choose k : ℕ) : ℝ) *
      ((k.choose 3 : ℝ) / (K.choose 3 : ℝ)) ^ (k + 1) ≤
      (e * (K / 4) / ((k : ℝ) + 1)) ^ (k + 1) * (e * K / k) ^ k * (((k : ℝ) / K) ^ 3) ^ (k + 1) := by
    apply mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC (by positivity)
      (by positivity)
  refine le_trans hP ?_
  rw [← aS_identity hK0 k]
  -- `(eK/k)^k (k/K)^{3(k+1)} = e^k (k/K)^{2k+3} ≤ e^k ((k+1)/K)^{2k+3}`.
  have hsplit : (((k : ℝ) / K) ^ 3) ^ (k + 1) = ((k : ℝ) / K) ^ k * ((k : ℝ) / K) ^ (2 * k + 3) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have hek : (e * K / k) ^ k * ((k : ℝ) / K) ^ k = e ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have hmono : ((k : ℝ) / K) ^ (2 * k + 3) ≤ (((k : ℝ) + 1) / K) ^ (2 * k + 3) := by
    gcongr; linarith
  rw [hsplit]
  calc (e * (K / 4) / ((k : ℝ) + 1)) ^ (k + 1) * (e * K / k) ^ k *
        (((k : ℝ) / K) ^ k * ((k : ℝ) / K) ^ (2 * k + 3))
      = (e * (K / 4) / ((k : ℝ) + 1)) ^ (k + 1) * ((e * K / k) ^ k * ((k : ℝ) / K) ^ k) *
        ((k : ℝ) / K) ^ (2 * k + 3) := by ring
    _ = (e * (K / 4) / ((k : ℝ) + 1)) ^ (k + 1) * e ^ k * ((k : ℝ) / K) ^ (2 * k + 3) := by
        rw [hek]
    _ ≤ (e * (K / 4) / ((k : ℝ) + 1)) ^ (k + 1) * e ^ k * (((k : ℝ) + 1) / K) ^ (2 * k + 3) := by
        gcongr

/-- `a_{s+1} ≤ (5e^3/16)((s+1)/K)a_s` for `s ≥ 4` (using `(1+1/s)^s ≤ e`). -/
private theorem aS_succ_le {K : ℝ} (hK : 0 < K) {s : ℕ} (hs : 4 ≤ s) :
    aS K (s + 1) ≤ 5 * Real.exp 1 ^ 3 / 16 * (((s : ℝ) + 1) / K) * aS K s := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hq : (4 : ℝ) ≤ s := by exact_mod_cast hs
  have hq0 : (0 : ℝ) < s := by linarith
  set e := Real.exp 1 with hedef
  set q : ℝ := (s : ℝ) with hqdef
  -- `(1 + 1/q)^s ≤ e`.
  have hbern : ((q + 1) / q) ^ s ≤ e := by
    have h1 : (q + 1) / q ≤ Real.exp (1 / q) := by
      have := Real.add_one_le_exp (1 / q)
      have h' : (q + 1) / q = 1 / q + 1 := by rw [add_div, div_self hq0.ne']; ring
      linarith
    calc ((q + 1) / q) ^ s ≤ Real.exp (1 / q) ^ s := by
          gcongr
      _ = e := by rw [← Real.exp_nat_mul, hedef]; congr 1; rw [← hqdef]; field_simp
  set W := (e ^ 2 * q / (4 * K)) ^ s with hW
  have hW0 : 0 ≤ W := by positivity
  have hfac : (e ^ 2 * (q + 1) / (4 * K)) ^ (s + 1) =
      (e ^ 2 * (q + 1) / (4 * K)) * (W * ((q + 1) / q) ^ s) := by
    rw [hW, ← mul_pow, pow_succ]
    have : e ^ 2 * q / (4 * K) * ((q + 1) / q) = e ^ 2 * (q + 1) / (4 * K) := by field_simp
    rw [this]; ring
  unfold aS
  push_cast
  rw [← hqdef, hfac, ← hW]
  have hX : 0 ≤ 1 / e * ((q + 1) / K) * (e ^ 2 * (q + 1) / (4 * K)) * W := by positivity
  calc 1 / e * ((q + 1) / K) * (e ^ 2 * (q + 1) / (4 * K) * (W * ((q + 1) / q) ^ s))
      = (1 / e * ((q + 1) / K) * (e ^ 2 * (q + 1) / (4 * K)) * W) * ((q + 1) / q) ^ s := by
        ring
    _ ≤ (1 / e * ((q + 1) / K) * (e ^ 2 * (q + 1) / (4 * K)) * W) * e :=
        mul_le_mul_of_nonneg_left hbern hX
    _ = (e ^ 2 * (q + 1) ^ 2 / (4 * K ^ 2)) * W := by field_simp
    _ ≤ (5 * e ^ 2 * (q + 1) * q / (16 * K ^ 2)) * W := by
        apply mul_le_mul_of_nonneg_right _ hW0
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ e ^ 2 * (q + 1) * K ^ 2 := by positivity
        nlinarith
    _ = 5 * e ^ 3 / 16 * ((q + 1) / K) * (1 / e * (q / K) * W) := by field_simp

/-- `a_s ≤ 2^{4−s}a_4` while `13s ≤ K` (`K ≥ 10^4`). -/
private theorem aS_le_geom {K : ℕ} (hK : 10 ^ 4 ≤ K) :
    ∀ s : ℕ, 4 ≤ s → 13 * s ≤ K → aS K s ≤ (1 / 2 : ℝ) ^ (s - 4) * aS K 4 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKr : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hc := (numWellDefSDRConst.2.1) (K : ℝ) hKr
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← exp_eq_pow]; norm_num
  rw [h3] at hc
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro _; simp
  | succ s hs ih =>
    intro h13
    have ih' := ih (by omega)
    have hr := aS_succ_le hK0 hs
    have hsK : ((s : ℝ) + 1) / K ≤ 1 / 13 + 1 / K := by
      have h13' : (13 : ℝ) * s ≤ K := by exact_mod_cast (show 13 * s ≤ K by omega)
      have : (s : ℝ) / K ≤ 1 / 13 := by rw [div_le_iff₀ hK0]; linarith
      rw [add_div]; linarith
    have hratio : 5 * Real.exp 1 ^ 3 / 16 * (((s : ℝ) + 1) / K) ≤ 1 / 2 := by
      have : 5 * Real.exp 1 ^ 3 / 16 * (((s : ℝ) + 1) / K) ≤
          5 * Real.exp 1 ^ 3 / 16 * (1 / 13 + 1 / K) :=
        mul_le_mul_of_nonneg_left hsK (by positivity)
      linarith
    have ha0 := aS_nonneg hK0 s
    calc aS K (s + 1) ≤ 5 * Real.exp 1 ^ 3 / 16 * (((s : ℝ) + 1) / K) * aS K s := hr
      _ ≤ 1 / 2 * aS K s := mul_le_mul_of_nonneg_right hratio ha0
      _ ≤ 1 / 2 * ((1 / 2 : ℝ) ^ (s - 4) * aS K 4) := by gcongr
      _ = (1 / 2 : ℝ) ^ (s + 1 - 4) * aS K 4 := by
          rw [show s + 1 - 4 = (s - 4) + 1 by omega, pow_succ]; ring

/-- `a_s ≤ (1/(4e))(e^2/16)^s ≤ 0.47^s` for `s ≤ K/4`. -/
private theorem aS_le_tail {K : ℝ} (hK : 0 < K) {s : ℕ} (hsK : (s : ℝ) ≤ K / 4) :
    aS K s ≤ (0.47 : ℝ) ^ s := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hc := numWellDefSDRConst
  have h4e : 1 / (4 * Real.exp 1) ≤ 1 := hc.2.2.1
  have he2 : Real.exp 2 / 16 ≤ 0.47 := hc.2.2.2.1
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← exp_eq_pow]; norm_num
  rw [h2] at he2
  have hq : (s : ℝ) / K ≤ 1 / 4 := by rw [div_le_iff₀ hK]; linarith
  have hr : Real.exp 1 ^ 2 * s / (4 * K) ≤ Real.exp 1 ^ 2 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (s : ℝ) * 16 ≤ 4 * K := by linarith
    nlinarith [sq_nonneg (Real.exp 1)]
  unfold aS
  calc 1 / Real.exp 1 * ((s : ℝ) / K) * (Real.exp 1 ^ 2 * s / (4 * K)) ^ s
      ≤ 1 / Real.exp 1 * (1 / 4) * (Real.exp 1 ^ 2 / 16) ^ s := by gcongr
    _ = 1 / (4 * Real.exp 1) * (Real.exp 1 ^ 2 / 16) ^ s := by ring
    _ ≤ 1 * (0.47 : ℝ) ^ s := by
        apply mul_le_mul h4e (pow_le_pow_left₀ (by positivity) he2 s) (by positivity)
          (by norm_num)
    _ = (0.47 : ℝ) ^ s := one_mul _

/-! ### The series -/

/-- [s7:lemWellDef] (iii) "`∑_{s=4}^m T_s ≤ 8800K^{−5} + 2·0.47^{K/13} ≤ K^{−4}` (`K ≥ 10^4`)",
for `m ≤ K/4`. -/
theorem numWellDefSDRSeries : EG.Spec.NumWellDefSDRSeriesStatement := by
  intro K m hK hm
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKr : (10 : ℝ) ^ 4 ≤ K := by exact_mod_cast hK
  have hc := numWellDefSDRConst
  have hsecond : 8800 * (K : ℝ) ^ (-5 : ℤ) + 2 * (0.47 : ℝ) ^ ((K : ℝ) / 13) ≤
      (K : ℝ) ^ (-4 : ℤ) := by
    have h := hc.2.2.2.2.2.2.1 (K : ℝ) hKr
    have hK4 : 0 < (K : ℝ) ^ (-4 : ℤ) := zpow_pos hK0 _
    linarith [h.1, h.2]
  refine ⟨?_, hsecond⟩
  set a4 := aS K 4 with ha4def
  have ha4 : 0 ≤ a4 := aS_nonneg hK0 4
  have ha4eq : a4 = 4 * Real.exp 1 ^ 7 / (K : ℝ) ^ 5 := aS_four hK0
  -- termwise bound
  have hterm : ∀ s ∈ Icc 4 m, EG.Spec.numSDRTerm K m s ≤
      (1 / 2 : ℝ) ^ (s - 4) * a4 + (if K < 13 * s then (0.47 : ℝ) ^ s else 0) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hT := numSDRTerm_le_aS (by omega) hm hs.1 hs.2
    have hsK : (s : ℝ) ≤ K / 4 := le_trans (by exact_mod_cast hs.2) hm
    by_cases h13 : K < 13 * s
    · rw [if_pos h13]
      have := aS_le_tail hK0 hsK
      have : 0 ≤ (1 / 2 : ℝ) ^ (s - 4) * a4 := by positivity
      linarith
    · rw [if_neg h13]
      have := aS_le_geom hK s hs.1 (by omega)
      linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter]
  -- the geometric part: `∑_{s=4}^m 2^{4−s} ≤ 2`
  have hgeo : ∑ s ∈ Icc 4 m, (1 / 2 : ℝ) ^ (s - 4) ≤ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact sum_geometric_two_le _
  -- the tail: `∑_{s > K/13} 0.47^s ≤ 0.47^{K/13}/0.53 ≤ 2·0.47^{K/13}`
  set s0 := K / 13 + 1 with hs0
  have hsub : (Icc 4 m).filter (fun s => K < 13 * s) ⊆ Ico s0 (m + 1) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs
    simp only [Finset.mem_Ico]
    omega
  have htail1 : ∑ s ∈ (Icc 4 m).filter (fun s => K < 13 * s), (0.47 : ℝ) ^ s ≤
      ∑ s ∈ Ico s0 (m + 1), (0.47 : ℝ) ^ s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have htail2 : ∑ s ∈ Ico s0 (m + 1), (0.47 : ℝ) ^ s ≤ (0.47 : ℝ) ^ s0 / (1 - 0.47) :=
    geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
  have hs0K : (K : ℝ) / 13 ≤ (s0 : ℝ) := by
    have : K < 13 * s0 := by omega
    have : (K : ℝ) < 13 * (s0 : ℝ) := by exact_mod_cast this
    rw [div_le_iff₀ (by norm_num)]; linarith
  have htail3 : (0.47 : ℝ) ^ s0 ≤ (0.47 : ℝ) ^ ((K : ℝ) / 13) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hs0K
  have hr0 : (0 : ℝ) ≤ (0.47 : ℝ) ^ ((K : ℝ) / 13) := by positivity
  have htail : ∑ s ∈ (Icc 4 m).filter (fun s => K < 13 * s), (0.47 : ℝ) ^ s ≤
      2 * (0.47 : ℝ) ^ ((K : ℝ) / 13) := by
    have h053 : (0.47 : ℝ) ^ s0 / (1 - 0.47) ≤ 2 * (0.47 : ℝ) ^ ((K : ℝ) / 13) := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  -- `2a_4 ≤ 8800K^{−5}`
  have ha4b : 2 * a4 ≤ 8800 * (K : ℝ) ^ (-5 : ℤ) := by
    rw [ha4eq, zpow_neg, zpow_ofNat]
    have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← exp_eq_pow]; norm_num
    have := hc.1
    rw [h7] at this
    have hK5 : 0 < (K : ℝ) ^ 5 := by positivity
    rw [← div_eq_mul_inv, mul_div_assoc', div_le_div_iff₀ hK5 hK5]
    nlinarith
  have : (∑ s ∈ Icc 4 m, (1 / 2 : ℝ) ^ (s - 4)) * a4 ≤ 2 * a4 :=
    mul_le_mul_of_nonneg_right hgeo ha4
  linarith

/-- [s7:lemWellDef] (iii), use form: `M ≥ 2^{40}`, `m ≤ M − 1`, `K = 4M`:
`∑_{s=4}^m T_s ≤ K^{−4}`. -/
theorem numWellDefSDRUse : EG.Spec.NumWellDefSDRUseStatement := by
  intro M m hM hm
  have hK : 10 ^ 4 ≤ 4 * M := (numWellDefSDRConst.2.2.2.2.2.2.2.2 M hM).2
  have hmK : (m : ℝ) ≤ ((4 * M : ℕ) : ℝ) / 4 := by
    have : m ≤ M := by omega
    have : (m : ℝ) ≤ M := by exact_mod_cast this
    push_cast; linarith
  have h := numWellDefSDRSeries (4 * M) m hK hmK
  exact le_trans h.1 h.2

end EG
