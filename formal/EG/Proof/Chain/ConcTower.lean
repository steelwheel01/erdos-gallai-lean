module

public import EG.Spec.Chain.ConcTower
public import EG.Lib.Found.Log
public import EG.Lib.Chain.TowerFacts
public import EG.Lib.HB.Run
public import EG.Proof.HB.TowerA

/-!
# Proofs of the `log*` facts of s6 (unit P3B, probe P-3 part 2)

Statement file: `EG/Spec/Chain/ConcTower.lean`. Design note `formal/work/p2b/P3B.md`.
* `logStarFacts` (stage 1): the Lib lemmas `EG.logStar_le_iff_le_tower`, `EG.logStar_of_one_lt`,
  `EG.logStar_le_one_add_logb`;
* `kStar`, `towerEnd`, `towerHalf` (proof round 1): the manuscript proof, with the monotonicity of
  `(2 log t + 6)/t`, `(7 + 2 log t)/t`, `(2 log t + 5)/t^{1/2}` replaced by the growth lemma
  `EG.Chain.grow` (`EG.Lib.Chain.TowerFacts`: `half_core`, `end_core`). `towerHalf` uses the
  declared input `EG.towerA` ([s2:lemTower] (a), first clause `λ_r ≥ d_{r+1}^{1/A}`).
-/

public section

namespace EG

/-- [s6:thmCONC] (s6, text before s6:thmCONC, not part of the theorem: the `log*` facts)
"For `x ≥ 1` and an integer `k ≥ 0`, `log* x ≤ k`
iff `x ≤ 𝖳_k`. For `x > 1`, `log* x = 1 + log*(log x)`. And `log* x ≤ 1 + log x` for all
`x ≥ 1`." -/
theorem logStarFacts : EG.Spec.LogStarFactsStatement := by
  refine ⟨fun x k _ => logStar_le_iff_le_tower k x, fun x hx => ?_,
    fun x hx => logStar_le_one_add_logb hx⟩
  rw [logStar_of_one_lt hx, Nat.add_comm]

open Real Chain in
/-- [s6:thmCONC] (s6, text before s6:thmCONC, not part of the theorem) "Put `k_* := log* D_*`.
By Γ1(a) at `μ = log log D_*`, `log log D_* ≥ 2^8 > 16`, so `D_* > 2^{65536} = 𝖳_5` and
`k_* ≥ 6`." -/
theorem kStar : EG.Spec.KStarStatement := by
  intro D hΓ
  have h8 := hΓ.two_pow_eight_le_loglog
  have h256 := hΓ.two_pow_256_le_logb
  have hD0 : 0 < D := by linarith [hΓ.two_lt]
  have h5 : tower 5 < D := by
    rw [tower_succ, tower_four]
    conv_rhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hD0]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num at h256 ⊢; linarith)
  refine ⟨h8, by norm_num at h8 ⊢; linarith, h5, ?_⟩
  have := (lt_logStar_iff_tower_lt 5 D).2 h5
  omega

open Real Chain in
/-- [s6:eqTowerEnd] "for every `d ≥ D_*`, `𝖺(d) ≤ (2k_*+4)/log D_*`,
`𝖻(d) ≤ (2k_*+3)/log log D_*`, `𝖼(d) ≤ (2k_*+3)/(log D_*)^{1/2}`." -/
theorem towerEnd : EG.Spec.TowerEndStatement := by
  intro D hΓ d hd
  set k := logStar D with hkdef
  have hD2 := hΓ.two_lt
  have hD0 : 0 < D := by linarith
  have hd0 : 0 < d := by linarith
  have h256 := hΓ.two_pow_256_le_logb
  have ht8 : (2 : ℝ) ^ 8 ≤ logb 2 D := le_trans (by norm_num) h256
  have ht0 : 0 < logb 2 D := lt_of_lt_of_le (by norm_num) ht8
  have htb : (2 : ℝ) ^ 14 * 105 * (logb 2 D) ^ 3 ≤ D := by
    have := hΓ.items_logb.b
    unfold Gamma1b at this
    rwa [cast_Aexp, Real.rpow_logb (by norm_num) (by norm_num) hD0] at this
  have ht'8 := hΓ.two_pow_eight_le_loglog
  have ht'0 : 0 < logb 2 (logb 2 D) := lt_of_lt_of_le (by norm_num) ht'8
  have ht'b : (2 : ℝ) ^ 14 * 105 * (logb 2 (logb 2 D)) ^ 3 ≤ logb 2 D := by
    have := (hΓ.items le_rfl).b
    unfold Gamma1b at this
    rwa [cast_Aexp, Real.rpow_logb (by norm_num) (by norm_num) ht0] at this
  have hlogd : logb 2 D ≤ logb 2 d := Real.logb_le_logb_of_le (by norm_num) hD0 hd
  have hloglogd : logb 2 (logb 2 D) ≤ logb 2 (logb 2 d) := loglog_mono hD2 hd
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ (logStar d : ℝ) := Nat.cast_nonneg _
  have hDT : D ≤ tower k := (logStar_le_iff_le_tower k D).1 le_rfl
  have hts : 0 < (logb 2 D) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
  by_cases hA : logb 2 d ≤ tower k
  · have hdk : d ≤ tower (k + 1) := by
      rw [tower_succ]; exact (Real.logb_le_iff_le_rpow (by norm_num) hd0).1 hA
    have hL : (logStar d : ℝ) ≤ k + 1 := by
      exact_mod_cast (logStar_le_iff_le_tower (k + 1) d).2 hdk
    refine ⟨?_, ?_, ?_⟩
    · unfold towA; exact div_le_div₀ (by positivity) (by linarith) ht0 hlogd
    · unfold towB; exact div_le_div₀ (by positivity) (by linarith) ht'0 hloglogd
    · unfold towC
      exact div_le_div₀ (by positivity) (by linarith) hts
        (Real.rpow_le_rpow ht0.le hlogd (by norm_num))
  · push Not at hA
    set x := logb 2 d with hxdef
    have hxD : D ≤ x := hDT.trans hA.le
    have hx0 : 0 < x := lt_of_lt_of_le hD0 hxD
    obtain ⟨ea, eb, ec⟩ := end_core hD0 ht8 htb ht'8 ht'b hxD
    have hd16 : (16 : ℝ) ≤ d := by
      have h117 := hΓ.gamma2a
      unfold Gamma2a at h117
      linarith [show (16 : ℝ) ≤ 2 ^ 117 by norm_num]
    have hL2 : (logStar d : ℝ) ≤ 2 + logb 2 x := logStar_le_two_add_loglog (by linarith)
    have hL3 : (logStar d : ℝ) ≤ 3 + logb 2 (logb 2 x) := logStar_le_three_add_logloglog hd16
    have hX : logb 2 D ≤ logb 2 x := Real.logb_le_logb_of_le (by norm_num) hD0 hxD
    have hX0 : 0 < logb 2 x := lt_of_lt_of_le ht0 hX
    have hxs : 0 < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
    refine ⟨?_, ?_, ?_⟩
    · unfold towA
      rw [div_le_div_iff₀ hx0 ht0]
      have h1 : (2 * (logStar d : ℝ) + 2) * logb 2 D ≤ (2 * logb 2 x + 6) * logb 2 D :=
        mul_le_mul_of_nonneg_right (by linarith) ht0.le
      have h2 : x ≤ (2 * (k : ℝ) + 4) * x := by nlinarith
      nlinarith
    · unfold towB
      rw [div_le_div_iff₀ hX0 ht'0]
      have h1 : (2 * (logStar d : ℝ) + 1) * logb 2 (logb 2 D) ≤
          (7 + 2 * logb 2 (logb 2 x)) * logb 2 (logb 2 D) :=
        mul_le_mul_of_nonneg_right (by linarith) ht'0.le
      have h2 : logb 2 x ≤ (2 * (k : ℝ) + 3) * logb 2 x := by nlinarith
      nlinarith
    · unfold towC
      rw [div_le_div_iff₀ hxs hts]
      have h1 : (2 * (logStar d : ℝ) + 1) * (logb 2 D) ^ ((1 : ℝ) / 2) ≤
          (2 * logb 2 x + 5) * (logb 2 D) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hts.le
      have h2 : x ^ ((1 : ℝ) / 2) ≤ (2 * (k : ℝ) + 3) * x ^ ((1 : ℝ) / 2) := by nlinarith
      nlinarith

open Real Chain HB in
/-- [s6:eqTowerHalf] "for every valid run and every `r < R`,
`𝖺(d_r) ≤ ½𝖺(d_{r+1})`, `𝖻(d_r) ≤ ½𝖻(d_{r+1})`, `𝖼(d_r) ≤ ½𝖼(d_{r+1})`." Uses the declared
input `EG.towerA` ([s2:lemTower] (a): `λ_r ≥ d_{r+1}^{1/A}`). -/
theorem towerHalf : EG.Spec.TowerHalfStatement := by
  intro V _ G D run hΓ hv r hr
  obtain ⟨hr1, hrR⟩ := Finset.mem_Ico.1 hr
  have hR1 : run.IsRound 1 := ⟨le_rfl, by omega⟩
  have hd1 := Run.Valid.dstar_le run G hv hR1
  obtain ⟨hA1, -⟩ := towerA V G D run hΓ hv hd1
  have hlam := hA1 r (Finset.mem_Icc.2 ⟨hr1, by omega⟩)
  have hdD : D ≤ run.d G r := Run.Valid.dstar_le run G hv ⟨hr1, by omega⟩
  have hd'D : D ≤ run.d G (r + 1) := Run.Valid.dstar_le run G hv ⟨by omega, by omega⟩
  unfold Run.lam lamOf at hlam
  set d := run.d G r with hddef
  set d' := run.d G (r + 1) with hd'def
  have hD2 := hΓ.two_lt
  have hd0 : 0 < d := by linarith
  have hd'0 : 0 < d' := by linarith
  have h256 := hΓ.two_pow_256_le_logb
  have hlogd' : logb 2 D ≤ logb 2 d' := Real.logb_le_logb_of_le (by norm_num) (by linarith) hd'D
  set y := logb 2 d' with hydef
  have hy0 : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) h256) hlogd'
  have hIt := hΓ.items_loglog hd'D
  have hv8 := hIt.a
  unfold Gamma1a at hv8
  have hvb : (2 : ℝ) ^ 14 * 105 * (logb 2 y) ^ 3 ≤ y := by
    have := hIt.b
    unfold Gamma1b at this
    rwa [cast_Aexp, Real.rpow_logb (by norm_num) (by norm_num) hy0] at this
  have hx : (2 : ℝ) ^ (y / 105) ≤ logb 2 d := by
    have e : d' ^ ((1 : ℝ) / (Aexp : ℝ)) = (2 : ℝ) ^ (y / 105) := by
      rw [cast_Aexp]
      conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hd'0]
      rw [← Real.rpow_mul (by norm_num), hydef]
      congr 1
      ring
    rw [← e]; exact hlam
  obtain ⟨ea, eb, ec⟩ := half_core hy0 hv8 hvb hx
  set x := logb 2 d with hxdef
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hd16 : (16 : ℝ) ≤ d := by
    have h117 := hΓ.gamma2a
    unfold Gamma2a at h117
    linarith [show (16 : ℝ) ≤ 2 ^ 117 by norm_num]
  have hL2 : (logStar d : ℝ) ≤ 2 + logb 2 x := logStar_le_two_add_loglog (by linarith)
  have hL3 : (logStar d : ℝ) ≤ 3 + logb 2 (logb 2 x) := logStar_le_three_add_logloglog hd16
  have hL0 : (0 : ℝ) ≤ (logStar d' : ℝ) := Nat.cast_nonneg _
  have hXw : y / 105 ≤ logb 2 x := (Real.le_logb_iff_rpow_le (by norm_num) hx0).2 hx
  have hX0 : 0 < logb 2 x := lt_of_lt_of_le (by positivity) hXw
  have hv0 : 0 < logb 2 y := lt_of_lt_of_le (by norm_num) hv8
  have hxs : 0 < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hys : 0 < y ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hy0 _
  refine ⟨?_, ?_, ?_⟩
  · unfold towA
    rw [div_div, div_le_div_iff₀ hx0 (by positivity)]
    have h1 : (2 * (logStar d : ℝ) + 2) * y ≤ (2 * logb 2 x + 6) * y :=
      mul_le_mul_of_nonneg_right (by linarith) hy0.le
    nlinarith
  · unfold towB
    rw [div_div, div_le_div_iff₀ hX0 (by positivity)]
    have h1 : (2 * (logStar d : ℝ) + 1) * logb 2 y ≤ (7 + 2 * logb 2 (logb 2 x)) * logb 2 y :=
      mul_le_mul_of_nonneg_right (by linarith) hv0.le
    nlinarith
  · unfold towC
    rw [div_div, div_le_div_iff₀ hxs (by positivity)]
    have h1 : (2 * (logStar d : ℝ) + 1) * y ^ ((1 : ℝ) / 2) ≤
        (2 * logb 2 x + 5) * y ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hys.le
    nlinarith

end EG
