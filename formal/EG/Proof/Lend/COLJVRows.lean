module

public import EG.Spec.Lend.COLJVRows
public import EG.Defs.Stage1.Zones
public import EG.Lib.Lend.Standing
public import EG.Proof.HB.TowerB
public import EG.Proof.Lend.COLJVCount

/-!
# Rows 4, 7, 8 of the COL-JV table (manuscript s3:lemCOLJV (ii)) — unit P4A

Stage 1, fix round 1 (review `formal/work/p2b/P4A.review1.md`, issue c1): only the bridge from
the precise form of row 7 (`COLJVRow7Statement`, with `ρ_Y^{-3}` replaced by `(12L_Y^5)^3`,
hazard H3 of `formal/work/p2b/P4A.md`) to the per-class failure bound of Theorem 16* with the
zone density `ρ_Y` itself, under `ρ_Y ≥ 1/(12L_Y^5)` ([s5:lemZones] (ii), a hypothesis here).
Proof round 1: rows 4, 7, 8 (`EG.colJVRow4`, `EG.colJVRow7`, `EG.colJVRow8`), from the declared
inputs `EG.towerBRound` ([s2:lemTower] (b): (B1) `L_Y ≤ Λ_r ≤ 2λ`, (B3) `s_r ≥ λ^{100}`) and
`EG.colJVCount` ([s3:lemCOLJV] (i): `|I^U(Y)| ≤ 12L_Y^3`, `k_lend ≤ k̄ ≤ λ^{3.3}`), the standing
bounds of `EG.Lib.Lend.Standing` ((B4), `t_Y ≤ 2λ^{1.6}`, `k_own ≤ L_Y/2 + 1`) and the column-3
inequalities at `μ = log λ_r` (Γ1(f)).

Manuscript v6.1, `s3.tex`, proof of [s3:lemCOLJV], row 7: "`t = t_Y ≤ 2λ^{1.6}` and
`ρ^{-3} ≤ 1728L_Y^{15}`." (`1728 L_Y^{15} = (12L_Y^5)^3`.)
-/

public section

namespace EG

open EG.HB

/-- [s3:lemCOLJV] (proof, row 7) "`ρ^{-3} ≤ 1728L_Y^{15}`": for `ρ ≥ 1/(12L^5)` with `L > 0`,
`ρ^{-3} ≤ (12L^5)^3`. -/
theorem zpow_neg_three_le_of_ge_inv {L ρ : ℝ} (hL : 0 < L) (hρ : 1 / (12 * L ^ 5) ≤ ρ) :
    ρ ^ (-3 : ℤ) ≤ (12 * L ^ 5) ^ 3 := by
  have hA : 0 < 12 * L ^ 5 := by positivity
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  have hinv : ρ⁻¹ ≤ 12 * L ^ 5 := by
    rw [one_div] at hρ
    calc ρ⁻¹ ≤ (12 * L ^ 5)⁻¹⁻¹ := inv_anti₀ (by positivity) hρ
      _ = 12 * L ^ 5 := inv_inv _
  rw [zpow_neg, ← inv_zpow, zpow_ofNat]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hρ0.le) hinv 3

/-- [s3:lemCOLJV] (ii), row 7, in the form of Theorem 16* (bridge for the consumer
[s3:lemCOL] (c); review P4A.review1 c1): "T16* failures over `I^U(Y)` sum to at most
`|V(Y)|^{-2}/4`", with the per-class failure bound `2^{86} t_Y L_Y^{19} ρ_Y^{-3} N^{-3}`
(`N = |V(Y)|`, `ρ_Y = EG.Stage1.rhoY`), from `COLJVRow7Statement` and the zone density
`ρ_Y ≥ 1/(12L_Y^5)` of [s5:lemZones] (ii) (a hypothesis, with `L_Y > 0`). -/
theorem colJVRow7_rhoY.{u} (h7 : EG.Spec.COLJVRow7Statement.{u}) {V : Type u} [DecidableEq V]
    (G : FGraph V) (Dstar : ℝ) (run : Run V) (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar)
    (Y : PartId) (hY : Y ∈ run.ancestors G) (hR : Y.1 + 2 ≤ run.R) (hL : 0 < run.LY G Y)
    (hρ : 1 / (12 * run.LY G Y ^ 5) ≤ Stage1.rhoY G run Y) :
    ∑ _i ∈ Stage1.IU G run Y,
        (2 : ℝ) ^ 86 * (Stage1.tY G run Y : ℝ) * run.LY G Y ^ 19 *
          Stage1.rhoY G run Y ^ (-3 : ℤ) * ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) ≤
      ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 4 := by
  refine le_trans (Finset.sum_le_sum fun _ _ => ?_) (h7 V G Dstar run hΓ hV Y hY hR)
  have h3 := zpow_neg_three_le_of_ge_inv hL hρ
  gcongr

/-! ### Rows 4, 7, 8 (proof round 1) -/

universe u

section Rows

variable {V : Type u} [DecidableEq V] {G : FGraph V} {Dstar : ℝ} {run : Run V}

/-- The standing bounds used by the three rows, at an ancestor `Y` of round `r`:
`λ = λ_r ≥ 2^{256}`, `0 ≤ L_Y ≤ 2λ` ((B1)), `λ^{100} ≤ s_r` ((B3)), and column 3 at `μ = log λ`
with `2^μ = λ`. -/
theorem colJV_rows_setup (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {Y : PartId}
    (hY : Y ∈ run.ancestors G) :
    (2 : ℝ) ^ 256 ≤ run.lam G Y.1 ∧ 0 ≤ run.LY G Y ∧ run.LY G Y ≤ 2 * run.lam G Y.1 ∧
      run.lam G Y.1 ^ 100 ≤ (run.s G Y.1 : ℝ) ∧ COLTable.col3 (Real.logb 2 (run.lam G Y.1)) ∧
      COLTable.lam (Real.logb 2 (run.lam G Y.1)) = run.lam G Y.1 := by
  have hR := Standing.isRound_of_mem_ancestors hY
  have hR1 : run.IsRound 1 := ⟨le_rfl, le_trans hR.1 hR.2⟩
  obtain ⟨-, -, -, hs100, -, -, hanc⟩ := towerBRound V G Dstar run hΓ.core hV
    (Run.Valid.dstar_le run G hV hR1) Y.1 (Finset.mem_Icc.2 hR)
  obtain ⟨hLΛ, hΛ⟩ := hanc Y hY rfl
  exact ⟨Standing.lam_ge hΓ hV hR, Standing.LY_nonneg Y, hLΛ.trans hΛ, hs100,
    Standing.col3_at hΓ hV hR, (Standing.lam_facts hΓ hV hR).2.2⟩

/-- `L^m · log₂ L ≤ (2λ)^m (μ + 1)` for `0 ≤ L ≤ 2λ`, `λ > 0`, `μ = log₂ λ ≥ -1`: "`log L_Y ≤ μ + 1`.
The right sides are increasing in `L_Y`". -/
theorem colJV_pow_mul_logb_le {L x : ℝ} (m : ℕ) (hL0 : 0 ≤ L) (hLx : L ≤ 2 * x) (hx : 0 < x)
    (hμ : -1 ≤ Real.logb 2 x) :
    L ^ m * Real.logb 2 L ≤ (2 * x) ^ m * (Real.logb 2 x + 1) := by
  by_cases hlg : Real.logb 2 L ≤ 0
  · have h1 : L ^ m * Real.logb 2 L ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hL0 m) hlg
    have h2 : 0 ≤ (2 * x) ^ m * (Real.logb 2 x + 1) :=
      mul_nonneg (pow_nonneg (by positivity) m) (by linarith)
    linarith
  · push Not at hlg
    have hLpos : 0 < L := by
      rcases hL0.eq_or_lt with h | h
      · rw [← h, Real.logb_zero] at hlg; exact absurd hlg (lt_irrefl 0)
      · exact h
    have hlog : Real.logb 2 L ≤ Real.logb 2 x + 1 := by
      calc Real.logb 2 L ≤ Real.logb 2 (2 * x) := Real.logb_le_logb_of_le (by norm_num) hLpos hLx
        _ = Real.logb 2 x + 1 := by
          rw [Real.logb_mul (by norm_num) hx.ne', Real.logb_self_eq_one (by norm_num)]; ring
    exact mul_le_mul (pow_le_pow_left₀ hL0 hLx m) hlog hlg.le (pow_nonneg (by positivity) m)

/-- [s3:lemCOLJV] (ii), row 8: "By (B3), `s_r/4 ≥ λ^{100}/4` and `s_r/2 ≥ λ^{100}/2`. Also
`k_own ≤ L_Y ≤ 2λ`, so `s' ≥ λ^{99}/32`, and `log L_Y ≤ μ + 1`. The right sides are increasing
in `L_Y`. Substituting `L_Y ≤ 2λ` gives the four inequalities." (Here `k_own ≤ L_Y/2 + 1 ≤ 2λ`.) -/
theorem colJVRow8 : EG.Spec.COLJVRow8Statement.{u} := by
  intro V _ G Dstar run hΓ hV Y hY
  obtain ⟨hx, hL0, hLx, hs, hcol, hlam⟩ := colJV_rows_setup hΓ hV hY
  have h8 := hcol.row (i := 8) (by norm_num) (by norm_num)
  rw [COLTable.row8_iff, hlam] at h8
  obtain ⟨h8a, h8b, h8c, h8d, h8e⟩ := h8
  have hk := Standing.kown_le (G := G) (run := run) Y
  have hk1 : (1 : ℝ) ≤ Stage1.kown G run Y := by exact_mod_cast Stage1.one_le_kown G run Y
  set x := run.lam G Y.1 with hxdef
  set L := run.LY G Y
  set s : ℝ := (run.s G Y.1 : ℝ)
  set k : ℝ := (Stage1.kown G run Y : ℝ)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hμ : (2 : ℝ) ^ 8 ≤ Real.logb 2 x := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hx0]
    calc (2 : ℝ) ^ ((2 : ℝ) ^ 8) = (2 : ℝ) ^ 256 := by rw [← Real.rpow_natCast]; norm_num
      _ ≤ x := hx
  set μ := Real.logb 2 x
  have hx42 : 0 ≤ x ^ 42 := by positivity
  have hx38 : 0 ≤ x ^ 38 := by positivity
  have hx41 : 0 ≤ x ^ 41 := by positivity
  have e100a : x ^ 100 = x ^ 58 * x ^ 42 := by rw [← pow_add]
  have e100b : x ^ 100 = x ^ 62 * x ^ 38 := by rw [← pow_add]
  have e99 : x ^ 99 = x ^ 58 * x ^ 41 := by rw [← pow_add]
  -- (a)
  have ha : (2 : ℝ) ^ 150 * L ^ 42 ≤ s / 4 := by
    have h1 : L ^ 42 ≤ (2 * x) ^ 42 := pow_le_pow_left₀ hL0 hLx 42
    rw [mul_pow] at h1
    have h2 := mul_le_mul_of_nonneg_right h8a hx42
    nlinarith
  -- (b), (c)
  have hlog := colJV_pow_mul_logb_le 38 hL0 hLx hx0 (by linarith)
  rw [mul_pow] at hlog
  have hb : (2 : ℝ) ^ 146 * L ^ 38 * Real.logb 2 L ≤ s / 4 := by
    have h2 := mul_le_mul_of_nonneg_right h8b hx38
    have h3 : 0 ≤ (μ + 1) * x ^ 38 := by positivity
    nlinarith
  have hc : (2 : ℝ) ^ 151 * L ^ 38 * Real.logb 2 L ≤ s / 2 := by
    have h2 := mul_le_mul_of_nonneg_right h8c hx38
    have h3 : 0 ≤ (μ + 1) * x ^ 38 := by positivity
    nlinarith
  -- (d): `s' ≥ λ^{99}/32`
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk1
  have hk2 : k ≤ 2 * x := by linarith
  have hs' : x ^ 99 / 32 ≤ s / (16 * k) := by
    rw [le_div_iff₀ (by positivity)]
    have : x ^ 99 / 32 * (16 * k) ≤ x ^ 99 / 32 * (16 * (2 * x)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : x ^ 99 / 32 * (16 * (2 * x)) = x ^ 100 := by ring
    linarith
  have hd1 : (2 : ℝ) ^ 145 * L ^ 41 ≤ s / (16 * k) := by
    have h1 : L ^ 41 ≤ (2 * x) ^ 41 := pow_le_pow_left₀ hL0 hLx 41
    rw [mul_pow] at h1
    have h2 := mul_le_mul_of_nonneg_right h8d hx41
    nlinarith
  have hd2 : 2 * (⌈L ^ 6⌉₊ : ℝ) ≤ s / (16 * k) := by
    have h1 : L ^ 6 ≤ (2 * x) ^ 6 := pow_le_pow_left₀ hL0 hLx 6
    have h2 : (⌈L ^ 6⌉₊ : ℝ) < L ^ 6 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : 64 * ((2 * x) ^ 6 + 1) ≤ x ^ 99 := h8e
    linarith
  exact ⟨ha, hb, hc, hd1, hd2⟩

/-- `x^{a} x^{b} = x^{a+b}` for real exponents and `x > 0`, with a natural-power factor. -/
theorem colJV_rpow_split4 {x : ℝ} (hx : 0 < x) (a b c : ℝ) (n m : ℕ) (h : a + b + c + n = m) :
    x ^ a * x ^ b * x ^ c * x ^ n = x ^ m := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_natCast x m, ← Real.rpow_add hx, ← Real.rpow_add hx,
    ← Real.rpow_add hx, h]

/-- `k_lend(Y) ≤ λ^{3.3}` and `k_lend(Y) > 0` for `r ≤ R - 2` (from the declared input
[s3:lemCOLJV] (i)), and `|I^U(Y)| ≤ 12L_Y^3`. -/
theorem colJV_klend_facts (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {Y : PartId}
    (hY : Y ∈ run.ancestors G) (hR2 : Y.1 + 2 ≤ run.R) :
    0 < (Stage1.klend G run Y : ℝ) ∧
      (Stage1.klend G run Y : ℝ) ≤ run.lam G Y.1 ^ (33 / 10 : ℝ) ∧
      ((Stage1.IU G run Y).card : ℝ) ≤ 12 * run.LY G Y ^ 3 := by
  obtain ⟨-, hc⟩ := colJVCount V G Dstar run hΓ hV Y hY
  obtain ⟨hIU, -, -, -, hk1, hk2, hk3, hk4, -⟩ := hc hR2
  refine ⟨by exact_mod_cast (Stage1.klend_pos_iff (G := G) (run := run)).2 hR2, ?_, hIU⟩
  linarith

/-- `s_Y ≥ s_r/2` ((B3), Definition s2:defAncestors). -/
theorem colJV_ancS_ge (Y : PartId) : (run.s G Y.1 : ℝ) / 2 ≤ run.ancS G Y := by
  classical
  unfold Run.ancS
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) ≤ run.s G Y.1 := Nat.cast_nonneg _
    linarith

/-- [s3:lemCOLJV] (ii), row 4: "Theorem 16*, with `t = t_Y = ⌈λ^{1.6}⌉ ≤ 2λ^{1.6}` and
`ρ ≥ 1/(12L_Y^5)`, requires `s ≥ 2^{135}tL_Y^{28}ρ^{-5}`, and
`2^{135}tL_Y^{28}ρ^{-5} ≤ 2^{136}12^5λ^{1.6}L_Y^{53}`. With `s = s_Y/(8k_lend) ≥ λ^{100}/(16k̄)`
and `L_Y ≤ 2λ`, it suffices that `λ^{100} ≥ 2^{4+136+53}12^5k̄λ^{54.6}`, i.e.
`λ^{45.4} ≥ 2^{193}·12^5·k̄`. By row 9, `k̄ ≤ λ^{3.3}`, so the sufficient inequality of column 3,
`λ^{42.1} ≥ 2^{193}·12^5`, implies it." (`k_lend ≤ λ^{3.3}` is taken from (i).) -/
theorem colJVRow4 : EG.Spec.COLJVRow4Statement.{u} := by
  intro V _ G Dstar run hΓ hV Y hY hR2
  obtain ⟨hx, hL0, hLx, hs, hcol, hlam⟩ := colJV_rows_setup hΓ hV hY
  have h4 := hcol.row (i := 4) (by norm_num) (by norm_num)
  rw [COLTable.row4_iff, hlam] at h4
  obtain ⟨hk0, hk, -⟩ := colJV_klend_facts hΓ hV hY hR2
  have hS := colJV_ancS_ge (G := G) (run := run) Y
  have hx0 : 0 < run.lam G Y.1 := lt_of_lt_of_le (by norm_num) hx
  have ht := Standing.tY_le (G := G) (run := run) (Y := Y) (le_trans (by norm_num) hx)
  have ht0 : (0 : ℝ) ≤ Stage1.tY G run Y := Nat.cast_nonneg _
  set x := run.lam G Y.1
  set L := run.LY G Y
  set t : ℝ := (Stage1.tY G run Y : ℝ)
  set k : ℝ := (Stage1.klend G run Y : ℝ)
  set a := x ^ (8 / 5 : ℝ)
  set b := x ^ (33 / 10 : ℝ)
  set c := x ^ (421 / 10 : ℝ)
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hx0 _
  have hc0 : 0 < c := Real.rpow_pos_of_pos hx0 _
  have e100 : c * a * b * x ^ 53 = x ^ 100 := colJV_rpow_split4 hx0 _ _ _ 53 100 (by norm_num)
  have hL53 : L ^ 53 ≤ (2 * x) ^ 53 := pow_le_pow_left₀ hL0 hLx 53
  rw [mul_pow] at hL53
  have hx53 : 0 ≤ x ^ 53 := by positivity
  -- the left side
  have hlhs : (2 : ℝ) ^ 135 * t * L ^ 28 * (12 * L ^ 5) ^ 5 ≤
      (2 : ℝ) ^ 189 * 12 ^ 5 * a * x ^ 53 := by
    have e : (2 : ℝ) ^ 135 * t * L ^ 28 * (12 * L ^ 5) ^ 5 = (2 : ℝ) ^ 135 * 12 ^ 5 * t * L ^ 53 := by
      ring
    rw [e]
    have h1 : t * L ^ 53 ≤ (2 * a) * (2 ^ 53 * x ^ 53) :=
      mul_le_mul ht hL53 (pow_nonneg hL0 _) (by positivity)
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have h8k : 8 * k ≤ 8 * b := by linarith
  calc (2 : ℝ) ^ 135 * t * L ^ 28 * (12 * L ^ 5) ^ 5 * (8 * k)
      ≤ (2 : ℝ) ^ 189 * 12 ^ 5 * a * x ^ 53 * (8 * b) :=
        mul_le_mul hlhs h8k (by positivity) (by positivity)
    _ = (2 : ℝ) ^ 193 * 12 ^ 5 * (a * b * x ^ 53) / 2 := by ring
    _ ≤ c * (a * b * x ^ 53) / 2 := by gcongr
    _ = x ^ 100 / 2 := by rw [← e100]; ring
    _ ≤ run.ancS G Y := by linarith

/-- [s3:lemCOLJV] (ii), row 7: "There are at most `12L_Y^3` U-classes, each with
`t = t_Y ≤ 2λ^{1.6}` and `ρ^{-3} ≤ 1728L_Y^{15}`. The sum is at most
`12L_Y^3·2^{86}·2λ^{1.6}L_Y^{19}·12^3L_Y^{15}N^{-3} = 12^4·2^{87}λ^{1.6}L_Y^{37}N^{-3} ≤
12^4·2^{124}λ^{38.6}N^{-3}`. This is at most `N^{-2}/4` if `N ≥ 12^4·2^{126}λ^{38.6}`, which by
(B4) follows from `λ^{103}/2 ≥ 12^4·2^{126}λ^{38.6}`, i.e. `λ^{64.4} ≥ 2^{127}·12^4`." -/
theorem colJVRow7 : EG.Spec.COLJVRow7Statement.{u} := by
  intro V _ G Dstar run hΓ hV Y hY hR2
  obtain ⟨hx, hL0, hLx, -, hcol, hlam⟩ := colJV_rows_setup hΓ hV hY
  have h7 := hcol.row (i := 7) (by norm_num) (by norm_num)
  rw [COLTable.row7_iff, hlam] at h7
  obtain ⟨-, -, hIU⟩ := colJV_klend_facts hΓ hV hY hR2
  have hN := Standing.card_ancVerts_ge hY
  have hx0 : 0 < run.lam G Y.1 := lt_of_lt_of_le (by norm_num) hx
  have ht := Standing.tY_le (G := G) (run := run) (Y := Y) (le_trans (by norm_num) hx)
  have ht0 : (0 : ℝ) ≤ Stage1.tY G run Y := Nat.cast_nonneg _
  rw [Finset.sum_const, nsmul_eq_mul]
  set x := run.lam G Y.1
  set L := run.LY G Y
  set t : ℝ := (Stage1.tY G run Y : ℝ)
  set N : ℝ := ((run.ancVerts G Y).card : ℝ)
  set I : ℝ := ((Stage1.IU G run Y).card : ℝ)
  set a := x ^ (8 / 5 : ℝ)
  set c := x ^ (322 / 5 : ℝ)
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx0 _
  have hc0 : 0 < c := Real.rpow_pos_of_pos hx0 _
  have e103 : c * a * x ^ 37 = x ^ 103 := by
    have := colJV_rpow_split4 hx0 (322 / 5) (8 / 5) 0 37 103 (by norm_num)
    rwa [Real.rpow_zero, mul_one] at this
  have hL37 : L ^ 37 ≤ (2 * x) ^ 37 := pow_le_pow_left₀ hL0 hLx 37
  rw [mul_pow] at hL37
  have hI0 : 0 ≤ I := Nat.cast_nonneg _
  have hx37 : 0 ≤ x ^ 37 := by positivity
  have hN0 : 0 < N := by
    have : 0 < x ^ 103 := by positivity
    linarith
  -- the total `I · 2^{86} t L^{19} (12L^5)^3 ≤ N/4`
  have hK : I * ((2 : ℝ) ^ 86 * t * L ^ 19 * (12 * L ^ 5) ^ 3) ≤ N / 4 := by
    have e : I * ((2 : ℝ) ^ 86 * t * L ^ 19 * (12 * L ^ 5) ^ 3) =
        (2 : ℝ) ^ 86 * 12 ^ 3 * (I * (t * L ^ 34)) := by ring
    rw [e]
    have h1 : I * (t * L ^ 34) ≤ (12 * L ^ 3) * (2 * a * L ^ 34) :=
      mul_le_mul hIU (mul_le_mul_of_nonneg_right ht (pow_nonneg hL0 _))
        (mul_nonneg ht0 (pow_nonneg hL0 _)) (by positivity)
    have e2 : (12 * L ^ 3) * (2 * a * L ^ 34) = 24 * a * L ^ 37 := by ring
    have h2 : 24 * a * L ^ 37 ≤ 24 * a * (2 ^ 37 * x ^ 37) :=
      mul_le_mul_of_nonneg_left hL37 (by positivity)
    have h3 : (2 : ℝ) ^ 127 * 12 ^ 4 * (a * x ^ 37) ≤ c * (a * x ^ 37) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    have h4 : c * (a * x ^ 37) = x ^ 103 := by rw [← e103]; ring
    nlinarith
  have hN3 : (0 : ℝ) < N ^ 3 := by positivity
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  calc I * ((2 : ℝ) ^ 86 * t * L ^ 19 * (12 * L ^ 5) ^ 3 * (N ^ 3)⁻¹)
      = I * ((2 : ℝ) ^ 86 * t * L ^ 19 * (12 * L ^ 5) ^ 3) * (N ^ 3)⁻¹ := by ring
    _ ≤ N / 4 * (N ^ 3)⁻¹ := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = (N ^ 2)⁻¹ / 4 := by field_simp

end Rows

end EG
