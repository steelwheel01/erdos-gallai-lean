module

public import EG.Spec.Lend.COLJVCount
public import EG.Lib.Lend.Standing
public import EG.Lib.Lend.GeomQuarter
public import EG.Lib.Stage1.COL
public import EG.Lib.HB.TowerRun
public import EG.Proof.HB.TowerA
public import EG.Proof.HB.TowerB
public import EG.Proof.HB.TowerBM
public import EG.Proof.Todo.TowerBRest

/-!
# Lemma COL-JV (i), the counting part (manuscript s3:lemCOLJV (i))

Originally a declared-input stub of unit P4A; proved in P3 (unit P3-s3) from Lemma s2:lemTower
((a): `R - r ≤ 2 log* d_r - 1`; (b): `L_Y ≤ 2λ`, `M_{r+2} ≤ M̄`, `M_{l+1} ≤ M_l/2`; (d) via
`2 log* d_r + 2 ≤ μ`), the standing bound (B4) `|V(Y)| ≥ λ^{103}/2` (so `L_Y ≥ 103μ - 1 ≥ μ`),
and column 3 of Table s3:tabCOLJV (rows 9 and 10) at `μ = log λ_r` (Γ1(f)).

Manuscript v6.1, `s3.tex`, proof of [s3:lemCOLJV], "(i) Counting. If `r ≥ R-1`, the three
index families are empty (Definition s3:defCOL(ii)), so `k_lend(Y) = 0`. Let now `r ≤ R-2`.
• `|I^U(Y)| = 4T^sl_Y(R-r-1) ≤ 4(L_Y^2+1)(2 log* d_r + 1)`. By (B5) and (B4),
  `2 log* d_r + 1 < μ ≤ L_Y`, since `L_Y ≥ 103μ-1`. Hence `|I^U(Y)| ≤ 4(L_Y^2+1)L_Y ≤ 12L_Y^3`.
• `|I^JS(Y)| = Σ_{l=r+2}^R M_l^2 ≤ M^2 Σ_{i≥0} 4^{-i} = (4/3)M^2` by (B2).
• `|I^JV(Y)| = R-r-1 ≤ 2 log* d_r + 1` by (B5).
The second inequality of the display holds because `2 log* d_r + 2 ≤ μ ≤ 12L_Y^3`. The third
follows from (B1) and (B2). The fourth is the sufficient inequality of row 9 … Then
`p_Y = 1/(2k_lend(Y)) ≥ 1/(2λ^{3.3}) ≥ λ^{-4}`, and row 10 gives the same conclusion directly."
-/

public section

namespace EG

open EG.HB

/-- Proved in P3. [s3:lemCOLJV] (i) "If `r ≥ R-1`, then `k_lend(Y) = 0`. If `r ≤ R-2`, then
`|I^U(Y)| ≤ 12L_Y^3`, `|I^JS(Y)| ≤ (4/3)M^2` and `|I^JV(Y)| = R-r-1 ≤ 2 log* d_r + 1`. Hence
`k_lend(Y) ≤ … ≤ k̄ ≤ λ^{3.3}`, and consequently `p_Y ≥ λ^{-4}`." -/
theorem colJVCount : EG.Spec.COLJVCountStatement := by
  intro V _ G Dstar run hΓ hV Y hY
  have hR := Standing.isRound_of_mem_ancestors hY
  refine ⟨fun h => ?_, fun hR2 => ?_⟩
  · by_contra hk
    have := (Stage1.klend_pos_iff (G := G) (run := run)).1 (Nat.pos_of_ne_zero hk)
    omega
  have hRi : Y.1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  have hD1 := Run.Valid.dstar_le run G hV (l := 1) ⟨le_rfl, le_trans hR.1 hR.2⟩
  have hP := Run.paramHyp hΓ.core hV hRi
  have hlam : run.lam G Y.1 = Real.logb 2 (run.d G Y.1) := rfl
  obtain ⟨-, hx0, hlamx⟩ := Standing.lam_facts hΓ hV hR
  have hmu : 256 ≤ Real.logb 2 (run.lam G Y.1) := by rw [hlam]; exact hP.mu_ge
  have hls : ((2 * logStar (run.d G Y.1) + 2 : ℕ) : ℝ) ≤ Real.logb 2 (run.lam G Y.1) := by
    rw [hlam]; exact hP.logStar_le_mu
  have hN := Standing.card_ancVerts_ge hY
  -- `L_Y ≥ 103μ - 1 ≥ μ`
  have hLμ : Real.logb 2 (run.lam G Y.1) ≤ run.LY G Y := by
    have hpos : 0 < run.lam G Y.1 ^ 103 / 2 := by positivity
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hN
    have e : Real.logb 2 (run.lam G Y.1 ^ 103 / 2) = 103 * Real.logb 2 (run.lam G Y.1) - 1 := by
      rw [Real.logb_div (by positivity) (by norm_num), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      push_cast; ring
    have hLY : run.LY G Y = Real.logb 2 ((run.ancVerts G Y).card : ℝ) := rfl
    rw [hLY]; linarith
  -- tower facts
  have hA := (towerA V G Dstar run hΓ.core hV hD1).2.2.1 Y.1 hRi
  obtain ⟨-, -, -, -, -, -, hanc⟩ := towerBRound V G Dstar run hΓ.core hV hD1 Y.1 hRi
  obtain ⟨hLΛ, hΛ⟩ := hanc Y hY rfl
  have hMb : (run.M G (Y.1 + 2) : ℝ) ≤ COLTable.Mbar (Real.logb 2 (run.lam G Y.1)) := by
    have := ((towerBM V G Dstar run hΓ.core hV hD1).1 (Y.1 + 2) (by have := hR.1; omega) hR2).1
    rwa [Nat.add_sub_cancel] at this
  have hhalf := (EG.Todo.TowerBRest V G Dstar run hΓ.core hV hD1).2.1
  have hcol := Standing.col3_at hΓ hV hR
  set x := run.lam G Y.1 with hxdef
  set μ := Real.logb 2 x with hμdef
  set L := run.LY G Y with hLdef
  set ls : ℕ := logStar (run.d G Y.1) with hlsdef
  set M : ℝ := (run.M G (Y.1 + 2) : ℝ) with hMdef
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLL3 : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
  have hRr : run.R - Y.1 - 1 ≤ 2 * ls + 1 := by omega
  have hRr' : ((run.R - Y.1 - 1 : ℕ) : ℝ) ≤ 2 * (ls : ℝ) + 1 := by exact_mod_cast hRr
  have hls' : 2 * (ls : ℝ) + 2 ≤ μ := by exact_mod_cast hls
  -- `|I^U(Y)| ≤ 12L^3`
  have hIU : ((Stage1.IU G run Y).card : ℝ) ≤ 12 * L ^ 3 := by
    by_cases hlt : run.isLight G Y.1 Y.2
    · rw [Stage1.card_IU_of_isLight hlt, show run.R + 1 - (Y.1 + 2) = run.R - Y.1 - 1 by omega]
      push_cast
      have hT : (Stage1.Tslot G run Y : ℝ) ≤ L ^ 2 + 1 := by
        unfold Stage1.Tslot
        have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ run.LY G Y ^ 2 by positivity)
        rw [← hLdef] at this
        linarith
      have hT0 : (0 : ℝ) ≤ Stage1.Tslot G run Y := Nat.cast_nonneg _
      have hr0 : (0 : ℝ) ≤ ((run.R - Y.1 - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hrL : ((run.R - Y.1 - 1 : ℕ) : ℝ) ≤ L := by linarith
      have h1 : ((run.R - Y.1 - 1 : ℕ) : ℝ) * 4 * (Stage1.Tslot G run Y : ℝ) ≤
          L * 4 * (L ^ 2 + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hrL (by norm_num)) hT hT0 (by positivity)
      have h2 : L * 4 * (L ^ 2 + 1) ≤ 12 * L ^ 3 := by nlinarith
      linarith
    · rw [Stage1.IU_eq_empty_of_not_isLight hlt, Finset.card_empty, Nat.cast_zero]
      positivity
  -- `|I^JS(Y)| = Σ_l M_l^2 ≤ (4/3)M^2`
  have hcard : (Stage1.IJS G run Y).card =
      ∑ l ∈ Stage1.lateRounds run Y.1, Stage1.KJS G run l := by
    unfold Stage1.IJS
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.card_image_of_injective _ (fun a b h => by cases h; rfl), Finset.card_range]
    · intro l _ l' _ hll'
      rw [Function.onFun, Finset.disjoint_left]
      intro t ht ht'
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨j', -, hj'⟩ := Finset.mem_image.1 ht'
      cases hj'
      exact hll' rfl
  have hIJS : ((Stage1.IJS G run Y).card : ℝ) ≤ 4 / 3 * M ^ 2 := by
    rw [hcard, Nat.cast_sum]
    have e : ∀ l, ((Stage1.KJS G run l : ℕ) : ℝ) = (run.M G l : ℝ) ^ 2 := fun l => by
      unfold Stage1.KJS; push_cast; ring
    simp only [e]
    exact sum_Icc_le_of_quarter (fun l => (run.M G l : ℝ) ^ 2) (fun _ => by positivity)
      (Y.1 + 2) run.R (fun l hl hlR => by
        have h := hhalf (l + 1) (by omega) hlR
        rw [Nat.add_sub_cancel] at h
        have h' : 2 * (run.M G (l + 1) : ℝ) ≤ run.M G l := by exact_mod_cast h
        have h0 : (0 : ℝ) ≤ run.M G (l + 1) := Nat.cast_nonneg _
        nlinarith)
  have hIJV : (Stage1.IJV run Y).card = run.R - Y.1 - 1 := by
    rw [Stage1.card_IJV]; omega
  have hk : (Stage1.klend G run Y : ℝ) ≤ 12 * L ^ 3 + 4 / 3 * M ^ 2 + 2 * (ls : ℝ) + 2 := by
    unfold Stage1.klend
    push_cast
    rw [hIJV]
    linarith
  have hk2 : 12 * L ^ 3 + 4 / 3 * M ^ 2 + 2 * (ls : ℝ) + 2 ≤ 24 * L ^ 3 + 4 / 3 * M ^ 2 := by
    linarith
  have hkb : 24 * L ^ 3 + 4 / 3 * M ^ 2 ≤ COLTable.kbar μ := by
    rw [COLTable.kbar_eq, hlamx]
    have hL2 : L ≤ 2 * x := hLΛ.trans hΛ
    have h1 : L ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ hL0 hL2 3
    have hM0 : 0 ≤ M := Nat.cast_nonneg _
    have h2 : M ^ 2 ≤ COLTable.Mbar μ ^ 2 := pow_le_pow_left₀ hM0 hMb 2
    nlinarith
  have h9 := hcol.row (i := 9) (by norm_num) (by norm_num)
  rw [COLTable.row9_iff, hlamx] at h9
  have h10 := hcol.row (i := 10) (by norm_num) (by norm_num)
  rw [COLTable.row10_iff, hlamx] at h10
  refine ⟨hIU, hIJS, hIJV, hRr, hk, hk2, hkb, h9, ?_⟩
  -- `p_Y = 1/(2k_lend) ≥ λ^{-4}`
  have hkpos : (0 : ℝ) < Stage1.klend G run Y := by
    exact_mod_cast (Stage1.klend_pos_iff (G := G) (run := run)).2 hR2
  have h2k : 2 * (Stage1.klend G run Y : ℝ) ≤ x ^ 4 := by linarith
  unfold Stage1.pY
  rw [Real.rpow_neg hx0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h2k

end EG
