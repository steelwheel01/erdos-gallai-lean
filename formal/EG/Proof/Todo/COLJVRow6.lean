module

public import EG.Spec.Lend.COLJV
public import EG.Proof.Lend.COLJVRows
public import EG.Proof.HB.TowerBM
public import EG.Proof.Todo.TowerBRest
public import EG.Lib.Stage1.COL
public import EG.Lib.HB.TowerRun

/-!
# P3 stub: `EG.Spec.COLJVRow6Statement` (s3:lemCOLJV)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.COLJVRow6`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemCOLJV] see `EG.Spec.COLJVRow6Statement`. -/
theorem COLJVRow6 : EG.Spec.COLJVRow6Statement := by
  intro V _ G Dstar run hΓ hV Y hY hR2
  obtain ⟨hx, hL0, hLx, -, hcol, hlam⟩ := colJV_rows_setup hΓ hV hY
  have h6 := hcol.row (i := 6) (by norm_num) (by norm_num)
  rw [COLTable.row6_iff, hlam] at h6
  have hN := Standing.card_ancVerts_ge hY
  have hR := Standing.isRound_of_mem_ancestors hY
  have hD1 := HB.Run.Valid.dstar_le run G hV (l := 1) ⟨le_rfl, le_trans hR.1 hR.2⟩
  have hMb : (run.M G (Y.1 + 2) : ℝ) ≤ COLTable.Mbar (Real.logb 2 (run.lam G Y.1)) := by
    have := ((towerBM V G Dstar run hΓ.core hV hD1).1 (Y.1 + 2) (by have := hR.1; omega) hR2).1
    rwa [Nat.add_sub_cancel] at this
  -- `|I^JS(Y)| = Σ_l K^JS_l ≤ (4/3) M^2`
  have hIJS : ((Stage1.IJS G run Y).card : ℝ) ≤ 4 / 3 * (run.M G (Y.1 + 2) : ℝ) ^ 2 := by
    obtain ⟨-, hc⟩ := colJVCount V G Dstar run hΓ hV Y hY
    exact (hc hR2).2.1
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
  -- monotonicity `M_l ≤ M_{r+2}` and `M_l ≥ 2^{40}` for `r+2 ≤ l ≤ R`
  have hhalf := (EG.Todo.TowerBRest V G Dstar run hΓ.core hV hD1).2.1
  have hmono : ∀ k : ℕ, Y.1 + 2 + k ≤ run.R → run.M G (Y.1 + 2 + k) ≤ run.M G (Y.1 + 2) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      have h1 := hhalf (Y.1 + 2 + (k + 1)) (by omega) hk
      rw [show Y.1 + 2 + (k + 1) - 1 = Y.1 + 2 + k by omega] at h1
      have := ih (by omega)
      omega
  have hlate : ∀ l ∈ Stage1.lateRounds run Y.1,
      run.M G l ≤ run.M G (Y.1 + 2) ∧ (2 : ℝ) ^ 40 ≤ (run.M G l : ℝ) := by
    intro l hl
    obtain ⟨h1, h2⟩ := (Stage1.mem_lateRounds run).1 hl
    refine ⟨?_, ?_⟩
    · have := hmono (l - (Y.1 + 2)) (by omega)
      rwa [show Y.1 + 2 + (l - (Y.1 + 2)) = l by omega] at this
    · exact HB.ParamHyp.two40_le_M (d := run.d G l)
  set x := run.lam G Y.1 with hxdef
  set L := run.LY G Y
  set Mb := COLTable.Mbar (Real.logb 2 x)
  set M : ℝ := (run.M G (Y.1 + 2) : ℝ)
  set N : ℝ := ((run.ancVerts G Y).card : ℝ)
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hMb0 : 0 ≤ Mb := COLTable.Mbar_nonneg' _
  have hN0 : 0 < N := by
    have : 0 < x ^ 103 := pow_pos hx0 _
    linarith
  have hNi : 0 ≤ N ^ (-3 : ℤ) := zpow_nonneg hN0.le _
  set C : ℝ := (2 : ℝ) ^ 86 * (3 * M) * (2 * x) ^ 19 * M ^ 12 * N ^ (-3 : ℤ) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (pow_nonneg (by linarith) _)) (pow_nonneg hM0 _)) hNi
  -- each class
  have hterm : ∀ l ∈ Stage1.lateRounds run Y.1,
      ∑ _j ∈ Finset.range (Stage1.KJS G run l),
          (2 : ℝ) ^ 86 * (Stage1.tJS G run l : ℝ) * L ^ 19 *
            Stage1.rhoJS G run l ^ (-3 : ℤ) * N ^ (-3 : ℤ) ≤
        (Stage1.KJS G run l : ℝ) * C := by
    intro l hl
    obtain ⟨hml, h40⟩ := hlate l hl
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hMl : (run.M G l : ℝ) ≤ M := (Nat.cast_le.2 hml : ((run.M G l : ℕ) : ℝ) ≤ (run.M G (Y.1 + 2) : ℝ))
    have hMl0 : (0 : ℝ) ≤ run.M G l := Nat.cast_nonneg _
    have ht : (Stage1.tJS G run l : ℝ) ≤ 3 * M := by
      unfold Stage1.tJS; push_cast; linarith
    have hρ : Stage1.rhoJS G run l ^ (-3 : ℤ) = (run.M G l : ℝ) ^ 12 := by
      unfold Stage1.rhoJS
      rw [← zpow_mul]; norm_num
    rw [hρ, hC]
    have ht0 : (0 : ℝ) ≤ Stage1.tJS G run l := Nat.cast_nonneg _
    have h3M : (0 : ℝ) ≤ 2 ^ 86 * (3 * M) := mul_nonneg (by norm_num) (by linarith)
    have hx2 : (0 : ℝ) ≤ 2 * x := by linarith
    have h1 : (2 : ℝ) ^ 86 * (Stage1.tJS G run l : ℝ) * L ^ 19 * (run.M G l : ℝ) ^ 12 ≤
        (2 : ℝ) ^ 86 * (3 * M) * (2 * x) ^ 19 * M ^ 12 :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num))
        (pow_le_pow_left₀ hL0 hLx 19) (pow_nonneg hL0 _) h3M)
        (pow_le_pow_left₀ hMl0 hMl 12) (pow_nonneg hMl0 _) (mul_nonneg h3M (pow_nonneg hx2 _))
    exact mul_le_mul_of_nonneg_right h1 hNi
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : (∑ l ∈ Stage1.lateRounds run Y.1, (Stage1.KJS G run l : ℝ)) ≤ 4 / 3 * M ^ 2 := by
    rw [← Nat.cast_sum, ← hcard]; exact hIJS
  refine (mul_le_mul_of_nonneg_right hsum hC0).trans ?_
  -- `(4/3) M^2 C = 2^{107} x^{19} M^{15} N^{-3} ≤ N^{-2}/4`
  have hM15 : M ^ 15 ≤ Mb ^ 15 := pow_le_pow_left₀ hM0 hMb 15
  have hkey : (2 : ℝ) ^ 109 * x ^ 19 * M ^ 15 ≤ N := by
    have h1 : (2 : ℝ) ^ 109 * x ^ 19 * M ^ 15 ≤ (2 : ℝ) ^ 109 * x ^ 19 * Mb ^ 15 :=
      mul_le_mul_of_nonneg_left hM15 (mul_nonneg (by norm_num) (pow_nonneg hx0.le _))
    have h2 : (2 : ℝ) ^ 110 * Mb ^ 15 * x ^ 19 ≤ x ^ 84 * x ^ 19 :=
      mul_le_mul_of_nonneg_right h6 (pow_nonneg hx0.le _)
    have e : x ^ 84 * x ^ 19 = x ^ 103 := by ring
    nlinarith
  rw [hC, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  have hN3 : 0 < N ^ 3 := pow_pos hN0 3
  have e : 4 / 3 * M ^ 2 * ((2 : ℝ) ^ 86 * (3 * M) * (2 * x) ^ 19 * M ^ 12 * (N ^ 3)⁻¹) =
      ((2 : ℝ) ^ 109 * x ^ 19 * M ^ 15) / N * ((N ^ 2)⁻¹ / 4) := by
    field_simp; ring
  rw [e]
  have hq : ((2 : ℝ) ^ 109 * x ^ 19 * M ^ 15) / N ≤ 1 := by
    rw [div_le_one hN0]; exact hkey
  have hN2 : 0 ≤ (N ^ 2)⁻¹ / 4 := div_nonneg (inv_nonneg.2 (pow_nonneg hN0.le _)) (by norm_num)
  calc ((2 : ℝ) ^ 109 * x ^ 19 * M ^ 15) / N * ((N ^ 2)⁻¹ / 4) ≤ 1 * ((N ^ 2)⁻¹ / 4) :=
        mul_le_mul_of_nonneg_right hq hN2
    _ = (N ^ 2)⁻¹ / 4 := one_mul _

end EG.Todo
