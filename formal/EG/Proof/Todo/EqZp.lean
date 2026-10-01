module

public import EG.Spec.Light.Setting
public import EG.Spec.HB.TowerA
public import EG.Spec.HB.StructureLight
public import EG.Proof.HB.TowerA
public import EG.Proof.HB.StructureLight
public import EG.Proof.Light.Setting
public import EG.Lib.Light.EqZpAux

/-!
# P3 stub: `EG.Spec.EqZpStatement` (s5:eqZp)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.EqZp`; consumers import this module.

Proof (P3), as in the setting paragraph of `s5.tex`: `v` lies in at most one light part per round
(s2:propStructure (iv), `EG.structureLight`); by (s5:eqLY) (`EG.eqLY`, the declared input of
probe P4B) `L_Y^{-2} ≤ (102 log₂λ_r)^{-2}`; by s2:lemTower (a) (`EG.towerA`) and Γ1 (a), (b),
`log₂λ_r ≥ 2^8·2^{R−r}` (`EG.Light.logb_lam_ge`); the geometric sum gives
`Σ ≤ 2 (102·2^8)^{-2} < 1/2`.
-/

public section

namespace EG.Todo

open EG.HB EG.Light Real

/-- Proved in P3. [s5:eqZp] see `EG.Spec.EqZpStatement`. -/
theorem EqZp : EG.Spec.EqZpStatement := by
  classical
  intro V _ G N0 Dstar run hR v
  have hD : Gamma1core Dstar := hR.1.1
  have hv : run.Valid G Dstar := hR.2.2.2.2.2
  have hd1 : Dstar ≤ run.d G 1 := hR.2.2.2.2.1
  have hTA := (EG.towerA V G Dstar run hD hv hd1).1
  have hge := logb_lam_ge hD hv hTA
  have hLY := EG.eqLY V G N0 Dstar run hR
  have hSL := EG.structureLight V G N0 Dstar run hR
  set S := (run.lightParts G).filter (fun Y => v ∈ run.ancVerts G Y) with hS
  set g : ℕ → ℝ := fun r => ((102 * logb 2 (run.lam G r)) ^ 2)⁻¹ with hg
  -- rounds of light parts are rounds of the run
  have hround : ∀ Y ∈ run.lightParts G, Y.1 ∈ Finset.Icc 1 run.R := by
    intro Y hY
    have := Run.isRound_of_mem_parts run G (Finset.mem_filter.1 hY).1
    exact Finset.mem_Icc.2 this
  -- step 1: each term is at most `g r`
  have h1 : ∀ Y ∈ S, run.LY G Y ^ (-2 : ℤ) ≤ g Y.1 := by
    intro Y hY
    have hYl := (Finset.mem_filter.1 hY).1
    obtain ⟨-, -, -, h102, -, -, -⟩ := hLY Y hYl
    have hL := (hLY Y hYl).2.2.1
    have hpos : 0 < 102 * logb 2 (run.lam G Y.1) := by
      have := hge Y.1 (hround Y hYl)
      have : (0 : ℝ) < 2 ^ 8 * 2 ^ (run.R - Y.1) := by positivity
      linarith
    have hle : 102 * logb 2 (run.lam G Y.1) ≤ run.LY G Y := by linarith
    rw [zpow_neg, zpow_ofNat]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hle 2)
  -- step 2: injectivity of `Y ↦ r(Y)` on `S`
  have hinj : Set.InjOn Prod.fst (S : Set PartId) := by
    intro Y hY Y' hY' h
    by_contra hne
    have hY1 := Finset.mem_filter.1 hY
    have hY2 := Finset.mem_filter.1 hY'
    exact Finset.disjoint_left.1 (hSL Y hY1.1 Y' hY2.1 h hne) hY1.2 hY2.2
  have hg0 : ∀ r, 0 ≤ g r := fun r => by positivity
  -- step 3: `g r ≤ (1/2)^{R−r} / (102·2^8)^2`
  have h3 : ∀ r ∈ Finset.Icc 1 run.R, g r ≤ (1 / (2 : ℝ)) ^ (run.R - r) / (102 * 2 ^ 8) ^ 2 := by
    intro r hr
    have hy := hge r hr
    set k := run.R - r
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hsq : (102 * 2 ^ 8) ^ 2 * (2 : ℝ) ^ k ≤ (102 * logb 2 (run.lam G r)) ^ 2 := by
      have hA : (0 : ℝ) ≤ 102 * (2 ^ 8 * 2 ^ k) := by positivity
      have hB : 102 * (2 ^ 8 * 2 ^ k) ≤ 102 * logb 2 (run.lam G r) := by linarith
      have := pow_le_pow_left₀ hA hB 2
      have e : (102 * (2 ^ 8 * (2 : ℝ) ^ k)) ^ 2 = (102 * 2 ^ 8) ^ 2 * (2 ^ k * 2 ^ k) := by ring
      rw [e] at this
      have : (102 * 2 ^ 8) ^ 2 * (2 : ℝ) ^ k ≤ (102 * 2 ^ 8) ^ 2 * (2 ^ k * 2 ^ k) := by
        have := mul_le_mul_of_nonneg_left h2k (show (0 : ℝ) ≤ 2 ^ k by positivity)
        nlinarith
      linarith
    have hpos : (0 : ℝ) < (102 * 2 ^ 8) ^ 2 * 2 ^ k := by positivity
    calc g r ≤ ((102 * 2 ^ 8) ^ 2 * (2 : ℝ) ^ k)⁻¹ := inv_anti₀ hpos hsq
      _ = (1 / (2 : ℝ)) ^ k / (102 * 2 ^ 8) ^ 2 := by
        rw [one_div_pow, mul_inv, div_eq_mul_inv, one_div, mul_comm]
  calc ∑ Y ∈ S, run.LY G Y ^ (-2 : ℤ)
      ≤ ∑ Y ∈ S, g Y.1 := Finset.sum_le_sum h1
    _ = ∑ r ∈ S.image Prod.fst, g r := (Finset.sum_image hinj).symm
    _ ≤ ∑ r ∈ Finset.Icc 1 run.R, g r := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ => hg0 r
        intro r hr
        obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hr
        exact hround Y (Finset.mem_filter.1 hY).1
    _ ≤ ∑ r ∈ Finset.Icc 1 run.R, (1 / (2 : ℝ)) ^ (run.R - r) / (102 * 2 ^ 8) ^ 2 :=
        Finset.sum_le_sum h3
    _ = (∑ r ∈ Finset.Icc 1 run.R, (1 / (2 : ℝ)) ^ (run.R - r)) / (102 * 2 ^ 8) ^ 2 := by
        rw [Finset.sum_div]
    _ ≤ 2 / (102 * 2 ^ 8) ^ 2 := by
        gcongr
        exact sum_Icc_half_pow_le run.R
    _ < 1 / 2 := by norm_num

end EG.Todo
