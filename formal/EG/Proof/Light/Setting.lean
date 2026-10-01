module

public import EG.Spec.Light.Setting
public import EG.Proof.HB.Structure
public import EG.Proof.HB.TowerA
public import EG.Proof.Todo.TowerD
public import EG.Lib.Light.EqZpAux

/-!
# [s5:eqLY] (formerly a declared input of probe P4B; proved in P3)

Upstream s5 setting fact; used by s5:lemParent Steps 4 and 9. Design note `formal/work/p2b/P4B.md`.

Proof (P3), as in the setting paragraph of `s5.tex`: `|Y| ≥ |Y^0|/2 ≥ P_r/2` is
s2:propStructure (iv) (`EG.structureVertex`); `P_r = ⌈λ_r^{103}⌉ ≥ λ_r^{103}` (definition);
`L_Y = log₂|Y| ≥ log₂(λ_r^{103}/2) = 103 log₂λ_r − 1`; `log₂λ_r ≥ 2^8 ≥ 1` (s2:lemTower (a)
(`EG.towerA`) with Γ1 (a), `EG.Light.logb_lam_ge`); `R − r ≤ 2 log* d_r + 2` is s2:lemTower (a)
and `2^{2 log* d_r + 2} ≤ λ_r` is s2:lemTower (d) (`EG.Todo.TowerD`), whence
`2 log* d_r + 2 ≤ log₂λ_r ≤ L_Y/102`.
-/

public section

namespace EG

open EG.HB Real

/-- Proved in P3. [s5:eqLY] "for a light part `Y` of round `r`, `|Y| ≥ P_r/2 ≥ λ_r^{103}/2`, `L_Y ≥ 103 log₂λ_r − 1 ≥ 102 log₂λ_r`, `R − r ≤ 2 log* d_r + 2 ≤ log₂λ_r`". -/
theorem eqLY : EG.Spec.EqLYStatement := by
  intro V _ G N0 Dstar run hR Y hY
  have hD : Gamma1core Dstar := hR.1.1
  have hv : run.Valid G Dstar := hR.2.2.2.2.2
  have hd1 : Dstar ≤ run.d G 1 := hR.2.2.2.2.1
  have hYl := (Run.mem_lightParts run G).1 hY
  have hr : Y.1 ∈ Finset.Icc 1 run.R :=
    Finset.mem_Icc.2 (Run.isRound_of_mem_prePartAddrs hYl.1)
  have hSV := (EG.structureVertex V G Dstar run hv Y.1 hr).2.1 Y.2 hYl.1 hYl.2
  have hTA := EG.towerA V G Dstar run hD hv hd1
  have hge := EG.Light.logb_lam_ge hD hv hTA.1 Y.1 hr
  have hTD := EG.Todo.TowerD V G Dstar run hD hv hd1 Y.1 Y.1 (Finset.mem_Icc.1 hr).1 le_rfl
    (Finset.mem_Icc.1 hr).2
  set lam := run.lam G Y.1 with hlam
  have hlog1 : (2 : ℝ) ^ 8 ≤ logb 2 lam := by
    have : (1 : ℝ) ≤ 2 ^ (run.R - Y.1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hlam_pos : 0 < lam := lt_of_lt_of_le (by positivity) hTD.1
  -- (1) and (2)
  have h1 : (run.P G Y.1 : ℝ) / 2 ≤ ((run.ancVerts G Y).card : ℝ) := by
    have := hSV.1; have := hSV.2
    change (run.P G Y.1 : ℝ) / 2 ≤ ((run.partVerts G Y.1 Y.2).card : ℝ)
    linarith
  have hPge : lam ^ 103 ≤ (run.P G Y.1 : ℝ) := by
    change lam ^ 103 ≤ ((⌈lamOf (run.d G Y.1) ^ Cp⌉₊ : ℕ) : ℝ)
    exact Nat.le_ceil _
  have h2 : lam ^ 103 / 2 ≤ (run.P G Y.1 : ℝ) / 2 := by linarith
  -- (3)
  have hcard : lam ^ 103 / 2 ≤ ((run.ancVerts G Y).card : ℝ) := le_trans h2 h1
  have h3 : 103 * logb 2 lam - 1 ≤ run.LY G Y := by
    have hp : 0 < lam ^ 103 / 2 := by positivity
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hp hcard
    rw [Real.logb_div (by positivity) (by norm_num), Real.logb_pow, Real.logb_self_eq_one
      (by norm_num)] at this
    change 103 * logb 2 lam - 1 ≤ logb 2 ((run.ancVerts G Y).card : ℝ)
    push_cast at this
    linarith
  -- (4)
  have h4 : 102 * logb 2 lam ≤ 103 * logb 2 lam - 1 := by linarith
  -- (5)
  have h5 : (run.R : ℝ) - (Y.1 : ℝ) ≤ 2 * (logStar (run.d G Y.1) : ℝ) + 2 := by
    have := hTA.2.2.2.1 Y.1 hr
    exact_mod_cast this
  -- (6)
  have h6 : 2 * (logStar (run.d G Y.1) : ℝ) + 2 ≤ logb 2 lam := by
    have hA := hTD.1
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hA
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    push_cast at this
    linarith
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  linarith
