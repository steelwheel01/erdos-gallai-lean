module

public import EG.Spec.Light.Stages
public import EG.Proof.HB.Structure
public import EG.Proof.HB.TowerB
public import EG.Proof.Todo.StructureExp
public import EG.Proof.Todo.TowerD
public import EG.Proof.Todo.HB
public import EG.Lib.HB.TowerRun
public import EG.Lib.Gamma.Full

/-!
# [s5:defStages] embedded claims (formerly a declared input of probe P4B; proved in P3)

Upstream s5 fact; used by s5:lemChild. Design note `formal/work/p2b/P4B.md`.

Proof (P3), as in Definition s5:defStages: `X_Y` is a spanning `(2^{-6}, s_r/2)`-expander on `Y`
(s2:propStructure (i), `EG.Todo.StructureExp`; `V(Y) = Z^0 \ S_Y` for a light part);
`L_Y ≤ Λ_r ≤ 2λ_r` (s2:lemTower (b), `EG.towerBRound`) and `λ_r^{100} ≤ s_r` give
`2vm_Y ≤ 2(L_Y^6 + 1) ≤ 2^7λ_r^6 + 2 ≤ s_r/2` (with `λ_r ≥ 4`, s2:lemTower (d),
`EG.Todo.TowerD`); `|Y| ≥ P_r/2 ≥ 2` (s2:propStructure (iv), `EG.structureVertex`), so Lemma
s3:lemHB (`EG.Todo.HB`) with `ε' = 2^{-6}`, `m = vm_Y` gives a family with
`b = ⌈2 vm_Y L_Y^2 / 2^{-6}⌉ = vb_Y`; `A_Y` is the `Classical.epsilon` choice of such a family.
-/

public section

namespace EG

open EG.HB EG.Light Real

/-- Proved in P3. [s5:defStages] (embedded claims) "`H_Y = X_Y` is a `(2^{-6},s_r/2)`-expander on `Y` … `2vm_Y ≤ … ≤ s_r/2` … Lemma s3:lemHB … provides sets `A_Y(w)`". -/
theorem stagesHB : EG.Spec.StagesHBStatement := by
  intro V _ G N0 Dstar run hR Y hY
  have hD : Gamma1core Dstar := hR.1.1
  have hv : run.Valid G Dstar := hR.2.2.2.2.2
  have hd1 : Dstar ≤ run.d G 1 := hR.2.2.2.2.1
  have hYl := (Run.mem_lightParts run G).1 hY
  have hr : Y.1 ∈ Finset.Icc 1 run.R :=
    Finset.mem_Icc.2 (Run.isRound_of_mem_prePartAddrs hYl.1)
  have hSE := EG.Todo.StructureExp V G Dstar run hD.gamma2a hv
  have hX := hSE.2.1 Y.1 hr Y.2 hYl.1 hYl.2
  have hS := (hSE.2.2.2 Y.1 hr).2
  have hSV := (EG.structureVertex V G Dstar run hv Y.1 hr).2.1 Y.2 hYl.1 hYl.2
  have hTB := EG.towerBRound V G Dstar run hD hv hd1 Y.1 hr
  have hanc : Y ∈ run.ancestors G := (Run.mem_ancestors run G).2 hYl.1
  have hLY := (hTB.2.2.2.2.2.2 Y hanc rfl)
  have hTD := (EG.Todo.TowerD V G Dstar run hD hv hd1 Y.1 Y.1 (Finset.mem_Icc.1 hr).1 le_rfl
    (Finset.mem_Icc.1 hr).2).1
  set lam := run.lam G Y.1 with hlam
  have hlam4 : (4 : ℝ) ≤ lam := by
    have : (4 : ℝ) ≤ 2 ^ (2 * logStar (run.d G Y.1) + 2) := by
      rw [pow_add]
      have : (1 : ℝ) ≤ 2 ^ (2 * logStar (run.d G Y.1)) := one_le_pow₀ (by norm_num)
      nlinarith
    linarith
  -- (1) the vertex set
  have hverts : (run.X G Y.1 Y.2).verts = run.ancVerts G Y := by
    rw [hX.1]
    unfold Run.ancVerts Run.partVerts Round.partVerts
    rw [if_pos (show Round.isLight (run.graph G Y.1) (run.choice Y.1) Y.2 from hYl.2)]
    rfl
  -- size of `Y`
  set N := (run.ancVerts G Y).card with hN
  have hPge : lam ^ 103 ≤ (run.P G Y.1 : ℝ) := by
    change lam ^ 103 ≤ ((⌈lamOf (run.d G Y.1) ^ Cp⌉₊ : ℕ) : ℝ)
    exact Nat.le_ceil _
  have hNge : (run.P G Y.1 : ℝ) / 2 ≤ (N : ℝ) := by
    have := hSV.1; have := hSV.2
    change (run.P G Y.1 : ℝ) / 2 ≤ ((run.partVerts G Y.1 Y.2).card : ℝ)
    linarith
  have h4pow : (4 : ℝ) ≤ lam ^ 103 := by
    calc (4 : ℝ) ≤ lam := hlam4
      _ = lam ^ 1 := (pow_one _).symm
      _ ≤ lam ^ 103 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hN2 : (2 : ℝ) ≤ N := by linarith
  set L := run.LY G Y with hL
  have hLdef : L = Real.logb 2 (N : ℝ) := rfl
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hN2
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have hL2 : L ≤ 2 * lam := le_trans hLY.1 hLY.2
  -- `vm` and `vb`
  have hvm : vm G run Y = ⌈L ^ 6⌉₊ := rfl
  have hvb : vb G run Y = ⌈(2 : ℝ) ^ 7 * L ^ 2 * (vm G run Y : ℝ)⌉₊ := rfl
  have hvm_le : (vm G run Y : ℝ) ≤ L ^ 6 + 1 := by
    rw [hvm]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hL6 : L ^ 6 ≤ 64 * lam ^ 6 := by
    have := pow_le_pow_left₀ (by linarith) hL2 6
    nlinarith
  have hvm2 : 2 * (vm G run Y : ℝ) ≤ (run.s G Y.1 : ℝ) / 2 := by
    have hs := hS
    have hl6 : (1 : ℝ) ≤ lam ^ 6 := one_le_pow₀ (by linarith)
    have h94 : (4 : ℝ) ^ 94 ≤ lam ^ 94 := pow_le_pow_left₀ (by norm_num) hlam4 94
    have e : lam ^ 100 = lam ^ 94 * lam ^ 6 := by ring
    have : (4 : ℝ) ^ 94 * lam ^ 6 ≤ lam ^ 100 := by
      rw [e]; exact mul_le_mul_of_nonneg_right h94 (by positivity)
    nlinarith
  refine ⟨hverts, hX.2, hvm2, ?_⟩
  -- the Lemma-HB family
  have hcard : (run.X G Y.1 Y.2).card = N := by
    unfold FGraph.card; rw [hverts]
  have hm1 : 1 ≤ vm G run Y := by
    rw [hvm]; exact Nat.one_le_ceil_iff.2 (by positivity)
  obtain ⟨A, hA⟩ := EG.Todo.HB V (run.X G Y.1 Y.2) (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / 2)
    (vm G run Y) hX.2 (by rw [hcard]; exact_mod_cast hN2) (by
      rw [zpow_neg, zpow_neg]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
    (by rw [zpow_neg]; exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by norm_num)))
    hm1 hvm2
  have hb : ⌈2 * (vm G run Y : ℝ) * Real.logb 2 ((run.X G Y.1 Y.2).card : ℝ) ^ 2 /
      (2 : ℝ) ^ (-6 : ℤ)⌉₊ = vb G run Y := by
    rw [hvb, hcard, ← hLdef]
    congr 1
    rw [zpow_neg]
    norm_num
    ring
  rw [hb] at hA
  exact Classical.epsilon_spec
    (p := fun A => IsHBFamily (run.X G Y.1 Y.2) (vm G run Y) (vb G run Y) A) ⟨A, hA⟩

end EG
