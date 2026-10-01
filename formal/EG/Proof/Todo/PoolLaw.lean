module

public import EG.Spec.Stage1.Pool
public import EG.Lib.Stage1.PoolLaw
public import EG.Lib.Found.Gamma
public import EG.Proof.HB.TowerBM

/-!
# P3 stub: `EG.Spec.PoolLawStatement` (s7:defPool)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.PoolLaw`; consumers import this module.

Proof: the arithmetic of the label law is in `EG/Lib/Stage1/Pool.lean` and
`EG/Lib/Stage1/PoolLaw.lean`; "`Σ_l M_l^{-1} ≤ 2/D_*` by Lemma s2:lemTower(b)" is `EG.towerBM`
(declared input of s2:lemTower (b)); the law and the independence of component (1d) are
`EG.Stage1.map_pool` and `EG.Stage1.indepFun_rest_pool`.
-/

public section

namespace EG.Todo

open EG.HB EG.Stage1

/-- Proved in P3. [s7:defPool] see `EG.Spec.PoolLawStatement`. -/
theorem PoolLaw : EG.Spec.PoolLawStatement := by
  intro V _ N0 Dstar G run hR
  obtain ⟨hΓ1, -, -, -, hd1, hrun⟩ := hR
  have hD2 : 2 < Dstar := hΓ1.1.two_lt
  -- "`Σ_l q_l ≤ Σ_l M_l^{-1} ≤ 2/D_* < 1` by Lemma s2:lemTower(b)"
  have hq : ∑ l ∈ Finset.Icc 3 run.R, qPool G run l ≤
      ∑ l ∈ Finset.Icc 3 run.R, ((run.M G l : ℝ))⁻¹ :=
    Finset.sum_le_sum fun l _ => qPool_le_inv G run l
  have hM : ∑ l ∈ Finset.Icc 3 run.R, ((run.M G l : ℝ))⁻¹ ≤ 2 / Dstar :=
    (sum_inv_M_le G run).trans (EG.towerBM V G Dstar run hΓ1.1 hrun hd1).2
  have h21 : 2 / Dstar < 1 := by
    rw [div_lt_one (by linarith)]
    exact hD2
  -- "This is a probability distribution"
  have hmass : poolMass G run < 1 :=
    lt_of_le_of_lt (poolMass_le_sum_qPool G run) (lt_of_le_of_lt (hq.trans hM) h21)
  refine ⟨fun l hl => ⟨sum_piPool_zpow l hl, by linarith [two_zpow_pos l]⟩,
    ⟨hq, hM, h21⟩, hmass, map_pool G run, ?_, ?_, ?_,
    fun π l l' h => disjoint_poolL π h,
    fun π l w hw => ⟨mem_poolSet_poolRound hw, fun r hr => (poolRound_eq hr).symm⟩,
    indepFun_rest_pool G run⟩
  · intro v hv l r hp
    rw [prob_plabOf_eq G run hv]
    exact prob_poolLabelLaw_some G run hmass.le hp
  · intro v hv
    rw [prob_plabOf_eq G run hv]
    exact prob_poolLabelLaw_none G run hmass.le
  · intro v hv l hl3 hlR
    rw [prob_mem_poolL G run hmass.le hv hl3 hlR]
    refine ⟨rfl, ?_⟩
    have h1 := two_zpow_pos l
    have h2 := qPool_nonneg G run l
    nlinarith

end EG.Todo
