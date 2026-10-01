module

public import EG.Spec.Quot.EXprime
public import EG.Proof.Todo.Lost
public import EG.Proof.Todo.Vstar
public import EG.Proof.Todo.CandCount
public import EG.Proof.HB.CapPrePart
public import EG.Proof.HB.TowerBM
public import EG.Lib.Quot.Xpool
public import EG.Lib.Quot.CandCount
public import EG.Lib.Stage1.PoolExpect
public import EG.Lib.Chain.StageInst
public import EG.Lib.Lend.Standing

/-!
# P3 stub: `EG.Spec.EXprimeStatement` (s7:lemEXprime)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.EXprime`; consumers import this module.

Proof (manuscript s7:lemEXprime): "The bound on `E X_U` is Lemma s6:lemLost (`EG.Todo.Lost`), and
the bound on `E X_V` is Lemma s7:lemVstar (`EG.Todo.Vstar`)." For `X_pool`, at each round `l`:
*pooled weights*: `E Σ_{v∈Pool_l} ω_l(v) ≤ q_l Σ_v ω_l(v) ≤ q_l(Σ_h c^agg_{h,l} + nM_l)`, with
`Σ_h c^agg_{h,l} ≤ (M_l − 1)n` (Lemma s2:lemCap(ii), `EG.capPrePart`, and the disjointness of the
classed-port sets; `EG/Lib/Quot/Xpool.lean`), so at most `2n/M_l`; *JV-bad ports*: at most `n`
classed ports, each JV-bad with probability `≤ exp(−Hcd_l/4) ≤ M_l^{-3}` (Lemma s7:lemCand (iii),
`EG.Todo.candCount_univ`; `Hcd_l ≥ 2^{10}M_l^{10}`), so the expected JV-bad weight is at most
`n/M_l^2 ≤ 0.4n/M_l`. Hence `E X_pool ≤ Σ_l 2.4n/M_l ≤ 4.8n/D_*` (Lemma s2:lemTower(b),
`EG.towerBM`). Adding the three bounds gives `E X' ≤ ε_X(D_*) n`.
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot EG.Stage1 EG.FinDist

universe u

/-- The round-`l` summand of `X_pool` has expectation at most `2.4 n/M_l`. -/
theorem xpool_round {V : Type u} [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V) (hR : RunHyp N0 Dstar G run) (hδ : IsDesignation run G δ) (l : ℕ)
    (hl3 : 3 ≤ l) (hlR : l ≤ run.R) :
    (Stage1.law G run).expect (fun ω =>
        (∑ v ∈ Stage1.poolL G ω.pool l, (poolWeight run G δ l v : ℝ)) +
          ((run.M G l - 1 : ℕ) : ℝ) * ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) ≤
      2.4 * (G.card : ℝ) / (run.M G l : ℝ) := by
  classical
  have hΓ1 := hR.1
  have hd1 := hR.2.2.2.2.1
  have hrun := hR.2.2.2.2.2
  have hBM := EG.towerBM V G Dstar run hΓ1.1 hrun hd1
  have hm : poolMass G run ≤ 1 := (poolMass_lt_one G run hΓ1.1.two_lt hBM.2).le
  have hM40 : (2 : ℝ) ^ 40 ≤ (run.M G l : ℝ) := by exact_mod_cast two_pow_le_M G run l
  have hM1 : (1 : ℝ) ≤ (run.M G l : ℝ) := le_trans (by norm_num) hM40
  have hM0 : 0 < (run.M G l : ℝ) := by linarith
  have hn : 0 ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hq : qPool G run l = 1 / (run.M G l : ℝ) ^ 2 := by
    unfold qPool
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, one_div]
  rw [expect_add, expect_const_mul]
  -- pooled weights
  have hW : ∑ v ∈ G.verts, (poolWeight run G δ l v : ℝ) ≤ 2 * (run.M G l : ℝ) * (G.card : ℝ) := by
    have hCap : ∀ a ∈ run.Std G l, ∀ v, degE (run.E G l a) v ≤ run.M G l - 1 := fun a ha v =>
      ((EG.capPrePart V G Dstar run hΓ1.1.gamma2a hrun l (Finset.mem_Icc.2 ⟨by omega, hlR⟩)).2 a
        (Std_subset_prePartAddrs run G l ha)).2 v
    have h := sum_poolWeight_le run G δ l hCap
    have h' : ((∑ v ∈ G.verts, poolWeight run G δ l v : ℕ) : ℝ) ≤
        (((run.M G l - 1) * G.card + run.M G l * G.card : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have hsub : ((run.M G l - 1 : ℕ) : ℝ) ≤ (run.M G l : ℝ) := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  have hA : (Stage1.law G run).expect (fun ω =>
      ∑ v ∈ Stage1.poolL G ω.pool l, (poolWeight run G δ l v : ℝ)) ≤ 2 * (G.card : ℝ) / (run.M G l : ℝ) := by
    have h := expect_sum_poolL G run hm hl3 hlR (fun _ w => (poolWeight run G δ l w : ℝ))
    rw [h]
    have e : ∑ r ∈ poolRounds l, qPool G run l * piPool l r *
        ∑ w ∈ G.verts, (poolWeight run G δ l w : ℝ) =
        qPool G run l * (∑ w ∈ G.verts, (poolWeight run G δ l w : ℝ)) *
          ∑ r ∈ poolRounds l, piPool l r := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
    rw [e, sum_piPool_zpow l hl3, hq]
    have hz := two_zpow_pos l
    have hW0 : 0 ≤ ∑ w ∈ G.verts, (poolWeight run G δ l w : ℝ) := by positivity
    calc 1 / (run.M G l : ℝ) ^ 2 * (∑ w ∈ G.verts, (poolWeight run G δ l w : ℝ)) *
          (1 - (2 : ℝ) ^ (-((l : ℤ) - 2)))
        ≤ 1 / (run.M G l : ℝ) ^ 2 * (∑ w ∈ G.verts, (poolWeight run G δ l w : ℝ)) :=
          mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ 1 / (run.M G l : ℝ) ^ 2 * (2 * (run.M G l : ℝ) * (G.card : ℝ)) := by gcongr
      _ = 2 * (G.card : ℝ) / (run.M G l : ℝ) := by field_simp
  -- JV-bad ports
  have hHcd : (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 ≤ Hcd run G l := by
    have hML := hBM.1 l hl3 hlR
    have hlam := Standing.lam_ge hΓ1 hrun (l := l - 2) ⟨by omega, by omega⟩
    exact Hcd_ge_arith hM1 (hML.1.trans hML.2) (le_trans (by norm_num) hlam)
  have hexp : Real.exp (-(Hcd run G l) / 4) ≤ 1 / (run.M G l : ℝ) ^ 3 := by
    have hx : 0 < Hcd run G l / 4 := by
      have : 0 < (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 := by positivity
      linarith
    have h1 : Real.exp (-(Hcd run G l) / 4) = (Real.exp (Hcd run G l / 4))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    have h2 : Hcd run G l / 4 + 1 ≤ Real.exp (Hcd run G l / 4) := Real.add_one_le_exp _
    have h3 : (run.M G l : ℝ) ^ 3 ≤ Hcd run G l / 4 := by
      have : (run.M G l : ℝ) ^ 3 ≤ (2 : ℝ) ^ 8 * (run.M G l : ℝ) ^ 10 := by
        have : (run.M G l : ℝ) ^ 3 ≤ (run.M G l : ℝ) ^ 10 := pow_le_pow_right₀ hM1 (by norm_num)
        nlinarith [pow_pos hM0 10]
      linarith
    rw [h1, one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  have hB : (Stage1.law G run).expect (fun ω =>
      ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) ≤ (G.card : ℝ) / (run.M G l : ℝ) ^ 3 := by
    have e : (fun ω : Outcome G run => ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) =
        fun ω => ∑ u ∈ classedPorts run G l,
          (if JVBad run G δ (stageOf ω) ω.pool l u then (1 : ℝ) else 0) := by
      funext ω
      unfold jvBadPorts
      rw [Finset.sum_boole]
    rw [e, expect_sum]
    have hu : ∀ u ∈ classedPorts run G l, (Stage1.law G run).expect (fun ω =>
        (if JVBad run G δ (stageOf ω) ω.pool l u then (1 : ℝ) else 0)) ≤ 1 / (run.M G l : ℝ) ^ 3 := by
      intro u hu
      rw [FinDist.expect_ite]
      have h := (candCount_univ V N0 Dstar G run δ hR hδ stageOf (fun _ _ _ => rfl) l u hl3
        hu).2.2.2.2.2.2.1
      exact h.trans hexp
    calc ∑ u ∈ classedPorts run G l, (Stage1.law G run).expect (fun ω =>
          (if JVBad run G δ (stageOf ω) ω.pool l u then (1 : ℝ) else 0))
        ≤ ∑ u ∈ classedPorts run G l, 1 / (run.M G l : ℝ) ^ 3 := Finset.sum_le_sum hu
      _ = ((classedPorts run G l).card : ℝ) * (1 / (run.M G l : ℝ) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (G.card : ℝ) * (1 / (run.M G l : ℝ) ^ 3) := by
          gcongr
          exact_mod_cast Finset.card_le_card (classedPorts_subset_verts run G l)
      _ = (G.card : ℝ) / (run.M G l : ℝ) ^ 3 := by ring
  have hsub : ((run.M G l - 1 : ℕ) : ℝ) ≤ (run.M G l : ℝ) := by exact_mod_cast Nat.sub_le _ _
  have hB0 : 0 ≤ (Stage1.law G run).expect (fun ω =>
      ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) :=
    expect_nonneg _ fun _ => Nat.cast_nonneg _
  have hC : ((run.M G l - 1 : ℕ) : ℝ) * (Stage1.law G run).expect (fun ω =>
      ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) ≤ 0.4 * (G.card : ℝ) / (run.M G l : ℝ) := by
    calc ((run.M G l - 1 : ℕ) : ℝ) * (Stage1.law G run).expect (fun ω =>
          ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ))
        ≤ (run.M G l : ℝ) * ((G.card : ℝ) / (run.M G l : ℝ) ^ 3) := mul_le_mul hsub hB hB0 (by positivity)
      _ = (G.card : ℝ) / (run.M G l : ℝ) / (run.M G l : ℝ) := by field_simp
      _ ≤ 0.4 * (G.card : ℝ) / (run.M G l : ℝ) := by
          apply div_le_div_of_nonneg_right _ hM0.le
          rw [div_le_iff₀ hM0]
          nlinarith
  calc _ ≤ 2 * (G.card : ℝ) / (run.M G l : ℝ) + 0.4 * (G.card : ℝ) / (run.M G l : ℝ) := add_le_add hA hC
    _ = 2.4 * (G.card : ℝ) / (run.M G l : ℝ) := by ring

/-- Proved in P3. [s7:lemEXprime] see `EG.Spec.EXprimeStatement`. -/
theorem EXprime : EG.Spec.EXprimeStatement := by
  intro V _ G N0 Dstar run δ hR hδ
  have hΓ1 := hR.1
  have hd1 := hR.2.2.2.2.1
  have hrun := hR.2.2.2.2.2
  have hD2 : 2 < Dstar := hΓ1.1.two_lt
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  -- `X_U` (Lemma s6:lemLost)
  have hU := Todo.Lost V G N0 Dstar run δ hR hδ
  have hXU : (Stage1.law G run).expect (fun ω => (XUOf run G δ ω : ℝ)) ≤
      Light.epsU Dstar * (G.card : ℝ) + 5.5 * (G.card : ℝ) / Dstar := hU.2.2.1.trans hU.2.2.2
  -- `X_V` (Lemma s7:lemVstar)
  have hXV : (Stage1.law G run).expect (fun ω => (XVOf run G ω : ℝ)) ≤
      2.1 * (6 * Real.logb 2 Dstar + 12) * (G.card : ℝ) / Dstar := by
    have := (Todo.Vstar V G N0 Dstar run hR).2
    have e : 2.1 * ((6 * Real.logb 2 Dstar + 12) * (G.card : ℝ) / Dstar) =
        2.1 * (6 * Real.logb 2 Dstar + 12) * (G.card : ℝ) / Dstar := by ring
    linarith
  -- `X_pool`
  have hXp : (Stage1.law G run).expect (fun ω => (XpoolOf run G δ ω : ℝ)) ≤
      4.8 * (G.card : ℝ) / Dstar := by
    have e : (fun ω : Outcome G run => (XpoolOf run G δ ω : ℝ)) = fun ω =>
        ∑ l ∈ Finset.Icc 3 run.R,
          ((∑ v ∈ Stage1.poolL G ω.pool l, (poolWeight run G δ l v : ℝ)) +
            ((run.M G l - 1 : ℕ) : ℝ) *
              ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ)) := by
      funext ω
      change ((Xpool run G δ (stageOf ω) ω.pool : ℕ) : ℝ) = _
      unfold Xpool
      push_cast
      rfl
    rw [e, expect_sum]
    have hM : ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) ≤ 2 / Dstar :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num : 1 ≤ 3) le_rfl)
        (fun _ _ _ => by positivity)).trans (EG.towerBM V G Dstar run hΓ1.1 hrun hd1).2
    calc ∑ l ∈ Finset.Icc 3 run.R, (Stage1.law G run).expect (fun ω =>
          (∑ v ∈ Stage1.poolL G ω.pool l, (poolWeight run G δ l v : ℝ)) +
            ((run.M G l - 1 : ℕ) : ℝ) * ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ))
        ≤ ∑ l ∈ Finset.Icc 3 run.R, 2.4 * (G.card : ℝ) * ((1 : ℝ) / (run.M G l : ℝ)) := by
          refine Finset.sum_le_sum fun l hl => ?_
          obtain ⟨hl3, hlR⟩ := Finset.mem_Icc.1 hl
          rw [mul_one_div]
          exact xpool_round G N0 Dstar run δ hR hδ l hl3 hlR
      _ = 2.4 * (G.card : ℝ) * ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ 2.4 * (G.card : ℝ) * (2 / Dstar) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 4.8 * (G.card : ℝ) / Dstar := by ring
  -- `X' = X_U + X_pool + X_V`
  have hX : (fun ω : Outcome G run => (XprimeOf run G δ ω : ℝ)) = fun ω =>
      (XUOf run G δ ω : ℝ) + (XpoolOf run G δ ω : ℝ) + (XVOf run G ω : ℝ) := by
    funext ω
    change ((Xprime run G δ (stageOf ω) ω.pool : ℕ) : ℝ) = _
    rw [Xprime_eq]
    push_cast
    rfl
  refine ⟨?_, hXU, hXp, hXV⟩
  rw [hX, expect_add, expect_add]
  have e : epsX Dstar * (G.card : ℝ) = Light.epsU Dstar * (G.card : ℝ) + 5.5 * (G.card : ℝ) / Dstar +
      4.8 * (G.card : ℝ) / Dstar + 2.1 * (6 * Real.logb 2 Dstar + 12) * (G.card : ℝ) / Dstar := by
    unfold epsX; ring
  rw [e]
  linarith

end EG.Todo
