module

public import EG.Spec.Quot.Vstar
public import EG.Proof.HB.TowerBM
public import EG.Proof.Todo.OVRun
public import EG.Proof.Todo.TowerBRest
public import EG.Lib.Stage1.PoolExpect
public import EG.Lib.Quot.Constants
public import EG.Lib.Found.Gamma

/-!
# P3 stub: `EG.Spec.VstarStatement` (s7:lemVstar)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.Vstar`; consumers import this module.

Proof (manuscript s7:lemVstar): "`t^CC_l + 1 ≤ 2log₂M_l + 2` and `E|Pool_l| ≤ q_l n = n/M_l^2`",
so the first summand has expectation at most `(6log₂M_l + 6)n/M_l`;
"`E Σ_{w∈Pool_l} mult_{r(w)}(w) = q_l Σ_r π_{l,r} Σ_w mult_r(w) ≤ q_l·1.37n`" by
Proposition s2:propOV (F11) (`EG.Todo.OVRun`) and `Σ_r π_{l,r} < 1` (Definition s7:defPool; the label law
is a probability law since `Σ_{l,r} q_l π_{l,r} < 1`, `EG.Stage1.poolMass_lt_one` with
`EG.towerBM`); summing with `Σ_l ψ(M_l) ≤ 2.1ψ(D_*)` (Lemma s2:lemTower(b),
`EG.Todo.TowerBRest`). Helpers: `EG/Lib/Stage1/PoolExpect.lean`.
-/

public section

namespace EG.Todo

open EG.HB EG.Quot EG.Stage1 EG.FinDist

/-- The per-round bound `E X_{V,l} ≤ (6 log₂M_l + 12) n/M_l`, i.e. `ψ(M_l) n`. -/
theorem vstar_round {V : Type*} [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (hR : RunHyp N0 Dstar G run) (l : ℕ) (hl3 : 3 ≤ l) (hlR : l ≤ run.R) :
    (Stage1.law G run).expect (fun ω => (XVl run G ω.pool l : ℝ)) ≤
      (6 * Real.logb 2 (run.M G l : ℝ) + 12) * (G.card : ℝ) / (run.M G l : ℝ) := by
  obtain ⟨hΓ1, -, -, -, hd1, hrun⟩ := hR
  have hm : poolMass G run ≤ 1 :=
    (poolMass_lt_one G run hΓ1.1.two_lt (EG.towerBM V G Dstar run hΓ1.1 hrun hd1).2).le
  set m : ℝ := (run.M G l : ℝ) with hmdef
  have hM1 : 1 ≤ run.M G l := le_trans Nat.one_le_two_pow (two_pow_le_M G run l)
  have hm1 : (1 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hM1
  have hm0 : 0 < m := by linarith
  have hq : qPool G run l = 1 / m ^ 2 := by
    unfold qPool
    rw [← hmdef, show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, one_div]
  set z : ℝ := (2 : ℝ) ^ (-((l : ℤ) - 2)) with hz
  have hz0 : 0 < z := two_zpow_pos l
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  set t : ℝ := (tCC (run.M G l) : ℝ) with ht
  have ht1 : t + 1 ≤ 2 * Real.logb 2 m + 2 := by
    have := tCC_le (run.M G l) hM1; rw [ht]; linarith
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  -- the decomposition of `X_{V,l}`
  have hX : (fun ω : Outcome G run => (XVl run G ω.pool l : ℝ)) = fun ω =>
      3 * m * (t + 1) * ((poolL G ω.pool l).card : ℝ) +
        4 * m * ∑ w ∈ poolL G ω.pool l, (run.mult G (poolRound ω.pool w) w : ℝ) := by
    funext ω
    unfold XVl
    push_cast
    rfl
  rw [hX, expect_add, expect_const_mul, expect_const_mul,
    expect_card_poolL G run hm hl3 hlR,
    expect_sum_poolL G run hm hl3 hlR (fun r w => (run.mult G r w : ℝ))]
  -- `Σ_w mult_r(w) ≤ 1.37 n` for every `r`
  have hOV : ∀ r ∈ poolRounds l, ∑ w ∈ G.verts, (run.mult G r w : ℝ) ≤ 1.37 * (G.card : ℝ) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    have h := Todo.OVRun V G Dstar run hΓ1.1.gamma2a hrun r
      (Finset.mem_Icc.2 ⟨hr.1.1, by omega⟩)
    have e := h.2.2.2.2.2.2.2.2.1
    have b := h.2.2.2.2.2.2.2.2.2.1
    rw [← e] at b
    exact_mod_cast b
  have hS : ∑ r ∈ poolRounds l, qPool G run l * piPool l r *
      ∑ w ∈ G.verts, (run.mult G r w : ℝ) ≤ qPool G run l * (1.37 * (G.card : ℝ)) := by
    calc ∑ r ∈ poolRounds l, qPool G run l * piPool l r * ∑ w ∈ G.verts, (run.mult G r w : ℝ)
        ≤ ∑ r ∈ poolRounds l, qPool G run l * piPool l r * (1.37 * (G.card : ℝ)) :=
          Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (hOV r hr)
            (mul_nonneg (qPool_nonneg G run l) (piPool_pos l r).le)
      _ = qPool G run l * (1.37 * (G.card : ℝ)) * ∑ r ∈ poolRounds l, piPool l r := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ = qPool G run l * (1.37 * (G.card : ℝ)) * (1 - z) := by
          rw [sum_piPool_zpow l hl3]
      _ ≤ qPool G run l * (1.37 * (G.card : ℝ)) :=
          mul_le_of_le_one_right (mul_nonneg (qPool_nonneg G run l) (by positivity))
            (by linarith)
  have hP : (G.card : ℝ) * (qPool G run l * (1 - z)) ≤ (G.card : ℝ) * qPool G run l :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (qPool_nonneg G run l) (by linarith)) hn
  rw [hq] at hS hP ⊢
  have hc0 : 0 ≤ 3 * m * (t + 1) := by positivity
  calc 3 * m * (t + 1) * ((G.card : ℝ) * (1 / m ^ 2 * (1 - z))) +
        4 * m * ∑ r ∈ poolRounds l, 1 / m ^ 2 * piPool l r * ∑ w ∈ G.verts, (run.mult G r w : ℝ)
      ≤ 3 * m * (t + 1) * ((G.card : ℝ) * (1 / m ^ 2)) +
        4 * m * (1 / m ^ 2 * (1.37 * (G.card : ℝ))) := by
        gcongr
    _ = (3 * (t + 1) + 5.48) * (G.card : ℝ) / m := by
        field_simp
        ring
    _ ≤ (6 * Real.logb 2 m + 12) * (G.card : ℝ) / m := by
        apply div_le_div_of_nonneg_right _ hm0.le
        apply mul_le_mul_of_nonneg_right _ hn
        linarith

/-- Proved in P3. [s7:lemVstar] see `EG.Spec.VstarStatement`. -/
theorem Vstar : EG.Spec.VstarStatement := by
  intro V _ G N0 Dstar run hR
  refine ⟨fun l hl3 hlR => vstar_round G N0 Dstar run hR l hl3 hlR, ?_⟩
  have hΓ1 := hR.1
  have hd1 := hR.2.2.2.2.1
  have hrun := hR.2.2.2.2.2
  have hn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hX : (fun ω : Outcome G run => (XVOf run G ω : ℝ)) =
      fun ω => ∑ l ∈ Finset.Icc 3 run.R, (XVl run G ω.pool l : ℝ) := by
    funext ω
    change ((XV run G ω.pool : ℕ) : ℝ) = _
    unfold XV
    push_cast
    rfl
  rw [hX, expect_sum]
  have hψ : ∀ l ∈ Finset.Icc 1 run.R, 0 ≤ psiPool (run.M G l : ℝ) := by
    intro l _
    have h1 : 1 ≤ run.M G l := le_trans Nat.one_le_two_pow (two_pow_le_M G run l)
    have hM : (1 : ℝ) ≤ (run.M G l : ℝ) := by exact_mod_cast h1
    have := Real.logb_nonneg (b := 2) (by norm_num) hM
    unfold psiPool
    have : 0 ≤ 6 * Real.logb 2 (run.M G l : ℝ) + 12 := by linarith
    positivity
  calc ∑ l ∈ Finset.Icc 3 run.R, (Stage1.law G run).expect (fun ω => (XVl run G ω.pool l : ℝ))
      ≤ ∑ l ∈ Finset.Icc 3 run.R, psiPool (run.M G l : ℝ) * (G.card : ℝ) := by
        refine Finset.sum_le_sum fun l hl => ?_
        obtain ⟨hl3, hlR⟩ := Finset.mem_Icc.1 hl
        have := vstar_round G N0 Dstar run hR l hl3 hlR
        unfold psiPool
        rw [div_mul_eq_mul_div]
        exact this
    _ = (G.card : ℝ) * ∑ l ∈ Finset.Icc 3 run.R, psiPool (run.M G l : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ (G.card : ℝ) * ∑ l ∈ Finset.Icc 1 run.R, psiPool (run.M G l : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hn
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc (by norm_num : 1 ≤ 3) le_rfl) (fun l hl _ => hψ l hl)
    _ ≤ (G.card : ℝ) * (2.1 * psiPool Dstar) := by
        gcongr
        exact (Todo.TowerBRest V G Dstar run hΓ1.1 hrun hd1).2.2.2
    _ = 2.1 * ((6 * Real.logb 2 Dstar + 12) * (G.card : ℝ) / Dstar) := by
        unfold psiPool; ring

end EG.Todo
