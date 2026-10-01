module

public import EG.Lib.Stage1.Pool
public import EG.Lib.Stage1.Law

/-!
# The pool-label law as a law of the stage-1 outcome (manuscript s7:defPool)

Helper lemmas for `EG.Spec.PoolLawStatement` (`EG/Proof/Todo/PoolLaw.lean`):
* `sum_piPool_zpow`: `Σ_{r=1}^{l-2} π_{l,r} = 1 − 2^{-(l-2)}` in the `zpow` form of the Spec;
* `poolMass_eq`: `Σ_{l,r} q_l π_{l,r} = Σ_l q_l (1 − 2^{-(l-2)})`, hence `poolMass_le_sum_qPool`;
* `qPool_le_inv`: `q_l = M_l^{-2} ≤ M_l^{-1}`;
* `prob_plabOf_mem`: under the stage-1 law, `plab(v)` has law `poolLabelLaw` for `v ∈ V(G)`;
* `prob_mem_poolL`: `P(v ∈ Pool_l) = q_l (1 − 2^{-(l-2)})` for `3 ≤ l ≤ R`.
-/

public section

namespace EG.Stage1

open EG.HB EG.FinDist Finset

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

theorem half_pow_eq_two_zpow (l : ℕ) (hl : 2 ≤ l) :
    (1 / 2 : ℝ) ^ (l - 2) = (2 : ℝ) ^ (-((l : ℤ) - 2)) := by
  rw [show (-((l : ℤ) - 2)) = -((l - 2 : ℕ) : ℤ) by push_cast [Nat.cast_sub hl]; ring,
    zpow_neg, zpow_natCast, one_div, inv_pow]

/-- [s7:defPool] "for each `l` we have `Σ_{r=1}^{l-2} π_{l,r} = 1 − 2^{-(l-2)}`" (`zpow` form). -/
theorem sum_piPool_zpow (l : ℕ) (hl : 3 ≤ l) :
    ∑ r ∈ (Finset.Icc 1 l).filter (fun r => r + 2 ≤ l), piPool l r =
      1 - (2 : ℝ) ^ (-((l : ℤ) - 2)) := by
  rw [sum_piPool l hl, half_pow_eq_two_zpow l (by omega)]

theorem two_zpow_pos (l : ℕ) : 0 < (2 : ℝ) ^ (-((l : ℤ) - 2)) := zpow_pos (by norm_num) _

/-- `q_l = M_l^{-2} ≤ M_l^{-1}` (as `M_l ≥ 1`). -/
theorem qPool_le_inv (l : ℕ) : qPool G run l ≤ ((run.M G l : ℝ))⁻¹ := by
  have hM : (1 : ℝ) ≤ run.M G l := by
    have := two_pow_le_M G run l
    exact_mod_cast le_trans (Nat.one_le_two_pow) this
  unfold qPool
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  have h0 : (0 : ℝ) < run.M G l := by linarith
  rw [inv_le_inv₀ (by positivity) h0]
  nlinarith

/-- `Σ_{(l,r)} q_l π_{l,r} = Σ_{l=3}^{R} q_l (1 − 2^{-(l-2)})`. -/
theorem poolMass_eq :
    poolMass G run =
      ∑ l ∈ Finset.Icc 3 run.R, qPool G run l * (1 - (2 : ℝ) ^ (-((l : ℤ) - 2))) := by
  unfold poolMass
  rw [Finset.sum_finset_product (poolIdx run) (Finset.Icc 3 run.R)
    (fun l => (Finset.Icc 1 l).filter (fun r => r + 2 ≤ l))]
  · refine Finset.sum_congr rfl fun l hl => ?_
    simp only
    rw [← Finset.mul_sum, sum_piPool_zpow l (Finset.mem_Icc.1 hl).1]
  · rintro ⟨l, r⟩
    rw [mem_poolIdx]
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega

theorem poolMass_le_sum_qPool :
    poolMass G run ≤ ∑ l ∈ Finset.Icc 3 run.R, qPool G run l := by
  rw [poolMass_eq]
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 := two_zpow_pos l
  have h2 := qPool_nonneg G run l
  nlinarith

/-- `Σ_{l=3}^{R} M_l^{-1} ≤ Σ_{l=1}^{R} 1/M_l`. -/
theorem sum_inv_M_le :
    ∑ l ∈ Finset.Icc 3 run.R, ((run.M G l : ℝ))⁻¹ ≤
      ∑ l ∈ Finset.Icc 1 run.R, (1 : ℝ) / (run.M G l : ℝ) := by
  simp only [one_div]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    (fun _ _ _ => by positivity)

/-- [s7:defPool] "This is a probability distribution": `Σ_{l,r} q_l π_{l,r} ≤ Σ_l q_l ≤
Σ_l M_l^{-1} ≤ 2/D_* < 1`, given `Σ_{l≤R} 1/M_l ≤ 2/D_*` (Lemma s2:lemTower(b)) and `D_* > 2`. -/
theorem poolMass_lt_one {Dstar : ℝ} (hD : 2 < Dstar)
    (hM : ∑ l ∈ Finset.Icc 1 run.R, (1 : ℝ) / (run.M G l : ℝ) ≤ 2 / Dstar) :
    poolMass G run < 1 := by
  have hq : ∑ l ∈ Finset.Icc 3 run.R, qPool G run l ≤
      ∑ l ∈ Finset.Icc 3 run.R, ((run.M G l : ℝ))⁻¹ :=
    Finset.sum_le_sum fun l _ => qPool_le_inv G run l
  have h21 : 2 / Dstar < 1 := by
    rw [div_lt_one (by linarith)]
    exact hD
  exact lt_of_le_of_lt (poolMass_le_sum_qPool G run)
    (lt_of_le_of_lt (hq.trans ((sum_inv_M_le G run).trans hM)) h21)

/-- The pool label of a vertex `v ∈ V(G)` under the stage-1 law has the law `poolLabelLaw`. -/
theorem prob_plabOf_mem {v : V} (hv : v ∈ G.verts) (A : Set (Option (ℕ × ℕ))) :
    (law G run).prob {ω | plabOf ω.pool v ∈ A} = (poolLabelLaw G run).prob A := by
  have h : {ω : Outcome G run | plabOf ω.pool v ∈ A} =
      Outcome.pool ⁻¹' {π : ↥G.verts → Option (ℕ × ℕ) | π ⟨v, hv⟩ ∈ A} := by
    ext ω
    simp [plabOf, hv]
  rw [h, ← prob_map, map_pool, poolLaw, prob_pi_eval]

theorem prob_plabOf_eq {v : V} (hv : v ∈ G.verts) (o : Option (ℕ × ℕ)) :
    (law G run).prob {ω | plabOf ω.pool v = o} = (poolLabelLaw G run).prob {o} := by
  rw [← prob_plabOf_mem G run hv {o}]
  rfl

/-- [s7:defPool] "`P(v ∈ Pool_l) = q_l(1 − 2^{-(l-2)})`" (for `3 ≤ l ≤ R`, `v ∈ V(G)`, under the
guard `Σ q_l π_{l,r} ≤ 1`). -/
theorem prob_mem_poolL (hm : poolMass G run ≤ 1) {v : V} (hv : v ∈ G.verts) {l : ℕ}
    (hl3 : 3 ≤ l) (hlR : l ≤ run.R) :
    (law G run).prob {ω | v ∈ poolL G ω.pool l} =
      qPool G run l * (1 - (2 : ℝ) ^ (-((l : ℤ) - 2))) := by
  set S := (Finset.Icc 1 l).filter (fun r => r + 2 ≤ l) with hS
  have hset : {ω : Outcome G run | v ∈ poolL G ω.pool l} =
      {ω | plabOf ω.pool v ∈ ((S.image fun r => some (l, r) : Finset (Option (ℕ × ℕ))) :
        Set (Option (ℕ × ℕ)))} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_poolL, Finset.coe_image, Set.mem_image, Finset.mem_coe, hS,
      Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨-, r, h1, h2, h3⟩
      exact ⟨r, ⟨⟨h1, by omega⟩, h2⟩, h3.symm⟩
    · rintro ⟨r, ⟨⟨h1, -⟩, h2⟩, h3⟩
      exact ⟨hv, r, h1, h2, h3.symm⟩
  rw [hset, prob_plabOf_mem G run hv, prob_coe_finset,
    Finset.sum_image (fun r _ r' _ h => by simpa using h)]
  have hw : ∀ r ∈ S, (poolLabelLaw G run).w (some (l, r)) = qPool G run l * piPool l r := by
    intro r hr
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hr
    rw [poolLabelLaw_w_of_le G run hm]
    have hp : (l, r) ∈ poolIdx run := (mem_poolIdx run).2 ⟨hl3, hlR, hr.1.1, hr.2⟩
    simp [plabWeight, hp]
  rw [Finset.sum_congr rfl hw, ← Finset.mul_sum, hS, sum_piPool_zpow l hl3]

end EG.Stage1
