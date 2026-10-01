module

public import EG.Lib.Stage1.PoolLaw

/-!
# Expectations of pool counts under the stage-1 law (manuscript s7:lemVstar, s7:lemEXprime)

* `card_poolL_eq_sum`, `sum_poolL_eq_sum`: `|Pool_l|` and `Σ_{w∈Pool_l} f(r(w), w)` as sums over
  `V(G)` of indicator terms of the pool label;
* `expect_ite`: the expectation of an indicator is the probability of its event;
* `expect_card_poolL`: `E|Pool_l| = |V(G)| q_l (1 − 2^{-(l-2)})`;
* `expect_sum_poolL`: `E Σ_{w ∈ Pool_l} f(r(w), w) = Σ_{r=1}^{l-2} q_l π_{l,r} Σ_{w ∈ V(G)} f(r, w)`
  ("`E Σ_{w∈Pool_l} mult_{r(w)}(w) = Σ_w Σ_{r=1}^{l-2} q_l π_{l,r} mult_r(w)`", s7:lemVstar).
-/

public section

namespace EG.Stage1

open EG.HB EG.FinDist Finset

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-- The round indices `1 ≤ r ≤ l − 2` of `Pool_l`. -/
abbrev poolRounds (l : ℕ) : Finset ℕ := (Finset.Icc 1 l).filter (fun r => r + 2 ≤ l)

theorem card_poolL_eq_sum (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) :
    ((poolL G π l).card : ℝ) = ∑ v ∈ G.verts, (if v ∈ poolL G π l then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2]
  intro v hv
  exact (mem_poolL.1 hv).1

theorem sum_poolL_eq_sum (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (f : ℕ → V → ℝ) :
    ∑ w ∈ poolL G π l, f (poolRound π w) w =
      ∑ w ∈ G.verts, ∑ r ∈ poolRounds l,
        (if plabOf π w = some (l, r) then f r w else 0) := by
  have hsub : poolL G π l ⊆ G.verts := fun v hv => (mem_poolL.1 hv).1
  rw [← Finset.sum_subset hsub (f := fun w => ∑ r ∈ poolRounds l,
      (if plabOf π w = some (l, r) then f r w else 0))]
  · refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨-, r, h1, h2, hr⟩ := mem_poolL.1 hw
    have hround : poolRound π w = r := by simp [poolRound, hr]
    rw [hround, hr]
    have : ∀ r' ∈ poolRounds l, (if some (l, r) = some (l, r') then f r' w else 0) =
        if r' = r then f r' w else 0 := by
      intro r' _
      by_cases h : r' = r
      · simp [h]
      · have : ¬ (some (l, r) = some (l, r')) := by
          simp only [Option.some.injEq, Prod.mk.injEq, true_and]; exact fun e => h e.symm
        simp [this, h]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    rw [if_pos]
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h1, by omega⟩, h2⟩
  · intro w hw hnot
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    intro h
    apply hnot
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr
    exact mem_poolL.2 ⟨hw, r, hr.1.1, hr.2, h⟩

/-- The expectation of the indicator of an event is its probability. -/
theorem _root_.EG.FinDist.expect_ite {Ω : Type*} (μ : FinDist Ω) (P : Ω → Prop)
    [DecidablePred P] : μ.expect (fun ω => if P ω then (1 : ℝ) else 0) = μ.prob {ω | P ω} := by
  rw [prob_eq_expect]
  congr 1
  funext ω
  by_cases h : P ω <;> simp [Set.indicator, h]

variable (G run)

/-- `E|Pool_l| = |V(G)| q_l (1 − 2^{-(l-2)})` (for `3 ≤ l ≤ R`, under `Σ q_l π_{l,r} ≤ 1`). -/
theorem expect_card_poolL (hm : poolMass G run ≤ 1) {l : ℕ} (hl3 : 3 ≤ l) (hlR : l ≤ run.R) :
    (law G run).expect (fun ω => ((poolL G ω.pool l).card : ℝ)) =
      (G.card : ℝ) * (qPool G run l * (1 - (2 : ℝ) ^ (-((l : ℤ) - 2)))) := by
  classical
  simp_rw [card_poolL_eq_sum]
  rw [expect_sum]
  have : ∀ v ∈ G.verts, (law G run).expect
      (fun ω => if v ∈ poolL G ω.pool l then (1 : ℝ) else 0) =
        qPool G run l * (1 - (2 : ℝ) ^ (-((l : ℤ) - 2))) := by
    intro v hv
    rw [FinDist.expect_ite, prob_mem_poolL G run hm hv hl3 hlR]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, FGraph.card]

/-- "`E Σ_{w∈Pool_l} f(r(w), w) = Σ_w Σ_{r=1}^{l-2} q_l π_{l,r} f(r, w)`" (for `3 ≤ l ≤ R`). -/
theorem expect_sum_poolL (hm : poolMass G run ≤ 1) {l : ℕ} (hl3 : 3 ≤ l) (hlR : l ≤ run.R)
    (f : ℕ → V → ℝ) :
    (law G run).expect (fun ω => ∑ w ∈ poolL G ω.pool l, f (poolRound ω.pool w) w) =
      ∑ r ∈ poolRounds l, qPool G run l * piPool l r * ∑ w ∈ G.verts, f r w := by
  classical
  simp_rw [sum_poolL_eq_sum]
  rw [expect_sum]
  have h1 : ∀ w ∈ G.verts, (law G run).expect (fun ω => ∑ r ∈ poolRounds l,
      (if plabOf ω.pool w = some (l, r) then f r w else 0)) =
        ∑ r ∈ poolRounds l, qPool G run l * piPool l r * f r w := by
    intro w hw
    rw [expect_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' := hr
    simp only [Finset.mem_filter, Finset.mem_Icc] at hr'
    have hp : (l, r) ∈ poolIdx run := (mem_poolIdx run).2 ⟨hl3, hlR, hr'.1.1, hr'.2⟩
    have e : (fun ω : Outcome G run => if plabOf ω.pool w = some (l, r) then f r w else 0) =
        fun ω => (if plabOf ω.pool w = some (l, r) then (1 : ℝ) else 0) * f r w := by
      funext ω; split_ifs <;> simp
    rw [e, expect_mul_const, FinDist.expect_ite, prob_plabOf_eq G run hw,
      prob_poolLabelLaw_some G run hm hp]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]

end EG.Stage1
