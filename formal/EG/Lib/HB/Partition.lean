module

public import EG.Lib.HB.Run
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Helpers for Proposition s2:propStructure (iii) (manuscript s2:propStructure)

Run-level facts on the edge flow of a run (unit P3-s2): "By (R1), `E(G_l) = E(Cyc_l) ⊔ E(G'_l)`
… `E(G'_l) = ⨆_{Z light} E_l(Z) ⊔ ⨆_{Z ∈ Std_l} E_l(Z) ⊔ E(G_{l+1})`", and the long-cycle count
("`|Cyc_l| ≤ (n/2)(y_l - y_{l+1})/(y_l log² y_l)`", summed by a telescoping bound in place of the
manuscript's dyadic grouping: `(y - y')/(y log² y) ≤ 1/log y' - 1/log y`).
-/

public section

namespace EG.HB

open Real

variable {V : Type*} [DecidableEq V]

namespace Run

variable (run : Run V) (G : FGraph V)

theorem E_of_isRound {l : ℕ} (hl : run.IsRound l) (a : Addr) :
    run.E G l a = Round.E (run.graph G l) (run.choice l) a := if_pos hl

theorem graph'_edges_subset (l : ℕ) : (run.graph' G l).edges ⊆ (run.graph G l).edges :=
  (Round.graph'_le _ _).2

theorem succ_edges_subset_graph' {l : ℕ} (hl : run.IsRound l) :
    (run.graph G (l + 1)).edges ⊆ (run.graph' G l).edges := by
  rw [graph_succ_of_isRound run G hl]
  exact Round.passed_subset _ _

theorem disjoint_cyc_graph' {l : ℕ} (hl : run.IsRound l) :
    Disjoint (run.cycEdges l) (run.graph' G l).edges := by
  rw [graph'_eq_deleteEdges run G hl]
  simp only [FGraph.deleteEdges_edges]
  exact Finset.disjoint_sdiff

theorem disjoint_E_succ {l : ℕ} (hl : run.IsRound l) (a : Addr) :
    Disjoint (run.E G l a) (run.graph G (l + 1)).edges := by
  rw [graph_succ_of_isRound run G hl, E_of_isRound run G hl]
  exact (Round.disjoint_passed_E _ _ a).symm

theorem edges_subset_succ_of_lt {r l : ℕ} (h : r + 1 ≤ l) :
    (run.graph G l).edges ⊆ (run.graph G (r + 1)).edges :=
  graph_edges_subset_of_le run G h

theorem mem_prePartAddrs_of_mem_E {l : ℕ} {a : Addr} {e : Sym2 V} (he : e ∈ run.E G l a) :
    a ∈ run.prePartAddrs G l := by
  by_cases hl : run.IsRound l
  · rw [E_of_isRound run G hl] at he
    rw [prePartAddrs_of_isRound run G hl]
    exact Round.mem_prePartAddrs_of_mem_E _ _ he
  · simp [hl] at he

end Run

/-- `(y - y')/(y log² y) ≤ 1/log y' - 1/log y` for `2 ≤ y' ≤ y` (`1 - t ≤ -ln t`, `ln 2 < 1`). -/
theorem cyc_step {y y' : ℝ} (hy' : 2 ≤ y') (hyy : y' ≤ y) :
    (y - y') / (y * logb 2 y ^ 2) ≤ 1 / logb 2 y' - 1 / logb 2 y := by
  have hy0 : 0 < y' := by linarith
  have hy : 0 < y := by linarith
  have hl' : 1 ≤ logb 2 y' := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hy0]; simpa using hy'
  have hll : logb 2 y' ≤ logb 2 y := Real.logb_le_logb_of_le (by norm_num) hy0 hyy
  have hl : 0 < logb 2 y := by linarith
  -- `(y - y')/y ≤ ln y - ln y'`
  have h1 : (y - y') / y ≤ Real.log y - Real.log y' := by
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hy)
    rw [Real.log_div hy0.ne' hy.ne'] at this
    rw [sub_div, div_self hy.ne']
    linarith
  have hln2 := Real.log_two_gt_d9
  have hln2' := Real.log_two_lt_d9
  have h2 : Real.log y - Real.log y' ≤ logb 2 y - logb 2 y' := by
    have e1 : Real.log y = logb 2 y * Real.log 2 := by
      rw [Real.logb, div_mul_cancel₀ _ (by positivity)]
    have e2 : Real.log y' = logb 2 y' * Real.log 2 := by
      rw [Real.logb, div_mul_cancel₀ _ (by positivity)]
    rw [e1, e2]
    nlinarith
  have h3 : (y - y') / (y * logb 2 y ^ 2) = ((y - y') / y) / logb 2 y ^ 2 := by
    rw [div_div]
  rw [h3]
  have h4 : ((y - y') / y) / logb 2 y ^ 2 ≤ (logb 2 y - logb 2 y') / logb 2 y ^ 2 :=
    div_le_div_of_nonneg_right (h1.trans h2) (by positivity)
  refine h4.trans ?_
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  have hd : 0 ≤ logb 2 y - logb 2 y' := by linarith
  have : (logb 2 y - logb 2 y') * (logb 2 y' * logb 2 y) ≤
      (logb 2 y - logb 2 y') * (logb 2 y * logb 2 y) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hd
  nlinarith

/-- The long-cycle count of s2:propStructure (iii): if `c_l (y_l log² y_l) ≤ (n/2)(y_l - y_{l+1})`
for `1 ≤ l ≤ R`, with `y_l ≥ 2^{117}` non-increasing on `[1, R]` and `y_{R+1} ≥ 0`, then
`Σ_{l≤R} c_l ≤ n`. -/
theorem cycles_sum_le (c : ℕ → ℕ) (y : ℕ → ℝ) (R : ℕ) (n : ℝ) (hn : 0 ≤ n)
    (hy : ∀ l ∈ Finset.Icc 1 R, (2 : ℝ) ^ 117 ≤ y l)
    (hmono : ∀ l ∈ Finset.Icc 1 R, y (l + 1) ≤ y l) (hlast : 0 ≤ y (R + 1))
    (hc : ∀ l ∈ Finset.Icc 1 R, (c l : ℝ) * (y l * logb 2 (y l) ^ 2) ≤ n / 2 * (y l - y (l + 1))) :
    ((∑ l ∈ Finset.Icc 1 R, c l : ℕ) : ℝ) ≤ n := by
  rcases Nat.eq_zero_or_pos R with hR | hR
  · subst hR; simp [hn]
  have hlam : ∀ l ∈ Finset.Icc 1 R, 117 ≤ logb 2 (y l) := by
    intro l hl
    have hyl := hy l hl
    rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le (by positivity) hyl)]
    calc (2 : ℝ) ^ (117 : ℝ) = (2 : ℝ) ^ (117 : ℕ) := by norm_num
      _ ≤ y l := hyl
  -- per-round bound `c_l ≤ b_l`
  set b : ℕ → ℝ := fun l => n / 2 * ((y l - y (l + 1)) / (y l * logb 2 (y l) ^ 2)) with hb
  have hcb : ∀ l ∈ Finset.Icc 1 R, (c l : ℝ) ≤ b l := by
    intro l hl
    have hpos : 0 < y l * logb 2 (y l) ^ 2 := by
      have := hy l hl; have := hlam l hl; positivity
    simp only [hb]
    rw [← mul_div_assoc, le_div_iff₀ hpos]
    exact hc l hl
  have claim : ∀ k, 1 ≤ k → k ≤ R → ((∑ l ∈ Finset.Icc 1 k, c l : ℕ) : ℝ) ≤
      n / 2 * (1 / logb 2 (y k) - 1 / logb 2 (y 1)) + b k := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      simp only [Finset.Icc_self, Finset.sum_singleton, sub_self, mul_zero, zero_add]
      exact hcb 1 (Finset.mem_Icc.2 ⟨le_rfl, hR⟩)
    | succ k hk ih =>
      intro hkR
      have hkR' : k ∈ Finset.Icc 1 R := Finset.mem_Icc.2 ⟨hk, by omega⟩
      have hk1R : k + 1 ∈ Finset.Icc 1 R := Finset.mem_Icc.2 ⟨by omega, hkR⟩
      have ih' := ih (by omega)
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      have hstep := cyc_step (y := y k) (y' := y (k + 1))
        (le_trans (by norm_num) (hy (k + 1) hk1R)) (hmono k hkR')
      have hbk : b k ≤ n / 2 * (1 / logb 2 (y (k + 1)) - 1 / logb 2 (y k)) :=
        mul_le_mul_of_nonneg_left hstep (by linarith)
      have := hcb (k + 1) hk1R
      push_cast at ih'
      linarith
  have hfin := claim R hR le_rfl
  have hRR : R ∈ Finset.Icc 1 R := Finset.mem_Icc.2 ⟨hR, le_rfl⟩
  have hl117 := hlam R hRR
  have hlam1 := hlam 1 (Finset.mem_Icc.2 ⟨le_rfl, hR⟩)
  have hyR := hy R hRR
  have hyR0 : 0 < y R := lt_of_lt_of_le (by positivity) hyR
  have hbR : b R ≤ n / 2 * (1 / 117) := by
    simp only [hb]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_iff₀ (by positivity)]
    have : 117 ^ 2 ≤ logb 2 (y R) ^ 2 := pow_le_pow_left₀ (by norm_num) hl117 2
    nlinarith
  have h1 : 1 / logb 2 (y R) ≤ 1 / 117 := one_div_le_one_div_of_le (by norm_num) hl117
  have h2 : 0 ≤ 1 / logb 2 (y 1) := by positivity
  have : n / 2 * (1 / logb 2 (y R) - 1 / logb 2 (y 1)) ≤ n / 2 * (1 / 117) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

theorem list_length_mul_le_sum {α : Type*} (L : List (List α)) (T : ℝ)
    (h : ∀ x ∈ L, T ≤ (x.length : ℝ)) :
    (L.length : ℝ) * T ≤ (((L.map List.length).sum : ℕ) : ℝ) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    push_cast at h2 ⊢
    linarith

end EG.HB
