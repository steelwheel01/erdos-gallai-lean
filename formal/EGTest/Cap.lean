import EG.Proof.HB.Cap
import EG.Lib.Found.Graph

/-! Non-vacuity tests for the pilot [cap]: `EG.Spec.CapStatement` ([s2:lemCap] (i)),
`EG.Spec.CapUniformStatement` (the remark), `EG.Spec.CapGraphStatement` (graph-level step of
(ii)) and `EG.Spec.BMLemma25Statement` ([s1:citLem25]).

* the hypotheses of each statement are jointly satisfiable (for the graph statements: the complete
  graph `K_{2^{40}}`, a `(2^{-5},0)`-expander all of whose cycles have length `≤ 2^{40} < 2^{117}`);
* each non-trivial hypothesis is load-bearing (dropping it makes the statement false).

Adapted from the clean-room review of round 1 (`work/p1b/cap.review1.md`, §2). -/

namespace EGTest.Cap

open EG

/-! ## The cycle encoding includes the closing edge -/

example : cycleEdges [1, 2, 3] = [s((1 : ℕ), 2), s(2, 3), s(3, 1)] := by decide

/-! ## `CapStatement` ([s2:lemCap] (i)) -/

theorem logb_two_pow (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- The hypotheses of (i) are satisfiable: `m = 2^{40}`, `T = 2^{117}`. -/
example : ∃ m T : ℝ, 2 ^ 40 ≤ m ∧ 2 ^ 117 ≤ T ∧ m < 18432 * T * Real.logb 2 m ^ 4 := by
  refine ⟨2 ^ 40, 2 ^ 117, le_rfl, le_rfl, ?_⟩
  rw [logb_two_pow]; norm_num

/-- The hypothesis `m < 18432 T log⁴ m` is load-bearing (`m = 2^{200}`, `T = 2^{117}`). -/
example : ¬ ∀ m T : ℝ, 2 ^ 40 ≤ m → 2 ^ 117 ≤ T → m ≤ 2 ^ 16 * T * Real.logb 2 T ^ 4 := by
  intro h
  have := h (2 ^ 200) (2 ^ 117) (by norm_num) le_rfl
  rw [logb_two_pow] at this; norm_num at this

/-- The threshold `T ≥ 2^{117}` is load-bearing: with `T ≥ 2^{20}` part (i) is false (the
remark's example `T = 2^{20}`, `m = 2^{55}`). -/
example : ¬ ∀ m T : ℝ, 2 ^ 40 ≤ m → 2 ^ 20 ≤ T → m < 18432 * T * Real.logb 2 m ^ 4 →
    m ≤ 2 ^ 16 * T * Real.logb 2 T ^ 4 := by
  intro h
  obtain ⟨h1, h2, h3⟩ := cap_remark_counterexample
  have := h _ _ h1 le_rfl h2
  linarith

/-! ## `CapUniformStatement` (the remark's uniform form) -/

/-- Its hypothesis `m < 18432 T log⁴ m` is load-bearing (`m = 2^{200}`, `T = 1`). -/
example : ¬ ∀ m T : ℝ, 1 ≤ T → m ≤ max (2 ^ 40) (2 ^ 16 * T * (Real.logb 2 T + 40) ^ 4) := by
  intro h
  have := h (2 ^ 200) 1 le_rfl
  simp at this
  norm_num at this

/-! ## Complete graphs `K_n` on `Fin n` -/

/-- The complete graph on `Fin n`. -/
def Kn (n : ℕ) : FGraph (Fin n) where
  verts := Finset.univ
  edges := Finset.univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag)
  edge_verts := by intros; simp
  loopless := by intro e he; simpa using he

theorem Kn_card (n : ℕ) : (Kn n).card = n := by simp [FGraph.card, Kn]

/-- `K_n` with `n = 2^k`, `k ≥ 1`, is a `(2^{-5},0)`-expander (a proof through Definition 11:
`F = ∅`, `Nbr(U) = V ∖ U`, and `2^{-5} |U| / k² ≤ n − |U|` for `|U| ≤ 2n/3`). -/
theorem Kn_expander (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ^ k = n) :
    (Kn n).IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 := by
  intro U F hU hF h1 h2 h3
  have hF0 : F = ∅ := by
    have : (F.card : ℝ) ≤ 0 := by simpa using h3
    have : F.card = 0 := by exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
    exact Finset.card_eq_zero.1 this
  subst hF0
  have hnb : ((Kn n).deleteEdges ∅).nbrSet U = Finset.univ \ U := by
    ext v
    rw [FGraph.mem_nbrSet, Finset.mem_sdiff]
    constructor
    · rintro ⟨_, hv, _⟩; exact ⟨Finset.mem_univ _, hv⟩
    · rintro ⟨_, hv⟩
      obtain ⟨u, hu⟩ : U.Nonempty := Finset.card_pos.1 (by omega)
      refine ⟨by simp [Kn], hv, u, hu, ?_⟩
      simp only [FGraph.adj_iff, FGraph.deleteEdges_edges, Kn, Finset.sdiff_empty,
        Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mk_isDiag_iff]
      rintro rfl; exact hv hu
  rw [hnb, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  rw [Kn_card] at h2 ⊢
  have hlog : Real.logb 2 (n : ℝ) = k := by
    rw [← hn, Nat.cast_pow, Real.logb_pow]; norm_num
  rw [hlog]
  have hUn : U.card ≤ n := by
    have := Finset.card_le_univ U; simpa using this
  push_cast [hUn]
  have : (U.card : ℝ) ≤ 2 * n / 3 := h2
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  rw [div_le_iff₀ (by positivity)]
  norm_num
  nlinarith

/-- Every cycle of a graph on `Fin n` has length at most `n`. -/
theorem cycle_length_le (n : ℕ) (c : List (Fin n)) (h : (Obj.cycle c).WF) : c.length ≤ n := by
  have := h.1.length_le_card; simpa using this

/-! ## `CapGraphStatement` and `BMLemma25Statement` -/

/-- The hypotheses of `CapGraphStatement` are jointly satisfiable: `K_{2^{40}}` with
`T = 2^{117}`. -/
example : ∃ (G : FGraph (Fin (2 ^ 40))) (T : ℝ), (2 : ℝ) ^ 117 ≤ T ∧
    (2 : ℝ) ^ 40 ≤ (G.card : ℝ) ∧ G.IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 ∧
    (∀ c : List (Fin (2 ^ 40)), (Obj.cycle c).WF → (∀ e ∈ cycleEdges c, e ∈ G.edges) →
      (c.length : ℝ) < T) := by
  refine ⟨Kn (2 ^ 40), (2 : ℝ) ^ 117, le_rfl, (by rw [Kn_card]; norm_num),
    Kn_expander 40 _ (by norm_num) rfl, ?_⟩
  intro c hc _
  have := cycle_length_le _ c hc
  have h' : (c.length : ℝ) ≤ 2 ^ 40 := by exact_mod_cast this
  linarith

/-- The hypotheses of `BMLemma25Statement` are jointly satisfiable: `ε = 2^{-5}`, `K_{2^{40}}`. -/
example : (2 : ℝ) ^ (-5 : ℤ) ≤ 2 ^ (-5 : ℤ) ∧
    (2 : ℝ) ^ 30 / ((2 : ℝ) ^ (-5 : ℤ)) ^ 2 ≤ ((Kn (2 ^ 40)).card : ℝ) ∧
    2 ≤ (Kn (2 ^ 40)).card ∧ (Kn (2 ^ 40)).IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 := by
  refine ⟨le_rfl, ?_, ?_, Kn_expander 40 _ (by norm_num) rfl⟩
  · rw [Kn_card]; norm_num
  · rw [Kn_card]; norm_num

/-- The no-long-cycle hypothesis of `CapGraphStatement` is load-bearing: `K_{2^{200}}` is a
`(2^{-5},0)`-expander violating the conclusion at `T = 2^{117}`. -/
example : ¬ ∀ (G : FGraph (Fin (2 ^ 200))) (T : ℝ), (2 : ℝ) ^ 117 ≤ T →
    (2 : ℝ) ^ 40 ≤ (G.card : ℝ) → G.IsExpander ((2 : ℝ) ^ (-5 : ℤ)) 0 →
    (G.card : ℝ) ≤ 2 ^ 16 * T * Real.logb 2 T ^ 4 := by
  intro h
  have := h (Kn (2 ^ 200)) (2 ^ 117) le_rfl (by rw [Kn_card]; norm_num)
    (Kn_expander 200 _ (by norm_num) rfl)
  rw [logb_two_pow, Kn_card] at this; norm_num at this

end EGTest.Cap
