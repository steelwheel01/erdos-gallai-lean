module

public import EG.Spec.HB.Exists
public import EG.Proof.Todo.DegRecRound
public import EG.Lib.HB.Run

/-!
# P3 stub: `EG.Spec.RunTerminatesStatement` (s2:propExists)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.RunTerminates`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propExists] see `EG.Spec.RunTerminatesStatement`. -/
theorem RunTerminates : EG.Spec.RunTerminatesStatement := by
  intro V _ G Dstar cs hD hcs
  set run : EG.HB.Run V := EG.HB.Run.mk cs with hrun
  have hR : run.R = cs.length := rfl
  have hD0 : 0 < Dstar := by linarith [hD.two_lt]
  -- `d_{l+1} < d_l`
  have hdec : ∀ l ∈ Finset.Icc 1 cs.length, run.d G (l + 1) < run.d G l := by
    intro l hl
    have hr : run.IsRound l := Finset.mem_Icc.1 hl
    obtain ⟨h1, h2⟩ := hcs l hl
    obtain ⟨-, -, -, hA1, hA2, hA3, hA4, hA5⟩ := EG.Todo.DegRecRound V (run.graph G l)
      (run.choice l) Dstar hD h1 h2
    have e : run.d G (l + 1) = EG.HB.Round.d (EG.HB.Round.next (run.graph G l) (run.choice l)) := by
      unfold EG.HB.Run.d; rw [EG.HB.Run.graph_succ_of_isRound run G hr]
    rw [e]
    change _ < EG.HB.Round.d (run.graph G l)
    linarith
  refine ⟨hdec, ?_⟩
  -- the number of edges drops in every round
  rcases Nat.eq_zero_or_pos cs.length with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hn : 0 < G.card := by
    by_contra hn0
    push Not at hn0
    have hn0' : G.card = 0 := by omega
    have := (hcs 1 (Finset.mem_Icc.2 ⟨le_rfl, hpos⟩)).1
    rw [EG.HB.Run.d_eq, hn0'] at this
    simp at this
    linarith
  have hn' : (0 : ℝ) < G.card := by exact_mod_cast hn
  have hedge : ∀ l ∈ Finset.Icc 1 cs.length,
      (run.graph G (l + 1)).edges.card < (run.graph G l).edges.card := by
    intro l hl
    have := hdec l hl
    rw [EG.HB.Run.d_eq, EG.HB.Run.d_eq, div_lt_div_iff_of_pos_right hn'] at this
    exact_mod_cast (lt_of_mul_lt_mul_left this (by norm_num))
  have key : ∀ k, k ≤ cs.length → (run.graph G (k + 1)).edges.card + k ≤ G.edges.card := by
    intro k
    induction k with
    | zero => intro _; simp [EG.HB.Run.graph_one]
    | succ k ih =>
      intro hk
      have := ih (by omega)
      have := hedge (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
      omega
  have := key cs.length le_rfl
  omega

end EG.Todo
