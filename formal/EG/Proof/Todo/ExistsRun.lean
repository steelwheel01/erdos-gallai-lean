module

public import EG.Spec.HB.Exists
public import EG.Lib.HB.Exists
public import EG.Proof.Todo.RoundExists
public import EG.Proof.Todo.DegRecRound

/-!
# P3 stub: `EG.Spec.ExistsRunStatement` (s2:propExists)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.ExistsRun`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:propExists] see `EG.Spec.ExistsRunStatement`. -/
theorem ExistsRun : EG.Spec.ExistsRunStatement := by
  intro V _ G Dstar hD
  have hD0 : 0 < Dstar := by linarith [hD.two_lt]
  have key : ∀ (n : ℕ) (H : FGraph V), H.edges.card ≤ n →
      ∃ cs : List (EG.HB.RoundChoice V), (EG.HB.Run.mk cs).Valid H Dstar := by
    intro n
    induction n with
    | zero =>
      intro H hH
      refine ⟨[], (EG.HB.Run.valid_nil_iff H Dstar).2 ?_⟩
      have h0 : H.edges.card = 0 := by omega
      unfold EG.HB.Round.d; rw [h0]; simpa using hD0
    | succ n ih =>
      intro H hH
      by_cases hd : EG.HB.Round.d H < Dstar
      · exact ⟨[], (EG.HB.Run.valid_nil_iff H Dstar).2 hd⟩
      push Not at hd
      obtain ⟨c, hc⟩ := EG.Todo.RoundExists V H Dstar hD.gamma2a hd
      obtain ⟨-, -, -, hA1, hA2, hA3, hA4, hA5⟩ := EG.Todo.DegRecRound V H c Dstar hD hd hc
      have hlt : EG.HB.Round.d (EG.HB.Round.next H c) < EG.HB.Round.d H := by linarith
      have hn : 0 < H.card := by
        by_contra h0
        have h0' : H.card = 0 := by omega
        have : EG.HB.Round.d H = 0 := by unfold EG.HB.Round.d; rw [h0']; simp
        linarith
      have hn' : (0 : ℝ) < H.card := by exact_mod_cast hn
      have hE : (EG.HB.Round.next H c).edges.card < H.edges.card := by
        unfold EG.HB.Round.d at hlt
        have hcard : (EG.HB.Round.next H c).card = H.card := rfl
        rw [hcard, div_lt_div_iff_of_pos_right hn'] at hlt
        exact_mod_cast (lt_of_mul_lt_mul_left hlt (by norm_num))
      obtain ⟨cs, hcs⟩ := ih (EG.HB.Round.next H c) (by omega)
      exact ⟨c :: cs, EG.HB.Run.valid_cons hd hc hcs⟩
  obtain ⟨cs, hcs⟩ := key G.edges.card G le_rfl
  exact ⟨_, hcs⟩

end EG.Todo
