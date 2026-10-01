module

public import EG.Spec.Link.Star
public import EG.Lib.Link.Star

/-!
# P3 stub: `EG.Spec.StarS6Statement` (s3:eqS6)

Generated at the P2→P3 transition (2026-09-30). Proved in P3: "immediate from (eqStar), since
`ε' ≤ 1 ≤ L`" (ceiling bounds of `EG/Lib/Link/Star.lean`). Keep the name `EG.Todo.StarS6`;
consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:eqS6] see `EG.Spec.StarS6Statement`. -/
theorem StarS6 : EG.Spec.StarS6Statement := by
  intro n ε' ρ hn hε1 hε2 h0 h1
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  have hL := Star.one_le_L hn
  have hp0 := Star.p_pos hn h0 h1
  have hp1 := Star.p_le_one (n := n) h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Star.sigma
    rw [le_div_iff₀ hε]
    have : (1 : ℝ) ≤ Star.L n ^ 2 := one_le_pow₀ hL
    nlinarith
  · have := Star.six_div_p_le_lam n ρ
    rw [div_le_iff₀ hp0] at this
    linarith
  · have := Star.one_div_p_le_d n ρ
    rw [div_le_iff₀ hp0] at this
    linarith
  · have := Star.d_lt hn h0 h1
    have h2 : (Star.d n ρ : ℝ) * Star.p n ρ ≤ (1 / Star.p n ρ + 1) * Star.p n ρ :=
      mul_le_mul_of_nonneg_right this.le hp0.le
    rw [add_mul, one_div, inv_mul_cancel₀ hp0.ne', one_mul] at h2
    exact h2
  · linarith

end EG.Todo
