module

public import EG.Spec.Link.P18s
public import EG.Lib.Link.P18s
public import EG.Proof.Todo.StarS4
public import EG.Proof.Todo.L17s

/-!
# P3 stub: `EG.Spec.P18sStatement` (s3:lemP18s)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.P18s`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemP18s] see `EG.Spec.P18sStatement`. -/
theorem P18s : EG.Spec.P18sStatement := by
  intro V _ G ε' s₁ ρ hG hn hε1 hε2 h0 h1 hs
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  have S4 := EG.Todo.StarS4 G.card ε' ρ hn hε1 hε2 h0 h1
  have h8 := S4.1.trans S4.2.1
  have hp0 := Star.p_pos hn h0 h1
  have hp1 := Star.p_le_one (n := G.card) h1
  have hθ1 : 1 ≤ Star.theta G.card ε' ρ := by
    have hpi : 1 ≤ (Star.p G.card ρ)⁻¹ := one_le_inv₀ hp0 |>.2 hp1
    have : 1 ≤ (Star.p G.card ρ)⁻¹ ^ 2 := one_le_pow₀ hpi
    linarith [S4.2.1]
  exact ⟨fun U hUV hU1 hU23 => P18sProof.prop18 G hG hn hε hε2 hθ1 hs U hUV hU1 hU23,
    fun Ω μ R hR => P18sProof.lemma19 EG.Todo.L17s G hG hn hε1 hε2 h0 h1 hs h8 hθ1 Ω μ R hR⟩

end EG.Todo
