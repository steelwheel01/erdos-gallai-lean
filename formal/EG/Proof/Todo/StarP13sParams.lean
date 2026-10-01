module

public import EG.Spec.Link.Star
public import EG.Lib.Link.Star

/-!
# P3 stub: `EG.Spec.StarP13sParamsStatement` (s3:eqStar)

Generated at the P2→P3 transition (2026-09-30). Proved in P3: "`σ_* = 24L^2/ε'` holds with
equality, and `Δ_*−λ_* = ⌈d_*λ_*/3⌉ ≥ d_*λ_*/3 = 8d_*λ_*L^2/(ε'σ_*)`". Keep the name
`EG.Todo.StarP13sParams`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:eqStar] see `EG.Spec.StarP13sParamsStatement`. -/
theorem StarP13sParams : EG.Spec.StarP13sParamsStatement := by
  intro n ε' ρ hn hε1 hε2 h0 h1
  have hε : 0 < ε' := lt_of_lt_of_le (by positivity) hε1
  have hL := Star.L_pos hn
  have hσ : Star.sigma n ε' = 24 * Real.logb 2 (n : ℝ) ^ 2 / ε' := rfl
  have heq : (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) / 3 =
      8 * (Star.d n ρ : ℝ) * (Star.lam n ρ : ℝ) * Real.logb 2 (n : ℝ) ^ 2 /
        (ε' * Star.sigma n ε') := by
    rw [hσ, ← Star.L_eq]
    field_simp
    ring
  have hle := Star.dlam_div_three_le n ρ
  refine ⟨hσ, hle, heq, Star.sigma_pos hn hε, Star.one_le_lam hn h0 h1, Star.one_le_d hn h0 h1,
    Star.lam_le_Delta n ρ, le_of_eq hσ.symm, ?_⟩
  rw [← heq]; exact hle

end EG.Todo
