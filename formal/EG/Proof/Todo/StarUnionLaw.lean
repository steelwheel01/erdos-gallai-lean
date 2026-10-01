module

public import EG.Spec.Link.Star
public import EG.Lib.Link.Star
public import EG.Lib.Prob.UnionRSubset

/-!
# P3 stub: `EG.Spec.StarUnionLawStatement` (s3:eqS2)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.StarUnionLaw`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:eqS2] see `EG.Spec.StarUnionLawStatement`. -/
theorem StarUnionLaw : EG.Spec.StarUnionLawStatement := by
  intro α _ Ω μ S n ρ Vs hn h0 h1 hind hR
  refine FinDist.isRSubset_biUnion Vs
    (fun i : Fin (Star.ell n) => if (i : ℕ) + 1 < Star.ell n then Star.p n ρ else Star.q ρ)
    h0.le h1 hind hR ?_
  rw [Fin.prod_univ_eq_prod_range
    (fun k => 1 - if k + 1 < Star.ell n then Star.p n ρ else Star.q ρ) (Star.ell n)]
  obtain ⟨m, hm⟩ : ∃ m, Star.ell n = m + 1 := ⟨Star.ell n - 1, by have := Star.two_le_ell hn; omega⟩
  have hpow := Star.one_sub_p_pow hn h1
  rw [show Star.ell n - 1 = m by omega] at hpow
  rw [hm, Finset.prod_range_succ, if_neg (lt_irrefl _)]
  rw [Finset.prod_congr rfl (fun k hk => by
    rw [if_pos (by have := Finset.mem_range.1 hk; omega)]), Finset.prod_const,
    Finset.card_range, hpow, Star.q]
  have hden : (1 : ℝ) - 9 / 10 * ρ ≠ 0 := by linarith
  rw [div_mul_cancel₀ _ hden]

end EG.Todo
