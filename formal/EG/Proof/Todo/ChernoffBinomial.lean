module

public import EG.Spec.Found.Chernoff
public import EG.Lib.Prob.Chernoff

/-!
# P3 stub: `EG.Spec.ChernoffBinomialStatement` (s1:citChernoff)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.ChernoffBinomial`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:citChernoff] Proved in P3. See `EG.Spec.ChernoffBinomialStatement`. -/
theorem ChernoffBinomial : EG.Spec.ChernoffBinomialStatement := by
  intro Ω P n p δ I hδ0 hδ1 hp0 _ hI hind hp
  have hE : P.expect (fun ω => ∑ i, I i ω) = n * p := by
    rw [FinDist.expect_sum_of_zero_or_one hI, Finset.sum_congr rfl fun i _ => hp i]
    simp
  have hnp : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have h₁ := FinDist.chernoffGen_upper hI hind Finset.univ hE.le hδ0 hδ1
  have h₂ := FinDist.chernoffGen_lower hI hind Finset.univ hnp hE.ge hδ0
  refine ⟨hE, le_trans (P.prob_mono ?_) h₁, le_trans (P.prob_mono ?_) h₂⟩
  · intro ω hω
    exact le_of_lt (Set.mem_ofPred_eq ▸ hω)
  · intro ω hω
    exact le_of_lt (Set.mem_ofPred_eq ▸ hω)

end EG.Todo
