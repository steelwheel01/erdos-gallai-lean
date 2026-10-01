module

public import EG.Spec.Found.Chernoff
public import EG.Lib.Prob.Chernoff

/-!
# P3 stub: `EG.Spec.ChernoffGenMeanStatement` (s1:citChernoffGen)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.ChernoffGenMean`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s1:citChernoffGen] Proved in P3. See `EG.Spec.ChernoffGenMeanStatement`. -/
theorem ChernoffGenMean : EG.Spec.ChernoffGenMeanStatement := by
  intro Ω P ι _ I δ hI hind hδ0 hδ1
  have hE : 0 ≤ P.expect (fun ω => ∑ i, I i ω) :=
    P.expect_nonneg fun ω => Finset.sum_nonneg fun i _ => by rcases hI i ω with h | h <;> simp [h]
  have h₁ := FinDist.chernoffGen_upper hI hind Finset.univ le_rfl hδ0 hδ1
  have h₂ := FinDist.chernoffGen_lower hI hind Finset.univ hE le_rfl hδ0
  refine ⟨le_trans (P.prob_mono ?_) h₁, le_trans (P.prob_mono ?_) h₂⟩
  · intro ω hω
    exact le_of_lt (Set.mem_ofPred_eq ▸ hω)
  · intro ω hω
    exact le_of_lt (Set.mem_ofPred_eq ▸ hω)

end EG.Todo
