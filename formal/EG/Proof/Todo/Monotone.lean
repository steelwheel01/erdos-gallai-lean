module

public import EG.Spec.Link.Monotone
public import EG.Lib.Found.Graph
public import EG.Lib.Prob.Basic

/-!
# P3 stub: `EG.Spec.MonotoneStatement` (s3:lemMonotone)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.Monotone`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemMonotone] see `EG.Spec.MonotoneStatement`. -/
theorem Monotone : EG.Spec.MonotoneStatement := by
  intro V _
  refine ⟨fun H H' ε' s hle hV hH => hH.of_le hle hV,
    fun H ε' s ε'' s' hε hs hH => hH.mono hε hs,
    fun G G' W W' ℓ ℓ' t t' hle hV hW _ hℓ ht hG => hG.mono hle hV hW hℓ ht,
    fun X W ℓ t κ _ ι _ P hX hP ht => hX.exists_paths_sigma P hP ht, ?_⟩
  intro Ω Ω' μ μ' X W X' W' ℓ t hmap
  have h1 := FinDist.prob_map (μ := μ) (fun ω => (X ω, W ω))
    {p : FGraph V × Finset V | p.1.IsPathConnected ℓ t p.2}
  have h2 := FinDist.prob_map (μ := μ') (fun ω => (X' ω, W' ω))
    {p : FGraph V × Finset V | p.1.IsPathConnected ℓ t p.2}
  rw [hmap] at h1
  exact h1.symm.trans h2

end EG.Todo
