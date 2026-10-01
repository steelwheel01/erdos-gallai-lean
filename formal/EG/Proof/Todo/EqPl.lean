module

public import EG.Spec.Light.Stages
public import EG.Spec.HB.Parentless
public import EG.Proof.Todo.ParentlessCount
public import EG.Lib.Light.PlParentless

/-!
# P3 stub: `EG.Spec.EqPlStatement` (s5:eqPl)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.EqPl`; consumers import this module.

Proof (P3, as in s5:defStages): for a light part `Z`, `Pl(Z)` is exactly the set of `v ∈ Z` with
`(v, Z)` parentless with respect to `Bad` (a light part outside `Bad` is a good parent), and
`lp = Σ_{Y ∈ Bad} |Y| (R − r(Y))`; so the sum over the non-demoted parts is at most the sum over all
light parts, which Proposition s2:propParentless (iii) (`EG.Todo.ParentlessCount`) bounds.
-/

public section

namespace EG.Todo

open EG.HB EG.Stage1 EG.Light

/-- Proved in P3. [s5:eqPl] see `EG.Spec.EqPlStatement`. -/
theorem EqPl : EG.Spec.EqPlStatement := by
  classical
  intro V _ G N0 Dstar run hR ω _
  have hV : run.Valid G Dstar := hR.2.2.2.2.2
  obtain ⟨h1, -⟩ := ParentlessCount V G Dstar run hV (Bad ω)
  calc ∑ Z ∈ (run.lightParts G).filter (fun Z => ¬ demoted ω Z), (Pl ω Z).card
      ≤ ∑ Z ∈ run.lightParts G, (Pl ω Z).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.zero_le _)
    _ = ∑ Z ∈ run.lightParts G, ((run.ancVerts G Z).filter (fun v =>
          ¬ ∃ Y ∈ run.lightParts G, Y ∉ Bad ω ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.ancVerts G Y)).card := by
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [Pl_eq_parentless]
    _ ≤ 2 * G.card + ∑ Y ∈ Bad ω, (run.ancVerts G Y).card * (run.R - Y.1) := by
        convert h1 using 3
    _ = 2 * G.card + lp ω := rfl

end EG.Todo
