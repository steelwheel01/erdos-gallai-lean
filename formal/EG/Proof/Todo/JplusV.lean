module

public import EG.Spec.Chain.JPlusV
public import EG.Lib.Stage1.Law

/-!
# P3 stub: `EG.Spec.JplusVStatement` (s6:lemJplus)

Generated at the P2→P3 transition (2026-09-30), proved in P3 (round 1 of P3-s6). The label triples
`ω.col Y e` are single coordinates of the stage-1 product, so the family over all pairs `(Y, e)`
is a family of functions of pairwise disjoint (singleton) coordinate blocks
(`EG.Stage1.iIndepFun_of_dependsOn`). Keep the name `EG.Todo.JplusV`; consumers import this module.
-/

public section

namespace EG.Todo

/-- [s6:lemJplus] see `EG.Spec.JplusVStatement`. Proved in P3. -/
theorem JplusV : EG.Spec.JplusVStatement := by
  intro V _ G run
  exact EG.Stage1.iIndepFun_of_dependsOn G run (fun p => {Sum.inl p})
    (fun p p' hpp' => by
      simp only [Set.disjoint_singleton, ne_eq, Sum.inl.injEq]
      exact hpp')
    _ (fun p ω ω' h => by cases ω; cases ω'; exact h _ (Set.mem_singleton _))

end EG.Todo
