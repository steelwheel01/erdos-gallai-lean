module

public import EG.Spec.HB.HBtpFacts
public import EG.Lib.HB.Run

/-!
# P3 stub: `EG.Spec.AncestorFactsStatement` (s2:defAncestors)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.AncestorFacts`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:defAncestors] see `EG.Spec.AncestorFactsStatement`. -/
theorem AncestorFacts : EG.Spec.AncestorFactsStatement := by
  intro V _ G Dstar run _
  refine ⟨fun r a => ?_, fun Y _ => EG.HB.Run.partVerts_subset_Z0 run G Y.1 Y.2,
    fun l hl x => EG.HB.Run.anc_eq_empty_of_le_two run G hl x,
    fun l hl a => EG.HB.Run.fresh_eq_ports_of_le_two run G hl a,
    fun r w => EG.HB.Run.mem_D_iff run G⟩
  rw [EG.HB.Run.mem_ancestors]
  exact ⟨fun h => ⟨EG.HB.Run.isRound_of_mem_prePartAddrs h, h⟩, fun h => h.2⟩

end EG.Todo
