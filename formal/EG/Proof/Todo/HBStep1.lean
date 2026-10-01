module

public import EG.Spec.HB.HBtpFacts
public import EG.Lib.HB.Run
public import EG.Lib.HB.SEP

/-!
# P3 stub: `EG.Spec.HBStep1Statement` (s2:defHBtp)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.HBStep1`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s2:defHBtp] see `EG.Spec.HBStep1Statement`. -/
theorem HBStep1 : EG.Spec.HBStep1Statement := by
  intro V _ H c _
  have hdisj : ∀ a ∈ EG.HB.Round.prePartAddrs H c, ∀ b ∈ EG.HB.Round.prePartAddrs H c, a ≠ b →
      Disjoint (EG.HB.Round.X0 H c a).edges (EG.HB.Round.X0 H c b).edges := by
    intro a ha b hb hab
    rw [Finset.disjoint_left]
    intro e hea heb
    have he : e ∈ (EG.HB.Round.graph' H c).edges := (EG.HB.Round.X0_le_graph' H c a).2 hea
    have hcount := EG.HB.STree.sep_count (EG.HB.Round.twoLevel H c) he
    have h2 : 1 < ((EG.HB.Round.twoLevel H c).leafAddrs.filter (fun L =>
        e ∈ ((EG.HB.Round.twoLevel H c).graphAtD (EG.HB.Round.graph' H c) L).edges)).card :=
      Finset.one_lt_card.2 ⟨a, Finset.mem_filter.2
        ⟨EG.HB.Round.prePartAddrs_subset_leafAddrs H c ha, hea⟩, b, Finset.mem_filter.2
        ⟨EG.HB.Round.prePartAddrs_subset_leafAddrs H c hb, heb⟩, hab⟩
    omega
  refine ⟨hdisj, fun a => (EG.HB.Round.X_le_X0 H c a).2, ?_⟩
  intro e a ha b hb hea heb
  by_contra hab
  exact Finset.disjoint_left.1 (hdisj a ha b hb hab) ((EG.HB.Round.partGraph_le_X0 H c a).2 hea)
    ((EG.HB.Round.partGraph_le_X0 H c b).2 heb)

end EG.Todo
