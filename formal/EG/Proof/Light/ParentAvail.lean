module

public import EG.Spec.Light.Parent
public import EG.Proof.HB.StructureHY
public import EG.Lib.Light.Stages
public import EG.Lib.Stage1.COL

/-!
# Proof of the disjointness of the available U-lent edge sets over `(l, c)` (s5:lemParent)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.lemParentAvailDisjoint`
(`LemParentAvailDisjointStatement`), Step 8: "For distinct pairs `(l,c) ≠ (l',c')` the sets
`LentU_{l,c}` and `LentU_{l',c'}` lie in disjoint colour classes (the index `(l,c,σ)` differs),
so they are disjoint", with "Connectors of distinct `(Y,σ)` lie in distinct classes
`LU_{Y,l,c,σ}`: for a fixed `Y` these are distinct colour classes of one colouring, and for
distinct `Y` they lie in the disjoint sets `E(H_Y) ⊆ E_{r(Y)}(Y)` (F-c)" ([s2:propStructure]
(iii), `EG.structureHY`, proved by P2J). Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.HB EG.Stage1 EG.Light

universe u

/-- A good parent is an ancestor. -/
theorem mem_ancestors_of_goodParent {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}
    {ω : Outcome G run} {Y : PartId} (h : goodParent ω Y) : Y ∈ run.ancestors G := by
  classical
  have := h.1
  unfold Run.lightParts at this
  exact (Finset.mem_filter.1 this).1

/-- [s5:lemParent] "The sets `LentU_{l,c}` for distinct pairs `(l,c)` are pairwise disjoint",
through the available sets of (i). -/
theorem lemParentAvailDisjoint : EG.Spec.LemParentAvailDisjointStatement.{u} := by
  intro V _ G N0 Dstar run h ω _ l l' c c' hne
  have hV : run.Valid G Dstar := h.2.2.2.2.2
  have hHY := (structureHY V G Dstar run hV).2.2.2
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [lentUAvail, Finset.mem_biUnion, Finset.mem_range] at he he'
  obtain ⟨Y, hY, σ, -, heY⟩ := he
  obtain ⟨Y', hY', σ', -, heY'⟩ := he'
  have hYa := mem_ancestors_of_goodParent ((mem_goodParents ω).1 hY).1
  have hYa' := mem_ancestors_of_goodParent ((mem_goodParents ω).1 hY').1
  by_cases hYY : Y = Y'
  · subst hYY
    have htag : LentTag.U l c σ ≠ LentTag.U l' c' σ' := by
      intro ht
      injection ht with h1 h2 _
      exact hne (by rw [h1, h2])
    exact Finset.disjoint_left.1 (disjoint_lentClass G run Y (ω.colAt Y) htag) heY heY'
  · have h1 : e ∈ (run.ancGraph G Y).edges :=
      Lend_edges_subset G run Y _ (lentClass_edges_subset_Lend G run Y _ _ heY)
    have h2 : e ∈ (run.ancGraph G Y').edges :=
      Lend_edges_subset G run Y' _ (lentClass_edges_subset_Lend G run Y' _ _ heY')
    exact Finset.disjoint_left.1 (hHY Y hYa Y' hYa' hYY) h1 h2

end EG
