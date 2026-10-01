module

public import EG.Spec.HB.StructureLight
public import EG.Spec.HB.Structure
public import EG.Proof.HB.Structure

/-!
# [s2:propStructure] (iv), light-part clause, in the form used by probe P4B

Proof file of `EG.Spec.StructureLightStatement` (unit P4B, probe P-4, part 2). It was a
declared-input stub; after the fix round of `formal/work/p2b/P4B.md` it is DERIVED from the
s2 unit's `EG.Spec.StructureVertexStatement` (first clause), so that propStructure (iv) has one
source. The declared input is now `EG.structureVertex` (`EG/Proof/HB/Structure.lean`).

Derivation: `RunHyp` contains `run.Valid`; a light part `Z ∈ run.lightParts G` is `(l, a)` with
`l ∈ [1,R]`, `a ∈ run.prePartAddrs G l` and `run.isLight G l a` (`lightParts = parts.filter
isLight`, `parts` = the pairs `(l, a)`); `run.ancVerts G Z = run.partVerts G Z.1 Z.2`
(definitional). Two distinct light parts of one round have distinct addresses.
-/

public section

namespace EG

open EG.HB

/-- Membership in `run.lightParts G`: a round `l ∈ [1,R]`, a pre-part address of round `l`, and
lightness. -/
theorem mem_lightParts_iff {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)
    (Z : PartId) :
    Z ∈ run.lightParts G ↔
      Z.1 ∈ Finset.Icc 1 run.R ∧ Z.2 ∈ run.prePartAddrs G Z.1 ∧ run.isLight G Z.1 Z.2 := by
  classical
  obtain ⟨l, a⟩ := Z
  simp only [Run.lightParts, Run.parts, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨l', hl', a', ha', he⟩, hL⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hl', ha', hL⟩
  · rintro ⟨hl, ha, hL⟩
    exact ⟨⟨l, hl, a, ha, rfl⟩, hL⟩

/-- `[s2:propStructure]` (iv), first clause, in the `RunHyp` / `lightParts` form, from
`StructureVertexStatement`. -/
theorem structureLight_of_structureVertex.{u}
    (hS : EG.Spec.StructureVertexStatement.{u}) : EG.Spec.StructureLightStatement.{u} := by
  intro V _ G N0 Dstar run h Z hZ Z' hZ' hl hne
  have hValid : run.Valid G Dstar := h.2.2.2.2.2
  rw [mem_lightParts_iff] at hZ hZ'
  obtain ⟨hZl, hZa, hZL⟩ := hZ
  obtain ⟨-, hZ'a, hZ'L⟩ := hZ'
  obtain ⟨l, a⟩ := Z
  obtain ⟨l', b⟩ := Z'
  simp only at hl hZl hZa hZL hZ'a hZ'L
  subst hl
  have hab : a ≠ b := fun e => hne (by rw [e])
  exact (hS V G Dstar run hValid l hZl).1 a hZa b hZ'a hab hZL hZ'L

/-- [s2:propStructure] (iv) "light parts of one round are pairwise vertex-disjoint" (derived from
the declared input `EG.structureVertex`). -/
theorem structureLight : EG.Spec.StructureLightStatement :=
  structureLight_of_structureVertex structureVertex

end EG
