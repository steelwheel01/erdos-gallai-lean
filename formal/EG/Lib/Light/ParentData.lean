module

public import EG.Defs.Walk
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Arcs indexed by (part, position) (s5:lemParent, Step 1)

Library for probe unit P4B (probe P-4, part 2), proof round 1. The arcs of the parts `Z ∈ Zs` are
given by lists `L Z`; the arc `(Z, j)` is `(L Z)[j]` ([s5:lemParent] Step 1: "For each `Z` list its
phase-`c` arcs in a fixed order as `a_{Z,1}, …, a_{Z,na(Z)}` … the class `i` is
`𝒜_i := {a_{Z,i} : na(Z) ≥ i}`"). Counting lemmas for the index set `arcIdx Zs L`. Design note
`formal/work/p2b/P4B.md`.
-/

public section

namespace EG.PData

variable {P V : Type*} [DecidableEq P]

/-- The index set of the arcs: pairs `(Z, j)` with `Z ∈ Zs`, `j < |L Z|`. -/
@[expose] def arcIdx (Zs : Finset P) (L : P → List (List V)) : Finset (P × ℕ) :=
  Zs.biUnion fun Z => (Finset.range (L Z).length).image (Prod.mk Z)

/-- The arc `(Z, j)`. -/
@[expose] def arcAt (L : P → List (List V)) (a : P × ℕ) : List V := (L a.1).getD a.2 []

theorem mem_arcIdx {Zs : Finset P} {L : P → List (List V)} {a : P × ℕ} :
    a ∈ arcIdx Zs L ↔ a.1 ∈ Zs ∧ a.2 < (L a.1).length := by
  obtain ⟨Z, j⟩ := a
  simp only [arcIdx, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨Z', hZ', j', hj', rfl, rfl⟩; exact ⟨hZ', hj'⟩
  · rintro ⟨hZ, hj⟩; exact ⟨Z, hZ, j, hj, rfl, rfl⟩

theorem arcAt_eq {L : P → List (List V)} {a : P × ℕ} (h : a.2 < (L a.1).length) :
    arcAt L a = (L a.1)[a.2] := by
  simp [arcAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem arcAt_mem {L : P → List (List V)} {a : P × ℕ} (h : a.2 < (L a.1).length) :
    arcAt L a ∈ L a.1 := by
  rw [arcAt_eq h]; exact List.getElem_mem h

theorem card_filter_range_getD {α : Type*} (Q : α → Prop) [DecidablePred Q] (d : α) :
    ∀ l : List α, ((Finset.range l.length).filter fun j => Q (l.getD j d)).card = l.countP Q
  | [] => by simp
  | a :: l => by
    rw [Finset.card_filter, List.length_cons, Finset.sum_range_succ', List.countP_cons]
    have ih := card_filter_range_getD Q d l
    rw [Finset.card_filter] at ih
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    simp

/-- Counting the arcs with a property, part by part. -/
theorem card_filter_arcIdx (Zs : Finset P) (L : P → List (List V)) (Q : List V → Prop)
    [DecidablePred Q] :
    ((arcIdx Zs L).filter fun a => Q (arcAt L a)).card = ∑ Z ∈ Zs, (L Z).countP Q := by
  rw [arcIdx, Finset.filter_biUnion, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun Z _ => ?_
    rw [Finset.filter_image, Finset.card_image_of_injective _ (Prod.mk_right_injective Z)]
    exact card_filter_range_getD Q [] (L Z)
  · intro Z _ Z' _ hZZ
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter, Finset.mem_image] at ha ha'
    obtain ⟨⟨j, -, rfl⟩, -⟩ := ha
    obtain ⟨⟨j', -, hj'⟩, -⟩ := ha'
    exact hZZ (congrArg Prod.fst hj').symm

theorem card_arcIdx (Zs : Finset P) (L : P → List (List V)) :
    (arcIdx Zs L).card = ∑ Z ∈ Zs, (L Z).length := by
  have := card_filter_arcIdx Zs L (fun _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial)] at this
  rw [this]
  refine Finset.sum_congr rfl fun Z _ => ?_
  simp

end EG.PData
