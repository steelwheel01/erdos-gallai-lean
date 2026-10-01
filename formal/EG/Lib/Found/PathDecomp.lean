module

public import EG.Defs.PathDecomp
public import EG.Lib.Found.Graph

/-!
# API for `IsPathDecomp`, `pathEndCount`, `IsPathCycleDecomp` (s1:citCor22, s4 (E))

* `IsPathDecomp.two_le_length`, `IsPathDecomp.nodup`, `IsPathDecomp.mem_iff`,
  `IsPathDecomp.edges_mem`, `IsPathDecomp.not_isDiag` (a loop is in no path decomposition),
  `isPathDecomp_nil` (the empty edge set), `isPathDecomp_singleton` (one edge);
* `pathEndCount_nil`, `pathEndCount_cons`, `pathEndCount_le_length`;
* `isPathCycleDecomp_nil_right` (no cycles: `IsPathCycleDecomp F P [] ↔ IsPathDecomp F P`).
-/

public section


namespace EG

variable {V : Type*}

/-- The edges of a walk without repeated vertices are not loops. -/
theorem not_isDiag_of_mem_walkEdges {p : List V} (hp : p.Nodup) {e : Sym2 V}
    (he : e ∈ walkEdges p) : ¬ e.IsDiag := by
  induction p with
  | nil => simp at he
  | cons a t ih =>
    cases t with
    | nil => simp at he
    | cons b t =>
      rw [walkEdges_cons_cons, List.mem_cons] at he
      rw [List.nodup_cons] at hp
      rcases he with rfl | he
      · rw [Sym2.mk_isDiag_iff]
        rintro rfl
        exact hp.1 (List.mem_cons_self ..)
      · exact ih hp.2 he

namespace IsPathDecomp

variable {F : Set (Sym2 V)} {P : List (List V)}

theorem two_le_length (h : IsPathDecomp F P) {p : List V} (hp : p ∈ P) : 2 ≤ p.length :=
  (h.1 p hp).1

theorem nodup (h : IsPathDecomp F P) {p : List V} (hp : p ∈ P) : p.Nodup := (h.1 p hp).2

theorem mem_iff (h : IsPathDecomp F P) {e : Sym2 V} : e ∈ P.flatMap walkEdges ↔ e ∈ F :=
  h.2.2 e

theorem edges_mem (h : IsPathDecomp F P) {p : List V} (hp : p ∈ P) {e : Sym2 V}
    (he : e ∈ walkEdges p) : e ∈ F :=
  h.mem_iff.1 (List.mem_flatMap.2 ⟨p, hp, he⟩)

/-- A path decomposition exists only for loopless edge sets. -/
theorem not_isDiag (h : IsPathDecomp F P) {e : Sym2 V} (he : e ∈ F) : ¬ e.IsDiag := by
  obtain ⟨p, hp, hep⟩ := List.mem_flatMap.1 (h.mem_iff.2 he)
  exact not_isDiag_of_mem_walkEdges (h.nodup hp) hep

end IsPathDecomp

theorem isPathDecomp_nil : IsPathDecomp (∅ : Set (Sym2 V)) [] := by
  simp [IsPathDecomp]

/-- A single non-loop edge `uv` is decomposed by the path `[u, v]`. -/
theorem isPathDecomp_singleton {u v : V} (huv : u ≠ v) :
    IsPathDecomp ({s(u, v)} : Set (Sym2 V)) [[u, v]] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [huv]
  · simp
  · intro e; simp

section DecEq

variable [DecidableEq V]

@[simp] theorem pathEndCount_nil (v : V) : pathEndCount ([] : List (List V)) v = 0 := rfl

theorem pathEndCount_cons (p : List V) (P : List (List V)) (v : V) :
    pathEndCount (p :: P) v =
      pathEndCount P v + if p.head? = some v ∨ p.getLast? = some v then 1 else 0 := by
  simp only [pathEndCount, List.countP_cons, decide_eq_true_eq]

theorem pathEndCount_le_length (P : List (List V)) (v : V) : pathEndCount P v ≤ P.length :=
  List.countP_le_length

end DecEq

/-- With no cycles, a path-and-cycle decomposition is a path decomposition. -/
theorem isPathCycleDecomp_nil_right {F : Set (Sym2 V)} {P : List (List V)} :
    IsPathCycleDecomp F P [] ↔ IsPathDecomp F P := by
  simp [IsPathCycleDecomp, IsPathDecomp]

end EG
