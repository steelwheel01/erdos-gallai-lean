module

public import EG.Lib.Vortex.StepCost

/-!
# One class of a TPV / VX⁺ step without rooted vertices (manuscript s4:lemTPV, proof, steps
(iv)–(v), "Cost of step `j`"; s4:thmVXp, proof, step (e) and "Cost")

Unit P3-s4. The step engine of `EG/Lib/Vortex/StepPhase.lean` … `StepCost.lean` (unit P4A,
written for Lemma PV) applied with no rooted vertices (`Rt = ∅`): then no path is an arc, and
every trail is split and its path closed later. The cost bound here is the one of Lemma TPV:
each trail gives at most three objects and closed paths (at most two split cycles, at most one
path, observation (S)), and each `w ∈ W` gives at most one single edge or cherry, so a class
produces at most `3|𝒫| + |W|` objects and closed paths (`EG.PVStep.Hyp.cost_paths`), where `𝒫`
is the Corollary-22 decomposition. (The manuscript counts `|W|` single edges plus three objects
per trail, cherries included; this is the same count, slightly sharper.)

Main result: `EG.PVStep.Hyp.exists_output_noRoot`.
-/

public section

namespace EG

namespace PVStep

open List

variable {V : Type*} [DecidableEq V]

/-- With no rooted vertices there are no arcs. -/
theorem outA_empty (P : List (List V)) : outA (∅ : Finset V) P = [] := by
  unfold outA
  apply eq_nil_of_forall_not_mem
  intro x hx
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.1 hx
  simp [isArc] at hp

section Hyp

variable {Rt W Up : Finset V} {F : Finset (Sym2 V)} {P : List (List V)} {u₁ u₂ : V → V}
  (h : Hyp Rt W Up F P u₁ u₂)
  {Cs : List V → List (List V)} {qs : List V → Option (List V)}
  (hCq : ∀ p ∈ P, SplitOut (trail W P u₁ u₂ p) (Cs p) (qs p))
include h hCq

/-- The cost of one class in the TPV form: at most three objects or closed paths per trail of a
path of `𝒫`, and at most one single edge or cherry per `w ∈ W`. -/
theorem Hyp.cost_paths :
    (outD Rt W P u₂ Cs).length + (outQ Rt W P u₁ u₂ qs).length ≤ 3 * P.length + W.card := by
  unfold outD outQ
  simp only [List.length_append, List.length_flatMap]
  have h1 := sum_map_le P
    (fun p => (if isArc Rt p then [] else (Cs p).map Obj.cycle).length +
      (if isArc Rt p then [] else (qs p).toList).length)
    (fun _ => 3)
    (fun p hp => by
      by_cases harc : isArc Rt p = true
      · rw [if_pos harc, if_pos harc]; simp
      · rw [if_neg harc, if_neg harc]
        have hC := (hCq p hp).2.1
        have hr := h.rep_trail hp
        have hq : (qs p).toList.length ≤ 1 := by cases qs p <;> simp
        simp only [List.length_map]
        omega)
  rw [List.sum_map_add] at h1
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h1
  have h2 : (W.toList.map fun w =>
        (if pathEndCount P w = 1 then [Obj.edge s(w, u₂ w)] else []).length).sum +
      (W.toList.map fun w => (if pathEndCount P w = 0 then [[u₁ w, w, u₂ w]] else []).length).sum
      ≤ W.card := by
    rw [← List.sum_map_add, Finset.sum_map_toList]
    have := Finset.sum_le_sum (s := W) (f := fun w =>
      (if pathEndCount P w = 1 then [Obj.edge s(w, u₂ w)] else []).length +
      (if pathEndCount P w = 0 then [[u₁ w, w, u₂ w]] else []).length) (g := fun _ => 1)
      (fun w _ => by split_ifs <;> simp_all)
    simpa using this
  have e1 : (P.map fun p => (if isArc Rt p then [] else (Cs p).map Obj.cycle).length).sum +
      (P.map fun p => (if isArc Rt p then [] else (qs p).toList).length).sum ≤ P.length * 3 := h1
  omega

end Hyp

/-- One class of a step with no rooted vertices: the output objects `D` (split cycles and single
edges) and the paths `Q` to be closed, with (P2)–(P4) of the manuscript and the cost bound
`|D| + |Q| ≤ 3|𝒫| + |W|`. -/
theorem Hyp.exists_output_noRoot {W Up : Finset V} {F : Finset (Sym2 V)} {P : List (List V)}
    {u₁ u₂ : V → V} (h : Hyp ∅ W Up F P u₁ u₂) :
    ∃ (D : List (Obj V)) (Q : List (List V)),
      (∀ o ∈ D, o.WF) ∧
      (D.flatMap Obj.edges ++ Q.flatMap walkEdges).Nodup ∧
      (∀ e, e ∈ D.flatMap Obj.edges ++ Q.flatMap walkEdges ↔
        e ∈ F ∨ ∃ w ∈ W, e = s(w, u₁ w) ∨ e = s(w, u₂ w)) ∧
      (∀ q ∈ Q, q.Nodup ∧ 2 ≤ pathLength q ∧ (∃ x ∈ Up, q.head? = some x) ∧
        (∃ y ∈ Up, q.getLast? = some y) ∧
        ∀ x ∈ q, (∃ e ∈ F, x ∈ e) ∨ x ∈ W ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w) ∧
      (∀ v : V, pathEndCount Q v ≤ 2 + (W.filter fun w => v = u₁ w ∨ v = u₂ w).card) ∧
      D.length + Q.length ≤ 3 * P.length + W.card := by
  obtain ⟨Cs, qs, hCq⟩ := h.exists_splits
  obtain ⟨hwf, hnd, hmem, _, _, hQ, hpec, _⟩ := h.output_props hCq
  have hA := outA_empty (V := V) P
  rw [hA] at hnd hmem
  simp only [List.flatMap_nil, List.append_nil] at hnd hmem
  refine ⟨outD ∅ W P u₂ Cs, outQ ∅ W P u₁ u₂ qs, hwf, hnd, hmem, fun q hq => ?_, hpec,
    h.cost_paths hCq⟩
  obtain ⟨h1, h2, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩, h5⟩ := hQ q hq
  simp only [Finset.empty_union] at hx hy
  exact ⟨h1, h2, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩, h5⟩

/-- `exists_output_noRoot` when no `w ∈ W` is an end of exactly one path (Theorem VX⁺, step
(d): "every `w ∈ W_j` is an end of an even number, hence of `0` or `2`, paths"): then no single
edge is output. -/
theorem Hyp.exists_output_noRoot_even {W Up : Finset V} {F : Finset (Sym2 V)}
    {P : List (List V)} {u₁ u₂ : V → V} (h : Hyp ∅ W Up F P u₁ u₂)
    (hW : ∀ w ∈ W, pathEndCount P w ≠ 1) :
    ∃ (D : List (Obj V)) (Q : List (List V)),
      (∀ o ∈ D, o.WF) ∧
      (D.flatMap Obj.edges ++ Q.flatMap walkEdges).Nodup ∧
      (∀ e, e ∈ D.flatMap Obj.edges ++ Q.flatMap walkEdges ↔
        e ∈ F ∨ ∃ w ∈ W, e = s(w, u₁ w) ∨ e = s(w, u₂ w)) ∧
      (∀ q ∈ Q, q.Nodup ∧ 2 ≤ pathLength q ∧ (∃ x ∈ Up, q.head? = some x) ∧
        (∃ y ∈ Up, q.getLast? = some y) ∧
        ∀ x ∈ q, (∃ e ∈ F, x ∈ e) ∨ x ∈ W ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w) ∧
      (∀ v : V, pathEndCount Q v ≤ 2 + (W.filter fun w => v = u₁ w ∨ v = u₂ w).card) ∧
      D.length + Q.length ≤ 3 * P.length + W.card ∧ D.countP Obj.isEdge = 0 := by
  obtain ⟨Cs, qs, hCq⟩ := h.exists_splits
  obtain ⟨hwf, hnd, hmem, _, _, hQ, hpec, _⟩ := h.output_props hCq
  have hA := outA_empty (V := V) P
  rw [hA] at hnd hmem
  simp only [List.flatMap_nil, List.append_nil] at hnd hmem
  have hD0 : (outD ∅ W P u₂ Cs).countP Obj.isEdge = 0 := by
    unfold outD
    rw [List.countP_eq_zero]
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨p, _, ho⟩ := List.mem_flatMap.1 ho
      split_ifs at ho
      · simp at ho
      · obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho
        simp [Obj.isEdge]
    · obtain ⟨w, hw, ho⟩ := List.mem_flatMap.1 ho
      rw [if_neg (hW w (Finset.mem_toList.1 hw))] at ho
      simp at ho
  refine ⟨outD ∅ W P u₂ Cs, outQ ∅ W P u₁ u₂ qs, hwf, hnd, hmem, fun q hq => ?_, hpec,
    h.cost_paths hCq, hD0⟩
  obtain ⟨h1, h2, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩, h5⟩ := hQ q hq
  simp only [Finset.empty_union] at hx hy
  exact ⟨h1, h2, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩, h5⟩

end PVStep

end EG
