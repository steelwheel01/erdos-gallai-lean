module

public import EG.Lib.Vortex.StepOutput

/-!
# One phase of a PV step: path ends (P4) and cost (manuscript s4:lemPV, proof, (v) (P4),
"Cost of step `j`")

Unit P4A, stage 3. `EG.PVStep.Hyp.outQ_pec` (every vertex `v` is an end of at most
`2 + #{w ∈ W : v ∈ {u₁ w, u₂ w}}` closed paths), `EG.PVStep.Hyp.cost` (at most
`|W| + 3(2|W| + 2|Up|)` objects and closed paths), and the assembled conclusion
`EG.PVStep.Hyp.exists_output`.
-/

public section

namespace EG

namespace PVStep

open List

variable {V : Type*} [DecidableEq V]

section Hyp

variable {Rt W Up : Finset V} {F : Finset (Sym2 V)} {P : List (List V)} {u₁ u₂ : V → V}
  (h : Hyp Rt W Up F P u₁ u₂)
  {Cs : List V → List (List V)} {qs : List V → Option (List V)}
  (hCq : ∀ p ∈ P, SplitOut (trail W P u₁ u₂ p) (Cs p) (qs p))
include h hCq

/-- (P4) for the closed paths of the phase, with the far-end count in place of `b`. -/
theorem Hyp.outQ_pec (v : V) :
    pathEndCount (outQ Rt W P u₁ u₂ qs) v ≤
      2 + (W.filter fun w => v = u₁ w ∨ v = u₂ w).card := by
  unfold outQ
  rw [pathEndCount, List.countP_append, List.countP_flatMap, List.countP_flatMap]
  have h1 := sum_map_le P
    (List.countP (fun q => decide (q.head? = some v ∨ q.getLast? = some v)) ∘
      fun p => if isArc Rt p then [] else (qs p).toList)
    (fun p => (if endAt v p then 1 else 0) +
      ∑ w ∈ W, (if endAt w p ∧ far P u₁ u₂ w p = v then 1 else 0))
    (fun p hp => by
      simp only [Function.comp]
      by_cases harc : isArc Rt p = true
      · rw [if_pos harc]; simp
      · rw [if_neg harc]; exact h.q_pec hp (hCq p hp) v)
  rw [List.sum_map_add, sum_map_ite_eq_countP, sum_map_finset_sum] at h1
  have h2 : (W.toList.map (List.countP (fun q => decide (q.head? = some v ∨ q.getLast? = some v)) ∘
      fun w => if pathEndCount P w = 0 then [[u₁ w, w, u₂ w]] else [])).sum =
      ∑ w ∈ W, (if pathEndCount P w = 0 ∧ (u₁ w = v ∨ u₂ w = v) then 1 else 0) := by
    rw [← Finset.sum_map_toList]
    congr 1
    refine List.map_congr_left fun w _ => ?_
    simp only [Function.comp]
    by_cases h0 : pathEndCount P w = 0
    · by_cases hv : u₁ w = v ∨ u₂ w = v <;> simp [h0, hv]
    · simp [h0]
  rw [h2]
  have h3 : ∑ w ∈ W, ((P.map fun p => if endAt w p ∧ far P u₁ u₂ w p = v then 1 else 0).sum +
      (if pathEndCount P w = 0 ∧ (u₁ w = v ∨ u₂ w = v) then 1 else 0)) ≤
      ∑ w ∈ W, (if v = u₁ w ∨ v = u₂ w then 1 else 0) := by
    refine Finset.sum_le_sum fun w hw => ?_
    rw [sum_map_ite_eq_countP]
    exact h.per_w hw v
  rw [Finset.sum_add_distrib] at h3
  rw [Finset.card_filter]
  have h4 := h.pec2 v
  have h5 : P.countP (fun p => endAt v p) = pathEndCount P v := rfl
  omega

/-- The cost of the phase (s4:eqPVstep, one phase). -/
theorem Hyp.cost :
    (outD Rt W P u₂ Cs).length + (outQ Rt W P u₁ u₂ qs).length ≤
      W.card + 3 * (2 * W.card + 2 * Up.card) := by
  unfold outD outQ
  simp only [List.length_append, List.length_flatMap]
  -- the paths
  have h1 := sum_map_le P
    (fun p => (if isArc Rt p then [] else (Cs p).map Obj.cycle).length +
      (if isArc Rt p then [] else (qs p).toList).length)
    (fun p => 3 * (if ∃ w ∈ W, endAt w p then 1 else 0) + (if ∃ u ∈ Up, endAt u p then 1 else 0))
    (fun p hp => by
      by_cases harc : isArc Rt p = true
      · rw [if_pos harc, if_pos harc]; simp
      · rw [if_neg harc, if_neg harc]; simpa using h.split_len hp (hCq p hp) harc)
  rw [List.sum_map_add, List.sum_map_add] at h1
  have e3 : (P.map fun p => 3 * (if ∃ w ∈ W, endAt w p then 1 else 0)).sum =
      3 * (P.map fun p => if ∃ w ∈ W, endAt w p then 1 else 0).sum := by
    rw [List.sum_map_mul_left]
  rw [e3, sum_map_ite_eq_countP, sum_map_ite_eq_countP] at h1
  have hcW := countP_exists_end_le P W
  have hcU := countP_exists_end_le P Up
  have hsW : ∑ w ∈ W, pathEndCount P w ≤ 2 * W.card := by
    have := Finset.sum_le_sum (s := W) fun w _ => h.pec2 w
    simpa [mul_comm] using this
  have hsU : ∑ w ∈ Up, pathEndCount P w ≤ 2 * Up.card := by
    have := Finset.sum_le_sum (s := Up) fun w _ => h.pec2 w
    simpa [mul_comm] using this
  -- the single edges and the cherries
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
  -- the order of the summands in the goal
  have e1 : (P.map fun p => (if isArc Rt p then [] else (Cs p).map Obj.cycle).length).sum +
      (P.map fun p => (if isArc Rt p then [] else (qs p).toList).length).sum ≤
      3 * P.countP (fun p => ∃ w ∈ W, endAt w p) + P.countP (fun p => ∃ u ∈ Up, endAt u p) := by
    exact h1
  omega

/-- The conclusion of `EG.Spec.PVStepPhaseStatement`, for given splits of the trails. -/
theorem Hyp.output_props :
    (∀ o ∈ outD Rt W P u₂ Cs, o.WF) ∧
      ((outD Rt W P u₂ Cs).flatMap Obj.edges ++ (outA Rt P).flatMap walkEdges ++
        (outQ Rt W P u₁ u₂ qs).flatMap walkEdges).Nodup ∧
      (∀ e, e ∈ (outD Rt W P u₂ Cs).flatMap Obj.edges ++ (outA Rt P).flatMap walkEdges ++
          (outQ Rt W P u₁ u₂ qs).flatMap walkEdges ↔
        e ∈ F ∨ ∃ w ∈ W, e = s(w, u₁ w) ∨ e = s(w, u₂ w)) ∧
      (∀ a ∈ outA Rt P, a.Nodup ∧ 2 ≤ a.length ∧ (∃ x ∈ Rt, a.head? = some x) ∧
        (∃ y ∈ Rt, a.getLast? = some y) ∧
        ∀ x ∈ a, (∃ e ∈ F, x ∈ e) ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w) ∧
      (outA Rt P).length ≤ P.length ∧
      (∀ q ∈ outQ Rt W P u₁ u₂ qs, q.Nodup ∧ 2 ≤ pathLength q ∧
        (∃ x ∈ Rt ∪ Up, q.head? = some x) ∧ (∃ y ∈ Rt ∪ Up, q.getLast? = some y) ∧
        ∀ x ∈ q, (∃ e ∈ F, x ∈ e) ∨ x ∈ W ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w) ∧
      (∀ v : V, pathEndCount (outQ Rt W P u₁ u₂ qs) v ≤
        2 + (W.filter fun w => v = u₁ w ∨ v = u₂ w).card) ∧
      (outD Rt W P u₂ Cs).length + (outQ Rt W P u₁ u₂ qs).length ≤
        W.card + 3 * (2 * W.card + 2 * Up.card) :=
  ⟨h.outD_wf hCq, (h.edges_nodup_mem hCq).1, (h.edges_nodup_mem hCq).2, h.outA_props,
    outA_length, h.outQ_props hCq, h.outQ_pec hCq, h.cost hCq⟩

end Hyp

/-- The splits exist (observation (S) for every trail). -/
theorem Hyp.exists_splits {Rt W Up : Finset V} {F : Finset (Sym2 V)} {P : List (List V)}
    {u₁ u₂ : V → V} (h : Hyp Rt W Up F P u₁ u₂) :
    ∃ (Cs : List V → List (List V)) (qs : List V → Option (List V)),
      ∀ p ∈ P, SplitOut (trail W P u₁ u₂ p) (Cs p) (qs p) := by
  have hs : ∀ p, ∃ (C : List (List V)) (q : Option (List V)),
      p ∈ P → SplitOut (trail W P u₁ u₂ p) C q := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨C, q, hCq⟩ := splitOut_exists (h.trail_ne_nil hp) (h.trail_edges_nodup hp)
        (h.trail_edges_notDiag hp)
      exact ⟨C, q, fun _ => hCq⟩
    · exact ⟨[], none, fun hp' => absurd hp' hp⟩
  choose Cs qs hCq using hs
  exact ⟨Cs, qs, hCq⟩

end PVStep

end EG
