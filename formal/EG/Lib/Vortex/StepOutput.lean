module

public import EG.Lib.Vortex.StepAssemble

/-!
# One phase of a PV step: the conclusion (manuscript s4:lemPV, proof, steps (iv)–(vi), "Cost of
step `j`")

Unit P4A, stage 3. The properties of `EG.PVStep.outD`, `EG.PVStep.outA`, `EG.PVStep.outQ`, and
`EG.PVStep.Hyp.exists_output` (the conclusion of `EG.Spec.PVStepPhaseStatement`).
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

/-! ## Objects -/

theorem Hyp.outD_wf : ∀ o ∈ outD Rt W P u₂ Cs, o.WF := by
  intro o ho
  unfold outD at ho
  rcases List.mem_append.1 ho with ho | ho
  · obtain ⟨p, hp, ho⟩ := List.mem_flatMap.1 ho
    split_ifs at ho
    · simp at ho
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
      exact (hCq p hp).1 c hc
  · obtain ⟨w, hw, ho⟩ := List.mem_flatMap.1 ho
    rw [Finset.mem_toList] at hw
    split_ifs at ho
    · rw [List.mem_singleton] at ho
      subst ho
      show ¬ (s(w, u₂ w)).IsDiag
      rw [Sym2.mk_isDiag_iff]
      intro e
      exact h.u₂_notW hw (by rw [← e]; exact hw)
    · simp at ho

/-! ## Edges -/

omit h hCq in
theorem outD_edges :
    (outD Rt W P u₂ Cs).flatMap Obj.edges =
      P.flatMap (fun p => (if isArc Rt p then [] else (Cs p).map Obj.cycle).flatMap Obj.edges) ++
        singlesE W P u₂ := by
  unfold outD singlesE
  rw [List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  congr 1
  funext w
  split_ifs <;> simp [Obj.edges]

omit h hCq in
theorem outA_edges :
    (outA Rt P).flatMap walkEdges =
      P.flatMap (fun p => (if isArc Rt p then [p] else []).flatMap walkEdges) := by
  unfold outA
  rw [List.flatMap_assoc]

omit h hCq in
theorem outQ_edges :
    (outQ Rt W P u₁ u₂ qs).flatMap walkEdges =
      P.flatMap (fun p => (if isArc Rt p then [] else (qs p).toList).flatMap walkEdges) ++
        cherryE W P u₁ u₂ := by
  unfold outQ cherryE
  rw [List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  congr 1
  funext w
  split_ifs <;> simp

theorem Hyp.edges_perm :
    List.Perm ((outD Rt W P u₂ Cs).flatMap Obj.edges ++ (outA Rt P).flatMap walkEdges ++
        (outQ Rt W P u₁ u₂ qs).flatMap walkEdges)
      (P.flatMap walkEdges ++ resE W P u₁ u₂) := by
  rw [outD_edges, outA_edges, outQ_edges]
  have h3 := flatMap3_perm P
    (fun p => (if isArc Rt p then [] else (Cs p).map Obj.cycle).flatMap Obj.edges)
    (fun p => (if isArc Rt p then [p] else []).flatMap walkEdges)
    (fun p => (if isArc Rt p then [] else (qs p).toList).flatMap walkEdges)
    walkEdges (appE W P u₁ u₂) (fun p hp => h.edges_perm_p hp (hCq p hp))
  unfold resE
  rw [List.perm_iff_count] at h3 ⊢
  intro e
  have := h3 e
  simp only [List.count_append] at this ⊢
  omega

theorem Hyp.edges_nodup_mem :
    ((outD Rt W P u₂ Cs).flatMap Obj.edges ++ (outA Rt P).flatMap walkEdges ++
        (outQ Rt W P u₁ u₂ qs).flatMap walkEdges).Nodup ∧
      ∀ e, e ∈ (outD Rt W P u₂ Cs).flatMap Obj.edges ++ (outA Rt P).flatMap walkEdges ++
          (outQ Rt W P u₁ u₂ qs).flatMap walkEdges ↔
        e ∈ F ∨ ∃ w ∈ W, e = s(w, u₁ w) ∨ e = s(w, u₂ w) := by
  have hp := h.edges_perm hCq
  refine ⟨hp.nodup_iff.2 ?_, fun e => (hp.mem_iff).trans ?_⟩
  · rw [List.nodup_append]
    refine ⟨h.dec.2.1, h.resE_nodup, ?_⟩
    intro a ha b hb hab
    subst hab
    have haF : a ∈ F := h.dec.mem_iff.1 ha
    obtain ⟨w, hw, e | e⟩ := h.mem_resE.1 hb <;> subst e
    · exact (h.res w hw).2.2.2.1 haF
    · exact (h.res w hw).2.2.2.2 haF
  · rw [List.mem_append, h.mem_resE]
    exact Iff.or h.dec.mem_iff Iff.rfl

/-! ## Arcs -/

omit hCq in
theorem Hyp.outA_props : ∀ a ∈ outA Rt P, a.Nodup ∧ 2 ≤ a.length ∧
    (∃ x ∈ Rt, a.head? = some x) ∧ (∃ y ∈ Rt, a.getLast? = some y) ∧
    ∀ x ∈ a, (∃ e ∈ F, x ∈ e) ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w := by
  intro a ha
  unfold outA at ha
  obtain ⟨p, hp, ha⟩ := List.mem_flatMap.1 ha
  split_ifs at ha with harc
  · rw [List.mem_singleton] at ha
    subst ha
    obtain ⟨h1, h2⟩ := isArc_iff.1 harc
    exact ⟨h.dec.nodup hp, h.dec.two_le_length hp, h1, h2, fun x hx => Or.inl (h.mem_edge hp hx)⟩
  · simp at ha

omit h hCq in
theorem outA_length : (outA Rt P).length ≤ P.length := by
  unfold outA
  rw [List.length_flatMap]
  have := sum_map_le P (fun p => (if isArc Rt p then [p] else []).length) (fun _ => 1)
    (fun p _ => by split_ifs <;> simp)
  simpa using this

/-! ## Closed paths -/

omit hCq in
theorem Hyp.trail_head_RU {p : List V} (hp : p ∈ P) :
    ∃ x ∈ Rt ∪ Up, (trail W P u₁ u₂ p).head? = some x := by
  obtain ⟨a, b, K, hpK, hK, ha, hb, hab⟩ := h.shape hp
  refine ⟨_, ?_, h.trail_head hp ha⟩
  split_ifs with haW
  · exact h.u_mem haW p
  · exact h.RU_of_notW hp (List.mem_of_head? ha) haW

omit hCq in
theorem Hyp.trail_last_RU {p : List V} (hp : p ∈ P) :
    ∃ y ∈ Rt ∪ Up, (trail W P u₁ u₂ p).getLast? = some y := by
  obtain ⟨a, b, K, hpK, hK, ha, hb, hab⟩ := h.shape hp
  refine ⟨_, ?_, h.trail_last hp hb⟩
  split_ifs with hbW
  · exact h.u_mem hbW p
  · exact h.RU_of_notW hp (List.mem_of_getLast? hb) hbW

theorem Hyp.outQ_props : ∀ q ∈ outQ Rt W P u₁ u₂ qs, q.Nodup ∧ 2 ≤ pathLength q ∧
    (∃ x ∈ Rt ∪ Up, q.head? = some x) ∧ (∃ y ∈ Rt ∪ Up, q.getLast? = some y) ∧
    ∀ x ∈ q, (∃ e ∈ F, x ∈ e) ∨ x ∈ W ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w := by
  intro q hq
  unfold outQ at hq
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    split_ifs at hq with harc
    · simp at hq
    have hq' : q ∈ qs p := by
      cases e : qs p with
      | none => rw [e] at hq; simp at hq
      | some q' => rw [e] at hq; simp only [Option.toList_some, List.mem_singleton] at hq; rw [hq]; rfl
    obtain ⟨hnd, hlen, hqh, hql⟩ := (hCq p hp).2.2.2.2.1 q hq'
    obtain ⟨x, hx, hxh⟩ := h.trail_head_RU hp
    obtain ⟨y, hy, hyl⟩ := h.trail_last_RU hp
    refine ⟨hnd, ?_, ⟨x, hx, hqh.trans hxh⟩, ⟨y, hy, hql.trans hyl⟩, ?_⟩
    · -- a path with one edge would have an edge avoiding `W`
      simp only [pathLength]
      by_contra hlt
      have hq2 : q.length = 2 := by omega
      obtain ⟨x', y', rfl⟩ : ∃ x' y', q = [x', y'] := by
        match q, hq2 with
        | [x', y'], _ => exact ⟨x', y', rfl⟩
      have hxe : x' = x := by simpa using hqh.trans hxh
      have hye : y' = y := by simpa using hql.trans hyl
      subst hxe hye
      have hsub : s(x', y') ∈ walkEdges (trail W P u₁ u₂ p) := by
        refine (hCq p hp).2.2.1.subset (List.mem_append.2 (Or.inr ?_))
        rw [hq']
        simp
      obtain ⟨w, hw, hwe⟩ := h.trail_edges_meet hp _ hsub
      rcases Sym2.mem_iff.1 hwe with rfl | rfl
      · exact h.notW_of_RU hx hw
      · exact h.notW_of_RU hy hw
    · intro z hz
      rcases h.mem_trail hp ((hCq p hp).2.2.2.2.2.2 q hq' z hz) with hz | ⟨w, hw, _, rfl⟩
      · exact Or.inl (h.mem_edge hp hz)
      · rcases far_mem (P := P) (u₁ := u₁) (u₂ := u₂) w p with e | e <;> rw [e]
        · exact Or.inr (Or.inr ⟨w, hw, Or.inl rfl⟩)
        · exact Or.inr (Or.inr ⟨w, hw, Or.inr rfl⟩)
  · obtain ⟨w, hw, hq⟩ := List.mem_flatMap.1 hq
    rw [Finset.mem_toList] at hw
    split_ifs at hq
    · rw [List.mem_singleton] at hq
      subst hq
      have hu := (h.res w hw).1
      have h1 : u₁ w ≠ w := fun e => h.u₁_notW hw (by rw [e]; exact hw)
      have h2 : w ≠ u₂ w := fun e => h.u₂_notW hw (by rw [← e]; exact hw)
      refine ⟨by simp [h1, h2, hu], by simp [pathLength], ⟨u₁ w, (h.res w hw).2.1, rfl⟩,
        ⟨u₂ w, (h.res w hw).2.2.1, rfl⟩, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inr (Or.inr ⟨w, hw, Or.inl rfl⟩)
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr ⟨w, hw, Or.inr rfl⟩)
    · simp at hq

end Hyp

end PVStep

end EG
