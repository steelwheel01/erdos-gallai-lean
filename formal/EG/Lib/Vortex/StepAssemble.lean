module

public import EG.Lib.Vortex.StepCount

/-!
# One phase of a PV step: the output (manuscript s4:lemPV, proof, steps (v), (vi) and "Cost of
step `j`")

Unit P4A, stage 3. Each trail is split by (S) (`EG.splitOut_exists`); a path of `P` with both ends
in `Rt` is declared an arc (it has no appended edge, so its trail is itself); every other trail
gives its split cycles (objects) and its path (closed in (vi)); a vertex `w ∈ W` that is an end of
exactly one path gives the single edge `w u₂(w)`; a vertex `w ∈ W` that is an end of no path gives
the cherry `u₁(w) w u₂(w)` (closed in (vi)).

Main result: `EG.PVStep.Hyp.exists_output` (the conclusion of `EG.Spec.PVStepPhaseStatement`).

Deviation from the manuscript's rule (vi), recorded in `formal/work/p2b/P4A.md` (proof round 1):
a path of `PathsQ_{j,c}` that comes from a trail with appended edges and has both ends in `Rt` is
closed here rather than declared an arc. The Spec allows it (the cost bound counts such trails as
type (1) anyway, and arcs are only required to be at most `|P|`).
-/

public section

namespace EG

namespace PVStep

open List

variable {V : Type*} [DecidableEq V]

/-! ## Generic lemmas -/

theorem flatMap3_perm {α β : Type*} [DecidableEq β] (l : List α) (f g k a b : α → List β)
    (h : ∀ x ∈ l, List.Perm (f x ++ g x ++ k x) (a x ++ b x)) :
    List.Perm (l.flatMap f ++ l.flatMap g ++ l.flatMap k) (l.flatMap a ++ l.flatMap b) := by
  rw [List.perm_iff_count]
  intro e
  induction l with
  | nil => simp
  | cons x l ih =>
    have h1 := (h x (List.mem_cons_self ..)).count_eq e
    have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons, List.count_append] at h1 h2 ⊢
    omega

/-! ## The arcs -/

section Defs

variable (Rt W : Finset V) (P : List (List V)) (u₁ u₂ : V → V)
  (Cs : List V → List (List V)) (qs : List V → Option (List V))

/-- A path with both ends in `Rt` (declared an arc). -/
@[expose] def isArc (p : List V) : Bool :=
  decide ((∃ x ∈ Rt, p.head? = some x) ∧ (∃ y ∈ Rt, p.getLast? = some y))

/-- The output objects: split cycles of the non-arc trails, and the single edges. -/
@[expose] noncomputable def outD : List (Obj V) :=
  P.flatMap (fun p => if isArc Rt p then [] else (Cs p).map Obj.cycle) ++
    W.toList.flatMap (fun w => if pathEndCount P w = 1 then [Obj.edge s(w, u₂ w)] else [])

/-- The arcs. -/
@[expose] def outA : List (List V) := P.flatMap (fun p => if isArc Rt p then [p] else [])

/-- The paths closed in (vi): the paths of the non-arc trails, and the cherries. -/
@[expose] noncomputable def outQ : List (List V) :=
  P.flatMap (fun p => if isArc Rt p then [] else (qs p).toList) ++
    W.toList.flatMap (fun w => if pathEndCount P w = 0 then [[u₁ w, w, u₂ w]] else [])

end Defs

theorem isArc_iff {Rt : Finset V} {p : List V} :
    isArc Rt p = true ↔ (∃ x ∈ Rt, p.head? = some x) ∧ (∃ y ∈ Rt, p.getLast? = some y) := by
  simp [isArc]

section Hyp

variable {Rt W Up : Finset V} {F : Finset (Sym2 V)} {P : List (List V)} {u₁ u₂ : V → V}
  (h : Hyp Rt W Up F P u₁ u₂)
include h

theorem Hyp.arc_noW {p : List V} (hp : p ∈ P) (ha : isArc Rt p = true) : ∀ w ∈ W, ¬ endAt w p := by
  obtain ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyp⟩⟩ := isArc_iff.1 ha
  intro w hw hwp
  rcases hwp with e | e
  · rw [hxp, Option.some.injEq] at e
    subst e
    exact Finset.disjoint_left.1 h.dRW hx hw
  · rw [hyp, Option.some.injEq] at e
    subst e
    exact Finset.disjoint_left.1 h.dRW hy hw

theorem Hyp.appE_arc {p : List V} (hp : p ∈ P) (ha : isArc Rt p = true) :
    appE W P u₁ u₂ p = [] := by
  apply eq_nil_of_forall_not_mem
  intro e he
  obtain ⟨w, hw, hwp, _⟩ := (h.mem_appE hp).1 he
  exact h.arc_noW hp ha w hw hwp

/-- The edges contributed by one path `p` of `P`. -/
theorem Hyp.edges_perm_p {Cs : List V → List (List V)} {qs : List V → Option (List V)}
    {p : List V} (hp : p ∈ P) (hCq : SplitOut (trail W P u₁ u₂ p) (Cs p) (qs p)) :
    List.Perm
      ((if isArc Rt p then [] else (Cs p).map Obj.cycle).flatMap Obj.edges ++
        (if isArc Rt p then [p] else []).flatMap walkEdges ++
        (if isArc Rt p then [] else (qs p).toList).flatMap walkEdges)
      (walkEdges p ++ appE W P u₁ u₂ p) := by
  by_cases ha : isArc Rt p = true
  · simp only [ha, if_true, List.flatMap_nil, List.nil_append, List.flatMap_singleton,
      List.append_nil, h.appE_arc hp ha]
    exact List.Perm.refl _
  · simp only [ha, Bool.false_eq_true, if_false, List.flatMap_nil, List.append_nil]
    refine List.Perm.trans ?_ (h.walkEdges_trail hp)
    refine List.Perm.trans ?_ hCq.2.2.1
    rw [List.flatMap_map]
    have e1 : ((Cs p).flatMap fun a => Obj.edges (Obj.cycle a)) = (Cs p).flatMap cycleEdges := rfl
    rw [e1]
    cases qs p <;> simp

/-- The number of objects and closed paths of one non-arc trail. -/
theorem Hyp.split_len {C : List (List V)} {q : Option (List V)} {p : List V} (hp : p ∈ P)
    (hCq : SplitOut (trail W P u₁ u₂ p) C q) (hna : ¬ isArc Rt p = true) :
    C.length + q.toList.length ≤
      3 * (if ∃ w ∈ W, endAt w p then 1 else 0) + (if ∃ u ∈ Up, endAt u p then 1 else 0) := by
  have hC := hCq.2.1
  have hq : q.toList.length ≤ 1 := by cases q <;> simp
  by_cases hW : ∃ w ∈ W, endAt w p
  · have := h.rep_trail hp
    simp only [hW, if_true]
    omega
  · have hW' : ∀ w ∈ W, ¬ endAt w p := fun w hw hwp => hW ⟨w, hw, hwp⟩
    rw [h.trail_eq_self hp hW', List.toFinset_card_of_nodup (h.dec.nodup hp), Nat.sub_self] at hC
    have hU : ∃ u ∈ Up, endAt u p := by
      obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
      have haR := h.RU_of_notW hp (List.mem_of_head? ha) (fun haW => hW' a haW (Or.inl ha))
      have hbR := h.RU_of_notW hp (List.mem_of_getLast? hb) (fun hbW => hW' b hbW (Or.inr hb))
      rw [Finset.mem_union] at haR hbR
      rcases haR with haR | haU
      · rcases hbR with hbR | hbU
        · exact absurd (isArc_iff.2 ⟨⟨a, haR, ha⟩, ⟨b, hbR, hb⟩⟩) hna
        · exact ⟨b, hbU, Or.inr hb⟩
      · exact ⟨a, haU, Or.inl ha⟩
    simp only [hW, hU, if_true, if_false]
    omega

omit h in
theorem ite_eq_le (c : Prop) [Decidable c] (x y v : V) :
    (if (if c then x else y) = v then 1 else 0) ≤
      (if y = v then 1 else 0) + (if c ∧ x = v then 1 else 0) := by
  by_cases hc : c <;> simp [hc]

omit h in
theorem sum_far_eq (W : Finset V) (f : V → V) {p : List V} {a b : V} (ha : p.head? = some a)
    (hb : p.getLast? = some b) (hab : a ≠ b) (v : V) :
    ∑ w ∈ W, (if endAt w p ∧ f w = v then 1 else 0) =
      (if a ∈ W ∧ f a = v then 1 else 0) + (if b ∈ W ∧ f b = v then 1 else 0) := by
  have hpt : ∀ w, (if endAt w p ∧ f w = v then 1 else 0) =
      (if w = a ∧ f a = v then 1 else 0) + (if w = b ∧ f b = v then 1 else 0) := by
    intro w
    simp only [endAt, ha, hb, Option.some.injEq]
    by_cases hwa : w = a
    · subst hwa
      simp [hab]
    · by_cases hwb : w = b
      · subst hwb
        have : a ≠ w := hab
        simp [this, hwa]
      · have h1 : a ≠ w := fun e => hwa e.symm
        have h2 : b ≠ w := fun e => hwb e.symm
        simp [hwa, hwb, h1, h2]
  rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_add_distrib]
  congr 1
  · by_cases hc : f a = v <;> simp [hc]
  · by_cases hc : f b = v <;> simp [hc]

/-- The ends of the closed path of one non-arc trail. -/
theorem Hyp.q_pec {C : List (List V)} {q : Option (List V)} {p : List V} (hp : p ∈ P)
    (hCq : SplitOut (trail W P u₁ u₂ p) C q) (v : V) :
    pathEndCount q.toList v ≤ (if endAt v p then 1 else 0) +
      ∑ w ∈ W, (if endAt w p ∧ far P u₁ u₂ w p = v then 1 else 0) := by
  cases q with
  | none => simp
  | some q =>
    obtain ⟨_, _, hq1, hq2⟩ := hCq.2.2.2.2.1 q rfl
    obtain ⟨a, b, K, hpK, hK, ha, hb, hab⟩ := h.shape hp
    rw [sum_far_eq W (fun w => far P u₁ u₂ w p) ha hb hab v]
    have hqh : q.head? = some (if a ∈ W then far P u₁ u₂ a p else a) :=
      hq1.trans (h.trail_head hp ha)
    have hql : q.getLast? = some (if b ∈ W then far P u₁ u₂ b p else b) :=
      hq2.trans (h.trail_last hp hb)
    have hend : (if endAt v p then 1 else 0) = (if a = v then 1 else 0) + (if b = v then 1 else 0) := by
      have := end_ite_eq (h.dec.nodup hp) (h.dec.two_le_length hp) v
      simp only [endAt]
      rw [this, ha, hb]
      simp
    rw [hend]
    have e1 := ite_eq_le (a ∈ W) (far P u₁ u₂ a p) a v
    have e2 := ite_eq_le (b ∈ W) (far P u₁ u₂ b p) b v
    rw [Option.toList_some, pathEndCount_cons, pathEndCount_nil, zero_add, hqh, hql]
    simp only [Option.some.injEq]
    by_cases h1 : (if a ∈ W then far P u₁ u₂ a p else a) = v <;>
      by_cases h2 : (if b ∈ W then far P u₁ u₂ b p else b) = v
    · rw [if_pos (Or.inl h1)]; rw [if_pos h1] at e1; omega
    · rw [if_pos (Or.inl h1)]; rw [if_pos h1] at e1; omega
    · rw [if_pos (Or.inr h2)]; rw [if_pos h2] at e2; omega
    · rw [if_neg (by tauto)]; omega

/-- Per `w ∈ W`: the reserved edges at `w` give at most one path end at `v`. -/
theorem Hyp.per_w {w : V} (hw : w ∈ W) (v : V) :
    P.countP (fun p => endAt w p ∧ far P u₁ u₂ w p = v) +
        (if pathEndCount P w = 0 ∧ (u₁ w = v ∨ u₂ w = v) then 1 else 0) ≤
      (if v = u₁ w ∨ v = u₂ w then 1 else 0) := by
  have hu := (h.res w hw).1
  have hpec : pathEndCount P w = P.countP (fun p => endAt w p) := rfl
  by_cases hv : v = u₁ w ∨ v = u₂ w
  · rw [if_pos hv]
    by_cases h0 : pathEndCount P w = 0
    · have : P.countP (fun p => endAt w p ∧ far P u₁ u₂ w p = v) = 0 := by
        have := List.countP_mono_left (l := P) (p := fun p => decide (endAt w p ∧ far P u₁ u₂ w p = v))
          (q := fun p => decide (endAt w p)) (fun x _ hx => by simp only [decide_eq_true_eq] at hx ⊢; exact hx.1)
        rw [← hpec] at this
        omega
      rw [this]
      split_ifs <;> omega
    · rw [if_neg (fun hc => h0 hc.1)]
      obtain ⟨p, hp, hwp⟩ : ∃ p ∈ P, endAt w p := by
        have : 0 < P.countP (isEnd w) := by rw [← pathEndCount_eq_countP_isEnd]; omega
        obtain ⟨p, hp, hpe⟩ := List.countP_pos_iff.1 this
        exact ⟨p, hp, isEnd_iff.1 hpe⟩
      obtain ⟨p₀, hf₀, hp₀, hw₀⟩ := find_some hp hwp
      rcases hv with rfl | rfl
      · -- only the first path gets `u₁ w`
        have hle : P.countP (fun p => endAt w p ∧ far P u₁ u₂ w p = u₁ w) ≤ P.count p₀ := by
          rw [List.count_eq_countP]
          refine List.countP_mono_left fun x _ hx => ?_
          simp only [decide_eq_true_eq] at hx
          have := (far_eq_u₁_iff hu x).1 hx.2
          rw [hf₀] at this
          simp [Option.some.inj this]
        have := List.nodup_iff_count_le_one.1 h.nodup p₀
        omega
      · -- the other paths get `u₂ w`; there is at most one
        have hsplit := countP_and_add_countP_and_not P (fun p => endAt w p) (fun p => p = p₀)
        have hge : 1 ≤ P.countP (fun p => endAt w p ∧ p = p₀) :=
          List.countP_pos_iff.2 ⟨p₀, hp₀, by simp [hw₀]⟩
        have hle : P.countP (fun p => endAt w p ∧ far P u₁ u₂ w p = u₂ w) ≤
            P.countP (fun p => endAt w p ∧ ¬ p = p₀) := by
          refine List.countP_mono_left fun x _ hx => ?_
          simp only [decide_eq_true_eq] at hx ⊢
          refine ⟨hx.1, fun e => ?_⟩
          have := (far_eq_u₂_iff hu x).1 hx.2
          rw [hf₀, e] at this
          exact this rfl
        have := h.pec2 w
        rw [hpec] at this
        omega
  · rw [if_neg hv]
    have h1 : P.countP (fun p => endAt w p ∧ far P u₁ u₂ w p = v) = 0 := by
      rw [List.countP_eq_zero]
      intro p _ hp
      simp only [decide_eq_true_eq] at hp
      rcases far_mem (P := P) (u₁ := u₁) (u₂ := u₂) w p with e | e <;> rw [e] at hp
      · exact hv (Or.inl hp.2.symm)
      · exact hv (Or.inr hp.2.symm)
    have h2 : ¬ (pathEndCount P w = 0 ∧ (u₁ w = v ∨ u₂ w = v)) := by
      rintro ⟨_, e | e⟩
      · exact hv (Or.inl e.symm)
      · exact hv (Or.inr e.symm)
    rw [h1, if_neg h2]

end Hyp

end PVStep

end EG
