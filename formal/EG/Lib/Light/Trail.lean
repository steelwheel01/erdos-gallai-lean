module

public import EG.Defs.Probe.P4B.Trail
public import EG.Defs.Objects
public import EG.Defs.Walk

/-!
# Closed trails of oriented arcs: basic lemmas (s5:lemParent, Steps 3–5)

Library for probe unit P4B (probe P-4, part 2), proof round 1. Lemmas on `EG.MTrail`
(`EG/Defs/Probe/P4B/Trail.lean`): the transitions of a cyclic list of oriented edges, their
projections, and the quotient endpoint map. Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG.MTrail

variable {ι N β : Type*}

theorem oSrc_qEnds (par : N → β) (ends : ι → N × N) (p : ι × Bool) :
    oSrc (qEnds par ends) p = par (oSrc ends p) := by
  unfold oSrc qEnds; split <;> rfl

theorem oTgt_qEnds (par : N → β) (ends : ι → N × N) (p : ι × Bool) :
    oTgt (qEnds par ends) p = par (oTgt ends p) := by
  unfold oTgt qEnds; split <;> rfl

/-- The two ends of an oriented edge are the two ends of its edge. -/
theorem oTgt_oSrc_iff (ends : ι → N × N) (p : ι × Bool) (v : N) :
    (oTgt ends p = v ∨ oSrc ends p = v) ↔ ((ends p.1).1 = v ∨ (ends p.1).2 = v) := by
  unfold oTgt oSrc; split <;> tauto

theorem oTgt_mem_ends (ends : ι → N × N) (p : ι × Bool) :
    oTgt ends p = (ends p.1).1 ∨ oTgt ends p = (ends p.1).2 := by
  unfold oTgt; split <;> simp

theorem oSrc_mem_ends (ends : ι → N × N) (p : ι × Bool) :
    oSrc ends p = (ends p.1).1 ∨ oSrc ends p = (ends p.1).2 := by
  unfold oSrc; split <;> simp

/-- If the two ends of the edge are distinct, so are the start and the end of the oriented edge. -/
theorem oTgt_ne_oSrc (ends : ι → N × N) (p : ι × Bool) (h : (ends p.1).1 ≠ (ends p.1).2) :
    oTgt ends p ≠ oSrc ends p := by
  unfold oTgt oSrc; split <;> simpa [eq_comm] using h

theorem transitions_qEnds (par : N → β) (ends : ι → N × N) (W : List (ι × Bool)) :
    transitions (qEnds par ends) W = (transitions ends W).map fun t => (par t.1, par t.2) := by
  unfold transitions
  rw [List.map_zipWith]
  simp only [oTgt_qEnds, oSrc_qEnds]

theorem length_transitions (ends : ι → N × N) (W : List (ι × Bool)) :
    (transitions ends W).length = W.length := by
  simp [transitions]

/-- Membership in the transitions: the pair `(v_j^+, v_{j+1}^-)` for a position `j`. -/
theorem mem_transitions {ends : ι → N × N} {W : List (ι × Bool)} {t : N × N} :
    t ∈ transitions ends W ↔ ∃ (j : ℕ) (hj : j < W.length),
      t = (oTgt ends W[j], oSrc ends (W[(j + 1) % W.length]'(Nat.mod_lt _ (by omega)))) := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < W.length := by simpa [transitions] using hj
    refine ⟨j, hj', ?_⟩
    simp only [transitions, List.getElem_zipWith, List.getElem_rotate]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j, by simpa [transitions] using hj, ?_⟩
    simp only [transitions, List.getElem_zipWith, List.getElem_rotate]

private theorem map_fst_zipWith_pair {α γ δ ε : Type*} (g : α → δ) (h : γ → ε) (l1 : List α)
    (l2 : List γ) (hl : l1.length = l2.length) :
    (List.zipWith (fun p q => (g p, h q)) l1 l2).map Prod.fst = l1.map g ∧
      (List.zipWith (fun p q => (g p, h q)) l1 l2).map Prod.snd = l2.map h := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a l ih =>
    cases l2 with
    | nil => simp at hl
    | cons b l2 =>
      simp only [List.length_cons, add_left_inj] at hl
      simp [(ih l2 hl).1, (ih l2 hl).2]

theorem map_fst_transitions (ends : ι → N × N) (W : List (ι × Bool)) :
    (transitions ends W).map Prod.fst = W.map (oTgt ends) :=
  (map_fst_zipWith_pair (oTgt ends) (oSrc ends) W (W.rotate 1) (by simp)).1

theorem map_snd_transitions (ends : ι → N × N) (W : List (ι × Bool)) :
    (transitions ends W).map Prod.snd = (W.rotate 1).map (oSrc ends) :=
  (map_fst_zipWith_pair (oTgt ends) (oSrc ends) W (W.rotate 1) (by simp)).2

theorem countP_or_add_countP_and {α : Type*} (p q : α → Bool) (l : List α) :
    l.countP (fun x => p x || q x) + l.countP (fun x => p x && q x) =
      l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.countP_cons]; cases p a <;> cases q a <;> simp <;> omega

/-- Step 5, first bullet, for one trail: the number of transitions containing `v` is at most the
number of arcs of the trail with an end `v` (the arcs having two distinct ends). -/
theorem countP_transitions_le [DecidableEq N] (ends : ι → N × N) (W : List (ι × Bool))
    (hW : ∀ p ∈ W, (ends p.1).1 ≠ (ends p.1).2) (v : N) :
    (transitions ends W).countP (fun t => t.1 = v ∨ t.2 = v) ≤
      (W.map Prod.fst).countP (fun a => (ends a).1 = v ∨ (ends a).2 = v) := by
  have h1 := countP_or_add_countP_and (fun t : N × N => decide (t.1 = v))
    (fun t => decide (t.2 = v)) (transitions ends W)
  have hA : (transitions ends W).countP (fun t => decide (t.1 = v)) =
      W.countP (fun p => decide (oTgt ends p = v)) := by
    have := congrArg (List.countP (fun x : N => decide (x = v))) (map_fst_transitions ends W)
    simpa [List.countP_map, Function.comp_def] using this
  have hB : (transitions ends W).countP (fun t => decide (t.2 = v)) =
      W.countP (fun p => decide (oSrc ends p = v)) := by
    have := congrArg (List.countP (fun x : N => decide (x = v))) (map_snd_transitions ends W)
    simp only [List.countP_map, Function.comp_def] at this
    rw [this]
    exact (List.rotate_perm W 1).countP_eq _
  have h2 := countP_or_add_countP_and (fun p : ι × Bool => decide (oTgt ends p = v))
    (fun p => decide (oSrc ends p = v)) W
  have hand : W.countP (fun p => decide (oTgt ends p = v) && decide (oSrc ends p = v)) = 0 := by
    rw [List.countP_eq_zero]
    intro p hp
    have := oTgt_ne_oSrc ends p (hW p hp)
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h1 h2; exact this (h1.trans h2.symm)
  have hor : W.countP (fun p => decide (oTgt ends p = v) || decide (oSrc ends p = v)) =
      (W.map Prod.fst).countP (fun a => (ends a).1 = v ∨ (ends a).2 = v) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro p _
    simp only [Bool.or_eq_true, decide_eq_true_eq, Function.comp_apply]
    exact oTgt_oSrc_iff ends p v
  have h3 : (transitions ends W).countP (fun t => decide (t.1 = v ∨ t.2 = v)) =
      (transitions ends W).countP (fun t => decide (t.1 = v) || decide (t.2 = v)) := by
    apply List.countP_congr; intro t _; simp
  rw [h3]
  omega

end EG.MTrail
