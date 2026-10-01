module

public import EG.Lib.Quot.Items

/-!
# The greedy PAR colouring of (b) (manuscript s7:lemWellDef (i)) — probe P-1, stage 3

[s7:lemWellDef] (i), proof: "A PAR object has at most two ports and at most one middle. Each of
its ports carries at most `M_l−2` further live items, and each further PAR object at that port uses
one of them. Its middle, if any, is the middle of at most `(M_l−1)/2−1` further cherries. So the
object conflicts with at most `2(M_l−2)+(M_l−1)/2<3M_l` others. When it is coloured, fewer than
`3M_l` colours are therefore blocked, and a colour of `[3M_l]` remains. The consequences are the
defining property of the colouring."

We use the cruder count `3(M_l − 1) < 3M_l` (each of the three classes — objects with an end at
either port, cherries with the same middle — has at most `M_l − 1` members, the object itself
included), which is all the statement needs.
-/

public section

namespace EG.Quot

open Finset

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

namespace Rules

variable (hI : I.Valid) (hR : R.Valid)
include hI hR

/-- [s7:lemWellDef] (i) "Every PAR object shares a port or a middle with fewer than `3M_l` other
PAR objects". -/
theorem card_conflicts_lt {o : ParObj V} (ho : o ∈ R.parObjs) :
    (open Classical in (R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o')).card <
      3 * I.M := by
  classical
  have hM : 1 ≤ I.M := le_trans (by norm_num) hI.M_ge
  set A : V → Finset (ParObj V) := fun u => R.parObjs.filter (fun o' => ∃ b, o'.endAt b = u)
  set B : Finset (ParObj V) :=
    R.parObjs.filter (fun o' => ∃ x, o.middle = some x ∧ o'.middle = some x)
  have hB : B.card ≤ I.M - 1 := by
    rcases hm : o.middle with _ | x
    · rw [Finset.card_eq_zero.2]
      · exact Nat.zero_le _
      · rw [Finset.filter_eq_empty_iff]
        rintro o' - ⟨x, hx, -⟩
        rw [hm] at hx; cases hx
    · refine le_trans (Finset.card_le_card ?_) (card_parObjs_middle_le_M hI hR x)
      intro o' ho'
      rw [Finset.mem_filter] at ho' ⊢
      obtain ⟨y, hy, hy'⟩ := ho'.2
      rw [hm, Option.some.injEq] at hy
      exact ⟨ho'.1, hy ▸ hy'⟩
  have hsub : (R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o') ⊆
      A (o.endAt false) ∪ A (o.endAt true) ∪ B := by
    intro o' ho'
    rw [Finset.mem_filter, Finset.mem_erase] at ho'
    obtain ⟨⟨-, ho'P⟩, hc⟩ := ho'
    rcases hc with ⟨b, b', hbb⟩ | hmid
    · cases b
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.2 ⟨ho'P, b', hbb.symm⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨ho'P, b', hbb.symm⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨ho'P, hmid⟩)
  have h1 : (A (o.endAt false)).card ≤ I.M - 1 :=
    card_parObjs_end_le_M hI hR (parObj_end_port hI hR ho false)
  have h2 : (A (o.endAt true)).card ≤ I.M - 1 :=
    card_parObjs_end_le_M hI hR (parObj_end_port hI hR ho true)
  calc _ ≤ (A (o.endAt false) ∪ A (o.endAt true) ∪ B).card := by
        convert Finset.card_le_card hsub
    _ ≤ (A (o.endAt false)).card + (A (o.endAt true)).card + B.card := by
        refine (Finset.card_union_le _ _).trans ?_
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (I.M - 1) + (I.M - 1) + (I.M - 1) := by omega
    _ < 3 * I.M := by omega

omit hR in
/-- The colour chosen in one greedy step exists (fewer than `3M` colours are blocked). -/
theorem find_colour_isSome (hR : R.Valid) (col : ParObj V → Option ℕ) {o : ParObj V}
    (ho : o ∈ R.parObjs) :
    ∃ c, (open Classical in (List.range (3 * I.M)).find? (fun c =>
      decide (∀ o' ∈ R.parObjs, o' ≠ o → ParObj.Conflict o o' → col o' ≠ some c))) = some c := by
  classical
  rw [← Option.isSome_iff_exists, List.find?_isSome]
  by_contra hne
  have hsub : Finset.range (3 * I.M) ⊆
      ((R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o')).biUnion
        (fun o' => (col o').toFinset) := by
    intro c hc
    have : ¬ (∀ o' ∈ R.parObjs, o' ≠ o → ParObj.Conflict o o' → col o' ≠ some c) :=
      fun h => hne ⟨c, List.mem_range.2 (Finset.mem_range.1 hc), decide_eq_true h⟩
    simp only [not_forall, not_not] at this
    obtain ⟨o', ho', hne', hc', hcol⟩ := this
    exact Finset.mem_biUnion.2 ⟨o', Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hne', ho'⟩, hc'⟩,
      by simp [hcol]⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := (R.parObjs.erase o).filter
    (fun o' => ParObj.Conflict o o')) (t := fun o' => (col o').toFinset)
  have h3 : ∑ o' ∈ (R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o'),
      (col o').toFinset.card ≤ ((R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o')).card
      := by
    calc _ ≤ ∑ _o' ∈ (R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o'), 1 :=
          Finset.sum_le_sum fun o' _ => by cases col o' <;> simp
      _ = _ := by simp
  have h4 := card_conflicts_lt hI hR ho
  rw [Finset.card_range] at h1
  have : ((R.parObjs.erase o).filter (fun o' => ParObj.Conflict o o')).card < 3 * I.M := by
    convert h4
  omega

/-- The invariant of the greedy colouring after processing the list `l`. -/
@[expose] def ColInv (R : Rules I) (col : ParObj V → Option ℕ) (l : List (ParObj V)) : Prop :=
  (∀ o κ, col o = some κ → κ < 3 * I.M) ∧
  (∀ o ∈ R.parObjs, ∀ o' ∈ R.parObjs, o ≠ o' → ParObj.Conflict o o' →
      ∀ κ, col o = some κ → col o' = some κ → False) ∧
  (∀ o, o ∉ l → col o = none) ∧
  (∀ o ∈ l, col o ≠ none)

omit hI hR in
theorem colInv_nil : ColInv R (fun _ => none) [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem colInv_step {col : ParObj V → Option ℕ} {l : List (ParObj V)} (hinv : ColInv R col l)
    {o : ParObj V} (ho : o ∈ R.parObjs) (hol : o ∉ l) :
    ColInv R (R.colourStep col o) (l ++ [o]) := by
  classical
  obtain ⟨c, hc⟩ := find_colour_isSome hI hR col ho
  have hcP := List.find?_some hc
  have hcr : c < 3 * I.M := List.mem_range.1 (List.mem_of_find?_eq_some hc)
  simp only [decide_eq_true_eq] at hcP
  have hstep : R.colourStep col o = Function.update col o (some c) := by
    unfold colourStep
    rw [hc]
  rw [hstep]
  obtain ⟨hb, hp, hn, hs⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o' κ h
    by_cases h' : o' = o
    · subst h'; simp at h; exact h ▸ hcr
    · rw [Function.update_of_ne h'] at h; exact hb o' κ h
  · intro a ha b hb' hab hconf κ h1 h2
    by_cases hao : a = o
    · subst hao
      rw [Function.update_of_ne (Ne.symm hab)] at h2
      simp only [Function.update_self, Option.some.injEq] at h1
      subst h1
      exact hcP b hb' (Ne.symm hab) hconf h2
    · by_cases hbo : b = o
      · subst hbo
        rw [Function.update_of_ne hab] at h1
        simp only [Function.update_self, Option.some.injEq] at h2
        subst h2
        exact hcP a ha hab hconf.symm h1
      · rw [Function.update_of_ne hao] at h1
        rw [Function.update_of_ne hbo] at h2
        exact hp a ha b hb' hab hconf κ h1 h2
  · intro o' ho'
    have hne : o' ≠ o := fun h => ho' (by simp [h])
    rw [Function.update_of_ne hne]
    exact hn o' (fun h => ho' (List.mem_append_left _ h))
  · intro o' ho'
    by_cases h' : o' = o
    · subst h'; simp
    · rw [Function.update_of_ne h']
      exact hs o' ((List.mem_append.1 ho').resolve_right (by simpa using h'))

theorem colInv_foldl : ∀ l : List (ParObj V), l.Nodup → (∀ o ∈ l, o ∈ R.parObjs) →
    ColInv R (l.foldl R.colourStep (fun _ => none)) l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ _; exact colInv_nil
  | append_singleton l o ih =>
    intro hnd hsub
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hnd' := List.nodup_append.1 hnd
    exact colInv_step hI hR (ih hnd'.1 (fun o' h => hsub o' (List.mem_append_left _ h)))
      (hsub o (by simp)) (fun h => hnd'.2.2 o h o (by simp) rfl)

theorem colInv_parColour : ColInv R R.parColour R.parOrder :=
  colInv_foldl hI hR R.parOrder hR.parOrder.1 (fun o h => by
    rw [← hR.parOrder.2]; exact List.mem_toFinset.2 h)

/-- [s7:lemWellDef] (i) "the greedy colouring of (b) succeeds": every PAR object receives a colour
of `[3M_l]`. -/
theorem parColour_some {o : ParObj V} (ho : o ∈ R.parObjs) :
    ∃ κ, κ < 3 * I.M ∧ R.parColour o = some κ := by
  have hinv := colInv_parColour hI hR
  have hol : o ∈ R.parOrder := by
    rw [← List.mem_toFinset, hR.parOrder.2]; exact ho
  obtain ⟨κ, hκ⟩ := Option.ne_none_iff_exists'.1 (hinv.2.2.2 o hol)
  exact ⟨κ, hinv.1 o κ hκ, hκ⟩

/-- Conflicting PAR objects receive different colours. -/
theorem parColour_proper {o o' : ParObj V} (ho : o ∈ R.parObjs) (ho' : o' ∈ R.parObjs)
    (hne : o ≠ o') (hc : ParObj.Conflict o o') {κ : ℕ} (h1 : R.parColour o = some κ)
    (h2 : R.parColour o' = some κ) : False :=
  (colInv_parColour hI hR).2.1 o ho o' ho' hne hc κ h1 h2

omit hI hR in
/-- Colours of the greedy colouring are always `< 3M` (no validity needed). -/
theorem parColour_lt' (hI : I.Valid) (hR : R.Valid) {o : ParObj V} {κ : ℕ}
    (h : R.parColour o = some κ) : κ < 3 * I.M :=
  (colInv_parColour hI hR).1 o κ h

/-- [s7:lemWellDef] (i) "every port carries at most one PAR object of each colour" (at every
vertex). -/
theorem card_parObjs_end_colour_le (u : V) (κ : ℕ) :
    (R.parObjs.filter (fun o => (∃ b, o.endAt b = u) ∧ R.parColour o = some κ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  by_contra hne
  obtain ⟨ba, hba⟩ := ha.2.1
  obtain ⟨bb, hbb⟩ := hb.2.1
  exact parColour_proper hI hR ha.1 hb.1 hne (Or.inl ⟨ba, bb, hba.trans hbb.symm⟩) ha.2.2 hb.2.2

/-- [s7:lemWellDef] (i) "every fresh centre is the middle of at most one cherry of each colour" (at
every vertex). -/
theorem card_parObjs_middle_colour_le (x : V) (κ : ℕ) :
    (R.parObjs.filter (fun o => o.middle = some x ∧ R.parColour o = some κ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  by_contra hne
  exact parColour_proper hI hR ha.1 hb.1 hne (Or.inr ⟨x, ha.2.1, hb.2.1⟩) ha.2.2 hb.2.2

/-- Two PAR objects of the same colour with an end at the same vertex are equal. -/
theorem parObj_eq_of_end_colour {o o' : ParObj V} (ho : o ∈ R.parObjs) (ho' : o' ∈ R.parObjs)
    {b b' : Bool} (he : o.endAt b = o'.endAt b') {κ : ℕ} (h1 : R.parColour o = some κ)
    (h2 : R.parColour o' = some κ) : o = o' := by
  by_contra hne
  exact parColour_proper hI hR ho ho' hne (Or.inl ⟨b, b', he⟩) h1 h2

/-- Two PAR objects of the same colour with the same middle are equal. -/
theorem parObj_eq_of_middle_colour {o o' : ParObj V} (ho : o ∈ R.parObjs)
    (ho' : o' ∈ R.parObjs) {x : V} (hm : o.middle = some x) (hm' : o'.middle = some x) {κ : ℕ}
    (h1 : R.parColour o = some κ) (h2 : R.parColour o' = some κ) : o = o' := by
  by_contra hne
  exact parColour_proper hI hR ho ho' hne (Or.inr ⟨x, hm, hm'⟩) h1 h2

end Rules

end EG.Quot
