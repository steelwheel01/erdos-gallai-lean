module

public import EG.Lib.Vortex.StepPhase

/-!
# One phase of a PV step: the reserved edges are used exactly once (manuscript s4:lemPV, proof,
step (iv))

Unit P4A, stage 3. For the construction of `EG/Lib/Vortex/StepPhase.lean`: the appended edges of
distinct paths are distinct, and together with the single edges (`w` an end of exactly one path)
and the cherries (`w` an end of no path) they are exactly the reserved edges, each once
(`EG.PVStep.Hyp.resE_nodup`, `EG.PVStep.Hyp.mem_resE`). Also generic counting lemmas on lists.
-/

public section

namespace EG

namespace PVStep

open List

variable {V : Type*} [DecidableEq V]

/-! ## Generic counting -/

theorem countP_and_add_countP_and_not {α : Type*} (l : List α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] :
    l.countP (fun x => p x ∧ q x) + l.countP (fun x => p x ∧ ¬ q x) = l.countP p := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.countP_cons]
    split_ifs <;> simp_all <;> omega

theorem card_le_countP {α : Type*} [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p]
    (S : Finset α) (hS : ∀ x ∈ S, x ∈ l ∧ p x) : S.card ≤ l.countP p := by
  have hsub : S ⊆ (l.filter p).toFinset := by
    intro x hx
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨(hS x hx).1, by simpa using (hS x hx).2⟩
  calc S.card ≤ (l.filter p).toFinset.card := Finset.card_le_card hsub
    _ ≤ (l.filter p).length := List.toFinset_card_le _
    _ = l.countP p := (List.countP_eq_length_filter).symm

theorem sum_map_ite_eq_countP {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map fun x => if p x then 1 else 0).sum = l.countP p := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases hp : p x <;> simp [hp] <;> omega

theorem sum_map_finset_sum {α ι : Type*} (l : List α) (S : Finset ι) (f : ι → α → ℕ) :
    (l.map fun x => ∑ i ∈ S, f i x).sum = ∑ i ∈ S, (l.map (f i)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [Finset.sum_add_distrib]

theorem sum_map_le {α : Type*} (l : List α) (f g : α → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x (List.mem_cons_self ..)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

/-- A list without an element is empty. -/
theorem eq_nil_of_forall_not_mem {α : Type*} {l : List α} (h : ∀ x, x ∉ l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l => exact absurd (List.mem_cons_self ..) (h a)

/-! ## The first path ending at `w` -/

section Hyp

variable {W Rt Up : Finset V} {F : Finset (Sym2 V)} {P : List (List V)} {u₁ u₂ : V → V}
  (h : Hyp Rt W Up F P u₁ u₂)
include h

omit h in
theorem find_some {w : V} {p : List V} (hp : p ∈ P) (hw : endAt w p) :
    ∃ p₀, P.find? (isEnd w) = some p₀ ∧ p₀ ∈ P ∧ endAt w p₀ := by
  cases e : P.find? (isEnd w) with
  | none =>
    rw [List.find?_eq_none] at e
    exact absurd (isEnd_iff.2 hw) (e p hp)
  | some p₀ =>
    exact ⟨p₀, rfl, List.mem_of_find?_eq_some e, isEnd_iff.1 (List.find?_some e)⟩

omit h in
theorem pec_pos {w : V} {p : List V} (hp : p ∈ P) (hw : endAt w p) :
    1 ≤ pathEndCount P w := by
  rw [pathEndCount_eq_countP_isEnd]
  exact List.countP_pos_iff.2 ⟨p, hp, isEnd_iff.2 hw⟩

omit h in
theorem pec_two {w : V} {p p' : List V} (hp : p ∈ P) (hp' : p' ∈ P) (hne : p ≠ p')
    (hw : endAt w p) (hw' : endAt w p') : 2 ≤ pathEndCount P w := by
  have := card_le_countP P (endAt w) {p, p'} (by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hp, hw⟩
    · exact ⟨hp', hw'⟩)
  rw [Finset.card_pair hne] at this
  exact this

omit h in
theorem pec_three {w : V} {p p' p'' : List V} (hp : p ∈ P) (hp' : p' ∈ P) (hp'' : p'' ∈ P)
    (h1 : p ≠ p') (h2 : p ≠ p'') (h3 : p' ≠ p'')
    (hw : endAt w p) (hw' : endAt w p') (hw'' : endAt w p'') : 3 ≤ pathEndCount P w := by
  have := card_le_countP P (endAt w) {p, p', p''} (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hp, hw⟩
    · exact ⟨hp', hw'⟩
    · exact ⟨hp'', hw''⟩)
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3] at this
  exact this

/-- The appended edges of distinct paths are distinct. -/
theorem Hyp.appE_disjoint {p p' : List V} (hp : p ∈ P) (hp' : p' ∈ P) (hne : p ≠ p') :
    List.Disjoint (appE W P u₁ u₂ p) (appE W P u₁ u₂ p') := by
  intro e he he'
  obtain ⟨w, hw, hwp, rfl⟩ := (h.mem_appE hp).1 he
  obtain ⟨w', hw', hwp', he'⟩ := (h.mem_appE hp').1 he'
  obtain ⟨rfl, hf⟩ := sym2_W hw hw' (h.far_notW hw p) (h.far_notW hw' p') he'
  have hu := (h.res w hw).1
  obtain ⟨p₀, hf₀, hp₀, hw₀⟩ := find_some hp hwp
  by_cases h0 : p₀ = p
  · subst h0
    have e1 := (far_eq_u₁_iff hu p₀).2 hf₀
    have e2 := (far_eq_u₂_iff hu p').2 (by rw [hf₀]; exact fun e => hne (Option.some.inj e))
    exact hu (e1.symm.trans (hf.trans e2))
  by_cases h0' : p₀ = p'
  · subst h0'
    have e1 := (far_eq_u₁_iff hu p₀).2 hf₀
    have e2 := (far_eq_u₂_iff hu p).2 (by rw [hf₀]; exact fun e => h0 (Option.some.inj e))
    exact hu (e1.symm.trans (hf.symm.trans e2))
  · have := pec_three hp₀ hp hp' h0 h0' hne hw₀ hwp hwp'
    have := h.pec2 w
    omega

/-! ## The reserved edges -/

variable (W P u₁ u₂) in
/-- The reserved edges output as single edges: `w u₂(w)` for `w` an end of exactly one path. -/
@[expose] noncomputable def singlesE : List (Sym2 V) :=
  W.toList.flatMap fun w => if pathEndCount P w = 1 then [s(w, u₂ w)] else []

variable (W P u₁ u₂) in
/-- The edges of the cherries `u₁(w) w u₂(w)`, `w` an end of no path. -/
@[expose] noncomputable def cherryE : List (Sym2 V) :=
  W.toList.flatMap fun w => if pathEndCount P w = 0 then walkEdges [u₁ w, w, u₂ w] else []

omit h in
theorem mem_singlesE {e : Sym2 V} :
    e ∈ singlesE W P u₂ ↔ ∃ w ∈ W, pathEndCount P w = 1 ∧ e = s(w, u₂ w) := by
  unfold singlesE
  simp only [List.mem_flatMap, Finset.mem_toList]
  constructor
  · rintro ⟨w, hw, he⟩
    split_ifs at he with h1
    · exact ⟨w, hw, h1, List.mem_singleton.1 he⟩
    · simp at he
  · rintro ⟨w, hw, h1, rfl⟩
    exact ⟨w, hw, by simp [h1]⟩

omit h in
theorem mem_cherryE {e : Sym2 V} :
    e ∈ cherryE W P u₁ u₂ ↔
      ∃ w ∈ W, pathEndCount P w = 0 ∧ (e = s(w, u₁ w) ∨ e = s(w, u₂ w)) := by
  unfold cherryE
  simp only [List.mem_flatMap, Finset.mem_toList]
  constructor
  · rintro ⟨w, hw, he⟩
    split_ifs at he with h0
    · refine ⟨w, hw, h0, ?_⟩
      simp only [walkEdges_cons_cons, walkEdges_singleton, List.mem_cons, List.not_mem_nil,
        or_false] at he
      rcases he with rfl | rfl
      · exact Or.inl (Sym2.eq_swap)
      · exact Or.inr rfl
    · simp at he
  · rintro ⟨w, hw, h0, he⟩
    refine ⟨w, hw, ?_⟩
    simp only [h0, if_true, walkEdges_cons_cons, walkEdges_singleton, List.mem_cons,
      List.not_mem_nil, or_false]
    rcases he with rfl | rfl
    · exact Or.inl Sym2.eq_swap
    · exact Or.inr rfl

variable (W P u₁ u₂) in
/-- All reserved edges as used by the construction. -/
@[expose] noncomputable def resE : List (Sym2 V) :=
  P.flatMap (appE W P u₁ u₂) ++ singlesE W P u₂ ++ cherryE W P u₁ u₂

theorem Hyp.mem_resE {e : Sym2 V} :
    e ∈ resE W P u₁ u₂ ↔ ∃ w ∈ W, e = s(w, u₁ w) ∨ e = s(w, u₂ w) := by
  unfold resE
  simp only [List.mem_append, List.mem_flatMap, mem_singlesE, mem_cherryE]
  constructor
  · rintro ((⟨p, hp, he⟩ | ⟨w, hw, _, rfl⟩) | ⟨w, hw, _, he⟩)
    · obtain ⟨w, hw, _, rfl⟩ := (h.mem_appE hp).1 he
      refine ⟨w, hw, ?_⟩
      rcases far_mem (P := P) (u₁ := u₁) (u₂ := u₂) w p with e | e <;> rw [e] <;> simp
    · exact ⟨w, hw, Or.inr rfl⟩
    · exact ⟨w, hw, he⟩
  · rintro ⟨w, hw, he⟩
    have hu := (h.res w hw).1
    by_cases h0 : pathEndCount P w = 0
    · exact Or.inr ⟨w, hw, h0, he⟩
    -- `w` is an end of a path; the first one gets `u₁ w`
    obtain ⟨p, hp, hwp⟩ : ∃ p ∈ P, endAt w p := by
      have : 0 < P.countP (isEnd w) := by rw [← pathEndCount_eq_countP_isEnd]; omega
      obtain ⟨p, hp, hpe⟩ := List.countP_pos_iff.1 this
      exact ⟨p, hp, isEnd_iff.1 hpe⟩
    obtain ⟨p₀, hf₀, hp₀, hw₀⟩ := find_some hp hwp
    rcases he with rfl | rfl
    · refine Or.inl (Or.inl ⟨p₀, hp₀, (h.mem_appE hp₀).2 ⟨w, hw, hw₀, ?_⟩⟩)
      rw [(far_eq_u₁_iff hu p₀).2 hf₀]
    · by_cases h1 : pathEndCount P w = 1
      · exact Or.inl (Or.inr ⟨w, hw, h1, rfl⟩)
      -- a second path ends at `w`
      obtain ⟨p', hp', hwp', hne⟩ : ∃ p' ∈ P, endAt w p' ∧ p' ≠ p₀ := by
        by_contra hcon
        have hle : P.countP (isEnd w) ≤ P.count p₀ := by
          rw [List.count_eq_countP]
          refine List.countP_mono_left fun x hx hxe => ?_
          have : x = p₀ := by
            by_contra hne
            exact hcon ⟨x, hx, isEnd_iff.1 hxe, hne⟩
          simp [this]
        have := List.nodup_iff_count_le_one.1 h.nodup p₀
        rw [← pathEndCount_eq_countP_isEnd] at hle
        omega
      refine Or.inl (Or.inl ⟨p', hp', (h.mem_appE hp').2 ⟨w, hw, hwp', ?_⟩⟩)
      rw [(far_eq_u₂_iff hu p').2 (by rw [hf₀]; exact fun e => hne (Option.some.inj e).symm)]

theorem Hyp.u₁_notW {w : V} (hw : w ∈ W) : u₁ w ∉ W := h.notW_of_RU (h.res w hw).2.1

theorem Hyp.u₂_notW {w : V} (hw : w ∈ W) : u₂ w ∉ W := h.notW_of_RU (h.res w hw).2.2.1

theorem Hyp.resE_nodup : (resE W P u₁ u₂).Nodup := by
  unfold resE
  have hWnd := Finset.nodup_toList W
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- the appended edges
    rw [List.nodup_flatMap]
    exact ⟨fun p hp => h.appE_nodup hp,
      h.nodup.pairwise_of_forall_ne fun p hp p' hp' hne => h.appE_disjoint hp hp' hne⟩
  · -- the single edges
    unfold singlesE
    rw [List.nodup_flatMap]
    refine ⟨fun w _ => by split_ifs <;> simp, hWnd.pairwise_of_forall_ne ?_⟩
    intro w hw w' hw' hne e he he'
    simp only [Finset.mem_toList] at hw hw'
    dsimp only at he he'
    split_ifs at he he' <;> simp only [List.mem_singleton, List.not_mem_nil] at he he'
    subst he
    exact hne (sym2_W hw hw' (h.u₂_notW hw) (h.u₂_notW hw') he').1
  · -- appended edges and single edges
    intro e he e' he' hee
    subst hee
    rw [List.mem_flatMap] at he
    obtain ⟨p, hp, he⟩ := he
    obtain ⟨w, hw, hwp, rfl⟩ := (h.mem_appE hp).1 he
    obtain ⟨w', hw', h1, he'⟩ := mem_singlesE.1 he'
    obtain ⟨rfl, hf⟩ := sym2_W hw hw' (h.far_notW hw p) (h.u₂_notW hw') he'
    obtain ⟨p₀, hf₀, hp₀, hw₀⟩ := find_some hp hwp
    have hne : p₀ ≠ p := by
      rintro rfl
      exact (h.res w hw).1 (((far_eq_u₁_iff (h.res w hw).1 p₀).2 hf₀).symm.trans hf)
    have := pec_two hp₀ hp hne hw₀ hwp
    omega
  · -- the cherries
    unfold cherryE
    rw [List.nodup_flatMap]
    refine ⟨fun w hw => ?_, hWnd.pairwise_of_forall_ne ?_⟩
    · simp only [Finset.mem_toList] at hw
      split_ifs
      · refine nodup_walkEdges ?_
        have hu := (h.res w hw).1
        have h1 : u₁ w ≠ w := fun e => h.u₁_notW hw (by rw [e]; exact hw)
        have h2 : w ≠ u₂ w := fun e => h.u₂_notW hw (by rw [← e]; exact hw)
        simp [h1, h2, hu]
      · simp
    · intro w hw w' hw' hne e he he'
      simp only [Finset.mem_toList] at hw hw'
      have key : ∀ x ∈ W, ∀ e ∈ (if pathEndCount P x = 0 then walkEdges [u₁ x, x, u₂ x] else []),
          e = s(x, u₁ x) ∨ e = s(x, u₂ x) := by
        intro x _ e he
        split_ifs at he
        · simp only [walkEdges_cons_cons, walkEdges_singleton, List.mem_cons, List.not_mem_nil,
            or_false] at he
          rcases he with rfl | rfl
          · exact Or.inl Sym2.eq_swap
          · exact Or.inr rfl
        · simp at he
      rcases key w hw e he with rfl | rfl <;> rcases key w' hw' _ he' with e2 | e2
      all_goals first
        | exact hne (sym2_W hw hw' (h.u₁_notW hw) (h.u₁_notW hw') e2).1
        | exact hne (sym2_W hw hw' (h.u₁_notW hw) (h.u₂_notW hw') e2).1
        | exact hne (sym2_W hw hw' (h.u₂_notW hw) (h.u₁_notW hw') e2).1
        | exact hne (sym2_W hw hw' (h.u₂_notW hw) (h.u₂_notW hw') e2).1
  · -- appended and single edges against the cherries
    intro e he e' he' hee
    subst hee
    obtain ⟨w', hw', h0, he'⟩ := mem_cherryE.1 he'
    have hx' : ∀ {x}, (e = s(w', x)) → x ∉ W → ∀ w ∈ W, ∀ y ∉ W, e = s(w, y) → w = w' := by
      intro x hex hx w hw y hy hey
      exact (sym2_W hw hw' hy hx (hey.symm.trans hex)).1
    have hx'' : ∃ x ∉ W, e = s(w', x) := by
      rcases he' with he' | he'
      · exact ⟨_, h.u₁_notW hw', he'⟩
      · exact ⟨_, h.u₂_notW hw', he'⟩
    obtain ⟨x, hx, hex⟩ := hx''
    rcases List.mem_append.1 he with he | he
    · obtain ⟨p, hp, he⟩ := List.mem_flatMap.1 he
      obtain ⟨w, hw, hwp, hew⟩ := (h.mem_appE hp).1 he
      have := hx' hex hx w hw _ (h.far_notW hw p) hew
      subst this
      have := pec_pos hp hwp
      omega
    · obtain ⟨w, hw, h1, hew⟩ := mem_singlesE.1 he
      have := hx' hex hx w hw _ (h.u₂_notW hw) hew
      subst this
      omega

end Hyp

end PVStep

end EG
