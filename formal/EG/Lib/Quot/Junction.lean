module

public import EG.Lib.Quot.Colour

/-!
# Junctions (manuscript s7:consRound (d), (e); s7:lemWellDef (iv), (v)) — probe P-1, stage 3

* HUB colours: the SDR colour of a coloured hub item lies in its list, so it is `< 4M_l`, and two
  coloured hub items at one port have different colours ((d): "every port carries at most one
  coloured hub item of each HUB colour");
* (e1): the invariants of the sequential step (`E1Inv`, unconditional): every assigned junction is
  a candidate of the port, lies in `Used(u)` and in `Used_κ(h)`; junctions at one port differ;
  junctions of one hub in one colour differ. Under validity, the step never fails
  ([s7:lemWellDef] (iv)) and `|Used(u)| ≤ M_l − 1`;
* (e2): `E'(u)` has at most `deg_J(u)` ends; an (e2) junction is a candidate of the port outside
  `Used(u)`; (e2) junctions at one port differ; under validity every end of `E'(u)` gets one
  ([s7:lemWellDef] (v));
* the junction of any end is a candidate of its port (hence pooled), and junctions at one port are
  pairwise distinct.
-/

public section

namespace EG.Quot

open Finset

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

namespace Rules

/-! ## HUB colours -/

theorem mem_colouredHub {L : Lists I.G I.M} {it : V × V} :
    it ∈ R.colouredHub L ↔ it ∈ I.hubItems ∧ R.SDRExists L it.2 := by
  classical
  unfold colouredHub
  rw [Finset.mem_filter]

theorem hubColour_of_coloured {L : Lists I.G I.M} {it : V × V} (h : it ∈ R.colouredHub L) :
    R.hubColour L it = some (R.sdr L it) := by
  classical
  unfold hubColour
  rw [if_pos ((mem_colouredHub).1 h)]

theorem hubColour_eq_some {L : Lists I.G I.M} {it : V × V} {κ : ℕ}
    (h : R.hubColour L it = some κ) : it ∈ R.colouredHub L ∧ R.sdr L it = κ := by
  classical
  unfold hubColour at h
  split_ifs at h with h'
  · exact ⟨(mem_colouredHub).2 h', Option.some.inj h⟩

theorem sdr_mem_hubList (hR : R.Valid) {L : Lists I.G I.M} {it : V × V}
    (h : it ∈ R.colouredHub L) : R.sdr L it ∈ R.hubList L it := by
  have h' := (mem_colouredHub).1 h
  exact (hR.sdr L it.2 h'.2).1 it ((I.mem_hubItemsAt).2 ⟨h'.1, rfl⟩)

theorem hubList_lt (L : Lists I.G I.M) (it : V × V) {c : ℕ} (hc : c ∈ R.hubList L it) :
    c < 4 * I.M := by
  classical
  unfold hubList at hc
  split_ifs at hc
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    exact a.2
  · exact lt_of_mem_listOf hc

/-- HUB colours are colours of `[4M_l]`. -/
theorem hubColour_lt (hR : R.Valid) {L : Lists I.G I.M} {it : V × V} {κ : ℕ}
    (h : R.hubColour L it = some κ) : κ < 4 * I.M := by
  obtain ⟨h1, rfl⟩ := hubColour_eq_some h
  exact hubList_lt L it (sdr_mem_hubList hR h1)

/-- (d) "every port carries at most one coloured hub item of each HUB colour". -/
theorem hub_eq_of_port_colour (hR : R.Valid) {L : Lists I.G I.M} {it it' : V × V}
    (h : it ∈ R.colouredHub L) (h' : it' ∈ R.colouredHub L) (hu : it.2 = it'.2)
    (hc : R.hubColour L it = R.hubColour L it') : it = it' := by
  rw [hubColour_of_coloured h, hubColour_of_coloured h', Option.some.injEq] at hc
  have hh := (mem_colouredHub).1 h
  have hh' := (mem_colouredHub).1 h'
  exact (hR.sdr L it.2 hh.2).2 ((I.mem_hubItemsAt).2 ⟨hh.1, rfl⟩)
    ((I.mem_hubItemsAt).2 ⟨hh'.1, hu.symm⟩) hc

/-- The items of a non-ultra hub `h` with the same colour lie in the same group. -/
theorem group_eq_of_colour (hR : R.Valid) {L : Lists I.G I.M} {it it' : V × V}
    (h : it ∈ R.colouredHub L) (h' : it' ∈ R.colouredHub L) (hh : it.1 = it'.1)
    (hnu : ¬ I.ultra it.1) (hc : R.hubColour L it = R.hubColour L it') :
    R.group it = R.group it' := by
  classical
  have m := sdr_mem_hubList hR h
  have m' := sdr_mem_hubList hR h'
  rw [hubColour_of_coloured h, hubColour_of_coloured h', Option.some.injEq] at hc
  unfold hubList at m m'
  rw [if_neg hnu] at m
  rw [if_neg (hh ▸ hnu)] at m'
  rw [← hh, ← hc] at m'
  by_contra hne
  exact Finset.disjoint_left.1 (disjoint_listOf _ hne) m m'

/-! ## (e1) -/

/-- The invariant of step (e1) (holds for every state reached, without validity). -/
@[expose] def E1Inv (R : Rules I) (L : Lists I.G I.M) (st : E1State V) : Prop :=
  (∀ it w, st.junc it = some w →
    w ∈ I.cand it.2 ∧ w ∈ st.used it.2 ∧ ∃ κ, R.hubColour L it = some κ ∧ w ∈ st.usedK it.1 κ) ∧
  (∀ it it' w, it ≠ it' → it.2 = it'.2 → st.junc it = some w → st.junc it' = some w → False) ∧
  (∀ it it' w, it ≠ it' → it.1 = it'.1 → R.hubColour L it = R.hubColour L it' →
    st.junc it = some w → st.junc it' = some w → False)

theorem e1Inv_init (L : Lists I.G I.M) : E1Inv R L ⟨fun _ => ∅, fun _ _ => ∅, fun _ => none⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem e1Step_eq (L : Lists I.G I.M) (st : E1State V) (it : V × V) :
    R.e1Step L st it = st ∨
    ∃ κ w, R.hubColour L it = some κ ∧ ¬ I.ultra it.1 ∧ w ∈ e1Free I st it κ ∧
      w ∈ R.vertOrder L ∧
      R.e1Step L st it =
        { used := Function.update st.used it.2 (insert w (st.used it.2))
          usedK := Function.update st.usedK it.1
            (Function.update (st.usedK it.1) κ (insert w (st.usedK it.1 κ)))
          junc := Function.update st.junc it (some w) } := by
  classical
  unfold e1Step
  rcases hc : R.hubColour L it with _ | κ
  · left; rfl
  · by_cases hu : I.ultra it.1
    · left; simp [hu]
    · rcases hf : (R.vertOrder L).find? (fun w => decide (w ∈ e1Free I st it κ)) with _ | w
      · left; simp [hu, hf]
      · right
        refine ⟨κ, w, rfl, hu, ?_, List.mem_of_find?_eq_some hf, ?_⟩
        · simpa using List.find?_some hf
        · simp [hu, hf]

theorem e1Step_of_found (L : Lists I.G I.M) (st : E1State V) {it : V × V} {κ : ℕ}
    (hκ : R.hubColour L it = some κ) (hnu : ¬ I.ultra it.1) {w : V}
    (hf : (R.vertOrder L).find? (fun w => decide (w ∈ e1Free I st it κ)) = some w) :
    R.e1Step L st it =
        { used := Function.update st.used it.2 (insert w (st.used it.2))
          usedK := Function.update st.usedK it.1
            (Function.update (st.usedK it.1) κ (insert w (st.usedK it.1 κ)))
          junc := Function.update st.junc it (some w) } := by
  classical
  unfold e1Step
  rw [hκ]
  simp only [hnu, if_false]
  rw [hf]

theorem e1Inv_step {L : Lists I.G I.M} {st : E1State V} (h : E1Inv R L st) (it : V × V) :
    E1Inv R L (R.e1Step L st it) := by
  rcases e1Step_eq L st it with hs | ⟨κ, w, hκ, -, hw, -, hs⟩
  · rw [hs]; exact h
  rw [hs]
  obtain ⟨h1, h2, h3⟩ := h
  simp only [e1Free, Finset.mem_sdiff] at hw
  obtain ⟨⟨hwc, hwu⟩, hwk⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · intro it' w' hj
    dsimp only at hj ⊢
    by_cases e : it' = it
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hj
      subst hj
      refine ⟨hwc, by simp, κ, hκ, by simp⟩
    · simp only [Function.update_of_ne e] at hj
      obtain ⟨a, b, κ', hκ', c⟩ := h1 it' w' hj
      refine ⟨a, ?_, κ', hκ', ?_⟩
      · by_cases hu : it'.2 = it.2
        · rw [hu]; simp only [Function.update_self]; exact Finset.mem_insert_of_mem (hu ▸ b)
        · rw [Function.update_of_ne hu]; exact b
      · by_cases hh : it'.1 = it.1
        · rw [hh]; simp only [Function.update_self]
          by_cases hk : κ' = κ
          · rw [hk]; simp only [Function.update_self]
            exact Finset.mem_insert_of_mem (hk ▸ hh ▸ c)
          · rw [Function.update_of_ne hk]; exact hh ▸ c
        · rw [Function.update_of_ne hh]; exact c
  · intro a b w' hab hp ha hb
    simp only at ha hb
    by_cases hai : a = it
    · subst hai
      rw [Function.update_of_ne (Ne.symm hab)] at hb
      simp only [Function.update_self, Option.some.injEq] at ha
      subst ha
      exact hwu (hp ▸ (h1 b w hb).2.1)
    · by_cases hbi : b = it
      · subst hbi
        rw [Function.update_of_ne hab] at ha
        simp only [Function.update_self, Option.some.injEq] at hb
        subst hb
        exact hwu (hp.symm ▸ (h1 a w ha).2.1)
      · rw [Function.update_of_ne hai] at ha
        rw [Function.update_of_ne hbi] at hb
        exact h2 a b w' hab hp ha hb
  · intro a b w' hab hh hc ha hb
    simp only at ha hb
    by_cases hai : a = it
    · subst hai
      rw [Function.update_of_ne (Ne.symm hab)] at hb
      simp only [Function.update_self, Option.some.injEq] at ha
      subst ha
      obtain ⟨-, -, κ', hκ', hk⟩ := h1 b w hb
      rw [← hc, hκ] at hκ'
      cases hκ'
      exact hwk (hh ▸ hk)
    · by_cases hbi : b = it
      · subst hbi
        rw [Function.update_of_ne hab] at ha
        simp only [Function.update_self, Option.some.injEq] at hb
        subst hb
        obtain ⟨-, -, κ', hκ', hk⟩ := h1 a w ha
        rw [hc, hκ] at hκ'
        cases hκ'
        exact hwk (hh.symm ▸ hk)
      · rw [Function.update_of_ne hai] at ha
        rw [Function.update_of_ne hbi] at hb
        exact h3 a b w' hab hh hc ha hb

theorem e1Inv_foldl (L : Lists I.G I.M) :
    ∀ (l : List (V × V)) (st : E1State V), E1Inv R L st → E1Inv R L (l.foldl (R.e1Step L) st)
  | [], _, h => h
  | it :: l, st, h => e1Inv_foldl L l _ (e1Inv_step h it)

theorem e1Inv_e1State (L : Lists I.G I.M) : E1Inv R L (R.e1State L) :=
  e1Inv_foldl L _ _ (e1Inv_init L)

/-- An (e1) junction is a candidate of its port. -/
theorem e1_junc_cand {L : Lists I.G I.M} {it : V × V} {w : V}
    (h : (R.e1State L).junc it = some w) : w ∈ I.cand it.2 :=
  ((e1Inv_e1State L).1 it w h).1

theorem e1_junc_used {L : Lists I.G I.M} {it : V × V} {w : V}
    (h : (R.e1State L).junc it = some w) : w ∈ R.used L it.2 :=
  ((e1Inv_e1State L).1 it w h).2.1

/-- The size invariant of (e1) along a duplicate-free processing order of coloured hub items. -/
@[expose] def E1Size (R : Rules I) (L : Lists I.G I.M) (st : E1State V) (l : List (V × V)) : Prop :=
  (∀ u, (st.used u).card ≤ (l.toFinset.filter (fun it => it.2 = u)).card) ∧
  (∀ h κ, (st.usedK h κ).card ≤
    (l.toFinset.filter (fun it => it.1 = h ∧ R.hubColour L it = some κ)).card) ∧
  (∀ it ∈ l, ∃ w, st.junc it = some w)

variable (hI : I.Valid) (hR : R.Valid)
include hI hR

theorem e1Items_sub {L : Lists I.G I.M} {it : V × V} (h : it ∈ R.e1Items L) :
    it ∈ R.colouredHub L ∧ ¬ I.ultra it.1 := by
  classical
  unfold e1Items at h
  exact Finset.mem_filter.1 h

theorem e1Size_step {L : Lists I.G I.M} {st : E1State V} {l : List (V × V)}
    (hsz : E1Size R L st l) {it : V × V} (hit : it ∈ R.e1Items L) (hl : it ∉ l)
    (hsub : ∀ x ∈ l, x ∈ R.e1Items L) : E1Size R L (R.e1Step L st it) (l ++ [it]) := by
  classical
  obtain ⟨hcol, hnu⟩ := e1Items_sub hI hR hit
  have hitH := ((mem_colouredHub).1 hcol).1
  set κ := R.sdr L it with hκdef
  have hκ : R.hubColour L it = some κ := hubColour_of_coloured hcol
  obtain ⟨hu, hk, hj⟩ := hsz
  -- the free set is nonempty
  have hfree : (e1Free I st it κ).Nonempty := by
    have hcand : I.Hcd ≤ ((I.cand it.2).card : ℝ) :=
      RoundInput.Hcd_le_cand_of_live hI (RoundInput.hubItems_live hI hitH)
        (Sym2.mem_mk_right _ _) (RoundInput.hubItems_port hitH)
    have hused : (st.used it.2).card + 1 ≤ I.M - 1 := by
      refine le_trans ?_ (RoundInput.card_hubItemsAt_le_M hI (RoundInput.hubItems_port hitH))
      refine le_trans (Nat.add_le_add_right (hu it.2) 1) ?_
      rw [← Finset.card_insert_of_notMem (s := l.toFinset.filter (fun x => x.2 = it.2))
        (a := it) (by simp [hl])]
      refine Finset.card_le_card fun x hx => ?_
      rw [Finset.mem_insert, Finset.mem_filter, List.mem_toFinset] at hx
      rw [I.mem_hubItemsAt]
      rcases hx with rfl | ⟨hx, hx2⟩
      · exact ⟨hitH, rfl⟩
      · exact ⟨((mem_colouredHub).1 (e1Items_sub hI hR (hsub x hx)).1).1, hx2⟩
    have hK : (st.usedK it.1 κ).card + 1 ≤ I.groupCap := by
      refine le_trans (Nat.add_le_add_right (hk it.1 κ) 1) ?_
      rw [← Finset.card_insert_of_notMem
        (s := l.toFinset.filter (fun x => x.1 = it.1 ∧ R.hubColour L x = some κ))
        (a := it) (by simp [hl])]
      refine le_trans (Finset.card_le_card (t := I.hubItems.filter
        (fun x => x.1 = it.1 ∧ R.group x = R.group it)) fun x hx => ?_)
        ((hR.group it.1 hnu).2 (R.group it))
      rw [Finset.mem_insert, Finset.mem_filter, List.mem_toFinset] at hx
      rw [Finset.mem_filter]
      rcases hx with rfl | ⟨hx, hx1, hx2⟩
      · exact ⟨hitH, rfl, rfl⟩
      · have hxc := (e1Items_sub hI hR (hsub x hx)).1
        refine ⟨((mem_colouredHub).1 hxc).1, hx1, ?_⟩
        exact (group_eq_of_colour hR hcol hxc hx1.symm hnu (by rw [hκ, hx2])).symm
    have hM : (2 : ℝ) ^ 40 ≤ I.M := by exact_mod_cast hI.M_ge
    have hHcd := hI.Hcd_ge
    have hgc : (I.groupCap : ℝ) < I.Hcd / 8 + 1 := Nat.ceil_lt_add_one (by
      have : (0 : ℝ) < I.Hcd := lt_of_lt_of_le (by positivity) hHcd
      positivity)
    have hM1 : 1 ≤ I.M := le_trans (by norm_num) hI.M_ge
    have hcard : (I.cand it.2).card ≤ (I.cand it.2 \ st.used it.2).card + (st.used it.2).card :=
      Finset.card_le_card_sdiff_add_card
    have hcard2 : (I.cand it.2 \ st.used it.2).card ≤ (e1Free I st it κ).card +
        (st.usedK it.1 κ).card := Finset.card_le_card_sdiff_add_card
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty] at hcard2
    have hc : (I.cand it.2).card ≤ (st.used it.2).card + (st.usedK it.1 κ).card := by omega
    have hc' : ((I.cand it.2).card : ℝ) ≤ ((st.used it.2).card : ℝ) + (st.usedK it.1 κ).card := by
      exact_mod_cast hc
    have hu' : ((st.used it.2).card : ℝ) + 1 ≤ (I.M : ℝ) - 1 := by
      have h3 : ((I.M - 1 : ℕ) : ℝ) = (I.M : ℝ) - 1 := by
        rw [Nat.cast_sub hM1]; simp
      rw [← h3]; exact_mod_cast hused
    have hk' : ((st.usedK it.1 κ).card : ℝ) + 1 ≤ I.groupCap := by exact_mod_cast hK
    have hM10 : 8 * (I.M : ℝ) ≤ (2 : ℝ) ^ 10 * (I.M : ℝ) ^ 10 := by
      have : (1 : ℝ) ≤ I.M := by exact_mod_cast hM1
      have h1 : (I.M : ℝ) ≤ (I.M : ℝ) ^ 10 := by
        calc (I.M : ℝ) = (I.M : ℝ) ^ 1 := by ring
          _ ≤ (I.M : ℝ) ^ 10 := pow_le_pow_right₀ this (by norm_num)
      nlinarith
    linarith
  obtain ⟨w0, hw0⟩ := hfree
  have hvert : ∀ w ∈ e1Free I st it κ, w ∈ R.vertOrder L := by
    intro w hw
    rw [← List.mem_toFinset, (hR.vertOrder L).2]
    simp only [e1Free, Finset.mem_sdiff] at hw
    exact hI.pool_sub (Finset.mem_filter.1 hw.1.1).1
  have hfind : ((R.vertOrder L).find? (fun w => decide (w ∈ e1Free I st it κ))).isSome := by
    rw [List.find?_isSome]
    exact ⟨w0, hvert w0 hw0, by simpa using hw0⟩
  obtain ⟨w, hwf⟩ := Option.isSome_iff_exists.1 hfind
  have hs := e1Step_of_found L st hκ hnu hwf
  · rw [hs]
    refine ⟨?_, ?_, ?_⟩
    · intro u
      dsimp only
      by_cases h' : u = it.2
      · subst h'
        simp only [Function.update_self]
        refine (Finset.card_insert_le _ _).trans ?_
        refine le_trans (Nat.add_le_add_right (hu it.2) 1) (le_of_eq ?_)
        rw [List.toFinset_append, Finset.filter_union, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.filter_singleton, if_pos rfl, Finset.card_union_of_disjoint]
        · simp
        · simp [hl]
      · rw [Function.update_of_ne h']
        refine (hu u).trans (Finset.card_le_card ?_)
        intro x hx
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append] at hx ⊢
        exact ⟨Or.inl hx.1, hx.2⟩
    · intro h κ''
      dsimp only
      by_cases h' : h = it.1
      · subst h'
        simp only [Function.update_self]
        by_cases hk' : κ'' = κ
        · rw [hk', Function.update_self]
          refine (Finset.card_insert_le _ _).trans ?_
          refine le_trans (Nat.add_le_add_right (hk it.1 κ) 1) (le_of_eq ?_)
          rw [List.toFinset_append, Finset.filter_union, List.toFinset_cons, List.toFinset_nil,
            insert_empty_eq, Finset.filter_singleton, if_pos ⟨rfl, hκ⟩,
            Finset.card_union_of_disjoint]
          · simp
          · simp [hl]
        · rw [Function.update_of_ne hk']
          refine (hk _ _).trans (Finset.card_le_card ?_)
          intro x hx
          simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append] at hx ⊢
          exact ⟨Or.inl hx.1, hx.2⟩
      · rw [Function.update_of_ne h']
        refine (hk _ _).trans (Finset.card_le_card ?_)
        intro x hx
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append] at hx ⊢
        exact ⟨Or.inl hx.1, hx.2⟩
    · intro x hx
      by_cases e : x = it
      · subst e; exact ⟨w, by simp⟩
      · rw [List.mem_append, List.mem_singleton] at hx
        obtain ⟨w', hw'⟩ := hj x (hx.resolve_right e)
        exact ⟨w', by simp [Function.update_of_ne e, hw']⟩

theorem e1Size_foldl (L : Lists I.G I.M) : ∀ l : List (V × V), l.Nodup →
    (∀ x ∈ l, x ∈ R.e1Items L) →
    E1Size R L (l.foldl (R.e1Step L) ⟨fun _ => ∅, fun _ _ => ∅, fun _ => none⟩) l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ _; refine ⟨?_, ?_, ?_⟩ <;> simp
  | append_singleton l it ih =>
    intro hnd hsub
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hnd' := List.nodup_append.1 hnd
    exact e1Size_step hI hR (ih hnd'.1 (fun x h => hsub x (List.mem_append_left _ h)))
      (hsub it (by simp)) (fun h => hnd'.2.2 it h it (by simp) rfl)
      (fun x h => hsub x (List.mem_append_left _ h))

theorem e1Size_e1State (L : Lists I.G I.M) : E1Size R L (R.e1State L) (R.e1Order L) :=
  e1Size_foldl hI hR L _ (hR.e1Order L).1 (fun x h => by
    rw [← (hR.e1Order L).2]; exact List.mem_toFinset.2 h)

/-- [s7:lemWellDef] (iv) "Step (e1) always finds a junction". -/
theorem e1_junc_some (L : Lists I.G I.M) {it : V × V} (hit : it ∈ R.e1Items L) :
    ∃ w, (R.e1State L).junc it = some w :=
  (e1Size_e1State hI hR L).2.2 it (by rw [← List.mem_toFinset, (hR.e1Order L).2]; exact hit)

/-- After (e1), `|Used(u)| ≤ |hub items at u| ≤ M_l − 1` at a port. -/
theorem card_used_le (L : Lists I.G I.M) {u : V} (hu : u ∈ I.ports) :
    (R.used L u).card ≤ I.M - 1 := by
  classical
  refine ((e1Size_e1State hI hR L).1 u).trans ?_
  refine le_trans (Finset.card_le_card ?_) (RoundInput.card_hubItemsAt_le_M hI hu)
  intro x hx
  rw [Finset.mem_filter, (hR.e1Order L).2] at hx
  exact (I.mem_hubItemsAt).2 ⟨((mem_colouredHub).1 (e1Items_sub hI hR hx.1).1).1, hx.2⟩

end Rules

end EG.Quot
