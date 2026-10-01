module

public import EG.Lib.Quot.Junction

/-!
# Step (e2) and the junctions of all ends (manuscript s7:consRound (e); s7:lemWellDef (v)) —
probe P-1, stage 3

* `E'(u)` has at most `deg_J(u) ≤ M_l − 1` ends ([s7:lemWellDef] (v) proof: "The elements of `E'(u)`
  correspond to further live items at `u`");
* an (e2) junction is a candidate of the port outside `Used(u)`; (e2) junctions at one port are
  pairwise distinct; under validity every end of `E'(u)` receives one;
* the junction of any end is a candidate of its port, junctions at one port are pairwise distinct
  ("The ends at `u` have pairwise distinct junctions: in (e1) every chosen junction is added to
  `Used(u)` and is excluded later, and in (e2) the map is injective into `Cand_l(u) \ Used(u)`"),
  and under validity every end of a coloured hub item or of a PAR object has a junction.
-/

public section

namespace EG.Quot

open Finset

variable {V : Type*} [DecidableEq V] {I : RoundInput V} {R : Rules I}

namespace Rules

theorem mem_E' {L : Lists I.G I.M} {u : V} {e : REnd V} :
    e ∈ R.E' L u ↔ (∃ o ∈ R.parObjs, ∃ b, o.endAt b = u ∧ e = REnd.par o b) ∨
      (∃ it ∈ R.colouredHub L, it.2 = u ∧ I.ultra it.1 ∧ e = REnd.hub it.1 it.2) := by
  classical
  unfold E'
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨o, ho, b, hb, rfl⟩ | ⟨it, ⟨hit, h1, h2⟩, rfl⟩)
    · exact Or.inl ⟨o, ho, b, hb, rfl⟩
    · exact Or.inr ⟨it, hit, h1, h2, rfl⟩
  · rintro (⟨o, ho, b, hb, rfl⟩ | ⟨it, hit, h1, h2, rfl⟩)
    · exact Or.inl ⟨o, ho, b, hb, rfl⟩
    · exact Or.inr ⟨it, ⟨hit, h1, h2⟩, rfl⟩

theorem port_of_mem_E' {L : Lists I.G I.M} {u : V} {e : REnd V} (he : e ∈ R.E' L u) :
    e.port = u := by
  rcases (mem_E').1 he with ⟨o, -, b, hb, rfl⟩ | ⟨it, -, h1, -, rfl⟩
  · exact hb
  · exact h1

/-- An (e2) junction is a candidate of the port, outside `Used(u)`. -/
theorem e2Junc_mem {ξ : Xi I.G I.M} {e : REnd V} {w : V} (h : R.e2Junc ξ e = some w) :
    w ∈ I.cand e.port \ R.used ξ.1 e.port := by
  unfold e2Junc at h
  split at h
  · cases h
  · have hw := List.mem_of_getElem? h
    by_cases hu : e.port ∈ I.G.verts
    · exact ((mem_inOrder hu _ w).1 hw).1
    · simp [inOrder, hu] at hw

/-- (e2) junctions at one port are pairwise distinct. -/
theorem e2Junc_inj {ξ : Xi I.G I.M} {e e' : REnd V} (hne : e ≠ e') (hp : e.port = e'.port)
    {w : V} (h : R.e2Junc ξ e = some w) (h' : R.e2Junc ξ e' = some w) : False := by
  unfold e2Junc at h h'
  rw [← hp] at h'
  split at h
  · cases h
  · rename_i i hi
    split at h'
    · cases h'
    · rename_i j hj
      have hi' := List.idxOf?_eq_some_iff.1 hi
      have hj' := List.idxOf?_eq_some_iff.1 hj
      by_cases hij : i = j
      · subst hij
        obtain ⟨_, hi1, -⟩ := hi'
        obtain ⟨_, hj1, -⟩ := hj'
        exact hne (hi1.symm.trans hj1)
      · have hnd := nodup_inOrder ξ.2 e.port (I.cand e.port \ R.used ξ.1 e.port)
        obtain ⟨hi2, hi3⟩ := List.getElem?_eq_some_iff.1 h
        obtain ⟨hj2, hj3⟩ := List.getElem?_eq_some_iff.1 h'
        exact hij ((hnd.getElem_inj_iff (hi := hi2) (hj := hj2)).1 (hi3.trans hj3.symm))

/-- The junction of any end is a candidate of its port. -/
theorem junction_mem_cand {ξ : Xi I.G I.M} {en : REnd V} {w : V}
    (h : R.junction ξ en = some w) : w ∈ I.cand en.port := by
  classical
  cases en with
  | par o b => exact (Finset.mem_sdiff.1 (e2Junc_mem h)).1
  | hub hh u =>
    simp only [junction] at h
    split_ifs at h
    · exact (Finset.mem_sdiff.1 (e2Junc_mem h)).1
    · exact e1_junc_cand h

theorem mem_cand {u w : V} (h : w ∈ I.cand u) :
    w ∈ I.pool ∧ I.poolRound w = (I.cls u).1 ∧ s(u, w) ∈ I.ljv (I.cls u) := by
  unfold RoundInput.cand at h
  rw [Finset.mem_filter] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem junction_pool {ξ : Xi I.G I.M} {en : REnd V} {w : V} (h : R.junction ξ en = some w) :
    w ∈ I.pool :=
  (mem_cand (junction_mem_cand h)).1

/-- Junctions at one port are pairwise distinct. -/
theorem junction_inj {ξ : Xi I.G I.M} {en en' : REnd V} (hp : en.port = en'.port) {w : V}
    (h : R.junction ξ en = some w) (h' : R.junction ξ en' = some w) : en = en' := by
  classical
  by_contra hne
  have e2e1 : ∀ (e : REnd V) (it : V × V), e.port = it.2 → R.e2Junc ξ e = some w →
      (R.e1State ξ.1).junc it = some w → False := by
    intro e it hp' h1 h2
    have := (Finset.mem_sdiff.1 (e2Junc_mem h1)).2
    rw [hp'] at this
    exact this (e1_junc_used h2)
  cases en with
  | par o b =>
    cases en' with
    | par o' b' => exact e2Junc_inj hne hp h h'
    | hub hh' u' =>
      simp only [junction] at h h'
      split_ifs at h'
      · exact e2Junc_inj hne hp h h'
      · exact e2e1 _ (hh', u') hp h h'
  | hub hh u =>
    cases en' with
    | par o' b' =>
      simp only [junction] at h h'
      split_ifs at h
      · exact e2Junc_inj hne hp h h'
      · exact e2e1 _ (hh, u) hp.symm h' h
    | hub hh' u' =>
      simp only [junction] at h h'
      split_ifs at h h'
      · exact e2Junc_inj hne hp h h'
      · exact e2e1 _ (hh', u') hp h h'
      · exact e2e1 _ (hh, u) hp.symm h' h
      · simp only [REnd.port] at hp
        have hinv := e1Inv_e1State (R := R) ξ.1
        unfold E1Inv at hinv
        exact hinv.2.1 (hh, u) (hh', u') w
          (fun e => hne (by cases e; rfl)) hp h h'

variable (hI : I.Valid) (hR : R.Valid)
include hI hR

/-- `|E'(u)| ≤ deg_J(u)`. -/
theorem card_E'_le (L : Lists I.G I.M) (u : V) : (R.E' L u).card ≤ degE I.J u := by
  classical
  unfold degE edgesAt
  refine Finset.card_le_card_of_injOn (fun e => match e with
    | REnd.par o b => o.jAt b
    | REnd.hub h u => s(h, u)) ?_ ?_
  · intro e he
    rw [Finset.mem_coe] at he
    rw [Finset.mem_coe, Finset.mem_filter]
    rcases (mem_E').1 he with ⟨o, ho, b, hb, rfl⟩ | ⟨it, hit, h1, -, rfl⟩
    · exact ⟨RoundInput.live_mem_J ((parObj_facts hI hR ho).1 b),
        hb ▸ ParObj.endAt_mem_jAt o b⟩
    · have hH := ((mem_colouredHub).1 hit).1
      exact ⟨RoundInput.Jhub_sub_J (RoundInput.hubItems_Jhub hH), h1 ▸ Sym2.mem_mk_right _ _⟩
  · intro e he e' he' heq
    rw [Finset.mem_coe] at he he'
    rcases (mem_E').1 he with ⟨o, ho, b, hb, rfl⟩ | ⟨it, hit, h1, -, rfl⟩ <;>
      rcases (mem_E').1 he' with ⟨o', ho', b', hb', rfl⟩ | ⟨it', hit', h1', -, rfl⟩
    · simp only at heq
      have := parObj_eq_of_jAt hI hR ho ho' heq
      subst this
      rw [parObj_end_inj hI hR ho (hb.trans hb'.symm)]
    · exfalso
      simp only at heq
      have hH := ((mem_colouredHub).1 hit').1
      rcases (parObj_facts hI hR ho).2.1 b with h | h
      · exact RoundInput.Jhub_not_Jpar hI (heq ▸ RoundInput.hubItems_Jhub hH) h
      · exact RoundInput.Jhub_not_Jfr hI (heq ▸ RoundInput.hubItems_Jhub hH) h
    · exfalso
      simp only at heq
      have hH := ((mem_colouredHub).1 hit).1
      rcases (parObj_facts hI hR ho').2.1 b' with h | h
      · exact RoundInput.Jhub_not_Jpar hI (heq.symm ▸ RoundInput.hubItems_Jhub hH) h
      · exact RoundInput.Jhub_not_Jfr hI (heq.symm ▸ RoundInput.hubItems_Jhub hH) h
    · simp only at heq
      have := RoundInput.hubItems_edge_inj ((mem_colouredHub).1 hit).1
        ((mem_colouredHub).1 hit').1 hI heq
      rw [this]

theorem card_E'_lt (L : Lists I.G I.M) {u : V} (hu : u ∈ I.ports) : (R.E' L u).card < I.M := by
  have h1 := card_E'_le hI hR L u
  have h2 := hI.J2 u (RoundInput.port_not_hub hI hu)
  have h3 : 1 ≤ I.M := le_trans (by norm_num) hI.M_ge
  omega

/-- [s7:lemWellDef] (v), the chain of inequalities, at a port carrying a live item. -/
theorem wellDefE2_ineqs (ξ : Xi I.G I.M) {u : V} (hu : u ∈ I.ports) (hlive : ∃ e ∈ I.live, u ∈ e) :
    I.Hcd - ((I.M : ℝ) - 1) ≤ ((I.cand u \ R.used ξ.1 u).card : ℝ) ∧
      I.Hcd / 2 ≤ I.Hcd - ((I.M : ℝ) - 1) ∧ (I.M : ℝ) ≤ I.Hcd / 2 ∧ (R.E' ξ.1 u).card < I.M := by
  obtain ⟨e, he, hue⟩ := hlive
  have hcand := RoundInput.Hcd_le_cand_of_live hI he hue hu
  have hused := card_used_le hI hR ξ.1 hu
  have hM1 : 1 ≤ I.M := le_trans (by norm_num) hI.M_ge
  have hsd : (I.cand u).card ≤ (I.cand u \ R.used ξ.1 u).card + (R.used ξ.1 u).card :=
    Finset.card_le_card_sdiff_add_card
  have hused' : ((R.used ξ.1 u).card : ℝ) ≤ (I.M : ℝ) - 1 := by
    have h3 : ((I.M - 1 : ℕ) : ℝ) = (I.M : ℝ) - 1 := by rw [Nat.cast_sub hM1]; simp
    rw [← h3]; exact_mod_cast hused
  have hsd' : ((I.cand u).card : ℝ) ≤ (I.cand u \ R.used ξ.1 u).card + (R.used ξ.1 u).card := by
    exact_mod_cast hsd
  have hHcd := hI.Hcd_ge
  have hM : (1 : ℝ) ≤ I.M := by exact_mod_cast hM1
  have hM10 : 2 * (I.M : ℝ) ≤ (2 : ℝ) ^ 10 * (I.M : ℝ) ^ 10 := by
    have h1 : (I.M : ℝ) ≤ (I.M : ℝ) ^ 10 := by
      calc (I.M : ℝ) = (I.M : ℝ) ^ 1 := by ring
        _ ≤ (I.M : ℝ) ^ 10 := pow_le_pow_right₀ hM (by norm_num)
    nlinarith
  refine ⟨by linarith, by linarith, by linarith, card_E'_lt hI hR ξ.1 hu⟩

/-- [s7:lemWellDef] (v) "so step (e2) is well defined": every end of `E'(u)` receives an (e2)
junction in `Cand_l(u) \ Used(u)`. -/
theorem e2Junc_some (ξ : Xi I.G I.M) {u : V} (hu : u ∈ I.ports) (hlive : ∃ e ∈ I.live, u ∈ e)
    {e : REnd V} (he : e ∈ R.E' ξ.1 u) : ∃ w, R.e2Junc ξ e = some w ∧ w ∈ I.cand u \ R.used ξ.1 u
    := by
  obtain ⟨h1, h2, h3, h4⟩ := wellDefE2_ineqs hI hR ξ hu hlive
  have hport := port_of_mem_E' he
  have hmem : e ∈ R.e2Order ξ.1 u := by
    rw [← List.mem_toFinset, (hR.e2Order ξ.1 u).2]; exact he
  have hlen : (R.e2Order ξ.1 u).length = (R.E' ξ.1 u).card := by
    rw [← List.toFinset_card_of_nodup (hR.e2Order ξ.1 u).1, (hR.e2Order ξ.1 u).2]
  have huG : u ∈ I.G.verts := hI.ports_sub hu
  have hsubG : I.cand u \ R.used ξ.1 u ⊆ I.G.verts := fun w hw =>
    hI.pool_sub (mem_cand (Finset.mem_sdiff.1 hw).1).1
  have hlen2 := length_inOrder (O := ξ.2) huG hsubG
  have hlt : (R.e2Order ξ.1 u).idxOf e < (inOrder ξ.2 u (I.cand u \ R.used ξ.1 u)).length := by
    have := List.idxOf_lt_length_of_mem hmem
    rw [hlen2]
    have hc : (R.E' ξ.1 u).card < (I.cand u \ R.used ξ.1 u).card := by
      have : ((R.E' ξ.1 u).card : ℝ) < ((I.cand u \ R.used ξ.1 u).card : ℝ) := by
        have : ((R.E' ξ.1 u).card : ℝ) < I.M := by exact_mod_cast h4
        linarith
      exact_mod_cast this
    omega
  refine ⟨(inOrder ξ.2 u (I.cand u \ R.used ξ.1 u))[(R.e2Order ξ.1 u).idxOf e], ?_, ?_⟩
  · unfold e2Junc
    rw [hport]
    have hidx : (R.e2Order ξ.1 u).idxOf? e = some ((R.e2Order ξ.1 u).idxOf e) := by
      rw [List.idxOf?_eq_some_iff]
      refine ⟨List.idxOf_lt_length_of_mem hmem, List.getElem_idxOf _, fun j hj hje => ?_⟩
      have hj' : j < (R.e2Order ξ.1 u).length := by
        have := List.idxOf_lt_length_of_mem hmem; omega
      have := (hR.e2Order ξ.1 u).1.idxOf_getElem j hj'
      rw [hje] at this
      omega
    rw [hidx]
    simp only
    exact List.getElem?_eq_getElem hlt
  · have hm := List.getElem_mem hlt
    exact ((mem_inOrder huG _ _).1 hm).1

/-- Every end of a PAR object has a junction. -/
theorem junction_par_some (ξ : Xi I.G I.M) {o : ParObj V} (ho : o ∈ R.parObjs) (b : Bool) :
    ∃ w, R.junction ξ (.par o b) = some w := by
  have hu := parObj_end_port hI hR ho b
  obtain ⟨w, hw, -⟩ := e2Junc_some hI hR ξ hu (parObj_end_live hI hR ho b)
    ((mem_E').2 (Or.inl ⟨o, ho, b, rfl, rfl⟩))
  exact ⟨w, hw⟩

/-- Every coloured hub item has a junction. -/
theorem junction_hub_some (ξ : Xi I.G I.M) {it : V × V} (hit : it ∈ R.colouredHub ξ.1) :
    ∃ w, R.junction ξ (.hub it.1 it.2) = some w := by
  classical
  have hH := ((mem_colouredHub).1 hit).1
  simp only [junction]
  split_ifs with hu
  · obtain ⟨w, hw, -⟩ := e2Junc_some hI hR ξ (RoundInput.hubItems_port hH)
      ⟨_, RoundInput.hubItems_live hI hH, Sym2.mem_mk_right _ _⟩
      ((mem_E').2 (Or.inr ⟨it, hit, rfl, hu, rfl⟩))
    exact ⟨w, hw⟩
  · have hit' : it ∈ R.e1Items ξ.1 := by
      unfold e1Items; exact Finset.mem_filter.2 ⟨hit, hu⟩
    exact e1_junc_some hI hR ξ.1 hit'

end Rules

end EG.Quot
