module

public import EG.Lib.Vortex.Ends

/-!
# One phase of a PV step: appending reserved edges (manuscript s4:lemPV, proof, steps (iv)–(vi))

Unit P4A, stage 3. The construction of step (iv) of the proof of Lemma PV for one phase:
every path `p` of the Corollary-22 decomposition `P` gets, at each of its ends `w ∈ W`, one of the
two reserved edges `w u₁(w)`, `w u₂(w)`: the first path of `P` (in list order) ending at `w` gets
`u₁(w)`, the other one (there are at most two) gets `u₂(w)` (`EG.PVStep.far`). The resulting walk
is `EG.PVStep.trail p`; its edges are those of `p` and the appended edges `EG.PVStep.appE p`.

This file: the definitions and the facts about a single trail.
-/

public section

namespace EG

namespace PVStep

open List

variable {V : Type*} [DecidableEq V]

section Defs

variable (W : Finset V) (P : List (List V)) (u₁ u₂ : V → V)

/-- `w` is an end of `q` (Boolean form, for `List.find?`). -/
@[expose] def isEnd (w : V) (q : List V) : Bool := decide (endAt w q)

/-- The far end of the reserved edge appended to the path `p` at its end `w`: `u₁ w` for the first
path of `P` ending at `w`, `u₂ w` otherwise. -/
@[expose] def far (w : V) (p : List V) : V :=
  if P.find? (isEnd w) = some p then u₁ w else u₂ w

/-- The vertex appended at the end `a` of `p` (none if `a ∉ W`). -/
@[expose] def extV (p : List V) (a : V) : List V :=
  if a ∈ W then [far P u₁ u₂ a p] else []

/-- The edge appended at the end `a` of `p` (none if `a ∉ W`). -/
@[expose] def extE (p : List V) (a : V) : List (Sym2 V) :=
  if a ∈ W then [s(a, far P u₁ u₂ a p)] else []

/-- The trail of step (iv): `p` with the reserved edges appended at its ends in `W`. -/
@[expose] def trail (p : List V) : List V :=
  (p.head?.map (extV W P u₁ u₂ p)).getD [] ++ p ++ (p.getLast?.map (extV W P u₁ u₂ p)).getD []

/-- The appended edges of `p`. -/
@[expose] def appE (p : List V) : List (Sym2 V) :=
  (p.head?.map (extE W P u₁ u₂ p)).getD [] ++ (p.getLast?.map (extE W P u₁ u₂ p)).getD []

end Defs

variable {W : Finset V} {P : List (List V)} {u₁ u₂ : V → V}

theorem isEnd_iff {w : V} {q : List V} : isEnd w q = true ↔ endAt w q := by
  simp [isEnd]

theorem pathEndCount_eq_countP_isEnd (w : V) : pathEndCount P w = P.countP (isEnd w) := rfl

theorem far_mem (w : V) (p : List V) : far P u₁ u₂ w p = u₁ w ∨ far P u₁ u₂ w p = u₂ w := by
  unfold far
  split_ifs <;> simp

theorem far_eq_u₁_iff {w : V} (h : u₁ w ≠ u₂ w) (p : List V) :
    far P u₁ u₂ w p = u₁ w ↔ P.find? (isEnd w) = some p := by
  unfold far
  split_ifs with hp
  · exact ⟨fun _ => hp, fun _ => rfl⟩
  · exact ⟨fun e => absurd e.symm h, fun e => absurd e hp⟩

theorem far_eq_u₂_iff {w : V} (h : u₁ w ≠ u₂ w) (p : List V) :
    far P u₁ u₂ w p = u₂ w ↔ P.find? (isEnd w) ≠ some p := by
  unfold far
  split_ifs with hp
  · exact ⟨fun e => absurd e h, fun e => absurd hp e⟩
  · exact ⟨fun _ => hp, fun _ => rfl⟩

omit [DecidableEq V] in
/-- A decomposition into paths has no repeated path. -/
theorem nodup_of_isPathDecomp {F : Set (Sym2 V)} (hP : IsPathDecomp F P) : P.Nodup := by
  have h := (List.nodup_flatMap.1 hP.2.1).2
  refine h.imp_of_mem ?_
  intro a b ha _ hab heq
  subst heq
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (l := a) (by have := hP.two_le_length ha; omega)
  obtain ⟨e, he, _⟩ := exists_mem_walkEdges_of_mem (hP.two_le_length ha) hx
  exact hab he he

/-- The hypotheses of `EG.Spec.PVStepPhaseStatement`. -/
structure Hyp (Rt W Up : Finset V) (F : Finset (Sym2 V)) (P : List (List V)) (u₁ u₂ : V → V) :
    Prop where
  dRW : Disjoint Rt W
  dRU : Disjoint Rt Up
  dWU : Disjoint W Up
  loop : ∀ e ∈ F, ¬ e.IsDiag
  ends : ∀ e ∈ F, ∀ v ∈ e, v ∈ Rt ∪ W ∪ Up
  meet : ∀ e ∈ F, ∃ w ∈ W, w ∈ e
  dec : IsPathDecomp (F : Set (Sym2 V)) P
  pec2 : ∀ v, pathEndCount P v ≤ 2
  res : ∀ w ∈ W, u₁ w ≠ u₂ w ∧ u₁ w ∈ Rt ∪ Up ∧ u₂ w ∈ Rt ∪ Up ∧ s(w, u₁ w) ∉ F ∧ s(w, u₂ w) ∉ F

omit [DecidableEq V] in
/-- An edge `s(w, x)` with `w ∈ W`, `x ∉ W` determines `w` and `x`. -/
theorem sym2_W {W : Finset V} {w w' x x' : V} (hw : w ∈ W) (_hw' : w' ∈ W) (_hx : x ∉ W)
    (hx' : x' ∉ W) (h : s(w, x) = s(w', x')) : w = w' ∧ x = x' := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · subst h1; exact absurd hw hx'

section Hyp

variable {Rt Up : Finset V} {F : Finset (Sym2 V)} (h : Hyp Rt W Up F P u₁ u₂)
include h

theorem Hyp.u_mem {w : V} (hw : w ∈ W) (p : List V) : far P u₁ u₂ w p ∈ Rt ∪ Up := by
  rcases far_mem (P := P) (u₁ := u₁) (u₂ := u₂) w p with e | e <;> rw [e]
  · exact (h.res w hw).2.1
  · exact (h.res w hw).2.2.1

theorem Hyp.notW_of_RU {x : V} (hx : x ∈ Rt ∪ Up) : x ∉ W := by
  intro hW
  rcases Finset.mem_union.1 hx with hx | hx
  · exact Finset.disjoint_left.1 h.dRW hx hW
  · exact Finset.disjoint_left.1 h.dWU hW hx

theorem Hyp.far_notW {w : V} (hw : w ∈ W) (p : List V) : far P u₁ u₂ w p ∉ W :=
  h.notW_of_RU (h.u_mem hw p)

theorem Hyp.far_ne {w : V} (hw : w ∈ W) (p : List V) : far P u₁ u₂ w p ≠ w := by
  intro e
  have := h.far_notW hw p
  rw [e] at this
  exact this hw

theorem Hyp.resE_notF {w : V} (hw : w ∈ W) (p : List V) : s(w, far P u₁ u₂ w p) ∉ F := by
  rcases far_mem (P := P) (u₁ := u₁) (u₂ := u₂) w p with e | e <;> rw [e]
  · exact (h.res w hw).2.2.2.1
  · exact (h.res w hw).2.2.2.2

theorem Hyp.mem_RWU {p : List V} (hp : p ∈ P) {x : V} (hx : x ∈ p) : x ∈ Rt ∪ W ∪ Up := by
  obtain ⟨e, he, hxe⟩ := exists_mem_walkEdges_of_mem (h.dec.two_le_length hp) hx
  exact h.ends e (h.dec.edges_mem hp he) x hxe

theorem Hyp.mem_edge {p : List V} (hp : p ∈ P) {x : V} (hx : x ∈ p) : ∃ e ∈ F, x ∈ e := by
  obtain ⟨e, he, hxe⟩ := exists_mem_walkEdges_of_mem (h.dec.two_le_length hp) hx
  exact ⟨e, h.dec.edges_mem hp he, hxe⟩

theorem Hyp.RU_of_notW {p : List V} (hp : p ∈ P) {x : V} (hx : x ∈ p) (hW : x ∉ W) :
    x ∈ Rt ∪ Up := by
  have := h.mem_RWU hp hx
  simp only [Finset.mem_union] at this ⊢
  tauto

theorem Hyp.nodup : P.Nodup := nodup_of_isPathDecomp h.dec

/-- The shape of a path of `P`: its two (distinct) ends. -/
theorem Hyp.shape {p : List V} (hp : p ∈ P) :
    ∃ a b K, p = a :: K ∧ K ≠ [] ∧ p.head? = some a ∧ p.getLast? = some b ∧ a ≠ b := by
  have h2 := h.dec.two_le_length hp
  have hn := h.dec.nodup hp
  obtain ⟨a, K, rfl⟩ : ∃ a K, p = a :: K := by
    cases p with
    | nil => simp at h2
    | cons a K => exact ⟨a, K, rfl⟩
  have hK : K ≠ [] := by rintro rfl; simp at h2
  obtain ⟨b, hb⟩ : ∃ b, (a :: K).getLast? = some b := by
    cases e : (a :: K).getLast? with
    | none => simp at e
    | some b => exact ⟨b, rfl⟩
  refine ⟨a, b, K, rfl, hK, rfl, hb, ?_⟩
  intro hab
  subst hab
  exact head?_ne_getLast?_of_nodup hn h2 hb.symm

omit [DecidableEq V] h in
theorem walkEdges_pre (x : V) {L : List V} {a : V} (hL : L.head? = some a) :
    walkEdges (x :: L) = s(x, a) :: walkEdges L := by
  obtain ⟨t, rfl⟩ := exists_eq_cons_of_head? hL
  rfl

omit [DecidableEq V] h in
theorem walkEdges_suf {L : List V} {b : V} (hL : L.getLast? = some b) (y : V) :
    walkEdges (L ++ [y]) = walkEdges L ++ [s(b, y)] := by
  rw [walkEdges_concat, hL]
  rfl

omit h in
/-- The trail of a path `p = a ⋯ b` of `P`. -/
theorem trail_eq {p : List V} {a b : V} (ha : p.head? = some a) (hb : p.getLast? = some b) :
    trail W P u₁ u₂ p = extV W P u₁ u₂ p a ++ p ++ extV W P u₁ u₂ p b := by
  simp [trail, ha, hb]

omit h in
theorem appE_eq {p : List V} {a b : V} (ha : p.head? = some a) (hb : p.getLast? = some b) :
    appE W P u₁ u₂ p = extE W P u₁ u₂ p a ++ extE W P u₁ u₂ p b := by
  simp [appE, ha, hb]

theorem Hyp.walkEdges_trail {p : List V} (hp : p ∈ P) :
    List.Perm (walkEdges (trail W P u₁ u₂ p)) (walkEdges p ++ appE W P u₁ u₂ p) := by
  obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
  rw [trail_eq ha hb, appE_eq ha hb]
  unfold extV extE
  by_cases haW : a ∈ W <;> by_cases hbW : b ∈ W <;> simp only [haW, hbW, if_true, if_false]
  · rw [List.singleton_append, List.cons_append, walkEdges_pre (a := a) _ (by simp),
      walkEdges_suf hb, Sym2.eq_swap]
    exact (List.perm_middle (l₁ := walkEdges (a :: K)) (l₂ := [s(b, far P u₁ u₂ b (a :: K))])).symm
  · rw [List.singleton_append, List.append_nil, List.cons_append, List.append_nil,
      walkEdges_pre _ ha, Sym2.eq_swap]
    exact (List.perm_append_singleton _ _).symm
  · rw [List.nil_append, List.nil_append, walkEdges_suf hb]
  · simp

theorem Hyp.mem_appE {p : List V} (hp : p ∈ P) {e : Sym2 V} :
    e ∈ appE W P u₁ u₂ p ↔ ∃ w ∈ W, endAt w p ∧ e = s(w, far P u₁ u₂ w p) := by
  obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
  rw [appE_eq ha hb]
  unfold extE
  constructor
  · intro he
    rw [List.mem_append] at he
    rcases he with he | he
    · split_ifs at he with haW
      · exact ⟨a, haW, Or.inl ha, List.mem_singleton.1 he⟩
      · simp at he
    · split_ifs at he with hbW
      · exact ⟨b, hbW, Or.inr hb, List.mem_singleton.1 he⟩
      · simp at he
  · rintro ⟨w, hw, hwp, rfl⟩
    rw [List.mem_append]
    rcases hwp with hwp | hwp
    · rw [ha, Option.some.injEq] at hwp
      subst hwp
      left
      simp [hw]
    · rw [hb, Option.some.injEq] at hwp
      subst hwp
      right
      simp [hw]

theorem Hyp.appE_nodup {p : List V} (hp : p ∈ P) : (appE W P u₁ u₂ p).Nodup := by
  obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
  rw [appE_eq ha hb]
  unfold extE
  by_cases haW : a ∈ W <;> by_cases hbW : b ∈ W <;> simp only [haW, hbW, if_true, if_false]
  · rw [List.singleton_append, List.nodup_cons]
    refine ⟨?_, List.nodup_singleton _⟩
    rw [List.mem_singleton]
    intro e
    exact hab (sym2_W haW hbW (h.far_notW haW _) (h.far_notW hbW _) e).1
  all_goals simp

theorem Hyp.appE_notF {p : List V} (hp : p ∈ P) {e : Sym2 V} (he : e ∈ appE W P u₁ u₂ p) :
    e ∉ F := by
  obtain ⟨w, hw, _, rfl⟩ := (h.mem_appE hp).1 he
  exact h.resE_notF hw p

theorem Hyp.trail_edges_nodup {p : List V} (hp : p ∈ P) :
    (walkEdges (trail W P u₁ u₂ p)).Nodup := by
  refine (h.walkEdges_trail hp).nodup_iff.2 ?_
  rw [List.nodup_append]
  refine ⟨nodup_walkEdges (h.dec.nodup hp), h.appE_nodup hp, ?_⟩
  intro e he e' he' hee
  subst hee
  exact h.appE_notF hp he' (h.dec.edges_mem hp he)

theorem Hyp.trail_edges_notDiag {p : List V} (hp : p ∈ P) :
    ∀ e ∈ walkEdges (trail W P u₁ u₂ p), ¬ e.IsDiag := by
  intro e he
  rcases List.mem_append.1 ((h.walkEdges_trail hp).subset he) with he | he
  · exact h.loop e (h.dec.edges_mem hp he)
  · obtain ⟨w, hw, _, rfl⟩ := (h.mem_appE hp).1 he
    rw [Sym2.mk_isDiag_iff]
    exact fun e => h.far_ne hw p e.symm

theorem Hyp.trail_edges_meet {p : List V} (hp : p ∈ P) :
    ∀ e ∈ walkEdges (trail W P u₁ u₂ p), ∃ w ∈ W, w ∈ e := by
  intro e he
  rcases List.mem_append.1 ((h.walkEdges_trail hp).subset he) with he | he
  · exact h.meet e (h.dec.edges_mem hp he)
  · obtain ⟨w, hw, _, rfl⟩ := (h.mem_appE hp).1 he
    exact ⟨w, hw, Sym2.mem_mk_left _ _⟩

theorem Hyp.trail_ne_nil {p : List V} (hp : p ∈ P) : trail W P u₁ u₂ p ≠ [] := by
  obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
  rw [trail_eq ha hb]
  simp

theorem Hyp.mem_trail {p : List V} (hp : p ∈ P) {x : V} (hx : x ∈ trail W P u₁ u₂ p) :
    x ∈ p ∨ ∃ w ∈ W, endAt w p ∧ x = far P u₁ u₂ w p := by
  obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
  rw [trail_eq ha hb] at hx
  unfold extV at hx
  simp only [List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · split_ifs at hx with haW
    · exact Or.inr ⟨a, haW, Or.inl ha, List.mem_singleton.1 hx⟩
    · simp at hx
  · exact Or.inl hx
  · split_ifs at hx with hbW
    · exact Or.inr ⟨b, hbW, Or.inr hb, List.mem_singleton.1 hx⟩
    · simp at hx

theorem Hyp.rep_trail {p : List V} (hp : p ∈ P) :
    (trail W P u₁ u₂ p).length - (trail W P u₁ u₂ p).toFinset.card ≤ 2 := by
  obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
  have hsub : (a :: K).toFinset ⊆ (trail W P u₁ u₂ (a :: K)).toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    rw [trail_eq ha hb]
    simp only [List.mem_append]
    exact Or.inl (Or.inr hx)
  have h1 := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (h.dec.nodup hp)] at h1
  have h2 : (trail W P u₁ u₂ (a :: K)).length ≤ (a :: K).length + 2 := by
    rw [trail_eq ha hb]
    unfold extV
    simp only [List.length_append]
    split_ifs <;> simp <;> omega
  omega

theorem Hyp.trail_eq_self {p : List V} (hp : p ∈ P) (hW : ∀ w ∈ W, ¬ endAt w p) :
    trail W P u₁ u₂ p = p := by
  obtain ⟨a, b, K, rfl, hK, ha, hb, hab⟩ := h.shape hp
  rw [trail_eq ha hb]
  unfold extV
  have haW : a ∉ W := fun haW => hW a haW (Or.inl ha)
  have hbW : b ∉ W := fun hbW => hW b hbW (Or.inr hb)
  simp [haW, hbW]

theorem Hyp.trail_head {p : List V} (hp : p ∈ P) {a : V} (ha : p.head? = some a) :
    (trail W P u₁ u₂ p).head? = some (if a ∈ W then far P u₁ u₂ a p else a) := by
  obtain ⟨a', b, K, rfl, hK, ha', hb, hab⟩ := h.shape hp
  rw [ha', Option.some.injEq] at ha
  subst ha
  rw [trail_eq ha' hb]
  unfold extV
  split_ifs <;> simp

theorem Hyp.trail_last {p : List V} (hp : p ∈ P) {b : V} (hb : p.getLast? = some b) :
    (trail W P u₁ u₂ p).getLast? = some (if b ∈ W then far P u₁ u₂ b p else b) := by
  obtain ⟨a, b', K, rfl, hK, ha, hb', hab⟩ := h.shape hp
  rw [hb', Option.some.injEq] at hb
  subst hb
  rw [trail_eq ha hb']
  unfold extV
  by_cases haW : a ∈ W <;> by_cases hbW : b' ∈ W <;> simp only [haW, hbW, if_true, if_false]
  · rw [List.getLast?_concat]
  · rw [List.append_nil, List.getLast?_append, hb']
    rfl
  · rw [List.getLast?_concat]
  · rw [List.append_nil, List.nil_append]
    exact hb'

end Hyp

end PVStep

end EG
