module

public import EG.Lib.Vortex.Trail

/-!
# Path ends and degrees (manuscript s4, observation (E); Lemma PV (c), per-vertex bound)

Unit P4A, stage 3. Double counting for path decompositions:
* `countP_mem_walkEdges_add`: a path contributes `2` to the degree of each inner vertex and `1`
  to each of its two ends;
* `IsPathDecomp.degE_add_pathEndCount`: `deg_F(v) + pec(P, v) = 2 · #{p ∈ P : v ∈ p}`;
* `IsPathDecomp.pathEndCount_mod_two` ((E), first sentence);
* `IsPathDecomp.pathEndCount_le_degE` (an end of a path lies on exactly one of its edges);
* `IsPathDecomp.length_le_card` ((E), second sentence);
* `degE_le_card_sub_one` (`deg_{H_0}(x) ≤ |Z| - 1`).
-/

public section

namespace EG

open List

variable {V : Type*} [DecidableEq V]

/-- A path (non-empty, no repeated vertex) meets each inner vertex in two edges and each end in
one: `#{edges at v} + [v = head] + [v = last] = 2 [v ∈ p]`. -/
theorem countP_mem_walkEdges_add : ∀ (p : List V), p.Nodup → p ≠ [] → ∀ v : V,
    (walkEdges p).countP (fun e => v ∈ e) + (if p.head? = some v then 1 else 0) +
      (if p.getLast? = some v then 1 else 0) = 2 * (if v ∈ p then 1 else 0)
  | [], _, h, _ => absurd rfl h
  | [a], _, _, v => by
    by_cases h : a = v
    · subst h; simp
    · have h' : v ≠ a := fun e => h e.symm
      simp [h, h']
  | a :: b :: t, hp, _, v => by
    have ih := countP_mem_walkEdges_add (b :: t) (List.nodup_cons.1 hp).2 (by simp) v
    have hab : a ∉ b :: t := (List.nodup_cons.1 hp).1
    have hl : (b :: t).getLast? ≠ some a := fun h => hab (List.mem_of_getLast? h)
    rw [walkEdges_cons_cons, List.countP_cons, List.head?_cons, List.getLast?_cons_cons]
    rw [List.head?_cons] at ih
    by_cases hva : v = a
    · subst hva
      have hvb : v ≠ b := fun h => hab (h ▸ List.mem_cons_self ..)
      have hbv : b ≠ v := fun h => hvb h.symm
      simp only [hl, hbv, hab, Option.some.injEq, if_false, if_true, List.mem_cons_self,
        Sym2.mem_mk_left, decide_true, add_zero] at ih ⊢
      omega
    · have hav : a ≠ v := fun h => hva h.symm
      have hmem : (v ∈ a :: b :: t) ↔ v ∈ b :: t := by
        simp [hva]
      have hs : (v ∈ s(a, b)) ↔ v = b := by
        simp [Sym2.mem_iff, hva]
      simp only [hmem, hs, hav, Option.some.injEq, if_false, add_zero] at ih ⊢
      by_cases hvb : v = b
      · subst hvb; simp at ih ⊢; omega
      · have hbv : b ≠ v := fun h => hvb h.symm
        simp only [hvb, hbv, decide_false, Bool.false_eq_true, if_false, add_zero] at ih ⊢
        omega

theorem end_ite_eq {p : List V} (hp : p.Nodup) (h2 : 2 ≤ p.length) (v : V) :
    (if p.head? = some v ∨ p.getLast? = some v then 1 else 0) =
      (if p.head? = some v then 1 else 0) + (if p.getLast? = some v then 1 else 0) := by
  have hne := head?_ne_getLast?_of_nodup hp h2
  by_cases h1 : p.head? = some v <;> by_cases h2' : p.getLast? = some v
  · exact absurd (h1.trans h2'.symm) hne
  all_goals simp [h1, h2']

/-- A path with at least one edge: `#{edges at v} + [v is an end] = 2 [v ∈ p]`. -/
theorem countP_mem_walkEdges_add_end {p : List V} (hp : p.Nodup) (h2 : 2 ≤ p.length) (v : V) :
    (walkEdges p).countP (fun e => v ∈ e) +
      (if p.head? = some v ∨ p.getLast? = some v then 1 else 0) =
      2 * (if v ∈ p then 1 else 0) := by
  have hne : p ≠ [] := by rintro rfl; simp at h2
  rw [end_ite_eq hp h2, ← add_assoc]
  exact countP_mem_walkEdges_add p hp hne v

theorem end_ite_le_countP {p : List V} (hp : p.Nodup) (h2 : 2 ≤ p.length) (v : V) :
    (if p.head? = some v ∨ p.getLast? = some v then 1 else 0) ≤
      (walkEdges p).countP (fun e => v ∈ e) := by
  have h := countP_mem_walkEdges_add_end hp h2 v
  have hm : (p.head? = some v ∨ p.getLast? = some v) → v ∈ p := by
    rintro (h | h)
    · exact List.mem_of_head? h
    · exact List.mem_of_getLast? h
  by_cases he : p.head? = some v ∨ p.getLast? = some v
  · simp only [he, if_true, hm he] at h ⊢
    omega
  · simp only [he, if_false]
    omega

theorem countP_flatMap_add_pathEndCount (P : List (List V))
    (hP : ∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup) (v : V) :
    (P.flatMap walkEdges).countP (fun e => v ∈ e) + pathEndCount P v =
      2 * P.countP (fun p => v ∈ p) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp := hP p (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have h1 := countP_mem_walkEdges_add_end hp.2 hp.1 v
    rw [List.flatMap_cons, List.countP_append, pathEndCount_cons, List.countP_cons]
    by_cases hv : v ∈ p
    · simp only [hv, decide_true, if_true] at h1 ⊢
      omega
    · simp only [hv, decide_false, Bool.false_eq_true, if_false] at h1 ⊢
      omega

theorem pathEndCount_le_countP_flatMap (P : List (List V))
    (hP : ∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup) (v : V) :
    pathEndCount P v ≤ (P.flatMap walkEdges).countP (fun e => v ∈ e) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp := hP p (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    have h1 := end_ite_le_countP hp.2 hp.1 v
    rw [List.flatMap_cons, List.countP_append, pathEndCount_cons]
    omega

namespace IsPathDecomp

variable {F : Finset (Sym2 V)} {P : List (List V)}

theorem finset_eq (h : IsPathDecomp (F : Set (Sym2 V)) P) : F = (P.flatMap walkEdges).toFinset := by
  ext e
  rw [List.mem_toFinset, h.mem_iff]
  rfl

theorem degE_eq_countP (h : IsPathDecomp (F : Set (Sym2 V)) P) (v : V) :
    degE F v = (P.flatMap walkEdges).countP (fun e => v ∈ e) := by
  unfold degE edgesAt
  rw [h.finset_eq, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (h.2.1.filter _)]
  congr 1
  ext e
  simp

theorem degE_add_pathEndCount (h : IsPathDecomp (F : Set (Sym2 V)) P) (v : V) :
    degE F v + pathEndCount P v = 2 * P.countP (fun p => v ∈ p) := by
  rw [h.degE_eq_countP]
  exact countP_flatMap_add_pathEndCount P h.1 v

/-- (E), first sentence. -/
theorem pathEndCount_mod_two (h : IsPathDecomp (F : Set (Sym2 V)) P) (v : V) :
    pathEndCount P v % 2 = degE F v % 2 := by
  have := h.degE_add_pathEndCount v
  omega

/-- An end of a path lies on one of its edges, and the paths are edge-disjoint. -/
theorem pathEndCount_le_degE (h : IsPathDecomp (F : Set (Sym2 V)) P) (v : V) :
    pathEndCount P v ≤ degE F v := by
  rw [h.degE_eq_countP]
  exact pathEndCount_le_countP_flatMap P h.1 v

end IsPathDecomp

/-! ## Counting path ends -/

/-- The end indicator of a path is `1` if `v` is an end. -/
abbrev endAt (v : V) (p : List V) : Prop := p.head? = some v ∨ p.getLast? = some v

theorem sum_head_ite {p : List V} {a : V} (ha : p.head? = some a) (W : Finset V) (haW : a ∈ W) :
    ∑ w ∈ W, (if p.head? = some w then 1 else 0) = 1 := by
  simp only [ha, Option.some.injEq]
  rw [Finset.sum_ite_eq]
  simp [haW]

theorem sum_last_ite {p : List V} {a : V} (ha : p.getLast? = some a) (W : Finset V)
    (haW : a ∈ W) : ∑ w ∈ W, (if p.getLast? = some w then 1 else 0) = 1 := by
  simp only [ha, Option.some.injEq]
  rw [Finset.sum_ite_eq]
  simp [haW]

theorem sum_end_ite_eq_two {p : List V} (hp : p.Nodup) (h2 : 2 ≤ p.length) (W : Finset V)
    (hW : ∀ x, endAt x p → x ∈ W) :
    ∑ w ∈ W, (if endAt w p then 1 else 0) = 2 := by
  simp only [endAt]
  rw [Finset.sum_congr rfl (fun w _ => end_ite_eq hp h2 w), Finset.sum_add_distrib]
  obtain ⟨a, ha⟩ : ∃ a, p.head? = some a := by
    cases p with
    | nil => simp at h2
    | cons a t => exact ⟨a, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, p.getLast? = some b := by
    cases hl : p.getLast? with
    | none => simp at hl; subst hl; simp at h2
    | some b => exact ⟨b, rfl⟩
  rw [sum_head_ite ha W (hW a (Or.inl ha)), sum_last_ite hb W (hW b (Or.inr hb))]

theorem sum_pathEndCount_eq (P : List (List V)) (hP : ∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup)
    (W : Finset V) (hW : ∀ p ∈ P, ∀ x, endAt x p → x ∈ W) :
    ∑ w ∈ W, pathEndCount P w = 2 * P.length := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hp := hP p (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
      (fun q hq => hW q (List.mem_cons_of_mem _ hq))
    simp only [pathEndCount_cons]
    rw [Finset.sum_add_distrib, ih',
      sum_end_ite_eq_two hp.2 hp.1 W (hW p (List.mem_cons_self ..)), List.length_cons]
    ring

theorem length_le_card_of_ends (P : List (List V)) (hP : ∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup)
    (W : Finset V) (hW : ∀ p ∈ P, ∀ x, endAt x p → x ∈ W) (h2 : ∀ v, pathEndCount P v ≤ 2) :
    P.length ≤ W.card := by
  have h := sum_pathEndCount_eq P hP W hW
  have h' : ∑ w ∈ W, pathEndCount P w ≤ ∑ _w ∈ W, 2 := Finset.sum_le_sum fun w _ => h2 w
  rw [Finset.sum_const, smul_eq_mul] at h'
  omega

/-- The paths with an end in `S` number at most the path ends in `S`. -/
theorem countP_exists_end_le (P : List (List V)) (S : Finset V) :
    P.countP (fun p => ∃ w ∈ S, endAt w p) ≤ ∑ w ∈ S, pathEndCount P w := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.countP_cons]
    simp only [pathEndCount_cons]
    rw [Finset.sum_add_distrib]
    have : (if decide (∃ w ∈ S, endAt w p) = true then 1 else 0) ≤
        ∑ w ∈ S, (if p.head? = some w ∨ p.getLast? = some w then 1 else 0) := by
      by_cases h : ∃ w ∈ S, endAt w p
      · obtain ⟨w, hw, hwp⟩ := h
        simp only [decide_eq_true_eq]
        rw [if_pos ⟨w, hw, hwp⟩]
        have := Finset.single_le_sum (f := fun w => if p.head? = some w ∨ p.getLast? = some w
          then 1 else 0) (fun _ _ => Nat.zero_le _) hw
        simp only [hwp, if_true] at this
        exact this
      · simp only [decide_eq_true_eq]
        rw [if_neg h]
        exact Nat.zero_le _
    omega

omit [DecidableEq V] in
/-- The ends of a path whose edges have both ends in `W` lie in `W`. -/
theorem endAt_mem_of_edges {p : List V} (h2 : 2 ≤ p.length) {W : Finset V}
    (hW : ∀ e ∈ walkEdges p, ∀ v ∈ e, v ∈ W) {x : V} (hx : endAt x p) : x ∈ W := by
  have hxp : x ∈ p := by
    rcases hx with h | h
    · exact List.mem_of_head? h
    · exact List.mem_of_getLast? h
  obtain ⟨e, he, hxe⟩ := exists_mem_walkEdges_of_mem h2 hxp
  exact hW e he x hxe

namespace IsPathDecomp

variable {F : Finset (Sym2 V)} {P : List (List V)}

/-- (E), second sentence. -/
theorem length_le_card (h : IsPathDecomp (F : Set (Sym2 V)) P) (h2 : ∀ v, pathEndCount P v ≤ 2)
    {W : Finset V} (hW : ∀ e ∈ F, ∀ v ∈ e, v ∈ W) : P.length ≤ W.card :=
  length_le_card_of_ends P h.1 W
    (fun _p hp _x hx => endAt_mem_of_edges (h.two_le_length hp)
      (fun e he v hv => hW e (h.edges_mem hp he) v hv) hx) h2

end IsPathDecomp

/-! ## Degree bound -/

/-- `deg_{H_0}(x) ≤ |Z| - 1` when `H_0` is loopless with all ends in `Z`. -/
theorem degE_le_card_sub_one {Z : Finset V} {H : Finset (Sym2 V)} (hD : ∀ e ∈ H, ¬ e.IsDiag)
    (hZ : ∀ e ∈ H, ∀ v ∈ e, v ∈ Z) (x : V) : degE H x ≤ Z.card - 1 := by
  by_cases hx : x ∈ Z
  · have hsub : edgesAt H x ⊆ (Z.erase x).image (fun y => s(x, y)) := by
      intro e he
      simp only [edgesAt, Finset.mem_filter] at he
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 he.2
      rw [Finset.mem_image]
      refine ⟨y, Finset.mem_erase.2 ⟨?_, hZ _ he.1 y (Sym2.mem_mk_right _ _)⟩, rfl⟩
      rintro rfl
      exact hD _ he.1 (Sym2.mk_isDiag_iff.2 rfl)
    calc degE H x = (edgesAt H x).card := rfl
      _ ≤ ((Z.erase x).image (fun y => s(x, y))).card := Finset.card_le_card hsub
      _ ≤ (Z.erase x).card := Finset.card_image_le
      _ = Z.card - 1 := Finset.card_erase_of_mem hx
  · have : edgesAt H x = ∅ := by
      ext e
      simp only [edgesAt, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro he hxe
      exact hx (hZ e he x hxe)
    simp [degE, this]

end EG
