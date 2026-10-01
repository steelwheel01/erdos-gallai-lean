# LovaszBasic.lean (archived, unused alternative Lovász route; not built)

```lean
module

public import EG.Lib.Ext.Cor22

/-!
# Lovász's path-and-cycle theorem: basic operations (manuscript s1:citThm21)

Helper file for the proof of `EG.Spec.LovaszStatement` (P3 unit s1, round 2; proof outline in
`formal/work/p3/s1.md`, "Round 2"). A path-and-cycle decomposition `(P, C)` of a finite edge set
`F` is `IsPathCycleDecomp (F : Set (Sym2 V)) P C`; its edges, as a multiset, are
`pcMS P C` (the multiset of the list `P.flatMap walkEdges ++ C.flatMap cycleEdges`).

* `isPCD_of_ms`: the generic replacement lemma: new paths and cycles whose edge multiset,
  plus the removed edges `Y ⊆ F`, is the old edge multiset plus new edges `X` (disjoint from
  `F`), decompose `(F \ Y) ∪ X`.
* Edges of `L ++ x :: R` as a multiset (`ms_walkEdges_split`).
* `exists_end_of_odd`: a vertex of odd degree is an end of some path.
* `pendant`: removing a pendant edge does not increase the size of a decomposition.
-/

public section

namespace EG

namespace Lov

open Cor22

variable {V : Type*}

/-! ### Multisets of edges -/

/-- The multiset of edges of a family of paths `P` and cycles `C`. -/
@[expose] def pcMS (P C : List (List V)) : Multiset (Sym2 V) :=
  ((P.flatMap walkEdges ++ C.flatMap cycleEdges : List (Sym2 V)) : Multiset (Sym2 V))

theorem coe_flatMap {W : Type*} (P : List (List V)) (f : List V → List W) :
    ((P.flatMap f : List W) : Multiset W) = (P.map fun p => (f p : Multiset W)).sum := by
  induction P with
  | nil => simp
  | cons p P ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

theorem pcMS_eq (P C : List (List V)) :
    pcMS P C = (P.map fun p => (walkEdges p : Multiset (Sym2 V))).sum +
      (C.map fun c => (cycleEdges c : Multiset (Sym2 V))).sum := by
  unfold pcMS
  rw [← Multiset.coe_add, coe_flatMap, coe_flatMap]

theorem pcMS_cons_left (p : List V) (P C : List (List V)) :
    pcMS (p :: P) C = (walkEdges p : Multiset (Sym2 V)) + pcMS P C := by
  rw [pcMS_eq, pcMS_eq, List.map_cons, List.sum_cons, add_assoc]

theorem pcMS_cons_right (P : List (List V)) (c : List V) (C : List (List V)) :
    pcMS P (c :: C) = (cycleEdges c : Multiset (Sym2 V)) + pcMS P C := by
  rw [pcMS_eq, pcMS_eq, List.map_cons, List.sum_cons]
  abel

theorem pcMS_append_left (P₁ P₂ C : List (List V)) :
    pcMS (P₁ ++ P₂) C = (P₁.map fun p => (walkEdges p : Multiset (Sym2 V))).sum + pcMS P₂ C := by
  rw [pcMS_eq, pcMS_eq, List.map_append, List.sum_append, add_assoc]

theorem pcMS_append_right (P C₁ C₂ : List (List V)) :
    pcMS P (C₁ ++ C₂) =
      (C₁.map fun c => (cycleEdges c : Multiset (Sym2 V))).sum + pcMS P C₂ := by
  rw [pcMS_eq, pcMS_eq, List.map_append, List.sum_append]
  abel

theorem pcMS_perm {P P' C C' : List (List V)} (hP : P.Perm P') (hC : C.Perm C') :
    pcMS P C = pcMS P' C' := by
  rw [pcMS_eq, pcMS_eq, (hP.map _).sum_eq, (hC.map _).sum_eq]

variable [DecidableEq V]

omit [DecidableEq V] in
theorem mem_pcMS {P C : List (List V)} {e : Sym2 V} :
    e ∈ pcMS P C ↔ e ∈ P.flatMap walkEdges ++ C.flatMap cycleEdges := Multiset.mem_coe

omit [DecidableEq V] in
theorem nodup_pcMS {P C : List (List V)} :
    (pcMS P C).Nodup ↔ (P.flatMap walkEdges ++ C.flatMap cycleEdges).Nodup := Multiset.coe_nodup

/-- The generic replacement lemma. -/
theorem isPCD_of_ms {F X Y : Finset (Sym2 V)} {P C P' C' : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C)
    (hP' : ∀ p ∈ P', 2 ≤ p.length ∧ p.Nodup) (hC' : ∀ c ∈ C', (Obj.cycle c).WF)
    (hX : Disjoint F X) (hY : Y ⊆ F)
    (hM : pcMS P' C' + Y.val = pcMS P C + X.val) :
    IsPathCycleDecomp (((F \ Y) ∪ X : Finset (Sym2 V)) : Set (Sym2 V)) P' C' := by
  obtain ⟨-, -, hnd, hmem⟩ := h
  have hM0 : (pcMS P C).Nodup := nodup_pcMS.2 hnd
  have hmemM : ∀ e, e ∈ pcMS P C ↔ e ∈ F := fun e => by
    rw [mem_pcMS, hmem e]; rfl
  have hnd2 : (pcMS P C + X.val).Nodup := by
    rw [Multiset.nodup_add]
    refine ⟨hM0, X.nodup, ?_⟩
    rw [Multiset.disjoint_left]
    intro e he heX
    exact Finset.disjoint_left.1 hX ((hmemM e).1 he) heX
  have hsum : (pcMS P' C' + Y.val).Nodup := hM ▸ hnd2
  refine ⟨hP', hC', nodup_pcMS.1 (Multiset.nodup_of_le (Multiset.le_add_right _ _) hsum), ?_⟩
  intro e
  have h1 : e ∈ pcMS P' C' ↔ e ∈ ((F \ Y) ∪ X : Finset (Sym2 V)) := by
    constructor
    · intro he
      have he2 : e ∈ pcMS P C + X.val := by
        rw [← hM]; exact Multiset.mem_add.2 (Or.inl he)
      rw [Finset.mem_union, Finset.mem_sdiff]
      rcases Multiset.mem_add.1 he2 with he2 | he2
      · refine Or.inl ⟨(hmemM e).1 he2, fun heY => ?_⟩
        rw [Multiset.nodup_add] at hsum
        exact Multiset.disjoint_left.1 hsum.2.2 he heY
      · exact Or.inr he2
    · intro he
      rw [Finset.mem_union, Finset.mem_sdiff] at he
      have he2 : e ∈ pcMS P' C' + Y.val := by
        rw [hM]
        rcases he with ⟨he, -⟩ | he
        · exact Multiset.mem_add.2 (Or.inl ((hmemM e).2 he))
        · exact Multiset.mem_add.2 (Or.inr he)
      rcases Multiset.mem_add.1 he2 with he2 | he2
      · exact he2
      · rcases he with ⟨-, heY⟩ | heX
        · exact absurd he2 heY
        · exact absurd (hY he2) (Finset.disjoint_right.1 hX heX)
  rw [← mem_pcMS, h1]
  rfl

/-- Special case: only new edges. -/
theorem isPCD_of_ms_add {F X : Finset (Sym2 V)} {P C P' C' : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C)
    (hP' : ∀ p ∈ P', 2 ≤ p.length ∧ p.Nodup) (hC' : ∀ c ∈ C', (Obj.cycle c).WF)
    (hX : Disjoint F X) (hM : pcMS P' C' = pcMS P C + X.val) :
    IsPathCycleDecomp ((F ∪ X : Finset (Sym2 V)) : Set (Sym2 V)) P' C' := by
  have := isPCD_of_ms (Y := ∅) h hP' hC' hX (Finset.empty_subset _) (by simpa using hM)
  simpa using this

/-! ### Edges of `L ++ x :: R` -/

omit [DecidableEq V] in
theorem ms_walkEdges_split (L R : List V) (x : V) :
    (walkEdges (L ++ x :: R) : Multiset (Sym2 V)) =
      (walkEdges L : Multiset (Sym2 V)) + (walkEdges R : Multiset (Sym2 V)) +
        ((L.getLast?.map fun a => s(a, x)).toList : Multiset (Sym2 V)) +
        ((R.head?.map fun b => s(x, b)).toList : Multiset (Sym2 V)) := by
  rw [walkEdges_append_cons, walkEdges_concat, walkEdges_cons]
  simp only [← Multiset.coe_add]
  abel

omit [DecidableEq V] in
theorem ms_walkEdges_reverse (p : List V) :
    (walkEdges p.reverse : Multiset (Sym2 V)) = (walkEdges p : Multiset (Sym2 V)) := by
  rw [walkEdges_reverse, Multiset.coe_reverse]

omit [DecidableEq V] in
theorem walkEdges_reverse_mem {p : List V} {e : Sym2 V} :
    e ∈ walkEdges p.reverse ↔ e ∈ walkEdges p := by
  rw [walkEdges_reverse, List.mem_reverse]

/-! ### Reversing a path, removing a path -/

/-- Replacing a path of a decomposition by a family with the same edges. -/
theorem isPCD_replace {F : Finset (Sym2 V)} {P₁ P₂ C : List (List V)} {p : List V}
    {ps : List (List V)} (h : IsPathCycleDecomp (F : Set (Sym2 V)) (P₁ ++ p :: P₂) C)
    (hps : ∀ q ∈ ps, 2 ≤ q.length ∧ q.Nodup)
    (hM : (ps.map fun q => (walkEdges q : Multiset (Sym2 V))).sum = walkEdges p) :
    IsPathCycleDecomp (F : Set (Sym2 V)) (P₁ ++ ps ++ P₂) C := by
  have := isPCD_of_ms (X := ∅) (Y := ∅) (P' := P₁ ++ ps ++ P₂) (C' := C) h ?_ h.2.1 (by simp) (Finset.empty_subset _) ?_
  · simpa using this
  · intro q hq
    rw [List.mem_append, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact h.1 q (List.mem_append_left _ hq)
    · exact hps q hq
    · exact h.1 q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))
  · rw [List.append_assoc, pcMS_append_left, pcMS_append_left, pcMS_append_left, pcMS_cons_left, hM]

/-- Reversing a path of a decomposition. -/
theorem isPCD_reverse {F : Finset (Sym2 V)} {P₁ P₂ C : List (List V)} {p : List V}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) (P₁ ++ p :: P₂) C) :
    IsPathCycleDecomp (F : Set (Sym2 V)) (P₁ ++ [p.reverse] ++ P₂) C := by
  refine isPCD_replace h ?_ ?_
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    obtain ⟨h2, hnd⟩ := h.1 p (List.mem_append_right _ (List.mem_cons_self ..))
    exact ⟨by simpa using h2, List.nodup_reverse.2 hnd⟩
  · simp [ms_walkEdges_reverse]

/-- The edges of a decomposed edge set are not loops. -/
theorem not_isDiag_of_isPCD {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {e : Sym2 V} (he : e ∈ F) : ¬ e.IsDiag := by
  obtain ⟨hP, hC, -, hmem⟩ := h
  have he' := (hmem e).2 he
  rcases List.mem_append.1 he' with he' | he'
  · obtain ⟨p, hp, hep⟩ := List.mem_flatMap.1 he'
    exact not_isDiag_of_mem_walkEdges (hP p hp).2 hep
  · obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 he'
    obtain ⟨hnd, h3⟩ := hC c hc
    exact not_isDiag_of_mem_cycleEdges hnd (by omega) hec

/-! ### Ends -/

/-- A vertex of odd degree is an end of some path. -/
theorem exists_end_of_odd {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {v : V} (hv : Odd (degE F v)) :
    ∃ p ∈ P, p.head? = some v ∨ p.getLast? = some v := by
  have he := even_degE_add_pathEndCount h v
  have hpos : 0 < pathEndCount P v := by
    rcases Nat.even_or_odd (pathEndCount P v) with h0 | h0
    · exact absurd (Nat.even_add.1 he |>.2 h0) (Nat.not_even_iff_odd.2 hv)
    · exact h0.pos
  unfold pathEndCount at hpos
  obtain ⟨p, hp, hpv⟩ := List.countP_pos_iff.1 hpos
  exact ⟨p, hp, by simpa using hpv⟩

/-- A vertex that is an end of some path can be made the first vertex of a path. -/
theorem exists_head_of_end {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {v : V}
    (hv : ∃ p ∈ P, p.head? = some v ∨ p.getLast? = some v) :
    ∃ P₁ P₂ : List (List V), ∃ p : List V, p.head? = some v ∧
      IsPathCycleDecomp (F : Set (Sym2 V)) (P₁ ++ p :: P₂) C ∧
      (P₁ ++ p :: P₂).length = P.length := by
  obtain ⟨p, hp, hpv⟩ := hv
  obtain ⟨P₁, P₂, rfl⟩ := List.append_of_mem hp
  rcases hpv with hpv | hpv
  · exact ⟨P₁, P₂, p, hpv, h, rfl⟩
  · refine ⟨P₁, P₂, p.reverse, by rw [List.head?_reverse, hpv], ?_, by simp⟩
    simpa using isPCD_reverse h

/-! ### Pendant edges -/

/-- Removing a pendant edge `xl` (the only edge of `F` at `l`) does not increase the size. -/
theorem pendant {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x l : V} (hxl : x ≠ l)
    (hmem : s(x, l) ∈ F) (hl : ∀ e ∈ F, l ∈ e → e = s(x, l)) :
    ∃ P' C' : List (List V), IsPathCycleDecomp ((F.erase s(x, l) : Finset _) : Set (Sym2 V)) P' C' ∧
      P'.length + C'.length ≤ P.length + C.length := by
  have hdeg : degE F l = 1 := by
    unfold degE edgesAt
    rw [Finset.card_eq_one]
    refine ⟨s(x, l), ?_⟩
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨he, hle⟩ => hl e he hle, fun he => he ▸ ⟨hmem, Sym2.mem_mk_right _ _⟩⟩
  obtain ⟨P₁, P₂, p, hph, h', hlen⟩ :=
    exists_head_of_end h (exists_end_of_odd h (by rw [hdeg]; exact odd_one))
  obtain ⟨h2, hnd⟩ := h'.1 p (List.mem_append_right _ (List.mem_cons_self ..))
  match p, hph, h2, hnd with
  | a :: y :: rest, hph, _, hnd =>
    have ha : a = l := by simpa using hph
    subst ha
    have hey : s(a, y) ∈ F := by
      have := (h'.2.2.2 s(a, y)).1 (List.mem_append_left _ (List.mem_flatMap.2
        ⟨a :: y :: rest, List.mem_append_right _ (List.mem_cons_self ..), by simp⟩))
      exact this
    have hy : y = x := by
      have := hl _ hey (Sym2.mem_mk_left _ _)
      rw [Sym2.eq_iff] at this
      rcases this with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact absurd h1.symm hxl
      · exact h1
    subst hy
    set ps : List (List V) := if rest = [] then [] else [y :: rest] with hps
    have hps' : ∀ q ∈ ps, 2 ≤ q.length ∧ q.Nodup := by
      intro q hq
      rw [hps] at hq
      split_ifs at hq with hr
      · simp at hq
      · rw [List.mem_singleton] at hq
        subst hq
        refine ⟨?_, (List.nodup_cons.1 hnd).2⟩
        cases rest with
        | nil => exact absurd rfl hr
        | cons _ _ => simp
    have hsum : (ps.map fun q => (walkEdges q : Multiset (Sym2 V))).sum + {s(y, a)} =
        (walkEdges (a :: y :: rest) : Multiset (Sym2 V)) := by
      rw [walkEdges_cons_cons, hps]
      split_ifs with hr
      · subst hr; simp [Sym2.eq_swap]
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm, Sym2.eq_swap]
    have key := isPCD_of_ms (X := ∅) (Y := {s(y, a)}) (P' := P₁ ++ ps ++ P₂) (C' := C) h'
      (by
        intro q hq
        rw [List.mem_append, List.mem_append] at hq
        rcases hq with (hq | hq) | hq
        · exact h'.1 q (List.mem_append_left _ hq)
        · exact hps' q hq
        · exact h'.1 q (List.mem_append_right _ (List.mem_cons_of_mem _ hq)))
      h'.2.1 (by simp) (by simpa using hmem)
      (by
        simp only [List.append_assoc, pcMS_append_left, pcMS_cons_left, ← hsum,
          Finset.empty_val, add_zero, Finset.singleton_val, Multiset.singleton_add]
        abel)
    refine ⟨P₁ ++ ps ++ P₂, C, ?_, ?_⟩
    · have hF : ((F \ {s(y, a)}) ∪ ∅ : Finset _) = F.erase s(y, a) := by
        rw [Finset.union_empty, Finset.sdiff_singleton_eq_erase]
      rw [hF] at key
      exact key
    · rw [← hlen]
      simp only [List.length_append, List.length_cons]
      have : ps.length ≤ 1 := by rw [hps]; split_ifs <;> simp
      omega

end Lov

end EG
```
