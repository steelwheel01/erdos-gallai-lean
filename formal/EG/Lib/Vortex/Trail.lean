module

public import EG.Lib.Found.PathDecomp

/-!
# Trail surgery for the vortex observations (S) and (C) (manuscript s4, "Trail splitting",
"Closing")

Unit P4A, stage 3. List lemmas for the vortex step engine:
* `walkEdges_append_cons`, `walkEdges_split3` (edges of a concatenation);
* `cycleEdges_cons` (`cycleEdges (a :: t) = walkEdges (a :: t ++ [a])`);
* `exists_first_dup` (a list with a repetition has a first repeated segment);
* `trailSplit_aux` (the induction of (S): cycle removal at a minimal repetition);
* `rep_le_two_of_interior_nodup` (the last sentence of (S));
* `closing_aux` ((C)).
-/

public section

namespace EG

open List

variable {V : Type*}

/-! ## Edges of concatenations -/

theorem walkEdges_append_cons (l₁ : List V) (x : V) (l₂ : List V) :
    walkEdges (l₁ ++ x :: l₂) = walkEdges (l₁ ++ [x]) ++ walkEdges (x :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      simp only [List.cons_append, walkEdges_cons_cons] at ih ⊢
      rw [ih]

theorem walkEdges_cons_append_cons (a : V) (l₁ : List V) (x : V) (l₂ : List V) :
    walkEdges (a :: (l₁ ++ x :: l₂)) = walkEdges (a :: l₁ ++ [x]) ++ walkEdges (x :: l₂) := by
  have := walkEdges_append_cons (a :: l₁) x l₂
  simpa using this

/-- `cycleEdges (a :: t)` are the edges of the closed walk `a t a`. -/
theorem cycleEdges_cons (a : V) (t : List V) :
    cycleEdges (a :: t) = walkEdges (a :: t ++ [a]) := by
  unfold cycleEdges walkEdges
  rw [List.rotate_cons_succ, List.rotate_zero]
  simp only [List.tail_cons, List.cons_append]
  have h : (a :: (t ++ [a])) = (a :: t) ++ [a] := by simp
  rw [h, show t ++ [a] = (t ++ [a]) ++ [] by simp, List.zipWith_append (by simp)]
  simp

theorem walkEdges_sublist_append_right (l t : List V) :
    walkEdges l <+ walkEdges (l ++ t) := by
  induction l with
  | nil => simp
  | cons a r ih =>
    cases r with
    | nil => simp
    | cons b r =>
      simp only [List.cons_append, walkEdges_cons_cons] at ih ⊢
      exact ih.cons_cons _

theorem walkEdges_sublist_append_left (s l : List V) :
    walkEdges l <+ walkEdges (s ++ l) := by
  have h := walkEdges_sublist_append_right l.reverse s.reverse
  rw [← List.reverse_append, walkEdges_reverse, walkEdges_reverse] at h
  exact List.reverse_sublist.1 h

theorem walkEdges_sublist_of_infix {l l' : List V} (h : l <:+: l') :
    walkEdges l <+ walkEdges l' := by
  obtain ⟨s, t, rfl⟩ := h
  exact (walkEdges_sublist_append_right l t).trans (by
    rw [List.append_assoc]; exact walkEdges_sublist_append_left s (l ++ t))

/-! ## Heads and lasts -/

theorem head?_ne_getLast?_of_nodup {p : List V} (hp : p.Nodup) (h2 : 2 ≤ p.length) :
    p.head? ≠ p.getLast? := by
  match p, h2 with
  | a :: b :: t, _ =>
    intro h
    rw [List.head?_cons, List.getLast?_cons_cons] at h
    have hm : a ∈ b :: t := List.mem_of_getLast? h.symm
    exact (List.nodup_cons.1 hp).1 hm

theorem head?_eq_getLast?_of_length_one {p : List V} (h : p.length = 1) :
    p.head? = p.getLast? := by
  match p, h with
  | [a], _ => rfl

/-! ## The first repetition -/

/-- A list with a repeated entry has a first repeated segment: `l = A ++ v :: (B ++ v :: R)` with
`A ++ v :: B` duplicate-free. -/
theorem exists_first_dup : ∀ l : List V, ¬ l.Nodup →
    ∃ (A : List V) (v : V) (B R : List V), l = A ++ v :: (B ++ v :: R) ∧ (A ++ v :: B).Nodup := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro h; exact absurd List.nodup_nil h
  | append_singleton l x ih =>
    intro h
    by_cases hl : l.Nodup
    · have hx : x ∈ l := by
        by_contra hx
        apply h
        rw [List.nodup_append]
        refine ⟨hl, List.nodup_singleton x, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        rintro rfl
        exact hx (hb ▸ ha)
      obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
      exact ⟨A, x, B, [], by simp, hl⟩
    · obtain ⟨A, v, B, R, rfl, hN⟩ := ih hl
      exact ⟨A, v, B, R ++ [x], by simp, hN⟩

/-! ## Trail splitting (S) -/

section Split

variable [DecidableEq V]

/-- The conclusion of (S) for the walk `T`: cycles `C` and at most one path `p`. -/
@[expose] def SplitOut (T : List V) (C : List (List V)) (p : Option (List V)) : Prop :=
  (∀ c ∈ C, (Obj.cycle c).WF) ∧ C.length ≤ T.length - T.toFinset.card ∧
    List.Perm (C.flatMap cycleEdges ++ (p.map walkEdges).getD []) (walkEdges T) ∧
    (p.isSome ↔ T.head? ≠ T.getLast?) ∧
    (∀ q ∈ p, q.Nodup ∧ 2 ≤ q.length ∧ q.head? = T.head? ∧ q.getLast? = T.getLast?) ∧
    (∀ c ∈ C, ∀ x ∈ c, x ∈ T) ∧ (∀ q ∈ p, ∀ x ∈ q, x ∈ T)

theorem splitOut_of_nodup {T : List V} (hT : T ≠ []) (hN : T.Nodup) :
    ∃ C p, SplitOut T C p := by
  by_cases h2 : 2 ≤ T.length
  · refine ⟨[], some T, by simp, by simp, by simp, ?_, ?_, by simp, ?_⟩
    · simp [head?_ne_getLast?_of_nodup hN h2]
    · intro q hq
      simp only [Option.mem_def, Option.some.injEq] at hq
      subst hq
      exact ⟨hN, h2, rfl, rfl⟩
    · intro q hq x hx
      simp only [Option.mem_def, Option.some.injEq] at hq
      subst hq
      exact hx
  · have h1 : T.length = 1 := by
      have := List.length_pos_of_ne_nil hT
      omega
    refine ⟨[], none, by simp, by simp, ?_, ?_, by simp, by simp, by simp⟩
    · match T, h1 with
      | [a], _ => simp
    · simp [head?_eq_getLast?_of_length_one h1]

theorem splitOut_exists_aux : ∀ (n : ℕ) (T : List V), T.length = n → T ≠ [] →
    (walkEdges T).Nodup → (∀ e ∈ walkEdges T, ¬ e.IsDiag) → ∃ C p, SplitOut T C p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn hT hE hD
  by_cases hN : T.Nodup
  · exact splitOut_of_nodup hT hN
  obtain ⟨A, v, B, R, rfl, hAB⟩ := exists_first_dup T hN
  have hsplit : walkEdges (A ++ v :: (B ++ v :: R)) =
      walkEdges (A ++ [v]) ++ (cycleEdges (v :: B) ++ walkEdges (v :: R)) := by
    rw [walkEdges_append_cons, walkEdges_cons_append_cons, cycleEdges_cons]
  have hT' : walkEdges (A ++ v :: R) = walkEdges (A ++ [v]) ++ walkEdges (v :: R) :=
    walkEdges_append_cons A v R
  rw [hsplit] at hE hD
  have hY : (cycleEdges (v :: B)).Nodup := (List.Nodup.of_append_right hE).of_append_left
  have hsub : walkEdges (A ++ v :: R) <+
      walkEdges (A ++ [v]) ++ (cycleEdges (v :: B) ++ walkEdges (v :: R)) := by
    rw [hT']
    exact (List.sublist_append_right _ _).append_left _
  have hB : 2 ≤ B.length := by
    rcases B with _ | ⟨b, _ | ⟨b', B⟩⟩
    · exfalso
      apply hD s(v, v) (by simp [cycleEdges_cons])
      exact Sym2.mk_isDiag_iff.2 rfl
    · exfalso
      rw [cycleEdges_cons] at hY
      simp [Sym2.eq_swap] at hY
    · simp
  have hvB : (v :: B).Nodup := List.Nodup.of_append_right hAB
  obtain ⟨C', p', h1, h2, h3, h4, h5, h6, h7⟩ :=
    ih (A ++ v :: R).length (by rw [← hn]; simp) (A ++ v :: R) rfl (by simp)
      (hE.sublist hsub) (fun e he => hD e (hsub.subset he))
  have hhead : (A ++ v :: R).head? = (A ++ v :: (B ++ v :: R)).head? := by
    cases A <;> simp
  have hlast : (A ++ v :: R).getLast? = (A ++ v :: (B ++ v :: R)).getLast? := by
    have e : v :: (B ++ v :: R) = (v :: B) ++ (v :: R) := rfl
    rw [e, ← List.append_assoc, List.getLast?_append, List.getLast?_append]
    cases h : (v :: R).getLast? with
    | none => simp at h
    | some x => rfl
  have hsubT : ∀ x ∈ A ++ v :: R, x ∈ A ++ v :: (B ++ v :: R) := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto
  refine ⟨(v :: B) :: C', p', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨hvB, by simp; omega⟩
    · exact h1 c hc
  · have hsubF : (A ++ v :: (B ++ v :: R)).toFinset ⊆ (A ++ v :: R).toFinset ∪ B.toFinset := by
      intro x hx
      simp only [List.mem_toFinset, Finset.mem_union, List.mem_append, List.mem_cons] at hx ⊢
      tauto
    have hc1 := Finset.card_le_card hsubF
    have hc2 := Finset.card_union_le (A ++ v :: R).toFinset B.toFinset
    have hc3 := List.toFinset_card_le B
    have hc4 := List.toFinset_card_le (A ++ v :: R)
    simp only [List.length_cons, List.length_append] at h2 hc4 ⊢
    omega
  · rw [List.flatMap_cons, List.append_assoc]
    refine ((h3.append_left _)).trans ?_
    rw [hT', hsplit]
    exact List.perm_append_comm_assoc _ _ _
  · rw [h4, hhead, hlast]
  · intro q hq
    obtain ⟨a, b, c, d⟩ := h5 q hq
    exact ⟨a, b, c.trans hhead, d.trans hlast⟩
  · intro c hc x hx
    rcases List.mem_cons.1 hc with rfl | hc
    · simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
    · exact hsubT x (h6 c hc x hx)
  · intro q hq x hx
    exact hsubT x (h7 q hq x hx)

/-- (S), the construction: every non-empty trail without loops splits. -/
theorem splitOut_exists {T : List V} (hT : T ≠ []) (hE : (walkEdges T).Nodup)
    (hD : ∀ e ∈ walkEdges T, ¬ e.IsDiag) : ∃ C p, SplitOut T C p :=
  splitOut_exists_aux _ T rfl hT hE hD

/-- (S), last sentence: duplicate-free inner vertices give `rep(T) ≤ 2`. -/
theorem rep_le_two_of_interior_nodup {T : List V} (h : (interior T).Nodup) :
    T.length - T.toFinset.card ≤ 2 := by
  have h1 : (interior T).toFinset ⊆ T.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact interior_subset T hx
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup h] at h2
  have h3 : (interior T).length = T.length - 2 := by
    simp [interior]
    omega
  omega

end Split

/-! ## Closing (C) -/

theorem exists_eq_cons_of_head? {l : List V} {x : V} (h : l.head? = some x) :
    ∃ t, l = x :: t := by
  cases l with
  | nil => simp at h
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at h
    exact ⟨t, by rw [h]⟩

theorem exists_eq_concat_of_getLast? {l : List V} {y : V} (h : l.getLast? = some y) :
    ∃ t, l = t ++ [y] :=
  List.getLast?_eq_some_iff.1 h

/-- (C): `Q ∪ Q'` is a cycle whose edges are those of `Q` and `Q'`. -/
theorem closing_aux {Q Q' : List V} {x y : V} (hQ : Q.Nodup) (hQ2 : 2 ≤ pathLength Q)
    (hQx : Q.head? = some x) (hQy : Q.getLast? = some y) (hQ' : Q'.Nodup)
    (hQ'x : Q'.head? = some x) (hQ'y : Q'.getLast? = some y)
    (hint : ∀ v ∈ interior Q', v ∉ Q) :
    (Obj.cycle (Q ++ (interior Q').reverse)).WF ∧
      List.Perm (cycleEdges (Q ++ (interior Q').reverse)) (walkEdges Q ++ walkEdges Q') := by
  have hlen : 3 ≤ Q.length := by
    simp only [pathLength] at hQ2
    omega
  have hxy : x ≠ y := by
    intro h
    subst h
    exact head?_ne_getLast?_of_nodup hQ (by omega) (hQx.trans hQy.symm)
  obtain ⟨t', rfl⟩ := exists_eq_cons_of_head? hQ'x
  have ht' : t'.getLast? = some y := by
    cases t' with
    | nil => simp at hQ'y; exact absurd hQ'y hxy
    | cons a t => rwa [List.getLast?_cons_cons] at hQ'y
  obtain ⟨I, rfl⟩ := exists_eq_concat_of_getLast? ht'
  have hI : interior (x :: (I ++ [y])) = I := by
    simp [interior]
  rw [hI] at hint ⊢
  have hInd : I.Nodup := (List.nodup_cons.1 hQ').2.of_append_left
  refine ⟨⟨?_, by simp; omega⟩, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hQ, List.nodup_reverse.2 hInd, ?_⟩
    intro a ha b hb hab
    subst hab
    exact hint a (List.mem_reverse.1 hb) ha
  · obtain ⟨Qt, rfl⟩ := exists_eq_cons_of_head? hQx
    obtain ⟨Q₀, hQ₀⟩ := exists_eq_concat_of_getLast? hQy
    rw [List.cons_append, cycleEdges_cons]
    have e1 : x :: (Qt ++ I.reverse) ++ [x] = Q₀ ++ y :: (I.reverse ++ [x]) := by
      rw [← List.cons_append, List.append_assoc, hQ₀]
      simp
    have e2 : (x :: (I ++ [y])).reverse = y :: (I.reverse ++ [x]) := by simp
    rw [e1, walkEdges_append_cons, ← hQ₀, ← e2, walkEdges_reverse]
    exact (List.reverse_perm _).append_left _

end EG
