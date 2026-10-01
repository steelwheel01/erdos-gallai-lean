module

public import EG.Lib.Found.Graph
public import EG.Lib.Found.PathDecomp
public import EG.Lib.Found.Fnum
public import EG.Lib.Found.Components
public import EG.Spec.Ext.Lovasz
public import EG.Spec.Ext.Cor22

/-!
# Bucić–Montgomery Corollary 22 from Lovász's theorem (manuscript s1:citCor22)

Proof of `EG.Spec.Cor22Statement` from `EG.Spec.LovaszStatement` ([s1:citThm21]), following
[BM]'s proof (arXiv:2211.07689v2, l. 1426–1442; blueprint `formal/work/p2/blueprint_s1.md`, node
`s1:citCor22`, hazard C22-PROOF-EXTERNAL): "Form a graph `G'` from `G` by adding a new vertex
`v₀` and an edge from `v₀` to each vertex `v ∈ V(G)` for which `d_G(v)` is even. By Theorem 21,
there is a collection `C` of at most `(n+1)/2` cycles and paths which decomposes `G'`. … each
vertex `v ∈ V(G)` has odd degree in `G'`, and therefore must be an endvertex of an odd number of
paths in `C` … each vertex in `G` is the endvertex of at most 1 path in `C` … `C` is in fact a
collection consisting only of paths … for each path `P ∈ C`, if `v₀ ∈ V(P)` then remove the
vertex `v₀` from `P` … each vertex is an endvertex of at most two paths in `C'`."

Here `V(G)` is the set `edgeVerts F` of ends of edges of `F`, `v₀ = none` and `G'` lives on
`Option V`.

* Parity: `countP_mem_walkEdges_add`, `countP_mem_cycleEdges`, `even_countP_add_pathEndCount`.
* Counting ends: `sum_pathEndCount_le`.
* Deleting `v₀` from a path: `exists_split_path`, `exists_split_paths`.
-/

public section

namespace EG

namespace Cor22

variable {V : Type*}

/-! ### Lists -/

theorem walkEdges_cons (x : V) (l : List V) :
    walkEdges (x :: l) = (l.head?.map fun b => s(x, b)).toList ++ walkEdges l := by
  cases l with
  | nil => rfl
  | cons b l => rfl

theorem walkEdges_append_cons (l₁ : List V) (x : V) (l₂ : List V) :
    walkEdges (l₁ ++ x :: l₂) = walkEdges (l₁ ++ [x]) ++ walkEdges (x :: l₂) := by
  induction l₁ with
  | nil => simp [walkEdges_cons]
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [List.cons_append, walkEdges_cons_cons] at ih ⊢
      rw [ih]

theorem walkEdges_map {W : Type*} (f : V → W) (l : List V) :
    walkEdges (l.map f) = (walkEdges l).map (Sym2.map f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      simp only [List.map_cons, walkEdges_cons_cons, Sym2.map_mk] at ih ⊢
      rw [ih]

theorem walkEdges_eq_nil_of_length_lt {l : List V} (h : l.length < 2) : walkEdges l = [] := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl

theorem exists_eq_map_some {l : List (Option V)} (h : none ∉ l) :
    ∃ l' : List V, l = l'.map some := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    rw [List.mem_cons, not_or] at h
    obtain ⟨l', rfl⟩ := ih h.2
    cases a with
    | none => exact absurd rfl h.1
    | some a => exact ⟨a :: l', rfl⟩

theorem head_ne_getLast {p : List V} (hp : p.Nodup) (h2 : 2 ≤ p.length) {x : V}
    (hh : p.head? = some x) (hl : p.getLast? = some x) : False := by
  match p, hp, h2 with
  | a :: b :: t, hp, _ =>
    have ha : a = x := by simpa using hh
    subst ha
    rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil b t),
      Option.some.injEq] at hl
    have hmem : (b :: t).getLast (List.cons_ne_nil b t) ∈ b :: t := List.getLast_mem _
    rw [hl] at hmem
    exact (List.nodup_cons.1 hp).1 hmem

/-! ### Parity of degrees in paths and cycles -/

variable [DecidableEq V]

/-- In a path `p` (no repeated vertex), the number of edges at `x`, plus `1` for each end equal
to `x`, is `2` if `x ∈ p` and `0` otherwise. -/
theorem countP_mem_walkEdges_add (x : V) :
    ∀ {p : List V}, p.Nodup → p ≠ [] →
      (walkEdges p).countP (fun e => x ∈ e) + (if p.head? = some x then 1 else 0) +
        (if p.getLast? = some x then 1 else 0) = 2 * (if x ∈ p then 1 else 0)
  | [], _, h => absurd rfl h
  | [a], _, _ => by
    by_cases h : a = x
    · subst h; simp
    · have h' : x ≠ a := fun e => h e.symm
      simp [h, h']
  | a :: b :: t, hp, _ => by
    have ih := countP_mem_walkEdges_add x (p := b :: t) (List.nodup_cons.1 hp).2
      (List.cons_ne_nil _ _)
    have hnd : a ∉ b :: t := (List.nodup_cons.1 hp).1
    rw [walkEdges_cons_cons, List.countP_cons, List.head?_cons, List.getLast?_cons_cons]
    rw [List.head?_cons] at ih
    by_cases hxa : x = a
    · subst hxa
      have hxb : x ≠ b := fun h => hnd (h ▸ List.mem_cons_self ..)
      have h0 : (if x ∈ b :: t then 1 else 0) = 0 := if_neg hnd
      rw [h0] at ih
      have hbx : ¬ (some b = some x) := fun h => hxb (Option.some.inj h).symm
      rw [if_neg hbx] at ih
      have hc : (walkEdges (b :: t)).countP (fun e => x ∈ e) = 0 := by omega
      have hl : ¬ ((b :: t).getLast? = some x) := by
        intro h; rw [if_pos h] at ih; omega
      rw [hc, if_neg hl, if_pos (List.mem_cons_self ..)]
      simp
    · have h1 : (x ∈ s(a, b)) ↔ (some b = some x) := by
        rw [Sym2.mem_iff, Option.some.injEq]
        exact ⟨fun h => h.resolve_left hxa ▸ rfl, fun h => Or.inr h.symm⟩
      have h2 : (some a = some x) ↔ False := by
        rw [Option.some.injEq]; exact ⟨fun h => hxa h.symm, False.elim⟩
      have h3 : (x ∈ a :: b :: t) ↔ (x ∈ b :: t) := by
        rw [List.mem_cons]; exact ⟨fun h => h.resolve_left hxa, Or.inr⟩
      simp only [h1, h2, h3, decide_eq_true_eq, if_false]
      omega

theorem zipWith_append_left_of_length_le {α β γ : Type*} (f : α → β → γ) :
    ∀ (l₁ l₃ : List α) (l₂ : List β), l₂.length ≤ l₁.length →
      List.zipWith f (l₁ ++ l₃) l₂ = List.zipWith f l₁ l₂
  | [], _, [], _ => by simp
  | [], _, _ :: _, h => absurd h (by simp)
  | _ :: _, _, [], _ => by simp
  | a :: l₁, l₃, b :: l₂, h => by
    simp only [List.cons_append, List.zipWith_cons_cons]
    rw [zipWith_append_left_of_length_le f l₁ l₃ l₂ (by simpa using h)]

omit [DecidableEq V] in
theorem cycleEdges_eq (a : V) (t : List V) :
    cycleEdges (a :: t) = walkEdges (a :: t ++ [a]) := by
  unfold cycleEdges walkEdges
  rw [List.rotate_cons_succ, List.rotate_zero, List.tail_append_of_ne_nil (List.cons_ne_nil a t),
    List.tail_cons, zipWith_append_left_of_length_le _ _ _ _ (by simp)]

/-- In a cycle (no repeated vertex, at least three vertices) every vertex has even degree. -/
theorem countP_mem_cycleEdges (x : V) {c : List V} (hc : c.Nodup) (h3 : 3 ≤ c.length) :
    (cycleEdges c).countP (fun e => x ∈ e) = 2 * (if x ∈ c then 1 else 0) := by
  match c, hc, h3 with
  | a :: t, hc, h3 =>
    have ht : t ≠ [] := by rintro rfl; simp at h3
    have hp := countP_mem_walkEdges_add x hc (List.cons_ne_nil a t)
    rw [cycleEdges_eq, walkEdges_concat, List.countP_append]
    obtain ⟨l, hl⟩ : ∃ l, (a :: t).getLast? = some l := ⟨_, List.getLast?_eq_some_getLast (List.cons_ne_nil a t)⟩
    rw [hl, List.head?_cons] at hp
    rw [hl]
    have hla : l ≠ a := by
      intro h
      subst h
      exact head_ne_getLast hc (by omega) (List.head?_cons ..) hl
    simp only [Option.map_some, Option.toList_some, List.countP_singleton]
    have e1 : (x ∈ s(l, a)) ↔ (l = x ∨ a = x) := by
      rw [Sym2.mem_iff]; exact ⟨fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
        fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    simp only [e1, Option.some.injEq, decide_eq_true_eq] at hp ⊢
    by_cases hax : a = x
    · subst hax
      have hm : a ∈ a :: t := List.mem_cons_self ..
      simp only [hla, hm, or_true, if_true, if_false] at hp ⊢
      omega
    · simp only [hax, or_false, if_false] at hp ⊢
      omega

/-- Degree parity in a family of paths: `deg(x) + #(paths ending at x)` is even. -/
theorem even_countP_add_pathEndCount (x : V) :
    ∀ {P : List (List V)}, (∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup) →
      Even ((P.flatMap walkEdges).countP (fun e => x ∈ e) + pathEndCount P x)
  | [], _ => by simp
  | p :: P, hP => by
    have ih := even_countP_add_pathEndCount x (P := P) (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    obtain ⟨h2, hnd⟩ := hP p (List.mem_cons_self ..)
    have hne : p ≠ [] := by rintro rfl; simp at h2
    have hp := countP_mem_walkEdges_add x hnd hne
    have hor : (if p.head? = some x ∨ p.getLast? = some x then 1 else 0) =
        (if p.head? = some x then 1 else 0) + (if p.getLast? = some x then 1 else 0) := by
      by_cases hh : p.head? = some x
      · have hl : ¬ p.getLast? = some x := fun hl => head_ne_getLast hnd h2 hh hl
        simp [hh, hl]
      · simp [hh]
    rw [List.flatMap_cons, List.countP_append, pathEndCount_cons, hor]
    rw [Nat.even_iff] at ih ⊢
    omega

/-- Degree parity in a family of cycles: every degree is even. -/
theorem even_countP_cycles (x : V) :
    ∀ {C : List (List V)}, (∀ c ∈ C, (Obj.cycle c).WF) →
      Even ((C.flatMap cycleEdges).countP (fun e => x ∈ e))
  | [], _ => by simp
  | c :: C, hC => by
    have ih := even_countP_cycles x (C := C) (fun q hq => hC q (List.mem_cons_of_mem _ hq))
    obtain ⟨hnd, h3⟩ := hC c (List.mem_cons_self ..)
    have hc := countP_mem_cycleEdges x hnd h3
    rw [List.flatMap_cons, List.countP_append, hc]
    rw [Nat.even_iff] at ih ⊢
    omega

/-- The degree `deg_E(x)` computed from a duplicate-free list of the edges of `E`. -/
theorem degE_eq_countP {E : Finset (Sym2 V)} {L : List (Sym2 V)} (hL : L.Nodup)
    (hmem : ∀ e, e ∈ L ↔ e ∈ E) (x : V) : degE E x = L.countP (fun e => x ∈ e) := by
  have hE : E = L.toFinset := by
    ext e; rw [List.mem_toFinset, hmem]
  unfold degE edgesAt
  have hf : L.toFinset.filter (fun e => x ∈ e) = (L.filter (fun e => decide (x ∈ e))).toFinset := by
    ext e; simp
  rw [hE, hf, List.toFinset_card_of_nodup (hL.filter _), List.countP_eq_length_filter]

/-- For a path-and-cycle decomposition `(P, C)` of `E`, `deg_E(x) + #(paths of P ending at x)`
is even. -/
theorem even_degE_add_pathEndCount {E : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (E : Set (Sym2 V)) P C) (x : V) :
    Even (degE E x + pathEndCount P x) := by
  obtain ⟨hP, hC, hnd, hmem⟩ := h
  rw [degE_eq_countP hnd (fun e => by rw [hmem]; rfl), List.countP_append]
  have h1 := even_countP_add_pathEndCount x hP
  have h2 := even_countP_cycles x hC
  rw [Nat.even_iff] at h1 h2 ⊢
  omega

/-! ### Counting ends -/

theorem sum_ends_le_two (S : Finset V) (p : List V) :
    ∑ x ∈ S, (if p.head? = some x ∨ p.getLast? = some x then 1 else 0) ≤ 2 := by
  have h1 : ∀ o : Option V, (S.filter fun x => o = some x).card ≤ 1 := by
    intro o
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact Option.some.inj (ha.2.symm.trans hb.2)
  calc ∑ x ∈ S, (if p.head? = some x ∨ p.getLast? = some x then 1 else 0)
      ≤ ∑ x ∈ S, ((if p.head? = some x then 1 else 0) + (if p.getLast? = some x then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hh : p.head? = some x <;> by_cases hl : p.getLast? = some x <;> simp [hh, hl]
    _ = (S.filter fun x => p.head? = some x).card + (S.filter fun x => p.getLast? = some x).card := by
        rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]
    _ ≤ 1 + 1 := Nat.add_le_add (h1 _) (h1 _)

/-- The paths of `P` have at most `2|P|` ends in total. -/
theorem sum_pathEndCount_le (S : Finset V) :
    ∀ P : List (List V), ∑ x ∈ S, pathEndCount P x ≤ 2 * P.length
  | [] => by simp
  | p :: P => by
    have ih := sum_pathEndCount_le S P
    simp only [pathEndCount_cons, Finset.sum_add_distrib, List.length_cons]
    have := sum_ends_le_two S p
    omega

/-- Edge-disjointness: an edge lies in at most one member of a family whose edge lists
concatenate to a duplicate-free list. -/
theorem countP_mem_le_one {α β : Type*} [DecidableEq β] (f : α → List β) (e : β) :
    ∀ {P : List α}, (P.flatMap f).Nodup → P.countP (fun p => e ∈ f p) ≤ 1
  | [], _ => by simp
  | p :: P, h => by
    rw [List.flatMap_cons, List.nodup_append] at h
    have ih := countP_mem_le_one f e h.2.1
    rw [List.countP_cons]
    by_cases he : e ∈ f p
    · have h0 : P.countP (fun p => e ∈ f p) = 0 := by
        rw [List.countP_eq_zero]
        intro q hq heq
        exact h.2.2 e he e (List.mem_flatMap.2 ⟨q, hq, by simpa using heq⟩) rfl
      simp [he, h0]
    · simp [he, ih]

/-! ### Deleting `v₀ = none` from a path -/

/-- The path `l` if it has an edge, and nothing otherwise. -/
def pieces (l : List V) : List (List V) := if 2 ≤ l.length then [l] else []

omit [DecidableEq V] in
theorem flatMap_pieces (l : List V) : (pieces l).flatMap walkEdges = walkEdges l := by
  unfold pieces
  split_ifs with h
  · simp
  · rw [walkEdges_eq_nil_of_length_lt (by omega)]; rfl

omit [DecidableEq V] in
theorem mem_pieces {l q : List V} (hl : l.Nodup) (hq : q ∈ pieces l) : 2 ≤ q.length ∧ q.Nodup := by
  unfold pieces at hq
  split_ifs at hq with h
  · rw [List.mem_singleton] at hq; subst hq; exact ⟨h, hl⟩
  · simp at hq

theorem pathEndCount_pieces (l : List V) (v : V) :
    pathEndCount (pieces l) v ≤ if l.head? = some v ∨ l.getLast? = some v then 1 else 0 := by
  unfold pieces
  split_ifs with h h'
  · simp [pathEndCount_cons, h']
  · simp [pathEndCount_cons, h']
  · simp
  · simp

theorem pathEndCount_append (P Q : List (List V)) (v : V) :
    pathEndCount (P ++ Q) v = pathEndCount P v + pathEndCount Q v := by
  unfold pathEndCount; rw [List.countP_append]

theorem filter_map_some (L : List (Sym2 V)) :
    (L.map (Sym2.map some)).filter (fun e => decide (none ∉ e)) = L.map (Sym2.map some) := by
  rw [List.filter_eq_self]
  intro e he
  obtain ⟨e', -, rfl⟩ := List.mem_map.1 he
  simp only [decide_eq_true_eq, Sym2.mem_map, not_exists, not_and]
  intro _ _ h; exact absurd h (by simp)

/-- Deleting `none` from a path on `Option V`: the remaining pieces with an edge form paths on
`V` with exactly the edges of the path that avoid `none`; a vertex `v` is an end of a piece only
if `some v` is an end of the path or `s(none, some v)` is an edge of it. -/
theorem exists_split_path {p : List (Option V)} (hp : p.Nodup) :
    ∃ Q : List (List V), (∀ q ∈ Q, 2 ≤ q.length ∧ q.Nodup) ∧
      (Q.flatMap walkEdges).map (Sym2.map some) =
        (walkEdges p).filter (fun e => decide (none ∉ e)) ∧
      ∀ v : V, pathEndCount Q v ≤
        (if p.head? = some (some v) ∨ p.getLast? = some (some v) then 1 else 0) +
        (if s(none, some v) ∈ walkEdges p then 1 else 0) := by
  by_cases hn : none ∈ p
  · obtain ⟨a, b, rfl⟩ := List.append_of_mem hn
    rw [List.nodup_append] at hp
    obtain ⟨hpa, hpb, hdisj⟩ := hp
    have hna : none ∉ a := fun h => hdisj none h none (List.mem_cons_self ..) rfl
    have hnb : none ∉ b := (List.nodup_cons.1 hpb).1
    obtain ⟨a', rfl⟩ := exists_eq_map_some hna
    obtain ⟨b', rfl⟩ := exists_eq_map_some hnb
    have ha' : a'.Nodup := List.Nodup.of_map _ hpa
    have hb' : b'.Nodup := List.Nodup.of_map _ (List.nodup_cons.1 hpb).2
    have hwe : walkEdges (a'.map some ++ none :: b'.map some) =
        (walkEdges a').map (Sym2.map some) ++
          ((a'.getLast?.map fun u => s(some u, none)).toList ++
            ((b'.head?.map fun u => s(none, some u)).toList ++ (walkEdges b').map (Sym2.map some))) := by
      rw [walkEdges_append_cons, walkEdges_concat, walkEdges_cons, walkEdges_map, walkEdges_map,
        List.getLast?_map, List.head?_map, Option.map_map, Option.map_map]
      simp only [List.append_assoc]
      rfl
    refine ⟨pieces a' ++ pieces b', ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with h | h
      · exact mem_pieces ha' h
      · exact mem_pieces hb' h
    · rw [hwe, List.flatMap_append, flatMap_pieces, flatMap_pieces, List.map_append,
        List.filter_append, List.filter_append, List.filter_append, filter_map_some,
        filter_map_some]
      have h1 : (a'.getLast?.map fun u => s(some u, none)).toList.filter
          (fun e => decide (none ∉ e)) = [] := by
        cases a'.getLast? <;> simp
      have h2 : (b'.head?.map fun u => s(none, some u)).toList.filter
          (fun e => decide (none ∉ e)) = [] := by
        cases b'.head? <;> simp
      rw [h1, h2, List.nil_append, List.nil_append]
    · intro v
      rw [pathEndCount_append]
      have hA := pathEndCount_pieces a' v
      have hB := pathEndCount_pieces b' v
      -- `v` is not in both `a'` and `b'`
      have hnot : ¬ (v ∈ a' ∧ v ∈ b') := by
        rintro ⟨h1, h2⟩
        exact hdisj (some v) (List.mem_map_of_mem h1) (some v)
          (List.mem_cons_of_mem _ (List.mem_map_of_mem h2)) rfl
      have hAe : (a'.head? = some v ∨ a'.getLast? = some v) →
          ((a'.map some ++ none :: b'.map some).head? = some (some v) ∨
            (a'.map some ++ none :: b'.map some).getLast? = some (some v)) ∨
          s(none, some v) ∈ walkEdges (a'.map some ++ none :: b'.map some) := by
        rintro (h | h)
        · left; left
          cases a' with
          | nil => simp at h
          | cons c a' => simpa using h
        · right
          rw [hwe, h]
          simp [Sym2.eq_swap]
      have hBe : (b'.head? = some v ∨ b'.getLast? = some v) →
          ((a'.map some ++ none :: b'.map some).head? = some (some v) ∨
            (a'.map some ++ none :: b'.map some).getLast? = some (some v)) ∨
          s(none, some v) ∈ walkEdges (a'.map some ++ none :: b'.map some) := by
        rintro (h | h)
        · right
          rw [hwe, h]
          simp
        · left; right
          rw [List.getLast?_append, List.getLast?_cons, List.getLast?_map, h]
          simp
      have hmemA : (a'.head? = some v ∨ a'.getLast? = some v) → v ∈ a' := by
        rintro (h | h)
        · exact List.mem_of_mem_head? h
        · exact List.mem_of_getLast? h
      have hmemB : (b'.head? = some v ∨ b'.getLast? = some v) → v ∈ b' := by
        rintro (h | h)
        · exact List.mem_of_mem_head? h
        · exact List.mem_of_getLast? h
      by_cases hA' : a'.head? = some v ∨ a'.getLast? = some v
      · have hB0 : ¬ (b'.head? = some v ∨ b'.getLast? = some v) :=
          fun hB' => hnot ⟨hmemA hA', hmemB hB'⟩
        rw [if_pos hA'] at hA
        rw [if_neg hB0] at hB
        rcases hAe hA' with h | h
        · rw [if_pos h]; omega
        · rw [if_pos h]; omega
      · rw [if_neg hA'] at hA
        by_cases hB' : b'.head? = some v ∨ b'.getLast? = some v
        · rw [if_pos hB'] at hB
          rcases hBe hB' with h | h
          · rw [if_pos h]; omega
          · rw [if_pos h]; omega
        · rw [if_neg hB'] at hB
          omega
  · obtain ⟨l, rfl⟩ := exists_eq_map_some hn
    have hl : l.Nodup := List.Nodup.of_map _ hp
    refine ⟨pieces l, fun q hq => mem_pieces hl hq, ?_, ?_⟩
    · rw [flatMap_pieces, walkEdges_map, filter_map_some]
    · intro v
      have h := pathEndCount_pieces l v
      have e : (l.head? = some v ∨ l.getLast? = some v) ↔
          ((l.map some).head? = some (some v) ∨ (l.map some).getLast? = some (some v)) := by
        simp [List.head?_map, List.getLast?_map]
      by_cases h' : l.head? = some v ∨ l.getLast? = some v
      · rw [if_pos h'] at h
        rw [if_pos (e.1 h')]
        omega
      · rw [if_neg h'] at h
        omega

theorem exists_split_paths :
    ∀ {P : List (List (Option V))}, (∀ p ∈ P, p.Nodup) →
      ∃ Q : List (List V), (∀ q ∈ Q, 2 ≤ q.length ∧ q.Nodup) ∧
        (Q.flatMap walkEdges).map (Sym2.map some) =
          (P.flatMap walkEdges).filter (fun e => decide (none ∉ e)) ∧
        ∀ v : V, pathEndCount Q v ≤
          pathEndCount P (some v) + P.countP (fun p => s(none, some v) ∈ walkEdges p)
  | [], _ => ⟨[], by simp, by simp, by simp⟩
  | p :: P, hP => by
    obtain ⟨Q₁, h₁, e₁, c₁⟩ := exists_split_path (hP p (List.mem_cons_self ..))
    obtain ⟨Q₂, h₂, e₂, c₂⟩ := exists_split_paths (P := P) (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    refine ⟨Q₁ ++ Q₂, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with h | h
      · exact h₁ q h
      · exact h₂ q h
    · rw [List.flatMap_append, List.map_append, e₁, e₂, List.flatMap_cons, List.filter_append]
    · intro v
      rw [pathEndCount_append, pathEndCount_cons, List.countP_cons]
      have := c₁ v
      have := c₂ v
      simp only [decide_eq_true_eq] at *
      omega

/-! ### Degrees in `G'` -/

theorem degE_union_of_disjoint {A B : Finset (Sym2 V)} (h : Disjoint A B) (x : V) :
    degE (A ∪ B) x = degE A x + degE B x := by
  unfold degE edgesAt
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

omit [DecidableEq V] in
theorem sym2Map_some_injective : Function.Injective (Sym2.map (some : V → Option V)) :=
  Sym2.map.injective (Option.some_injective V)

theorem degE_image_some (F : Finset (Sym2 V)) (v : V) :
    degE (F.image (Sym2.map some)) (some v) = degE F v := by
  unfold degE edgesAt
  have : (F.image (Sym2.map some)).filter (fun e => some v ∈ e) =
      (F.filter (fun e => v ∈ e)).image (Sym2.map some) := by
    rw [Finset.filter_image]
    congr 1
    ext e
    simp [Sym2.mem_map]
  rw [this, Finset.card_image_of_injective _ sym2Map_some_injective]

theorem degE_star (A : Finset V) (v : V) :
    degE (A.image fun w => s(none, some w)) (some v) = if v ∈ A then 1 else 0 := by
  unfold degE edgesAt
  have : (A.image fun w => s(none, some w)).filter (fun e => some v ∈ e) =
      if v ∈ A then {s(none, some v)} else ∅ := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    split_ifs with hv
    · rw [Finset.mem_singleton]
      constructor
      · rintro ⟨⟨w, _, rfl⟩, hw⟩
        simp at hw
        rw [hw]
      · rintro rfl
        exact ⟨⟨v, hv, rfl⟩, Sym2.mem_mk_right _ _⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      rintro ⟨w, hw, rfl⟩ hvw
      simp at hvw
      exact hv (hvw ▸ hw)
  rw [this]
  split_ifs <;> simp

/-! ### Corollary 22 -/

universe u

/-- [s1:citCor22] ([BM, Corollary 22]) from Lovász's theorem ([s1:citThm21]): "Every graph can be
decomposed into paths such that each vertex is an end of at most two of the paths." -/
theorem cor22_of_lovasz (hL : Spec.LovaszStatement.{u}) {V : Type u} [DecidableEq V]
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    ∃ P : List (List V), IsPathDecomp (F : Set (Sym2 V)) P ∧ ∀ v, pathEndCount P v ≤ 2 := by
  classical
  set U := edgeVerts F with hU
  set Ueven := U.filter (fun v => Even (degE F v)) with hUeven
  set E₁ : Finset (Sym2 (Option V)) := F.image (Sym2.map some) with hE₁
  set E₂ : Finset (Sym2 (Option V)) := Ueven.image (fun w => s(none, some w)) with hE₂
  set E' := E₁ ∪ E₂ with hE'
  set W' : Finset (Option V) := insert none (U.image some) with hW'
  have hdisj : Disjoint E₁ E₂ := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨e₁, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 h2
    have : none ∈ Sym2.map some e₁ := hw ▸ Sym2.mem_mk_left _ _
    simp [Sym2.mem_map] at this
  have hE'loop : ∀ e ∈ E', ¬ e.IsDiag := by
    intro e he
    rcases Finset.mem_union.1 he with h | h
    · obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.1 h
      rw [Sym2.isDiag_map (Option.some_injective V)]
      exact hF e₁ he₁
    · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 h
      simp
  have hE'verts : ∀ e ∈ E', ∀ x ∈ e, x ∈ W' := by
    intro e he x hx
    rcases Finset.mem_union.1 he with h | h
    · obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.1 hx
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (mem_edgeVerts.2 ⟨e₁, he₁, hy⟩))
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.1 hw).1)
  set G' := FGraph.ofEdges W' E' with hG'
  have hG'e : G'.edges = E' := FGraph.ofEdges_edges_of_subset hE'loop hE'verts
  have hG'c : G'.card = U.card + 1 := by
    rw [FGraph.card_def, hG', FGraph.ofEdges_verts, hW', Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective V)]
  obtain ⟨P, C, hPC, hlen⟩ := hL (Option V) G'
  rw [hG'e, hG'c] at *
  -- every vertex of `U` has odd degree in `G'`
  have hodd : ∀ v ∈ U, Odd (degE E' (some v)) := by
    intro v hv
    rw [hE', degE_union_of_disjoint hdisj, hE₁, degE_image_some, hE₂, degE_star]
    by_cases he : Even (degE F v)
    · rw [if_pos (Finset.mem_filter.2 ⟨hv, he⟩)]
      exact he.add_one
    · rw [if_neg (show v ∉ Ueven from fun h => he (Finset.mem_filter.1 h).2), add_zero]
      exact Nat.not_even_iff_odd.1 he
  have hends : ∀ v ∈ U, Odd (pathEndCount P (some v)) := by
    intro v hv
    have h1 := even_degE_add_pathEndCount hPC (some v)
    have h2 := hodd v hv
    rw [Nat.even_add] at h1
    rw [← Nat.not_even_iff_odd] at h2 ⊢
    exact fun h => h2 (h1.2 h)
  have hsum : ∑ v ∈ U, pathEndCount P (some v) ≤ 2 * P.length := by
    have := sum_pathEndCount_le (U.image some) P
    rwa [Finset.sum_image (fun a _ b _ h => Option.some_injective V h)] at this
  have hsum_ge : U.card ≤ ∑ v ∈ U, pathEndCount P (some v) := by
    calc U.card = ∑ _v ∈ U, 1 := by simp
      _ ≤ ∑ v ∈ U, pathEndCount P (some v) :=
        Finset.sum_le_sum fun v hv => (hends v hv).pos
  -- no cycles, and every vertex of `U` is an end of exactly one path
  have hC : C = [] := by
    rw [← List.length_eq_zero_iff]
    omega
  subst hC
  rw [isPathCycleDecomp_nil_right] at hPC
  have hone : ∀ v ∈ U, pathEndCount P (some v) ≤ 1 := by
    intro v hv
    have hsplit := Finset.add_sum_erase U (fun v => pathEndCount P (some v)) hv
    have hrest : (U.erase v).card ≤ ∑ w ∈ U.erase v, pathEndCount P (some w) := by
      calc (U.erase v).card = ∑ _w ∈ U.erase v, 1 := by simp
        _ ≤ ∑ w ∈ U.erase v, pathEndCount P (some w) :=
          Finset.sum_le_sum fun w hw => (hends w (Finset.mem_of_mem_erase hw)).pos
    have hcard := Finset.card_erase_of_mem hv
    have hU1 : 1 ≤ U.card := Finset.card_pos.2 ⟨v, hv⟩
    have hle : pathEndCount P (some v) ≤ 2 := by simp at hlen; omega
    obtain ⟨k, hk⟩ := hends v hv
    omega
  -- delete `none`
  obtain ⟨Q, hQ, hQe, hQc⟩ := exists_split_paths (P := P) (fun p hp => (hPC.1 p hp).2)
  have hQdecomp : IsPathDecomp (F : Set (Sym2 V)) Q := by
    refine ⟨hQ, ?_, ?_⟩
    · have : ((Q.flatMap walkEdges).map (Sym2.map some)).Nodup := by
        rw [hQe]; exact hPC.2.1.filter _
      exact List.Nodup.of_map _ this
    · intro e
      rw [← List.mem_map_of_injective sym2Map_some_injective, hQe, List.mem_filter,
        hPC.2.2, Finset.mem_coe, hE', Finset.mem_union, hE₁, hE₂, Finset.mem_coe]
      constructor
      · rintro ⟨h | h, -⟩
        · obtain ⟨e₁, he₁, heq⟩ := Finset.mem_image.1 h
          rwa [← sym2Map_some_injective heq]
        · obtain ⟨w, -, hw⟩ := Finset.mem_image.1 h
          have : none ∈ Sym2.map some e := hw ▸ Sym2.mem_mk_left _ _
          simp [Sym2.mem_map] at this
      · intro he
        refine ⟨Or.inl (Finset.mem_image_of_mem _ he), ?_⟩
        simp [Sym2.mem_map]
  refine ⟨Q, hQdecomp, fun v => ?_⟩
  by_cases hv : v ∈ U
  · have h1 := hone v hv
    have h2 := countP_mem_le_one walkEdges (s(none, some v)) hPC.2.1
    have h3 := hQc v
    omega
  · -- `v` is on no edge of `F`, so it is on no path of `Q`
    have h0 : pathEndCount Q v = 0 := by
      unfold pathEndCount
      rw [List.countP_eq_zero]
      intro q hq hend
      obtain ⟨h2, -⟩ := hQ q hq
      have hvq : v ∈ q := by
        have hend' : q.head? = some v ∨ q.getLast? = some v := by simpa using hend
        rcases hend' with h | h
        · exact List.mem_of_mem_head? h
        · exact List.mem_of_getLast? h
      obtain ⟨e, he, hve⟩ := exists_mem_walkEdges_of_mem h2 hvq
      have heF : e ∈ F := by
        have := (hQdecomp.2.2 e).1 (List.mem_flatMap.2 ⟨q, hq, he⟩)
        exact_mod_cast this
      exact hv (mem_edgeVerts.2 ⟨e, heF, hve⟩)
    omega

end Cor22

end EG
