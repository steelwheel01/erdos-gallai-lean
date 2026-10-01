module

public import EG.Lib.Quot.Round
public import EG.Lib.Found.Graph
public import EG.Lib.Found.Fnum

/-!
# List lemmas for the round step (probe P-1, stage 3)

Generic list facts used by the proofs of s7:lemSimple, s7:lemMULT, s7:lemWellDef and s7:lemLift
(unit P1, design note `formal/work/p2b/P1.md`):
* the pairing lists of (b): `pairUp_flatten_leftover` (a list is its consecutive pairs followed by
  its leftover), and the consequences for duplicate-free lists (`pairUp_ne`, `pairUp_unique`,
  `mem_pairUp_or_leftover`, `not_mem_pairUp_of_leftover`);
* ranks (g): `rankIn l f e` (one more than the number of earlier entries of `l` with the same key
  `f`), injectivity on a key class (`rankIn_inj`), and the rank set of a key class is
  `{1, …, size of the class}` (`image_rankIn_eq_Icc`);
* closed walks: `cycleEdges (a :: t) = walkEdges (a :: t ++ [a])`, and the edges of a concatenation
  of segments along a cyclic list (`walkEdges_flatMap_zip`), used for the lift of cycles (h).
-/

public section

namespace EG.Quot

open Finset

/-! ## Pairing lists -/

section pairUp

variable {α : Type*}

/-- A list is the concatenation of its consecutive pairs followed by its leftover. -/
theorem pairUp_flatten_leftover (l : List α) :
    (pairUp l).flatMap (fun p => [p.1, p.2]) ++ (leftover l).toList = l := by
  induction l using pairUp.induct with
  | case1 a b t ih => simp [pairUp, leftover, ih]
  | case2 l h =>
    rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp [pairUp, leftover]
    · simp [pairUp, leftover]
    · exact absurd rfl (h a b t)

theorem mem_pairUp_or_leftover {l : List α} {x : α} (hx : x ∈ l) :
    (∃ p ∈ pairUp l, x = p.1 ∨ x = p.2) ∨ leftover l = some x := by
  rw [← pairUp_flatten_leftover l] at hx
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 h
    left
    refine ⟨p, hp, ?_⟩
    simpa using hx
  · right
    simpa [eq_comm] using h

theorem pairUp_ne : ∀ {l : List α}, l.Nodup → ∀ {p : α × α}, p ∈ pairUp l → p.1 ≠ p.2
  | a :: b :: t, hl, p, hp => by
    simp only [pairUp, List.mem_cons] at hp
    rw [List.nodup_cons, List.nodup_cons] at hl
    rcases hp with rfl | hp
    · exact fun h => hl.1 (by simp only at h; simp [h])
    · exact pairUp_ne hl.2.2 hp
  | [], _, _, hp => by simp [pairUp] at hp
  | [_], _, _, hp => by simp [pairUp] at hp

theorem pairUp_unique : ∀ {l : List α}, l.Nodup → ∀ {p p' : α × α}, p ∈ pairUp l →
    p' ∈ pairUp l → ∀ {x : α}, (x = p.1 ∨ x = p.2) → (x = p'.1 ∨ x = p'.2) → p = p'
  | a :: b :: t, hl, p, p', hp, hp', x, hx, hx' => by
    simp only [pairUp, List.mem_cons] at hp hp'
    rw [List.nodup_cons, List.nodup_cons] at hl
    have hnot : ∀ q ∈ pairUp t, x = q.1 ∨ x = q.2 → x ≠ a ∧ x ≠ b := by
      intro q hq hxq
      have hm := mem_of_mem_pairUp hq
      have hxt : x ∈ t := by rcases hxq with rfl | rfl <;> simp [hm.1, hm.2]
      exact ⟨fun h => hl.1 (by simp [← h, hxt]), fun h => hl.2.1 (h ▸ hxt)⟩
    rcases hp with rfl | hp <;> rcases hp' with rfl | hp'
    · rfl
    · exfalso
      have := hnot p' hp' hx'
      rcases hx with h | h <;> simp_all
    · exfalso
      have := hnot p hp hx
      rcases hx' with h | h <;> simp_all
    · exact pairUp_unique hl.2.2 hp hp' hx hx'
  | [], _, _, _, hp, _, _, _, _ => by simp [pairUp] at hp
  | [_], _, _, _, hp, _, _, _, _ => by simp [pairUp] at hp

theorem not_mem_pairUp_of_leftover : ∀ {l : List α}, l.Nodup → ∀ {x : α},
    leftover l = some x → ¬ ∃ p ∈ pairUp l, x = p.1 ∨ x = p.2
  | a :: b :: t, hl, x, hx, ⟨p, hp, hxp⟩ => by
    simp only [pairUp, List.mem_cons] at hp
    simp only [leftover] at hx
    rw [List.nodup_cons, List.nodup_cons] at hl
    have hxt := mem_of_leftover hx
    rcases hp with rfl | hp
    · rcases hxp with rfl | rfl
      · exact hl.1 (by simp [hxt])
      · exact hl.2.1 hxt
    · exact not_mem_pairUp_of_leftover hl.2.2 hx ⟨p, hp, hxp⟩
  | [a], _, x, _, ⟨p, hp, _⟩ => by simp [pairUp] at hp
  | [], _, x, hx, _ => by simp [leftover] at hx

end pairUp

/-! ## Ranks -/

section rank

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The rank of `e` in the list `l` for the key `f`: one more than the number of entries of `l`
before `e` with the same key (the shape of `Rules.rank`). -/
@[expose] def rankIn (l : List α) (f : α → β) (e : α) : ℕ :=
  ((l.takeWhile (fun e' => decide (e' ≠ e))).filter (fun e' => decide (f e' = f e))).length + 1

theorem rankIn_nil (f : α → β) (e : α) : rankIn [] f e = 1 := by simp [rankIn]

theorem rankIn_cons_self (l : List α) (f : α → β) (e : α) : rankIn (e :: l) f e = 1 := by
  simp [rankIn]

theorem rankIn_cons_of_ne (x : α) (l : List α) (f : α → β) {e : α} (h : x ≠ e) :
    rankIn (x :: l) f e = (if f x = f e then 1 else 0) + rankIn l f e := by
  simp only [rankIn, List.takeWhile_cons, ne_eq, h, not_false_eq_true, decide_true]
  by_cases h' : f x = f e
  · simp [h']; omega
  · simp [h']

theorem one_le_rankIn (l : List α) (f : α → β) (e : α) : 1 ≤ rankIn l f e := by
  unfold rankIn; omega

/-- Ranks are at most the size of the key class. -/
theorem rankIn_le (l : List α) (f : α → β) {e : α} (he : e ∈ l) :
    rankIn l f e ≤ (l.filter (fun x => decide (f x = f e))).length := by
  induction l with
  | nil => simp at he
  | cons x t ih =>
    by_cases hx : x = e
    · subst hx
      rw [rankIn_cons_self]
      simp
    · rw [rankIn_cons_of_ne x t f hx, List.filter_cons]
      have he' : e ∈ t := by
        rcases List.mem_cons.1 he with h | h
        · exact absurd h.symm hx
        · exact h
      have := ih he'
      split_ifs with h1 <;> simp_all <;> omega

/-- Ranks are injective on a key class of a duplicate-free list. -/
theorem rankIn_inj {l : List α} (hl : l.Nodup) (f : α → β) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hf : f a = f b) (hr : rankIn l f a = rankIn l f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.nodup_cons] at hl
    by_cases hxa : x = a
    · by_cases hxb : x = b
      · exact hxa.symm.trans hxb
      · subst hxa
        rw [rankIn_cons_self, rankIn_cons_of_ne x t f hxb, if_pos hf] at hr
        have := one_le_rankIn t f b
        omega
    · by_cases hxb : x = b
      · subst hxb
        rw [rankIn_cons_self, rankIn_cons_of_ne x t f hxa, if_pos hf.symm] at hr
        have := one_le_rankIn t f a
        omega
      · rw [rankIn_cons_of_ne x t f hxa, rankIn_cons_of_ne x t f hxb, hf] at hr
        have ha' : a ∈ t := (List.mem_cons.1 ha).resolve_left (Ne.symm hxa)
        have hb' : b ∈ t := (List.mem_cons.1 hb).resolve_left (Ne.symm hxb)
        exact ih hl.2 ha' hb' (by omega)

/-- The ranks of a key class `c` of a duplicate-free list are exactly `1, …, n`, `n` the size of
the class. -/
theorem image_rankIn_eq_Icc {l : List α} (hl : l.Nodup) (f : α → β) (c : β) :
    (l.filter (fun x => decide (f x = c))).toFinset.image (rankIn l f) =
      Icc 1 (l.filter (fun x => decide (f x = c))).length := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    rw [List.mem_toFinset, List.mem_filter] at hx
    have hfx : f x = c := by simpa using hx.2
    rw [Finset.mem_Icc]
    refine ⟨one_le_rankIn _ _ _, ?_⟩
    have := rankIn_le l f hx.1
    rw [hfx] at this
    exact this
  · rw [Nat.card_Icc, Nat.add_sub_cancel, Finset.card_image_of_injOn, List.toFinset_card_of_nodup
      (hl.filter _)]
    intro x hx y hy hxy
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter] at hx hy
    exact rankIn_inj hl f hx.1 hy.1 (by simp at hx hy; rw [hx.2, hy.2]) hxy

end rank

/-! ## Closed walks along a cyclic list -/

section walk

variable {α β : Type*}

theorem walkEdges_append_cons' (l₁ : List β) (x : β) (l₂ : List β) :
    walkEdges (l₁ ++ x :: l₂) = walkEdges (l₁ ++ [x]) ++ walkEdges (x :: l₂) := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      simp only [List.cons_append, walkEdges_cons_cons] at ih ⊢
      rw [ih]

/-- `cycleEdges (a :: t)` are the edges of the closed walk `a t a`. -/
theorem cycleEdges_cons' (a : β) (t : List β) :
    cycleEdges (a :: t) = walkEdges (a :: t ++ [a]) := by
  unfold cycleEdges walkEdges
  rw [List.rotate_cons_succ, List.rotate_zero]
  simp only [List.tail_cons, List.cons_append]
  have h : (a :: (t ++ [a])) = (a :: t) ++ [a] := by simp
  rw [h, show t ++ [a] = (t ++ [a]) ++ [] by simp, List.zipWith_append (by simp)]
  simp

theorem rotate_one_cons (a : α) (t : List α) : (a :: t).rotate 1 = t ++ [a] := by
  rw [List.rotate_cons_succ, List.rotate_zero]

/-- The walk obtained by concatenating the segments `g x :: T x y` along the consecutive pairs
`(x, y)` of `x :: t ++ [z]`, closed by `g z`: its edges are the edges of the segments, each closed
by the head `g y` of the next one. -/
theorem walkEdges_flatMap_zip (g : α → β) (T : α → α → List β) :
    ∀ (x : α) (t : List α) (z : α),
      walkEdges ((List.zip (x :: t) (t ++ [z])).flatMap (fun p => g p.1 :: T p.1 p.2) ++ [g z]) =
        (List.zip (x :: t) (t ++ [z])).flatMap
          (fun p => walkEdges (g p.1 :: T p.1 p.2 ++ [g p.2]))
  | x, [], z => by simp
  | x, y :: t, z => by
    have ih := walkEdges_flatMap_zip g T y t z
    have hz : List.zip (x :: y :: t) (y :: t ++ [z]) =
        (x, y) :: List.zip (y :: t) (t ++ [z]) := by simp
    have hs : List.zip (y :: t) (t ++ [z]) = (y, (t ++ [z]).head (by simp)) ::
        List.zip t ((t ++ [z]).tail) := by
      cases t <;> simp
    rw [hz, List.flatMap_cons, List.flatMap_cons, List.append_assoc]
    have hM : (List.zip (y :: t) (t ++ [z])).flatMap (fun p => g p.1 :: T p.1 p.2) ++ [g z] =
        g y :: (T y ((t ++ [z]).head (by simp)) ++
          ((List.zip t ((t ++ [z]).tail)).flatMap (fun p => g p.1 :: T p.1 p.2) ++ [g z])) := by
      rw [hs]; simp
    rw [hM, show g x :: T x y ++ g y :: (T y ((t ++ [z]).head (by simp)) ++
        ((List.zip t ((t ++ [z]).tail)).flatMap (fun p => g p.1 :: T p.1 p.2) ++ [g z])) =
        (g x :: T x y) ++ g y :: (T y ((t ++ [z]).head (by simp)) ++
        ((List.zip t ((t ++ [z]).tail)).flatMap (fun p => g p.1 :: T p.1 p.2) ++ [g z])) by simp,
      walkEdges_append_cons', ← hM, ih]

/-- The closed walk of a cyclic list of segments: `cycleEdges` of the concatenation of the
segments `g x :: T x y` over the consecutive pairs `(x, y)` of the cyclic list `c` are the edges of
the segments, each closed by `g y`. -/
theorem cycleEdges_flatMap_zip (g : α → β) (T : α → α → List β) (c : List α) :
    cycleEdges ((List.zip c (c.rotate 1)).flatMap (fun p => g p.1 :: T p.1 p.2)) =
      (List.zip c (c.rotate 1)).flatMap (fun p => walkEdges (g p.1 :: T p.1 p.2 ++ [g p.2])) := by
  rcases c with _ | ⟨a, t⟩
  · simp [cycleEdges]
  · rw [rotate_one_cons]
    have hz : List.zip (a :: t) (t ++ [a]) = (a, (t ++ [a]).head (by simp)) ::
        List.zip t ((t ++ [a]).tail) := by
      cases t <;> simp
    have hL : (List.zip (a :: t) (t ++ [a])).flatMap (fun p => g p.1 :: T p.1 p.2) =
        g a :: (T a ((t ++ [a]).head (by simp)) ++
          (List.zip t ((t ++ [a]).tail)).flatMap (fun p => g p.1 :: T p.1 p.2)) := by
      rw [hz]; simp
    rw [hL, cycleEdges_cons', ← hL]
    exact walkEdges_flatMap_zip g T a t a

/-- Propagation along the consecutive pairs of a cyclic list. -/
theorem forall_eq_of_zip_rotate (f : α → β) :
    ∀ (x : α) (t : List α) (z : α), (∀ p ∈ List.zip (x :: t) (t ++ [z]), f p.1 = f p.2) →
      ∀ y ∈ x :: t, f y = f x
  | x, [], z, _, y, hy => by rw [List.mem_singleton.1 hy]
  | x, y₀ :: t, z, h, y, hy => by
    have h0 : f x = f y₀ := h (x, y₀) (by simp)
    have ih := forall_eq_of_zip_rotate f y₀ t z (fun p hp => h p (by simp [hp]))
    rcases List.mem_cons.1 hy with rfl | hy
    · rfl
    · rw [ih y hy, h0]

theorem forall_eq_of_zip_rotate_one (f : α → β) {c : List α}
    (h : ∀ p ∈ List.zip c (c.rotate 1), f p.1 = f p.2) {a : α} (ha : a ∈ c) :
    ∀ y ∈ c, f y = f a := by
  rcases c with _ | ⟨x, t⟩
  · simp at ha
  · rw [rotate_one_cons] at h
    intro y hy
    rw [forall_eq_of_zip_rotate f x t x h y hy, forall_eq_of_zip_rotate f x t x h a ha]

theorem map_fst_zip_rotate (c : List α) : (List.zip c (c.rotate 1)).map Prod.fst = c :=
  List.map_fst_zip (by simp)

theorem cycleEdges_eq_map_zip (c : List α) :
    cycleEdges c = (List.zip c (c.rotate 1)).map (fun p => s(p.1, p.2)) := by
  unfold cycleEdges
  rw [List.map_zip_eq_zipWith]
  rfl

theorem length_zip_rotate (c : List α) : (List.zip c (c.rotate 1)).length = c.length := by
  simp

theorem two_mul_le_length_flatMap {l : List α} {F : α → List β} (h : ∀ x ∈ l, 2 ≤ (F x).length) :
    2 * l.length ≤ (l.flatMap F).length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

end walk

end EG.Quot
