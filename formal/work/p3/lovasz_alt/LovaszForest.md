# LovaszForest.lean (archived, unused alternative Lovász route; not built)

```lean
module

public import EG.Lib.Ext.LovaszBasic

/-!
# Lovász's theorem: arms at a vertex and the in-forest of arms (manuscript s1:citThm21)

Helper file for `EG.Spec.LovaszStatement` (proof outline: `formal/work/p3/s1.md`, Round 2,
step 3). Fix a path-and-cycle decomposition `(P, C)` of `F` and a vertex `x`. A path
`p = L ++ x :: R` of `P` through `x` has the *arm* `R` attached at `u = R.head` (free end
`R.last`) and the arm `L.reverse` attached at `u = L.last` (free end `L.head`):
`ArmTo P x u t`. Arms are functional (`armTo_unique`); `succ P x u` is the free end of the arm
at `u`. Vertices `b` with `s(x, b) ∉ F` have no arm (roots). Descending from a root along arms
(`exists_chain`) one reaches a *live* vertex (an end of a path avoiding `x`), provided every
vertex met is an end of some path; chains of different roots are disjoint (`reach_root_unique`).
-/

public section

namespace EG

namespace Lov

open Cor22

variable {V : Type*} [DecidableEq V]

/-! ### Splitting a path at `x` -/

/-- The part of `p` before the first `x`. -/
@[expose] def lpart (x : V) (p : List V) : List V := p.takeWhile (fun y => y ≠ x)

/-- The part of `p` after the first `x`. -/
@[expose] def rpart (x : V) (p : List V) : List V := (p.dropWhile (fun y => y ≠ x)).tail

theorem lpart_append {x : V} {L : List V} (hx : x ∉ L) (R : List V) :
    lpart x (L ++ x :: R) = L := by
  unfold lpart
  rw [List.takeWhile_append_of_pos (by
      intro a ha
      simp only [ne_eq, decide_eq_true_eq]
      rintro rfl; exact hx ha),
    List.takeWhile_cons_of_neg (by simp), List.append_nil]

theorem rpart_append {x : V} {L : List V} (hx : x ∉ L) (R : List V) :
    rpart x (L ++ x :: R) = R := by
  unfold rpart
  rw [List.dropWhile_append_of_pos (by
      intro a ha
      simp only [ne_eq, decide_eq_true_eq]
      rintro rfl; exact hx ha),
    List.dropWhile_cons_of_neg (by simp)]
  rfl

theorem exists_split {x : V} : ∀ {p : List V}, x ∈ p → ∃ L R, p = L ++ x :: R ∧ x ∉ L
  | a :: t, h => by
    by_cases hax : a = x
    · subst hax; exact ⟨[], t, rfl, by simp⟩
    · have ht : x ∈ t := (List.mem_cons.1 h).resolve_left (Ne.symm hax)
      obtain ⟨L, R, hLR, hxL⟩ := exists_split ht
      refine ⟨a :: L, R, by rw [hLR]; rfl, ?_⟩
      rw [List.mem_cons, not_or]
      exact ⟨Ne.symm hax, hxL⟩

theorem split_eq {x : V} {p : List V} (hx : x ∈ p) : p = lpart x p ++ x :: rpart x p := by
  obtain ⟨L, R, rfl, hxL⟩ := exists_split hx
  rw [lpart_append hxL, rpart_append hxL]

theorem split_unique {x : V} {L R L' R' : List V} (hL : x ∉ L) (hL' : x ∉ L')
    (h : L ++ x :: R = L' ++ x :: R') : L = L' ∧ R = R' := by
  have h1 := lpart_append hL R
  have h2 := rpart_append hL R
  rw [h, lpart_append hL'] at h1
  rw [h, rpart_append hL'] at h2
  exact ⟨h1.symm, h2.symm⟩

theorem not_mem_of_nodup_split {x : V} {L R : List V} (h : (L ++ x :: R).Nodup) : x ∉ L := by
  intro hx
  rw [List.nodup_append] at h
  exact h.2.2 x hx x (List.mem_cons_self ..) rfl

theorem not_mem_right_of_nodup_split {x : V} {L R : List V} (h : (L ++ x :: R).Nodup) :
    x ∉ R := by
  rw [List.nodup_append] at h
  exact (List.nodup_cons.1 h.2.1).1

theorem disjoint_of_nodup_split {x : V} {L R : List V} (h : (L ++ x :: R).Nodup) {u : V}
    (hL : u ∈ L) (hR : u ∈ R) : False := by
  rw [List.nodup_append] at h
  exact h.2.2 u hL u (List.mem_cons_of_mem _ hR) rfl

omit [DecidableEq V] in
theorem head?_split (L R : List V) (x : V) :
    (L ++ x :: R).head? = if L = [] then some x else L.head? := by
  cases L <;> simp

omit [DecidableEq V] in
theorem getLast?_split (L R : List V) (x : V) :
    (L ++ x :: R).getLast? = if R = [] then some x else R.getLast? := by
  rw [List.getLast?_append]
  cases R with
  | nil => simp
  | cons b R => simp [List.getLast?_cons]

/-! ### Paths through an edge -/

omit [DecidableEq V] in
theorem eq_of_mem_walkEdges {P : List (List V)} (hnd : (P.flatMap walkEdges).Nodup)
    {p p' : List V} (hp : p ∈ P) (hp' : p' ∈ P) {e : Sym2 V} (he : e ∈ walkEdges p)
    (he' : e ∈ walkEdges p') : p = p' := by
  by_contra hne
  rw [List.nodup_flatMap] at hnd
  haveI : Std.Symm (Function.onFun List.Disjoint (walkEdges (V := V))) :=
    ⟨fun a b h => List.disjoint_comm.1 h⟩
  have := hnd.2.forall hp hp' hne
  exact this he he'

omit [DecidableEq V] in
theorem nodup_of_flatMap {P : List (List V)} (hnd : (P.flatMap walkEdges).Nodup)
    (hne : ∀ p ∈ P, walkEdges p ≠ []) : P.Nodup := by
  rw [List.nodup_flatMap] at hnd
  unfold List.Nodup
  rw [List.pairwise_iff_forall_sublist]
  intro a b hab
  have hd := List.pairwise_iff_forall_sublist.1 hnd.2 hab
  rintro rfl
  have ha : a ∈ P := hab.subset (List.mem_cons_self ..)
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hne a ha)
  exact hd he he

omit [DecidableEq V] in
theorem walkEdges_ne_nil {p : List V} (h : 2 ≤ p.length) : walkEdges p ≠ [] := by
  match p, h with
  | a :: b :: t, _ => simp

theorem nodup_P {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) : P.Nodup :=
  nodup_of_flatMap (List.nodup_append.1 h.2.2.1).1 (fun p hp => walkEdges_ne_nil (h.1 p hp).1)

omit [DecidableEq V] in
theorem mem_walkEdges_split_right (L R : List V) (x u : V) (hu : R.head? = some u) :
    s(x, u) ∈ walkEdges (L ++ x :: R) := by
  match R, hu with
  | u' :: R', hu =>
    have : u' = u := by simpa using hu
    subst this
    rw [walkEdges_append_cons, walkEdges_cons_cons]
    exact List.mem_append_right _ (List.mem_cons_self ..)

omit [DecidableEq V] in
theorem mem_walkEdges_split_left (L R : List V) (x u : V) (hu : L.getLast? = some u) :
    s(x, u) ∈ walkEdges (L ++ x :: R) := by
  rw [walkEdges_append_cons, walkEdges_concat, hu]
  simp [Sym2.eq_swap]

/-! ### Arms -/

/-- `ArmTo P x u t`: the arm of a path of `P` through `x` attached at `u` has free end `t`. -/
@[expose] def ArmTo (P : List (List V)) (x u t : V) : Prop :=
  ∃ p ∈ P, ∃ L R : List V, p = L ++ x :: R ∧
    ((R.head? = some u ∧ R.getLast? = some t) ∨ (L.getLast? = some u ∧ L.head? = some t))

theorem armTo_mem_walkEdges {P : List (List V)} {x u t : V} (h : ArmTo P x u t) :
    ∃ p ∈ P, s(x, u) ∈ walkEdges p := by
  obtain ⟨p, hp, L, R, rfl, hs | hs⟩ := h
  · exact ⟨_, hp, mem_walkEdges_split_right L R x u hs.1⟩
  · exact ⟨_, hp, mem_walkEdges_split_left L R x u hs.1⟩

theorem armTo_mem {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x u t : V} (ha : ArmTo P x u t) :
    s(x, u) ∈ F := by
  obtain ⟨p, hp, he⟩ := armTo_mem_walkEdges ha
  exact (h.2.2.2 _).1 (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, he⟩))

theorem armTo_unique {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x u t t' : V}
    (ha : ArmTo P x u t) (ha' : ArmTo P x u t') : t = t' := by
  obtain ⟨p, hp, L, R, hpLR, hs⟩ := ha
  obtain ⟨p', hp', L', R', hpLR', hs'⟩ := ha'
  have hnd := (List.nodup_append.1 h.2.2.1).1
  have he : s(x, u) ∈ walkEdges p := by
    rw [hpLR]
    rcases hs with hs | hs
    · exact mem_walkEdges_split_right L R x u hs.1
    · exact mem_walkEdges_split_left L R x u hs.1
  have he' : s(x, u) ∈ walkEdges p' := by
    rw [hpLR']
    rcases hs' with hs' | hs'
    · exact mem_walkEdges_split_right L' R' x u hs'.1
    · exact mem_walkEdges_split_left L' R' x u hs'.1
  have hpp := eq_of_mem_walkEdges hnd hp hp' he he'
  subst hpp
  have hpn := (h.1 p hp).2
  rw [hpLR] at hpn
  obtain ⟨rfl, rfl⟩ := split_unique (not_mem_of_nodup_split hpn)
    (not_mem_of_nodup_split (hpLR' ▸ hpLR ▸ hpn)) (hpLR.symm.trans hpLR')
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact Option.some.inj (h2.symm.trans h2')
  · exact (disjoint_of_nodup_split hpn (List.mem_of_getLast? h1')
      (List.mem_of_mem_head? h1)).elim
  · exact (disjoint_of_nodup_split hpn (List.mem_of_getLast? h1)
      (List.mem_of_mem_head? h1')).elim
  · exact Option.some.inj (h2.symm.trans h2')

/-- A path through `x` ending at `v ≠ x` makes `v` the free end of an arm. -/
theorem end_cases {P : List (List V)} {x v : V} (hv : v ≠ x) {p : List V} (hp : p ∈ P)
    (hend : p.head? = some v ∨ p.getLast? = some v) :
    (x ∉ p) ∨ ∃ u, ArmTo P x u v := by
  by_cases hx : x ∈ p
  · right
    obtain ⟨L, R, rfl, -⟩ := exists_split hx
    rcases hend with hend | hend
    · rw [head?_split] at hend
      split_ifs at hend with hL
      · exact absurd (Option.some.inj hend).symm hv
      · obtain ⟨u, hu⟩ : ∃ u, L.getLast? = some u :=
          ⟨L.getLast hL, List.getLast?_eq_some_getLast hL⟩
        exact ⟨u, _, hp, L, R, rfl, Or.inr ⟨hu, hend⟩⟩
    · rw [getLast?_split] at hend
      split_ifs at hend with hR
      · exact absurd (Option.some.inj hend).symm hv
      · obtain ⟨u, hu⟩ : ∃ u, R.head? = some u := by
          cases R with
          | nil => exact absurd rfl hR
          | cons b _ => exact ⟨b, rfl⟩
        exact ⟨u, _, hp, L, R, rfl, Or.inl ⟨hu, hend⟩⟩
  · exact Or.inl hx

/-! ### The successor map and its iterates -/

/-- The free end of the arm attached at `u` (if any). -/
noncomputable def succ (P : List (List V)) (x u : V) : Option V := by
  classical
  exact if h : ∃ t, ArmTo P x u t then some h.choose else none

theorem succ_eq_some {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x u t : V} :
    succ P x u = some t ↔ ArmTo P x u t := by
  unfold succ
  split_ifs with hex
  · rw [Option.some.injEq]
    exact ⟨fun ht => ht ▸ hex.choose_spec, fun ht => armTo_unique h hex.choose_spec ht⟩
  · exact ⟨fun h' => absurd h' (by simp), fun ht => absurd ⟨t, ht⟩ hex⟩

/-- Iterates of `succ`. -/
@[expose] noncomputable def iterS (P : List (List V)) (x : V) : ℕ → V → Option V
  | 0, v => some v
  | k + 1, v => (iterS P x k v).bind (succ P x)

theorem iterS_zero (P : List (List V)) (x v : V) : iterS P x 0 v = some v := rfl

theorem iterS_succ (P : List (List V)) (x : V) (k : ℕ) (v : V) :
    iterS P x (k + 1) v = (iterS P x k v).bind (succ P x) := rfl

theorem iterS_add (P : List (List V)) (x : V) (a c : ℕ) (v : V) :
    iterS P x (a + c) v = (iterS P x a v).bind (iterS P x c) := by
  induction c with
  | zero => cases iterS P x a v <;> rfl
  | succ c ih =>
    rw [← Nat.add_assoc, iterS_succ, ih, Option.bind_assoc]
    rfl

theorem iterS_one (P : List (List V)) (x v : V) : iterS P x 1 v = succ P x v := rfl

theorem iterS_none_add {P : List (List V)} {x v : V} {k : ℕ} (h : iterS P x k v = none) (c : ℕ) :
    iterS P x (k + c) v = none := by
  rw [iterS_add, h]; rfl

theorem iterS_root {P : List (List V)} {x b : V} (hb : succ P x b = none) (c : ℕ) :
    iterS P x (c + 1) b = none := by
  rw [Nat.add_comm, iterS_add, iterS_one, hb]; rfl

/-- `v` reaches `b` along arms. -/
@[expose] def Reach (P : List (List V)) (x v b : V) : Prop := ∃ k, iterS P x k v = some b

theorem reach_refl (P : List (List V)) (x v : V) : Reach P x v v := ⟨0, rfl⟩

theorem reach_step {P : List (List V)} {x u t b : V} (hu : succ P x u = some t)
    (ht : Reach P x t b) : Reach P x u b := by
  obtain ⟨k, hk⟩ := ht
  refine ⟨1 + k, ?_⟩
  rw [iterS_add, iterS_one, hu]
  exact hk

theorem reach_trans {P : List (List V)} {x u t b : V} (hut : Reach P x u t)
    (ht : Reach P x t b) : Reach P x u b := by
  obtain ⟨k, hk⟩ := hut
  obtain ⟨k', hk'⟩ := ht
  refine ⟨k + k', ?_⟩
  rw [iterS_add, hk]
  exact hk'

/-- A vertex reaching a root reaches it in a unique number of steps, and reaches no other root. -/
theorem reach_root_unique {P : List (List V)} {x v b b' : V} (hb : succ P x b = none)
    (hb' : succ P x b' = none) {k k' : ℕ} (hk : iterS P x k v = some b)
    (hk' : iterS P x k' v = some b') : k = k' ∧ b = b' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [show k + c + 1 = k + (c + 1) by omega, iterS_add, hk, Option.bind_some,
      iterS_root hb] at hk'
    exact absurd hk' (by simp)
  · subst heq
    exact ⟨rfl, Option.some.inj (hk.symm.trans hk')⟩
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    rw [show k' + c + 1 = k' + (c + 1) by omega, iterS_add, hk', Option.bind_some,
      iterS_root hb'] at hk
    exact absurd hk (by simp)

/-- No vertex reaching a root lies on a cycle of arms. -/
theorem not_cycle {P : List (List V)} {x v b : V} (hb : succ P x b = none) (hv : Reach P x v b)
    {m : ℕ} (hm : iterS P x (m + 1) v = some v) : False := by
  obtain ⟨k, hk⟩ := hv
  have hper : ∀ j, iterS P x ((m + 1) * j) v = some v := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Nat.mul_succ, iterS_add, ih, Option.bind_some, hm]
  have hnone : iterS P x (k + 1) v = none := by
    rw [iterS_add, hk, Option.bind_some, iterS_one, hb]
  have hge : k + 1 ≤ (m + 1) * (k + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos m)
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hge
  have := iterS_none_add hnone c
  rw [← hc, hper] at this
  exact absurd this (by simp)

/-! ### Live vertices and chains -/

/-- `v` is an end of a path of `P` avoiding `x`. -/
@[expose] def Live (P : List (List V)) (x v : V) : Prop :=
  ∃ q ∈ P, x ∉ q ∧ (q.head? = some v ∨ q.getLast? = some v)

/-- The chain relation: consecutive `a, c` with `c`'s arm ending at `a`. -/
@[expose] def ChainRel (P : List (List V)) (x : V) (a c : V) : Prop := succ P x c = some a

theorem chain_reach {P : List (List V)} {x : V} :
    ∀ {l : List V}, List.IsChain (ChainRel P x) l → ∀ {a : V}, l.head? = some a →
      ∀ v ∈ l, Reach P x v a
  | [], _, _, _, v, hv => by simp at hv
  | [c], _, a, ha, v, hv => by
    have : c = a := by simpa using ha
    rw [List.mem_singleton] at hv
    subst hv; subst this; exact reach_refl _ _ _
  | c :: d :: t, hl, a, ha, v, hv => by
    have hca : c = a := by simpa using ha
    subst hca
    rw [List.isChain_cons_cons] at hl
    rcases List.mem_cons.1 hv with rfl | hv
    · exact reach_refl _ _ _
    · exact reach_trans (chain_reach hl.2 rfl v hv) (reach_step hl.1 (reach_refl _ _ _))

theorem chain_nodup {P : List (List V)} {x b : V} (hb : succ P x b = none) :
    ∀ {l : List V}, List.IsChain (ChainRel P x) l → (∀ v ∈ l, Reach P x v b) → l.Nodup
  | [], _, _ => List.nodup_nil
  | [c], _, _ => List.nodup_singleton c
  | c :: d :: t, hl, hr => by
    rw [List.isChain_cons_cons] at hl
    have ih := chain_nodup hb hl.2 (fun v hv => hr v (List.mem_cons_of_mem _ hv))
    refine List.nodup_cons.2 ⟨fun hc => ?_, ih⟩
    -- `c` lies below `d`, and `d`'s arm ends at `c`: a cycle
    obtain ⟨k, hk⟩ := chain_reach hl.2 rfl c hc
    have hcyc : iterS P x (k + 1) c = some c := by
      rw [iterS_succ, hk]
      exact hl.1
    exact not_cycle hb (hr c (List.mem_cons_self ..)) hcyc

theorem chain_tail_map {P : List (List V)} {x : V} (f : V → V) (hf : ∀ u a, succ P x u = some a → f u = a) :
    ∀ {l : List V}, List.IsChain (ChainRel P x) l → l.tail.map f = l.dropLast
  | [], _ => rfl
  | [c], _ => rfl
  | c :: d :: t, hl => by
    rw [List.isChain_cons_cons] at hl
    have ih := chain_tail_map f hf hl.2
    rw [List.tail_cons, List.map_cons, List.dropLast_cons₂, hf d c hl.1]
    rw [List.tail_cons] at ih
    cases t with
    | nil => rfl
    | cons e t => rw [ih]

/-- Descent from a root to a live vertex. -/
theorem exists_chain {F : Finset (Sym2 V)} {P C : List (List V)}
    (h : IsPathCycleDecomp (F : Set (Sym2 V)) P C) {x b : V} (hb : succ P x b = none)
    (hend : ∀ t, Reach P x t b → t ≠ x ∧ ∃ p ∈ P, p.head? = some t ∨ p.getLast? = some t) :
    ∃ l : List V, l.head? = some b ∧ List.IsChain (ChainRel P x) l ∧
      ∃ c, l.getLast? = some c ∧ Live P x c := by
  classical
  set Nf : Finset V := insert b (edgeVerts F) with hNf
  let D : V → Finset V := fun t => Nf.filter (fun u => u ≠ t ∧ Reach P x u t)
  suffices H : ∀ n t, Reach P x t b → (D t).card ≤ n → ∃ l : List V, l.head? = some t ∧
      List.IsChain (ChainRel P x) l ∧ ∃ c, l.getLast? = some c ∧ Live P x c from
    H _ b (reach_refl _ _ _) le_rfl
  intro n
  induction n with
  | zero =>
    intro t ht hD
    by_cases hlive : Live P x t
    · exact ⟨[t], rfl, List.isChain_singleton _, t, rfl, hlive⟩
    · exfalso
      obtain ⟨htx, p, hp, hpe⟩ := hend t ht
      rcases end_cases htx hp hpe with hxp | ⟨u, hu⟩
      · exact hlive ⟨p, hp, hxp, hpe⟩
      · have hsu : succ P x u = some t := (succ_eq_some h).2 hu
        have hut : u ≠ t := by
          rintro rfl
          exact not_cycle hb ht (m := 0) (by rw [iterS_one]; exact hsu)
        have huD : u ∈ D t := by
          refine Finset.mem_filter.2 ⟨?_, hut, reach_step hsu (reach_refl _ _ _)⟩
          exact Finset.mem_insert_of_mem (mem_edgeVerts.2 ⟨_, armTo_mem h hu,
            Sym2.mem_mk_right _ _⟩)
        have := Finset.card_pos.2 ⟨u, huD⟩
        omega
  | succ n ih =>
    intro t ht hD
    by_cases hlive : Live P x t
    · exact ⟨[t], rfl, List.isChain_singleton _, t, rfl, hlive⟩
    · obtain ⟨htx, p, hp, hpe⟩ := hend t ht
      rcases end_cases htx hp hpe with hxp | ⟨u, hu⟩
      · exact absurd ⟨p, hp, hxp, hpe⟩ hlive
      · have hsu : succ P x u = some t := (succ_eq_some h).2 hu
        have hut : u ≠ t := by
          rintro rfl
          exact not_cycle hb ht (m := 0) (by rw [iterS_one]; exact hsu)
        have hub : Reach P x u b := reach_step hsu ht
        have huD : u ∈ D t := by
          refine Finset.mem_filter.2 ⟨?_, hut, reach_step hsu (reach_refl _ _ _)⟩
          exact Finset.mem_insert_of_mem (mem_edgeVerts.2 ⟨_, armTo_mem h hu,
            Sym2.mem_mk_right _ _⟩)
        have hsub : D u ⊆ D t := by
          intro w hw
          obtain ⟨hwN, hwu, hwr⟩ := Finset.mem_filter.1 hw
          refine Finset.mem_filter.2 ⟨hwN, ?_, reach_trans hwr (reach_step hsu (reach_refl _ _ _))⟩
          rintro rfl
          obtain ⟨k, hk⟩ := hwr
          cases k with
          | zero => exact hwu (Option.some.inj hk)
          | succ k =>
            refine not_cycle hb ht (m := k + 1) ?_
            rw [iterS_succ, hk]
            exact hsu
        have hlt : (D u).card < (D t).card := by
          refine Finset.card_lt_card ⟨hsub, fun hts => ?_⟩
          have := hts huD
          exact (Finset.mem_filter.1 this).2.1 rfl
        obtain ⟨l, hl1, hl2, c, hc, hlc⟩ := ih u hub (by omega)
        refine ⟨t :: l, rfl, ?_, c, ?_, hlc⟩
        · cases l with
          | nil => simp at hl1
          | cons d l =>
            have hdu : d = u := by simpa using hl1
            subst hdu
            exact List.IsChain.cons_cons hsu hl2
        · cases l with
          | nil => simp at hl1
          | cons d l => rw [List.getLast?_cons_cons]; exact hc

end Lov

end EG
```
