module

public import EG.Defs.Probe.P4B.Trail
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Chain
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Euler circuits in multigraphs with loops (manuscript s1:citEuler (b))

Proof of `EG.Spec.EulerMultiStatement` (used by `EG.eulerMulti`): "A connected graph (or
multigraph) in which every vertex has even degree has a closed trail using every edge exactly
once." Standard maximal-trail argument:

* a longest trail `W` (open: consecutive oriented edges match, `IsTrailIn`) exists, since trails
  have at most `|E|` edges;
* it is closed: every edge at its last vertex `z` is used (otherwise `W` extends), and the
  parity of the edge-end incidences at `z` (`even_sum_inc_add`) then forces the first vertex to be
  `z`;
* every edge at a vertex of `W` is used (rotate `W` to start there and extend otherwise);
* by connectivity every edge has an end on `W`.
-/

public section

namespace EG.MTrail.EulerProof

variable {N ι : Type*}

/-- Consecutive oriented edges match. -/
def Link (ends : ι → N × N) (p q : ι × Bool) : Prop := oTgt ends p = oSrc ends q

/-- An (open) trail of the multigraph `(E, ends)`: distinct edges of `E`, consecutive oriented
edges matching. -/
def IsTrailIn (E : Finset ι) (ends : ι → N × N) (W : List (ι × Bool)) : Prop :=
  (W.map Prod.fst).Nodup ∧ W.IsChain (Link ends) ∧ ∀ p ∈ W, p.1 ∈ E

theorem transitions_cons (ends : ι → N × N) (a : ι × Bool) (l : List (ι × Bool)) :
    transitions ends (a :: l) =
      List.zipWith (fun p q => (oTgt ends p, oSrc ends q)) (a :: l) (l ++ [a]) := by
  unfold transitions
  rw [List.rotate_cons_succ, List.rotate_zero]

/-- The transitions of `a :: l` against `l ++ [x]` all match iff `a :: l` is a chain and its last
oriented edge links to `x`. -/
theorem forall_zipWith_iff (ends : ι → N × N) (x : ι × Bool) :
    ∀ (a : ι × Bool) (l : List (ι × Bool)),
      (∀ t ∈ List.zipWith (fun p q => (oTgt ends p, oSrc ends q)) (a :: l) (l ++ [x]),
          t.1 = t.2) ↔
        (a :: l).IsChain (Link ends) ∧ Link ends ((a :: l).getLast (List.cons_ne_nil _ _)) x
  | a, [] => by simp [Link]
  | a, b :: l => by
    have ih := forall_zipWith_iff ends x b l
    simp only [List.cons_append, List.zipWith_cons_cons, List.mem_cons, forall_eq_or_imp,
      List.isChain_cons_cons, List.getLast_cons_cons] at ih ⊢
    rw [ih]
    simp only [Link]
    tauto

theorem isClosedTrail_iff {ends : ι → N × N} {a : ι × Bool} {l : List (ι × Bool)} :
    IsClosedTrail ends (a :: l) ↔ ((a :: l).map Prod.fst).Nodup ∧
      (a :: l).IsChain (Link ends) ∧ Link ends ((a :: l).getLast (List.cons_ne_nil _ _)) a := by
  unfold IsClosedTrail
  rw [transitions_cons, forall_zipWith_iff]
  simp

/-- Rotating a closed trail gives a closed trail. -/
theorem isClosedTrail_rotate {ends : ι → N × N} {W : List (ι × Bool)}
    (h : IsClosedTrail ends W) (n : ℕ) : IsClosedTrail ends (W.rotate n) := by
  obtain ⟨hne, hnd, ht⟩ := h
  refine ⟨fun h => hne (List.rotate_eq_nil_iff.1 h), ?_, ?_⟩
  · rw [List.map_rotate]; exact List.nodup_rotate.2 hnd
  · intro t htm
    unfold transitions at htm
    rw [List.rotate_rotate, add_comm, ← List.rotate_rotate,
      ← List.zipWith_rotate_distrib _ _ _ _ (by simp), List.mem_rotate] at htm
    exact ht t htm

/-- Each oriented edge of a closed trail ends where some oriented edge of it starts. -/
theorem exists_src_eq_tgt_of_closed {ends : ι → N × N} {W : List (ι × Bool)}
    (h : IsClosedTrail ends W) {p : ι × Bool} (hp : p ∈ W) :
    ∃ q ∈ W, oSrc ends q = oTgt ends p := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hlen : (transitions ends W).length = W.length := by
    unfold transitions; simp
  have hti : (transitions ends W)[i]'(by omega) ∈ transitions ends W := List.getElem_mem _
  have := h.2.2 _ hti
  unfold transitions at this
  rw [List.getElem_zipWith] at this
  exact ⟨(W.rotate 1)[i]'(by simp; omega), List.mem_rotate.1 (List.getElem_mem _), this.symm⟩

variable [DecidableEq ι]

theorem IsTrailIn.length_le {E : Finset ι} {ends : ι → N × N} {W : List (ι × Bool)}
    (h : IsTrailIn E ends W) : W.length ≤ E.card := by
  have hsub : (W.map Prod.fst).toFinset ⊆ E := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 he)
    exact h.2.2 p hp
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup h.1, List.length_map] at this

omit [DecidableEq ι] in
/-- Appending an unused edge of `E` that starts where the trail ends. -/
theorem IsTrailIn.append_single {E : Finset ι} {ends : ι → N × N} {W : List (ι × Bool)}
    (h : IsTrailIn E ends W) {p : ι × Bool} (hpE : p.1 ∈ E) (hpW : p.1 ∉ W.map Prod.fst)
    (hlink : ∀ z ∈ W.getLast?, Link ends z p) : IsTrailIn E ends (W ++ [p]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨h.1, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    rw [List.map_singleton, List.mem_singleton] at hb
    apply hpW
    rw [← hb, ← hab]
    exact ha
  · exact h.2.1.append (List.isChain_singleton p) (by simpa using hlink)
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact h.2.2 q hq
    · rw [List.mem_singleton] at hq; exact hq ▸ hpE

/-! ### Parity -/

variable [DecidableEq N]

/-- Edge-end incidences of an oriented edge at `x` (independent of the orientation). -/
def inc (ends : ι → N × N) (x : N) (p : ι × Bool) : ℕ :=
  (if oSrc ends p = x then 1 else 0) + (if oTgt ends p = x then 1 else 0)

omit [DecidableEq ι] in
theorem inc_eq (ends : ι → N × N) (x : N) (p : ι × Bool) :
    inc ends x p = (if (ends p.1).1 = x then 1 else 0) + (if (ends p.1).2 = x then 1 else 0) := by
  unfold inc oSrc oTgt
  cases p.2 <;> simp [add_comm]

omit [DecidableEq ι] in
theorem even_sum_inc_add (ends : ι → N × N) (x : N) :
    ∀ (a : ι × Bool) (l : List (ι × Bool)), (a :: l).IsChain (Link ends) →
      Even (((a :: l).map (inc ends x)).sum + (if oSrc ends a = x then 1 else 0) +
        (if oTgt ends ((a :: l).getLast (List.cons_ne_nil _ _)) = x then 1 else 0))
  | a, [], _ => by
    by_cases h1 : oSrc ends a = x <;> by_cases h2 : oTgt ends a = x <;>
      simp [h1, h2, inc, Nat.even_iff]
  | a, b :: l, h => by
    rw [List.isChain_cons_cons] at h
    have ih := even_sum_inc_add ends x b l h.2
    have hab : oTgt ends a = oSrc ends b := h.1
    rw [List.getLast_cons_cons]
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    unfold inc at ih ⊢
    rw [hab]
    rw [Nat.even_iff] at ih ⊢
    omega

theorem sum_inc_eq {E : Finset ι} {ends : ι → N × N} {W : List (ι × Bool)}
    (hnd : (W.map Prod.fst).Nodup) (hW : ∀ p ∈ W, p.1 ∈ E) (x : N)
    (hall : ∀ e ∈ E, ((ends e).1 = x ∨ (ends e).2 = x) → e ∈ W.map Prod.fst) :
    (W.map (inc ends x)).sum = mdeg E ends x := by
  have h1 : (W.map (inc ends x)).sum =
      ((W.map Prod.fst).map fun e =>
        (if (ends e).1 = x then 1 else 0) + (if (ends e).2 = x then 1 else 0)).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun p _ => inc_eq ends x p
  rw [h1, ← List.sum_toFinset _ hnd, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  unfold mdeg
  have hS : (W.map Prod.fst).toFinset ⊆ E := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 he)
    exact hW p hp
  have e1 : (W.map Prod.fst).toFinset.filter (fun e => (ends e).1 = x) =
      E.filter (fun e => (ends e).1 = x) := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hS h.1, h.2⟩, fun h => ⟨List.mem_toFinset.2 (hall e h.1 (Or.inl h.2)), h.2⟩⟩
  have e2 : (W.map Prod.fst).toFinset.filter (fun e => (ends e).2 = x) =
      E.filter (fun e => (ends e).2 = x) := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hS h.1, h.2⟩, fun h => ⟨List.mem_toFinset.2 (hall e h.1 (Or.inr h.2)), h.2⟩⟩
  rw [e1, e2, Nat.cast_id, Nat.cast_id]

/-! ### Euler's theorem -/

omit [DecidableEq ι] [DecidableEq N] in
theorem exists_orient {ends : ι → N × N} {e : ι} {y : N}
    (h : (ends e).1 = y ∨ (ends e).2 = y) : ∃ b : Bool, oSrc ends (e, b) = y := by
  rcases h with h | h
  · exact ⟨true, by simp [oSrc, h]⟩
  · exact ⟨false, by simp [oSrc, h]⟩

omit [DecidableEq ι] [DecidableEq N] in
theorem ends_eq (ends : ι → N × N) (p : ι × Bool) (y : N) :
    ((ends p.1).1 = y ∨ (ends p.1).2 = y) ↔ (oSrc ends p = y ∨ oTgt ends p = y) := by
  unfold oSrc oTgt
  cases p.2 <;> simp [or_comm]

omit [DecidableEq ι] in
/-- [s1:citEuler] (b) "A connected graph (or multigraph) in which every vertex has even degree has
a closed trail using every edge exactly once" (multigraph `(E, ends)` with loops, `E ≠ ∅`). -/
theorem exists_eulerian (E : Finset ι) (ends : ι → N × N) (hE : E.Nonempty)
    (hconn : ∀ x ∈ mVerts E ends, ∀ y ∈ mVerts E ends, (mAdj E ends).Reachable x y)
    (heven : ∀ x : N, Even (mdeg E ends x)) :
    ∃ W : List (ι × Bool), IsClosedTrail ends W ∧ ∀ e, e ∈ W.map Prod.fst ↔ e ∈ E := by
  classical
  let P : ℕ → Prop := fun n => ∃ W, IsTrailIn E ends W ∧ W.length = n
  obtain ⟨e₀, he₀⟩ := hE
  have hP1 : P 1 :=
    ⟨[(e₀, true)], ⟨by simp, List.isChain_singleton _, by simpa using he₀⟩, rfl⟩
  have h1E : 1 ≤ E.card := Finset.card_pos.2 ⟨e₀, he₀⟩
  obtain ⟨W, hW, hWlen⟩ : P (Nat.findGreatest P E.card) := Nat.findGreatest_spec h1E hP1
  have hmax : ∀ W', IsTrailIn E ends W' → W'.length ≤ Nat.findGreatest P E.card :=
    fun W' h' => Nat.le_findGreatest h'.length_le ⟨W', h', rfl⟩
  have hM1 : 1 ≤ Nat.findGreatest P E.card := Nat.le_findGreatest h1E hP1
  -- a longest trail cannot be extended at its end
  have hnoext : ∀ V' : List (ι × Bool), IsTrailIn E ends V' →
      V'.length = Nat.findGreatest P E.card → ∀ q ∈ V'.getLast?, ∀ e ∈ E,
        ((ends e).1 = oTgt ends q ∨ (ends e).2 = oTgt ends q) → e ∈ V'.map Prod.fst := by
    intro V' hV' hlen q hq e he hat
    by_contra hnot
    obtain ⟨b, hb⟩ := exists_orient hat
    have hext := hmax _ (hV'.append_single (p := (e, b)) he hnot (fun z hz' => by
      have : z = q := Option.mem_unique hz' hq
      subst this
      exact hb.symm))
    rw [List.length_append, List.length_singleton] at hext
    omega
  obtain ⟨a, l, rfl⟩ : ∃ a l, W = a :: l := by
    cases W with
    | nil => simp at hWlen; omega
    | cons a l => exact ⟨a, l, rfl⟩
  -- the longest trail is closed
  have hz : (a :: l).getLast? = some ((a :: l).getLast (List.cons_ne_nil _ _)) :=
    List.getLast?_eq_some_getLast _
  have hall_z := hnoext _ hW hWlen _ hz
  have hpar := even_sum_inc_add ends (oTgt ends ((a :: l).getLast (List.cons_ne_nil _ _))) a l
    hW.2.1
  rw [sum_inc_eq hW.1 hW.2.2 _ hall_z, if_pos rfl] at hpar
  have hsrc : oSrc ends a = oTgt ends ((a :: l).getLast (List.cons_ne_nil _ _)) := by
    by_contra hne
    rw [if_neg hne] at hpar
    have hev := heven (oTgt ends ((a :: l).getLast (List.cons_ne_nil _ _)))
    rw [Nat.even_iff] at hpar hev
    omega
  have hclosed : IsClosedTrail ends (a :: l) :=
    isClosedTrail_iff.2 ⟨hW.1, hW.2.1, hsrc.symm⟩
  -- every edge at a vertex where some oriented edge of the trail starts is used
  have hB : ∀ p ∈ a :: l, ∀ e ∈ E, ((ends e).1 = oSrc ends p ∨ (ends e).2 = oSrc ends p) →
      e ∈ (a :: l).map Prod.fst := by
    intro p hp e he hat
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    have hc' := isClosedTrail_rotate hclosed j
    have hhead : ((a :: l).rotate j).head? = some ((a :: l)[j]) := by
      rw [List.head?_rotate hj, List.getElem?_eq_getElem hj]
    obtain ⟨b, l', hbl⟩ : ∃ b l', (a :: l).rotate j = b :: l' := by
      cases h : (a :: l).rotate j with
      | nil => rw [h] at hhead; simp at hhead
      | cons b l' => exact ⟨b, l', rfl⟩
    rw [hbl, List.head?_cons, Option.some.injEq] at hhead
    rw [hbl] at hc'
    obtain ⟨hnd', hch', hlink'⟩ := isClosedTrail_iff.1 hc'
    have htr : IsTrailIn E ends (b :: l') := by
      refine ⟨hnd', hch', fun q hq => hW.2.2 q ?_⟩
      rw [← hbl] at hq
      exact List.mem_rotate.1 hq
    have hlen' : (b :: l').length = Nat.findGreatest P E.card := by
      rw [← hbl, List.length_rotate, hWlen]
    have hm := hnoext (b :: l') htr hlen' _ (List.getLast?_eq_some_getLast _) e he
      (by rw [hlink', hhead]; exact hat)
    rw [← hbl, List.map_rotate, List.mem_rotate] at hm
    exact hm
  -- vertex set of the trail
  let A : N → Prop := fun y => ∃ p ∈ a :: l, oSrc ends p = y
  have hendsA : ∀ e ∈ (a :: l).map Prod.fst, ∀ y, ((ends e).1 = y ∨ (ends e).2 = y) → A y := by
    intro e he y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    rcases (ends_eq ends p y).1 hy with h | h
    · exact ⟨p, hp, h⟩
    · obtain ⟨q, hq, hqe⟩ := exists_src_eq_tgt_of_closed hclosed hp
      exact ⟨q, hq, hqe.trans h⟩
  have hAedge : ∀ y, A y → ∀ e ∈ E, ((ends e).1 = y ∨ (ends e).2 = y) →
      e ∈ (a :: l).map Prod.fst := by
    rintro y ⟨p, hp, rfl⟩ e he hat
    exact hB p hp e he hat
  have hwalk : ∀ {u v : N} (w : (mAdj E ends).Walk u v), A u → A v := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons u u' v h w ih =>
      intro hu
      apply ih
      rw [mAdj, SimpleGraph.fromRel_adj] at h
      rcases h.2 with ⟨e, he, hends⟩ | ⟨e, he, hends⟩
      · have hmem := hAedge u hu e he (Or.inl (by rw [hends]))
        exact hendsA e hmem u' (Or.inr (by rw [hends]))
      · have hmem := hAedge u hu e he (Or.inr (by rw [hends]))
        exact hendsA e hmem u' (Or.inl (by rw [hends]))
  refine ⟨a :: l, hclosed, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact hW.2.2 p hp
  · have hx : oSrc ends a ∈ mVerts E ends := by
      unfold mVerts
      rw [Finset.mem_biUnion]
      refine ⟨a.1, hW.2.2 a (List.mem_cons_self ..), ?_⟩
      unfold oSrc
      cases a.2 <;> simp
    have hy : (ends e).1 ∈ mVerts E ends := by
      unfold mVerts
      rw [Finset.mem_biUnion]
      exact ⟨e, he, by simp⟩
    obtain ⟨w⟩ := hconn _ hx _ hy
    have hAy := hwalk w ⟨a, List.mem_cons_self .., rfl⟩
    exact hAedge _ hAy e he (Or.inl rfl)

end EG.MTrail.EulerProof
