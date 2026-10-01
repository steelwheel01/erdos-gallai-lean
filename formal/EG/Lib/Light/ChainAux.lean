module

public import EG.Lib.Light.Trail
public import EG.Lib.Found.Graph
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sigma

/-!
# List lemmas for the chaining of Lemma parent side (s5:lemParent, Steps 5–8)

Library for probe unit P4B (probe P-4, part 2), proof round 1:
* `card_filter_fin`: counting positions of a list satisfying a predicate;
* `getElem_transitions`, `mem_zip_rotate`: positions of transitions and of consecutive pairs;
* `sum_countP_fiber`: a list is the disjoint union of its fibres;
* `orient`: an arc traversed in the orientation of an oriented edge;
* `slot`: the rank of a position among the positions with the same node (Step 5: "give the
  transitions of `𝒲` at `Y` pairwise distinct slots `σ ∈ [T^sl_Y]`, by a fixed rule").
Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG.MTrail

variable {α β ι V : Type*}

theorem card_filter_fin (P : α → Prop) [DecidablePred P] :
    ∀ l : List α, (Finset.univ.filter fun j : Fin l.length => P l[j]).card = l.countP P
  | [] => by simp
  | a :: l => by
    rw [Finset.card_filter]
    erw [Fin.sum_univ_succ]
    rw [List.countP_cons]
    have ih := card_filter_fin P l
    rw [Finset.card_filter] at ih
    simp only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ, Fin.val_zero,
      List.getElem_cons_zero] at ih ⊢
    rw [ih]
    split_ifs <;> simp_all <;> omega

theorem getElem_transitions (ends : ι → V × V) (W : List (ι × Bool)) (j : ℕ)
    (hj : j < (transitions ends W).length) :
    (transitions ends W)[j] = (oTgt ends (W[j]'(by simpa [transitions] using hj)),
      oSrc ends (W[(j + 1) % W.length]'(Nat.mod_lt _ (by simp [transitions] at hj; omega)))) := by
  simp only [transitions, List.getElem_zipWith, List.getElem_rotate]

theorem mem_zip_rotate {l : List α} {p : α × α} :
    p ∈ List.zip l (l.rotate 1) ↔ ∃ (j : ℕ) (hj : j < l.length),
      p = (l[j], l[(j + 1) % l.length]'(Nat.mod_lt _ (by omega))) := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < l.length := by simpa using hj
    exact ⟨j, hj', by simp [List.getElem_zip, List.getElem_rotate]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by simpa using hj, by simp [List.getElem_zip, List.getElem_rotate]⟩

/-- A list is the disjoint union of its fibres over a finset containing all values. -/
theorem sum_countP_fiber [DecidableEq β] (f : α → β) (S : Finset β) :
    ∀ l : List α, (∀ x ∈ l, f x ∈ S) → ∑ y ∈ S, l.countP (fun x => decide (f x = y)) = l.length
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.countP_cons, Finset.sum_add_distrib, List.length_cons]
    rw [sum_countP_fiber f S l (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    congr 1
    simp only [decide_eq_true_eq]
    rw [Finset.sum_ite_eq]
    simp [h a List.mem_cons_self]

/-! ### Oriented arcs -/

/-- The arc `arcPath p.1` traversed from `oSrc` to `oTgt` (reversed if `p.2 = false`). -/
def orient (arcPath : ι → List V) (p : ι × Bool) : List V :=
  if p.2 then arcPath p.1 else (arcPath p.1).reverse

theorem orient_head? {arcPath : ι → List V} {ends : ι → V × V} {p : ι × Bool}
    (h1 : (arcPath p.1).head? = some (ends p.1).1) (h2 : (arcPath p.1).getLast? = some (ends p.1).2) :
    (orient arcPath p).head? = some (oSrc ends p) := by
  unfold orient oSrc; split <;> simp_all [List.head?_reverse]

theorem orient_getLast? {arcPath : ι → List V} {ends : ι → V × V} {p : ι × Bool}
    (h1 : (arcPath p.1).head? = some (ends p.1).1) (h2 : (arcPath p.1).getLast? = some (ends p.1).2) :
    (orient arcPath p).getLast? = some (oTgt ends p) := by
  unfold orient oTgt; split <;> simp_all [List.getLast?_reverse]

theorem orient_nodup {arcPath : ι → List V} {p : ι × Bool} :
    (orient arcPath p).Nodup ↔ (arcPath p.1).Nodup := by
  unfold orient; split <;> simp

theorem length_orient (arcPath : ι → List V) (p : ι × Bool) :
    (orient arcPath p).length = (arcPath p.1).length := by
  unfold orient; split <;> simp

theorem mem_orient {arcPath : ι → List V} {p : ι × Bool} {x : V} :
    x ∈ orient arcPath p ↔ x ∈ arcPath p.1 := by
  unfold orient; split <;> simp

theorem walkEdges_orient_perm (arcPath : ι → List V) (p : ι × Bool) :
    (walkEdges (orient arcPath p)).Perm (walkEdges (arcPath p.1)) := by
  unfold orient; split
  · exact List.Perm.refl _
  · rw [walkEdges_reverse]; exact List.reverse_perm _

/-! ### Slots -/

/-- The slot of position `j` of `W` with respect to the node map `f`: the number of earlier
positions with the same node. -/
def slot [DecidableEq β] (f : α → β) (W : List α) (j : ℕ) (y : β) : ℕ :=
  (W.take j).countP fun p => decide (f p = y)

theorem slot_lt [DecidableEq β] (f : α → β) (W : List α) (j : ℕ) (hj : j < W.length) :
    slot f W j (f W[j]) < W.countP fun p => decide (f p = f W[j]) := by
  unfold slot
  have h1 : (W.take (j + 1)).countP (fun p => decide (f p = f W[j])) =
      (W.take j).countP (fun p => decide (f p = f W[j])) + 1 := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.countP_append]
    simp
  have h2 : (W.take (j + 1)).countP (fun p => decide (f p = f W[j])) ≤
      W.countP (fun p => decide (f p = f W[j])) :=
    (List.take_sublist _ _).countP_le
  omega

theorem slot_lt_slot [DecidableEq β] (f : α → β) (W : List α) {j j' : ℕ} (hj : j < W.length)
    (hj' : j' < W.length) (hjj : j < j') (hf : f W[j] = f W[j']) :
    slot f W j (f W[j]) < slot f W j' (f W[j']) := by
  unfold slot
  rw [← hf]
  have h1 : (W.take (j + 1)).countP (fun p => decide (f p = f W[j])) =
      (W.take j).countP (fun p => decide (f p = f W[j])) + 1 := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.countP_append]
    simp
  have h2 : (W.take (j + 1)).countP (fun p => decide (f p = f W[j])) ≤
      (W.take j').countP (fun p => decide (f p = f W[j])) :=
    (List.take_sublist_take_left (by omega)).countP_le
  omega

/-! ### Positions of a list of trails -/

theorem trailEdges_flatMap {γ : Type*} (L : List γ) (f : γ → List (List (ι × Bool))) :
    trailEdges (L.flatMap f) = L.flatMap fun i => trailEdges (f i) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ← ih]
    simp [trailEdges, List.flatMap_append]

theorem sum_fin_getElem {M : Type*} [AddCommMonoid M] (L : List α) (f : α → M) :
    ∑ k : Fin L.length, f L[k.1] = (L.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  conv_rhs => rw [← List.ofFn_getElem (xs := L), List.map_ofFn]
  rfl

/-- The positions `(k, j)` of a list of trails `L` (trail `k`, position `j` in it). -/
abbrev Pos (L : List (List α)) : Type := Σ k : Fin L.length, Fin (L[k.1]).length

/-- Counting the positions whose transition satisfies `P` is counting the transitions of all
trails satisfying `P`. -/
theorem card_pos_filter (ends : ι → V × V) (L : List (List (ι × Bool))) (P : V × V → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun x : Pos L => P (oTgt ends L[x.1.1][x.2.1],
        oSrc ends (L[x.1.1][(x.2.1 + 1) % L[x.1.1].length]'(Nat.mod_lt _
          (lt_of_le_of_lt (Nat.zero_le _) x.2.isLt))))).card =
      (L.flatMap (transitions ends)).countP P := by
  rw [Finset.card_filter, Fintype.sum_sigma, List.countP_flatMap]
  have hk : ∀ k : Fin L.length, (∑ j : Fin (L[k.1]).length,
      if P (oTgt ends L[k.1][j.1], oSrc ends (L[k.1][(j.1 + 1) % L[k.1].length]'(Nat.mod_lt _
        (lt_of_le_of_lt (Nat.zero_le _) j.isLt)))) then 1 else 0) =
        (transitions ends L[k.1]).countP P := by
    intro k
    rw [← Finset.card_filter, ← card_filter_fin P (transitions ends L[k.1])]
    refine Finset.card_equiv (finCongr (length_transitions ends L[k.1]).symm) fun j => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, finCongr_apply, Fin.getElem_fin,
      Fin.val_cast]
    rw [getElem_transitions]
  rw [Finset.sum_congr rfl fun k _ => hk k]
  exact sum_fin_getElem L (fun W => (transitions ends W).countP P)


end EG.MTrail
