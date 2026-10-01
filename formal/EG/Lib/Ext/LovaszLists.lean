module

public import EG.Lib.Ext.Cor22

/-!
# List lemmas for the Lovász construction (manuscript s1:citThm21)

Helper file for `EG.LovaszC.lovasz_construction` (`EG/Lib/Ext/LovaszCons.lean`), the proof of
Lovász's path-and-cycle theorem ([s1:citThm21], `EG.Spec.LovaszStatement`) following Lovász's
construction as reproduced in L. Yan, *On path decompositions of graphs* (PhD thesis, Arizona State
University, 1998), §2.1. See `formal/work/p3/lovasz.md`.

Contents:
* membership in `walkEdges` of `x :: l`, `l ++ [x]`, `A ++ x :: B`, `l.reverse`, and in
  `cycleEdges (U ++ [x])`;
* `pre x U` / `post x U`: the parts of `U` before / after the first occurrence of `x`;
* `reroute x U l₁ l₂`: the path `U = A ++ x :: B` with `A` reversed if `l₁` and `B` reversed if `l₂`
  (the rerouting step of the construction), its validity and its edges.
-/

public section

namespace EG

namespace LovaszC

variable {V : Type*}

/-! ### Membership in `walkEdges` -/

theorem mem_walkEdges_cons (x : V) (l : List V) (e : Sym2 V) :
    e ∈ walkEdges (x :: l) ↔ (∃ b, l.head? = some b ∧ e = s(x, b)) ∨ e ∈ walkEdges l := by
  rw [Cor22.walkEdges_cons, List.mem_append]
  cases l.head? <;> simp

theorem mem_walkEdges_concat (l : List V) (x : V) (e : Sym2 V) :
    e ∈ walkEdges (l ++ [x]) ↔ e ∈ walkEdges l ∨ (∃ a, l.getLast? = some a ∧ e = s(a, x)) := by
  rw [walkEdges_concat, List.mem_append]
  cases l.getLast? <;> simp

theorem mem_walkEdges_append_cons (A : List V) (x : V) (B : List V) (e : Sym2 V) :
    e ∈ walkEdges (A ++ x :: B) ↔ e ∈ walkEdges A ∨ (∃ a, A.getLast? = some a ∧ e = s(a, x)) ∨
      (∃ b, B.head? = some b ∧ e = s(x, b)) ∨ e ∈ walkEdges B := by
  rw [Cor22.walkEdges_append_cons, List.mem_append, mem_walkEdges_concat, mem_walkEdges_cons]
  simp only [or_assoc]

theorem mem_walkEdges_reverse {l : List V} {e : Sym2 V} :
    e ∈ walkEdges l.reverse ↔ e ∈ walkEdges l := by
  rw [walkEdges_reverse, List.mem_reverse]

/-- The edges of the cycle `U ++ [x]` (closing edge `s(x, head)`). -/
theorem mem_cycleEdges_concat {U : List V} (hU : U ≠ []) (x : V) (e : Sym2 V) :
    e ∈ cycleEdges (U ++ [x]) ↔ e ∈ walkEdges U ∨ (∃ a, U.getLast? = some a ∧ e = s(a, x)) ∨
      (∃ b, U.head? = some b ∧ e = s(x, b)) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hU
  have h1 : a :: t ++ [x] = a :: (t ++ [x]) := rfl
  have h2 : a :: (t ++ [x]) ++ [a] = (a :: t ++ [x]) ++ [a] := rfl
  have hl : (a :: t ++ [x]).getLast? = some x := by
    rw [List.getLast?_append]; simp
  rw [h1, Cor22.cycleEdges_eq, h2, mem_walkEdges_concat, mem_walkEdges_concat, hl]
  simp only [List.head?_cons, Option.some.injEq]
  constructor
  · rintro ((h | h) | ⟨b, hb, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨a, rfl, hb ▸ h⟩)
  · rintro (h | h | ⟨b, hb, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨x, rfl, hb ▸ h⟩

/-! ### Splitting a list at `x` -/

variable [DecidableEq V]

/-- The part of `U` before the first occurrence of `x` (all of `U` if `x ∉ U`). -/
def pre (x : V) : List V → List V
  | [] => []
  | a :: t => if a = x then [] else a :: pre x t

/-- The part of `U` after the first occurrence of `x` (`[]` if `x ∉ U`). -/
def post (x : V) : List V → List V
  | [] => []
  | a :: t => if a = x then t else post x t

theorem pre_append_post {x : V} : ∀ {U : List V}, x ∈ U → U = pre x U ++ x :: post x U
  | [], h => absurd h List.not_mem_nil
  | a :: t, h => by
    by_cases hax : a = x
    · subst hax; simp [pre, post]
    · have ht : x ∈ t := (List.mem_cons.1 h).resolve_left (Ne.symm hax)
      simp only [pre, post, if_neg hax, List.cons_append]
      rw [← pre_append_post ht]

theorem not_mem_pre (x : V) : ∀ U : List V, x ∉ pre x U
  | [] => by simp [pre]
  | a :: t => by
    by_cases hax : a = x
    · simp [pre, hax]
    · simp only [pre, if_neg hax, List.mem_cons, not_or]
      exact ⟨Ne.symm hax, not_mem_pre x t⟩

theorem pre_post_eq {x : V} : ∀ {A : List V} (B : List V), x ∉ A →
    pre x (A ++ x :: B) = A ∧ post x (A ++ x :: B) = B
  | [], B, _ => by simp [pre, post]
  | a :: A, B, h => by
    rw [List.mem_cons, not_or] at h
    have hax : a ≠ x := Ne.symm h.1
    obtain ⟨h1, h2⟩ := pre_post_eq (A := A) B h.2
    simp [pre, post, hax, h1, h2]

/-- In a list without repetitions, `x` is not after itself. -/
theorem not_mem_post {x : V} {U : List V} (hU : U.Nodup) (hx : x ∈ U) : x ∉ post x U := by
  have h := pre_append_post hx
  rw [h] at hU
  rw [List.nodup_append] at hU
  exact (List.nodup_cons.1 hU.2.1).1

/-- The two sides of `x` in a list without repetitions are disjoint. -/
theorem pre_post_disjoint {x : V} {U : List V} (hU : U.Nodup) (hx : x ∈ U) {v : V}
    (h1 : v ∈ pre x U) (h2 : v ∈ post x U) : False := by
  have h := pre_append_post hx
  rw [h, List.nodup_append] at hU
  exact hU.2.2 v h1 v (List.mem_cons_of_mem _ h2) rfl

/-- Splitting the reverse. -/
theorem pre_reverse {x : V} {U : List V} (hU : U.Nodup) (hx : x ∈ U) :
    pre x U.reverse = (post x U).reverse ∧ post x U.reverse = (pre x U).reverse := by
  have h := pre_append_post hx
  have hr : U.reverse = (post x U).reverse ++ x :: (pre x U).reverse := by
    conv_lhs => rw [h]
    simp
  rw [hr]
  exact pre_post_eq _ (by rw [List.mem_reverse]; exact not_mem_post hU hx)

/-- Every edge of `U` at... membership in `walkEdges U` through its split at `x`. -/
theorem mem_walkEdges_split {x : V} {U : List V} (hx : x ∈ U) (e : Sym2 V) :
    e ∈ walkEdges U ↔ e ∈ walkEdges (pre x U) ∨
      (∃ a, (pre x U).getLast? = some a ∧ e = s(a, x)) ∨
      (∃ b, (post x U).head? = some b ∧ e = s(x, b)) ∨ e ∈ walkEdges (post x U) := by
  conv_lhs => rw [pre_append_post hx]
  exact mem_walkEdges_append_cons _ _ _ _

/-! ### Rerouting -/

/-- The rerouted path: `U = A ++ x :: B` becomes `A' ++ x :: B'` with `A' = A.reverse` if `l₁`
(else `A`) and `B' = B.reverse` if `l₂` (else `B`). -/
def reroute (x : V) (U : List V) (l₁ l₂ : Bool) : List V :=
  (if l₁ then (pre x U).reverse else pre x U) ++ x :: (if l₂ then (post x U).reverse else post x U)

theorem reroute_perm {x : V} {U : List V} (hx : x ∈ U) (l₁ l₂ : Bool) :
    (reroute x U l₁ l₂).Perm U := by
  have h : U = pre x U ++ x :: post x U := pre_append_post hx
  have hA : (if l₁ then (pre x U).reverse else pre x U).Perm (pre x U) := by
    split_ifs
    · exact List.reverse_perm _
    · exact List.Perm.refl _
  have hB : (if l₂ then (post x U).reverse else post x U).Perm (post x U) := by
    split_ifs
    · exact List.reverse_perm _
    · exact List.Perm.refl _
  unfold reroute
  conv_rhs => rw [h]
  exact List.Perm.append hA (List.Perm.cons x hB)

theorem reroute_nodup {x : V} {U : List V} (hU : U.Nodup) (hx : x ∈ U) (l₁ l₂ : Bool) :
    (reroute x U l₁ l₂).Nodup :=
  (reroute_perm hx l₁ l₂).nodup_iff.2 hU

theorem reroute_length {x : V} {U : List V} (hx : x ∈ U) (l₁ l₂ : Bool) :
    (reroute x U l₁ l₂).length = U.length :=
  (reroute_perm hx l₁ l₂).length_eq

/-- The edges of the rerouted path. -/
theorem mem_walkEdges_reroute (x : V) (U : List V) (l₁ l₂ : Bool) (e : Sym2 V) :
    e ∈ walkEdges (reroute x U l₁ l₂) ↔ e ∈ walkEdges (pre x U) ∨
      (∃ a, (if l₁ then (pre x U).head? else (pre x U).getLast?) = some a ∧ e = s(a, x)) ∨
      (∃ b, (if l₂ then (post x U).getLast? else (post x U).head?) = some b ∧ e = s(x, b)) ∨
      e ∈ walkEdges (post x U) := by
  unfold reroute
  rw [mem_walkEdges_append_cons]
  have hA : e ∈ walkEdges (if l₁ then (pre x U).reverse else pre x U) ↔ e ∈ walkEdges (pre x U) := by
    split_ifs
    · exact mem_walkEdges_reverse
    · exact Iff.rfl
  have hB : e ∈ walkEdges (if l₂ then (post x U).reverse else post x U) ↔
      e ∈ walkEdges (post x U) := by
    split_ifs
    · exact mem_walkEdges_reverse
    · exact Iff.rfl
  have hA' : (if l₁ then (pre x U).reverse else pre x U).getLast? =
      (if l₁ then (pre x U).head? else (pre x U).getLast?) := by
    split_ifs
    · exact List.getLast?_reverse
    · rfl
  have hB' : (if l₂ then (post x U).reverse else post x U).head? =
      (if l₂ then (post x U).getLast? else (post x U).head?) := by
    split_ifs
    · exact List.head?_reverse
    · rfl
  rw [hA, hB, hA', hB']

end LovaszC

end EG
