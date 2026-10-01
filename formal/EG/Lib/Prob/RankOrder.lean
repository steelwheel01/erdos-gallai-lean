module

public import EG.Lib.Prob.Uniform
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fintype

/-!
# The elements of a set in a uniformly random linear order

For a finite type `W` and a uniformly random bijection `o : W ≃ Fin n` (the rank function of a
uniformly random linear order of `W`), `rankList o C` lists the elements of `C ⊆ W` in increasing
rank. This file proves the laws used by Construction s7:consRound (e2) ("the map `e_i ↦ w_i` is a
uniformly random injection of `E'(u)` into `Cand_l(u) \ Used(u)`") and Lemmas s7:lemCC (i),
s7:lemUltra (i) ("uniform on `Cand_l(u_i) \ Used(u_i)`"):

* `prob_rankList_take`: for a duplicate-free list `cs` of `q` elements of `C`, the first `q`
  elements of `C` in the random order are `cs` with probability `1/(|C|)_q` (falling factorial);
* the symmetry behind it: `rankList_trans` (relabelling by a permutation preserving `C`) and
  `prob_trans_preimage` (the uniform law is invariant under relabelling).

(This is item 3 of the Uniform-law plan of `EG/Lib/Prob/Uniform.lean`.)
-/

public section

namespace EG

namespace FinDist

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W] {n : ℕ}

/-- The elements of `C` listed in increasing rank for the rank function `o`. -/
@[expose] def rankList (o : W ≃ Fin n) (C : Finset W) : List W :=
  (List.finRange n).filterMap (fun i => if o.symm i ∈ C then some (o.symm i) else none)

theorem rankList_def (o : W ≃ Fin n) (C : Finset W) :
    rankList o C =
      (List.finRange n).filterMap (fun i => if o.symm i ∈ C then some (o.symm i) else none) :=
  rfl

theorem mem_rankList (o : W ≃ Fin n) (C : Finset W) (v : W) : v ∈ rankList o C ↔ v ∈ C := by
  simp only [rankList, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h
    · cases hi; exact h
  · intro hv
    exact ⟨o v, by simp [hv]⟩

theorem nodup_rankList (o : W ≃ Fin n) (C : Finset W) : (rankList o C).Nodup := by
  unfold rankList
  refine List.Nodup.filterMap ?_ (List.nodup_finRange _)
  intro i j b hi hj
  split_ifs at hi hj
  · simp only [Option.mem_def, Option.some.injEq] at hi hj
    exact o.symm.injective (hi.trans hj.symm)
  all_goals simp at hi hj

theorem length_rankList (o : W ≃ Fin n) (C : Finset W) : (rankList o C).length = C.card := by
  rw [← List.toFinset_card_of_nodup (nodup_rankList o C)]
  congr 1
  ext v
  simp [mem_rankList]

/-- Relabelling the ranks by a permutation `τ` that preserves `C` maps the list by `τ`. -/
theorem rankList_trans (o : W ≃ Fin n) (C : Finset W) (τ : Equiv.Perm W)
    (hτ : ∀ x, τ x ∈ C ↔ x ∈ C) :
    rankList ((τ.symm).trans o) C = (rankList o C).map τ := by
  unfold rankList
  rw [List.map_filterMap]
  refine List.filterMap_congr fun i _ => ?_
  have e : ((τ.symm).trans o).symm i = τ (o.symm i) := by simp [Equiv.symm_trans_apply]
  rw [e]
  by_cases h : o.symm i ∈ C
  · simp [h, (hτ _).2 h]
  · simp [h, mt (hτ _).1 h]

variable [Nonempty (W ≃ Fin n)]

/-- The uniform law of a linear order is invariant under relabelling by a permutation. -/
theorem prob_trans_preimage (τ : Equiv.Perm W) (A : Set (W ≃ Fin n)) :
    (uniform (W ≃ Fin n)).prob {o | (τ.symm).trans o ∈ A} = (uniform (W ≃ Fin n)).prob A := by
  let e : (W ≃ Fin n) ≃ (W ≃ Fin n) :=
    { toFun := fun o => (τ.symm).trans o
      invFun := fun o => τ.trans o
      left_inv := fun o => by ext x; simp
      right_inv := fun o => by ext x; simp }
  have h := map_equiv_uniform (α := W ≃ Fin n) (β := W ≃ Fin n) e
  change (uniform (W ≃ Fin n)).prob (e ⁻¹' A) = _
  rw [← prob_map, h]

/-- Two injections of `Fin q` into `C` differ by a permutation of `W` preserving `C`. -/
theorem exists_perm_map (C : Finset W) {q : ℕ} (e e' : Fin q ↪ C) :
    ∃ τ : Equiv.Perm W, (∀ x, τ x ∈ C ↔ x ∈ C) ∧ ∀ i, τ (e i) = e' i := by
  classical
  let f : C → W := Function.extend e (fun i => (e' i : W)) (fun x => (x : W))
  have hf : ∀ i, f (e i) = e' i := fun i => e.injective.extend_apply _ _ i
  obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq (α := C) (t := C)
    (by simp) (s := Finset.univ.map e) (f := f)
    (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
      rw [hf]; exact (e' i).2)
    (by
      intro x hx y hy hxy
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hx)
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hy)
      rw [hf, hf] at hxy
      rw [e'.injective (Subtype.ext hxy)])
  refine ⟨g.extendSubtype, fun x => ?_, fun i => ?_⟩
  · by_cases hx : x ∈ C
    · exact ⟨fun _ => hx, fun _ => g.extendSubtype_mem x hx⟩
    · exact ⟨fun h => absurd h (g.extendSubtype_not_mem x hx), fun h => absurd h hx⟩
  · rw [g.extendSubtype_apply_of_mem _ (e i).2]
    have := hg (e i) (Finset.mem_map_of_mem _ (Finset.mem_univ i))
    rw [this, hf]

/-- The list of an injection of `Fin q` into `C`. -/
@[expose] def embList {C : Finset W} {q : ℕ} (e : Fin q ↪ C) : List W := List.ofFn fun i => (e i : W)

theorem embList_injective {C : Finset W} {q : ℕ} :
    Function.Injective (embList (C := C) (q := q)) := by
  intro e e' h
  have h' := List.ofFn_injective h
  ext i
  exact congrFun h' i

theorem map_embList {C : Finset W} {q : ℕ} (e : Fin q ↪ C) (τ : Equiv.Perm W) :
    (embList e).map τ = List.ofFn fun i => τ (e i) := by
  simp [embList, List.map_ofFn, Function.comp_def]

/-- A duplicate-free list of `q` elements of `C` is the list of an injection `Fin q ↪ C`. -/
theorem exists_embList {C : Finset W} (cs : List W) (hnd : cs.Nodup) (hC : ∀ c ∈ cs, c ∈ C) :
    ∃ e : Fin cs.length ↪ C, embList e = cs := by
  refine ⟨⟨fun i => ⟨cs[i], hC _ (List.getElem_mem _)⟩, fun i j h => ?_⟩, ?_⟩
  · have h' : cs[i] = cs[j] := congrArg Subtype.val h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h')
  · apply List.ext_getElem (by simp [embList])
    intro i h1 h2
    simp [embList]

/-- All injections `Fin q ↪ C` are equally likely prefixes. -/
theorem prob_take_eq_embList_eq (C : Finset W) {q : ℕ} (e e' : Fin q ↪ C) :
    (uniform (W ≃ Fin n)).prob {o | (rankList o C).take q = embList e} =
      (uniform (W ≃ Fin n)).prob {o | (rankList o C).take q = embList e'} := by
  obtain ⟨τ, hτ, he⟩ := exists_perm_map C e e'
  rw [← prob_trans_preimage τ {o | (rankList o C).take q = embList e'}]
  congr 1
  ext o
  simp only [Set.mem_ofPred_eq]
  rw [rankList_trans o C τ hτ, ← List.map_take]
  have hl : embList e' = (embList e).map τ := by
    rw [map_embList]; simp only [he]; rfl
  rw [hl]
  exact (List.map_injective_iff.2 τ.injective).eq_iff.symm

/-- Every rank function has exactly one prefix of length `q ≤ |C|`. -/
theorem sum_ite_take_eq (C : Finset W) {q : ℕ} (hq : q ≤ C.card) (o : W ≃ Fin n) :
    ∑ e : Fin q ↪ C, (if (rankList o C).take q = embList e then (1 : ℝ) else 0) = 1 := by
  classical
  have hnd : ((rankList o C).take q).Nodup := (nodup_rankList o C).sublist (List.take_sublist _ _)
  have hmem : ∀ c ∈ (rankList o C).take q, c ∈ C :=
    fun c hc => (mem_rankList o C c).1 (List.mem_of_mem_take hc)
  have hlen : ((rankList o C).take q).length = q := by
    rw [List.length_take, length_rankList]; omega
  let e0 : Fin q ↪ C :=
    ⟨fun i => ⟨((rankList o C).take q)[i.1]'(by rw [hlen]; exact i.2),
        hmem _ (List.getElem_mem _)⟩, fun i j h => by
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h')⟩
  have he0 : embList e0 = (rankList o C).take q := by
    apply List.ext_getElem (by simp [embList, hlen])
    intro i h1 h2
    simp [embList, e0]
  have key : ∀ e : Fin q ↪ C, ((rankList o C).take q = embList e) ↔ e0 = e := by
    intro e
    rw [← he0]
    exact embList_injective.eq_iff
  simp_rw [key]
  rw [Finset.sum_ite_eq]
  simp

/-- The first `q` elements of `C` in a uniformly random order form a given injection
`Fin q ↪ C` with probability `1/(|C|)_q`. -/
theorem prob_take_embList (C : Finset W) {q : ℕ} (e1 : Fin q ↪ C) :
    (uniform (W ≃ Fin n)).prob {o | (rankList o C).take q = embList e1} =
      1 / (C.card.descFactorial q : ℝ) := by
  classical
  have hq' : q ≤ C.card := by
    have := Fintype.card_le_of_embedding e1
    simpa using this
  -- all prefixes are equally likely, and they partition the space
  have hsum : ∑ e : Fin q ↪ C,
      (uniform (W ≃ Fin n)).prob {o | (rankList o C).take q = embList e} = 1 := by
    have h1 : ∀ e : Fin q ↪ C,
        (uniform (W ≃ Fin n)).prob {o | (rankList o C).take q = embList e} =
          (uniform (W ≃ Fin n)).expect
            (fun o => if (rankList o C).take q = embList e then (1 : ℝ) else 0) := by
      intro e
      rw [prob_eq_expect]
      congr 1
      funext o
      by_cases h : (rankList o C).take q = embList e <;> simp [Set.indicator, h]
    simp_rw [h1]
    rw [← expect_sum]
    simp_rw [sum_ite_take_eq C hq']
    exact expect_const _ 1
  have hconst : ∀ e : Fin q ↪ C,
      (uniform (W ≃ Fin n)).prob {o | (rankList o C).take q = embList e} =
        (uniform (W ≃ Fin n)).prob {o | (rankList o C).take q = embList e1} :=
    fun e => prob_take_eq_embList_eq C e e1
  rw [Finset.sum_congr rfl fun e _ => hconst e, Finset.sum_const, Finset.card_univ,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < (C.card.descFactorial q : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.2 hq'
  rw [eq_div_iff hpos.ne', mul_comm]
  exact hsum

/-- [s7:consRound] (e2): for a duplicate-free list `cs` of `q` elements of `C`, the first `q`
elements of `C` in a uniformly random order are `cs` with probability `1/(|C|)_q`. -/
theorem prob_rankList_take (C : Finset W) (cs : List W) (hnd : cs.Nodup)
    (hC : ∀ c ∈ cs, c ∈ C) :
    (uniform (W ≃ Fin n)).prob {o | (rankList o C).take cs.length = cs} =
      1 / (C.card.descFactorial cs.length : ℝ) := by
  obtain ⟨e1, he1⟩ := exists_embList cs hnd hC
  have := prob_take_embList (n := n) C e1
  rw [he1] at this
  exact this

/-- [s7:lemUltra] (i), [s7:lemCC] (i): the `i`-th element of `C` (`i < |C|`) in a uniformly random
order is uniform on `C`. -/
theorem prob_rankList_getElem? (C : Finset W) {i : ℕ} (hi : i < C.card) {w : W} (hw : w ∈ C) :
    (uniform (W ≃ Fin n)).prob {o | (rankList o C)[i]? = some w} = 1 / (C.card : ℝ) := by
  classical
  -- all elements of `C` are equally likely at position `i`
  have hconst : ∀ w' ∈ C, (uniform (W ≃ Fin n)).prob {o | (rankList o C)[i]? = some w'} =
      (uniform (W ≃ Fin n)).prob {o | (rankList o C)[i]? = some w} := by
    intro w' hw'
    let τ := Equiv.swap w' w
    have hτ : ∀ x, τ x ∈ C ↔ x ∈ C := by
      intro x
      by_cases h1 : x = w'
      · subst h1; simp [τ, Equiv.swap_apply_left, hw, hw']
      · by_cases h2 : x = w
        · subst h2; simp [τ, Equiv.swap_apply_right, hw, hw']
        · simp [τ, Equiv.swap_apply_of_ne_of_ne h1 h2]
    rw [← prob_trans_preimage τ {o | (rankList o C)[i]? = some w}]
    congr 1
    ext o
    simp only [Set.mem_ofPred_eq]
    rw [rankList_trans o C τ hτ, List.getElem?_map]
    constructor
    · intro h; rw [h]; simp [τ, Equiv.swap_apply_left]
    · intro h
      obtain ⟨x, hx, hxw⟩ := Option.map_eq_some_iff.1 h
      have : x = w' := by
        have := congrArg τ hxw
        simpa [τ, Equiv.swap_apply_right] using this
      rw [hx, this]
  -- they sum to one
  have hsum : ∑ w' ∈ C, (uniform (W ≃ Fin n)).prob {o | (rankList o C)[i]? = some w'} = 1 := by
    have h1 : ∀ w' ∈ C, (uniform (W ≃ Fin n)).prob {o | (rankList o C)[i]? = some w'} =
        (uniform (W ≃ Fin n)).expect
          (fun o => if (rankList o C)[i]? = some w' then (1 : ℝ) else 0) := by
      intro w' _
      rw [prob_eq_expect]
      congr 1
      funext o
      by_cases h : (rankList o C)[i]? = some w' <;> simp [Set.indicator, h]
    rw [Finset.sum_congr rfl h1, ← expect_sum]
    have h2 : ∀ o : W ≃ Fin n,
        ∑ w' ∈ C, (if (rankList o C)[i]? = some w' then (1 : ℝ) else 0) = 1 := by
      intro o
      have hi' : i < (rankList o C).length := by rw [length_rankList]; exact hi
      rw [List.getElem?_eq_getElem hi']
      simp only [Option.some.injEq]
      rw [Finset.sum_ite_eq]
      rw [if_pos ((mem_rankList o C _).1 (List.getElem_mem _))]
    simp_rw [h2]
    exact expect_const _ 1
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i) hi)
  rw [eq_div_iff hpos.ne', mul_comm]
  exact hsum

end FinDist

end EG
