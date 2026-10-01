module

public import EG.Lib.Prob.RankOrder
public import EG.Lib.Prob.Indep
public import EG.Defs.Quot.Round
public import Mathlib.Data.Fintype.Perm

/-!
# The law of the lists of the hub groups

Construction [s7:consRound] (c): the list of group `i` of a non-ultra hub `h` is
`listOf η_h i = {η_h(3i), η_h(3i+1), η_h(3i+2)}` for a uniformly random permutation `η_h` of
`[4M_l]`. This file proves:

* `card_listOf`, `listOf_subset_range`, `disjoint_listOf`: the lists of the groups `i` with
  `3i + 3 ≤ K` are pairwise disjoint `3`-subsets of `[K]`;
* `prob_listOf_eq`: for `3k ≤ K`, the first `k` lists form a given sequence of pairwise disjoint
  `3`-subsets with probability `6^k / (K)_{3k}` ("a uniformly random sequence of `k_h` pairwise
  disjoint `3`-subsets of `[4M_l]`"): the event is the disjoint union, over the `6^k` orderings
  of the given sets, of the events that the first `3k` values of `η` form that ordering, each of
  probability `1/(K)_{3k}` (`EG.FinDist.prob_rankList_take`).
-/

public section

namespace EG.Quot

open Finset EG.FinDist

/-- A prefix of `List.ofFn f` is `List.ofFn c` iff `f` and `c` agree on it. -/
theorem take_ofFn_eq_iff {α : Type*} {N m : ℕ} (hm : m ≤ N) (f : Fin N → α) (c : Fin m → α) :
    (List.ofFn f).take m = List.ofFn c ↔ ∀ j : Fin m, f (Fin.castLE hm j) = c j := by
  rw [List.ext_getElem_iff]
  simp only [List.length_take, List.length_ofFn, List.getElem_take, List.getElem_ofFn]
  constructor
  · rintro ⟨-, h⟩ j
    exact h j.1 (by simp only [Nat.min_eq_left hm]; exact j.2) j.2
  · intro h
    exact ⟨Nat.min_eq_left hm, fun n _ h2 => h ⟨n, h2⟩⟩

/-- The rank list of the whole of `Fin K`: the values of the inverse rank function in order. -/
theorem rankList_univ {K : ℕ} (o : Fin K ≃ Fin K) :
    rankList o (univ : Finset (Fin K)) = List.ofFn o.symm := by
  rw [rankList_def, List.ofFn_eq_map]
  simp only [mem_univ, if_true]
  exact congrFun List.filterMap_eq_map _

theorem mem_listOf {K : ℕ} (η : Equiv.Perm (Fin K)) (i n : ℕ) :
    n ∈ listOf η i ↔ ∃ a : Fin K, a.val / 3 = i ∧ (η a).val = n := by
  simp [listOf]

theorem listOf_subset_range {K : ℕ} (η : Equiv.Perm (Fin K)) (i : ℕ) :
    listOf η i ⊆ range K := by
  intro n hn
  obtain ⟨a, -, rfl⟩ := (mem_listOf η i n).1 hn
  exact mem_range.2 (η a).2

theorem card_listOf {K : ℕ} (η : Equiv.Perm (Fin K)) {i : ℕ} (hi : 3 * i + 3 ≤ K) :
    (listOf η i).card = 3 := by
  have hset : listOf η i = (univ : Finset (Fin 3)).image
      (fun r : Fin 3 => (η ⟨3 * i + r.val, by have := r.isLt; omega⟩).val) := by
    ext n
    rw [mem_listOf, mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a.val % 3, Nat.mod_lt _ (by norm_num)⟩, mem_univ _, ?_⟩
      congr 2
      ext
      simp only
      omega
    · rintro ⟨r, -, rfl⟩
      exact ⟨_, by have := r.isLt; simp only; omega, rfl⟩
  rw [hset, card_image_of_injective, card_univ, Fintype.card_fin]
  intro r r' h
  have h1 := Fin.ext h
  have h2 := congrArg Fin.val (η.injective h1)
  simp only at h2
  exact Fin.ext (by omega)

theorem disjoint_listOf {K : ℕ} (η : Equiv.Perm (Fin K)) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (listOf η i) (listOf η j) := by
  rw [disjoint_left]
  intro n hi hj
  obtain ⟨a, ha, rfl⟩ := (mem_listOf η i _).1 hi
  obtain ⟨b, hb, hab⟩ := (mem_listOf η j _).1 hj
  have := η.injective (Fin.ext hab)
  subst this
  exact hij (ha.symm.trans hb)

/-- [s7:consRound] (c): for `3k ≤ K`, the lists of the first `k` groups of a uniformly random
permutation `η` of `[K]` form a given sequence of pairwise disjoint `3`-subsets of `[K]` with
probability `6^k/(K)_{3k}`. -/
theorem prob_listOf_eq {K k : ℕ} (hk : 3 * k ≤ K) (A : ℕ → Finset ℕ)
    (hA : ∀ i < k, A i ⊆ range K ∧ (A i).card = 3)
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (A i) (A j)) :
    (uniform (Equiv.Perm (Fin K))).prob {η | ∀ i < k, listOf η i = A i} =
      (6 : ℝ) ^ k / (K.descFactorial (3 * k) : ℝ) := by
  classical
  -- the orderings of the given sets
  let idx : Fin k → Fin 3 → Fin K := fun i r => ⟨3 * i.val + r.val, by omega⟩
  let F : (∀ i : Fin k, Fin 3 ≃ ↥(A i)) → Set (Equiv.Perm (Fin K)) := fun β =>
    {η | ∀ i r, (η (idx i r)).val = ((β i r : ↥(A i)) : ℕ)}
  have hidx : ∀ (β : ∀ i : Fin k, Fin 3 ≃ ↥(A i)) (i i' : Fin k), i = i' →
      ∀ r r' : Fin 3, r = r' → ((β i r : ↥(A i)) : ℕ) = ((β i' r' : ↥(A i')) : ℕ) := by
    rintro β i _ rfl r _ rfl; rfl
  -- the event is the union of the `F β`
  have hE : ∀ η : Equiv.Perm (Fin K), (∀ i < k, listOf η i = A i) ↔ ∃ β, η ∈ F β := by
    intro η
    constructor
    · intro h
      have hmem : ∀ (i : Fin k) (r : Fin 3), (η (idx i r)).val ∈ A i := by
        intro i r
        rw [← h i.1 i.2, mem_listOf]
        exact ⟨idx i r, by simp only [idx]; omega, rfl⟩
      let g : ∀ i : Fin k, Fin 3 → ↥(A i) := fun i r => ⟨_, hmem i r⟩
      have hg : ∀ i, Function.Bijective (g i) := by
        intro i
        rw [Fintype.bijective_iff_injective_and_card]
        refine ⟨fun r r' hr => ?_, by simp [(hA i.1 i.2).2]⟩
        have h1 : η (idx i r) = η (idx i r') := Fin.ext (congrArg Subtype.val hr)
        have h2 := congrArg Fin.val (η.injective h1)
        simp only [idx] at h2
        exact Fin.ext (by omega)
      exact ⟨fun i => Equiv.ofBijective (g i) (hg i), fun i r => rfl⟩
    · rintro ⟨β, hβ⟩ i hi
      ext n
      rw [mem_listOf]
      constructor
      · rintro ⟨a, ha, rfl⟩
        have hr : a.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
        have ha' : a = idx ⟨i, hi⟩ ⟨a.val % 3, hr⟩ := Fin.ext (by simp only [idx]; omega)
        rw [ha', hβ]
        exact (β ⟨i, hi⟩ _).2
      · intro hn
        refine ⟨idx ⟨i, hi⟩ ((β ⟨i, hi⟩).symm ⟨n, hn⟩), by simp only [idx]; omega, ?_⟩
        rw [hβ, Equiv.apply_symm_apply]
  -- the `F β` are pairwise disjoint
  have hdisjF : ∀ β β' η, η ∈ F β → η ∈ F β' → β = β' := by
    intro β β' η h h'
    funext i
    ext r
    rw [← h i r, ← h' i r]
  -- each `F β` has probability `1/(K)_{3k}`
  have hF : ∀ β, (uniform (Equiv.Perm (Fin K))).prob (F β) =
      1 / (K.descFactorial (3 * k) : ℝ) := by
    intro β
    have hlt : ∀ j : Fin (3 * k), j.val / 3 < k := fun j => by omega
    let c : Fin (3 * k) → Fin K := fun j =>
      ⟨((β ⟨j.val / 3, hlt j⟩ ⟨j.val % 3, Nat.mod_lt _ (by norm_num)⟩ : ↥(A _)) : ℕ),
        mem_range.1 ((hA _ (hlt j)).1 (β ⟨j.val / 3, hlt j⟩ _).2)⟩
    have hc : Function.Injective c := by
      intro j j' h
      have hv := congrArg Fin.val h
      simp only [c] at hv
      by_cases hij : j.val / 3 = j'.val / 3
      · have hinj : ∀ (i i' : Fin k), i = i' → ∀ r r' : Fin 3,
            ((β i r : ↥(A i)) : ℕ) = ((β i' r' : ↥(A i')) : ℕ) → r = r' := by
          rintro i _ rfl r r' h
          exact (β i).injective (Subtype.ext h)
        have := hinj _ _ (Fin.ext hij) _ _ hv
        have := congrArg Fin.val this
        simp only at this
        exact Fin.ext (by omega)
      · exfalso
        have m1 := (β ⟨j.val / 3, hlt j⟩ ⟨j.val % 3, Nat.mod_lt _ (by norm_num)⟩).2
        have m2 := (β ⟨j'.val / 3, hlt j'⟩ ⟨j'.val % 3, Nat.mod_lt _ (by norm_num)⟩).2
        rw [← hv] at m2
        exact disjoint_left.1 (hdisj _ (hlt j) _ (hlt j') hij) m1 m2
    have hnd : (List.ofFn c).Nodup := List.nodup_ofFn.2 hc
    have key := prob_rankList_take (W := Fin K) (n := K) univ (List.ofFn c) hnd
      (fun _ _ => mem_univ _)
    rw [List.length_ofFn, card_univ, Fintype.card_fin] at key
    have hset : F β = (Equiv.inv (Equiv.Perm (Fin K))) ⁻¹'
        {o : Fin K ≃ Fin K | (rankList o univ).take (3 * k) = List.ofFn c} := by
      ext η
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, F]
      show _ ↔ (rankList η.symm univ).take (3 * k) = List.ofFn c
      rw [rankList_univ, Equiv.symm_symm, take_ofFn_eq_iff hk]
      constructor
      · intro h j
        have := h ⟨j.val / 3, hlt j⟩ ⟨j.val % 3, Nat.mod_lt _ (by norm_num)⟩
        refine Fin.ext ?_
        have e : Fin.castLE hk j = idx ⟨j.val / 3, hlt j⟩ ⟨j.val % 3, Nat.mod_lt _ (by norm_num)⟩ :=
          Fin.ext (by simp only [idx, Fin.val_castLE]; omega)
        rw [e, this]
      · intro h i r
        have := congrArg Fin.val (h ⟨3 * i.val + r.val, by omega⟩)
        have e : Fin.castLE hk ⟨3 * i.val + r.val, by omega⟩ = idx i r := Fin.ext rfl
        rw [e] at this
        rw [this]
        simp only [c]
        exact hidx β _ _ (Fin.ext (by simp only; omega)) _ _ (Fin.ext (by simp only; omega))
    rw [hset, ← prob_map, map_equiv_uniform]
    exact key
  -- sum over the orderings
  have hsum : (uniform (Equiv.Perm (Fin K))).prob {η | ∀ i < k, listOf η i = A i} =
      ∑ β : (∀ i : Fin k, Fin 3 ≃ ↥(A i)), (uniform (Equiv.Perm (Fin K))).prob (F β) := by
    simp_rw [prob_eq_expect]
    rw [← expect_sum]
    refine expect_congr _ fun η _ => ?_
    by_cases h : ∀ i < k, listOf η i = A i
    · obtain ⟨β0, hβ0⟩ := (hE η).1 h
      rw [Set.indicator_of_mem (show η ∈ {η | ∀ i < k, listOf η i = A i} from h),
        sum_eq_single β0 (fun β _ hne => Set.indicator_of_notMem
          (fun hm => hne (hdisjF _ _ _ hm hβ0)) _) (fun h' => absurd (mem_univ _) h'),
        Set.indicator_of_mem hβ0]
    · rw [Set.indicator_of_notMem (show η ∉ {η | ∀ i < k, listOf η i = A i} from h)]
      exact (sum_eq_zero fun β _ =>
        Set.indicator_of_notMem (fun hm => h ((hE η).2 ⟨β, hm⟩)) _).symm
  have hcard : Fintype.card (∀ i : Fin k, Fin 3 ≃ ↥(A i)) = 6 ^ k := by
    rw [Fintype.card_pi]
    have : ∀ i : Fin k, Fintype.card (Fin 3 ≃ ↥(A i)) = 6 := by
      intro i
      have e : Fin 3 ≃ ↥(A i) :=
        Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, (hA i.1 i.2).2])
      rw [Fintype.card_equiv e, Fintype.card_fin]
      rfl
    simp [this]
  rw [hsum, sum_congr rfl fun β _ => hF β, sum_const, card_univ, hcard, nsmul_eq_mul]
  push_cast
  ring

/-- The lists regrouped by hub: the pair `(η_x, (ζ_{x,u})_u)` for every vertex `x`. -/
def listsByHub {V : Type*} [DecidableEq V] (G : FGraph V) (M : ℕ) :
    (↥G.verts → Equiv.Perm (Fin (4 * M)) × (↥G.verts → Finset (Fin (4 * M)))) ≃ Lists G M where
  toFun f := (fun x => (f x).1, fun p => (f p.1).2 p.2)
  invFun L := fun x => (L.1 x, fun u => L.2 (x, u))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The law of the lists is the product over the vertices `x` of the laws of
`(η_x, (ζ_{x,u})_u)`. -/
theorem listsLaw_eq_map {V : Type*} [DecidableEq V] (G : FGraph V) (M : ℕ) :
    listsLaw G M = (pi fun _ : ↥G.verts => (uniform (Equiv.Perm (Fin (4 * M)))).prod
      (pi fun _ : ↥G.verts => subset3Law (4 * M))).map (listsByHub G M) := by
  ext L
  rw [map_equiv_w]
  unfold listsLaw
  simp only [prod_w', pi_w]
  rw [Finset.prod_mul_distrib, ← Fintype.prod_prod_type']
  rfl

/-- Functions of the lists of pairwise disjoint sets of hubs are mutually independent ("Lists of
distinct hubs are independent"). -/
theorem iIndepFun_listsLaw {V : Type*} [DecidableEq V] (G : FGraph V) (M : ℕ) {U : Type*}
    {β : U → Type*} (B : U → Set ↥G.verts) (hB : Pairwise fun u v => Disjoint (B u) (B v))
    (X : ∀ u, Lists G M → β u)
    (hX : ∀ u (L L' : Lists G M), (∀ x ∈ B u, L.1 x = L'.1 x ∧ ∀ y, L.2 (x, y) = L'.2 (x, y)) →
      X u L = X u L') :
    (listsLaw G M).iIndepFun X := by
  rw [listsLaw_eq_map, iIndepFun_map_iff]
  refine iIndepFun_pi_of_dependsOn _ B hB _ fun u f f' h => hX u _ _ fun x hx => ?_
  have e := h x hx
  exact ⟨congrArg Prod.fst e, fun y => congrFun (congrArg Prod.snd e) y⟩

end EG.Quot
