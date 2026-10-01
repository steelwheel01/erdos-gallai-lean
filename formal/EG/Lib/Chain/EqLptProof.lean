module

public import EG.Lib.Chain.EqLpt
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Max

/-!
# Lemma EQ-LPT: existence and properties of greedy placements (manuscript s6:lemEQLPT)

Probe unit P2E (probe P-2, part 1), proof round 1.
* `EG.Chain.exists_isGreedyLPT`: "An empty layer has load `0`, which is minimum. So the rule is
  consistent": a greedy placement exists (built item by item; the rule for item `i` reads only
  the placement of the items before `i`);
* `EG.Chain.IsGreedyLPT.surjective`: "the first `k` items go to the `k` distinct empty layers.
  Since `k ≤ m`, every layer is non-empty" (a layer that stays empty forces every item to a
  fresh layer, so `σ` would be injective into the other `k − 1` layers);
* `EG.Chain.IsGreedyLPT.layerLoad_sub_le`: "Let `j^*` be a layer of maximum final load and `x`
  the last item placed in it ... `max_j Φ^lay_j ≤ min_j Φ^lay_j + Φ_1`", for any two layers.
-/

public section

namespace EG.Chain

variable {m k : ℕ}

/-- `loadBefore` at item `i` reads only the placement of the items before `i`. -/
theorem loadBefore_congr (Φ : Fin m → ℝ) {σ τ : Fin m → Fin k} {i : Fin m}
    (h : ∀ i', i' < i → σ i' = τ i') (j : Fin k) : loadBefore Φ σ i j = loadBefore Φ τ i j := by
  unfold loadBefore
  congr 1
  ext i'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h i' h1).symm.trans h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h i' h1).trans h2⟩

theorem emptyBefore_congr {σ τ : Fin m → Fin k} {i : Fin m} (h : ∀ i', i' < i → σ i' = τ i')
    (j : Fin k) : EmptyBefore σ i j ↔ EmptyBefore τ i j := by
  unfold EmptyBefore
  constructor
  · intro h' i' hi'; rw [← h i' hi']; exact h' i' hi'
  · intro h' i' hi'; rw [h i' hi']; exact h' i' hi'

/-- The greedy condition at item `i` (one conjunct of `IsGreedyLPT`). -/
@[expose] def GreedyAt (Φ : Fin m → ℝ) (σ : Fin m → Fin k) (i : Fin m) : Prop :=
  (∀ j : Fin k, loadBefore Φ σ i (σ i) ≤ loadBefore Φ σ i j) ∧
    ((∃ j : Fin k, EmptyBefore σ i j) → EmptyBefore σ i (σ i))

theorem greedyAt_congr (Φ : Fin m → ℝ) {σ τ : Fin m → Fin k} {i : Fin m}
    (h : ∀ i', i' ≤ i → σ i' = τ i') : GreedyAt Φ σ i ↔ GreedyAt Φ τ i := by
  have hlt : ∀ i', i' < i → σ i' = τ i' := fun i' hi' => h i' hi'.le
  unfold GreedyAt
  rw [h i le_rfl]
  simp only [loadBefore_congr Φ hlt, emptyBefore_congr hlt]

/-- An empty layer has load `0`. -/
theorem loadBefore_eq_zero_of_emptyBefore (Φ : Fin m → ℝ) {σ : Fin m → Fin k} {i : Fin m}
    {j : Fin k} (h : EmptyBefore σ i j) : loadBefore Φ σ i j = 0 := by
  unfold loadBefore
  refine Finset.sum_eq_zero fun i' hi' => ?_
  rw [Finset.mem_filter] at hi'
  exact absurd hi'.2.2 (h i' hi'.2.1)

theorem loadBefore_nonneg {Φ : Fin m → ℝ} (hΦ : ∀ i, 0 ≤ Φ i) (σ : Fin m → Fin k) (i : Fin m)
    (j : Fin k) : 0 ≤ loadBefore Φ σ i j :=
  Finset.sum_nonneg fun i _ => hΦ i

/-- The greedy choice for item `i` exists, whatever the placement of the earlier items. -/
theorem exists_greedy_choice (hk : 1 ≤ k) {Φ : Fin m → ℝ} (hΦ : ∀ i, 0 ≤ Φ i)
    (σ : Fin m → Fin k) (i : Fin m) :
    ∃ c : Fin k, (∀ j, loadBefore Φ σ i c ≤ loadBefore Φ σ i j) ∧
      ((∃ j, EmptyBefore σ i j) → EmptyBefore σ i c) := by
  by_cases he : ∃ j, EmptyBefore σ i j
  · obtain ⟨c, hc⟩ := he
    refine ⟨c, fun j => ?_, fun _ => hc⟩
    rw [loadBefore_eq_zero_of_emptyBefore Φ hc]
    exact loadBefore_nonneg hΦ σ i j
  · have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    obtain ⟨c, -, hc⟩ := Finset.exists_min_image Finset.univ (loadBefore Φ σ i) hne
    exact ⟨c, fun j => hc j (Finset.mem_univ _), fun h => absurd h he⟩

/-- Greedy placement of the first `n` items. -/
theorem exists_greedy_prefix (hk : 1 ≤ k) {Φ : Fin m → ℝ} (hΦ : ∀ i, 0 ≤ Φ i) :
    ∀ n : ℕ, ∃ σ : Fin m → Fin k, ∀ i : Fin m, i.val < n → GreedyAt Φ σ i
  | 0 => ⟨fun _ => ⟨0, hk⟩, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨σ, hσ⟩ := exists_greedy_prefix hk hΦ n
    by_cases hn : n < m
    · set i0 : Fin m := ⟨n, hn⟩
      obtain ⟨c, hc1, hc2⟩ := exists_greedy_choice hk hΦ σ i0
      refine ⟨Function.update σ i0 c, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · -- earlier items are unchanged
        refine (greedyAt_congr Φ fun i' hi' => ?_).2 (hσ i hi)
        have : i' ≠ i0 := by
          intro h; subst h; exact absurd (Fin.le_def.1 hi') (by simp [i0]; omega)
        exact Function.update_of_ne this c σ
      · have hii : i = i0 := Fin.ext hi
        subst hii
        have hlt : ∀ i', i' < i0 → Function.update σ i0 c i' = σ i' :=
          fun i' hi' => Function.update_of_ne (ne_of_lt hi') c σ
        unfold GreedyAt
        rw [Function.update_self]
        simp only [loadBefore_congr Φ hlt, emptyBefore_congr hlt]
        exact ⟨hc1, hc2⟩
    · exact ⟨σ, fun i hi => hσ i (by have := i.2; omega)⟩

/-- [s6:lemEQLPT] (proof) "An empty layer has load `0`, which is minimum. So the rule is
consistent": for `k ≥ 1` and non-negative loads a greedy placement exists. -/
theorem exists_isGreedyLPT (hk : 1 ≤ k) {Φ : Fin m → ℝ} (hΦ : ∀ i, 0 ≤ Φ i) :
    ∃ σ : Fin m → Fin k, IsGreedyLPT Φ σ := by
  obtain ⟨σ, hσ⟩ := exists_greedy_prefix hk hΦ m
  exact ⟨σ, fun i => hσ i i.2⟩

/-- [s6:lemEQLPT] (proof) "the first `k` items go to the `k` distinct empty layers. Since
`k ≤ m`, every layer is non-empty." -/
theorem IsGreedyLPT.surjective {Φ : Fin m → ℝ} {σ : Fin m → Fin k} (hσ : IsGreedyLPT Φ σ)
    (hkm : k ≤ m) : Function.Surjective σ := by
  intro j
  by_contra hj
  push Not at hj
  -- `j` is empty before every item, so every item goes to a layer empty before it
  have hinj : Function.Injective σ := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hσ b).2 ⟨j, fun i' _ => hj i'⟩ a h hab
    · exact (hσ a).2 ⟨j, fun i' _ => hj i'⟩ b h hab.symm
  have hsub : Finset.univ.image σ ⊆ Finset.univ.erase j := fun x hx => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_erase.2 ⟨hj a, Finset.mem_univ _⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at this
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact j.elim0
    · exact h
  omega

/-- "loads only grow": the load of a layer before an item is at most its final load. -/
theorem loadBefore_le_layerLoad {Φ : Fin m → ℝ} (hΦ : ∀ i, 0 ≤ Φ i) (σ : Fin m → Fin k)
    (i : Fin m) (j : Fin k) : loadBefore Φ σ i j ≤ layerLoad Φ σ j := by
  unfold loadBefore layerLoad
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x _ _ => hΦ x)
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.2⟩

/-- The final load of a layer is its load before its last item `x` plus `Φ_x`. -/
theorem layerLoad_eq_loadBefore_add {Φ : Fin m → ℝ} (σ : Fin m → Fin k) {j : Fin k} {x : Fin m}
    (hx : σ x = j) (hlast : ∀ i, σ i = j → i ≤ x) :
    layerLoad Φ σ j = loadBefore Φ σ x j + Φ x := by
  unfold layerLoad loadBefore
  have hset : Finset.univ.filter (fun i => σ i = j) =
      insert x (Finset.univ.filter (fun i' => i' < x ∧ σ i' = j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le (hlast i h) with h' | h'
      · exact Or.inr ⟨h', h⟩
      · exact Or.inl h'
    · rintro (rfl | ⟨-, h⟩)
      · exact hx
      · exact h
  rw [hset, Finset.sum_insert (by simp), add_comm]

/-- [s6:lemEQLPT] "the final layer loads satisfy `max_j Φ^lay_j − min_j Φ^lay_j ≤ Φ_1`": for any
two layers `j, j'`, `Φ^lay_j − Φ^lay_{j'} ≤ Φ_1`. -/
theorem IsGreedyLPT.layerLoad_sub_le {Φ : Fin m → ℝ} {σ : Fin m → Fin k} (hσ : IsGreedyLPT Φ σ)
    (hanti : Antitone Φ) (hΦ : ∀ i, 0 ≤ Φ i) (hm : 0 < m) (j j' : Fin k) :
    layerLoad Φ σ j - layerLoad Φ σ j' ≤ Φ ⟨0, hm⟩ := by
  by_cases hne : (Finset.univ.filter (fun i => σ i = j)).Nonempty
  · -- `x`: the last item placed in `j`
    set x := (Finset.univ.filter (fun i => σ i = j)).max' hne
    have hx : σ x = j := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
    have hlast : ∀ i, σ i = j → i ≤ x := fun i hi =>
      Finset.le_max' _ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    rw [layerLoad_eq_loadBefore_add σ hx hlast]
    have h1 : loadBefore Φ σ x j ≤ loadBefore Φ σ x j' := by
      have := (hσ x).1 j'
      rwa [hx] at this
    have h2 := loadBefore_le_layerLoad hΦ σ x j'
    have h3 : Φ x ≤ Φ ⟨0, hm⟩ := hanti (Fin.le_def.2 (Nat.zero_le _))
    linarith
  · have h0 : layerLoad Φ σ j = 0 := by
      unfold layerLoad
      rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    rw [h0]
    have := layerLoad_nonneg hΦ σ j'
    have := hΦ ⟨0, hm⟩
    linarith

end EG.Chain
