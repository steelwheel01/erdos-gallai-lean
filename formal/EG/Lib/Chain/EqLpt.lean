module

public import EG.Defs.Chain.EqLpt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Greedy LPT placement: basic API (companion of `EG.Defs.Chain.EqLpt`)

* before the first item every layer is empty and has load `0`;
* the final layer loads add up to the total load (`EG.Chain.sum_layerLoad`), and they are
  non-negative for non-negative item loads.
-/

public section

namespace EG.Chain

variable {m k : ℕ}

theorem emptyBefore_of_forall_le (σ : Fin m → Fin k) {i : Fin m} (hi : ∀ i' : Fin m, i ≤ i')
    (j : Fin k) : EmptyBefore σ i j :=
  fun i' hi' => absurd (hi i') (not_le.2 hi')

theorem loadBefore_of_forall_le (Φ : Fin m → ℝ) (σ : Fin m → Fin k) {i : Fin m}
    (hi : ∀ i' : Fin m, i ≤ i') (j : Fin k) : loadBefore Φ σ i j = 0 := by
  unfold loadBefore
  refine Finset.sum_eq_zero fun i' hi' => ?_
  exact absurd (hi i') (not_le.2 (Finset.mem_filter.1 hi').2.1)

/-- The final layer loads add up to the total load `∑_i Φ_i`. -/
theorem sum_layerLoad (Φ : Fin m → ℝ) (σ : Fin m → Fin k) :
    ∑ j, layerLoad Φ σ j = ∑ i, Φ i := by
  unfold layerLoad
  exact Finset.sum_fiberwise Finset.univ σ Φ

theorem layerLoad_nonneg {Φ : Fin m → ℝ} (hΦ : ∀ i, 0 ≤ Φ i) (σ : Fin m → Fin k) (j : Fin k) :
    0 ≤ layerLoad Φ σ j :=
  Finset.sum_nonneg fun i _ => hΦ i

end EG.Chain
