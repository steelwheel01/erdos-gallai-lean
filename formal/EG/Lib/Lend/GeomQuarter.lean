module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Real.Basic

/-!
# A geometric bound for the JS class count (manuscript s3:lemCOLJV (i)) — P3-s3

"`|I^JS(Y)| = Σ_{l=r+2}^R M_l^2 ≤ M^2 Σ_{i≥0} 4^{-i} = (4/3) M^2`": if a non-negative sequence
decreases by a factor `4` at each step, its partial sums are at most `4/3` of the first term.
-/

public section

namespace EG

/-- If `f(a+k+1) ≤ f(a+k)/4` for `k < n` and `f ≥ 0`, then `Σ_{k ≤ n} f(a+k) ≤ (4/3) f(a)`. -/
theorem sum_range_le_of_quarter (f : ℕ → ℝ) (hf0 : ∀ k, 0 ≤ f k) :
    ∀ (n a : ℕ), (∀ k < n, f (a + k + 1) ≤ f (a + k) / 4) →
      ∑ k ∈ Finset.range (n + 1), f (a + k) ≤ 4 / 3 * f a := by
  intro n
  induction n with
  | zero =>
    intro a _
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, add_zero]
    linarith [hf0 a]
  | succ n ih =>
    intro a h
    rw [Finset.sum_range_succ']
    have h1 := ih (a + 1) (fun k hk => by
      have := h (k + 1) (by omega)
      rwa [show a + (k + 1) + 1 = a + 1 + k + 1 by omega, show a + (k + 1) = a + 1 + k by omega]
        at this)
    have e : ∀ k, a + (k + 1) = a + 1 + k := fun k => by omega
    rw [Finset.sum_congr rfl (fun k _ => by rw [e k]), add_zero]
    have h0 := h 0 (by omega)
    simp only [add_zero] at h0
    linarith

/-- The same bound over an interval `[a, b]` of naturals. -/
theorem sum_Icc_le_of_quarter (f : ℕ → ℝ) (hf0 : ∀ k, 0 ≤ f k) (a b : ℕ)
    (h : ∀ l, a ≤ l → l + 1 ≤ b → f (l + 1) ≤ f l / 4) :
    ∑ l ∈ Finset.Icc a b, f l ≤ 4 / 3 * f a := by
  by_cases hab : a ≤ b
  · have e : Finset.Icc a b = Finset.Ico a (b + 1) := by
      ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sum_range, show b + 1 - a = (b - a) + 1 by omega]
    exact sum_range_le_of_quarter f hf0 (b - a) a (fun k hk => h (a + k) (by omega) (by omega))
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    linarith [hf0 a]

end EG
