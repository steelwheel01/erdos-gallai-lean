module

public import EG.Spec.Link.Multiset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# P3 stub: `EG.Spec.MultisetCountStatement` (s3:remMultiset)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.MultisetCount`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:remMultiset] see `EG.Spec.MultisetCountStatement`. -/
theorem MultisetCount : EG.Spec.MultisetCountStatement := by
  intro V _ ι _ P t I I' _hne ht hsub hdisj hmax
  classical
  set W : Finset V := I'.biUnion (fun j => ({(P j).1, (P j).2} : Finset V)) with hW
  set F : V → Finset ι := fun v => Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)
    with hF
  -- `|W| ≤ 2|I'|`
  have hWc : W.card ≤ 2 * I'.card := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ j ∈ I', ({(P j).1, (P j).2} : Finset V).card ≤ ∑ _j ∈ I', 2 :=
          Finset.sum_le_sum fun j _ => Finset.card_le_two
      _ = 2 * I'.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- every pair of `I` meets `W`
  have hcov : I ⊆ W.biUnion F := by
    intro i hi
    rw [Finset.mem_biUnion]
    by_cases hi' : i ∈ I'
    · refine ⟨(P i).1, ?_, ?_⟩
      · rw [hW, Finset.mem_biUnion]; exact ⟨i, hi', by simp⟩
      · simp [hF]
    · have h := hmax i hi hi'
      rw [Set.pairwiseDisjoint_insert] at h
      push Not at h
      obtain ⟨j, hj, -, hnd⟩ := h hdisj
      obtain ⟨v, hv1, hv2⟩ := Finset.not_disjoint_iff.1 hnd
      refine ⟨v, ?_, ?_⟩
      · rw [hW, Finset.mem_biUnion]; exact ⟨j, hj, hv2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv1
        simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hv1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
  have hcard : (I.card : ℝ) ≤ (W.card : ℝ) * t := by
    have h1 : I.card ≤ ∑ v ∈ W, (F v).card :=
      (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    have h2 : ((∑ v ∈ W, (F v).card : ℕ) : ℝ) ≤ ∑ _v ∈ W, t := by
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum fun v _ => ht v
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    exact (Nat.cast_le.2 h1).trans h2
  rcases I.eq_empty_or_nonempty with hI | ⟨i, hi⟩
  · have : I' = ∅ := Finset.subset_empty.1 (hI ▸ hsub)
    simp [hI, this]
  · have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg _) (ht (P i).1)
    have : (W.card : ℝ) ≤ 2 * (I'.card : ℝ) := by exact_mod_cast hWc
    nlinarith

end EG.Todo
