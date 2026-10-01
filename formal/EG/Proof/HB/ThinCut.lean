module

public import EG.Spec.HB.ThinCut
public import EG.Lib.HB.SEP

/-!
# Proof of the thin-cut lemma (manuscript s2:lemThinCut)

Unit P3A, proof round 1. Design note `formal/work/p2b/P3A.md`. The argument is
`EG.HB.STree.thinCut_lt` (count `< τ`) and `EG.HB.STree.thinCut_eq_zero` in `EG.Lib.HB.SEP`;
they use only that the labels are produced by the `τ`-rules from some pair `(U, N)`
(`STree.TauLabels`), as the manuscript remarks ("the argument below uses only the structure of
the `τ`-rules").

* `EG.thinCut : EG.Spec.ThinCutStatement`;
* `EG.thinCutEdge : EG.Spec.ThinCutEdgeStatement`.
-/

public section

namespace EG

open EG.HB EG.HB.STree

namespace HB

/-- A natural number `< τ` is `≤ ⌈τ⌉ - 1`. -/
theorem natCast_le_ceil_sub_one {n : ℕ} {τ : ℝ} (h : (n : ℝ) < τ) : (n : ℤ) ≤ ⌈τ⌉ - 1 := by
  have h1 : ((n : ℤ) : ℝ) < τ := by exact_mod_cast h
  have := Int.lt_ceil.2 h1
  omega

/-- A natural number `< k` is `≤ k - 1`. -/
theorem le_sub_one_of_cast_lt {n k : ℕ} {τ : ℝ} (h : (n : ℝ) < τ) (hk : τ = k) : n ≤ k - 1 := by
  rw [hk] at h
  have : n < k := by exact_mod_cast h
  omega

end HB

/-- [s2:lemThinCut] (main part) "for every leaf `Leaf` and every vertex `h`,
`#{deleted edges hu : u ∈ V(Leaf) \ Dup} ≤ ⌈τ⌉ - 1`, which is `τ - 1` when `τ` is an integer (as
in all applications), and this number is `0` if `h ∈ V(Leaf)`." -/
theorem thinCut : EG.Spec.ThinCutStatement := by
  intro V _ H t τ hτ ht L hL h
  have hlt := thinCut_lt hτ ht.tauLabels hL h
  exact ⟨HB.natCast_le_ceil_sub_one hlt, fun k hk => HB.le_sub_one_of_cast_lt hlt hk,
    fun hh => thinCut_eq_zero hL hh⟩

/-- [s2:lemThinCut] (Moreover) "if `u ∉ Dup` then every edge at `u` is either deleted or an edge
of the unique leaf containing `u`." -/
theorem thinCutEdge : EG.Spec.ThinCutEdgeStatement := by
  intro V _ H t τ _ _ u hu e he hue
  exact thinCut_edge t hu he hue

end EG
