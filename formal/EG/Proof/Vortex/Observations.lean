module

public import EG.Spec.Vortex.Observations
public import EG.Lib.Vortex.Ends

/-!
# Proofs of the vortex observations (S), (E), (C) (manuscript s4, "Conventions and elementary
observations") — unit P4A, stage 3

The list surgery is in `EG/Lib/Vortex/Trail.lean` ((S): cycle removal at the first repetition;
(C)) and the double counting in `EG/Lib/Vortex/Ends.lean` ((E)).
-/

public section

namespace EG

universe u

/-- [s4:eqSplit] (S) "Then `E(T)` is the disjoint union of the edge sets of at most `rep(T)`
cycles, each of length at least `3`, and of at most one path …". Proof: induction, removing the
cycle at the first repetition (`EG.splitOut_exists`). -/
theorem trailSplit : EG.Spec.TrailSplitStatement.{u} := by
  intro V _ T hT hE hD
  exact splitOut_exists hT hE hD

/-- [s4:eqSplit] (S), last sentence: "if the inner vertices `x_1,…,x_{q-1}` are pairwise
distinct, then `rep(T) ≤ 2`". -/
theorem trailRepInner : EG.Spec.TrailRepInnerStatement.{u} := by
  intro V _ T h
  exact rep_le_two_of_interior_nodup h

/-- [s4:eqEnds] (E), first sentence: "A path contributes `2` to the degree of each of its inner
vertices and `1` to the degree of each of its two (distinct) ends." -/
theorem pathEndsParity : EG.Spec.PathEndsParityStatement.{u} := by
  intro V _ F P h v
  exact h.pathEndCount_mod_two v

/-- [s4:eqEnds] (E), second sentence: "count path ends: `2|𝒫| ≤ 2|W|`". -/
theorem pathEndsCount : EG.Spec.PathEndsCountStatement.{u} := by
  intro V _ F P W h h2 hW
  exact h.length_le_card h2 hW

/-- [s4:eqClose] (C) "The only common vertices of `Q` and `Q'` are `x` and `y`, so `Q ∪ Q'` is a
cycle; its length is `|E(Q)| + |E(Q')| ≥ 2 + 1`." -/
theorem closing : EG.Spec.ClosingStatement.{u} := by
  intro V _ Q Q' x y hQ hQ2 hQx hQy hQ' hQ'x hQ'y hint _
  exact closing_aux hQ hQ2 hQx hQy hQ' hQ'x hQ'y hint

end EG
