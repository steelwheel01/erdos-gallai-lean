module

public import EG.Spec.Quot.UHsplit
public import EG.Proof.Todo.UHsplitSum
public import EG.Proof.Todo.UHsplitDet
public import EG.Proof.Todo.EXprime

/-!
# P3 stub: `EG.Spec.UHsplitThetaStatement` (s7:lemUHsplit)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.UHsplitTheta`; consumers import this module.

Proof (manuscript s7:lemUHsplit (iv)): by (iii) (`EG.Todo.UHsplitSum`),
`Σ_l |V(Q_l)| ≤ 12 E X' + 4Σ_l det_l`; by Lemma s7:lemEXprime (`EG.Todo.EXprime`),
`E X' ≤ ε_X(D_*) n`; by (iv), first sentence (`EG.Todo.UHsplitDet`),
`Σ_l det_l ≤ 3ε_A n + 60n/D_* + 2F(log₂D_*) n`. The sum is `ε_2(D_*) n`.
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- Proved in P3. [s7:lemUHsplit] see `EG.Spec.UHsplitThetaStatement`. -/
theorem UHsplitTheta : EG.Spec.UHsplitThetaStatement := by
  intro V _ G N0 Dstar run δ hR hδ ω hω hX Js hJs Rs hRs ξs hξ
  have h1 := Todo.UHsplitSum V G N0 Dstar run δ hR hδ ω hω hX Js hJs Rs hRs ξs hξ
  have h2 := (Todo.EXprime V G N0 Dstar run δ hR hδ).1
  have h3 := (Todo.UHsplitDet V G N0 Dstar run hR).1
  have he : eps2 Dstar * (G.card : ℝ) =
      12 * (epsX Dstar * (G.card : ℝ)) +
        4 * (3 * epsA Dstar * (G.card : ℝ) + 60 * (G.card : ℝ) / Dstar +
          2 * FQ (Real.logb 2 Dstar) * (G.card : ℝ)) := by
    unfold eps2; ring
  rw [he]
  linarith

end EG.Todo
