module

public import EG.Spec.Vortex.PVCore
public import EG.Lib.Vortex.Params
public import EG.Lib.Vortex.StepCost
public import EG.Lib.Vortex.Strip

/-!
# Proofs of the PV(c) core (manuscript s4:lemPV, proof) — unit P4A

Stage 1 proved the two arithmetic nodes `EG.pvStepCost` ((s4:eqPVstep)) and `EG.pvT`
((s4:eqPVt)). Stage 3 (proof round 1) adds `EG.pvStepPhase` (the construction is in
`EG/Lib/Vortex/StepPhase.lean` … `StepCost.lean`), `EG.pvStrip` (`EG/Lib/Vortex/Strip.lean`) and
`EG.pvArcEndsDeg` (`EG/Lib/Vortex/Ends.lean`). The finish `EG.pvFinish` is in
`EG/Proof/Vortex/PVFinish.lean` (it uses the declared input `EG.cor22`). Design note
`formal/work/p2b/P4A.md`.
-/

public section

namespace EG

/-- [s4:lemPV] (s4:eqPVstep) "`4|W_j| + 4·3(2|Pl ∩ U_{j+1}| + 2|W_j|) ≤ 28|Pl ∩ U_j|`", using
`W_j ⊔ (Pl ∩ U_{j+1}) = Pl ∩ U_j`. -/
theorem pvStepCost : EG.Spec.PVStepCostStatement := by
  intro V _ W Up h
  rw [Finset.card_union_of_disjoint h]
  omega

/-- [s4:lemPV] (s4:eqPVt) "`2 + b ≤ 2^7L^8 + 2^7L^2 + 3 ≤ 2^9L^8 = t`". -/
theorem pvT : EG.Spec.PVtStatement := by
  intro N hL
  have hL0 : 0 ≤ Vortex.L N := Vortex.L_nonneg N
  have hm := Vortex.pvM_lt N
  have hb := Vortex.pvB_lt N
  have h1 : (1 : ℝ) ≤ Vortex.L N := le_trans (by norm_num) hL
  set L := Vortex.L N
  refine ⟨?_, ?_⟩
  · have : (2 : ℝ) ^ 7 * L ^ 2 * (Vortex.pvM N : ℝ) ≤ 2 ^ 7 * L ^ 2 * (L ^ 6 + 1) :=
      mul_le_mul_of_nonneg_left hm.le (by positivity)
    nlinarith
  · have h2 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ h1 (by norm_num)
    have h3 : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ h1
    nlinarith

universe u

/-- [s4:lemPV] (proof, steps (iv)–(vi) for one phase and "Cost of step `j`"; CR1-PV). The trails
of step (iv) (`EG.PVStep.trail`: each path of `Paths_{j,c}` with the reserved edges appended at its
ends in `W_j`, the first path ending at `w` getting `e^{c,1}_w`), split by (S); single edges for
`w` an end of one path, cherries for `w` an end of none; paths with both ends in `Rt` are arcs. -/
theorem pvStepPhase : EG.Spec.PVStepPhaseStatement.{u} := by
  intro V _ Rt W Up F P u₁ u₂ h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hyp : PVStep.Hyp Rt W Up F P u₁ u₂ := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨Cs, qs, hCq⟩ := hyp.exists_splits
  exact ⟨PVStep.outD Rt W P u₂ Cs, PVStep.outA Rt P, PVStep.outQ Rt W P u₁ u₂ qs,
    hyp.output_props hCq⟩

/-- [s4:lemPV] (proof, "Finish", stripping; CR1-PV): "If an end `p` of `T` lies in `Pl_J`, the
edge of `T` at `p` lies in `E_2`, so its other end lies in `Rt`; output this edge as a single
edge". -/
theorem pvStrip : EG.Spec.PVStripStatement.{u} := by
  intro V _ Rt PlJ T hdis hT h2 hV hE
  exact strip_exists hdis hT h2 hV hE

/-- [s4:lemPV] (c), the per-vertex bound (CR1-PV): "An arc with end `x` contains exactly one edge
at `x` …, and distinct arcs are edge-disjoint; so `x` is an end of at most `deg_{H_0}(x)` arcs.
Every edge of `H_0` at `x` joins `x` to a vertex of `Z \ {x}`, and distinct edges at `x` have
distinct other ends …; hence `deg_{H_0}(x) ≤ |Z| - 1`." -/
theorem pvArcEndsDeg : EG.Spec.PVArcEndsDegStatement.{u} := by
  intro V _ Z H0 Harc arcs hD hZ hsub hdec x
  exact ⟨(hdec.pathEndCount_le_degE x).trans (FGraph.degE_mono hsub x),
    degE_le_card_sub_one hD hZ x⟩

end EG
