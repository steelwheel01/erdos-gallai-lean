module

public import EG.Spec.Light.Demoted
public import EG.Spec.Light.Stages
public import EG.Spec.Vortex.VX
public import EG.Spec.Lend.COLJVRows
public import EG.Proof.Todo.VX
public import EG.Proof.Light.Stages
public import EG.Proof.Lend.COLJVRows
public import EG.Lib.Light.Stages
public import EG.Lib.Lend.Standing
public import EG.Lib.Gamma.Full

/-!
# P3 stub: `EG.Spec.LemDemotedStatement` (s5:lemDemoted)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.LemDemoted`; consumers import this module.

Proof (P3), as in `s5.tex`: a demoted part is not a good parent (Definition s5:defStages), so it is
not in `goodParents ω l`. `X_Y` is a spanning `(2^{-6}, s_r/2)`-expander on `Y` (the embedded claim
of s5:defStages, `EG.stagesHB`, declared input of probe P4B); `N = |Y| ≥ P_r/2 ≥ N_0` (Γ3,
`EG.Standing.card_ancVerts_ge`); the threshold `s_r/2 ≥ 2^{151}L^{38}log₂L` is row 8 (c) of
Table s3:tabCOLJV (`EG.colJVRow8`). Every edge of `E_r(Y)` has both ends in `Y`
(s2:propStructure (iii), `EG.Light.E_subset_sym2`), so `(Y, E)` is a graph containing `X_Y`, and
Theorem s4:thmVXp (`EG.Todo.VX`, deterministic form) gives a decomposition into at most
`38.4N + 13N ≤ 80N` objects.
-/

public section

namespace EG.Todo

open EG.HB EG.Stage1 EG.Light

/-- Proved in P3. [s5:lemDemoted] see `EG.Spec.LemDemotedStatement`. -/
theorem LemDemoted : EG.Spec.LemDemotedStatement := by
  classical
  intro V _ G N0 Dstar run hR ω _ Y hY hdem
  refine ⟨fun h => h.2.1 hdem, fun l hl => (Finset.mem_filter.1 hl).2.1.2.1 hdem, ?_⟩
  intro E hXE hEE
  have hLight := isLight_of_mem_lightParts hY
  have hanc : Y ∈ run.ancestors G := by
    unfold Run.lightParts at hY
    exact (Finset.mem_filter.1 hY).1
  have hHB := EG.stagesHB V G N0 Dstar run hR Y hY
  have row8 := (EG.colJVRow8 V G Dstar run hR.gamma1 hR.valid Y hanc).2.2.1
  -- the size condition `N ≥ N_0`
  have hN0 : N0 ≤ ((run.ancVerts G Y).card : ℝ) := by
    have hRd := Standing.isRound_of_mem_ancestors hanc
    have hcard := Standing.card_ancVerts_ge hanc
    have h3 := hR.gamma3
    unfold Gamma3 at h3
    have hD2 := hR.gamma1core.two_lt
    have hlogD : 0 ≤ Real.logb 2 Dstar := Real.logb_nonneg (by norm_num) (by linarith)
    have hd := Run.Valid.dstar_le run G hR.valid hRd
    have hlam : Real.logb 2 Dstar ≤ run.lam G Y.1 :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hd
    have hpow : Real.logb 2 Dstar ^ 103 ≤ run.lam G Y.1 ^ 103 := pow_le_pow_left₀ hlogD hlam 103
    have hCp : ((Cp : ℕ) : ℕ) = 103 := rfl
    rw [hCp] at h3
    linarith
  have hVX := hR.n0Cond.vx hN0
  -- the graph `(Y, E)`
  have hEsym : ∀ e ∈ E, ∀ v ∈ e, v ∈ run.ancVerts G Y := by
    intro e he v hv
    have := E_subset_sym2 (G := G) (run := run) Y.1 Y.2 (hEE he)
    exact Finset.mem_sym2_iff.1 this v hv
  have hEloop : ∀ e ∈ E, ¬ e.IsDiag := fun e he =>
    (run.graph' G Y.1).loopless e (Run.E_subset_graph'_edges run G Y.1 Y.2 (hEE he))
  let GY : FGraph V := ⟨run.ancVerts G Y, E, hEsym, hEloop⟩
  obtain ⟨⟨D, hD, hlen, -⟩, -⟩ := EG.Todo.VX V (run.ancVerts G Y) (run.X G Y.1 Y.2)
    (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / 2) hVX hHB.1 hHB.2.1 (Or.inr ⟨rfl, row8⟩) GY rfl hXE
  refine ⟨D, hD, ?_⟩
  have : (D.length : ℝ) ≤ 80 * ((run.ancVerts G Y).card : ℝ) := by
    have h0 : (0 : ℝ) ≤ ((run.ancVerts G Y).card : ℝ) := Nat.cast_nonneg _
    linarith
  exact_mod_cast this

end EG.Todo
