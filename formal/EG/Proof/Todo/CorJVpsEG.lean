module

public import EG.Spec.Main.CorJVpsEG
public import EG.Proof.Todo.JVps
public import EG.Proof.Todo.ExistsRun
public import EG.Proof.Quot.HI
public import EG.Lib.Chain.Design
public import EG.Lib.HB.Run
public import EG.Lib.Found.Gamma
public import EG.Lib.Found.FGraphFnum
public import EG.Lib.Quot.ConstNonneg

/-!
# P3 stub: `EG.Spec.CorJVpsEGStatement` (s7:thmMainProof)

Generated at the P2→P3 transition (2026-09-30). Prove it in place: replace `by sorry` with the proof
(helper lemmas go in `EG/Lib/**`). Keep the name `EG.Todo.CorJVpsEG`; consumers import this module.

Proof (manuscript s7:thmMainProof): Theorem HI″ (`EG.hi`) with `C := C_0`, `ϑ := θ_Q`; its
hypothesis from Proposition s2:propExists (`EG.Todo.ExistsRun`), a designation
(`EG.Chain.exists_isDesignation`, s6:defDesign) and Theorem JV⁺* (`EG.Todo.JVps`). The statement
ranges over vertex types of every universe; Theorem HI″ is stated on `Type`, and the conclusion is
transported through `f(G) ≤ f(|V(G)|)` (`EG.FGraph.fnum_edges_le_fmax`, `EG.exists_fnum_eq_fmax`).
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- Proved in P3. [s7:thmMainProof] see `EG.Spec.CorJVpsEGStatement`. -/
theorem CorJVpsEG : EG.Spec.CorJVpsEGStatement := by
  intro N0 Dstar hN0 hΓ V G
  have hD4 : (4 : ℝ) ≤ Dstar := le_trans (by norm_num) hΓ.2.1
  -- "Its assumptions on the constants hold: `C_0 ≥ D_*/2`, since `ε_1 ≥ 0`; and
  -- `0 ≤ θ_Q ≤ 1/4 < 1/2`."
  have hC : Dstar / 2 ≤ C0 Dstar := half_le_C0 hD4
  have hθ0 : 0 ≤ thetaQ Dstar := thetaQ_nonneg hD4
  have hθ : thetaQ Dstar < 1 / 2 := by
    have := hΓ.2.2.2.2
    unfold thetaQ
    linarith
  -- "Let `G` be a graph without isolated vertices, with `n ≥ N_0` vertices and `d_1 ≥ D_*`. By
  -- Proposition s2:propExists, `G` has a valid run. A designation exists … Theorem s7:thmJVps
  -- gives simple graphs `Q_3, …, Q_R` … This is the hypothesis of Theorem s7:thmHI"
  have hyp : Spec.HIHyp Dstar N0 (C0 Dstar) (thetaQ Dstar) := by
    apply hiHyp_of_fintype_index
    intro V G _ hN hd
    classical
    obtain ⟨run, hrun⟩ := Todo.ExistsRun V G Dstar hΓ.1.1
    obtain ⟨δ, hδ⟩ := Chain.exists_isDesignation run G
    have hd1 : Dstar ≤ run.d G 1 := by
      simpa [Run.d, Round.d] using hd
    obtain ⟨W, Q, -, h1, h2⟩ := Todo.JVps V G N0 Dstar run δ hN0 hΓ hN hd1 hrun hδ
    refine ⟨Finset.Icc 3 run.R, inferInstance, fun l => W l.1, fun l => Q l.1, ?_, ?_⟩
    · rw [Finset.sum_coe_sort (Finset.Icc 3 run.R) (fun l => (fnum (Q l).edges : ℝ))]
      exact h1
    · rw [Finset.sum_coe_sort (Finset.Icc 3 run.R) (fun l => ((Q l).card : ℝ))]
      exact h2
  -- transport to a graph on `Fin |V(G)|` realising `f(|V(G)|)`
  classical
  obtain ⟨H, hH⟩ := exists_fnum_eq_fmax G.card
  have h1 : (fnum G.edges : ℝ) ≤ (fmax G.card : ℝ) := by exact_mod_cast G.fnum_edges_le_fmax
  have h2 := hi Dstar N0 _ _ hC hθ0 hθ hyp (Fin G.card) (FGraph.ofSimpleGraph H)
  rw [FGraph.ofSimpleGraph_edges, hH] at h2
  have h3 : (FGraph.ofSimpleGraph H).card = G.card := by
    rw [FGraph.ofSimpleGraph_card, Fintype.card_fin]
  rw [h3] at h2
  exact h1.trans h2

end EG.Todo
