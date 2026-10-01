module

public import EG.Spec.Chain.MixC
public import EG.Lib.Chain.MixCTPV
public import EG.Proof.Todo.COL
public import EG.Proof.Todo.StructureExp

/-!
# P3 stub: `EG.Spec.MixCTPVApplicableStatement` (s6:thmMIXC)

Generated at the P2→P3 transition (2026-09-30), proved in P3 (round 1 of P3-s6), following the
bullet "Lemma TPV at step (1)" of the proof of s6:thmMIXC (a):
* "`|Z^0| ≥ P_l ≥ N_0` by (s1:condG3)": `EG.Chain.n0_le_card_Z0`, then `N0Cond` gives `TPVSize`;
* lend-good `Z`: `O_Z = Own_Z` is a `(2^{-5}, s_l/4)`-expander on `Z^0` by Lemma s3:lemCOL(a)
  (lend-good includes the events of COL(a), `EG.Chain.lendBad`);
* lend-bad `Z`: `O_Z = X^0_Z` is a spanning `(2^{-5}, s_l)`-expander on `Z^0` by
  Proposition s2:propStructure(i) (`EG.Todo.StructureExp`);
* `s_l ≥ s_l/4 ≥ 2^{150} L_Z^{42}` by Lemma s3:lemCOL(e) (`EG.Todo.COL`);
* `Ret_Z ⊆ Z^0` (s6:defLending, `EG.Chain.ret_union_qs`).
Keep the name `EG.Todo.MixCTPVApplicable`; consumers import this module.
-/

public section

namespace EG.Todo

open EG.HB EG.Chain EG.Quot

/-- [s6:thmMIXC] see `EG.Spec.MixCTPVApplicableStatement`. Proved in P3. -/
theorem MixCTPVApplicable : EG.Spec.MixCTPVApplicableStatement := by
  intro V _ G N0 Dstar run δ hrun _hδ ω _hω l a ha
  obtain ⟨hpre, hnl⟩ := (Run.mem_Std_iff run G).1 ha
  have hR := Run.isRound_of_mem_prePartAddrs hpre
  have hl : l ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  have hY : ((l, a) : PartId) ∈ run.ancestors G := (Run.mem_ancestors run G).2 hpre
  have hcol := EG.Todo.COL.{_, 0} V G Dstar run hrun.gamma1 hrun.valid (l, a) hY
  have hs : (2 : ℝ) ^ 150 * Vortex.L (run.Z0 G l a).card ^ 42 ≤ (run.s G l : ℝ) / 4 := by
    have h := (hcol.2.1.1 hnl).1
    rw [ancS_std run G hnl] at h
    have hL : run.LY G (l, a) = Vortex.L (run.Z0 G l a).card := by
      unfold Run.LY Vortex.L
      rw [ancVerts_std run G hnl]
    rwa [hL] at h
  have hsize : Vortex.TPVSize (run.Z0 G l a).card :=
    (hrun.n0Cond.2 _ (n0_le_card_Z0 hrun hpre)).1
  have hret : ret run G δ (stageOf ω) l a ⊆ run.Z0 G l a := by
    rw [← ret_union_qs run G δ (stageOf ω) l a]
    exact Finset.subset_union_left
  have he1 : (2 : ℝ) ^ (-7 : ℤ) ≤ (2 : ℝ) ^ (-5 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  have hs0 : (0 : ℝ) ≤ (run.s G l : ℝ) := Nat.cast_nonneg _
  constructor
  · intro hgood
    rw [OZ_of_not_lendBad run G (stageOf ω) hgood]
    have hA : Stage1.COLa G run (l, a) (ω.cOutAt (l, a)) := by
      by_contra hc
      exact hgood (Or.inr (Or.inl hc))
    refine ⟨hsize, rfl, ?_, he1, le_rfl, hs, hret⟩
    change (FGraph.ofEdges (run.Z0 G l a)
      (Stage1.Own G run (l, a) (ω.colAt (l, a))).edges).IsExpander _ _
    rw [ofEdges_own_std run G hnl]
    have h := hA.1
    rwa [ancEps_std run G hnl, ancS_std run G hnl] at h
  · intro hbad
    rw [OZ_of_lendBad run G (stageOf ω) hbad]
    obtain ⟨hv, hexp⟩ := (EG.Todo.StructureExp V G Dstar run hrun.gamma2a hrun.valid).1 l hl a hpre
    exact ⟨hsize, hv, hexp, he1, le_rfl, by linarith, hret⟩

end EG.Todo
