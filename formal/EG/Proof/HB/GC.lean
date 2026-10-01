module

public import EG.Spec.HB.GC
public import EG.Lib.HB.GC
public import EG.Proof.HB.TowerC

/-!
# Proof of Lemma "rule GC" (manuscript s2:lemGC)

Unit P3A (probe P-3, part 1). Design note `formal/work/p2b/P3A.md`. Round-level lemmas:
`EG.Lib.HB.GC`.

* `EG.gcDef : EG.Spec.GCDefStatement` ((i), second clause): definitional, `isLight` is
  `isL1 ∧ isL2 ∧ isGC`;
* `EG.gc : EG.Spec.GCStatement` ((ii), (iii)); (iii) does not need Lemma EL: an edge of
  `G_{r+1}` is an edge of `G'_r` that (R5) does not assign, and every edge of `G'_r` inside `Z^0`
  of a standalone pre-part is assigned;
* `EG.gcTheta : EG.Spec.GCThetaStatement` ((iv)), from the declared input `EG.towerC`
  ([s2:lemTower] (c)).
-/

public section

namespace EG

open EG.HB

/-- [s2:lemGC] (i) "(GC) only decides whether a pre-part satisfying (L1) and (L2) is light or
standalone." -/
theorem gcDef : EG.Spec.GCDefStatement := by
  intro V _ G Dstar run _ r _ a _
  refine ⟨fun h1 h2 => ⟨fun h => h.2.2, fun h => ⟨h1, h2, h⟩⟩, fun h hl => h ⟨hl.1, hl.2.1⟩⟩

/-- [s2:lemGC] (ii), (iii) "(ii) for every light part `Y` of round `r` and every guest
`x ∈ S_Y`, `e_{X^0_Y}(x, Y) < θ^GC_r(Y^0)`, where `Y` denotes the vertex set `Y^0 \ S_Y`;
(iii) GC-parts are standalone; for a GC-part `Y`, every edge of `G'_r` with both ends in `Y^0` is
assigned at round `r` (the edges of `X^0_Y`, those between a guest and `Y^0 \ S_Y` included, by
(R5)(1)), so no edge of `G_{r+1}` has both ends in `V(Y) = Y^0`; and every guest `x ∈ S_Y` lies in
`D_r ⊆ Dup*_r`." -/
theorem gc : EG.Spec.GCStatement := by
  intro V _ G Dstar run hv r hr
  have hR : run.IsRound r := Finset.mem_Icc.1 hr
  have hvr := Run.Valid.round run G hv hR
  refine ⟨fun a _ hl x hx => ?_, fun a ha hgc => ?_⟩
  · have := hl.2.2 x hx
    rw [FGraph.card_nbrs_inter_eq_eBetween] at this
    exact this
  · have ha' : a ∈ Round.prePartAddrs (run.graph G r) (run.choice r) := by
      rw [← run.prePartAddrs_of_isRound G hR]; exact ha
    have hnl : ¬ run.isLight G r a := fun h => hgc.2.2 h.2.2
    have hassign : ∀ e ∈ (run.graph' G r).edges, e ∈ (run.Z0 G r a).sym2 →
        run.assign G r e ≠ none := by
      intro e _ he
      simp only [Run.assign, if_pos hR]
      exact Round.assign_ne_none_of_not_isLight hvr ha' hnl he
    refine ⟨(run.mem_Std_iff G).2 ⟨ha, hnl⟩, Round.partVerts_of_not_isLight hnl, hassign,
      fun e he => ?_, fun e he hin => ?_, ?_, ?_⟩
    · simp only [Run.E, if_pos hR]
      exact (Round.mem_E _ _).2 ⟨(Round.X0_le_graph' _ _ a).2 he,
        Round.assign_eq_of_mem_X0 hvr ha' hnl he⟩
    · rw [run.graph_succ_of_isRound G hR, Round.next_edges] at he
      obtain ⟨he', hnone⟩ := (Round.mem_passed _ _).1 he
      refine hassign e he' hin ?_
      simp only [Run.assign, if_pos hR]
      exact hnone
    · simp only [Run.D, if_pos hR]
      exact Round.guests_subset_D a
    · simp only [Run.D, Run.DupStar, if_pos hR]
      exact Round.D_subset_DupStar

/-- [s2:lemGC] (iv) "`θ^GC_r(Z^0) > τ_r` for every round-`r` pre-part `Z`." This is
[s2:lemTower] (c) (declared input `EG.towerC`). -/
theorem gcTheta : EG.Spec.GCThetaStatement := by
  intro V _ G Dstar run hΓ hv r hr a ha
  have hR : run.IsRound r := Finset.mem_Icc.1 hr
  have hR1 : run.IsRound 1 := ⟨le_rfl, le_trans hR.1 hR.2⟩
  obtain ⟨-, -, -, h⟩ := towerC V G Dstar run hΓ hv (Run.Valid.dstar_le run G hv hR1) r hr
  obtain ⟨h1, h2⟩ := h a ha
  have : (run.tau G r : ℝ) < run.thetaGC G r a := lt_of_lt_of_le h2 h1
  exact_mod_cast this

end EG
