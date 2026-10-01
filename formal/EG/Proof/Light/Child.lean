module

public import EG.Spec.Light.Child
public import EG.Spec.Vortex.PV
public import EG.Proof.Vortex.PV
public import EG.Proof.Light.Stages
public import EG.Proof.Lend.COLJVRows
public import EG.Proof.Stage1.COLc
public import EG.Lib.Light.Stages
public import EG.Lib.Gamma.Full

/-!
# Proof of Lemma child side (manuscript s5:lemChild), deterministic form

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.lemChild`
(`LemChildStatement`, the s5 unit's Spec): the child data satisfy the hypotheses of Lemma PV
(including (E1′)), and Lemma PV (the declared input `EG.pvLemma`, P4A's deterministic Spec) gives
for every admissible `H_0(Z)` the partition with (a)–(d).

Manuscript v6.1, `s5.tex`, proof of [s5:lemChild], "Hypotheses": `N ≥ P_l/2 ≥ N_0` (Γ3); `O = X_Z`
a spanning `(2^{-6},s_l/2)`-expander, `2vm ≤ s_l/2`, the Lemma-HB sets (the s5 unit's
`StagesHBStatement`, declared input `EG.stagesHB`); the own classes from COL(a) (`Z` not demoted)
and row 8 (d) (`s' ≥ 2^{145}L^{41}`, P4A's proved `EG.colJVRow8`); the partition `Rt ⊔ Pl`;
(E1′) from (E1) at `l = r(Z)`. "Conclusion": (a)–(d) from Lemma PV (a)–(d) ("If `x` lay in a
round-`l` phase-`c` zone … then `ext(x) = c`"; `4(J+1)N ≤ 14(J+1)N`). The good event and its
probability are not part of the deterministic Spec (T0-stage3-det). Design note
`formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.HB EG.Stage1 EG.Light

universe u

namespace ChildAux

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-- The own classes are graphs on `V(Y)` (for light `Y`). -/
theorem ownClass_verts {Y : PartId} (hL : run.isLight G Y.1 Y.2) (c : Colouring G run Y)
    (o : Fin (kown G run Y)) : (ownClass G run Y c o).verts = run.ancVerts G Y := by
  show (run.ancGraph G Y).verts = _
  rw [ancGraph_eq_X_of_isLight hL, X_verts_of_isLight hL]

/-- [s5:lemChild] "`N ≥ P_l/2 ≥ N_0`, by Proposition s2:propStructure(iv) and Γ3": the size
condition of Lemma PV for a light part (its round `l` has `λ_l ≥ log₂ D_*`). -/
theorem N0_le_card {N0 Dstar : ℝ} (h : RunHyp N0 Dstar G run) {Y : PartId}
    (hY : Y ∈ run.lightParts G) : N0 ≤ ((run.ancVerts G Y).card : ℝ) := by
  have hanc := COLcAux.mem_ancestors_of_mem_lightParts hY
  have hR := Standing.isRound_of_mem_ancestors hanc
  have hcard := Standing.card_ancVerts_ge hanc
  have h3 := h.gamma3
  unfold Gamma3 at h3
  have hD2 := h.gamma1core.two_lt
  have hlogD : 0 ≤ Real.logb 2 Dstar := Real.logb_nonneg (by norm_num) (by linarith)
  have hd := Run.Valid.dstar_le run G h.valid hR
  have hlam : Real.logb 2 Dstar ≤ run.lam G Y.1 :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hd
  have hpow : Real.logb 2 Dstar ^ 103 ≤ run.lam G Y.1 ^ 103 := pow_le_pow_left₀ hlogD hlam 103
  have hCp : ((Cp : ℕ) : ℕ) = 103 := rfl
  rw [hCp] at h3
  linarith

end ChildAux

open ChildAux

/-- [s5:lemChild] Lemma child side, deterministic form. -/
theorem lemChild : EG.Spec.LemChildStatement.{u} := by
  intro V _ G N0 Dstar run h ω _ Z hZ hdem
  have hHB := stagesHB V G N0 Dstar run h Z hZ
  have hΓ := h.gamma1
  have hV := h.valid
  have hLight := isLight_of_mem_lightParts hZ
  have hanc := COLcAux.mem_ancestors_of_mem_lightParts hZ
  have hR := Standing.isRound_of_mem_ancestors hanc
  have hE1 : E1 ω Z := by
    by_contra hc; exact hdem (Or.inl hc)
  have hCOLa : COLa G run Z (ω.cOutAt Z) := by
    by_contra hc; exact hdem (Or.inr hc)
  have hown := hCOLa.2.2.2 hLight
  have row8 := (colJVRow8 V G Dstar run hΓ hV Z hanc).2.2.2.1
  -- the hypotheses of Lemma PV
  have hPV : Vortex.PVHyp (childData ω Z) := by
    refine ⟨h.n0Cond.pv (N0_le_card h hZ), hHB.1, hHB.2.1, hHB.2.2.1, hHB.2.2.2, ?_, ?_, ?_, ?_,
      ?_, ?_, disjoint_Rt_Pl ω Z, Rt_union_Pl ω Z, ?_⟩
    · intro p
      exact ⟨ownClass_verts hLight _ _, hown _⟩
    · exact ownClass_verts hLight _ _
    · exact hown _
    · exact row8
    · intro p p' hpp
      refine disjoint_ownClass G run Z _ ?_
      intro he
      exact hpp (Option.some.inj ((ownIdx _).injective he))
    · intro p
      refine disjoint_ownClass G run Z _ ?_
      intro he
      exact Option.some_ne_none _ ((ownIdx _).injective he)
    · intro w hw
      exact E1_childData ω hE1 hR.2 (Pl_subset ω Z hw)
  refine ⟨hPV, fun H0 hH0 => ?_⟩
  -- `H_0` is admissible for Lemma PV
  have hadm : Vortex.PVAdm (childData ω Z) H0 := by
    refine ⟨fun e he => ?_, fun e he v hv => ?_, ?_, fun p => ?_⟩
    · exact (run.graph' G Z.1).loopless e (Run.E_subset_graph'_edges run G Z.1 Z.2 (hH0.2 he))
    · have := Run.E_subset_sym2 run G Z.1 Z.2 (hH0.2 he)
      exact Finset.mem_sym2_iff.1 this v hv
    · exact (ownClass_edges_subset_Own G run Z _ _).trans hH0.1
    · exact (ownClass_edges_subset_Own G run Z _ _).trans hH0.1
  obtain ⟨Hobj, Dobj, as, hsub, hdec, hlen, hpd, hends, hnum, hdeg, hdegZ, hRt, -⟩ :=
    pvLemma V (childData ω Z) hPV H0 hadm
  have hfm : (as.map Prod.fst).flatMap walkEdges = as.flatMap fun a => walkEdges a.1 := by
    rw [List.flatMap_map]
  have harc : arcEdges as = H0 \ Hobj := by
    ext e
    have h1 := hpd.2.2 e
    rw [hfm, List.mem_flatMap, Finset.mem_coe] at h1
    rw [mem_arcEdges, ← h1]
  refine ⟨Hobj, Dobj, as, ?_, ?_, hdec, hlen, ?_⟩
  · rw [harc]; exact Finset.disjoint_sdiff
  · rw [harc]; exact Finset.union_sdiff_of_subset hsub
  · refine ⟨by rw [← hfm]; exact hpd.2.1, fun a ha => ?_, ?_, fun x => ⟨hdeg x, ?_⟩, hRt⟩
    · have hp := hpd.1 a.1 (List.mem_map_of_mem ha)
      refine ⟨⟨fun hn => by simp [hn] at hp, hp.2, fun e he => ?_⟩, ?_, (hends a ha).1, ?_⟩
      · have : e ∈ (as.map Prod.fst).flatMap walkEdges :=
          List.mem_flatMap.2 ⟨a.1, List.mem_map_of_mem ha, he⟩
        exact (Finset.mem_sdiff.1 ((hpd.2.2 e).1 this)).1
      · unfold pathLength; omega
      · intro x hx Y σ
        exact not_mem_Zone_of_zonePhase_ne ω.zone ((hends a ha).2 x hx) Y σ
    · refine hnum.trans ?_
      show 4 * (Vortex.pvJ (run.ancVerts G Z).card + 1) * (run.ancVerts G Z).card ≤
        14 * (JY G run Z + 1) * (run.ancVerts G Z).card
      unfold JY
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    · exact (hdeg x).trans (hdegZ x)

end EG
