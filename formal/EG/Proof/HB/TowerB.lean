module

public import EG.Spec.HB.TowerB
public import EG.Lib.HB.TowerRun
public import EG.Proof.HB.CapPrePart

/-!
# Declared-input stub of unit P4A: Lemma "tower facts" (b), first sentence (manuscript
s2:lemTower (b))

One of the three `sorry`s of unit P4A (the others are `EG.cor22`, `EG/Proof/Ext/Cor22.lean`, and
`EG.colJVCount`, `EG/Proof/Lend/COLJVCount.lean`). Rows 4, 7, 8 of the COL-JV table use the
standing bounds (B1) and (B3) of the proof of [s3:lemCOLJV], which quote [s2:lemTower] (b); its
proof needs the (R2) parameter algebra and s2:propStructure, which are not nodes of probe P-4.
Justification: design note `formal/work/p2b/P4A.md`, "Declared inputs".
-/

public section

namespace EG

/-- Proved in P3. [s2:lemTower] (b) "For `r ≤ R`: `M_r ≤ d_r^2`; `λ_r ≤ Λ_r ≤ 2λ_r`;
`λ_r^{100} ≤ s_r ≤ 2Λ_r^σ`; `s_r ≤ P_r`; and `L_Y ≤ log M_r ≤ 2λ_r` for every ancestor `Y` of round
`r`." Owner: s2 tower unit (blueprint s2b). -/
theorem towerBRound : EG.Spec.TowerBRoundStatement := by
  intro V _ G Dstar run hD hv _ r hr
  have h := EG.HB.Run.paramHyp hD hv hr
  have hLam2 : run.Lam G r ≤ 2 * run.lam G r := h.Lam_le_two_lam
  refine ⟨h.M_le_sq, h.lam_le_Lam, hLam2, h.lam100_le_s, h.s_le_two, h.s_le_P, ?_⟩
  intro Y hY hYr
  refine ⟨?_, hLam2⟩
  obtain ⟨r', a⟩ := Y
  simp only at hYr
  subst hYr
  have hYp : a ∈ run.prePartAddrs G r' := (EG.HB.Run.mem_ancestors run G).1 hY
  have hcap := ((EG.capPrePart V G Dstar run hD.gamma2a hv r' hr).2 a hYp).1
  have hsub : (run.ancVerts G (r', a)).card ≤ (run.Z0 G r' a).card :=
    Finset.card_le_card (EG.HB.Run.partVerts_subset_Z0 run G r' a)
  have hM : ((run.ancVerts G (r', a)).card : ℝ) ≤ (run.M G r' : ℝ) := by
    exact_mod_cast hsub.trans hcap
  unfold EG.HB.Run.LY
  rcases Nat.eq_zero_or_pos (run.ancVerts G (r', a)).card with h0 | h0
  · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero]; exact h.Lam_pos.le
  · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h0) hM

end EG
