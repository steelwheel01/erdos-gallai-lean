module

public import EG.Spec.Stage1.COL
public import EG.Lib.Stage1.COLb
public import EG.Proof.Link.T16s
public import EG.Proof.HB.TowerB
public import EG.Proof.HB.TowerBM
public import EG.Proof.Todo.TowerBRest
public import EG.Proof.Todo.COLJVRow5
public import EG.Proof.Todo.COLJVRow6
public import EG.Proof.Stage1.COLa
public import EG.Proof.Stage1.COLc
public import EG.Proof.Lend.COLJVRows

/-!
# P3 stub: `EG.Spec.COLStatement` (s3:lemCOL)

Generated at the P2→P3 transition (2026-09-30). Proved in P3. Keep the name `EG.Todo.COL`; consumers import this module.
-/

public section

namespace EG.Todo

/-- Proved in P3. [s3:lemCOL] see `EG.Spec.COLStatement`. -/
theorem COL : EG.Spec.COLStatement := by
  intro V _ G Dstar run hΓ hV Y hY
  classical
  have hR := Standing.isRound_of_mem_ancestors hY
  have hD1 := HB.Run.Valid.dstar_le run G hV (l := 1) ⟨le_rfl, le_trans hR.1 hR.2⟩
  set N : ℝ := ((run.ancVerts G Y).card : ℝ) with hNdef
  -- (e): the own-device thresholds (row 8)
  have he : Stage1.COLe G run Y := by
    obtain ⟨r1, r2, r3, r4, r5⟩ := colJVRow8 V G Dstar run hΓ hV Y hY
    refine ⟨fun hl => ?_, fun _ => ⟨r3, r4, r5⟩⟩
    rw [HB.Run.ancS, if_neg hl]
    exact ⟨r1, r2⟩
  -- `P((a) ∧ ¬(b)) ≤ N^{-2}/4` under any `μ` with law `colLaw`
  have hb : ∀ (Ω : Type _) (μ : FinDist Ω) (D : Ω → Stage1.COLOut G run Y),
      μ.map D = Stage1.colLaw G run Y →
      μ.prob {ω | Stage1.COLa G run Y (D ω) ∧ ¬ Stage1.COLb G run Y (D ω)} ≤ N ^ (-2 : ℤ) / 4 := by
    intro Ω μ D hD
    have e : {ω | Stage1.COLa G run Y (D ω) ∧ ¬ Stage1.COLb G run Y (D ω)} =
        D ⁻¹' {ω | Stage1.COLa G run Y ω ∧ ¬ Stage1.COLb G run Y ω} := rfl
    rw [e, ← FinDist.prob_map, hD]
    exact COLbProof.prob_notb_le EG.t16s towerBRound towerBM EG.Todo.TowerBRest
      EG.Todo.COLJVRow5 EG.Todo.COLJVRow6 hΓ hV Y hY
  refine ⟨fun h => ?_, he, fun ω hω => Stage1.COLg_of_mem_supp_colLaw G run Y hω, ?_, ?_⟩
  · by_contra hk
    have := (Stage1.klend_pos_iff (G := G) (run := run)).1 (Nat.pos_of_ne_zero hk)
    omega
  · intro Ω μ D hD
    have ha := colaProb V G Dstar run hΓ hV hD1 Y hY Ω μ D hD
    have hbb := hb Ω μ D hD
    have hsub : {ω | Stage1.COLa G run Y (D ω) ∧ Stage1.COLb G run Y (D ω) ∧ Stage1.COLe G run Y}ᶜ ⊆
        {ω | ¬ Stage1.COLa G run Y (D ω)} ∪
          {ω | Stage1.COLa G run Y (D ω) ∧ ¬ Stage1.COLb G run Y (D ω)} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and] at hω
      by_cases h1 : Stage1.COLa G run Y (D ω)
      · exact Or.inr ⟨h1, fun h2 => hω h1 h2 he⟩
      · exact Or.inl h1
    have h1 := (FinDist.prob_mono μ hsub).trans (FinDist.prob_union_le μ _ _)
    rw [FinDist.prob_compl] at h1
    linarith
  · intro hYl Ω μ D Vs ρ hD hVs hind
    have ha := colaProb V G Dstar run hΓ hV hD1 Y hY Ω μ D hD
    have hbb := hb Ω μ D hD
    have hc := colc V G Dstar run hΓ hV hD1 Y hYl Ω μ D Vs ρ hD hVs hind
    have hsub : {ω | Stage1.COLa G run Y (D ω) ∧ Stage1.COLb G run Y (D ω) ∧
        Stage1.COLc G run Y (D ω) (Vs ω) ∧ Stage1.COLe G run Y}ᶜ ⊆
        ({ω | ¬ Stage1.COLa G run Y (D ω)} ∪
          {ω | Stage1.COLa G run Y (D ω) ∧ ¬ Stage1.COLb G run Y (D ω)}) ∪
          {ω | ¬ Stage1.COLc G run Y (D ω) (Vs ω)} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and] at hω
      by_cases h1 : Stage1.COLa G run Y (D ω)
      · by_cases h2 : Stage1.COLb G run Y (D ω)
        · exact Or.inr (fun h3 => hω h1 h2 h3 he)
        · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inl (Or.inl h1)
    have h1 := (FinDist.prob_mono μ hsub).trans ((FinDist.prob_union_le μ _ _).trans
      (add_le_add (FinDist.prob_union_le μ _ _) le_rfl))
    rw [FinDist.prob_compl] at h1
    linarith

end EG.Todo
