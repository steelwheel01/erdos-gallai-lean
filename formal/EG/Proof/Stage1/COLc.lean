module

public import EG.Spec.Stage1.COLc
public import EG.Proof.Link.T16s
public import EG.Proof.Stage1.COLa
public import EG.Proof.Lend.COLJVRows
public import EG.Lib.Light.Stages
public import EG.Lib.Prob.Indep

/-!
# Proof of Lemma COL (c) (manuscript s3:lemCOL (c)): T16* per U-index, joint independence

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.colcIndex`
(`COLcIndexStatement`) and `EG.colc` (`COLcStatement`, refutation target: the multiplicity `t_Y`).

Manuscript v6.1, `s3.tex`, proof of (c): "Condition as in (b). The sets `V_{l,c,σ}` are independent
of the colouring. For a fixed index, apply Theorem s3:thmT16s to the fixed class `LU_{Y,l,c,σ}`, an
`N`-vertex `(2^{-6},s_r/(16k))`-expander, with `t := t_Y` … and `ρ := ρ_{l,c,σ} ≥ 1/(12L^5)`. Its
hypotheses hold: `s_r/(16k) ≥ 2^{135}tL^{28}ρ^{-5}` by row 4 …; `ρN ≥ N/(12L^5) ≥
λ^{103}/(24(2λ)^5) ≥ L^2`. Each index fails with probability at most `2^{86}tL^{19}(12L^5)^3N^{-3}`.
The theorem is applied to one index at a time, so dependence across indices is irrelevant. By row 7,
the union over `I^U(Y)` is at most `N^{-2}/4`. Together with the failure probability of (a), (c)
fails with probability at most `N^{-2}/2`."

Formal route: the conditioning on the lending data is `FinDist.IsRSubset.map_pair_eq_prod` (the joint
law of `D` and an independent `ρ`-random set is a product) and `FinDist.prob_compProd_le_of_forall`
(bound every section); Theorem 16* is applied to the fixed class and the law `rsubset V(Y) ρ`
itself. Declared inputs: `EG.t16s` ([s3:thmT16s]), `EG.colaProb` ([s3:lemCOL] (a), failure
bound). Rows 4 and 7 are P4A's proved `EG.colJVRow4`, `EG.colJVRow7` (from the declared inputs
`EG.towerBRound`, `EG.colJVCount`). Design note `formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.HB

namespace COLcAux

/-- Conditioning on a random variable `D` independent of a `ρ`-random set `W`: if for every value
`d` of positive probability the `ρ`-random set satisfies `Q d` with probability at most `q`, then
`P(Q (D, W)) ≤ q`. -/
theorem prob_le_of_indep_rsubset {Ω γ α : Type*} (μ : FinDist Ω) (D : Ω → γ) (W : Ω → Finset α)
    (S : Finset α) (ρ : ℝ) (hW : μ.IsRSubset W S ρ) (hi : μ.IndepFun D W)
    (Q : γ → Finset α → Prop) (q : ℝ)
    (h : ∀ d, 0 < (μ.map D).w d →
      (FinDist.rsubset S ρ hW.nonneg hW.le_one).prob {T | Q d T} ≤ q) :
    μ.prob {ω | Q (D ω) (W ω)} ≤ q := by
  have e : {ω | Q (D ω) (W ω)} = (fun ω => (D ω, W ω)) ⁻¹' {p | Q p.1 p.2} := rfl
  rw [e, ← FinDist.prob_map, hW.map_pair_eq_prod hi]
  exact FinDist.prob_compProd_le_of_forall _ _ h

/-- `ρ^{-n} ≤ (12L^5)^n` for `ρ ≥ 1/(12L^5)`, `L > 0`. -/
theorem zpow_neg_le_of_ge_inv {L ρ : ℝ} (hL : 0 < L) (hρ : 1 / (12 * L ^ 5) ≤ ρ) (n : ℕ) :
    ρ ^ (-(n : ℤ)) ≤ (12 * L ^ 5) ^ n := by
  have hA : 0 < 12 * L ^ 5 := by positivity
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  have hinv : ρ⁻¹ ≤ 12 * L ^ 5 := by
    rw [one_div] at hρ
    calc ρ⁻¹ ≤ (12 * L ^ 5)⁻¹⁻¹ := inv_anti₀ (by positivity) hρ
      _ = 12 * L ^ 5 := inv_inv _
  rw [zpow_neg, ← inv_zpow, zpow_natCast]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hρ0.le) hinv n

variable {V : Type*} [DecidableEq V] {G : FGraph V} {Dstar : ℝ} {run : Run V}

/-- A light part is an ancestor. -/
theorem mem_ancestors_of_mem_lightParts {Y : PartId} (h : Y ∈ run.lightParts G) :
    Y ∈ run.ancestors G := by
  classical
  unfold Run.lightParts at h
  exact (Finset.mem_filter.1 h).1

/-- The standing bounds at a light part `Y` of round `r ≤ R − 2`: `λ ≥ 2^{256}`, `0 < L_Y ≤ 2λ`,
`N ≥ λ^{103}/2`, and "`ρN ≥ N/(12L^5) ≥ λ^{103}/(24(2λ)^5) ≥ L^2`" for `ρ ≥ 1/(12L^5)`. -/
theorem setup (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {Y : PartId}
    (hY : Y ∈ run.ancestors G) :
    0 < run.LY G Y ∧ ∀ ρ : ℝ, 1 / (12 * run.LY G Y ^ 5) ≤ ρ →
      run.LY G Y ^ 2 ≤ ρ * ((run.ancVerts G Y).card : ℝ) := by
  obtain ⟨hlam, hL0, hL2, -, -, -⟩ := colJV_rows_setup hΓ hV hY
  have hN := Standing.card_ancVerts_ge hY
  set lam := run.lam G Y.1
  set N : ℝ := ((run.ancVerts G Y).card : ℝ)
  set L := run.LY G Y
  have hlam1 : (1 : ℝ) ≤ lam := le_trans (by norm_num) hlam
  have hlam2 : (2 : ℝ) ≤ lam := le_trans (by norm_num) hlam
  -- `λ^{96} ≥ 2^{96}`
  have h96 : (2 : ℝ) ^ 96 ≤ lam ^ 96 := pow_le_pow_left₀ (by norm_num) hlam2 96
  have hN2 : (2 : ℝ) ≤ N := by
    have : (2 : ℝ) ≤ lam ^ 103 / 2 := by
      have h103 : (2 : ℝ) ^ 103 ≤ lam ^ 103 := pow_le_pow_left₀ (by norm_num) hlam2 103
      have : (4 : ℝ) ≤ 2 ^ 103 := by norm_num
      linarith
    linarith
  have hLpos : 0 < L := by
    have : (1 : ℝ) ≤ L := by
      show (1 : ℝ) ≤ Real.logb 2 _
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
      exact hN2
    linarith
  refine ⟨hLpos, fun ρ hρ => ?_⟩
  have hL5 : 0 < 12 * L ^ 5 := by positivity
  have hN0 : 0 ≤ N := by linarith
  have h1 : N / (12 * L ^ 5) ≤ ρ * N := by
    rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right hρ hN0
  refine le_trans ?_ h1
  rw [le_div_iff₀ hL5]
  -- `12 L^7 ≤ 12 (2λ)^7 ≤ λ^{103}/2 ≤ N`
  have hL7 : L ^ 7 ≤ (2 * lam) ^ 7 := pow_le_pow_left₀ hL0 hL2 7
  have hlam7 : 0 ≤ lam ^ 7 := by positivity
  have hkey : 12 * (2 * lam) ^ 7 ≤ lam ^ 103 / 2 := by
    have e1 : (2 * lam) ^ 7 = 128 * lam ^ 7 := by ring
    have e2 : lam ^ 103 = lam ^ 7 * lam ^ 96 := by ring
    rw [e1, e2]
    have : (3072 : ℝ) ≤ lam ^ 96 := le_trans (by norm_num) h96
    nlinarith
  calc L ^ 2 * (12 * L ^ 5) = 12 * L ^ 7 := by ring
    _ ≤ 12 * (2 * lam) ^ 7 := by linarith
    _ ≤ lam ^ 103 / 2 := hkey
    _ ≤ N := hN

end COLcAux

open COLcAux

universe u v

/-- [s3:lemCOL] (c), proof, the per-index step: "Condition on a stage-(i)/(ii) outcome in which (a)
holds. … For a fixed index, apply Theorem s3:thmT16s to the fixed class `LU_{Y,l,c,σ}` … Each
index fails with probability at most `2^{86}tL^{19}(12L^5)^3N^{-3}`." -/
theorem colcIndex : EG.Spec.COLcIndexStatement.{u, v} := by
  intro V _ G Dstar run hΓ hV hd1 Y hY i hi Ω μ D W ρ hD hW hρ hind
  have hLight := Light.isLight_of_mem_lightParts hY
  have hanc : Y ∈ run.ancestors G := mem_ancestors_of_mem_lightParts hY
  obtain ⟨-, l, c, σ, rfl, hl, hσ⟩ := Stage1.mem_IU.1 hi
  have hR : Y.1 + 2 ≤ run.R := by have := (Stage1.mem_lateRounds run).1 hl; omega
  obtain ⟨hLpos, hρN⟩ := setup hΓ hV hanc
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ
  have hρ1 : ρ ≤ 1 := hW.le_one
  have row4 := colJVRow4 V G Dstar run hΓ hV Y hanc hR
  have hverts : (run.ancGraph G Y).verts = run.ancVerts G Y := by
    rw [Light.ancGraph_eq_X_of_isLight hLight, Light.X_verts_of_isLight hLight]
  have hε : run.ancEps G Y = 2 ^ (-6 : ℤ) := by
    rw [Run.ancEps_of_isLight run G hLight, epsC]; norm_num
  -- `1 ≤ t_Y`
  have ht1 : (1 : ℝ) ≤ (Stage1.tY G run Y : ℝ) := by
    have hpos := (Standing.lam_facts hΓ hV (Standing.isRound_of_mem_ancestors hanc)).2.1
    have : 1 ≤ Stage1.tY G run Y := by
      unfold Stage1.tY
      exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hpos _)).ne'
    exact_mod_cast this
  set bound := (2 : ℝ) ^ 86 * (Stage1.tY G run Y : ℝ) * run.LY G Y ^ 19 *
    (12 * run.LY G Y ^ 5) ^ 3 * ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) with hbound
  have hb0 : 0 ≤ bound := by positivity
  refine prob_le_of_indep_rsubset μ D W (run.ancVerts G Y) ρ hW hind
    (fun d T => Stage1.COLa G run Y d ∧ ¬ (Stage1.lentClass G run Y d.1
      (Stage1.LentTag.U l c σ)).IsPathConnected ((2 : ℝ) ^ 12 * run.LY G Y ^ 4)
        (Stage1.tY G run Y) T) bound ?_
  intro d _
  by_cases ha : Stage1.COLa G run Y d
  · set X := Stage1.lentClass G run Y d.1 (Stage1.LentTag.U l c σ) with hX
    have hXv : X.verts = run.ancVerts G Y := hverts
    have hXc : (X.card : ℝ) = ((run.ancVerts G Y).card : ℝ) := by
      rw [FGraph.card, hXv]
    have hexp : X.IsExpander (run.ancEps G Y)
        (run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ))) :=
      ha.2.2.1 _ (Stage1.mem_lentIdx.2 (Or.inl hi))
    set rs := FinDist.rsubset (run.ancVerts G Y) ρ hW.nonneg hW.le_one
    have hrs : rs.IsRSubset (fun T => T) X.verts ρ := by
      rw [hXv]; exact FinDist.isRSubset_rsubset _ _
    have h3 : ρ ^ (-3 : ℤ) ≤ (12 * run.LY G Y ^ 5) ^ 3 := by
      simpa using zpow_neg_le_of_ge_inv hLpos hρ 3
    have h5 : ρ ^ (-5 : ℤ) ≤ (12 * run.LY G Y ^ 5) ^ 5 := by
      simpa using zpow_neg_le_of_ge_inv hLpos hρ 5
    have hLX : Real.logb 2 (X.card : ℝ) = run.LY G Y := by rw [hXc]; rfl
    have hT := t16s V X (run.ancEps G Y) (run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ))) ρ
      (Stage1.tY G run Y : ℝ) (Finset V) rs (fun T => T) (by rw [hε]; norm_num)
      (by rw [hε]; norm_num) hexp hρ0 hρ1 ht1 hrs
      (by rw [hLX, hXc]; exact hρN ρ hρ)
      (by
        rw [hLX]
        refine le_trans ?_ row4
        gcongr)
    rw [hLX, hXc] at hT
    have hsub : {T : Finset V | Stage1.COLa G run Y d ∧ ¬ X.IsPathConnected
        ((2 : ℝ) ^ 12 * run.LY G Y ^ 4) (Stage1.tY G run Y) T} ⊆
        {T | X.IsPathConnected ((2 : ℝ) ^ 12 * run.LY G Y ^ 4) (Stage1.tY G run Y) T}ᶜ :=
      fun T hT' => hT'.2
    refine (FinDist.prob_mono _ hsub).trans ?_
    rw [FinDist.prob_compl]
    refine le_trans (by linarith) (?_ : (2 : ℝ) ^ 86 * (Stage1.tY G run Y : ℝ) *
      run.LY G Y ^ 19 * ρ ^ (-3 : ℤ) * ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) ≤ bound)
    rw [hbound]
    gcongr
  · refine le_trans (le_of_eq ?_) hb0
    rw [FinDist.prob_eq_zero_iff]
    intro T hT
    exact absurd hT.1 ha

/-- [s3:lemCOL] (c): "with probability at least `1 − |V(Y)|^{-2}/2` over the lending data and the
sets, every U-lent class `LU_{Y,l,c,σ}` is `(2^{12}L_Y^4, t_Y)`-path connected through
`V_{l,c,σ}`". Proof: "The theorem is applied to one index at a time, so dependence across indices
is irrelevant. By row 7, the union over `I^U(Y)` is at most `N^{-2}/4`. Together with the failure
probability of (a), (c) fails with probability at most `N^{-2}/2`." -/
theorem colc : EG.Spec.COLcStatement.{u, v} := by
  intro V _ G Dstar run hΓ hV hd1 Y hY Ω μ D Vs ρ hD hVs hind
  have hanc : Y ∈ run.ancestors G := mem_ancestors_of_mem_lightParts hY
  set N : ℝ := ((run.ancVerts G Y).card : ℝ)
  have hN0 : 0 ≤ N ^ (-2 : ℤ) / 2 := by positivity
  by_cases hR : Y.1 + 2 ≤ run.R
  · -- the failure event lies in "(a) fails" or "(a) holds and index `i` fails"
    have hsub : {ω | ¬ Stage1.COLc G run Y (D ω) (Vs ω)} ⊆
        {ω | ¬ Stage1.COLa G run Y (D ω)} ∪ ⋃ i ∈ Stage1.IU G run Y,
          {ω | Stage1.COLa G run Y (D ω) ∧ ¬ (Stage1.lentClass G run Y (D ω).1 i).IsPathConnected
            ((2 : ℝ) ^ 12 * run.LY G Y ^ 4) (Stage1.tY G run Y) (Vs ω i)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Stage1.COLc, not_forall] at hω
      obtain ⟨i, hi, hni⟩ := hω
      by_cases ha : Stage1.COLa G run Y (D ω)
      · exact Or.inr (Set.mem_biUnion hi ⟨ha, hni⟩)
      · exact Or.inl ha
    refine (FinDist.prob_mono _ hsub).trans ((FinDist.prob_union_le _ _ _).trans ?_)
    have ha := colaProb V G Dstar run hΓ hV hd1 Y hanc Ω μ D hD
    have hU := (FinDist.prob_biUnion_le μ _ _).trans (Finset.sum_le_sum fun i hi =>
      colcIndex V G Dstar run hΓ hV hd1 Y hY i hi Ω μ D (fun ω => Vs ω i) (ρ i) hD (hVs i hi).1
        (hVs i hi).2 (hind.comp id fun f => f i))
    have h7 := colJVRow7 V G Dstar run hΓ hV Y hanc hR
    have : N ^ (-2 : ℤ) / 2 = N ^ (-2 : ℤ) / 4 + N ^ (-2 : ℤ) / 4 := by ring
    rw [this]
    exact add_le_add ha (hU.trans h7)
  · -- `r ≥ R − 1`: `I^U(Y) = ∅`, the event (c) always holds
    refine le_trans (le_of_eq ?_) hN0
    rw [FinDist.prob_eq_zero_iff]
    intro ω hω
    exfalso
    simp only [Set.mem_setOf_eq, Stage1.COLc, not_forall] at hω
    obtain ⟨i, hi, -⟩ := hω
    obtain ⟨-, l, c, σ, -, hl, -⟩ := Stage1.mem_IU.1 hi
    have := (Stage1.mem_lateRounds run).1 hl
    omega

end EG
