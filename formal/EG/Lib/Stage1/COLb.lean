module

public import EG.Spec.Stage1.COL
public import EG.Spec.Link.T16s
public import EG.Lib.Stage1.COL
public import EG.Lib.Prob.Indep
public import EG.Lib.HB.Run
public import EG.Lib.HB.Params
public import EG.Lib.Lend.Standing
public import EG.Spec.HB.TowerB
public import EG.Spec.HB.TowerBM
public import EG.Spec.HB.Tower
public import EG.Spec.Lend.COLJV

/-!
# Lemma COL (b) (manuscript s3:lemCOL (b)): T16* per JS class — P3-s3

Manuscript v6.1, `s3.tex`, proof of Lemma [s3:lemCOL] (b): "Condition on the colouring with (a).
For `r+2 ≤ l ≤ R` and `0 ≤ j < K^JS_l`, the set `T_j(Y,l)` is a `ρ_l`-random subset of `V(Y)`,
independent of the colouring. Apply Theorem s3:thmT16s to the fixed class `LJS_{Y,l,j}` … with
`t := t^JS_l` and `ρ := ρ_l`. … By row 6 the failures sum to at most `|V(Y)|^{-2}/4`."

Theorem 16* enters as the hypothesis `hT16 : Spec.T16sStatement`; the independence of the labels
from the colouring is the product structure of `colLaw` (`FinDist.prob_compProd_le_of_forall`),
and `T_j(Y,l)` is `ρ_l`-random by `Stage1.isRSubset_Tj`.
-/

public section

namespace EG.COLbProof

open EG.HB

universe u

variable {V : Type u} [DecidableEq V] {G : FGraph V} {run : Run V}

/-- The event that (a) holds and the JS class `LJS_{Y,l,j}` is not
`(2^{12}L_Y^4, t^JS_l)`-path connected through `T_j(Y,l)`. -/
def BadJS (G : FGraph V) (run : Run V) (Y : PartId) (l j : ℕ) : Set (Stage1.COLOut G run Y) :=
  {ω | Stage1.COLa G run Y ω ∧ ¬ (Stage1.LJS G run Y ω.1 l j).IsPathConnected
      ((2 : ℝ) ^ 12 * run.LY G Y ^ 4) (Stage1.tJS G run l) (Stage1.Tj G run Y ω.2 l j)}

/-- Per JS index: the failure probability of Theorem 16* for the class `LJS_{Y,l,j}`. -/
theorem prob_badJS_le (hT16 : Spec.T16sStatement.{u, u}) (Y : PartId) (l j : ℕ)
    (hl : l ∈ Stage1.lateRounds run Y.1) (hj : j < Stage1.KJS G run l)
    (hε1 : (2 : ℝ) ^ (-7 : ℤ) ≤ run.ancEps G Y) (hε2 : run.ancEps G Y ≤ 1)
    (hρ0 : 0 < Stage1.rhoJS G run l) (ht1 : (1 : ℝ) ≤ Stage1.tJS G run l)
    (hρN : run.LY G Y ^ 2 ≤ Stage1.rhoJS G run l * ((run.ancVerts G Y).card : ℝ))
    (hs : (2 : ℝ) ^ 135 * (Stage1.tJS G run l : ℝ) * run.LY G Y ^ 28 *
        Stage1.rhoJS G run l ^ (-5 : ℤ) ≤ run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ))) :
    (Stage1.colLaw G run Y).prob (BadJS G run Y l j) ≤
      (2 : ℝ) ^ 86 * (Stage1.tJS G run l : ℝ) * run.LY G Y ^ 19 *
        Stage1.rhoJS G run l ^ (-3 : ℤ) * ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) := by
  classical
  set bound := (2 : ℝ) ^ 86 * (Stage1.tJS G run l : ℝ) * run.LY G Y ^ 19 *
    Stage1.rhoJS G run l ^ (-3 : ℤ) * ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) with hbound
  have hb0 : 0 ≤ bound := by
    rw [hbound]
    have : 0 ≤ run.LY G Y ^ 19 := by
      have := Real.logb_nonneg (b := 2) (x := ((run.ancVerts G Y).card : ℝ)) (by norm_num)
      rcases Nat.eq_zero_or_pos (run.ancVerts G Y).card with h | h
      · unfold Run.LY; rw [h]; simp
      · exact pow_nonneg (this (by exact_mod_cast h)) _
    have h1 : 0 ≤ Stage1.rhoJS G run l ^ (-3 : ℤ) := zpow_nonneg hρ0.le _
    have h2 : (0 : ℝ) ≤ ((run.ancVerts G Y).card : ℝ) ^ (-3 : ℤ) := zpow_nonneg (Nat.cast_nonneg _) _
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ 86 * (Stage1.tJS G run l : ℝ) :=
      mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg h3 this) h1) h2
  show ((Stage1.colouringLaw G run Y).compProd fun _ => Stage1.jsLaw G run Y).prob _ ≤ bound
  refine FinDist.prob_compProd_le_of_forall _ _ fun c _ => ?_
  by_cases ha : Stage1.COLa G run Y (c, fun _ => none)
  · set X := Stage1.LJS G run Y c l j with hX
    have hXv : X.verts = run.ancVerts G Y := by
      rw [hX, Stage1.LJS, Stage1.lentClass]; simp [FGraph.restrictEdges]
    have hXc : (X.card : ℝ) = ((run.ancVerts G Y).card : ℝ) := by rw [FGraph.card, hXv]
    have hLX : Real.logb 2 (X.card : ℝ) = run.LY G Y := by rw [hXc]; rfl
    have hexp : X.IsExpander (run.ancEps G Y)
        (run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ))) :=
      ha.2.2.1 _ (Stage1.mem_lentIdx.2 (Or.inr (Or.inl (Stage1.JS_mem_IJS.2 ⟨hl, hj⟩))))
    have hRS := Stage1.isRSubset_Tj G run Y hl hj
    set rs := FinDist.rsubset (run.ancVerts G Y) (Stage1.rhoJS G run l) hRS.nonneg hRS.le_one
    have hrs : rs.IsRSubset (fun T => T) X.verts (Stage1.rhoJS G run l) := by
      rw [hXv]; exact FinDist.isRSubset_rsubset _ _
    have hT := hT16 V X (run.ancEps G Y) (run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ)))
      (Stage1.rhoJS G run l) (Stage1.tJS G run l : ℝ) (Finset V) rs (fun T => T) hε1 hε2 hexp
      hρ0 hRS.le_one ht1 hrs (by rw [hLX, hXc]; exact hρN) (by rw [hLX]; exact hs)
    rw [hLX, hXc] at hT
    have hsub : Prod.mk c ⁻¹' BadJS G run Y l j ⊆ (fun lab => Stage1.Tj G run Y lab l j) ⁻¹'
        {T | X.IsPathConnected ((2 : ℝ) ^ 12 * run.LY G Y ^ 4) (Stage1.tJS G run l) T}ᶜ :=
      fun lab h => h.2
    refine (FinDist.prob_mono _ hsub).trans ?_
    rw [hRS.prob_preimage, FinDist.prob_compl]
    linarith
  · refine le_trans (le_of_eq ?_) hb0
    rw [FinDist.prob_eq_zero_iff]
    intro lab hlab
    exact absurd hlab.1 ha

/-- [s3:lemCOL] (b), failure bound: "Condition on the colouring with (a). … By row 6 the failures
sum to at most `|V(Y)|^{-2}/4`": `P((a) ∧ ¬(b)) ≤ |V(Y)|^{-2}/4` under the law of the lending data.
Inputs: Theorem 16* (`hT16`), Lemma s2:lemTower (b) (`hBR`, `hBM`, `hRest`), rows 5 and 6 of the
COL-JV table (`h5`, `h6`), and Γ1(f) at `μ = log λ_r` (row 12). -/
theorem prob_notb_le (hT16 : Spec.T16sStatement.{u, u}) (hBR : Spec.TowerBRoundStatement.{u})
    (hBM : Spec.TowerBMStatement.{u}) (hRest : Spec.TowerBRestStatement.{u})
    (h5 : Spec.COLJVRow5Statement.{u}) (h6 : Spec.COLJVRow6Statement.{u})
    {Dstar : ℝ} (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) (Y : PartId)
    (hY : Y ∈ run.ancestors G) :
    (Stage1.colLaw G run Y).prob {ω | Stage1.COLa G run Y ω ∧ ¬ Stage1.COLb G run Y ω} ≤
      ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 4 := by
  classical
  have hR := Standing.isRound_of_mem_ancestors hY
  have hD1 := Run.Valid.dstar_le run G hV (l := 1) ⟨le_rfl, le_trans hR.1 hR.2⟩
  have hN4 : (0 : ℝ) ≤ ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 4 :=
    div_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
  by_cases hR2 : Y.1 + 2 ≤ run.R
  swap
  · refine le_trans (le_of_eq ?_) hN4
    rw [FinDist.prob_eq_zero_iff]
    intro ω hω
    exfalso
    apply hω.2
    intro l hl
    have := (Stage1.mem_lateRounds run).1 hl
    omega
  -- standing facts
  obtain ⟨-, hx0, hlamx⟩ := Standing.lam_facts hΓ hV hR
  have hx := Standing.lam_ge hΓ hV hR
  have hcol := Standing.col3_at hΓ hV hR
  have hRi : Y.1 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 hR
  obtain ⟨-, -, -, -, -, -, hanc⟩ := hBR V G Dstar run hΓ.core hV hD1 Y.1 hRi
  obtain ⟨hLΛ, hΛ⟩ := hanc Y hY rfl
  have hL0 := Standing.LY_nonneg (G := G) (run := run) Y
  have hN := Standing.card_ancVerts_ge hY
  have hMb : (run.M G (Y.1 + 2) : ℝ) ≤ COLTable.Mbar (Real.logb 2 (run.lam G Y.1)) := by
    have := ((hBM V G Dstar run hΓ.core hV hD1).1 (Y.1 + 2) (by have := hR.1; omega) hR2).1
    rwa [Nat.add_sub_cancel] at this
  have h12 := hcol.row (i := 12) (by norm_num) (by norm_num)
  rw [COLTable.row12_iff, hlamx] at h12
  have hhalf := (hRest V G Dstar run hΓ.core hV hD1).2.1
  have hmono : ∀ k : ℕ, Y.1 + 2 + k ≤ run.R → run.M G (Y.1 + 2 + k) ≤ run.M G (Y.1 + 2) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      have h1 := hhalf (Y.1 + 2 + (k + 1)) (by omega) hk
      rw [show Y.1 + 2 + (k + 1) - 1 = Y.1 + 2 + k by omega] at h1
      have := ih (by omega)
      omega
  have hε1 : (2 : ℝ) ^ (-7 : ℤ) ≤ run.ancEps G Y ∧ run.ancEps G Y ≤ 1 := by
    by_cases hl : run.isLight G Y.1 Y.2
    · rw [Run.ancEps_of_isLight run G hl, epsC]; norm_num
    · rw [Run.ancEps_of_not_isLight run G hl, epsC]; norm_num
  have row5 := h5 V G Dstar run hΓ hV Y hY hR2
  set x := run.lam G Y.1 with hxdef
  set L := run.LY G Y with hLdef
  set N : ℝ := ((run.ancVerts G Y).card : ℝ) with hNdef
  set M : ℝ := (run.M G (Y.1 + 2) : ℝ) with hMdef
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have hM8 : M ≤ x ^ (8 / 5 : ℝ) := hMb.trans h12
  -- per round `l`
  have hper : ∀ l ∈ Stage1.lateRounds run Y.1, ∀ j < Stage1.KJS G run l,
      (Stage1.colLaw G run Y).prob (BadJS G run Y l j) ≤
        (2 : ℝ) ^ 86 * (Stage1.tJS G run l : ℝ) * L ^ 19 *
          Stage1.rhoJS G run l ^ (-3 : ℤ) * N ^ (-3 : ℤ) := by
    intro l hl j hj
    obtain ⟨hl1, hl2⟩ := (Stage1.mem_lateRounds run).1 hl
    have hMl : (run.M G l : ℝ) ≤ M := by
      have := hmono (l - (Y.1 + 2)) (by omega)
      rw [show Y.1 + 2 + (l - (Y.1 + 2)) = l by omega] at this
      exact (Nat.cast_le.2 this : ((run.M G l : ℕ) : ℝ) ≤ (run.M G (Y.1 + 2) : ℝ))
    have h40 : (2 : ℝ) ^ 40 ≤ (run.M G l : ℝ) := ParamHyp.two40_le_M (d := run.d G l)
    have hMl0 : (0 : ℝ) < run.M G l := lt_of_lt_of_le (by norm_num) h40
    have hρ : Stage1.rhoJS G run l = ((run.M G l : ℝ) ^ 4)⁻¹ := by
      unfold Stage1.rhoJS; rw [zpow_neg, zpow_ofNat]
    have hρ0 : 0 < Stage1.rhoJS G run l := by rw [hρ]; positivity
    have ht : (Stage1.tJS G run l : ℝ) ≤ 3 * M := by
      unfold Stage1.tJS; push_cast; linarith
    have ht1 : (1 : ℝ) ≤ Stage1.tJS G run l := by
      unfold Stage1.tJS; push_cast; linarith
    -- `ρ_l N ≥ L^2`
    have hM4 : (run.M G l : ℝ) ^ 4 ≤ x ^ 7 := by
      have h1 : (run.M G l : ℝ) ^ 4 ≤ (x ^ (8 / 5 : ℝ)) ^ 4 :=
        pow_le_pow_left₀ hMl0.le (hMl.trans hM8) 4
      have h2 : (x ^ (8 / 5 : ℝ)) ^ 4 ≤ x ^ 7 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast x 7]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      exact h1.trans h2
    have hρN : L ^ 2 ≤ Stage1.rhoJS G run l * N := by
      rw [hρ, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      have hL2 : L ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ hL0 (hLΛ.trans hΛ) 2
      have h1 : L ^ 2 * (run.M G l : ℝ) ^ 4 ≤ (2 * x) ^ 2 * x ^ 7 :=
        mul_le_mul hL2 hM4 (by positivity) (by positivity)
      have h94 : (8 : ℝ) ≤ x ^ 94 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 94)
      have e : (2 * x) ^ 2 * x ^ 7 = 4 * x ^ 9 := by ring
      have e2 : x ^ 103 = x ^ 9 * x ^ 94 := by ring
      have hx9 : 0 ≤ x ^ 9 := by positivity
      nlinarith
    -- `2^{135} t L^{28} ρ^{-5} ≤ s_Y/(8k_lend)`
    have hρ5 : Stage1.rhoJS G run l ^ (-5 : ℤ) = (run.M G l : ℝ) ^ 20 := by
      unfold Stage1.rhoJS; rw [← zpow_mul]; norm_num
    have hs : (2 : ℝ) ^ 135 * (Stage1.tJS G run l : ℝ) * L ^ 28 *
        Stage1.rhoJS G run l ^ (-5 : ℤ) ≤ run.ancS G Y / (8 * (Stage1.klend G run Y : ℝ)) := by
      rw [hρ5]
      refine le_trans ?_ row5
      have hM20 : (run.M G l : ℝ) ^ 20 ≤ M ^ 20 := pow_le_pow_left₀ hMl0.le hMl 20
      have ht0 : (0 : ℝ) ≤ Stage1.tJS G run l := Nat.cast_nonneg _
      have hL28 : 0 ≤ L ^ 28 := pow_nonneg hL0 _
      calc (2 : ℝ) ^ 135 * (Stage1.tJS G run l : ℝ) * L ^ 28 * (run.M G l : ℝ) ^ 20
          ≤ (2 : ℝ) ^ 135 * (3 * M) * L ^ 28 * M ^ 20 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ht (by norm_num)) hL28) hM20 (by positivity)
            exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hL28
        _ = _ := rfl
    exact prob_badJS_le hT16 Y l j hl hj hε1.1 hε1.2 hρ0 ht1 hρN hs
  -- the union bound and row 6
  have hsub : {ω | Stage1.COLa G run Y ω ∧ ¬ Stage1.COLb G run Y ω} ⊆
      ⋃ l ∈ Stage1.lateRounds run Y.1, ⋃ j ∈ Finset.range (Stage1.KJS G run l),
        BadJS G run Y l j := by
    intro ω hω
    obtain ⟨ha, hb⟩ := hω
    simp only [Stage1.COLb, not_forall] at hb
    obtain ⟨l, hl, j, hj, hnot⟩ := hb
    simp only [Set.mem_iUnion]
    exact ⟨l, hl, j, Finset.mem_range.2 hj, ha, hnot⟩
  refine (FinDist.prob_mono _ hsub).trans ?_
  refine (FinDist.prob_biUnion_le _ _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun l hl =>
    (FinDist.prob_biUnion_le _ _ _).trans (Finset.sum_le_sum fun j hj =>
      hper l hl j (Finset.mem_range.1 hj))) ?_
  exact h6 V G Dstar run hΓ hV Y hY hR2

end EG.COLbProof
