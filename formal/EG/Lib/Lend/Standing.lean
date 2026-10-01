module

public import EG.Defs.Stage1.COL
public import EG.Lib.Gamma.Full
public import EG.Lib.Found.Gamma
public import EG.Lib.HB.Run
public import EG.Lib.Lend.COLTable
public import EG.Lib.Vortex.Params
public import EG.Lib.Stage1.COL

/-!
# Standing bounds of the proof of [s3:lemCOLJV] that hold in the HB model — unit P4A

Manuscript v6.1, `s3.tex`, proof of Lemma s3:lemCOLJV: "Every round `r ≤ R` has `d_r ≥ D_*`, so
`μ = log λ_r ≥ log log D_*`, and the items of Γ1 hold at `μ`", and
(B4) "`|V(Y)| ≥ P_r/2 ≥ λ^{103}/2`. A standalone `Y` has `|V(Y)| = |Y^0| ≥ P_r`, and a light `Y`
has `|Y| ≥ |Y^0|/2 ≥ P_r/2`; and `P_r = ⌈λ^{C'}⌉` with `C' = 103`" (definitional in the locked
HB model: pre-parts have `|Z^0| ≥ P_r`, and (L1) `2|S_Z| ≤ |Z^0|`).

Also elementary bounds on the parameters of s3:defCOL: `t_Y = ⌈λ^{1.6}⌉ ≤ 2λ^{1.6}`,
`L_Y ≥ 0`, and `k_own = 4J_Y + 1 ≤ L_Y/2 + 1` (the manuscript uses `k_own ≤ L_Y`; the bound here
is equivalent for the use `k_own ≤ 2λ`).
-/

public section

namespace EG.Standing

open EG.HB Real

variable {V : Type*} [DecidableEq V] {G : FGraph V} {Dstar : ℝ} {run : Run V}

theorem isRound_of_mem_ancestors {Y : PartId} (hY : Y ∈ run.ancestors G) : run.IsRound Y.1 :=
  Run.isRound_of_mem_parts run G hY

/-- "Every round `r ≤ R` has `d_r ≥ D_*`, so `μ = log λ_r ≥ log log D_*`"; `λ_r > 0` and
`2^μ = λ_r`. -/
theorem lam_facts (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {l : ℕ} (hl : run.IsRound l) :
    logb 2 (logb 2 Dstar) ≤ logb 2 (run.lam G l) ∧ 0 < run.lam G l ∧
      COLTable.lam (logb 2 (run.lam G l)) = run.lam G l := by
  have hd := Run.Valid.dstar_le run G hV hl
  have h2 := hΓ.two_lt
  have hlam : run.lam G l = logb 2 (run.d G l) := rfl
  have hpos : 0 < run.lam G l := by
    rw [hlam]; exact Real.logb_pos (by norm_num) (by linarith)
  refine ⟨?_, hpos, ?_⟩
  · rw [hlam]; exact loglog_mono h2 hd
  · rw [COLTable.lam_eq, Real.rpow_logb (by norm_num) (by norm_num) hpos]

/-- `λ_r ≥ 2^{256}` (from Γ1(a) at `μ = log λ_r`). -/
theorem lam_ge (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {l : ℕ} (hl : run.IsRound l) :
    (2 : ℝ) ^ 256 ≤ run.lam G l := by
  obtain ⟨hμ, hpos, hlam⟩ := lam_facts hΓ hV hl
  have ha : (2 : ℝ) ^ 8 ≤ logb 2 (run.lam G l) := (hΓ.items hμ).a
  rw [← hlam, COLTable.lam_eq]
  calc (2 : ℝ) ^ 256 = (2 : ℝ) ^ ((2 : ℝ) ^ 8) := by
        rw [← Real.rpow_natCast]; norm_num
    _ ≤ (2 : ℝ) ^ logb 2 (run.lam G l) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha

/-- The column-3 inequalities of Table s3:tabCOLJV hold at `μ = log λ_r` (Γ1(f)). -/
theorem col3_at (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {l : ℕ} (hl : run.IsRound l) :
    COLTable.col3 (logb 2 (run.lam G l)) :=
  hΓ.col3 (lam_facts hΓ hV hl).1

/-- `L_Y = log |V(Y)| ≥ 0`. -/
theorem LY_nonneg (Y : PartId) : 0 ≤ run.LY G Y := by
  unfold Run.LY
  rcases Nat.eq_zero_or_pos (run.ancVerts G Y).card with h | h
  · rw [h, Nat.cast_zero, Real.logb_zero]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

/-- `t_Y = ⌈λ^{1.6}⌉ ≤ 2λ^{1.6}` for `λ ≥ 1`. -/
theorem tY_le {Y : PartId} (h1 : 1 ≤ run.lam G Y.1) :
    (Stage1.tY G run Y : ℝ) ≤ 2 * run.lam G Y.1 ^ (8 / 5 : ℝ) := by
  unfold Stage1.tY
  have e : (1.6 : ℝ) = 8 / 5 := by norm_num
  rw [e]
  have hge : 1 ≤ run.lam G Y.1 ^ (8 / 5 : ℝ) := Real.one_le_rpow h1 (by norm_num)
  have := Nat.ceil_lt_add_one (zero_le_one.trans hge)
  linarith

/-- `J = ⌊log₂(L/8)⌋ ≤ L/8` (`L ≥ 0`). -/
theorem floor_logb_le_self {x : ℝ} (hx : 0 ≤ x) : (⌊logb 2 x⌋₊ : ℝ) ≤ x := by
  by_cases h1 : 1 ≤ x
  · have h := Vortex.two_pow_floor_logb_le h1
    have hlt : (⌊logb 2 x⌋₊ : ℝ) < (2 : ℝ) ^ ⌊logb 2 x⌋₊ := by
      exact_mod_cast Nat.lt_two_pow_self
    linarith
  · push Not at h1
    have : logb 2 x ≤ 0 := by
      rcases hx.eq_or_lt with h0 | h0
      · rw [← h0, Real.logb_zero]
      · exact Real.logb_nonpos (by norm_num) h0.le h1.le
    rw [Nat.floor_eq_zero.2 (lt_of_le_of_lt this one_pos), Nat.cast_zero]
    exact hx

/-- `k_own = 4J_Y + 1 ≤ L_Y/2 + 1`. -/
theorem kown_le (Y : PartId) : (Stage1.kown G run Y : ℝ) ≤ run.LY G Y / 2 + 1 := by
  unfold Stage1.kown Stage1.JY Vortex.pvJ
  have hL : Vortex.L (run.ancVerts G Y).card = run.LY G Y := rfl
  rw [hL]
  have h := floor_logb_le_self (x := run.LY G Y / 8) (by linarith [LY_nonneg (run := run) (G := G) Y])
  push_cast
  linarith

/-- (B4) "`|V(Y)| ≥ P_r/2 ≥ λ^{103}/2`" (definitional in the HB model). -/
theorem card_ancVerts_ge {Y : PartId} (hY : Y ∈ run.ancestors G) :
    run.lam G Y.1 ^ 103 / 2 ≤ ((run.ancVerts G Y).card : ℝ) := by
  have hR := isRound_of_mem_ancestors hY
  have ha : Y.2 ∈ Round.prePartAddrs (run.graph G Y.1) (run.choice Y.1) := by
    rw [← run.prePartAddrs_of_isRound G hR]; exact (Run.mem_ancestors run G).1 hY
  unfold Round.prePartAddrs at ha
  have hP : POf (Round.d (run.graph G Y.1)) ≤
      (Round.Z0 (run.graph G Y.1) (run.choice Y.1) Y.2).card := (Finset.mem_filter.1 ha).2
  have hPl : run.lam G Y.1 ^ 103 ≤ (POf (Round.d (run.graph G Y.1)) : ℝ) := by
    unfold POf
    exact Nat.le_ceil _
  have hZ : run.lam G Y.1 ^ 103 ≤
      ((Round.Z0 (run.graph G Y.1) (run.choice Y.1) Y.2).card : ℝ) :=
    hPl.trans (by exact_mod_cast hP)
  unfold Run.ancVerts Run.partVerts Round.partVerts
  split_ifs with hl
  · have hL1 : 2 * (Round.guests (run.graph G Y.1) (run.choice Y.1) Y.2).card ≤
        (Round.Z0 (run.graph G Y.1) (run.choice Y.1) Y.2).card := hl.1
    rw [Finset.card_sdiff_of_subset (Round.guests_subset _ _ _)]
    have hle := (Round.guests_subset (run.graph G Y.1) (run.choice Y.1) Y.2)
    have hc := Finset.card_le_card hle
    rw [Nat.cast_sub hc]
    have : (2 : ℝ) * (Round.guests (run.graph G Y.1) (run.choice Y.1) Y.2).card ≤
        (Round.Z0 (run.graph G Y.1) (run.choice Y.1) Y.2).card := by exact_mod_cast hL1
    linarith
  · have h0 : (0 : ℝ) ≤ (Round.Z0 (run.graph G Y.1) (run.choice Y.1) Y.2).card :=
      Nat.cast_nonneg _
    linarith

end EG.Standing
