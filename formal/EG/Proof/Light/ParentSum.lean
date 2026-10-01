module

public import EG.Spec.Light.Parent
public import EG.Proof.Light.EtaHalving
public import EG.Proof.HB.TowerBM
public import EG.Proof.HB.TowerA
public import EG.Proof.HB.TowerBLate
public import EG.Proof.HB.CapPrePart
public import EG.Lib.Lend.Standing
public import EG.Lib.Light.Stages
public import EG.Lib.Gamma.Full
public import EG.Proof.HB.StructureLight
public import EG.Proof.Stage1.COLc

/-!
# Proof of the sum over the rounds of Lemma parent side (s5:lemParent (ii), Step 9)

Proof file of probe unit P4B (probe P-4, part 2), proof round 1: `EG.lemParentSum`
(`LemParentSumStatement`):
`∑_{l=3}^{R} (4·14(J̄_l+1)M_l(M_l+1)ν_l + 14(J̄_l+1)n/(102 log₂λ_{l−2})^2) ≤ ε_ch(D_*) n`.

Manuscript v6.1, `s5.tex`, proof of [s5:lemParent], Step 9: "By (F-a), `J̄_l+1 ≤ log₂log₂M_l ≤ M_l`;
moreover `M_l+1 ≤ 2M_l`, `ν_l ≤ 2.74n/P_{l−2}`, and `P_{l−2} ≥ M_l^{13}`. So
`4·14(J̄_l+1)M_l(M_l+1)ν_l ≤ … ≤ 307n/M_l`, and `∑_l 307n/M_l ≤ 614n/D_*`. … `log₂M_l ≤
2A log₂(A log₂λ_{l−2})`. With `η(x) := …` this gives `cap_l ≤ (14/102^2) n η(λ_{l−2})`. … As
`λ_{r'} ≥ 2^{λ_{r'+1}/A}`, `η(λ_{r'}) ≤ η(2^{λ_{r'+1}/A}) ≤ η(λ_{r'+1})/2`. Hence
`∑_{l=3}^R η(λ_{l−2}) ≤ 2η(λ_{R−2}) ≤ 2η(log₂D_*)` … Adding the two sums gives `ε_ch(D_*)n`."

Inputs: `EG.etaHalving` (proved), the declared inputs `EG.towerBM` ([s2:lemTower] (b), `M_l`
clauses), `EG.towerA` ((a)), `EG.towerBLate` ((b), late clauses), `EG.capPrePart` ([s2:lemCap]
(ii), `|Z^0| ≤ M_l`, for (F-a)). The geometric sum is done inline, as in the TeX. Design note
`formal/work/p2b/P4B.md`.
-/

public section

namespace EG

open EG.HB EG.Stage1 EG.Light Real

universe u

namespace ParentSumAux

theorem A_eq : (Aexp : ℝ) = 105 := by norm_num [Aexp]

/-- `M_l ≥ 2^{40}` (definition (R2)). -/
theorem M_ge {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V) (l : ℕ) :
    (2 : ℝ) ^ 40 ≤ (run.M G l : ℝ) := by
  show (2 : ℝ) ^ 40 ≤ (MOf (run.d G l) : ℝ)
  unfold MOf
  exact (le_max_left _ _).trans (Nat.le_ceil _)

/-- (F-a): "`J_Z+1 ≤ log₂L_Z − 2 ≤ log₂log₂M_l`" for `1 ≤ N ≤ M` (`J = ⌊log₂(L/8)⌋`,
`L = log₂N`), and `≥ 1` also when `J = 0` (`M ≥ 2^{40}`). -/
theorem pvJ_add_one_le {N : ℕ} {M : ℝ} (hN : 1 ≤ N) (hNM : (N : ℝ) ≤ M) (hM : (2 : ℝ) ^ 40 ≤ M) :
    (Vortex.pvJ N : ℝ) + 1 ≤ logb 2 (logb 2 M) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hlogM : (40 : ℝ) ≤ logb 2 M := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hM0]
    calc (2 : ℝ) ^ (40 : ℝ) = 2 ^ (40 : ℕ) := by norm_num
      _ ≤ M := hM
  have hll : (1 : ℝ) ≤ logb 2 (logb 2 M) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]; linarith
  unfold Vortex.pvJ
  have hL0 : 0 ≤ Vortex.L N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  set L := Vortex.L N with hL
  rcases Nat.eq_zero_or_pos ⌊logb 2 (L / 8)⌋₊ with h0 | hpos
  · rw [h0, Nat.cast_zero, zero_add]; exact hll
  · have h1 : (1 : ℝ) ≤ logb 2 (L / 8) := Nat.floor_pos.1 hpos
    have hLpos : 0 < L := by
      rcases hL0.lt_or_eq with h | h
      · exact h
      · rw [← h, zero_div, Real.logb_zero] at h1; linarith
    have hfl : (⌊logb 2 (L / 8)⌋₊ : ℝ) ≤ logb 2 (L / 8) := Nat.floor_le (by linarith)
    have hdiv : logb 2 (L / 8) = logb 2 L - 3 := by
      rw [Real.logb_div hLpos.ne' (by norm_num)]
      have : logb 2 (8 : ℝ) = 3 := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        norm_num
      rw [this]
    have hLM : L ≤ logb 2 M := Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hN) hNM
    have hmono : logb 2 L ≤ logb 2 (logb 2 M) := Real.logb_le_logb_of_le (by norm_num) hLpos hLM
    linarith

/-- Geometric sum ("`X_r ≤ X_{r+1}/2` gives `∑ X_r ≤ 2X_R`"), inline as in Step 9. -/
theorem geom_sum (y : ℕ → ℝ) (a : ℕ) (h0 : 0 ≤ y a) :
    ∀ m, a ≤ m → (∀ l, a ≤ l → l < m → y l ≤ y (l + 1) / 2) →
      ∑ l ∈ Finset.Icc a m, y l ≤ 2 * y m := by
  intro m ham
  induction m, ham using Nat.le_induction with
  | base => intro _; simp; linarith
  | succ m ham ih =>
    intro hstep
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := ih fun l hl hlm => hstep l hl (by omega)
    have h2 := hstep m ham (by omega)
    linarith

/-- `η ≥ 0` on `[log₂D_*, ∞)`. -/
theorem etaCh_nonneg {Dstar x : ℝ} (hΓ : Gamma1 Dstar) (hx : logb 2 Dstar ≤ x) :
    0 ≤ etaCh x := by
  have h8 : (2 : ℝ) ^ 8 ≤ logb 2 x := (hΓ.1.items_logb_of_le hx).a
  have hA := A_eq
  have hu : 2 ≤ logb 2 ((Aexp : ℝ) * logb 2 x) := EtaAux.two_le_logb (by rw [hA]; nlinarith)
  have hg : 2 ≤ logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * logb 2 x)) :=
    EtaAux.two_le_logb (by rw [hA] at hu ⊢; nlinarith)
  unfold etaCh
  positivity

/-- "`2^{x/A} ≥ log₂D_*` for `x ≥ log₂D_*`" (`x/A ≥ log₂ x` by Γ1 (b) at `log₂ x`). -/
theorem logb_le_two_rpow_div {Dstar x : ℝ} (hΓ : Gamma1 Dstar) (hx : logb 2 Dstar ≤ x) :
    logb 2 Dstar ≤ (2 : ℝ) ^ (x / (Aexp : ℝ)) := by
  have hL := hΓ.1.two_pow_256_le_logb
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 2 ^ 256 by norm_num]
  have hit := hΓ.1.items_logb_of_le hx
  have h8 : (2 : ℝ) ^ 8 ≤ logb 2 x := hit.a
  have hb := hit.b
  unfold Gamma1b at hb
  rw [Real.rpow_logb (by norm_num) (by norm_num) hx0] at hb
  have hA := A_eq
  have hlx : logb 2 x ≤ x / (Aexp : ℝ) := by
    rw [hA, le_div_iff₀ (by norm_num)]
    rw [hA] at hb
    have h1 : (1 : ℝ) ≤ logb 2 x := le_trans (by norm_num) h8
    have h2 : 1 ≤ logb 2 x ^ 2 := one_le_pow₀ h1
    have h3 : logb 2 x ≤ logb 2 x ^ 3 := by
      have : logb 2 x * 1 ≤ logb 2 x * logb 2 x ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one h1)
      nlinarith
    nlinarith
  have : x ≤ (2 : ℝ) ^ (x / (Aexp : ℝ)) := by
    calc x = (2 : ℝ) ^ (logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num) hx0).symm
      _ ≤ (2 : ℝ) ^ (x / (Aexp : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlx
  linarith

variable {V : Type*} [DecidableEq V] {G : FGraph V} {Dstar : ℝ} {run : Run V}

/-- `λ_r = log₂ d_r ≥ log₂ D_*` for every round `r`. -/
theorem logb_le_lam (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {r : ℕ} (hr : run.IsRound r) :
    logb 2 Dstar ≤ run.lam G r := by
  have hd := Run.Valid.dstar_le run G hV hr
  exact Real.logb_le_logb_of_le (by norm_num) (by linarith [hΓ.1.two_lt]) hd

/-- (F-a) for the round: "`J̄_l+1 ≤ log₂log₂M_l`". -/
theorem Jbar_add_one_le (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) {l : ℕ}
    (hl : l ∈ Finset.Icc 1 run.R) :
    (Jbar G run l : ℝ) + 1 ≤ logb 2 (logb 2 (run.M G l : ℝ)) := by
  classical
  have hM := M_ge G run l
  have hcap := capPrePart V G Dstar run hΓ.gamma2a hV l hl
  unfold Jbar
  rcases Finset.eq_empty_or_nonempty ((run.lightParts G).filter fun Z => Z.1 = l) with he | hne
  · rw [he, Finset.sup_empty]
    have := pvJ_add_one_le (N := 1) le_rfl
      (by rw [Nat.cast_one]; linarith [show (1 : ℝ) ≤ 2 ^ 40 by norm_num]) hM
    have h0 : (0 : ℝ) ≤ (Vortex.pvJ 1 : ℝ) := Nat.cast_nonneg _
    simp only [bot_eq_zero', Nat.cast_zero, zero_add]
    linarith
  · obtain ⟨Z, hZ, hsup⟩ := Finset.exists_mem_eq_sup _ hne (JY G run)
    rw [hsup]
    obtain ⟨hZL, hZl⟩ := Finset.mem_filter.1 hZ
    obtain ⟨-, hZa, -⟩ := (mem_lightParts_iff G run Z).1 hZL
    have hanc := COLcAux.mem_ancestors_of_mem_lightParts hZL
    have hN1 : 1 ≤ (run.ancVerts G Z).card := by
      have := Standing.card_ancVerts_ge hanc
      have hlam := Standing.lam_ge hΓ hV (Standing.isRound_of_mem_ancestors hanc)
      have : (1 : ℝ) ≤ ((run.ancVerts G Z).card : ℝ) := by
        have h103 : (2 : ℝ) ^ 103 ≤ run.lam G Z.1 ^ 103 :=
          pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) hlam) 103
        have : (2 : ℝ) ≤ 2 ^ 103 := by norm_num
        linarith
      exact_mod_cast this
    have hNM : ((run.ancVerts G Z).card : ℝ) ≤ (run.M G l : ℝ) := by
      have h1 : (run.ancVerts G Z).card ≤ (run.Z0 G Z.1 Z.2).card :=
        Finset.card_le_card (run.partVerts_subset_Z0 G Z.1 Z.2)
      have h2 := (hcap.2 Z.2 (by rw [← hZl]; exact hZa)).1
      rw [hZl] at h1
      exact_mod_cast h1.trans h2
    exact pvJ_add_one_le hN1 hNM hM

/-- "`log₂M_l ≤ 2A log₂(A log₂λ_{l−2})`", hence `log₂log₂M_l ≤ log₂(2A log₂(A log₂λ_{l−2}))`. -/
theorem loglogM_le (hΓ : Gamma1 Dstar) (hV : run.Valid G Dstar) (hd1 : Dstar ≤ run.d G 1)
    {l : ℕ} (hl3 : 3 ≤ l) (hlR : l ≤ run.R) :
    logb 2 (logb 2 (run.M G l : ℝ)) ≤
      logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * logb 2 (run.lam G (l - 2)))) := by
  have hBM := ((towerBM V G Dstar run hΓ.1 hV hd1).1 l hl3 hlR).1
  have hlam := Standing.lam_ge hΓ hV (l := l - 2) ⟨by omega, by omega⟩
  have hA := A_eq
  set μ := logb 2 (run.lam G (l - 2))
  have hμ : (256 : ℝ) ≤ μ := by
    show (256 : ℝ) ≤ logb 2 _
    rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le (by norm_num) hlam)]
    calc (2 : ℝ) ^ (256 : ℝ) = 2 ^ (256 : ℕ) := by norm_num
      _ ≤ _ := hlam
  have hM := M_ge G run l
  have hM0 : 0 < (run.M G l : ℝ) := lt_of_lt_of_le (by norm_num) hM
  have hAμ : 0 < (Aexp : ℝ) * μ := by rw [hA]; linarith
  have hlogM : logb 2 (run.M G l : ℝ) ≤ 2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * μ) := by
    calc logb 2 (run.M G l : ℝ) ≤ logb 2 (((Aexp : ℝ) * μ) ^ (2 * Aexp)) :=
          Real.logb_le_logb_of_le (by norm_num) hM0 hBM
      _ = 2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * μ) := by
          rw [Real.logb_pow]; push_cast; ring
  have hlogM0 : 0 < logb 2 (run.M G l : ℝ) :=
    Real.logb_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hM)
  exact Real.logb_le_logb_of_le (by norm_num) hlogM0 hlogM

end ParentSumAux

open ParentSumAux

/-- [s5:lemParent] (ii), the sum over the rounds (with `cap_l` replaced by its bound, T0):
`∑_{l=3}^{R} (4·14(J̄_l+1)M_l(M_l+1)ν_l + 14(J̄_l+1)n/(102 log₂λ_{l−2})^2) ≤ ε_ch(D_*) n`. -/
theorem lemParentSum : EG.Spec.LemParentSumStatement.{u} := by
  intro V _ G N0 Dstar run h
  obtain ⟨hΓ, -, -, -, hd1, hV⟩ := h
  have hA := A_eq
  set n : ℝ := (G.card : ℝ) with hn_def
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hD : 2 < Dstar := hΓ.1.two_lt
  have hL := hΓ.1.two_pow_256_le_logb
  have hEta := etaHalving Dstar hΓ
  -- the first term: `≤ 307n/M_l`
  have hT1 : ∀ l ∈ Finset.Icc 3 run.R,
      4 * 14 * ((Jbar G run l : ℝ) + 1) * (run.M G l : ℝ) * ((run.M G l : ℝ) + 1) *
        (run.nuAnc G l : ℝ) ≤ 307 * n / (run.M G l : ℝ) := by
    intro l hl
    obtain ⟨hl3, hlR⟩ := Finset.mem_Icc.1 hl
    set M : ℝ := (run.M G l : ℝ)
    have hM := M_ge G run l
    have hM1 : 1 ≤ M := le_trans (by norm_num) hM
    have hM0 : 0 < M := by linarith
    have hJ := Jbar_add_one_le hΓ hV (l := l) (Finset.mem_Icc.2 ⟨by omega, hlR⟩)
    have hlogM : (40 : ℝ) ≤ logb 2 M := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hM0]
      calc (2 : ℝ) ^ (40 : ℝ) = 2 ^ (40 : ℕ) := by norm_num
        _ ≤ M := hM
    have hJM : (Jbar G run l : ℝ) + 1 ≤ M := by
      have h1 := EG.logb_le_sub_one (y := logb 2 M) (by linarith)
      have h2 := EG.logb_le_sub_one (y := M) (by linarith)
      linarith
    obtain ⟨hPM, hnu⟩ := towerBLate V G Dstar run hΓ.1 hV hd1 l hl3 hlR
    have hPM' : M ^ 13 ≤ (run.P G (l - 2) : ℝ) := by
      simp only [M]; exact_mod_cast hPM
    have hM13 : 0 < M ^ 13 := by positivity
    have hnu' : (run.nuAnc G l : ℝ) ≤ 2.74 * n / M ^ 13 :=
      hnu.trans (div_le_div_of_nonneg_left (by positivity) hM13 hPM')
    calc 4 * 14 * ((Jbar G run l : ℝ) + 1) * M * (M + 1) * (run.nuAnc G l : ℝ)
        ≤ 4 * 14 * M * M * (2 * M) * (2.74 * n / M ^ 13) := by
          gcongr
          linarith
      _ = 306.88 * (n / M ^ 10) := by field_simp; ring
      _ ≤ 307 * (n / M) := by
          have h10 : M ≤ M ^ 10 := le_self_pow₀ hM1 (by norm_num)
          have := div_le_div_of_nonneg_left hn hM0 h10
          have h0 : 0 ≤ n / M ^ 10 := by positivity
          nlinarith
      _ = 307 * n / M := by ring
  -- the second term: `≤ (14/102^2) n η(λ_{l−2})`
  have hT2 : ∀ l ∈ Finset.Icc 3 run.R,
      14 * ((Jbar G run l : ℝ) + 1) * n / (102 * logb 2 (run.lam G (l - 2))) ^ 2 ≤
        14 / 10404 * n * etaCh (run.lam G (l - 2)) := by
    intro l hl
    obtain ⟨hl3, hlR⟩ := Finset.mem_Icc.1 hl
    have hJ := (Jbar_add_one_le hΓ hV (l := l) (Finset.mem_Icc.2 ⟨by omega, hlR⟩)).trans
      (loglogM_le hΓ hV hd1 hl3 hlR)
    have hlam := Standing.lam_ge hΓ hV (l := l - 2) ⟨by omega, by omega⟩
    have hμ : 0 < logb 2 (run.lam G (l - 2)) :=
      Real.logb_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hlam)
    have hJ0 : 0 ≤ (Jbar G run l : ℝ) + 1 := by positivity
    calc 14 * ((Jbar G run l : ℝ) + 1) * n / (102 * logb 2 (run.lam G (l - 2))) ^ 2
        ≤ 14 * logb 2 (2 * (Aexp : ℝ) * logb 2 ((Aexp : ℝ) * logb 2 (run.lam G (l - 2)))) * n /
            (102 * logb 2 (run.lam G (l - 2))) ^ 2 := by gcongr
      _ = 14 / 10404 * n * etaCh (run.lam G (l - 2)) := by
          unfold etaCh; field_simp; ring
  -- the sum of the first terms
  have hS1 : ∑ l ∈ Finset.Icc 3 run.R, 307 * n / (run.M G l : ℝ) ≤ 614 * n / Dstar := by
    have hsum := (towerBM V G Dstar run hΓ.1 hV hd1).2
    have hsub : ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) ≤
        ∑ l ∈ Finset.Icc 1 run.R, (1 : ℝ) / (run.M G l : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl)
        (fun _ _ _ => by positivity)
    have e : ∑ l ∈ Finset.Icc 3 run.R, 307 * n / (run.M G l : ℝ) =
        307 * n * ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => by ring
    rw [e]
    have h307 : 0 ≤ 307 * n := by positivity
    calc 307 * n * ∑ l ∈ Finset.Icc 3 run.R, (1 : ℝ) / (run.M G l : ℝ)
        ≤ 307 * n * (2 / Dstar) := mul_le_mul_of_nonneg_left (hsub.trans hsum) h307
      _ = 614 * n / Dstar := by ring
  -- the sum of `η(λ_{l−2})`
  have hη0 : 0 ≤ etaCh (logb 2 Dstar) := etaCh_nonneg hΓ le_rfl
  have hS2 : ∑ l ∈ Finset.Icc 3 run.R, etaCh (run.lam G (l - 2)) ≤ 2 * etaCh (logb 2 Dstar) := by
    by_cases hR3 : 3 ≤ run.R
    · have hdom : ∀ l, 3 ≤ l → l ≤ run.R → logb 2 Dstar ≤ run.lam G (l - 2) := fun l h1 h2 =>
        logb_le_lam hΓ hV ⟨by omega, by omega⟩
      have hg := geom_sum (fun l => etaCh (run.lam G (l - 2))) 3
        (etaCh_nonneg hΓ (hdom 3 le_rfl hR3)) run.R hR3 (by
          intro l hl hlR
          show etaCh (run.lam G (l - 2)) ≤ etaCh (run.lam G (l + 1 - 2)) / 2
          have hr : l - 2 ∈ Finset.Icc 1 run.R := Finset.mem_Icc.2 ⟨by omega, by omega⟩
          have hTA := (towerA V G Dstar run hΓ.1 hV hd1).1 (l - 2) hr
          rw [show l - 2 + 1 = l - 1 by omega] at hTA
          rw [show l + 1 - 2 = l - 1 by omega]
          have hx : logb 2 Dstar ≤ run.lam G (l - 1) := logb_le_lam hΓ hV ⟨by omega, by omega⟩
          have hd0 : 0 < run.d G (l - 1) := by
            have := Run.Valid.dstar_le run G hV (l := l - 1) ⟨by omega, by omega⟩; linarith
          have hpow : run.d G (l - 1) ^ ((1 : ℝ) / (Aexp : ℝ)) =
              (2 : ℝ) ^ (run.lam G (l - 1) / (Aexp : ℝ)) := by
            show run.d G (l - 1) ^ ((1 : ℝ) / (Aexp : ℝ)) =
              (2 : ℝ) ^ (logb 2 (run.d G (l - 1)) / (Aexp : ℝ))
            conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hd0]
            rw [← Real.rpow_mul (by norm_num)]
            ring_nf
          rw [hpow] at hTA
          have hdom2 := logb_le_two_rpow_div hΓ hx
          exact (hEta.1 hdom2 (hdom2.trans hTA) hTA).trans (hEta.2 _ hx))
      refine hg.trans ?_
      show 2 * etaCh (run.lam G (run.R - 2)) ≤ _
      have := hEta.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (hdom run.R hR3 le_rfl))
        (hdom run.R hR3 le_rfl)
      linarith
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      linarith
  -- the total
  have hε : epsChain Dstar = 614 / Dstar + etaCh (logb 2 Dstar) / 371 := by
    simp only [epsChain, Chain.epsK, etaCh]
    ring
  rw [Finset.sum_add_distrib]
  calc _ ≤ ∑ l ∈ Finset.Icc 3 run.R, 307 * n / (run.M G l : ℝ) +
          ∑ l ∈ Finset.Icc 3 run.R, 14 / 10404 * n * etaCh (run.lam G (l - 2)) :=
        add_le_add (Finset.sum_le_sum hT1) (Finset.sum_le_sum hT2)
    _ = ∑ l ∈ Finset.Icc 3 run.R, 307 * n / (run.M G l : ℝ) +
          14 / 10404 * n * ∑ l ∈ Finset.Icc 3 run.R, etaCh (run.lam G (l - 2)) := by
        rw [Finset.mul_sum]
    _ ≤ 614 * n / Dstar + 14 / 10404 * n * (2 * etaCh (logb 2 Dstar)) :=
        add_le_add hS1 (mul_le_mul_of_nonneg_left hS2 (by positivity))
    _ ≤ epsChain Dstar * n := by
        rw [hε]
        have : 0 ≤ n * etaCh (logb 2 Dstar) := mul_nonneg hn hη0
        have e : (614 / Dstar + etaCh (logb 2 Dstar) / 371) * n =
            614 * n / Dstar + n * etaCh (logb 2 Dstar) / 371 := by ring
        rw [e]
        nlinarith

end EG
