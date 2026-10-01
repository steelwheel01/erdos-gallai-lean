import EGTest.HB
import EG.Spec.HB.Origin
import EG.Spec.HB.TowerA
import EG.Spec.HB.OVRunK
import EG.Spec.HB.LacunaryGeom
import EG.Spec.Chain.ConcTower
import EG.Spec.Chain.CONC
import EG.Spec.Chain.CONCL
import EG.Lib.Found.Gamma
import EG.Lib.Found.Log

/-! Non-vacuity checks for the statements of probe unit P3B (probe P-3, part 2; design note
`formal/work/p2b/P3B.md`): the hypotheses of the statements in
`EG/Spec/HB/{Origin, TowerA, OVRunK, LacunaryGeom}.lean` and
`EG/Spec/Chain/{ConcTower, CONC, CONCL}.lean` are satisfiable on small instances, reusing the
valid run `run1` on `K3` of `EGTest.HB` (one round, three one-vertex pre-parts `{0}`, `{1}`,
`{2}`, all light, `D_1 = Dup*_1 = ∅`):
* `OriginTypesStatement` etc.: `run1` is valid, round `1 ∈ [1,R]`, pre-part `[false]`, and
  `0 ∈ Y^0 \ Dup*_1`;
* CONC (i)–(ii), CONC-L (i)–(iii), the per-ancestor bound: every function `δ` is a designation of
  `run1` (`R = 1`, so there are no standalone pre-parts of rounds `l ≥ 3`), and `[false]` is a
  light part of round `1`;
* the Γ-statements (CONC (iii), the two shared sums, CONC-L (iv), the tower facts): `Gamma1core D`,
  a valid run and a designation are jointly satisfiable (the run without rounds on `E2`; a run with
  a round under Γ1 needs `d_1 ≥ D_* ≥ 2^{2^{256}}` and is not built);
* `TowerEndStatement`: `Gamma1core D` and `D ≤ d` (take `d = D`);
* `LacunaryGeomStatement`: the hypotheses hold for `X_r = 2^r`, `R = 3` (with equality in the
  halving condition);
* parse checks (`rfl`) of the new probe Defs `towA`, `towB`, `towC`, `OriginBeta`,
  `OriginAlpha`, and one value: `𝖺(𝖳_2) = 𝖺(4) = 3`.
No valid run with a type-(β) edge, a guest or a standalone pre-part of a round `r` with a class
round `l ≥ r + 2` exists at toy size (a `τ`-run split needs a non-`(ε, s_r)`-expander with
`s_r ≥ 40^{100}`, and a class needs `R ≥ 3`); the conclusions are therefore exercised only in
degenerate form (design note, "Non-vacuity"). -/

namespace EGTest.ProbeP3B

open EG EG.HB EG.Chain EGTest.HB

/-! ## ORIGIN^τ: the hypotheses are satisfiable on `run1` -/

theorem hr1 : run1.IsRound 1 := ⟨le_rfl, le_rfl⟩

/-- `Dup*_1 = ∅` for `run1`: the three leaves of the two-level recursion are disjoint. -/
theorem DupStar_run1 : run1.DupStar K3 1 = ∅ := by
  rw [Run.DupStar, if_pos hr1, Run.graph_one]
  change (Round.twoLevel K3 c1).dup (Round.graph' K3 c1) = ∅
  rw [twoLevel_eq]
  decide

theorem prePartAddrs_run1 : run1.prePartAddrs K3 1 = {[false], [true, false], [true, true]} := by
  rw [Run.prePartAddrs_of_isRound run1 K3 hr1, Run.graph_one]
  exact prePartAddrs_eq.trans tree0_leafAddrs

theorem Z0_run1_F : run1.Z0 K3 1 [false] = {0} := by
  change Round.Z0 (run1.graph K3 1) (run1.choice 1) [false] = {0}
  rw [Run.graph_one]
  change Round.Z0 K3 c1 [false] = {0}
  rw [Z0_eq, verts_F]

/-- **Non-vacuity of `OriginTypesStatement`, `OriginThinStatement`,
`OriginGuestCapStatement`** (hypotheses): a valid run, a round `r ∈ [1,R]`, a round-`r` pre-part
`Y` and a vertex `u ∈ Y^0 \ Dup*_r`. -/
example : run1.Valid K3 1 ∧ 1 ∈ Finset.Icc 1 run1.R ∧ [false] ∈ run1.prePartAddrs K3 1 ∧
    (0 : Fin 3) ∈ run1.Z0 K3 1 [false] \ run1.DupStar K3 1 := by
  refine ⟨run1_valid, by decide, ?_, ?_⟩
  · rw [prePartAddrs_run1]; decide
  · rw [Z0_run1_F, DupStar_run1]; decide

/-- The pre-part `[false]` of `run1` is light, and its piece is itself (a big piece whose
`τ`-run is a single leaf). -/
theorem isLight_run1 (a : Addr) : run1.isLight K3 1 a := by
  change Round.isLight (run1.graph K3 1) (run1.choice 1) a
  rw [Run.graph_one]
  exact isLight_c1 a

example : run1.pieceOf 1 [false] = [false] := rfl

/-- `OriginAlpha` requires lightness (parse check of the probe Def). -/
example (u x : Fin 3) : run1.OriginAlpha K3 1 [false] u x ↔
    run1.isLight K3 1 [false] ∧ x ∈ run1.guests K3 1 [false] ∧
      s(u, x) ∈ (run1.X0 K3 1 [false]).edges := Iff.rfl

/-- `OriginBeta` (parse check of the probe Def). -/
example (u x : Fin 3) : run1.OriginBeta K3 1 [false] u x ↔
    x ∉ run1.Z0 K3 1 [false] ∧ s(u, x) ∈ (run1.tauRun 1 [false]).deleted
      (run1.piece K3 1 [false]) := Iff.rfl

/-! ## CONC (i)–(ii), CONC-L (i)–(iii), per-ancestor bound: designations of `run1` -/

/-- Every function is a designation of `run1` (no standalone pre-part of a round `l ≥ 3`). -/
theorem isDesignation_run1 (δ : Designation (Fin 3)) : IsDesignation run1 K3 δ := by
  intro l hl a ha
  have hnot : ¬ run1.IsRound l := by
    rintro ⟨-, h⟩
    have : run1.R = 1 := rfl
    omega
  have : run1.Std K3 l = ∅ := by
    simp [Run.Std, Run.prePartAddrs_of_not_isRound run1 K3 hnot]
  rw [this] at ha
  simp at ha

/-- **Non-vacuity of `ConcLIStatement` … `ConcLIIIStatement`, `ConcLPerAncestorStatement`**
(hypotheses): a valid run, a designation, a light part `[false]` of round `1`, and `l = 2 ≥ 1 + 1`;
`(1, [false])` is an ancestor. -/
example : run1.Valid K3 1 ∧ IsDesignation run1 K3 (fun _ _ => (1, [false])) ∧
    [false] ∈ run1.prePartAddrs K3 1 ∧ run1.isLight K3 1 [false] ∧ 1 + 1 ≤ 2 ∧
    ((1 : ℕ), ([false] : Addr)) ∈ run1.ancestors K3 := by
  refine ⟨run1_valid, isDesignation_run1 _, ?_, isLight_run1 _, le_rfl, ?_⟩
  · rw [prePartAddrs_run1]; decide
  · rw [Run.mem_ancestors, prePartAddrs_run1]; decide

/-! ## The Γ-statements: `Gamma1core`, a valid run and a designation are jointly satisfiable -/

/-- **Non-vacuity of `ConcIIIStatement`, `ConcTauSumStatement`, `ConcDStarSumStatement`,
`ConcLAlphaStatement`, `ConcLGCSumStatement`, `ConcLSumStatement`, `TowerHalfStatement`**
(hypotheses): the run without rounds on `E2`, with any `D` satisfying `Gamma1core` and any
designation. -/
example : ∃ D : ℝ, Gamma1core D ∧ (⟨[]⟩ : Run (Fin 2)).Valid E2 D ∧
    IsDesignation (⟨[]⟩ : Run (Fin 2)) E2 (fun _ _ => (0, [])) := by
  obtain ⟨D, hD⟩ := exists_gamma1core
  refine ⟨D, hD, (Run.valid_nil_iff E2 D).2 ?_, ?_⟩
  · have hE : E2.edges = ∅ := by decide
    have h2 : (2 : ℝ) < D := hD.1
    simp only [Round.d, hE, Finset.card_empty, Nat.cast_zero, mul_zero, zero_div]
    linarith
  · intro l hl a ha
    have hnot : ¬ (⟨[]⟩ : Run (Fin 2)).IsRound l := by
      rintro ⟨h1, h2⟩
      have : (⟨[]⟩ : Run (Fin 2)).R = 0 := rfl
      omega
    have : (⟨[]⟩ : Run (Fin 2)).Std E2 l = ∅ := by
      simp [Run.Std, Run.prePartAddrs_of_not_isRound _ E2 hnot]
    rw [this] at ha
    simp at ha

/-- **Non-vacuity of `TowerEndStatement`, `KStarStatement`** (hypotheses). -/
example : ∃ D d : ℝ, Gamma1core D ∧ D ≤ d := by
  obtain ⟨D, hD⟩ := exists_gamma1core
  exact ⟨D, D, hD, le_rfl⟩

/-! ## `LacunaryGeomStatement`: the hypotheses hold for a doubling sequence -/

/-- **Non-vacuity of `LacunaryGeomStatement`** (hypotheses): `X_r = 2^r`, `R = 3`. -/
example : 1 ≤ 3 ∧ (∀ r ∈ Finset.Icc 1 3, (0 : ℝ) ≤ 2 ^ r) ∧
    (∀ r ∈ Finset.Ico 1 3, (2 : ℝ) ^ r ≤ 2 ^ (r + 1) / 2) := by
  refine ⟨by norm_num, fun r _ => by positivity, fun r _ => ?_⟩
  rw [pow_succ]
  linarith

/-! ## The tower functions (parse checks) -/

example (d : ℝ) : towA d = (2 * (logStar d : ℝ) + 2) / Real.logb 2 d := rfl
example (d : ℝ) : towB d = (2 * (logStar d : ℝ) + 1) / Real.logb 2 (Real.logb 2 d) := rfl
example (d : ℝ) : towC d = (2 * (logStar d : ℝ) + 1) / Real.logb 2 d ^ ((1 : ℝ) / 2) := rfl

/-- `𝖺(𝖳_2) = 3`: `𝖳_2 = 4`, `log* 4 = 2`, `log 4 = 2`. -/
example : towA (tower 2) = 3 := by
  have h1 : tower 1 = 2 := by simp [tower]
  rw [towA, logStar_tower, show tower 2 = tower (1 + 1) from rfl, logb_tower_succ, h1]
  norm_num

/-- The value of `ε_CONC` is the displayed formula (parse check against `EG.Chain.epsCONC`). -/
example (D : ℝ) : epsCONC D = (2 : ℝ) ^ (sigmaC + 15) * (logStar D : ℝ) / Real.logb 2 D
    + 200 * epsC * (logStar D : ℝ) / ((Cp : ℝ) * Real.logb 2 (Real.logb 2 D))
    + 4 * (2 * (logStar D : ℝ) + 2) / Real.logb 2 D ^ ((1 : ℝ) / 2) := rfl

/-! ## Sign checks of the right-hand sides under Γ1 (fix round 1, review M1)

The Γ-statements are exercised above only by a run with `R = 0` (empty sums; a run with `R ≥ 1`
under Γ1 needs `d_1 ≥ 2^{2^{256}}`). The checks below show that each bound's right-hand side is
positive under `Gamma1core D` for `n ≥ 1` (and the tower functions are positive for `d ≥ D`), which
rules out a sign or constant typo that would make a bound false for every non-empty run. -/

/-- Under Γ1: `log D > 0`, `log log D > 0`, `log* D ≥ 1`. -/
theorem gamma_pos {D : ℝ} (hD : Gamma1core D) :
    0 < Real.logb 2 D ∧ 0 < Real.logb 2 (Real.logb 2 D) ∧ (1 : ℝ) ≤ (logStar D : ℝ) := by
  refine ⟨by linarith [hD.one_lt_logb], ?_, ?_⟩
  · have h8 := hD.two_pow_eight_le_loglog
    have : (0 : ℝ) < 2 ^ 8 := by norm_num
    linarith
  · have h1 : (1 : ℝ) < D := by linarith [hD.two_lt]
    have hne : logStar D ≠ 0 := by
      rw [Ne, logStar_eq_zero_iff]
      linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne

theorem epsC_pos : (0 : ℝ) < epsC := by unfold epsC; positivity

theorem Cp_pos : (0 : ℝ) < (Cp : ℝ) := by unfold Cp; norm_num

/-- `ConcTauSumStatement`: its right-hand side `2^{σ+14} n log* D/log D` is positive. -/
example {D n : ℝ} (hD : Gamma1core D) (hn : 0 < n) :
    0 < (2 : ℝ) ^ (sigmaC + 14) * n * (logStar D : ℝ) / Real.logb 2 D := by
  obtain ⟨h1, -, h3⟩ := gamma_pos hD
  have hk : (0 : ℝ) < logStar D := by linarith
  exact div_pos (mul_pos (mul_pos (by positivity) hn) hk) h1

/-- `ConcDStarSumStatement`: its right-hand side `80 ε n log* D/(C' log log D)` is positive. -/
example {D n : ℝ} (hD : Gamma1core D) (hn : 0 < n) :
    0 < 80 * epsC * n * (logStar D : ℝ) / ((Cp : ℝ) * Real.logb 2 (Real.logb 2 D)) := by
  obtain ⟨-, h2, h3⟩ := gamma_pos hD
  have hk : (0 : ℝ) < logStar D := by linarith
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) epsC_pos) hn) hk) (mul_pos Cp_pos h2)

/-- `ConcIIIStatement`: its right-hand side is positive. -/
example {D n : ℝ} (hD : Gamma1core D) (hn : 0 < n) :
    0 < (2 : ℝ) ^ (sigmaC + 14) * n * (logStar D : ℝ) / Real.logb 2 D +
      100 * epsC * n * (logStar D : ℝ) / ((Cp : ℝ) * Real.logb 2 (Real.logb 2 D)) := by
  obtain ⟨h1, h2, h3⟩ := gamma_pos hD
  have hk : (0 : ℝ) < logStar D := by linarith
  exact add_pos (div_pos (mul_pos (mul_pos (by positivity) hn) hk) h1)
    (div_pos (mul_pos (mul_pos (mul_pos (by norm_num) epsC_pos) hn) hk) (mul_pos Cp_pos h2))

/-- `ConcLGCSumStatement`: its right-hand side `4n(2 log* D + 2)/(log D)^{1/2}` is positive. -/
example {D n : ℝ} (hD : Gamma1core D) (hn : 0 < n) :
    0 < 4 * n * (2 * (logStar D : ℝ) + 2) / Real.logb 2 D ^ ((1 : ℝ) / 2) := by
  obtain ⟨h1, -, h3⟩ := gamma_pos hD
  exact div_pos (mul_pos (mul_pos (by norm_num) hn) (by linarith))
    (Real.rpow_pos_of_pos h1 _)

/-- `ConcLSumStatement`: `ε_CONC(D) > 0`, so its right-hand side `ε_CONC(D) n` is positive. -/
theorem epsCONC_pos {D : ℝ} (hD : Gamma1core D) : 0 < epsCONC D := by
  obtain ⟨h1, h2, h3⟩ := gamma_pos hD
  have hk : (0 : ℝ) < logStar D := by linarith
  unfold epsCONC
  refine add_pos (add_pos (div_pos (mul_pos (by positivity) hk) h1)
    (div_pos (mul_pos (mul_pos (by norm_num) epsC_pos) hk) (mul_pos Cp_pos h2))) ?_
  exact div_pos (mul_pos (by norm_num) (by linarith)) (Real.rpow_pos_of_pos h1 _)

example {D n : ℝ} (hD : Gamma1core D) (hn : 0 < n) : 0 < epsCONC D * n :=
  mul_pos (epsCONC_pos hD) hn

/-- `TowerHalfStatement`, `TowerEndStatement`: the tower functions are positive at every
`d ≥ D`, and so are the right-hand sides of `TowerEndStatement`. -/
example {D d : ℝ} (hD : Gamma1core D) (hd : D ≤ d) :
    0 < towA d ∧ 0 < towB d ∧ 0 < towC d ∧
      0 < (2 * (logStar D : ℝ) + 4) / Real.logb 2 D ∧
      0 < (2 * (logStar D : ℝ) + 3) / Real.logb 2 (Real.logb 2 D) ∧
      0 < (2 * (logStar D : ℝ) + 3) / Real.logb 2 D ^ ((1 : ℝ) / 2) := by
  obtain ⟨h1, h2, h3⟩ := gamma_pos hD
  obtain ⟨g1, g2, g3⟩ := gamma_pos (hD.mono hd)
  refine ⟨div_pos (by linarith) g1, div_pos (by linarith) g2,
    div_pos (by linarith) (Real.rpow_pos_of_pos g1 _), div_pos (by linarith) h1,
    div_pos (by linarith) h2, div_pos (by linarith) (Real.rpow_pos_of_pos h1 _)⟩

end EGTest.ProbeP3B
