module

public import EG.Defs.Main.GammaCond
public import EG.Lib.Found.Gamma

/-!
# API for `Gamma1`, `Gamma1f`, `N0Cond`, `Gamma3`, `RunHyp` and `GammaCond` (manuscript s1:condGamma)

Elementary lemmas about the definitions of `EG/Defs/Gamma/Full.lean` and
`EG/Defs/Main/GammaCond.lean` (unit GAMMA, design note `formal/work/p2b/GAMMA.md`).

* access: `Gamma1.core`, `Gamma1.f`, `Gamma1.two_lt`, `Gamma1.col3`, `Gamma1.items`;
  `N0Cond.two_pow_forty_le`, `N0Cond.size`, `N0Cond.tpv`, `N0Cond.pv`, `N0Cond.vx`;
  `GammaCond.gamma1`, `.gamma2a`, `.gamma3`, `.gamma4`, `.gamma1core`; the projections of
  `RunHyp`;
* [s1:condG1] "So Γ1 is upward closed in `D_*`": `Gamma1f.mono`, `Gamma1.mono`;
  [s1:condG2] "(a) is immediate from Γ1": `Gamma1.gamma2a`;
* [s1:tabOrder] "(so every requirement is upward closed in `N_0`)": `N0Cond.mono`;
  Γ3 is a lower bound on `D_*` (`Gamma3.mono`) and an upper bound on `N_0` (`Gamma3.anti`);
* the standing hypotheses of s5–s7: `RunHyp.gamma2a` (derived, TRIAGE §2.6),
  `RunHyp.gammaCond` (`RunHyp` and Γ4 give Γ1–Γ4).
-/

public section

namespace EG

open Real

/-! ### Γ1 -/

theorem Gamma1.core {D : ℝ} (h : Gamma1 D) : Gamma1core D := h.1

theorem Gamma1.f {D : ℝ} (h : Gamma1 D) : Gamma1f D := h.2

theorem Gamma1.two_lt {D : ℝ} (h : Gamma1 D) : 2 < D := h.1.1

theorem Gamma1.items {D μ : ℝ} (h : Gamma1 D) (hμ : logb 2 (logb 2 D) ≤ μ) :
    Gamma1Items μ := h.1.items hμ

theorem Gamma1.col3 {D μ : ℝ} (h : Gamma1 D) (hμ : logb 2 (logb 2 D) ≤ μ) :
    COLTable.col3 μ := h.2 μ hμ

/-- [s1:condG1] upward closure of item (f) (for `D > 2`). -/
theorem Gamma1f.mono {D D' : ℝ} (h : Gamma1f D) (hD2 : 2 < D) (hD : D ≤ D') : Gamma1f D' :=
  fun _ hμ => h _ ((loglog_mono hD2 hD).trans hμ)

/-- [s1:condG1] "So Γ1 is upward closed in `D_*`." -/
theorem Gamma1.mono {D D' : ℝ} (h : Gamma1 D) (hD : D ≤ D') : Gamma1 D' :=
  ⟨h.1.mono hD, h.2.mono h.two_lt hD⟩

/-- [s1:condG2] "(a) is immediate from Γ1". -/
theorem Gamma1.gamma2a {D : ℝ} (h : Gamma1 D) : Gamma2a D := h.1.gamma2a

/-! ### `N_0` -/

theorem N0Cond.two_pow_forty_le {N0 : ℝ} (h : N0Cond N0) : (2 : ℝ) ^ 40 ≤ N0 := h.1

theorem N0Cond.size {N0 : ℝ} (h : N0Cond N0) {N : ℕ} (hN : N0 ≤ (N : ℝ)) :
    Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N := h.2 N hN

theorem N0Cond.tpv {N0 : ℝ} (h : N0Cond N0) {N : ℕ} (hN : N0 ≤ (N : ℝ)) :
    Vortex.TPVSize N := (h.size hN).1

theorem N0Cond.pv {N0 : ℝ} (h : N0Cond N0) {N : ℕ} (hN : N0 ≤ (N : ℝ)) :
    Vortex.PVSize N := (h.size hN).2.1

theorem N0Cond.vx {N0 : ℝ} (h : N0Cond N0) {N : ℕ} (hN : N0 ≤ (N : ℝ)) :
    Vortex.VXSize N := (h.size hN).2.2

theorem N0Cond.pos {N0 : ℝ} (h : N0Cond N0) : 0 < N0 :=
  lt_of_lt_of_le (by norm_num) h.1

/-- [s1:tabOrder] "`N`, so every requirement is upward closed in `N_0`". -/
theorem N0Cond.mono {N0 N0' : ℝ} (h : N0Cond N0) (hN : N0 ≤ N0') : N0Cond N0' :=
  ⟨h.1.trans hN, fun N hN' => h.2 N (hN.trans hN')⟩

/-! ### Γ3 -/

/-- Γ3 is a lower bound on `D_*` (for `D_* ≥ 1`, where `log₂ D_* ≥ 0`). -/
theorem Gamma3.mono {N0 D D' : ℝ} (h : Gamma3 N0 D) (hD1 : 1 ≤ D) (hD : D ≤ D') :
    Gamma3 N0 D' := by
  unfold Gamma3 at *
  refine h.trans (pow_le_pow_left₀ (Real.logb_nonneg (by norm_num) hD1) ?_ _)
  exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hD

/-- Γ3 is an upper bound on `N_0`. -/
theorem Gamma3.anti {N0 N0' D : ℝ} (h : Gamma3 N0 D) (hN : N0' ≤ N0) : Gamma3 N0' D := by
  unfold Gamma3 at *
  linarith

/-! ### Γ1–Γ4 -/

theorem GammaCond.gamma1 {N0 D : ℝ} (h : GammaCond N0 D) : Gamma1 D := h.1
theorem GammaCond.gamma2a {N0 D : ℝ} (h : GammaCond N0 D) : Gamma2a D := h.2.1
theorem GammaCond.gamma3 {N0 D : ℝ} (h : GammaCond N0 D) : Gamma3 N0 D := h.2.2.1
theorem GammaCond.gamma4 {N0 D : ℝ} (h : GammaCond N0 D) : Gamma4 D := h.2.2.2
theorem GammaCond.gamma1core {N0 D : ℝ} (h : GammaCond N0 D) : Gamma1core D := h.1.1

/-- `GammaCond` from Γ1, Γ3 and Γ4 (Γ2(a) is derived from Γ1). -/
theorem GammaCond.of_gamma134 {N0 D : ℝ} (h1 : Gamma1 D) (h3 : Gamma3 N0 D) (h4 : Gamma4 D) :
    GammaCond N0 D :=
  ⟨h1, h1.gamma2a, h3, h4⟩

/-! ### The standing hypotheses of s5–s7 -/

section RunHyp

variable {V : Type*} [DecidableEq V] {N0 D : ℝ} {G : FGraph V} {run : HB.Run V}

theorem RunHyp.gamma1 (h : RunHyp N0 D G run) : Gamma1 D := h.1
theorem RunHyp.gamma1core (h : RunHyp N0 D G run) : Gamma1core D := h.1.1
theorem RunHyp.gamma3 (h : RunHyp N0 D G run) : Gamma3 N0 D := h.2.1
theorem RunHyp.n0Cond (h : RunHyp N0 D G run) : N0Cond N0 := h.2.2.1
theorem RunHyp.n0_le_card (h : RunHyp N0 D G run) : N0 ≤ (G.card : ℝ) := h.2.2.2.1
theorem RunHyp.le_d_one (h : RunHyp N0 D G run) : D ≤ run.d G 1 := h.2.2.2.2.1
theorem RunHyp.valid (h : RunHyp N0 D G run) : run.Valid G D := h.2.2.2.2.2

/-- TRIAGE §2.6 "`Gamma2a` is derived". -/
theorem RunHyp.gamma2a (h : RunHyp N0 D G run) : Gamma2a D := h.gamma1.gamma2a

/-- The setting of s5 and s7 ("`D_*` satisfies Γ1–Γ4"): `RunHyp` together with Γ4. -/
theorem RunHyp.gammaCond (h : RunHyp N0 D G run) (h4 : Gamma4 D) : GammaCond N0 D :=
  GammaCond.of_gamma134 h.gamma1 h.gamma3 h4

/-- `RunHyp` from its parts, with the hypotheses in the order of the setting of s5
("`G` is a graph on `n ≥ N_0` vertices with `d_1 ≥ D_*`; `D_*` satisfies Γ1–Γ4; a valid `HB^tp`
run on `G` is fixed"), for `N_0` as in s1:defConstants (ii). -/
theorem RunHyp.of_gammaCond (hN : N0Cond N0) (hG : GammaCond N0 D) (hn : N0 ≤ (G.card : ℝ))
    (hd : D ≤ run.d G 1) (hv : run.Valid G D) : RunHyp N0 D G run :=
  ⟨hG.gamma1, hG.gamma3, hN, hn, hd, hv⟩

end RunHyp

end EG
