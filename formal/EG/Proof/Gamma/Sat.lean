module

public import EG.Spec.Gamma.Sat
public import EG.Spec.Gamma.N0
public import EG.Lib.Gamma.Full
public import EG.Lib.Gamma.Col3
public import EG.Lib.Gamma.Eps
public import EG.Proof.Gamma.N0

/-!
# The galactic conditions are satisfiable (manuscript s7:lemGammaSat): reductions

Unit GAMMA, design note `formal/work/p2b/GAMMA.md`. Stage 1 of the unit: the structure of the
proof of Lemma [s7:lemGammaSat], as reductions between the statements of
`EG/Spec/Gamma/Sat.lean`:
* (i) from [s3:lemCOLJVev] (iii) and the eventuality of items (a)–(e)
  (`EG.eventually_gamma1Items`, already proved): `gammaSatItems_of_col3`;
* (iii) from (i) and (ii): `gammaSat_of_items_eps` (the proof's `D_0 = max(D_1, 2^{117},
  2^{(2N_0)^{1/C'}}, D'')`, with Γ2(a) derived from Γ1 and every threshold an eventuality);
* the existence of `N_0` and `D_*` from (iii) and the existence of `N_0`:
  `gammaCondExists_of`.
The remaining inputs are proved in the Lib (they are not declared inputs):
[s3:lemCOLJVev] (iii) (`Spec.Col3EventuallyStatement`, `EG.COLTable.eventually_col3` in
`EG/Lib/Gamma/Col3.lean`), (ii) (`Spec.GammaSatEpsStatement`, `EG.Quot.tendsto_eps1`,
`EG.Quot.tendsto_eps2` in `EG/Lib/Gamma/Eps.lean`) and the size eventuality
(`Spec.VortexEventuallySizeStatement`, `EG.Vortex.eventually_size`). The final theorems are
`EG.col3_eventually`, `EG.gammaSat_items`, `EG.gammaSat_eps`, `EG.gammaSat` and
`EG.exists_gammaCond`. No `sorry`.
-/

public section

namespace EG

open Filter Topology Real

/-- [s7:lemGammaSat] (i), proof: "item (f) holds for all sufficiently large `μ` by
Lemma s3:lemCOLJVev(iii). So each of the finitely many inequalities of Γ1 holds for all `μ` at
least some threshold; let `μ_1 ≥ 1` be at least all of these thresholds. If `D_* > 2` and
`log₂log₂D_* ≥ μ_1`, every `μ ≥ log₂log₂D_*` satisfies `μ ≥ μ_1`, so Γ1 holds." -/
theorem gammaSatItems_of_col3 (h : Spec.Col3EventuallyStatement) :
    Spec.GammaSatItemsStatement := by
  have e : ∀ᶠ μ : ℝ in atTop, Gamma1Items μ ∧ COLTable.col3 μ := eventually_gamma1Items.and h
  refine ⟨e, ?_⟩
  obtain ⟨μ0, hμ0⟩ := eventually_atTop.1 e
  refine ⟨max 1 μ0, le_max_left _ _, fun μ hμ => hμ0 μ ((le_max_right _ _).trans hμ), ?_⟩
  intro D hD hμ1
  have key : ∀ μ, logb 2 (logb 2 D) ≤ μ → Gamma1Items μ ∧ COLTable.col3 μ :=
    fun μ hμ => hμ0 μ ((le_max_right _ _).trans (hμ1.trans hμ))
  exact ⟨⟨hD, fun μ hμ => (key μ hμ).1⟩, fun μ hμ => (key μ hμ).2⟩

/-- `log₂ log₂ D → ∞` as `D → ∞`. -/
theorem tendsto_logb_logb_atTop :
    Tendsto (fun D : ℝ => logb 2 (logb 2 D)) atTop atTop :=
  (Real.tendsto_logb_atTop (by norm_num)).comp (Real.tendsto_logb_atTop (by norm_num))

/-- [s7:lemGammaSat] (iii), proof: "By (i), Γ1 holds for every `D_* ≥ D_1`, since then
`log₂log₂D_* ≥ μ_1`. Γ2(a) holds for every `D_* ≥ 2^{117}`, and Γ2(b),(c) are implied by Γ1.
Γ3 holds for every `D_* ≥ 2^{(2N_0)^{1/C'}}`; here `N_0` is fixed before `D_*`. By (ii) there is
`D''` with `ε_1(D_*) ≤ 6` and `ε_2(D_*) ≤ 1/4` for all `D_* ≥ D''`, which is Γ4." -/
theorem gammaSat_of_items_eps (hi : Spec.GammaSatItemsStatement)
    (he : Spec.GammaSatEpsStatement) : Spec.GammaSatStatement := by
  intro N0
  obtain ⟨μ1, -, -, hΓ1⟩ := hi.2
  have h1 : ∀ᶠ D : ℝ in atTop, Gamma1 D := by
    filter_upwards [eventually_gt_atTop 2,
      tendsto_logb_logb_atTop.eventually (eventually_ge_atTop μ1)] with D hD hμ
    exact hΓ1 D hD hμ
  have h3 : ∀ᶠ D : ℝ in atTop, Gamma3 N0 D :=
    ((tendsto_pow_atTop (by norm_num [Cp])).comp
      (Real.tendsto_logb_atTop (by norm_num))).eventually (eventually_ge_atTop (2 * N0))
  have h4 : ∀ᶠ D : ℝ in atTop, Gamma4 D := by
    filter_upwards [he.1.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 6)),
      he.2.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with D a b
    exact ⟨a, b⟩
  filter_upwards [h1, h3, h4] with D a b c
  exact GammaCond.of_gamma134 a b c

/-- [s7:lemGammaSat] "In particular a constant `D_*` as in Definition s1:defConstants(iii)
exists", for an `N_0` as in s1:defConstants (ii). -/
theorem gammaCondExists_of (hN : Spec.N0ExistsStatement) (h : Spec.GammaSatStatement) :
    Spec.GammaCondExistsStatement := by
  obtain ⟨N0, hN0⟩ := hN
  obtain ⟨D, hD⟩ := (h N0).exists
  exact ⟨N0, D, hN0, hD⟩

/-- [s3:lemCOLJVev] (iii) "Consequently, for each row of Table s3:tabCOLJV, every inequality in
column 3 holds at `λ = 2^μ` for all sufficiently large real `μ`." -/
theorem col3_eventually : Spec.Col3EventuallyStatement := COLTable.eventually_col3

/-- [s7:lemGammaSat] (i) "each item (a)–(f) of Γ1 holds for all sufficiently large real `μ`;
hence there is `μ_1 ≥ 1` such that all of them hold for every `μ ≥ μ_1`, and Γ1 holds for every
`D_* > 2` with `log₂log₂D_* ≥ μ_1`". -/
theorem gammaSat_items : Spec.GammaSatItemsStatement := gammaSatItems_of_col3 col3_eventually

/-- [s7:lemGammaSat] (ii) "`ε_1(D_*) → 0` and `ε_2(D_*) → 0` as `D_* → ∞`". -/
theorem gammaSat_eps : Spec.GammaSatEpsStatement := ⟨Quot.tendsto_eps1, Quot.tendsto_eps2⟩

/-- [s7:lemGammaSat] (iii) "there is `D_0` such that every `D_* ≥ D_0` satisfies Γ1–Γ4
simultaneously" (for every real `N_0`). -/
theorem gammaSat : Spec.GammaSatStatement := gammaSat_of_items_eps gammaSat_items gammaSat_eps

/-- [s7:lemGammaSat] "In particular a constant `D_*` as in Definition s1:defConstants(iii)
exists", with [s1:defConstants] (ii) "So such an `N_0` exists": the standing hypotheses
`N0Cond N0 ∧ GammaCond N0 D` of the main theorem are satisfiable. -/
theorem exists_gammaCond : Spec.GammaCondExistsStatement := gammaCondExists_of exists_N0 gammaSat

end EG
