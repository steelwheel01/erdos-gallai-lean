import EG.Proof.Gamma.Sat
import EG.Proof.Gamma.N0

/-! Unit GAMMA: full non-vacuity of the constants (manuscript s1:defConstants (ii), (iii),
s7:lemGammaSat).

* `N0Cond` is satisfiable (`EG.exists_N0`), and every large real `N_0` satisfies it;
* for every `N_0` some `D_*` satisfies Γ1–Γ4 (`EG.gammaSat`);
* jointly, `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` (`EG.exists_gammaCond`): the standing hypotheses
  of the main theorem are not vacuous. (`RunHyp` additionally needs a graph with a valid run and
  `d_1 ≥ D_*`; that is s2:propExists, not this unit.)
No `sorry`. -/

namespace EGTest.GammaFull

open EG Filter

example : ∃ N0 : ℝ, N0Cond N0 := exists_N0

example : ∀ᶠ N0 : ℝ in atTop, N0Cond N0 := eventually_N0Cond

example : ∀ᶠ N : ℕ in atTop, Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N :=
  Vortex.eventually_size

example : ∀ N0 : ℝ, ∃ D : ℝ, GammaCond N0 D := fun N0 => (gammaSat N0).exists

example : ∃ N0 D : ℝ, N0Cond N0 ∧ GammaCond N0 D := exists_gammaCond

-- the parts of `GammaCond` individually, at a common witness
example : ∃ N0 D : ℝ, N0Cond N0 ∧ Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D := by
  obtain ⟨N0, D, h0, h1, h2, h3, h4⟩ := exists_gammaCond
  exact ⟨N0, D, h0, h1, h2, h3, h4⟩

-- Γ1(f) holds on a ray: `col3 μ` for every `μ ≥ 2^{40}`
example (μ : ℝ) (h : (2 : ℝ) ^ 40 ≤ μ) : COLTable.col3 μ := COLTable.col3_of_le h

-- the three statements that stage 1 left open are now theorems
example : Spec.VortexEventuallySizeStatement := vortexEventuallySize
example : Spec.Col3EventuallyStatement := col3_eventually
example : Spec.GammaSatEpsStatement := gammaSat_eps
example : Spec.GammaSatItemsStatement := gammaSat_items

end EGTest.GammaFull
