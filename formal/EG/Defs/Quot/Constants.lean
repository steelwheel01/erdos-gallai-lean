module

public import EG.Defs.Quot.Cand
public import EG.Defs.Chain.Constants
public import EG.Defs.Light.Constants

/-!
# The small functions of s7: `ε_X`, `det_l`, `F`, `ε_2 = θ_Q`, `ε_1`, `C_0`

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s7.tex`: Lemma [s7:lemEXprime] (`ε_X`), Lemma [s7:lemUHsplit] (`det_l`, `F`,
`ε_2`, `θ_Q`), Proposition [s7:propCost] (`ε_1`, `C_0`), quoted below; `s1.tex`,
Definition [s1:defConstants] (iv), (v). Design note: `formal/work/p2d/quot.md`. Namespace
`EG.Quot`; TRIAGE §2.4 ("ε-functions are Defs with exactly the formulas of the defining
statements; the Γ4 bullet list is descriptive only"), §3 item 33.

Names of the other small functions: `ε_A = EG.HB.epsA`, `ε_U = EG.Light.epsU`,
`ε_K = EG.Chain.epsK` (`= EG.Light.epsChain` by `rfl`), `ε_CONC = EG.Chain.epsCONC`. `log = log₂`
(`Real.logb 2`); `x^{-90.2}` is `Real.rpow`; decimal literals are exact rationals.
-/

@[expose] public section

namespace EG.Quot

open EG.HB

/-- [s7:lemEXprime] "`ε_X(D_*) := ε_U(D_*) + 10.3/D_* + 2.1 (6 log₂ D_* + 12)/D_*`". -/
noncomputable def epsX (Dstar : ℝ) : ℝ :=
  Light.epsU Dstar + 10.3 / Dstar + 2.1 * (6 * Real.logb 2 Dstar + 12) / Dstar

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V)

/-- [s7:lemUHsplit] "For `3 ≤ l ≤ R` put
`det_l := 3|D_l| + 78 nM_l/Hcd_l + 30 n/M_l + 320 nM_l^3(log₂ θ^ult_l + 8)/λ_{l-2}^{95}`, a
deterministic function of the run" (`n = |V(G)|`). -/
noncomputable def detl (l : ℕ) : ℝ :=
  3 * ((run.D G l).card : ℝ) + 78 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l +
    30 * (G.card : ℝ) / (run.M G l : ℝ) +
    320 * (G.card : ℝ) * (run.M G l : ℝ) ^ 3 * (Real.logb 2 (thult run G l : ℝ) + 8) /
      run.lam G (l - 2) ^ 95

/-- [s7:lemUHsplit] (iv) "Put `F(x) := (3184 + 30400 log₂ x) x^{-90.2}` for `x ≥ 1`" (total in
`x`). -/
noncomputable def FQ (x : ℝ) : ℝ := (3184 + 30400 * Real.logb 2 x) * x ^ (-(90.2 : ℝ))

/-- [s7:lemUHsplit] (iv) "`θ_Q := ε_2(D_*) := 12 ε_X(D_*) + 4(3ε_A + 60/D_* + 2F(log₂ D_*))`, with
`ε_A = 31ε/(C' log log D_*)` as in Lemma [s2:lemTower] (e)". -/
noncomputable def eps2 (Dstar : ℝ) : ℝ :=
  12 * epsX Dstar + 4 * (3 * epsA Dstar + 60 / Dstar + 2 * FQ (Real.logb 2 Dstar))

/-- [s1:defConstants] (iv) "`θ_Q := ε_2(D_*)`". -/
noncomputable def thetaQ (Dstar : ℝ) : ℝ := eps2 Dstar

/-- [s7:propCost] "`ε_1(D_*) := ε_K(D_*) + 169 ε_A + 252/D_* + 1.5 ε_CONC(D_*) + 3 ε_X(D_*) +
9/D_*`, with `ε_A = 31ε/(C' log log D_*)` as in Lemma [s2:lemTower] (e)." -/
noncomputable def eps1 (Dstar : ℝ) : ℝ :=
  Chain.epsK Dstar + 169 * epsA Dstar + 252 / Dstar + 1.5 * Chain.epsCONC Dstar +
    3 * epsX Dstar + 9 / Dstar

/-- [s7:propCost], [s1:defConstants] (v) "`C_0 := D_*/2 + 1085 + ε_1(D_*)`". -/
noncomputable def C0 (Dstar : ℝ) : ℝ := Dstar / 2 + 1085 + eps1 Dstar

end EG.Quot
