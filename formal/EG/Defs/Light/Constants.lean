module

public import EG.Defs.Chain.Constants

/-!
# The small constants of s5: `ε_U` (s5:lemExpect) and `ε_ch` (s5:lemParent (ii))

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s5.tex`. Design note: `formal/work/p2d/light.md`. Namespace `EG.Light`.
TRIAGE §2.4 ("ε-functions are Defs with exactly the formulas of the defining statements") and
§3 item 20.

* `epsU` is the constant of [s5:lemExpect]: "`ε_U(D_*) := 2462 (log₂ D_*)^{-205}`" (an integer
  power, `zpow`).
* `epsChain` is the constant of [s5:lemParent] (ii). Its formula is written **once**, as
  `EG.Chain.epsK` (`EG/Defs/Chain/Constants.lean`), which is "`ε_K(D_*) := ε_ch(D_*)`" of
  [s5:lemKRED]; here `epsChain` is that definition (TRIAGE item 20, G-S5-1: "never a second literal
  copy of the ε_ch formula"). `EG.Light.epsChain_eq_epsK` (Lib) is `rfl`.

Both functions are total in `D_*`; for small `D_*` some logarithms are `≤ 0` (Real junk values),
while every statement using them assumes Γ.
-/

@[expose] public section

namespace EG.Light

/-- [s5:lemExpect] "where `ε_U(D_*) := 2462 (log₂ D_*)^{-205}`" (`log₂ = Real.logb 2`, the
exponent `-205` an integer power). -/
noncomputable def epsU (Dstar : ℝ) : ℝ := 2462 * Real.logb 2 Dstar ^ (-205 : ℤ)

/-- [s5:lemParent] (ii) "`ε_ch(D_*) := 614/D_* + log₂(2A log₂(A log₂ log₂ D_*)) /
(371 (log₂ log₂ D_*)^2)`" (`A = 105`), written as `EG.Chain.epsK` (the same constant, "`ε_K(D_*) :=
ε_ch(D_*)`" of [s5:lemKRED]; one locked copy of the formula, TRIAGE G-S5-1). -/
noncomputable def epsChain (Dstar : ℝ) : ℝ := EG.Chain.epsK Dstar

end EG.Light
