module

public import EG.Defs.Log
public import EG.Defs.Constants
public import EG.Defs.HB.Run

/-!
# The small constants of s6: `ε_CONC`, `ε_K`, `ε_M` (s6:thmCONCL (iv), s6:thmMIXC (c))

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1. Design note: `formal/work/p2d/design.md`. Namespace `EG.Chain`.

TRIAGE §2.4: "ε-functions are Defs with exactly the formulas of the defining statements; the Γ4
bullet list is descriptive only". Conventions: `log = log₂` (`Real.logb 2`), `log*` is
`EG.logStar` (`EG.Defs.Log`), `σ = EG.sigmaC`, `ε = EG.epsC`, `C' = EG.Cp`, `A = EG.Aexp`,
`ε_A = EG.HB.epsA`; the exponent `1/2` is `Real.rpow` with the rational exponent `1/2`
(TRIAGE §2.3). The functions are total in `D_*`; for `D_* ≤ 4` some logarithms are `≤ 1` or
`≤ 0` (Real junk values), while every statement using them assumes Γ (`log log D_* ≥ 2^8`).

`ε_K` is the constant of s5:lemKRED, "`ε_K(D_*) := ε_ch(D_*)`", with `ε_ch` of s5:lemParent (ii).
It is written out here (`EG.Chain.epsK`) because Theorem MIX-C names it and the s5 Defs
(`EG/Defs/Light/Constants.lean`, TRIAGE §3 item 20) do not exist yet; when they do, the equality
`epsK D = epsChain D` must be a `rfl` Lib lemma (same formula).
-/

@[expose] public section

namespace EG.Chain

/-- [s6:thmCONCL] (iv) "`ε_CONC(D_*) := 2^{σ+15} log* D_*/log D_* + 200 ε log* D_*/(C' log log D_*)
+ 4(2 log* D_* + 2)/(log D_*)^{1/2}`" (`σ = 100`, `ε = 2^{-5}`, `C' = 103`, `log = log₂`). -/
noncomputable def epsCONC (Dstar : ℝ) : ℝ :=
  (2 : ℝ) ^ (sigmaC + 15) * (logStar Dstar : ℝ) / Real.logb 2 Dstar
    + 200 * epsC * (logStar Dstar : ℝ) / ((Cp : ℝ) * Real.logb 2 (Real.logb 2 Dstar))
    + 4 * (2 * (logStar Dstar : ℝ) + 2) / Real.logb 2 Dstar ^ ((1 : ℝ) / 2)

/-- [s5:lemKRED] "`ε_K(D_*) := ε_ch(D_*)`", with [s5:lemParent] (ii)
"`ε_ch(D_*) := 614/D_* + log₂(2A log₂(A log₂ log₂ D_*)) / (371 (log₂ log₂ D_*)^2)`" (`A = 105`). -/
noncomputable def epsK (Dstar : ℝ) : ℝ :=
  614 / Dstar + Real.logb 2 (2 * (Aexp : ℝ) * Real.logb 2 ((Aexp : ℝ) *
      Real.logb 2 (Real.logb 2 Dstar)))
    / (371 * Real.logb 2 (Real.logb 2 Dstar) ^ 2)

/-- [s6:thmMIXC] (c) "`ε_M(D_*) := ε_K(D_*) + 169 ε_A + 252/D_*`, with `ε_A = 31ε/(C' log log D_*)`
as defined in Lemma s2:lemTower(e). Thus `ε_M` is a function of `D_*` alone". -/
noncomputable def epsM (Dstar : ℝ) : ℝ :=
  epsK Dstar + 169 * HB.epsA Dstar + 252 / Dstar

end EG.Chain
