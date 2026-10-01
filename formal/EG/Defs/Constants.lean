module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Field.Power

/-!
# The absolute constants `ε`, `σ`, `C'`, `A` (manuscript s1:defConstants (i))

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript text ([s1:defConstants] (i)):
"`ε := 2^{-5}`, `σ := 100`, `C' := 103` and `A := 105`."
([s1:remOrder] step 1 and [s1:tabOrder] step 1: they are fixed first and are explicit.)

Formal counterparts (TRIAGE §2.4):
* `EG.epsC : ℝ := 2 ^ (-5 : ℤ)` (`ε`);
* `EG.sigmaC : ℕ := 100` (`σ`);
* `EG.Cp : ℕ := 103` (`C'`);
* `EG.Aexp : ℕ := 105` (`A`).

Names. The Greek letters `ε` and `σ` are the usual names of bound variables (for example
`IsExpander G ε s`), so the constants are `epsC` and `sigmaC`, to avoid shadowing.
Types. `σ`, `C'`, `A` are natural numbers because the manuscript uses them as exponents
(`2^{σ+15}`, `(log₂ D_*)^{C'}`, `(Aμ)^{46A}`, `(Aμ)^{2A}`); in real expressions they appear
through the cast (`(Aexp : ℝ)`). `ε` is a real number.
The later constants of s1:defConstants ((ii) `N_0`, (iii) `D_*`, (iv)–(vi) `ε₁`, `ε₂`, `C_0`,
`c_EG`) are not constants of this file: `N_0` and `D_*` are universally quantified with the
predicates `EG.N0Cond`, `EG.Gamma1core`, … (TRIAGE §2.4), and `ε₁`, `ε₂`, `C_0`, `c_EG` are
defined in the s7 layer.
Value lemmas `epsC_eq`, `sigmaC_eq`, `Cp_eq`, `Aexp_eq` (all `rfl`) are in
`EG/Lib/Found/Constants.lean`.
-/

@[expose] public section


namespace EG

/-- [s1:defConstants] (i) "`ε := 2^{-5}`". -/
noncomputable def epsC : ℝ := 2 ^ (-5 : ℤ)

/-- [s1:defConstants] (i) "`σ := 100`". -/
def sigmaC : ℕ := 100

/-- [s1:defConstants] (i) "`C' := 103`". -/
def Cp : ℕ := 103

/-- [s1:defConstants] (i) "`A := 105`". -/
def Aexp : ℕ := 105

end EG
