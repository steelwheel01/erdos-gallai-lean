module

public import EG.Defs.Quot.Constants

/-!
# The last galactic condition Γ4 and the constant `c_EG` (manuscript s1:condG4, s1:defConstants)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s1.tex`: Condition [s1:condGamma] item Γ4, Definition [s1:defConstants] (vi),
Theorem [s1:thmMain]; quoted below. Design note: `formal/work/p2d/quot.md`. Namespace `EG`;
TRIAGE §2.4 ("`EG/Defs/Main/Gamma.lean` (last): `Gamma4`, `GammaCond N0 D`, `cEG`"), §3 item 34.

Γ4 mentions `ε_1` and `ε_2` (`EG.Quot.eps1`, `EG.Quot.eps2`), hence it lives after the s7 Defs
(blueprint s1 CONST-LAYERING). The bullet list of Γ4 in s1 is descriptive; the formulas are those
of the defining statements (`EG/Defs/Quot/Constants.lean`).

`GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D` (blueprint s1) needs `Gamma1`,
`Gamma3` of `EG/Defs/Gamma/Full.lean` (TRIAGE §3 item 14), which does not exist yet; it is added
here (additively) once that file exists. See the design note.
-/

@[expose] public section

namespace EG

/-- [s1:condG4] "`ε_1(D_*) ≤ 6` and `θ_Q = ε_2(D_*) ≤ 1/4`, where `ε_1` and `ε_2` are the
explicit expressions of Proposition [s7:propCost] and Lemma [s7:lemUHsplit]." -/
def Gamma4 (D : ℝ) : Prop := Quot.eps1 D ≤ 6 ∧ Quot.eps2 D ≤ 1 / 4

/-- [s1:defConstants] (vi), [s1:thmMain] "`c_EG := max{C_0/(1 − 2θ_Q), N_0/2}`" with
"`C_0 := D_*/2 + 1085 + ε_1(D_*)`" and "`θ_Q = ε_2(D_*)`" (a function of `N_0` and `D_*`). -/
noncomputable def cEG (N0 D : ℝ) : ℝ := max (Quot.C0 D / (1 - 2 * Quot.thetaQ D)) (N0 / 2)

end EG
