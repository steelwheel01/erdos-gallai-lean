module

public import EG.Defs.Main.Gamma
public import EG.Defs.Gamma.Full

/-!
# The galactic conditions Γ1–Γ4 as one predicate (manuscript s1:condGamma, s1:defConstants (iii))

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s1.tex`, Definition [s1:defConstants] (iii): "`D_*` is a constant satisfying
Γ1–Γ4 of Condition s1:condGamma." Condition [s1:condGamma] lists Γ1 (items (a)–(f)), Γ2 (a)–(c),
Γ3 and Γ4, and says of Γ2: "Each of (a)–(c) is implied by Γ1 … They are listed separately for
traceability."

Formal reading (TRIAGE §2.4; blueprint s1, risk MAIN-GAMMA2BC):
`GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D`. Γ2(b),(c) are not predicates
of `D_*` (they quantify over runs and over failure probabilities); they are lemmas
(s2:lemTower (b), s3:lemCOL, s5:lemE1), never fields. Γ2(a) is kept as a field although it
follows from Γ1 (`Gamma1core.gamma2a`), as in the manuscript's list. `N0` is a parameter because
Γ3 depends on it ("`N_0` is chosen before `D_*`", s1:remOrder).

This file is separate from the locked `EG/Defs/Main/Gamma.lean` (which holds `Gamma4`, `cEG`):
that file was locked before `EG/Defs/Gamma/Full.lean` existed (design note
`formal/work/p2d/quot.md`, Open item 1). Design note: `formal/work/p2b/GAMMA.md`.
-/

@[expose] public section

namespace EG

/-- [s1:condGamma], [s1:defConstants] (iii) "`D_*` is a constant satisfying Γ1–Γ4 of
Condition s1:condGamma" (with `N_0` fixed before `D_*`; Γ2(b),(c) are lemmas, not fields). -/
def GammaCond (N0 D : ℝ) : Prop := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D

end EG
