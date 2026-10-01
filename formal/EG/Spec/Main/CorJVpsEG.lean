module

public import EG.Defs.Main.GammaCond
public import EG.Defs.Graph
public import EG.Defs.Fnum

/-!
# Statement of Corollary JV⁺*-EG, the explicit form of the Main Theorem (manuscript s7:thmMainProof)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:thmMainProof` (and blueprint s1, node `s1:thmMain`, "optional unlocked explicit form").

Manuscript v6.1, `s7.tex`, Corollary [s7:thmMainProof] (Corollary JV⁺*-EG; proof of the Main
Theorem): "Theorem s1:thmMain holds."

Manuscript v6.1, `s1.tex`, Theorem [s1:thmMain] (Main Theorem; candidate): "Let
`ε, σ, C', A, N_0, D_*` be as in Definition s1:defConstants, with `D_*` satisfying Γ1–Γ4 of
Condition s1:condGamma. Put `C_0 := D_*/2 + 1085 + ε_1(D_*)` and
`c_EG := max{C_0/(1 − 2θ_Q), N_0/2}`, where `ε_1(D_*)` and `θ_Q = ε_2(D_*)` are the explicit
functions of `D_*` defined in Proposition s7:propCost and Lemma s7:lemUHsplit. Then every graph
`G` on `n` vertices satisfies `f(G) ≤ c_EG n`. In particular `f(n) = O(n)`."

Formal reading.
* The Tier-1 target is the locked `EG.Spec.MainInternal` (`EG/Spec/Main.lean`: existence of a
  constant `c`), which is the "In particular `f(n) = O(n)`" (with `c = ⌈c_EG⌉₊` for any admissible
  `N_0`, `D_*`). This file adds the explicit form (Tier-2, blueprint s1 MAIN-EXISTENTIAL,
  s7b MAIN-EXPLICIT-OPTIONAL): for all `N_0` as in s1:defConstants (ii) (`EG.N0Cond N0`) and `D_*`
  satisfying Γ1–Γ4 (`EG.GammaCond N0 D`), every graph `G` (an `EG.FGraph` on any vertex type)
  satisfies `f(G) ≤ c_EG · |V(G)|`, with `c_EG = EG.cEG N0 D` (`C_0 = EG.Quot.C0`,
  `θ_Q = EG.Quot.thetaQ`), `f = EG.fnum`.
* `ε, σ, C', A` are the locked numerals `EG.epsC, EG.sigmaC, EG.Cp, EG.Aexp` inside the Defs.
* Name: `CorJVpsEGStatement` (the corollary's name), to avoid a clash with a `MainExplicit`
  statement the s1 unit may write for `s1:thmMain`; the two would be the same proposition.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s7:thmMainProof] Corollary JV⁺*-EG, "Theorem s1:thmMain holds", explicit form: "Let
`ε, σ, C', A, N_0, D_*` be as in Definition s1:defConstants, with `D_*` satisfying Γ1–Γ4 …
Put `C_0 := D_*/2 + 1085 + ε_1(D_*)` and `c_EG := max{C_0/(1 − 2θ_Q), N_0/2}` … Then every graph
`G` on `n` vertices satisfies `f(G) ≤ c_EG n`." -/
def CorJVpsEGStatement : Prop :=
  ∀ N0 Dstar : ℝ, N0Cond N0 → GammaCond N0 Dstar →
    ∀ (V : Type u) (G : FGraph V), (fnum G.edges : ℝ) ≤ cEG N0 Dstar * (G.card : ℝ)

end EG.Spec
