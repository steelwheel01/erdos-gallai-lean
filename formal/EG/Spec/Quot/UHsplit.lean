module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Quot.Constants
public import EG.Defs.Gamma.Full

/-!
# Statement of Lemma UH*-split: quotient size (manuscript s7:lemUHsplit)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:lemUHsplit` (Tier-2 Spec over the s7a round-step Defs, S7-ROUNDSTEP-IN-DEFS).

Manuscript v6.1, `s7.tex`, Lemma [s7:lemUHsplit] (Lemma UH*-split: quotient size):
"For `3 ≤ l ≤ R` put
`det_l := 3|D_l| + 78 nM_l/Hcd_l + 30 n/M_l + 320 nM_l^3(log₂θ^ult_l + 8)/λ_{l-2}^{95}`,
a deterministic function of the run.
(i) `X_{V,l}` is the stage-1 weight of Lemma s7:lemVstar.
(ii) For every past, `E[copies_l | Past_l] ≤ X_{V,l} + det_l`.
(iii) If the stage-1 outcome satisfies `X' ≤ 3 E X'` and at every round `ξ_l` lies in the event of
Construction s7:consRound(f), then `Σ_{l=3}^{R} |V(Q_l)| ≤ 12 E X' + 4 Σ_{l=3}^{R} det_l`.
(iv) Put `F(x) := (3184 + 30400 log₂x) x^{-90.2}` for `x ≥ 1`. Then
`Σ_l det_l ≤ 3ε_A n + 60n/D_* + 2F(log₂D_*) n`, and `2F(log₂D_*) < 2^{-1000}`. Hence, in the
situation of (iii), `Σ_{l=3}^{R} |V(Q_l)| ≤ θ_Q n`,
`θ_Q := ε_2(D_*) := 12 ε_X(D_*) + 4(3ε_A + 60/D_* + 2F(log₂D_*))`, with `ε_A = 31ε/(C' log log D_*)`
as in Lemma s2:lemTower(e). So `θ_Q` depends on `D_*` only, and `θ_Q ≤ 1/4` by condition
s1:condG4."

Formal reading (TRIAGE §2.6, §2.10; blueprint s7b UH-*).
* Setting: `EG.RunHyp N0 Dstar G run` and a designation `δ` with `IsDesignation run G δ`; a stage-1
  outcome `ω ∈ (Stage1.law G run).supp`. No Γ4: "`θ_Q ≤ 1/4` by condition s1:condG4" is the
  condition Γ4 itself (`EG.Gamma4`), not a claim of the lemma, and is not restated (TRIAGE §2.6,
  GAMMA fix round 1, m1: "drop the `θ_Q ≤ 1/4` clause and derive it where used").
* `det_l = EG.Quot.detl run G l`, `F = EG.Quot.FQ`, `θ_Q = ε_2 = EG.Quot.eps2`,
  `ε_A = EG.HB.epsA`, `X_{V,l} = EG.Quot.XVl run G ω.pool l` (so (i) is definitional),
  `E X' = E[XprimeOf run G δ ·]` under `EG.Stage1.law G run`; `n = G.card`.
* (ii) "For every past": every `J` with `JPlusProps run G δ (stageOf ω) l J`, the past
  `I = pastOf run G δ ω l J`, and every valid rule `R : Rules I`; `copies_l = R.copies ξ`
  (`= |V(Q_l)|`), `E[· | Past_l]` the expectation under `roundLaw I.G I.M`.
* (iii) "the stage-1 outcome satisfies `X' ≤ 3E X'` and at every round `ξ_l` lies in the event of
  (f)": for every family of admissible J-sets `Js`, valid rules `Rs` and draws `ξs` with
  `(Rs l).MarkovEvent (ξs l)` at every round `3 ≤ l ≤ R`; `Q_l = (Rs l).Q (ξs l)`. The chosen
  quotient `roundQuotient run G δ (stageOf ω) ω.pool l J` of the J-consumer is one instance
  (chosen rules, chosen `ξ_l`).
* (iv) is split into `UHsplitDetStatement` (the bound on `Σ det_l` and `2F(log₂D_*) < 2^{-1000}`,
  functions of the run and `D_*` only) and `UHsplitThetaStatement` ("Hence, in the situation of
  (iii), `Σ |V(Q_l)| ≤ θ_Q n`").
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s7:lemUHsplit] (ii) "For every past, `E[copies_l | Past_l] ≤ X_{V,l} + det_l`" (every
admissible `J_l`, every valid choice of the fixed rules; `E` over the round randomness `ξ_l`). -/
def UHsplitRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
    ∀ J : Finset (Sym2 V), JPlusProps run G δ (stageOf ω) l J →
    ∀ I : RoundInput V, I = pastOf run G δ ω l J → ∀ R : Rules I, R.Valid →
      (roundLaw I.G I.M).expect (fun ξ => (R.copies ξ : ℝ)) ≤
        (XVl run G ω.pool l : ℝ) + detl run G l

/-- [s7:lemUHsplit] (iii) "If the stage-1 outcome satisfies `X' ≤ 3 E X'` and at every round `ξ_l`
lies in the event of Construction s7:consRound(f), then
`Σ_{l=3}^{R} |V(Q_l)| ≤ 12 E X' + 4 Σ_{l=3}^{R} det_l`." -/
def UHsplitSumStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp,
    (XprimeOf run G δ ω : ℝ) ≤
      3 * (Stage1.law G run).expect (fun ω' => (XprimeOf run G δ ω' : ℝ)) →
    ∀ Js : ℕ → Finset (Sym2 V),
    (∀ l ∈ Finset.Icc 3 run.R, JPlusProps run G δ (stageOf ω) l (Js l)) →
    ∀ Rs : (l : ℕ) → Rules (pastOf run G δ ω l (Js l)),
    (∀ l ∈ Finset.Icc 3 run.R, (Rs l).Valid) →
    ∀ ξs : (l : ℕ) → Xi G (run.M G l),
    (∀ l ∈ Finset.Icc 3 run.R, (Rs l).MarkovEvent (ξs l)) →
      ∑ l ∈ Finset.Icc 3 run.R, (((Rs l).Q (ξs l)).card : ℝ) ≤
        12 * (Stage1.law G run).expect (fun ω' => (XprimeOf run G δ ω' : ℝ)) +
          4 * ∑ l ∈ Finset.Icc 3 run.R, detl run G l

/-- [s7:lemUHsplit] (iv), first sentence: "Put `F(x) := (3184 + 30400 log₂x) x^{-90.2}` for
`x ≥ 1`. Then `Σ_l det_l ≤ 3ε_A n + 60n/D_* + 2F(log₂D_*) n`, and `2F(log₂D_*) < 2^{-1000}`."
(The sum over `3 ≤ l ≤ R`; a statement about the run and `D_*` only.) -/
def UHsplitDetStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∑ l ∈ Finset.Icc 3 run.R, detl run G l ≤
        3 * epsA Dstar * (G.card : ℝ) + 60 * (G.card : ℝ) / Dstar +
          2 * FQ (Real.logb 2 Dstar) * (G.card : ℝ) ∧
      2 * FQ (Real.logb 2 Dstar) < (2 : ℝ) ^ (-(1000 : ℤ))

/-- [s7:lemUHsplit] (iv), last part: "Hence, in the situation of (iii),
`Σ_{l=3}^{R} |V(Q_l)| ≤ θ_Q n`, `θ_Q := ε_2(D_*) := 12 ε_X(D_*) + 4(3ε_A + 60/D_* + 2F(log₂D_*))`"
(`θ_Q = EG.Quot.eps2 Dstar`; "`θ_Q ≤ 1/4` by condition s1:condG4" is the hypothesis Γ4 of the
consumers, not restated). -/
def UHsplitThetaStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp,
    (XprimeOf run G δ ω : ℝ) ≤
      3 * (Stage1.law G run).expect (fun ω' => (XprimeOf run G δ ω' : ℝ)) →
    ∀ Js : ℕ → Finset (Sym2 V),
    (∀ l ∈ Finset.Icc 3 run.R, JPlusProps run G δ (stageOf ω) l (Js l)) →
    ∀ Rs : (l : ℕ) → Rules (pastOf run G δ ω l (Js l)),
    (∀ l ∈ Finset.Icc 3 run.R, (Rs l).Valid) →
    ∀ ξs : (l : ℕ) → Xi G (run.M G l),
    (∀ l ∈ Finset.Icc 3 run.R, (Rs l).MarkovEvent (ξs l)) →
      ∑ l ∈ Finset.Icc 3 run.R, (((Rs l).Q (ξs l)).card : ℝ) ≤ eps2 Dstar * (G.card : ℝ)

end EG.Spec
