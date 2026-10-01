module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Main.Gamma
public import EG.Defs.Gamma.Full

/-!
# Statement of Proposition "cost on the chosen outcome" (manuscript s7:propCost)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:propCost` (Tier-2 Spec over the s7a round-step Defs; MIX-C interface B′,
S7-MIXC-INTERFACE, TRIAGE §2.9).

Manuscript v6.1, `s7.tex`, Proposition [s7:propCost] (Cost on the chosen outcome):
"On an outcome as in Lemma s7:lemOneOutcome, with the round step of Construction s7:consRound as
the J-consumer, the decomposition of `E(G)` given by Theorem s6:thmMIXC has at most
`(D_*/2 + 1085 + ε_1(D_*)) n + 2 Σ_{l=3}^{R} f(Q_l)` objects, where
`ε_1(D_*) := ε_K(D_*) + 169 ε_A + 252/D_* + 1.5 ε_CONC(D_*) + 3 ε_X(D_*) + 9/D_*`,
with `ε_A = 31ε/(C' log log D_*)` as in Lemma s2:lemTower(e). The terms are itemized in
Table s7:tabCost. The constant is `745 + 338 + 2 = 1085`, and `ε_1` is counted once. Consequently
`C_0 = D_*/2 + 1085 + ε_1(D_*) ≤ D_*/2 + 1091` under Γ4. No term involves `c_EG`. The only Markov
multipliers are the fixed 3 (stage 1) and 4 (per round). There is no term for VX-parts
(`𝒱 = ∅`)."

Formal reading (blueprint s7b COST-*, JV-SAME-Q; TRIAGE §2.9, §2.10).
* Setting: `EG.RunHyp N0 Dstar G run` and a designation `δ` with `IsDesignation run G δ`.
* "An outcome as in Lemma s7:lemOneOutcome": a stage-1 outcome `ω ∈ (Stage1.law G run).supp` with
  `X'(ω) ≤ 3 E X'` (property (1)); property (2) has no Lean content (deterministic stage-3 Specs,
  `EG/Spec/Quot/OneOutcome.lean`); property (3) (`ξ_l` in the event of (f) at every round) is built
  into the J-consumer of s7, `EG.Quot.roundOut`, which uses the chosen rules and the chosen draw
  `Rules.xiChosen` (in the event whenever the event has an outcome of positive weight, which
  `OneOutcomeRoundStatement` asserts for every past).
* "the round step of Construction s7:consRound as the J-consumer … the decomposition of `E(G)`
  given by Theorem s6:thmMIXC": MIX-C (option B′) returns the J-sets `J_l` of the chain, which
  satisfy `JPlusProps` at every round `3 ≤ l ≤ R`, and a decomposition `D` of `E(G)`; the
  quotients `Q_l` are those of the same round steps, `roundQuotient run G δ (stageOf ω) ω.pool l J_l`
  (same chosen rules and same `ξ_l` as the J-consumer output `roundOut`, JV-SAME-Q). The Spec is
  the existence of such `J_l` and `D` with the stated bound (T0: the decomposition is not named as
  "the one given by MIX-C"; its only use, s7:thmJVps, needs `f(G) ≤ |D|` and the same `Q_l`).
* `ε_1 = EG.Quot.eps1` (with `ε_K = EG.Chain.epsK`, `ε_CONC = EG.Chain.epsCONC`,
  `ε_X = EG.Quot.epsX`, `ε_A = EG.HB.epsA`), `C_0 = EG.Quot.C0`, `f = EG.fnum`, `n = G.card`.
* "Consequently `C_0 ≤ D_*/2 + 1091` under Γ4" is `CostC0Statement`. The sentences "The terms are
  itemized …", "No term involves `c_EG`", "The only Markov multipliers …" and "There is no term for
  VX-parts" are commentary (VX-parts are not defined in the formalization).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s7:propCost] "On an outcome as in Lemma s7:lemOneOutcome, with the round step of
Construction s7:consRound as the J-consumer, the decomposition of `E(G)` given by Theorem
s6:thmMIXC has at most `(D_*/2 + 1085 + ε_1(D_*)) n + 2 Σ_{l=3}^{R} f(Q_l)` objects". -/
def CostStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp,
    (XprimeOf run G δ ω : ℝ) ≤
      3 * (Stage1.law G run).expect (fun ω' => (XprimeOf run G δ ω' : ℝ)) →
    ∃ Js : ℕ → Finset (Sym2 V),
      (∀ l ∈ Finset.Icc 3 run.R, JPlusProps run G δ (stageOf ω) l (Js l)) ∧
      ∃ D : List (Obj V), IsDecomp (G.edges : Set (Sym2 V)) D ∧
        (D.length : ℝ) ≤ (Dstar / 2 + 1085 + eps1 Dstar) * (G.card : ℝ) +
          2 * ∑ l ∈ Finset.Icc 3 run.R,
            (fnum (roundQuotient run G δ (stageOf ω) ω.pool l (Js l)).edges : ℝ)

/-- [s7:propCost] "Consequently `C_0 = D_*/2 + 1085 + ε_1(D_*) ≤ D_*/2 + 1091` under Γ4." -/
def CostC0Statement : Prop :=
  ∀ Dstar : ℝ, Gamma4 Dstar → C0 Dstar ≤ Dstar / 2 + 1091

end EG.Spec
