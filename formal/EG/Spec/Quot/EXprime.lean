module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Quot.Constants
public import EG.Defs.Gamma.Full

/-!
# Statement of Lemma "expectation of `X'`" (manuscript s7:lemEXprime)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:lemEXprime`.

Manuscript v6.1, `s7.tex`, Lemma [s7:lemEXprime] (Expectation of `X'`):
"`E X' ≤ ε_X(D_*) n`, where
`ε_X(D_*) := ε_U(D_*) + 10.3/D_* + 2.1 (6 log₂D_* + 12)/D_*`
and `ε_U` is the function of Lemma s5:lemExpect (through Lemma s6:lemLost). More precisely,
`E X_U ≤ ε_U(D_*) n + 5.5 n/D_*`, `E X_pool ≤ 4.8 n/D_*` and
`E X_V ≤ 2.1 (6 log₂D_* + 12) n/D_*`."

Formal reading.
* Setting: `EG.RunHyp N0 Dstar G run` (the statement has no hypotheses in the text; the proof
  uses those of s6:lemLost, s5:lemExpect, s2:lemCap, s2:propOV, s2:propStructure, s2:lemTower,
  which are the standing hypotheses of s5–s7; blueprint EXP-HYPS) and a designation `δ` with
  `IsDesignation run G δ` ("Fix a valid run, a designation `δ` …", s6:defLending; `X_pool` depends
  on `δ` through `c^agg` and JV-badness).
* `X_U`, `X_pool`, `X_V`, `X'` at a stage-1 outcome `ω` are `XUOf`, `XpoolOf`, `XVOf`,
  `XprimeOf` (`EG/Defs/Probe/S7b/Outcome.lean`: the locked Defs `EG.Chain.XU`, `EG.Quot.Xpool`,
  `EG.Quot.XV`, `EG.Quot.Xprime` at the stage data `stageOf ω` and the pool labels `ω.pool`);
  natural numbers, cast to `ℝ`.
* `E` is the expectation under the joint stage-1 law `EG.Stage1.law G run` (TRIAGE §2.7).
* `ε_X = EG.Quot.epsX`, `ε_U = EG.Light.epsU` (locked formulas); `n = G.card`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s7:lemEXprime] "`E X' ≤ ε_X(D_*) n`, where `ε_X(D_*) := ε_U(D_*) + 10.3/D_* +
2.1(6 log₂D_* + 12)/D_*` … More precisely, `E X_U ≤ ε_U(D_*) n + 5.5 n/D_*`,
`E X_pool ≤ 4.8 n/D_*` and `E X_V ≤ 2.1 (6 log₂D_* + 12) n/D_*`." (Setting `RunHyp`, a designation
`δ`; `E` over the stage-1 law.) -/
def EXprimeStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    (Stage1.law G run).expect (fun ω => (XprimeOf run G δ ω : ℝ)) ≤
        epsX Dstar * (G.card : ℝ) ∧
      (Stage1.law G run).expect (fun ω => (XUOf run G δ ω : ℝ)) ≤
        Light.epsU Dstar * (G.card : ℝ) + 5.5 * (G.card : ℝ) / Dstar ∧
      (Stage1.law G run).expect (fun ω => (XpoolOf run G δ ω : ℝ)) ≤
        4.8 * (G.card : ℝ) / Dstar ∧
      (Stage1.law G run).expect (fun ω => (XVOf run G ω : ℝ)) ≤
        2.1 * (6 * Real.logb 2 Dstar + 12) * (G.card : ℝ) / Dstar

end EG.Spec
