module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Light.Constants
public import EG.Defs.Gamma.Full

/-!
# Statement of Lemma "lost ports; the constant (K6)" (manuscript s6:lemLost)

Statement file (`EG/Spec/**`) of the P2 Spec unit s6b (`formal/work/p2s/s6b.md`); blueprint s6b,
node `s6:lemLost`.

Manuscript v6.1, `s6.tex`, Lemma [s6:lemLost] (lost ports; the constant (K6)):
"Fix a valid run and a designation `δ`. Probabilities and expectations are over the stage-1
outcome.
(i) for every classed port `u` of round `l ≥ 3`,
`P(u ∈ Lost) ≤ K^JS_l ρ_l + P(Y(u) lend-bad) ≤ M_l^{-2} + 2|V(Y(u))|^{-2} ≤ 2M_l^{-2}`;
(K6) `E|Lost_l| ≤ 2n/M_l^2` for every round `l`;
(iii) `E X_U ≤ ε_U(D_*) n + Σ_l 2n(169 + M_l)/M_l^2 ≤ ε_U(D_*) n + 5.5 n/D_*`."

Formal reading (blueprint s6b LOST-*, TRIAGE §2.6, §2.7).
* **Setting.** "Fix a valid run" hides the standing hypotheses of s5–s7 (blueprint LOST-HYPS: the
  proof uses Γ1 through s3:lemCOL, s5:lemE1, s5:lemExpect, and `n ≥ N_0`, `d_1 ≥ D_*` through
  s2:propStructure(iv), s2:lemTower(b)): `EG.RunHyp N0 Dstar G run` (TRIAGE §2.6: "s5, s6b (Lost,
  JS-LC, MIX-C) and s7 take `RunHyp`"). A designation `δ` with `IsDesignation run G δ`, quantified
  before the law (it is deterministic).
* **"over the stage-1 outcome"**: the joint stage-1 law `EG.Stage1.law G run` (TRIAGE §2.7), the
  space of s5:lemE1, s5:lemExpect and of the consumer s7:lemEXprime. The stage-2 data of an
  outcome `ω` are `EG.Quot.stageOf ω` (= `StageData.ofOutcome ω (Light.demoted ω) (Light.dem ω)
  (Light.lp ω)`, the instantiation contract D-DES-1 / TRIAGE §3 item 20).
* **(i).** "a classed port `u` of round `l ≥ 3`": `u ∈ Q_Z = run.classed G l a` for some
  `Z = a ∈ Std_l` (the unique such `Z`, s2:propStructure(iv); `Std_l = ∅` for `l > R`, so
  `l ≤ R` is automatic). "`u ∈ Lost`" is `u ∈ Lost_Z = EG.Chain.lost run G δ S l a`; "`Y(u)`" is
  `δ l u`; "lend-bad" is `EG.Chain.lendBad`. `K^JS_l = Stage1.KJS G run l` (a natural number),
  `ρ_l = Stage1.rhoJS G run l = M_l^{-4}`, `M_l = run.M G l`, `|V(Y)| = (run.ancVerts G Y).card`;
  `^{-2}` is an integer power of a real. The displayed chain is stated literally as three
  inequalities (the middle one combines `K^JS_l ρ_l = M_l^{-2}` with the proof's
  `P(Y lend-bad) ≤ 2|V(Y)|^{-2}`).
* **(K6)** for every natural `l` ("every round"; for `l ∉ [3, R]`, `Lost_l = ∅` and the bound is
  `0 ≤ 2n/M_l^2`, true as `M_l ≥ 2^{40}`); `|Lost_l| = (EG.Chain.lostRound …).card`, `n = G.card`.
* **(iii).** `X_U` at `ω` is `EG.Quot.XUOf run G δ ω` (= `EG.Chain.XU run G δ (stageOf ω)`, the
  consumer form of s7:lemEXprime, `EG/Spec/Quot/EXprime.lean`); `Σ_l` ranges over the rounds
  `l ∈ [1, R]` (the range of `X_U` in `EG.Chain.XU`, blueprint LEND-XU-RANGE); `ε_U = Light.epsU`.
  The chain is stated as two inequalities.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s6:lemLost] "Fix a valid run and a designation `δ`. Probabilities and expectations are over
the stage-1 outcome. (i) for every classed port `u` of round `l ≥ 3`,
`P(u ∈ Lost) ≤ K^JS_l ρ_l + P(Y(u) lend-bad) ≤ M_l^{-2} + 2|V(Y(u))|^{-2} ≤ 2M_l^{-2}`;
(K6) `E|Lost_l| ≤ 2n/M_l^2` for every round `l`;
(iii) `E X_U ≤ ε_U(D_*) n + Σ_l 2n(169 + M_l)/M_l^2 ≤ ε_U(D_*) n + 5.5 n/D_*`."
(Setting `RunHyp`; the stage-1 law; module docstring.) -/
def LostStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    -- (i)
    (∀ l : ℕ, 3 ≤ l → ∀ a ∈ run.Std G l, ∀ u ∈ run.classed G l a,
      (Stage1.law G run).prob {ω | u ∈ lost run G δ (stageOf ω) l a} ≤
          (Stage1.KJS G run l : ℝ) * Stage1.rhoJS G run l +
            (Stage1.law G run).prob {ω | lendBad run G (stageOf ω) (δ l u)} ∧
      (Stage1.KJS G run l : ℝ) * Stage1.rhoJS G run l +
            (Stage1.law G run).prob {ω | lendBad run G (stageOf ω) (δ l u)} ≤
          (run.M G l : ℝ) ^ (-2 : ℤ) + 2 * ((run.ancVerts G (δ l u)).card : ℝ) ^ (-2 : ℤ) ∧
      (run.M G l : ℝ) ^ (-2 : ℤ) + 2 * ((run.ancVerts G (δ l u)).card : ℝ) ^ (-2 : ℤ) ≤
          2 * (run.M G l : ℝ) ^ (-2 : ℤ)) ∧
    -- (K6)
    (∀ l : ℕ,
      (Stage1.law G run).expect (fun ω => ((lostRound run G δ (stageOf ω) l).card : ℝ)) ≤
        2 * (G.card : ℝ) / (run.M G l : ℝ) ^ 2) ∧
    -- (iii)
    (Stage1.law G run).expect (fun ω => (XUOf run G δ ω : ℝ)) ≤
        Light.epsU Dstar * (G.card : ℝ) +
          ∑ l ∈ Finset.Icc 1 run.R,
            2 * (G.card : ℝ) * (169 + (run.M G l : ℝ)) / (run.M G l : ℝ) ^ 2 ∧
    Light.epsU Dstar * (G.card : ℝ) +
          ∑ l ∈ Finset.Icc 1 run.R,
            2 * (G.card : ℝ) * (169 + (run.M G l : ℝ)) / (run.M G l : ℝ) ^ 2 ≤
        Light.epsU Dstar * (G.card : ℝ) + 5.5 * (G.card : ℝ) / Dstar

end EG.Spec
