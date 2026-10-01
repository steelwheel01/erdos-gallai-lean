module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Quot.Constants
public import EG.Defs.Gamma.Full

/-!
# Statement of Lemma "one joint outcome exists" (manuscript s7:lemOneOutcome)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:lemOneOutcome` (T0 decision OO-PROCEDURAL: the lemma is split into its stage-1 part and
its round part; the stage-3 part has no Lean content).

Manuscript v6.1, `s7.tex`, Lemma [s7:lemOneOutcome] (One joint outcome exists):
"There is a joint outcome, consisting of a stage-1 outcome, stage-3 outcomes for all parts, and
draws `ξ_R, …, ξ_3`, such that:
(1) `X' ≤ 3 E X'`;
(2) the stage-3 labels of every part lie in that part's good event: the event of Lemma s4:lemTPV
for every standalone pre-part (with the data of step (1) of Construction s6:consOrder); the event
of Lemma s4:lemPV as used in Lemma s5:lemChild for every non-demoted light part; and the event of
Theorem s4:thmVXp as used in Lemma s5:lemDemoted for every demoted light part;
(3) at every round `3 ≤ l ≤ R`, `ξ_l` lies in the event of Construction s7:consRound(f).
Consequently `copies_l ≤ 4(X_{V,l} + det_l)` and `pay^rd_l ≤ 4(n/(256M_l^3) + 5.5 nM_l/Hcd_l)`.
Such an outcome is obtained as follows. (i) Choose the stage-1 outcome in `{X' ≤ 3E X'}`; stage 2
is then determined. (ii) For every part, choose its stage-3 labels in its good event. (iii) For
`l = R, R−1, …, 3` in turn: run steps (1)–(3) of Construction s6:consOrder at round `l`, which are
deterministic given the past; draw `ξ_l` and choose it in the event of Construction
s7:consRound(f); build `Q_l`, fix `Dec_l`, lift it, and record `LentJV_l` (step (4) of
Construction s6:consOrder). (iv) At rounds 2 and 1, run steps (1)–(2) of Construction
s6:consOrder; here `J_2 = J_1 = ∅`."

Formal reading (T0 OO-PROCEDURAL, OO-SUPP, OO-STAGE3-DETERMINISTIC; TRIAGE §2.8, §2.10).
There is no Lean object "joint outcome": the procedure is realized by the MIX-C chain and by the
J-consumer, which picks its own `ξ_l` (`Rules.xiChosen`, a choice in the event of (f) whenever
that event has an outcome of positive weight). The lemma becomes:
* (1) + step (i): `OneOutcomeStage1Statement`: there is a stage-1 outcome **of positive weight**
  (`ω ∈ (Stage1.law G run).supp`, needed by the s5/s6 Specs that quantify over the support) with
  `X'(ω) ≤ 3 E X'`.
* (2) + step (ii): no Lean statement. The stage-3 Specs s4:lemTPV, s4:lemPV, s4:thmVXp (and
  s5:lemChild, s5:lemDemoted) are deterministic existence statements (TRIAGE §2.8: "the TeX
  conclusions are label-free"; the good events are proof-internal), so "the labels lie in the good
  events" has no content beyond the hypotheses of those Specs, which MIX-C discharges.
* (3) + step (iii): `OneOutcomeRoundStatement`: for **every** past (every stage-1 outcome of
  positive weight, every round `3 ≤ l ≤ R`, every `J` with `JPlusProps`, every valid rule) the
  event of (f) contains an outcome of positive weight of the round law (so a choice of `ξ_l` in
  it exists, "whatever happened before"), and on the event
  `copies_l ≤ 4(X_{V,l} + det_l)` and `pay^rd_l ≤ 4(n/(256M_l^3) + 5.5 nM_l/Hcd_l)`.
* Step (iv) (rounds 2, 1; `J_2 = J_1 = ∅`) is part of the MIX-C chain (no round step there).
* Setting: `EG.RunHyp N0 Dstar G run`, a designation `δ` with `IsDesignation run G δ`;
  `X' = XprimeOf run G δ`, `E` under `EG.Stage1.law G run`; `n = G.card`, `M_l = run.M G l`,
  `Hcd_l = EG.Quot.Hcd run G l`, `det_l = EG.Quot.detl run G l`,
  `X_{V,l} = EG.Quot.XVl run G ω.pool l`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s7:lemOneOutcome] (1), step (i): "Choose the stage-1 outcome in `{X' ≤ 3E X'}`" — there is a
stage-1 outcome of positive weight with `X' ≤ 3 E X'`. -/
def OneOutcomeStage1Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∃ ω ∈ (Stage1.law G run).supp,
      (XprimeOf run G δ ω : ℝ) ≤
        3 * (Stage1.law G run).expect (fun ω' => (XprimeOf run G δ ω' : ℝ))

/-- [s7:lemOneOutcome] (3), step (iii): "at every round `3 ≤ l ≤ R`, `ξ_l` lies in the event of
Construction s7:consRound(f). Consequently `copies_l ≤ 4(X_{V,l} + det_l)` and
`pay^rd_l ≤ 4(n/(256M_l^3) + 5.5 nM_l/Hcd_l)`" — for every past, the event of (f) contains an
outcome of positive weight, and the two bounds hold on the event. -/
def OneOutcomeRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
    ∀ J : Finset (Sym2 V), JPlusProps run G δ (stageOf ω) l J →
    ∀ I : RoundInput V, I = pastOf run G δ ω l J → ∀ R : Rules I, R.Valid →
      (∃ ξ : Xi I.G I.M, 0 < (roundLaw I.G I.M).w ξ ∧ R.MarkovEvent ξ) ∧
      ∀ ξ : Xi I.G I.M, R.MarkovEvent ξ →
        (R.copies ξ : ℝ) ≤ 4 * ((XVl run G ω.pool l : ℝ) + detl run G l) ∧
        (R.payrd ξ : ℝ) ≤ 4 * ((G.card : ℝ) / (256 * (run.M G l : ℝ) ^ 3) +
          5.5 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l)

end EG.Spec
