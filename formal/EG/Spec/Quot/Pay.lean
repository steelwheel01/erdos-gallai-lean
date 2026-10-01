module

public import EG.Defs.Probe.S7b.Outcome
public import EG.Defs.Gamma.Full

/-!
# Statement of Lemma "payments" (manuscript s7:lemPay)

Statement file (`EG/Spec/**`) of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`); blueprint s7b,
node `s7:lemPay` (Tier-2 Spec over the s7a round-step Defs, S7-ROUNDSTEP-IN-DEFS).

Manuscript v6.1, `s7.tex`, Lemma [s7:lemPay] (Payments):
"For every past and every `3 ≤ l ≤ R` the following hold.
(a1) `|J^lost_l| ≤ (M_l − 1)|Lost_l|`.
(a2) The number of items with a vertex in `Pool_l` is at most `Σ_{v∈Pool_l} ω_l(v)`, where
`ω_l(v) := c^agg_{v,l}` if `v ∈ D_l` and `ω_l(v) := M_l` otherwise.
(a3) The number of items with a JV-bad port end is at most `M_l − 1` times the number of JV-bad
classed ports of round `l`.
(b) Every fresh centre has at most one unpaired fresh leg per round, so the number of unpaired
fresh legs over all rounds is at most `Σ_{l,Z}|F_Z| ≤ 2n`.
(c) `E[SDR-failure payments | Past_l] ≤ n(M_l − 1)(4M_l)^{-4} ≤ n/(256M_l^3)`, and
`E[loop-paid edges | Past_l] ≤ 2·(2/Hcd_l)·#{PAR objects} ≤ 5.5 nM_l/Hcd_l`.
(d) If `ξ_l` lies in the event of Construction s7:consRound(f), then
`pay^rd_l ≤ 4(n/(256M_l^3) + 5.5 nM_l/Hcd_l) ≤ 2n/M_l`; if this holds at every round, then
`Σ_l pay^rd_l ≤ 9n/D_*`.
(e) No other item is paid. In particular, no item is paid because of a coincidence of junctions
at an ultra hub, and no item is paid for a concentrated pair."

Formal reading (TRIAGE §2.6, §2.10; blueprint s7b PAY-*; design note work/p2d/quot.md).
* Setting: `EG.RunHyp N0 Dstar G run`, a designation `δ` with `IsDesignation run G δ`, a stage-1
  outcome `ω ∈ (Stage1.law G run).supp` (its stage data `stageOf ω`, its pool labels `ω.pool`).
* **"For every past"** at round `l`: every `J` with `JPlusProps run G δ (stageOf ω) l J` (the
  past enters the round step only through `J_l`, TRIAGE §2.9/§2.10), the past as read by the round
  step `I = pastOf run G δ ω l J` (`RoundInput.ofPast`), and **every** valid choice
  `R : Rules I`, `R.Valid`, of the fixed rules of s7:consRound (stronger than the one chosen rule
  `RoundInput.chosenRules`, which is valid when the past is).
* `M_l = run.M G l`, `n = G.card`, `Hcd_l = EG.Quot.Hcd run G l` (`= I.Hcd` by `rfl`),
  `Lost_l = EG.Chain.lostRound`, `Pool_l = Stage1.poolL G ω.pool l`, `ω_l(v) = poolWeight`,
  the JV-bad classed ports of round `l` = `jvBadPorts` (Defs, `EG/Defs/Quot/Xprime.lean`).
  `M_l − 1` is written in `ℝ` (no truncated subtraction).
* Items and payments are the Defs of `EG/Defs/Quot/Round.lean`: `I.Jlost` (`J^lost_l`),
  `I.paidPool` (items with a vertex in `Pool_l`), `I.paidJVBad` (items with a JV-bad port end),
  `R.unpairedLegs` (the unpaired fresh legs of (b)), `R.sdrPaid L` (the edges paid for SDR
  failures, a function of the lists `L`), `R.loopPaid ξ` (the loop-paid edges of (e3)),
  `R.payrd ξ` (`pay^rd_l`, the number of edges paid in (d) and (e3)), `R.parObjs` (the PAR
  objects), `R.MarkovEvent ξ` (the event of (f)).
* `E[· | Past_l]` is the expectation under the round law `roundLaw I.G I.M` with the past `I`
  fixed (`EG/Defs/Quot/Schedule.lean`).
* (b) and (d) are stated per round (`PayStatement`: at most one unpaired leg at each fresh centre,
  at most `Σ_{Z∈Std_l}|F_Z|` legs at round `l`; `pay^rd_l ≤ … ≤ 2n/M_l` on the event) and summed
  over the rounds `3 ≤ l ≤ R` (`PayGlobalStatement`), for any family of admissible J-sets, valid
  rules and draws in the events (blueprint PAY-PER-ROUND). "`Σ_{l,Z}|F_Z|`" runs over all rounds
  `1 ≤ l ≤ R` (as in s2:propParentless (i)).
* (e) "No other item is paid": the paid single edges of the round step are exactly the union of
  the six categories (a1), (a2), (a3), (b), (d), (e3). In the Defs the paid set `R.paidEdges ξ` is
  *defined* as this union (blueprint PAY-E-INSPECTION), so (e) is the defining equation (`rfl` in
  the locked Defs; checked); the
  "in particular" sentence is commentary (there is no payment category for ultra-hub
  coincidences or concentrated pairs).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

universe u

/-- [s7:lemPay] (a1)–(e), per round: "For every past and every `3 ≤ l ≤ R` … (a1)
`|J^lost_l| ≤ (M_l − 1)|Lost_l|`. (a2) The number of items with a vertex in `Pool_l` is at most
`Σ_{v∈Pool_l} ω_l(v)` … (a3) The number of items with a JV-bad port end is at most `M_l − 1` times
the number of JV-bad classed ports of round `l`. (b) Every fresh centre has at most one unpaired
fresh leg per round … (c) `E[SDR-failure payments | Past_l] ≤ n(M_l − 1)(4M_l)^{-4} ≤
n/(256M_l^3)`, and `E[loop-paid edges | Past_l] ≤ 2·(2/Hcd_l)·#{PAR objects} ≤ 5.5 nM_l/Hcd_l`.
(d) If `ξ_l` lies in the event of Construction s7:consRound(f), then
`pay^rd_l ≤ 4(n/(256M_l^3) + 5.5 nM_l/Hcd_l) ≤ 2n/M_l` … (e) No other item is paid." -/
def PayStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ l : ℕ, 3 ≤ l → l ≤ run.R →
    ∀ J : Finset (Sym2 V), JPlusProps run G δ (stageOf ω) l J →
    ∀ I : RoundInput V, I = pastOf run G δ ω l J → ∀ R : Rules I, R.Valid →
      -- (a1)
      (I.Jlost.card : ℝ) ≤
          ((run.M G l : ℝ) - 1) * ((lostRound run G δ (stageOf ω) l).card : ℝ) ∧
      -- (a2)
      I.paidPool.card ≤ ∑ v ∈ Stage1.poolL G ω.pool l, poolWeight run G δ l v ∧
      -- (a3)
      (I.paidJVBad.card : ℝ) ≤
          ((run.M G l : ℝ) - 1) * ((jvBadPorts run G δ (stageOf ω) ω.pool l).card : ℝ) ∧
      -- (b), per round
      (∀ x ∈ I.fresh, (R.unpairedLegs.filter (fun e => x ∈ e)).card ≤ 1) ∧
      R.unpairedLegs.card ≤ ∑ a ∈ run.Std G l, (run.fresh G l a).card ∧
      -- (c), SDR failures
      (roundLaw I.G I.M).expect (fun ξ => ((R.sdrPaid ξ.1).card : ℝ)) ≤
          (G.card : ℝ) * ((run.M G l : ℝ) - 1) / (4 * (run.M G l : ℝ)) ^ 4 ∧
      (G.card : ℝ) * ((run.M G l : ℝ) - 1) / (4 * (run.M G l : ℝ)) ^ 4 ≤
          (G.card : ℝ) / (256 * (run.M G l : ℝ) ^ 3) ∧
      -- (c), loops
      (roundLaw I.G I.M).expect (fun ξ => ((R.loopPaid ξ).card : ℝ)) ≤
          2 * (2 / Hcd run G l) * (R.parObjs.card : ℝ) ∧
      2 * (2 / Hcd run G l) * (R.parObjs.card : ℝ) ≤
          5.5 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l ∧
      -- (d), per round
      (∀ ξ : Xi I.G I.M, R.MarkovEvent ξ →
          (R.payrd ξ : ℝ) ≤ 4 * ((G.card : ℝ) / (256 * (run.M G l : ℝ) ^ 3) +
            5.5 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l)) ∧
      4 * ((G.card : ℝ) / (256 * (run.M G l : ℝ) ^ 3) +
          5.5 * (G.card : ℝ) * (run.M G l : ℝ) / Hcd run G l) ≤
        2 * (G.card : ℝ) / (run.M G l : ℝ) ∧
      -- (e)
      ∀ ξ : Xi I.G I.M, R.paidEdges ξ =
        I.Jlost ∪ I.paidPool ∪ I.paidJVBad ∪ R.unpairedLegs ∪ R.sdrPaid ξ.1 ∪ R.loopPaid ξ

/-- [s7:lemPay] (b), (d), over all rounds: "the number of unpaired fresh legs over all rounds is
at most `Σ_{l,Z}|F_Z| ≤ 2n`" and "if this holds at every round, then `Σ_l pay^rd_l ≤ 9n/D_*`".
For a family of pasts (`J_l` with `JPlusProps` at every round `3 ≤ l ≤ R`), any valid rules `R_l`
at every round, and (for (d)) any draws `ξ_l` in the events of Construction s7:consRound(f) at
every round. -/
def PayGlobalStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ Js : ℕ → Finset (Sym2 V),
    (∀ l ∈ Finset.Icc 3 run.R, JPlusProps run G δ (stageOf ω) l (Js l)) →
    ∀ Rs : (l : ℕ) → Rules (pastOf run G δ ω l (Js l)),
    (∀ l ∈ Finset.Icc 3 run.R, (Rs l).Valid) →
      -- (b), over all rounds
      (∑ l ∈ Finset.Icc 3 run.R, (Rs l).unpairedLegs.card ≤
          ∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card ∧
        ((∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card : ℕ) : ℝ) ≤
          2 * (G.card : ℝ)) ∧
      -- (d), over all rounds
      ∀ ξs : (l : ℕ) → Xi G (run.M G l),
        (∀ l ∈ Finset.Icc 3 run.R, (Rs l).MarkovEvent (ξs l)) →
        ∑ l ∈ Finset.Icc 3 run.R, ((Rs l).payrd (ξs l) : ℝ) ≤ 9 * (G.card : ℝ) / Dstar

end EG.Spec
