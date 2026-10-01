module

public import EG.Defs.Quot.Cand
public import EG.Defs.Chain.StageInst
public import EG.Defs.Gamma.Full

/-!
# The claims made inside Definition "Candidates and JV-bad ports" (manuscript s7:defCand)

Statement file (`EG/Spec/**`), chunk s7a (P2 Specs). Status note: `formal/work/p2s/s7a.md`.
Definitions: `EG.Quot.cand`, `EG.Quot.Hcd`, `EG.Quot.candMean`, `EG.Quot.JVBad`
(`EG/Defs/Quot/Cand.lean`, locked). The remark "`½E|Cand_l(u)| ≥ Hcd_l` … Consequently every JV-good
port has `|Cand_l(u)| ≥ Hcd_l`" is Lemma s7:lemCand (ii), (iv) (`EG.Spec.CandCountStatement`,
`EG/Spec/Quot/Cand.lean`); "JV-badness is a deterministic function of stage 1" is definitional
(`JVBad` reads only the stage data and the pool labels).

Manuscript v6.1, `s7.tex`, Definition [s7:defCand]:
"Let `u` be a classed port of round `l ≥ 3`, with class `Y := Y(u)` of round `r := r(u) ≤ l−2`.
Its *candidate set* is `Cand_l(u) := {w ∈ Pool_{l,r(u)} : uw ∈ LJV_{Y,l}}`. Since
`LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)` and `H_Y` is a graph on `V(Y)`, automatically
`Cand_l(u) ⊆ N_{H_Y}(u)` and `N_{H_Y}(u) ⊆ V(Y)`. The candidate sets are always taken in the class
graph `H_{Y(u)}` itself; this is used in Lemma MULT below."
Section setting of s7: "For a classed port `u` of round `l` (that is, `u ∈ Q_Z` for some
`Z ∈ Std_l`) we write `Y(u)` for its class and `r(u)` for the round of `Y(u)`; since
`Y(u) ∈ anc_l(u)` we have `r(u) ≤ l−2` and `u ∈ V(Y(u))`."

Formal reading (as in `EG/Spec/Quot/Cand.lean`).
* Setting: `EG.RunHyp N0 Dstar G run` and a designation `δ` with `IsDesignation run G δ`; "a classed
  port of round `l ≥ 3`" is `3 ≤ l` and `u ∈ Chain.classedPorts run G l`; `Y(u) = δ l u`, of round
  `r(u) = (δ l u).1`; the rounds of the run are `1, …, R`, so `1 ≤ r(u)` (ancestors are parts of
  rounds `1 ≤ r ≤ R`).
* The candidate set of a stage-1 outcome `ω` is `cand G δ (Sω ω) ω.pool l u`, where the stage-data
  record `Sω ω` has the JV-lent classes of `ω` (hypothesis `hS`, the same as in
  `CandCountStatement`); `N_{H_Y}(u) = (run.ancGraph G Y).nbrs u`, `V(Y) = run.ancVerts G Y`.
  The inclusions are claimed for every outcome.
* The consumer is the instantiation of the round input (`RoundInput.ofPast`, fields `cls_anc`,
  `cls_round`, `cls_mem` and `ljv_in` of `RoundInput.Valid`) and, through it, Lemma MULT
  (`MultRunStatement`: "`w ∈ Cand_l(u_i) ⊆ N_{H_{Y(u_i)}}(u_i) ⊆ V(Y(u_i))`").
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

/-- [s7:defCand] "Let `u` be a classed port of round `l ≥ 3`, with class `Y := Y(u)` of round
`r := r(u) ≤ l−2`. … Since `LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)` and `H_Y` is a graph on `V(Y)`,
automatically `Cand_l(u) ⊆ N_{H_Y}(u)` and `N_{H_Y}(u) ⊆ V(Y)`." (With the section setting:
"since `Y(u) ∈ anc_l(u)` we have `r(u) ≤ l−2` and `u ∈ V(Y(u))`.") -/
def CandSubsetStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : Run V) (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ (Sω : Stage1.Outcome G run → StageData V),
      (∀ ω Y l, (Sω ω).ljv Y l = (Stage1.LJV G run Y (ω.colAt Y) l).edges) →
    ∀ (l : ℕ) (u : V), 3 ≤ l → u ∈ classedPorts run G l →
      -- the class `Y(u)` is an ancestor of round `1 ≤ r(u) ≤ l − 2` with `u ∈ V(Y(u))`
      δ l u ∈ run.ancestors G ∧ 1 ≤ (δ l u).1 ∧ (δ l u).1 + 2 ≤ l ∧
      u ∈ run.ancVerts G (δ l u) ∧
      -- `Cand_l(u) ⊆ N_{H_Y}(u)` and `N_{H_Y}(u) ⊆ V(Y)`
      ∀ ω : Stage1.Outcome G run,
        cand G δ (Sω ω) ω.pool l u ⊆ (run.ancGraph G (δ l u)).nbrs u ∧
        (run.ancGraph G (δ l u)).nbrs u ⊆ run.ancVerts G (δ l u)

end EG.Spec
