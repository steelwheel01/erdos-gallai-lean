module

public import EG.Defs.Chain.Lending
public import EG.Defs.Stage1.Law

/-!
# The stage data of a stage-1 outcome, and the stage-1 facts s6/s7 read from it

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Companion of `EG.Defs.Chain.Lending` (decision D-DES-1 of `formal/work/p2d/design.md`, fix
round 1, review item MAJOR-1). Namespace `EG.Chain`.

Manuscript v6.1, [s6:defLending]: "Fix a valid run, a designation `δ` and a stage-1 outcome: the
colourings and JS labels of Definition [s3:defCOL], and the zones of Definition [s5:defZones]."
The record `EG.Chain.StageData` bundles exactly the objects of such an outcome that s6 reads. This
file adds
* **`StageData.ofOutcome ω demoted dem lp`**: the record of a stage-1 outcome
  `ω : EG.Stage1.Outcome G run` (the instantiation contract of D-DES-1): `colA`/`colB` are the
  events `EG.Stage1.COLa`/`COLb` of [s3:lemCOL] (a)/(b) at the lending data of `Y` in `ω`, `lab`
  the JS labels `ω.labAt`, `own`/`ljs`/`ljv` the edge sets of the classes `Own_Y`, `LJS_{Y,l,j}`,
  `LJV_{Y,l}` of [s3:defCOL] (i), (ii). The s5 status data (`demoted`, `dem`, `lp` of
  [s5:defStages]) are **parameters** until `EG/Defs/Light/Stages.lean` exists; the s5 layer then
  instantiates them (a function of `ω`), without changing this definition.
* **`StageData.Coherent run G S`**: the stage-1 facts about the record that the s6/s7 statements
  use (JS-LC, s6:lemLent, `JConsumer` "of `G`", s7 `RoundInput.ofPast`), as one named, reviewed
  predicate. Its fields are sentences of [s3:defCOL] and [s3:lemCOL] (a), (b), (g), read on the
  record. It holds for the record of every stage-1 outcome of positive weight
  (`EG.Chain.coherent_ofOutcome` in `EG.Lib.Chain.StageInst`), so a statement
  "`∀ S, S.Coherent run G → …`" transfers to every `ω ∈ (Stage1.law G run).supp`.
  - `colB_conn` is `Stage1.COLb` in exactly its form (with `Stage1.lateRounds`, `Stage1.KJS`,
    `Stage1.tJS`, `run.LY`); the class `LJS_{Y,l,j}` "regarded as a graph with vertex set `V(Y)`"
    is `H_Y.restrictEdges (S.ljs Y l j)`, which is `Stage1.LJS` itself on the instantiation;
  - `colA_own`, `colA_ljs`, `colA_ljv` are the conjuncts of `Stage1.COLa` about `Own_Y`, the
    JS-lent classes and the JV-lent classes;
  - `own_sub`, `ljs_sub`, `ljv_sub`: every class is a set of edges of `H_Y`;
  - `ljs_disj`, `ljv_disj`, `ljs_ljv_disj`, `own_ljs_disj`, `own_ljv_disj`: the classes of one
    ancestor are pairwise edge-disjoint ([s3:lemCOL] (g); classes of distinct ancestors are
    disjoint by s2:propStructure(iii), a run fact, and are not repeated here);
  - `ljs_eq_empty`, `ljv_eq_empty`: there are no JS classes outside `r(Y)+2 ≤ l ≤ R`,
    `j < K^JS_l`, and no JV classes outside `r(Y)+2 ≤ l ≤ R` (the index families of
    [s3:defCOL] (ii); on the support every lent index lies in them). This is what makes
    `LJV_{Y,l}` disjoint from `E_l(Z)` for `r(Y)+2 > l` (review item MINOR-4);
  - `lab_dom`, `lab_lt`: a label `≠ *` sits at a site `r(Y)+2 ≤ l ≤ R`, `y ∈ V(Y)`, and has value
    `< K^JS_l` ([s3:defCOL] (iv)).

The record `StageData` itself keeps no axioms (D-DES-1): definitions of s6 are functions of an
arbitrary record, and statements that need stage-1 facts assume `S.Coherent run G`.
-/

@[expose] public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V]

/-- [s6:defLending] "a stage-1 outcome: the colourings and JS labels of Definition [s3:defCOL]"
as read by s6: the stage data of the stage-1 outcome `ω` ([s3:lemCOL] (a), (b) events, JS labels
`lab_{Y,l}`, classes `Own_Y`, `LJS_{Y,l,j}`, `LJV_{Y,l}` as edge sets), with the s5 status data
`demoted`, `dem`, `lp` ([s5:defStages]) as parameters. -/
noncomputable def StageData.ofOutcome {G : FGraph V} {run : Run V} (ω : Stage1.Outcome G run)
    (demoted : PartId → Prop) (dem lp : ℕ) : StageData V where
  colA Y := Stage1.COLa G run Y (ω.cOutAt Y)
  colB Y := Stage1.COLb G run Y (ω.cOutAt Y)
  demoted := demoted
  lab Y l y := ω.labAt Y l y
  own Y := (Stage1.Own G run Y (ω.colAt Y)).edges
  ljs Y l j := (Stage1.LJS G run Y (ω.colAt Y) l j).edges
  ljv Y l := (Stage1.LJV G run Y (ω.colAt Y) l).edges
  dem := dem
  lp := lp

/-- The stage-1 facts about a stage-data record that the s6/s7 statements read (see the module
docstring; each field quotes its source). Holds for `StageData.ofOutcome ω …` for every stage-1
outcome `ω` of positive weight (`EG.Chain.coherent_ofOutcome`). -/
structure StageData.Coherent (run : Run V) (G : FGraph V) (S : StageData V) : Prop where
  /-- [s3:lemCOL] (b) "For all `r+2 ≤ l ≤ R` and `0 ≤ j < K^JS_l`, the class `LJS_{Y,l,j}` is
  `(2^{12}L_Y^4, t^JS_l)`-path connected through `T_j(Y,l)`", whenever the COL(b) events hold for
  `Y` (the form of `EG.Stage1.COLb`; the class as a graph on `V(Y)`). -/
  colB_conn : ∀ Y, S.colB Y → ∀ l ∈ Stage1.lateRounds run Y.1, ∀ j < Stage1.KJS G run l,
    ((run.ancGraph G Y).restrictEdges (S.ljs Y l j)).IsPathConnected
      (2 ^ 12 * run.LY G Y ^ 4) (Stage1.tJS G run l) (Tj run G S Y l j)
  /-- [s3:lemCOL] (a) "`Own_Y` … [is an] `(ε_Y, s_Y/4)`-expander on `V(Y)`", whenever the COL(a)
  events hold for `Y`. -/
  colA_own : ∀ Y, S.colA Y →
    ((run.ancGraph G Y).restrictEdges (S.own Y)).IsExpander (run.ancEps G Y) (run.ancS G Y / 4)
  /-- [s3:lemCOL] (a) "Every lent class, as a graph on `V(Y)`, is an
  `(ε_Y, s_Y/(8k_lend(Y)))`-expander": the JS-lent classes `LJS_{Y,l,j}`
  (`r+2 ≤ l ≤ R`, `j < K^JS_l`). -/
  colA_ljs : ∀ Y, S.colA Y → ∀ l ∈ Stage1.lateRounds run Y.1, ∀ j < Stage1.KJS G run l,
    ((run.ancGraph G Y).restrictEdges (S.ljs Y l j)).IsExpander (run.ancEps G Y)
      (run.ancS G Y / (8 * Stage1.klend G run Y))
  /-- [s3:lemCOL] (a) the same for the JV-lent classes `LJV_{Y,l}` (`r+2 ≤ l ≤ R`). -/
  colA_ljv : ∀ Y, S.colA Y → ∀ l ∈ Stage1.lateRounds run Y.1,
    ((run.ancGraph G Y).restrictEdges (S.ljv Y l)).IsExpander (run.ancEps G Y)
      (run.ancS G Y / (8 * Stage1.klend G run Y))
  /-- [s3:defCOL] (i) "Every edge of `H_Y` independently lies in `Own_Y` or in `Lend_Y`":
  `Own_Y ⊆ E(H_Y)`. -/
  own_sub : ∀ Y, S.own Y ⊆ (run.ancGraph G Y).edges
  /-- [s3:defCOL] (ii) `LJS_{Y,l,j} ⊆ Lend_Y ⊆ E(H_Y)`. -/
  ljs_sub : ∀ Y l j, S.ljs Y l j ⊆ (run.ancGraph G Y).edges
  /-- [s3:defCOL] (ii) `LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)`. -/
  ljv_sub : ∀ Y l, S.ljv Y l ⊆ (run.ancGraph G Y).edges
  /-- [s3:lemCOL] (g) "the lent classes are pairwise edge-disjoint": distinct JS-indices. -/
  ljs_disj : ∀ Y l j l' j', (l, j) ≠ (l', j') → Disjoint (S.ljs Y l j) (S.ljs Y l' j')
  /-- [s3:lemCOL] (g) "the lent classes are pairwise edge-disjoint": distinct JV-indices. -/
  ljv_disj : ∀ Y l l', l ≠ l' → Disjoint (S.ljv Y l) (S.ljv Y l')
  /-- [s3:lemCOL] (g) "the lent classes are pairwise edge-disjoint": a JS- and a JV-index. -/
  ljs_ljv_disj : ∀ Y l j l', Disjoint (S.ljs Y l j) (S.ljv Y l')
  /-- [s3:defCOL] (i) `Own_Y` and `Lend_Y ⊇ LJS_{Y,l,j}` are disjoint. -/
  own_ljs_disj : ∀ Y l j, Disjoint (S.own Y) (S.ljs Y l j)
  /-- [s3:defCOL] (i) `Own_Y` and `Lend_Y ⊇ LJV_{Y,l}` are disjoint. -/
  own_ljv_disj : ∀ Y l, Disjoint (S.own Y) (S.ljv Y l)
  /-- [s3:defCOL] (ii) the JS-indices are `I^JS(Y) = {(l,j) : r+2 ≤ l ≤ R, 0 ≤ j < K^JS_l}`: there
  is no JS class outside this range. -/
  ljs_eq_empty : ∀ Y l j, ¬ (l ∈ Stage1.lateRounds run Y.1 ∧ j < Stage1.KJS G run l) →
    S.ljs Y l j = ∅
  /-- [s3:defCOL] (ii) the JV-indices are `I^JV(Y) = {l : r+2 ≤ l ≤ R}`: there is no JV class
  outside this range. -/
  ljv_eq_empty : ∀ Y l, l ∉ Stage1.lateRounds run Y.1 → S.ljv Y l = ∅
  /-- [s3:defCOL] (iv) labels are drawn "for every `r+2 ≤ l ≤ R` and every `y ∈ V(Y)`": a label
  `≠ *` sits at such a site. -/
  lab_dom : ∀ Y l y, S.lab Y l y ≠ none →
    l ∈ Stage1.lateRounds run Y.1 ∧ y ∈ run.ancVerts G Y
  /-- [s3:defCOL] (iv) "`lab_{Y,l}(y) ∈ {*} ∪ {0,1,…,K^JS_l − 1}`". -/
  lab_lt : ∀ Y l y j, S.lab Y l y = some j → j < Stage1.KJS G run l

end EG.Chain
