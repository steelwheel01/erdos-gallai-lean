module

public import EG.Spec.Stage1.COLc

/-!
# Statement of Lemma COL (manuscript s3:lemCOL): the probability bounds and items (e), (g)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3b (`formal/work/p2s/s3b.md`; blueprint
`formal/work/p2/blueprint_s3b.md`, node `s3:lemCOL`). No proof here (blueprint: stage α through
Theorem 16*). Item (c) alone is the existing `EG.Spec.COLcStatement` (`EG/Spec/Stage1/COLc.lean`,
probe unit P4B, reused unchanged), which this file imports; the whole lemma is
`COLLemmaStatement` below. The existing `EG.Spec.COLaProbStatement` (`EG/Spec/Stage1/COLa.lean`)
and `EG.Spec.COLcIndexStatement` are proof-internal steps of this lemma (failure bound of (a),
per-index step of (c)), not the lemma.

Manuscript v6.1, `s3.tex`, Lemma [s3:lemCOL]:
"Assume condition s1:condG1. Let `Y` be an ancestor of round `r`, with the stage-1 lending data
of Definition s3:defCOL. If `r ≥ R-1`, then `k_lend(Y) = 0` and every statement below about lent
classes is vacuous.
(a) `Own_Y` and `Lend_Y` are `(ε_Y,s_Y/4)`-expanders on `V(Y)`. Every lent class, as a graph on
`V(Y)`, is an `(ε_Y, s_Y/(8k_lend(Y)))`-expander. If `Y` is light, every own class `R_{j,c}`,
`M`, as a graph on `V(Y)`, is a `(2^{-6}, s_r/(16k_own))`-expander.
(b) For all `r+2 ≤ l ≤ R` and `0 ≤ j < K^JS_l`, the class `LJS_{Y,l,j}` is
`(2^{12}L_Y^4, t^JS_l)`-path connected through `T_j(Y,l)`. By Lemma s3:lemMonotone(iii), one
application routes any multiset of pairs of distinct vertices in which every vertex lies in at
most `t^JS_l` pairs. …
(c) Let `Y` be light. Let `(V_{l,c,σ})_{(l,c,σ) ∈ I^U(Y)}` be random subsets of `V(Y)`,
independent of the stage-1 lending data of `Y`, such that each `V_{l,c,σ}` is a
`ρ_{l,c,σ}`-random subset of `V(Y)` with `ρ_{l,c,σ} ≥ 1/(12L_Y^5)`. The family may be dependent
across indices. Then, with probability at least `1 - |V(Y)|^{-2}/2` over the lending data and the
sets, every U-lent class `LU_{Y,l,c,σ}` is `(2^{12}L_Y^4,t_Y)`-path connected through
`V_{l,c,σ}`, where `t_Y = ⌈λ_r^{1.6}⌉` (Definition s3:defCOL).
(e) The own-device thresholds hold. If `Y` is standalone, then `s_Y/4 ≥ 2^{150}L_Y^{42}` and
`s_Y/4 ≥ 2^{146}L_Y^{38} log L_Y`. On (a), `Own_Y` is therefore a spanning
`(2^{-5},s_r/4)`-expander of `V(Y)` … If `Y` is light, then `s_r/2 ≥ 2^{151}L_Y^{38} log L_Y`; …
Moreover, on (a) every own class is a `(2^{-6},s')`-expander with
`s' := s_r/(16k_own) ≥ 2^{145}L_Y^{41}` and `2⌈L_Y^6⌉ ≤ s'`.
(g) (COL(g).) The consumers listed in Definition s3:defCOL are exclusive. The own classes
partition `Own_Y`, and if `r ≤ R-2`, the lent classes are pairwise edge-disjoint and partition
`Lend_Y`. So no edge of `H_Y` is available to two consumers, and every lent edge that its
consumer does not use is junk for `Y`'s own device. If `r ≥ R-1`, then `Lend_Y` has no classes,
and all of `Lend_Y` is junk for `Y`'s own device (Definition s3:defCOL, Consumers).
Items (a), (b) and (e) hold simultaneously with probability at least `1 - |V(Y)|^{-2}/2` over
the stage-1 lending data of `Y`. For every family as in (c), items (a), (b), (c) and (e) hold
simultaneously with probability at least `1 - |V(Y)|^{-2}`. Item (g) always holds. …"

Formal reading (Stage-1 layer, design note `formal/work/p2d/stage1.md`; the event predicates
`EG.Stage1.COLa/COLb/COLc/COLe/COLg` of the locked `EG/Defs/Stage1/COL.lean`; same conventions as
`COLcStatement`).
* Hypotheses: Γ1 and a valid run (TRIAGE §2.6: `Gamma1 D ∧ run.Valid G D`); `Y` any ancestor
  (`Y ∈ run.ancestors G`, round `r = Y.1`). (`COLaProbStatement`/`COLcStatement` also assume
  `D_* ≤ d_1`; this follows from `run.Valid` as soon as an ancestor exists, so it is omitted.)
* "with the stage-1 lending data of `Y`": any finite probability space `μ` and random variable
  `D : Ω → COLOut G run Y` with law `colLaw G run Y` (`μ.map D = Stage1.colLaw G run Y`), so that
  the statement applies on the global stage-1 space.
* "If `r ≥ R-1`, then `k_lend(Y) = 0`": `run.R ≤ Y.1 + 1 → Stage1.klend G run Y = 0`. "Every
  statement … about lent classes is vacuous" needs no statement: `lentIdx`, `I^U`, `I^JS` and the
  rounds `r+2 ≤ l ≤ R` are then empty, so the lent-class clauses of `COLa`, `COLb`, `COLc` hold.
* (e) is deterministic: `Stage1.COLe G run Y` (the inequalities only; its consequences "on (a)"
  are clauses of `COLa`). It is also conjoined inside the events, as the text says "(a), (b) and
  (e) hold simultaneously".
* (g): the partition facts `Stage1.COLg`. "Item (g) always holds" is read on the support of the
  law of the lending data (`ω ∈ (colLaw G run Y).supp`): off the support an edge of `Lend_Y` may
  carry an index outside `lentIdx` (docstring of `COLg`). The consumer-exclusivity sentence is a
  design rule of s4–s6, not a property of the data (blueprint COL-CONSUMERS-NOT-A-PROPERTY).
* The joint probability of (a), (b), (c), (e) is stated "for every family as in (c)": `Y` light,
  written `Y ∈ run.lightParts G` as in `COLcStatement` (for an ancestor this is equivalent to
  `run.isLight G Y.1 Y.2`, `EG.HB.Run.mem_lightParts`),
  `Vs : Ω → LentTag → Finset V` jointly independent of `D` (`μ.IndepFun D Vs`), each `Vs · i`
  (`i ∈ I^U(Y)`) a `ρ i`-random subset of `V(Y)` with deterministic `ρ i ≥ 1/(12L_Y^5)`.
* `N = |V(Y)| = (run.ancVerts G Y).card`; `N^{-2}` is an integer power.
* The sentences "By Lemma s3:lemMonotone(iii), one application routes …" in (b) and "On (a),
  `Own_Y` is therefore …" in (e) are consequences of the definitions (Def 7 multiset form) and of
  (a), and are not restated.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u v

/-- [s3:lemCOL] Lemma COL, the deterministic items and the probability bounds: "If `r ≥ R-1`, then
`k_lend(Y) = 0` …; (e) The own-device thresholds hold. … (g) … The own classes partition `Own_Y`,
and if `r ≤ R-2`, the lent classes are pairwise edge-disjoint and partition `Lend_Y`. … Items
(a), (b) and (e) hold simultaneously with probability at least `1 - |V(Y)|^{-2}/2` over the
stage-1 lending data of `Y`. For every family as in (c), items (a), (b), (c) and (e) hold
simultaneously with probability at least `1 - |V(Y)|^{-2}`. Item (g) always holds." (Under Γ1,
for every ancestor `Y` of a valid run.) -/
def COLStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1 Dstar → run.Valid G Dstar →
    ∀ Y ∈ run.ancestors G,
      (run.R ≤ Y.1 + 1 → Stage1.klend G run Y = 0) ∧
      Stage1.COLe G run Y ∧
      (∀ ω ∈ (Stage1.colLaw G run Y).supp, Stage1.COLg G run Y ω) ∧
      (∀ (Ω : Type v) (μ : FinDist Ω) (D : Ω → Stage1.COLOut G run Y),
        μ.map D = Stage1.colLaw G run Y →
        1 - ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 2 ≤
          μ.prob {ω | Stage1.COLa G run Y (D ω) ∧ Stage1.COLb G run Y (D ω) ∧
            Stage1.COLe G run Y}) ∧
      (Y ∈ run.lightParts G →
        ∀ (Ω : Type v) (μ : FinDist Ω) (D : Ω → Stage1.COLOut G run Y)
          (Vs : Ω → Stage1.LentTag → Finset V) (ρ : Stage1.LentTag → ℝ),
          μ.map D = Stage1.colLaw G run Y →
          (∀ i ∈ Stage1.IU G run Y,
            μ.IsRSubset (fun ω => Vs ω i) (run.ancVerts G Y) (ρ i) ∧
              1 / (12 * run.LY G Y ^ 5) ≤ ρ i) →
          μ.IndepFun D Vs →
          1 - ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) ≤
            μ.prob {ω | Stage1.COLa G run Y (D ω) ∧ Stage1.COLb G run Y (D ω) ∧
              Stage1.COLc G run Y (D ω) (Vs ω) ∧ Stage1.COLe G run Y})

/-- [s3:lemCOL] Lemma COL, all items: `COLStatement` together with item (c) (`COLcStatement`:
"with probability at least `1 - |V(Y)|^{-2}/2` over the lending data and the sets, every U-lent
class `LU_{Y,l,c,σ}` is `(2^{12}L_Y^4,t_Y)`-path connected through `V_{l,c,σ}`"). `COLcStatement`
carries the extra hypothesis `D_* ≤ d_1`, implied by `run.Valid` once an ancestor exists. -/
def COLLemmaStatement : Prop :=
  COLStatement.{u, v} ∧ COLcStatement.{u, v}

end EG.Spec
