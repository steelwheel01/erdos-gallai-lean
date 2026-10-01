module

public import EG.Defs.Chain.JSet
public import EG.Defs.Chain.StageInst
public import EG.Defs.Gamma.Full
public import EG.Defs.Objects

/-!
# Statement of Lemma JS-LC, with the J-interface of Lemma J⁺ (manuscript s6:lemJSLC, s6:lemJplus)

Statement file of probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`).

Manuscript v6.1, Lemma JS-LC [s6:lemJSLC] ("one round `l ≥ 3`; cherry split for giant pairs"):
"Fix a valid run, a designation `δ`, a stage-1 outcome with its stage-2 data (Definition
s6:defLending), and a round `3 ≤ l ≤ R`. For every `Z ∈ Std_l` let `B_Z ⊆ E_l(Z)` be a set of
edges, each of which has an end in `Q*_Z`. (In the assembly `B_Z := E^Q(Z)`, which has this
property by (T1) of Lemma s4:lemTPV.)
Hypothesis: no edge of any class `LJS_{Y,l,j}` (`0 ≤ j < K^JS_l`, `Y` a lend-good ancestor of a
round `≤ l − 2`) has been used.
Then there are a set `J_l ⊆ ⋃_Z B_Z` and a set `LentJS_l ⊆ ⋃_{Y,j} LJS_{Y,l,j}` such that
`⋃_Z B_Z ∪ LentJS_l` is partitioned into the single edges of `J_l` and at most
`126 n/M_l + 1.5 Σ_{(Y,l) giant} m_{Y,l}` cycles.
Here the sum is over the ancestors `Y` for which the pair `(Y,l)` is giant (Definition
s6:defDesign), and `m_{Y,l}` is the maximal class-`Y` degree of Definition s6:defDesign. … Each
cycle consists of edges of `⋃_Z B_Z` and edges of `⋃_j LJS_{Y,l,j}` for a single ancestor `Y`.
Moreover (s6:eqJbound)
`|J_l| ≤ Σ_{h∈D_l} c^agg_{h,l} + Σ_{Z∈Std_l} [Σ_{x∈F_Z} c_x(Z) + (M_l − 1)|Lost_Z| + ½ Σ_{u∈Q_Z} c_pp(u)]`.
… The edges of `⋃_{Y,j} LJS_{Y,l,j}` outside `LentJS_l`, among them the returned edges inside the
graphs `G[T_j(Y,l)]`, are not used; they are junk for their owner `Y`."

Manuscript v6.1, Lemma J⁺ [s6:lemJplus]: "In Lemma s6:lemJSLC, the set `J_l` … Moreover
`J_l = J^lost_l ⊔ J^hub_l ⊔ J^fr_l ⊔ J^par_l` … (J1) … (J2) … (J3) … (i) … (ii) … (iii) … (iv) …
(v) …" (quoted in full in `EG.Chain.JPlusProps`, `EG/Defs/Chain/JSet.lean`).

Formal reading (TRIAGE §2.9: "JS-LC and J⁺ are one existential Spec, `JSLCStatement`, whose
conclusion contains `JPlusProps`"; design note `work/p2d/design.md`, "Notes for Spec authors"):
* **Setting.** `EG.RunHyp N0 Dstar G run` (TRIAGE §2.6: s6b's JS-LC takes `RunHyp`: Γ1, Γ3,
  `N0Cond`, `n ≥ N_0`, `d_1 ≥ D_*`, a valid run; the proof uses `M_l ≥ 2^{40}`, `P_{l−2} ≥ M_l^{13}`
  and `ν_l ≤ 2.74n/P_{l−2}` of s2:lemTower(b)); a designation `δ` with `IsDesignation run G δ`
  (quantified before the stage data, D-DES-2); "a stage-1 outcome with its stage-2 data" is a
  stage-data record `S : EG.Chain.StageData V` with `S.Coherent run G` (design note fix round 1,
  MAJOR-1: the statement then transfers to every stage-1 outcome of positive weight by
  `EG.Chain.coherent_ofOutcome`); a round `3 ≤ l ≤ R`.
* **Input.** `B : Addr → Finset (Sym2 V)`, read at the addresses `a ∈ Std_l` (`Z` is its address):
  `B a ⊆ E_l(Z)` and every edge of `B a` has an end `u ∈ Q*_Z` (`EG.Chain.qs`). `⋃_Z B_Z` is
  `(run.Std G l).biUnion B`.
* **The hypothesis "no edge of any class `LJS_{Y,l,j}` has been used"** is not a mathematical
  predicate (it is about the state of the assembly). It is encoded by giving JS-LC the whole
  classes: nothing is assumed, and the output `LentJS_l` may use every edge of every class
  (blueprint s6b JSLC-USED; the manuscript uses the hypothesis only in claim (d), "so the whole
  class is available"). The "not used before" obligation is discharged by the consumer (MIX-C (a),
  s6:lemLent (i)) through disjointness.
* **`LentJS_l ⊆ ⋃_{Y,j} LJS_{Y,l,j}`**: the union over the classes named in the hypothesis, i.e.
  `Y ∈ lendGoodAnc run G S l` ("`Y` a lend-good ancestor of a round `≤ l − 2`") and
  `j < K^JS_l = Stage1.KJS G run l`. This is the reading the consumers use (MIX-C (a): "JS-LC at
  round `l` uses only classes `LJS_{Y,l,·}` … of ancestors `Y` of rounds `≤ l − 2`"; s6:lemLent (ii):
  a lend-bad `Y` has no JS system).
* **"`⋃_Z B_Z ∪ LentJS_l` is partitioned into the single edges of `J_l` and at most … cycles"**:
  `J ⊆ ⋃_Z B_Z` and a list `D` of cycle objects with
  `IsDecomp ((⋃_Z B_Z ∪ LentJS) \ J) D` (the edges of the cycles are exactly the rest, pairwise
  disjoint and disjoint from `J`; with `J ⊆ ⋃_Z B_Z` the union of `J` and the cycle edges is the
  whole set). The objects of `D` are cycles (`Obj.cycle`); well-formedness (`Obj.WF`, length
  `≥ 3`, simple) is part of `IsDecomp`. `Disjoint (⋃_Z B_Z) LentJS` (blueprint (1)) is not a
  conjunct: it is derivable, since `LentJS` lies in lend-good classes `LJS_{Y,l,j}`, which are
  disjoint from every `E_l(Z)` (`EG.Spec.JslcStep7DisjStatement`, proved), and `B_Z ⊆ E_l(Z)`.
* **The count** `|D| ≤ 126 n/M_l + 1.5 Σ_{Y ancestor, (Y,l) giant} m_{Y,l}` in `ℝ`, `n = G.card`,
  `M_l = run.M G l`, the sum over `Y ∈ run.ancestors G` with `EG.Chain.IsGiant run G δ Y l`, and
  `m_{Y,l} = EG.Chain.mY run G δ Y l`. This is the v6.1 statement (T1 patch JSLC-G-UNDEFINED:
  the statement no longer mentions `g_{Y,l}`), and the form read by the consumer MIX-C (c).
* **"Each cycle consists of edges of `⋃_Z B_Z` and edges of `⋃_j LJS_{Y,l,j}` for a single
  ancestor `Y`"**: for each cycle `o ∈ D` some `Y ∈ run.ancestors G` with every edge of `o` in
  `⋃_Z B_Z` or in some `S.ljs Y l j`, `j < K^JS_l`.
* **(s6:eqJbound)** `|J_l| ≤ EG.Chain.jBound run G δ S l` (in `ℝ`, because of the `½`). The TeX
  records it "for completeness"; it stays a conjunct (blueprint JSLC-EQJBOUND: no weakening).
* **Lemma J⁺**: `EG.Chain.JPlusProps run G δ S l J` (types (i) exhaustive, (J1) aggregated at
  hubs, fresh and lost centres, (J2), (ii)). The J-independent items of J⁺ ((J3), exclusivity in
  (i), (iii), (iv)) are `EG.Spec.JplusFactsStatement` (`EG/Spec/Chain/JPlus.lean`); (v) is a
  property of the stage-1 law (TRIAGE §2.9). The clause "`J_l` consists exactly of the deletions of
  Step 2 … for every choice … Steps 3–8 delete nothing" is about the proof and is not encoded
  (blueprint JPLUS-EXISTENTIAL; design note D-DES-7).
* The sentence on the unused edges of the classes ("junk for their owner") is commentary for the
  consumer; it is not a property of the output and is not encoded.
* Remark s6:remStar (the star split is not used) has no content to formalize: the Spec has no
  star-split option.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain

universe u

open Classical in
/-- [s6:lemJSLC] **Lemma JS-LC** (one round `l ≥ 3`; cherry split for giant pairs), together with
the J-interface of [s6:lemJplus] **Lemma J⁺** (`JPlusProps`): "Fix a valid run, a designation `δ`,
a stage-1 outcome with its stage-2 data (Definition s6:defLending), and a round `3 ≤ l ≤ R`. For
every `Z ∈ Std_l` let `B_Z ⊆ E_l(Z)` be a set of edges, each of which has an end in `Q*_Z`. …
Then there are a set `J_l ⊆ ⋃_Z B_Z` and a set `LentJS_l ⊆ ⋃_{Y,j} LJS_{Y,l,j}` such that
`⋃_Z B_Z ∪ LentJS_l` is partitioned into the single edges of `J_l` and at most
`126 n/M_l + 1.5 Σ_{(Y,l) giant} m_{Y,l}` cycles. … Each cycle consists of edges of `⋃_Z B_Z` and
edges of `⋃_j LJS_{Y,l,j}` for a single ancestor `Y`. Moreover (s6:eqJbound) `|J_l| ≤ …`", and
(Lemma J⁺) `J_l` has the properties (i) (exhaustive), (J1), (J2), (ii).

See the module docstring for the encoding of each clause (in particular the hypothesis "no edge
of any class `LJS_{Y,l,j}` has been used", which is encoded by assuming nothing about the
classes). -/
def JSLCStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V)
    (δ : Designation V) (S : StageData V) (l : ℕ) (B : Addr → Finset (Sym2 V)),
    RunHyp N0 Dstar G run → IsDesignation run G δ → S.Coherent run G →
    3 ≤ l → l ≤ run.R →
    (∀ a ∈ run.Std G l, B a ⊆ run.E G l a ∧ ∀ e ∈ B a, ∃ u ∈ qs run G δ S l a, u ∈ e) →
    ∃ (J LentJS : Finset (Sym2 V)) (D : List (Obj V)),
      J ⊆ (run.Std G l).biUnion B ∧
      LentJS ⊆ (lendGoodAnc run G S l).biUnion
        (fun Y => (Finset.range (Stage1.KJS G run l)).biUnion (S.ljs Y l)) ∧
      IsDecomp ((((run.Std G l).biUnion B ∪ LentJS) \ J : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
      (∀ o ∈ D, ∃ c : List V, o = Obj.cycle c) ∧
      (D.length : ℝ) ≤ 126 * (G.card : ℝ) / (run.M G l : ℝ) +
        1.5 * ∑ Y ∈ (run.ancestors G).filter (fun Y => IsGiant run G δ Y l),
          (mY run G δ Y l : ℝ) ∧
      (∀ o ∈ D, ∃ Y ∈ run.ancestors G, ∀ e ∈ o.edges,
        e ∈ (run.Std G l).biUnion B ∨ ∃ j < Stage1.KJS G run l, e ∈ S.ljs Y l j) ∧
      (J.card : ℝ) ≤ jBound run G δ S l ∧
      JPlusProps run G δ S l J

end EG.Spec
