import EG.Lib.Chain.StageInst
import EG.Lib.Chain.JSet
import EGTest.Design

/-! Unit tests for `EG.Defs.Chain.StageInst` (`StageData.ofOutcome`, `StageData.Coherent`) and
the fix-round-1 additions to `EG.Lib.Chain.JSet` (design note `work/p2d/design.md`, "Fix round 1").

* **Coherence has content.** On the run `run3` of `EGTest.Design`:
  - the record `S0` (every ancestor fails COL(a) and COL(b), no classes, all labels `*`) is
    coherent; with it the classed port `2` of `[true]` is lost at round 3 (its class is lend-bad);
  - `Slab` (every label `0`, also at rounds `l < r(Y) + 2`) is **not** coherent (`lab_dom`);
  - a record with a JV class at a round outside `[r(Y)+2, R]` is **not** coherent
    (`ljv_eq_empty`, review item MINOR-4);
  - a record with an own class outside `E(H_Y)` is **not** coherent (`own_sub`).
* **Instantiation.** For every run, the record of every stage-1 outcome of positive weight is
  coherent (`coherent_ofOutcome`), and its COL(b) events give exactly the path-connectivity of
  `Stage1.COLb` read through the record (the JS-LC hypothesis); the junction sets agree
  (`Tj_ofOutcome`). Coherent records exist for every run (`exists_coherent`).
* **Positive J-lemmas** (review item MINOR-1): a `J^hub`-edge makes `d_{Y,l}(h)`, `c^agg_{h,l}`
  positive, and the s7 shapes of (J1)/(J2) follow from `JPlusProps` (abstract run). -/

namespace EGTest.StageInst

open EG EG.HB EG.Chain EGTest.HB EGTest.HB.StandaloneTest EGTest.Design

/-! ## Coherence on `run3` -/

/-- Every ancestor fails COL(a) and COL(b); no classes; every label `*`. -/
def S0 : StageData (Fin 5) where
  colA _ := False
  colB _ := False
  demoted _ := False
  lab _ _ _ := none
  own _ := ∅
  ljs _ _ _ := ∅
  ljv _ _ := ∅
  dem := 0
  lp := 0

theorem coherent_S0 : S0.Coherent run3 G5 where
  colB_conn _ h := h.elim
  colA_own _ h := h.elim
  colA_ljs _ h := h.elim
  colA_ljv _ h := h.elim
  own_sub _ := Finset.empty_subset _
  ljs_sub _ _ _ := Finset.empty_subset _
  ljv_sub _ _ := Finset.empty_subset _
  ljs_disj _ _ _ _ _ _ := Finset.disjoint_empty_left _
  ljv_disj _ _ _ _ := Finset.disjoint_empty_left _
  ljs_ljv_disj _ _ _ _ := Finset.disjoint_empty_left _
  own_ljs_disj _ _ _ := Finset.disjoint_empty_left _
  own_ljv_disj _ _ := Finset.disjoint_empty_left _
  ljs_eq_empty _ _ _ _ := rfl
  ljv_eq_empty _ _ _ := rfl
  lab_dom _ _ _ h := (h rfl).elim
  lab_lt _ _ _ _ h := by simp [S0] at h

/-- With `S0` the class `(1,[true])` of the port `2` is lend-bad, so `2` is lost at round 3. -/
example : lost run3 G5 δ3 S0 3 [true] = {2} := by
  classical
  ext u
  rw [mem_lost_iff run3 G5 δ3 S0 le_rfl, classed3_t]
  simp [S0, lendBad]

/-- `Slab` labels every vertex `0` at every round, also at `l = 0 < r(Y) + 2`: not coherent. -/
example : ¬ Slab.Coherent run3 G5 := fun h => by
  have := (h.lab_dom (1, [true]) 0 0 (by simp [Slab])).1
  simp [Stage1.lateRounds] at this

/-- A JV class at round `0` (outside `[r(Y)+2, R]`): not coherent. -/
example : ¬ ({ S0 with ljv := fun _ _ => {s(0, 1)} } : StageData (Fin 5)).Coherent run3 G5 :=
  fun h => by
    have := h.ljv_eq_empty (1, [true]) 0 (by simp [Stage1.lateRounds])
    simp at this

/-- An own class containing the edge `04`, which has an end outside `V((1,[true])) = {0,1,2}` and
so is no edge of `H_{(1,[true])}`: not coherent. -/
example : ¬ ({ S0 with own := fun _ => {s(0, 4)} } : StageData (Fin 5)).Coherent run3 G5 :=
  fun h => by
    have h04 := h.own_sub (1, [true]) (Finset.mem_singleton_self _)
    have h4 := (run3.ancGraph G5 (1, [true])).edge_verts _ h04 4 (Sym2.mem_mk_right _ _)
    rw [Run.ancGraph_verts, Run.ancVerts, partVerts3_one, partVertsA_t] at h4
    simp at h4

/-! ## Instantiation (abstract run) -/

section Abstract

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-- The JS-LC hypothesis for a lend-good ancestor, read from the record of an outcome of
positive weight, is exactly `Stage1.COLb`'s path connectivity through `Stage1.Tj`. -/
example {ω : Stage1.Outcome G run} (hω : ω ∈ (Stage1.law G run).supp) (d : PartId → Prop)
    (dem lp : ℕ) {Y : PartId} (hY : (StageData.ofOutcome ω d dem lp).colB Y)
    {l j : ℕ} (hl : l ∈ Stage1.lateRounds run Y.1) (hj : j < Stage1.KJS G run l) :
    (Stage1.LJS G run Y (ω.colAt Y) l j).IsPathConnected (2 ^ 12 * run.LY G Y ^ 4)
      (Stage1.tJS G run l) (Stage1.Tj G run Y (ω.jsAt Y) l j) := by
  have := (coherent_ofOutcome hω d dem lp).colB_conn Y hY l hl j hj
  rwa [Tj_ofOutcome, ofOutcome_ljs, LJS_restrict] at this

/-- Coherent records exist for every run. -/
example : ∃ S : StageData V, S.Coherent run G := exists_coherent run G

/-- On a coherent record there is no JV class before round `r(Y) + 2`. -/
example {S : StageData V} (hS : S.Coherent run G) : S.ljv (5, []) 6 = ∅ :=
  hS.ljv_eq_empty_of_lt (by norm_num)

/-- Positive class data of a `J^hub`-edge (MINOR-1). -/
example {δ : Designation V} {S : StageData V} {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (he : IsJhubEdge run G δ S l h Y e) :
    1 ≤ classDeg run G δ Y l h ∧ 1 ≤ mY run G δ Y l ∨ h ∉ G.verts := by
  by_cases hh : h ∈ G.verts
  · exact Or.inl ⟨he.one_le_classDeg,
      le_trans he.one_le_classDeg (Finset.le_sup (f := classDeg run G δ Y l) hh)⟩
  · exact Or.inr hh

example {δ : Designation V} {S : StageData V} {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (he : IsJhubEdge run G δ S l h Y e) : 1 ≤ cAgg run G δ h l := he.one_le_cAgg

/-! Design review 2: glue lemmas and non-vacuity beyond `∅`. -/

/-- The JV-lent classes of a coherent record lie in `E(G)` with no hypothesis on the run. -/
example {S : StageData V} (hS : S.Coherent run G) (Y : PartId) (l : ℕ) :
    S.ljv Y l ⊆ G.edges := hS.ljv_subset_graph_edges Y l

example (Y : PartId) : (run.ancGraph G Y).edges ⊆ G.edges := ancGraph_edges_subset_edges run G Y

/-- MIX-C's TPV bullet: for a lend-good standalone `Z`, `O_Z` is the own class as a graph on
`Z^0`, which `colA_own` makes an expander when `colA Z` holds. -/
example {S : StageData V} (hS : S.Coherent run G) {l : ℕ} {a : Addr}
    (hstd : ¬ run.isLight G l a) (hgood : ¬ lendBad run G S (l, a)) :
    (OZ run G S l a).verts = run.Z0 G l a ∧
      OZ run G S l a = (run.ancGraph G (l, a)).restrictEdges (S.own (l, a)) :=
  ⟨OZ_verts run G S l a, OZ_eq_restrictEdges hS hstd hgood⟩

/-- A one-edge `J^hub` set satisfies `JPlusProps` (`M_l ≥ 2`). -/
example {δ : Designation V} {S : StageData V} {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (he : IsJhubEdge run G δ S l h Y e) (hM : 2 ≤ run.M G l) :
    JPlusProps run G δ S l {e} ∧ ({e} : Finset (Sym2 V)).Nonempty :=
  ⟨he.jPlusProps_singleton hM, Finset.singleton_nonempty e⟩

example {S : StageData V} (Y : PartId) (l : ℕ) :
    Disjoint (Tj run G S Y l 0) (Tj run G S Y l 1) := Tj_disjoint run G S Y l (by norm_num)

/-- Positive `Bead`/`IsGiant`/`alphaY` (MINOR-D, abstract): a `J^hub`-edge is a bead edge, and
makes its pair giant when `γ_l = 0`. -/
example {δ : Designation V} {S : StageData V} {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (he : IsJhubEdge run G δ S l h Y e) (hγ : gammaL run G l = 0) :
    e ∈ Bead run G δ Y l ∧ IsGiant run G δ Y l :=
  ⟨he.mem_Bead, he.isGiant_of_gammaL_eq_zero hγ⟩

example {δ : Designation V} {Y : PartId} {l : ℕ} {x u : V} {a : Addr}
    (hx : x ∈ run.guests G Y.1 Y.2) (hu : u ∈ run.ancVerts G Y) (hu' : u ∉ run.DupStar G Y.1)
    (ha : a ∈ run.Std G l) (huc : u ∈ run.classed G l a) (hY : δ l u = Y)
    (he : s(x, u) ∈ run.E G l a) : alphaY run G δ Y l ≠ 0 :=
  Nat.one_le_iff_ne_zero.1 (one_le_alphaY run G δ hx hu hu' ha huc hY he)

end Abstract

end EGTest.StageInst
