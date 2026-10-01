module

public import EG.Defs.Chain.StageInst
public import EG.Lib.Stage1.Law
public import EG.Lib.Chain.Lending

/-!
# The stage data of a stage-1 outcome: API (companion of `EG.Defs.Chain.StageInst`)

* the fields of `StageData.ofOutcome` (`ofOutcome_*`, all `rfl`);
* the bridge `Tj_ofOutcome`: `EG.Chain.Tj` of the instantiated record is `EG.Stage1.Tj` of the JS
  labels of `ω` (review item MINOR-2: the s3 and s6 junction sets cannot drift apart);
* `restrictEdges_edges_self`, `LJS_restrict`, `LJV_restrict`, `Own_restrict`: a class as a graph
  on `V(Y)` is recovered from its edge set, so `StageData.Coherent.colB_conn` is `Stage1.COLb`
  on the instantiation;
* `js_mem_supp_jsLaw`, `mem_lentIdx_of_mem_lentClass`: support facts;
* **`coherent_ofOutcome`**: for every stage-1 outcome `ω` of positive weight and every choice of
  the s5 status data, `(StageData.ofOutcome ω d dem lp).Coherent run G`; `exists_coherent`;
* consequences of `Coherent` in the forms the s6/s7 statements use:
  `StageData.Coherent.ljv_subset_edges`, `ljs_subset_edges` (`LJV_{Y,l}, LJS_{Y,l,j} ⊆ E(G)` on a
  run whose ancestor graphs lie in `G`), `StageData.Coherent.Tj_eq_empty` (`T_j(Y,l) = ∅` for
  `j ≥ K^JS_l`), `StageData.Coherent.ljv_eq_empty_of_lt` (`LJV_{Y,l} = ∅` for `l < r(Y) + 2`);
* glue (design review 2): `ancGraph_le`, `ancGraph_edges_subset_edges` (`H_Y ≤ G`),
  `StageData.Coherent.{ljv,ljs,own}_subset_graph_edges` (classes `⊆ E(G)`, no hypothesis), and
  `OZ_eq_restrictEdges` (`O_Z = H_Z.restrictEdges Own_Z` for a lend-good standalone `Z`).
-/

public section

namespace EG.Chain

open EG.HB EG.FinDist

variable {V : Type*} [DecidableEq V] {G : FGraph V} {run : Run V}

/-! ### The fields of `ofOutcome` -/

section Fields

variable (ω : Stage1.Outcome G run) (d : PartId → Prop) (dem lp : ℕ)

theorem ofOutcome_colA (Y : PartId) :
    (StageData.ofOutcome ω d dem lp).colA Y = Stage1.COLa G run Y (ω.cOutAt Y) := rfl

theorem ofOutcome_colB (Y : PartId) :
    (StageData.ofOutcome ω d dem lp).colB Y = Stage1.COLb G run Y (ω.cOutAt Y) := rfl

theorem ofOutcome_demoted : (StageData.ofOutcome ω d dem lp).demoted = d := rfl

theorem ofOutcome_lab (Y : PartId) (l : ℕ) (y : V) :
    (StageData.ofOutcome ω d dem lp).lab Y l y = ω.labAt Y l y := rfl

theorem ofOutcome_own (Y : PartId) :
    (StageData.ofOutcome ω d dem lp).own Y = (Stage1.Own G run Y (ω.colAt Y)).edges := rfl

theorem ofOutcome_ljs (Y : PartId) (l j : ℕ) :
    (StageData.ofOutcome ω d dem lp).ljs Y l j = (Stage1.LJS G run Y (ω.colAt Y) l j).edges := rfl

theorem ofOutcome_ljv (Y : PartId) (l : ℕ) :
    (StageData.ofOutcome ω d dem lp).ljv Y l = (Stage1.LJV G run Y (ω.colAt Y) l).edges := rfl

theorem ofOutcome_dem : (StageData.ofOutcome ω d dem lp).dem = dem := rfl

theorem ofOutcome_lp : (StageData.ofOutcome ω d dem lp).lp = lp := rfl

/-- [s3:defCOL] (iv) the junction set `T_j(Y,l)` of s6 (`EG.Chain.Tj`, read from the record) is
the junction set of s3 (`EG.Stage1.Tj`, read from the JS labels of `ω`). -/
theorem Tj_ofOutcome (Y : PartId) (l j : ℕ) :
    Tj run G (StageData.ofOutcome ω d dem lp) Y l j = Stage1.Tj G run Y (ω.jsAt Y) l j := by
  ext y
  rw [Stage1.Outcome.mem_Tj_iff]
  unfold Tj
  exact Finset.mem_filter

end Fields

/-! ### Classes as graphs on `V(Y)` -/

theorem restrictEdges_edges_self (H : FGraph V) (F : Finset (Sym2 V)) :
    H.restrictEdges (H.restrictEdges F).edges = H.restrictEdges F := by
  refine FGraph.ext rfl ?_
  ext e
  simp only [FGraph.restrictEdges, Finset.mem_filter]
  tauto

theorem lentClass_restrict (Y : PartId) (c : Stage1.Colouring G run Y) (i : Stage1.LentTag) :
    (run.ancGraph G Y).restrictEdges (Stage1.lentClass G run Y c i).edges =
      Stage1.lentClass G run Y c i :=
  restrictEdges_edges_self _ _

theorem LJS_restrict (Y : PartId) (c : Stage1.Colouring G run Y) (l j : ℕ) :
    (run.ancGraph G Y).restrictEdges (Stage1.LJS G run Y c l j).edges = Stage1.LJS G run Y c l j :=
  restrictEdges_edges_self _ _

theorem LJV_restrict (Y : PartId) (c : Stage1.Colouring G run Y) (l : ℕ) :
    (run.ancGraph G Y).restrictEdges (Stage1.LJV G run Y c l).edges = Stage1.LJV G run Y c l :=
  restrictEdges_edges_self _ _

theorem Own_restrict (Y : PartId) (c : Stage1.Colouring G run Y) :
    (run.ancGraph G Y).restrictEdges (Stage1.Own G run Y c).edges = Stage1.Own G run Y c :=
  restrictEdges_edges_self _ _

/-! ### Support facts -/

/-- On the support of the stage-1 law, the JS labels of an ancestor lie in the support of their
law. -/
theorem js_mem_supp_jsLaw {ω : Stage1.Outcome G run} (hω : ω ∈ (Stage1.law G run).supp)
    (Y : ↥(run.ancestors G)) : ω.js Y ∈ (Stage1.jsLaw G run Y).supp := by
  rw [← Stage1.map_js G run Y, mem_supp, map_w]
  refine (lt_of_lt_of_le ((mem_supp_iff_pos _).1 hω) ?_).ne'
  rw [← prob_singleton]
  exact prob_mono _ (fun ω' h => by simp only [Set.mem_singleton_iff] at h; subst h; rfl)

/-- On the support, an edge of the lent class of index `i` (in the colouring of `Y` read from
`ω`) witnesses `i ∈ I^U(Y) ⊔ I^JS(Y) ⊔ I^JV(Y)` (off the ancestors the colouring is junk with all
bits `false`, so the class is empty). -/
theorem mem_lentIdx_of_mem_lentClass {ω : Stage1.Outcome G run}
    (hω : ω ∈ (Stage1.law G run).supp) {Y : PartId} {i : Stage1.LentTag} {e : Sym2 V}
    (he : e ∈ (Stage1.lentClass G run Y (ω.colAt Y) i).edges) : i ∈ Stage1.lentIdx G run Y := by
  obtain ⟨h, hb, hi⟩ := (Stage1.mem_lentClass_edges G run Y (ω.colAt Y)).1 he
  by_cases hY : Y ∈ run.ancestors G
  · have hc : ω.colAt Y = ω.col ⟨Y, hY⟩ := by simp [Stage1.Outcome.colAt, hY]
    rw [hc] at hi
    exact Stage1.idx_mem_of_mem_supp G run Y (Stage1.col_mem_supp_colouringLaw G run hω ⟨Y, hY⟩)
      ⟨e, h⟩ i hi
  · simp [Stage1.Outcome.colAt, hY] at hb

/-- On the support, a JS label `lab_{Y,l}(y) = j` has `j < K^JS_l`. -/
theorem lt_KJS_of_labAt {ω : Stage1.Outcome G run} (hω : ω ∈ (Stage1.law G run).supp)
    {Y : PartId} {l : ℕ} {y : V} {j : ℕ} (h : ω.labAt Y l y = some j) : j < Stage1.KJS G run l := by
  unfold Stage1.Outcome.labAt at h
  split_ifs at h with hs
  by_cases hY : Y ∈ run.ancestors G
  · have hj : ω.jsAt Y = ω.js ⟨Y, hY⟩ := by simp [Stage1.Outcome.jsAt, hY]
    rw [hj] at h
    have hsupp := (mem_supp_pi _).1 (js_mem_supp_jsLaw hω ⟨Y, hY⟩) ⟨(l, y), hs⟩
    rw [h, mem_supp] at hsupp
    change Stage1.jsWeight (run.M G l) (some j) ≠ 0 at hsupp
    simp only [Stage1.jsWeight] at hsupp
    split_ifs at hsupp with hlt
    · exact hlt
    · exact absurd rfl hsupp
  · simp [Stage1.Outcome.jsAt, hY] at h

/-! ### Coherence of the instantiated record -/

/-- **The instantiated record is coherent.** For every stage-1 outcome `ω` of positive weight and
every choice of the s5 status data `d`, `dem`, `lp`, the record `StageData.ofOutcome ω d dem lp`
satisfies every stage-1 fact of `StageData.Coherent`. So a statement proved for every coherent
record holds at every `ω ∈ (Stage1.law G run).supp`. -/
theorem coherent_ofOutcome {ω : Stage1.Outcome G run} (hω : ω ∈ (Stage1.law G run).supp)
    (d : PartId → Prop) (dem lp : ℕ) : (StageData.ofOutcome ω d dem lp).Coherent run G := by
  -- the JS index `(l, j)` and the JV index `l` lie in the index families
  have hJS : ∀ {Y : PartId} {l j : ℕ}, l ∈ Stage1.lateRounds run Y.1 → j < Stage1.KJS G run l →
      Stage1.LentTag.JS l j ∈ Stage1.lentIdx G run Y := fun hl hj =>
    Stage1.mem_lentIdx.2 (Or.inr (Or.inl (Stage1.mem_IJS.2 ⟨_, _, rfl, hl, hj⟩)))
  have hJV : ∀ {Y : PartId} {l : ℕ}, l ∈ Stage1.lateRounds run Y.1 →
      Stage1.LentTag.JV l ∈ Stage1.lentIdx G run Y := fun hl =>
    Stage1.mem_lentIdx.2 (Or.inr (Or.inr (Stage1.mem_IJV.2 ⟨_, rfl, hl⟩)))
  have hsub : ∀ (H : FGraph V) (F : Finset (Sym2 V)), (H.restrictEdges F).edges ⊆ H.edges :=
    fun H F e he => (Finset.mem_filter.1 he).1
  refine
    { colB_conn := ?_, colA_own := ?_, colA_ljs := ?_, colA_ljv := ?_,
      own_sub := fun Y => hsub _ _, ljs_sub := fun Y l j => hsub _ _,
      ljv_sub := fun Y l => hsub _ _,
      ljs_disj := ?_, ljv_disj := ?_, ljs_ljv_disj := ?_, own_ljs_disj := ?_,
      own_ljv_disj := ?_, ljs_eq_empty := ?_, ljv_eq_empty := ?_, lab_dom := ?_,
      lab_lt := ?_ }
  · intro Y hY l hl j hj
    rw [Tj_ofOutcome, ofOutcome_ljs, LJS_restrict]
    exact hY l hl j hj
  · intro Y hY
    rw [ofOutcome_own, Own_restrict]
    exact hY.1
  · intro Y hY l hl j hj
    rw [ofOutcome_ljs, LJS_restrict]
    exact hY.2.2.1 _ (hJS hl hj)
  · intro Y hY l hl
    rw [ofOutcome_ljv, LJV_restrict]
    exact hY.2.2.1 _ (hJV hl)
  · intro Y l j l' j' hne
    refine Stage1.disjoint_lentClass G run Y _ ?_
    intro h
    cases h
    exact hne rfl
  · intro Y l l' hne
    refine Stage1.disjoint_lentClass G run Y _ ?_
    intro h
    cases h
    exact hne rfl
  · intro Y l j l'
    exact Stage1.disjoint_lentClass G run Y _ (by intro h; cases h)
  · intro Y l j
    exact Finset.disjoint_of_subset_right (Stage1.lentClass_edges_subset_Lend G run Y _ _)
      (Stage1.disjoint_Own_Lend G run Y _)
  · intro Y l
    exact Finset.disjoint_of_subset_right (Stage1.lentClass_edges_subset_Lend G run Y _ _)
      (Stage1.disjoint_Own_Lend G run Y _)
  · intro Y l j hn
    refine Finset.eq_empty_of_forall_notMem fun e he => hn ?_
    have hi := mem_lentIdx_of_mem_lentClass hω he
    rcases Stage1.mem_lentIdx.1 hi with h | h | h
    · obtain ⟨-, l', c, σ, heq, -⟩ := Stage1.mem_IU.1 h
      cases heq
    · obtain ⟨l', j', heq, hl, hj⟩ := Stage1.mem_IJS.1 h
      cases heq
      exact ⟨hl, hj⟩
    · obtain ⟨l', heq, -⟩ := Stage1.mem_IJV.1 h
      cases heq
  · intro Y l hn
    refine Finset.eq_empty_of_forall_notMem fun e he => hn ?_
    have hi := mem_lentIdx_of_mem_lentClass hω he
    rcases Stage1.mem_lentIdx.1 hi with h | h | h
    · obtain ⟨-, l', c, σ, heq, -⟩ := Stage1.mem_IU.1 h
      cases heq
    · obtain ⟨l', j', heq, -⟩ := Stage1.mem_IJS.1 h
      cases heq
    · obtain ⟨l', heq, hl⟩ := Stage1.mem_IJV.1 h
      cases heq
      exact hl
  · intro Y l y hne
    rw [ofOutcome_lab] at hne
    unfold Stage1.Outcome.labAt at hne
    split_ifs at hne with hs
    · exact Finset.mem_product.1 hs
    · exact absurd rfl hne
  · intro Y l y j h
    exact lt_KJS_of_labAt hω h

/-- Non-vacuity: every run has a coherent stage-data record (the record of any stage-1 outcome
of positive weight). -/
theorem exists_coherent (run : Run V) (G : FGraph V) : ∃ S : StageData V, S.Coherent run G := by
  obtain ⟨ω, hω⟩ := (Stage1.law G run).supp_nonempty
  exact ⟨_, coherent_ofOutcome hω (fun _ => False) 0 0⟩

/-! ### Consequences of coherence -/

variable {S : StageData V}

/-- On a coherent record, every junction set `T_j(Y,l)` with `j ≥ K^JS_l` is empty. -/
theorem StageData.Coherent.Tj_eq_empty (hS : S.Coherent run G) {Y : PartId} {l j : ℕ}
    (hj : Stage1.KJS G run l ≤ j) : Tj run G S Y l j = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun y hy => ?_
  have := hS.lab_lt Y l y j (Finset.mem_filter.1 hy).2
  omega

/-- Every JV-lent class lies in `E(G)` when the ancestor graph `H_Y` does (the "of `G`" of
s6:defJconsumer (JC2), D-DES-8). -/
theorem StageData.Coherent.ljv_subset_edges (hS : S.Coherent run G) {Y : PartId} {l : ℕ}
    (hY : (run.ancGraph G Y).edges ⊆ G.edges) : S.ljv Y l ⊆ G.edges :=
  (hS.ljv_sub Y l).trans hY

/-- Every JS-lent class lies in `E(G)` when the ancestor graph `H_Y` does. -/
theorem StageData.Coherent.ljs_subset_edges (hS : S.Coherent run G) {Y : PartId} {l j : ℕ}
    (hY : (run.ancGraph G Y).edges ⊆ G.edges) : S.ljs Y l j ⊆ G.edges :=
  (hS.ljs_sub Y l j).trans hY

/-- For `r(Y) + 2 > l` the JV-lent class `LJV_{Y,l}` is empty (review item MINOR-4: this is what
makes `LJV_{Y,l}` disjoint from the J-edges of round `l` without a range guard). -/
theorem StageData.Coherent.ljv_eq_empty_of_lt (hS : S.Coherent run G) {Y : PartId} {l : ℕ}
    (hl : l < Y.1 + 2) : S.ljv Y l = ∅ :=
  hS.ljv_eq_empty Y l (fun h => by rw [Stage1.mem_lateRounds] at h; omega)

/-! ### Glue for the s7 instantiation and MIX-C (design review 2, COSMETIC-B/C) -/

section Glue

/-- `H_Y ≤ G`: the ancestor graph of every part identifier is a subgraph of `G`
(`H_Y ≤ X^0_Y ≤ G_{r(Y)} ≤ G_0 = G`). -/
theorem ancGraph_le (run : Run V) (G : FGraph V) (Y : PartId) : run.ancGraph G Y ≤ G := by
  have h0 : run.graph G Y.1 ≤ G := by
    simpa using Run.graph_le_of_le run G (Nat.zero_le Y.1)
  exact le_trans (Run.partGraph_le_X0 run G Y.1 Y.2)
    (le_trans (Run.X0_le_graph run G Y.1 Y.2) h0)

/-- `E(H_Y) ⊆ E(G)` (the hypothesis of `Coherent.ljv_subset_edges`, now unconditional). -/
theorem ancGraph_edges_subset_edges (run : Run V) (G : FGraph V) (Y : PartId) : (run.ancGraph G Y).edges ⊆ G.edges :=
  (ancGraph_le run G Y).2

/-- Every JV-lent class of a coherent record lies in `E(G)` (the "of `G`" of s6:defJconsumer
(JC2), D-DES-8; the `RoundInput.Valid` field `ljv_in` of s7). -/
theorem StageData.Coherent.ljv_subset_graph_edges (hS : S.Coherent run G) (Y : PartId) (l : ℕ) :
    S.ljv Y l ⊆ G.edges :=
  hS.ljv_subset_edges (ancGraph_edges_subset_edges run G Y)

/-- Every JS-lent class of a coherent record lies in `E(G)`. -/
theorem StageData.Coherent.ljs_subset_graph_edges (hS : S.Coherent run G) (Y : PartId)
    (l j : ℕ) : S.ljs Y l j ⊆ G.edges :=
  hS.ljs_subset_edges (ancGraph_edges_subset_edges run G Y)

/-- The own class of a coherent record lies in `E(G)`. -/
theorem StageData.Coherent.own_subset_graph_edges (hS : S.Coherent run G) (Y : PartId) :
    S.own Y ⊆ G.edges :=
  (hS.own_sub Y).trans (ancGraph_edges_subset_edges run G Y)

/-- On a coherent record, for a standalone part `Z = (l, a)` that is lend-good, the graph `O_Z`
of s6:defLending is the class `Own_Z` as a graph on `V(Z) = Z^0`, i.e.
`H_Z.restrictEdges (own Z)`: literally the graph that `StageData.Coherent.colA_own` calls an
`(ε_Z, s_Z/4)`-expander. This is the TPV bullet of MIX-C (design review 2, Check B). -/
theorem OZ_eq_restrictEdges (hS : S.Coherent run G) {l : ℕ} {a : Addr}
    (hstd : ¬ run.isLight G l a) (hgood : ¬ lendBad run G S (l, a)) :
    OZ run G S l a = (run.ancGraph G (l, a)).restrictEdges (S.own (l, a)) := by
  classical
  rw [OZ_of_not_lendBad run G S hgood]
  have hH : run.ancGraph G (l, a) = run.X0 G l a := by
    have hstd' : ¬ Round.isLight (run.graph G l) (run.choice l) a := hstd
    unfold Run.ancGraph Run.partGraph Round.partGraph
    rw [if_neg hstd']
    rfl
  have hsub := hS.own_sub (l, a)
  rw [hH] at hsub ⊢
  have hverts : (run.X0 G l a).verts = run.Z0 G l a := rfl
  refine FGraph.ext hverts.symm ?_
  ext e
  simp only [FGraph.ofEdges, FGraph.restrictEdges, Finset.mem_filter]
  constructor
  · rintro ⟨he, -, -⟩
    exact ⟨hsub he, he⟩
  · rintro ⟨heX, he⟩
    refine ⟨he, (run.X0 G l a).loopless e heX, ?_⟩
    rw [Finset.mem_sym2_iff]
    intro v hv
    exact (run.X0 G l a).edge_verts e heX v hv

end Glue

end EG.Chain
