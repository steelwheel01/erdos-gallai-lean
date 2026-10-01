import EG.Lib.Light.Stages
import EG.Lib.Light.Constants
import EG.Lib.Chain.StageInst
import EGTest.HB

/-! Unit tests for `EG.Defs.Light.{Stages, Constants}` ([s5:defStages], [s5:lemChild] data,
[s5:lemParent] arcs and bundles, [s5:lemExpect] `ε_U`, [s5:lemParent] `ε_ch`):
* the constants: `ε_U(2) = 2462`, `ε_ch = ε_K` (`rfl`), positivity, the two limits;
* `vm`, `vb` are the Lemma-PV parameters (`rfl`), the child data is a `Vortex.PVData` and its own
  classes have the index type `Fin (pvJ |Z|) × Fin 4` of Lemma PV without a cast;
* `IsHBFamily` on `K_3`: one true instance, and the size and multiplicity clauses each refute one;
* `ArcHyp` is the per-part `H0Adm ∧ ArcSys`;
* on the valid one-round run `run1` on `K_3` (three light parts of one vertex each, `R = 1`):
  every light part satisfies (E1) and COL(a), is not demoted, not parent-bad (`r ≥ R - 1`), and
  is a good parent; `Bad = ∅`, `dem = lp = 0`, `Rt = ∅`, `Pl = V(Z)`, `par` is undefined;
  the empty arc systems satisfy `ArcHyp` at round `1`;
* generic: demoted ⇒ not a good parent, `Rt ⊔ Pl = V(Z)`, `Rt = ∅` for `l ≤ 2`, the U-bundle of
  empty arc systems is empty, and the s6 stage record `StageData.ofOutcome ω (demoted ω) (dem ω)
  (lp ω)` typechecks with no cast and is coherent on the support (TRIAGE item 20). -/

namespace EGTest.Light

open EG EG.HB EG.Stage1 EG.Light EGTest.HB

/-! ## Constants -/

example : epsU 2 = 2462 := by simp [epsU]

example (D : ℝ) : epsChain D = EG.Chain.epsK D := rfl

example : 0 < epsU 4 := epsU_pos (by norm_num)

example : Filter.Tendsto epsU Filter.atTop (nhds 0) := tendsto_epsU

example : Filter.Tendsto epsChain Filter.atTop (nhds 0) := tendsto_epsChain

/-! ## `vm`, `vb`, the child data -/

section Generic

variable {V : Type} [DecidableEq V] {G : FGraph V} {run : Run V}

example (Y : PartId) : vm G run Y = ⌈run.LY G Y ^ 6⌉₊ := rfl
example (Y : PartId) : vm G run Y = Vortex.pvM (run.ancVerts G Y).card := rfl
example (Y : PartId) : vb G run Y = Vortex.pvB (run.ancVerts G Y).card := rfl

/-- The child data is a value of the canonical Lemma-PV record (TRIAGE §2.8 PV-DATA-RECORD). -/
noncomputable example (ω : Outcome G run) (Z : PartId) : Vortex.PVData V := childData ω Z

/-- A Lemma-PV-shaped predicate on own-class families indexed by `Fin (pvJ |Z|) × Fin 4` accepts
the own classes of the child data with no cast (TRIAGE §2.7 PV-OWNCLASS-INDEX). -/
example (ω : Outcome G run) (Z : PartId)
    (P : ∀ Zs : Finset V, (Fin (Vortex.pvJ Zs.card) × Fin 4 → FGraph V) → Prop) :
    P (childData ω Z).Z (childData ω Z).R ↔
      P (run.ancVerts G Z) (fun p => ownR G run Z (ω.colAt Z) p.1 p.2) := Iff.rfl

example (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).M = ownM G run Z (ω.colAt Z) := rfl

example (ω : Outcome G run) (Z : PartId) :
    (childData ω Z).sOwn = (run.s G Z.1 : ℝ) / (16 * kown G run Z) := rfl

/-- (E1) at `l = r(Z)` is (E1') for the child data. -/
example (ω : Outcome G run) (Z : PartId) (h : E1 ω Z) (hR : Z.1 ≤ run.R) (w : V)
    (hw : w ∈ run.ancVerts G Z) :
    run.LY G Z ^ 5 / 8 ≤ ((((childData ω Z).A w).filter fun u =>
      s(w, u) ∈ (childData ω Z).M.edges ∧ (childData ω Z).ext u = none).card : ℝ) :=
  E1_childData ω h hR hw

/-- A demoted part is not a good parent ([s5:lemDemoted] (1)). -/
example (ω : Outcome G run) (Y : PartId) (h : demoted ω Y) : ¬ goodParent ω Y :=
  not_goodParent_of_demoted ω h

/-- A demoted light part lies in `Bad`. -/
example (ω : Outcome G run) (Y : PartId) (hY : Y ∈ run.lightParts G) (h : demoted ω Y) :
    Y ∈ Bad ω :=
  (mem_Bad ω).2 ⟨hY, Or.inl h⟩

example (ω : Outcome G run) (Z : PartId) : Rt ω Z ∪ Pl ω Z = run.ancVerts G Z :=
  Rt_union_Pl ω Z

example (ω : Outcome G run) (Z : PartId) (hZ : Z.1 ≤ 2) : Rt ω Z = ∅ :=
  Rt_eq_empty_of_le_two ω hZ

/-- A part of round `r ≥ R - 1` is never parent-bad. -/
example (ω : Outcome G run) (Y : PartId) (hY : run.R < Y.1 + 2) : ¬ parentBad ω Y :=
  not_parentBad_of_R_lt ω hY

/-- `par(v)` is defined exactly on `Rt(Z)`. -/
example (ω : Outcome G run) (Z : PartId) (v : V) :
    v ∈ Rt ω Z ↔ v ∈ run.ancVerts G Z ∧ (parU ω Z.1 v).isSome :=
  mem_Rt_iff_parU ω

/-- `ArcHyp` is the per-part predicate `H0Adm ∧ ArcSys` (review MINOR-1): a lemChild-shaped
per-part conclusion `ArcSys` feeds `ArcHyp` with no clause-by-clause rebuilding. -/
example (ω : Outcome G run) (l : ℕ) (H0 : PartId → Finset (Sym2 V))
    (arcs : PartId → List (Arc V))
    (h : ∀ Z ∈ childParts ω l, H0Adm ω Z (H0 Z) → ArcSys ω Z (H0 Z) (arcs Z))
    (hH0 : ∀ Z ∈ childParts ω l, H0Adm ω Z (H0 Z)) :
    ArcHyp ω l H0 arcs :=
  fun Z hZ => ⟨hH0 Z hZ, h Z hZ (hH0 Z hZ)⟩

example (ω : Outcome G run) (Z : PartId) (H0 : Finset (Sym2 V)) : ArcSys ω Z H0 [] :=
  ArcSys.nil ω Z H0

/-- The U-bundle of the empty arc systems is empty. -/
example (ω : Outcome G run) (l : ℕ) (c : Fin 4) :
    bundleEdges ω l (fun _ => ([] : List (Arc V))) c = ∅ := by
  ext e
  simp [mem_bundleEdges]

/-- The s6 stage record of a stage-1 outcome, with the s5 statuses (TRIAGE item 20: no cast). -/
noncomputable example (ω : Outcome G run) : EG.Chain.StageData V :=
  EG.Chain.StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)

example (ω : Outcome G run) :
    (EG.Chain.StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)).dem = dem ω := rfl

example (ω : Outcome G run) (hω : ω ∈ (law G run).supp) :
    (EG.Chain.StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)).Coherent run G :=
  EG.Chain.coherent_ofOutcome hω _ _ _

end Generic

/-! ## Lemma-HB families on `K_3` (non-vacuity, review COSMETIC-2) -/

/-- `A(w) = {w+1}` is a Lemma-HB family of `K_3` with `m = b = 1`. -/
example : IsHBFamily K3 1 1 (fun w => {w + 1}) := by
  unfold IsHBFamily FGraph.nbrs FGraph.Adj
  decide

/-- The size clause bites: `|N_{K_3}(w)| = 2 < 3`, so no family with `m = 3`. -/
example : ¬ ∃ A, IsHBFamily K3 3 10 A := by
  rintro ⟨A, hA, -⟩
  obtain ⟨hsub, hcard⟩ := hA 0 (by decide)
  have h2 : (K3.nbrs 0).card = 2 := by
    unfold FGraph.nbrs FGraph.Adj
    decide
  have := Finset.card_le_card hsub
  omega

/-- The multiplicity clause bites: every vertex lies in one set `{w+1}`, so `b = 0` fails. -/
example : ¬ IsHBFamily K3 1 0 (fun w => {w + 1}) := by
  rintro ⟨-, hb⟩
  have := hb 1
  revert this
  decide

/-! ## The valid one-round run on `K_3` -/

theorem ancVerts_run1 (a : Addr) : run1.ancVerts K3 (1, a) = (tree0.graphAtD E3 a).verts := by
  classical
  simp only [Run.ancVerts, Run.partVerts, Run.graph_one]
  change Round.partVerts K3 c1 a = _
  simp [Round.partVerts, isLight_c1, guests_eq, Z0_eq]

/-- Every light part of `run1` has round `1` and one vertex. -/
theorem lightPart_run1 {Y : PartId} (hY : Y ∈ run1.lightParts K3) :
    Y.1 = 1 ∧ (run1.ancVerts K3 Y).card = 1 := by
  obtain ⟨h, -⟩ := (Run.mem_lightParts run1 K3).1 hY
  have hr := Run.isRound_of_mem_prePartAddrs h
  have h1 : Y.1 = 1 := le_antisymm hr.2 hr.1
  refine ⟨h1, ?_⟩
  rw [h1, Run.prePartAddrs_of_isRound run1 K3 ⟨le_rfl, le_rfl⟩, Run.graph_one] at h
  change Y.2 ∈ Round.prePartAddrs K3 c1 at h
  rw [prePartAddrs_eq] at h
  obtain ⟨y1, y2⟩ := Y
  simp only at h1 h
  subst h1
  rw [ancVerts_run1]
  exact card_leaf h

theorem LY_run1 {Y : PartId} (hY : Y ∈ run1.lightParts K3) : run1.LY K3 Y = 0 := by
  simp [Run.LY, (lightPart_run1 hY).2]

/-- (E1) holds trivially (`L_Y = 0`). -/
theorem E1_run1 (ω : Outcome K3 run1) {Y : PartId} (hY : Y ∈ run1.lightParts K3) : E1 ω Y := by
  intro l _ w _
  rw [LY_run1 hY]
  norm_num

/-- COL(a) holds: every class is a graph on one vertex, hence an expander. -/
theorem COLa_run1 (ω : Outcome K3 run1) {Y : PartId} (hY : Y ∈ run1.lightParts K3) :
    COLa K3 run1 Y (ω.cOutAt Y) := by
  have h1 := (lightPart_run1 hY).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact FGraph.isExpander_of_card_le_one (by simp [FGraph.card, h1])
  · exact FGraph.isExpander_of_card_le_one (by simp [FGraph.card, h1])
  · intro i _
    exact FGraph.isExpander_of_card_le_one (by simp [FGraph.card, h1])
  · intro _ o
    exact FGraph.isExpander_of_card_le_one (by simp [FGraph.card, h1])

theorem not_demoted_run1 (ω : Outcome K3 run1) {Y : PartId} (hY : Y ∈ run1.lightParts K3) :
    ¬ demoted ω Y := by
  rintro (h | h)
  · exact h (E1_run1 ω hY)
  · exact h (COLa_run1 ω hY)

theorem not_parentBad_run1 (ω : Outcome K3 run1) {Y : PartId} (hY : Y ∈ run1.lightParts K3) :
    ¬ parentBad ω Y :=
  not_parentBad_of_R_lt ω (by rw [(lightPart_run1 hY).1]; decide)

/-- Every light part of `run1` is a good parent. -/
example (ω : Outcome K3 run1) {Y : PartId} (hY : Y ∈ run1.lightParts K3) : goodParent ω Y :=
  ⟨hY, not_demoted_run1 ω hY, not_parentBad_run1 ω hY⟩

theorem Bad_run1 (ω : Outcome K3 run1) : Bad ω = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro Y hY
  obtain ⟨hL, h⟩ := (mem_Bad ω).1 hY
  rcases h with h | h
  · exact not_demoted_run1 ω hL h
  · exact not_parentBad_run1 ω hL h

example (ω : Outcome K3 run1) : dem ω = 0 := by
  classical
  unfold dem
  rw [Finset.sum_eq_zero]
  intro Y hY
  exact absurd (Finset.mem_filter.1 hY).2 (not_demoted_run1 ω (Finset.mem_filter.1 hY).1)

example (ω : Outcome K3 run1) : lp ω = 0 := by
  simp [lp, Bad_run1]

/-- Round `1`: no parents, `Rt(Z) = ∅`, `Pl(Z) = V(Z)`, and `par` is undefined. -/
example (ω : Outcome K3 run1) (a : Addr) : Rt ω (1, a) = ∅ :=
  Rt_eq_empty_of_le_two ω (show (1 : ℕ) ≤ 2 by norm_num)

example (ω : Outcome K3 run1) (a : Addr) : Pl ω (1, a) = run1.ancVerts K3 (1, a) :=
  Pl_eq_of_le_two ω (show (1 : ℕ) ≤ 2 by norm_num)

example (ω : Outcome K3 run1) (v : Fin 3) : parU ω 1 v = none := by
  have : ¬ (parU ω 1 v).isSome := by
    rw [parU_isSome_iff]
    rintro ⟨Y, hg, hr, -⟩
    have := (lightPart_run1 hg.1).1
    omega
  simpa using this

/-- The empty arc systems satisfy the child-side hypotheses at round `1` (with `H_0(Z) = ∅`:
the one-vertex parts have no edges, so `Own_Z = ∅`). -/
example (ω : Outcome K3 run1) : ArcHyp ω 1 (fun _ => ∅) (fun _ => []) := by
  refine ArcHyp.nil fun Z hZ => ⟨?_, Finset.empty_subset _⟩
  have hL := ((mem_childParts ω).1 hZ).1
  have h1 := (lightPart_run1 hL).2
  intro e he
  exfalso
  have hsub : (Own K3 run1 Z (ω.colAt Z)).edges ⊆ (run1.ancGraph K3 Z).edges :=
    ((run1.ancGraph K3 Z).restrictEdges_le _).2
  have he' := hsub he
  obtain ⟨x, y⟩ := e
  have hx := (run1.ancGraph K3 Z).edge_verts _ he' x (Sym2.mem_mk_left x y)
  have hy := (run1.ancGraph K3 Z).edge_verts _ he' y (Sym2.mem_mk_right x y)
  have hne := (run1.ancGraph K3 Z).loopless _ he'
  rw [Run.ancGraph_verts] at hx hy
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 h1
  rw [hu, Finset.mem_singleton] at hx hy
  subst hx hy
  exact hne (Sym2.mk_isDiag_iff.2 rfl)

end EGTest.Light
