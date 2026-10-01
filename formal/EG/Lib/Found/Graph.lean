module

public import EG.Defs.Expander
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Basic lemmas on `FGraph`, paths, balls, expanders and path connectivity

Companion of `EG.Defs.Graph`, `EG.Defs.Walk`, `EG.Defs.Expander`.

* membership / simp lemmas for all graph operations; degree bounds; `d_H(v) = deg_{E(H)}(v)`;
* monotonicity of `Nbr`, paths, "through", balls;
* [s1:citDef11] remark of B–M: an `(ε,s)`-expander on at least two vertices has `δ(G) > s`
  (`EG.FGraph.IsExpander.lt_deg`, `EG.FGraph.IsExpander.lt_minDeg`; this needs `ε > 0`, which
  B–M assume implicitly: for `ε ≤ 0` every graph is an `(ε,s)`-expander);
* monotonicity of expansion and of path connectivity in the sense of [s3:lemMonotone] (i), (ii)
  (`EG.FGraph.IsExpander.mono`, `EG.FGraph.IsExpander.of_le`, `EG.FGraph.IsPathConnected.mono`);
* `EG.FGraph.IsPathConnected.exists_paths`: Definition 7 applied to an index type in any
  universe; `EG.FGraph.IsPathConnected.exists_paths_sigma`: joint routing of several multisets
  ([s3:lemMonotone] (iii)); `EG.FGraph.isPathConnected_natFloor_iff`: a real multiplicity
  `t ≥ 0` may be replaced by `⌊t⌋₊`;
* `EG.FGraph.toSimpleGraph` and Mathlib walks: `EG.IsPathBetween.exists_walk` and
  `EG.isPathBetween_support` translate between list paths and `SimpleGraph.Walk.IsPath`.
-/

public section


namespace EG

variable {V : Type*}

/-! ## Graph basics -/

namespace FGraph

variable (H : FGraph V)

@[simp] theorem card_def : H.card = H.verts.card := rfl

theorem adj_iff {u v : V} : H.Adj u v ↔ s(u, v) ∈ H.edges := Iff.rfl

variable {H}

theorem le_def {H' : FGraph V} : H ≤ H' ↔ H.verts ⊆ H'.verts ∧ H.edges ⊆ H'.edges := Iff.rfl

theorem Adj.symm {u v : V} (h : H.Adj u v) : H.Adj v u := by
  rw [adj_iff, Sym2.eq_swap]; exact h

theorem adj_comm {u v : V} : H.Adj u v ↔ H.Adj v u := ⟨Adj.symm, Adj.symm⟩

theorem Adj.ne {u v : V} (h : H.Adj u v) : u ≠ v := fun huv =>
  H.loopless _ h (Sym2.mk_isDiag_iff.2 huv)

theorem Adj.mem_verts_left {u v : V} (h : H.Adj u v) : u ∈ H.verts :=
  H.edge_verts _ h u (Sym2.mem_mk_left u v)

theorem Adj.mem_verts_right {u v : V} (h : H.Adj u v) : v ∈ H.verts :=
  H.edge_verts _ h v (Sym2.mem_mk_right u v)

theorem Adj.mono {H' : FGraph V} (hle : H ≤ H') {u v : V} (h : H.Adj u v) : H'.Adj u v :=
  hle.2 h

theorem edges_subset_sym2 : H.edges ⊆ H.verts.sym2 := fun e he =>
  Finset.mem_sym2_iff.2 (H.edge_verts e he)

theorem card_edges_le_card_sym2 : H.edges.card ≤ H.verts.sym2.card :=
  Finset.card_le_card edges_subset_sym2

theorem mem_edges_iff_exists_adj {e : Sym2 V} :
    e ∈ H.edges ↔ ∃ u v, H.Adj u v ∧ s(u, v) = e := by
  constructor
  · intro he
    induction e using Sym2.ind with
    | h u v => exact ⟨u, v, he, rfl⟩
  · rintro ⟨u, v, h, rfl⟩
    exact h

section DecEq

variable [DecidableEq V]

/-! ### Neighbourhoods and degrees -/

@[simp] theorem mem_nbrs {v w : V} : w ∈ H.nbrs v ↔ H.Adj v w := by
  unfold nbrs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.mem_verts_right, h⟩⟩

theorem nbrs_subset_verts (v : V) : H.nbrs v ⊆ H.verts := Finset.filter_subset _ _

theorem self_not_mem_nbrs (v : V) : v ∉ H.nbrs v := fun h => (mem_nbrs.1 h).ne rfl

theorem nbrs_mono {H' : FGraph V} (hle : H ≤ H') (v : V) : H.nbrs v ⊆ H'.nbrs v :=
  fun _ hw => mem_nbrs.2 ((mem_nbrs.1 hw).mono hle)

theorem deg_def (v : V) : H.deg v = (H.nbrs v).card := rfl

theorem deg_mono {H' : FGraph V} (hle : H ≤ H') (v : V) : H.deg v ≤ H'.deg v :=
  Finset.card_le_card (nbrs_mono hle v)

theorem deg_le_card (v : V) : H.deg v ≤ H.card :=
  Finset.card_le_card (nbrs_subset_verts v)

/-- A vertex has at most `|H| - 1` neighbours. -/
theorem deg_lt_card {v : V} (hv : v ∈ H.verts) : H.deg v < H.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
    ⟨nbrs_subset_verts v, fun h => self_not_mem_nbrs (H := H) v (h ▸ hv)⟩)

@[simp] theorem mem_edgesAt {F : Finset (Sym2 V)} {v : V} {e : Sym2 V} :
    e ∈ edgesAt F v ↔ e ∈ F ∧ v ∈ e := Finset.mem_filter

theorem edgesAt_subset (F : Finset (Sym2 V)) (v : V) : edgesAt F v ⊆ F :=
  Finset.filter_subset _ _

theorem edgesAt_mono {F F' : Finset (Sym2 V)} (h : F ⊆ F') (v : V) :
    edgesAt F v ⊆ edgesAt F' v :=
  Finset.filter_subset_filter _ h

theorem degE_mono {F F' : Finset (Sym2 V)} (h : F ⊆ F') (v : V) : degE F v ≤ degE F' v :=
  Finset.card_le_card (edgesAt_mono h v)

theorem degE_le_card (F : Finset (Sym2 V)) (v : V) : degE F v ≤ F.card :=
  Finset.card_le_card (edgesAt_subset F v)

/-- The edges of `H` at `v` are the edges `vw`, `w ∈ N_H(v)`. -/
theorem edgesAt_edges_eq_image (v : V) :
    edgesAt H.edges v = (H.nbrs v).image (fun w => s(v, w)) := by
  ext e
  rw [mem_edgesAt, Finset.mem_image]
  constructor
  · rintro ⟨he, hv⟩
    refine ⟨Sym2.Mem.other hv, ?_, Sym2.other_spec hv⟩
    rw [mem_nbrs, adj_iff, Sym2.other_spec hv]
    exact he
  · rintro ⟨w, hw, rfl⟩
    exact ⟨mem_nbrs.1 hw, Sym2.mem_mk_left v w⟩

/-- [s1:convGraphs] (c): `d_H(v) = deg_{E(H)}(v)`, the number of neighbours of `v` equals the
number of edges of `H` at `v`. -/
theorem deg_eq_degE (v : V) : H.deg v = degE H.edges v := by
  rw [degE, edgesAt_edges_eq_image, Finset.card_image_of_injective]
  · rfl
  · intro w w' h
    exact Sym2.congr_right.1 h

theorem minDeg_le_deg {v : V} (hv : v ∈ H.verts) : H.minDeg ≤ H.deg v := by
  unfold minDeg
  rw [dif_pos ⟨v, hv⟩]
  exact Finset.inf'_le _ hv

theorem deg_le_maxDeg {v : V} (hv : v ∈ H.verts) : H.deg v ≤ H.maxDeg :=
  Finset.le_sup (f := H.deg) hv

/-- `δ(H) > s` iff every vertex has degree `> s` (for a graph with at least one vertex). -/
theorem lt_minDeg_iff (hne : H.verts.Nonempty) {s : ℝ} :
    s < (H.minDeg : ℝ) ↔ ∀ v ∈ H.verts, s < (H.deg v : ℝ) := by
  constructor
  · intro h v hv
    exact h.trans_le (by exact_mod_cast minDeg_le_deg hv)
  · intro h
    unfold minDeg
    rw [dif_pos hne]
    obtain ⟨v, hv, hveq⟩ := Finset.exists_mem_eq_inf' hne H.deg
    rw [hveq]
    exact h v hv

/-! ### Outside neighbourhood `Nbr_H(U)` -/

@[simp] theorem mem_nbrSet {U : Finset V} {v : V} :
    v ∈ H.nbrSet U ↔ v ∈ H.verts ∧ v ∉ U ∧ ∃ u ∈ U, H.Adj u v := by
  unfold nbrSet
  rw [Finset.mem_filter, Finset.mem_sdiff, and_assoc]

theorem nbrSet_subset_verts (U : Finset V) : H.nbrSet U ⊆ H.verts := fun _ hv =>
  (mem_nbrSet.1 hv).1

theorem disjoint_nbrSet (U : Finset V) : Disjoint U (H.nbrSet U) :=
  Finset.disjoint_left.2 fun _ hu hv => (mem_nbrSet.1 hv).2.1 hu

theorem nbrSet_subset_sdiff (U : Finset V) : H.nbrSet U ⊆ H.verts \ U :=
  Finset.filter_subset _ _

theorem card_nbrSet_le (U : Finset V) : (H.nbrSet U).card ≤ H.card :=
  Finset.card_le_card (nbrSet_subset_verts U)

/-- `Nbr` grows when edges are added and vertices are kept (`V(H) = V(H')`). -/
theorem nbrSet_mono {H' : FGraph V} (hle : H ≤ H') (U : Finset V) :
    H.nbrSet U ⊆ H'.nbrSet U := by
  intro v hv
  obtain ⟨hvV, hvU, u, hu, huv⟩ := mem_nbrSet.1 hv
  exact mem_nbrSet.2 ⟨hle.1 hvV, hvU, u, hu, huv.mono hle⟩

theorem nbrSet_singleton {v : V} : H.nbrSet {v} = H.nbrs v := by
  ext w
  rw [mem_nbrSet, mem_nbrs]
  constructor
  · rintro ⟨-, -, u, hu, h⟩
    rw [Finset.mem_singleton] at hu
    exact hu ▸ h
  · intro h
    refine ⟨h.mem_verts_right, ?_, v, Finset.mem_singleton_self v, h⟩
    rw [Finset.mem_singleton]
    exact fun hwv => h.ne hwv.symm

/-! ### Deleting edges `H - F` -/

@[simp] theorem deleteEdges_verts (F : Finset (Sym2 V)) : (H.deleteEdges F).verts = H.verts :=
  rfl

@[simp] theorem deleteEdges_edges (F : Finset (Sym2 V)) :
    (H.deleteEdges F).edges = H.edges \ F := rfl

@[simp] theorem deleteEdges_card (F : Finset (Sym2 V)) : (H.deleteEdges F).card = H.card := rfl

@[simp] theorem deleteEdges_adj {F : Finset (Sym2 V)} {u v : V} :
    (H.deleteEdges F).Adj u v ↔ H.Adj u v ∧ s(u, v) ∉ F := Finset.mem_sdiff

theorem deleteEdges_le (F : Finset (Sym2 V)) : H.deleteEdges F ≤ H :=
  ⟨subset_rfl, Finset.sdiff_subset⟩

theorem deleteEdges_anti {F F' : Finset (Sym2 V)} (h : F ⊆ F') :
    H.deleteEdges F' ≤ H.deleteEdges F :=
  ⟨subset_rfl, Finset.sdiff_subset_sdiff subset_rfl h⟩

@[simp] theorem deleteEdges_empty : H.deleteEdges ∅ = H := by
  ext <;> simp

theorem deleteEdges_inter_edges (F : Finset (Sym2 V)) :
    H.deleteEdges (F ∩ H.edges) = H.deleteEdges F := by
  ext e
  · rfl
  · simp only [deleteEdges_edges, Finset.mem_sdiff, Finset.mem_inter]
    tauto

theorem deleteEdges_deleteEdges (F F' : Finset (Sym2 V)) :
    (H.deleteEdges F).deleteEdges F' = H.deleteEdges (F ∪ F') := by
  ext e
  · rfl
  · simp only [deleteEdges_edges, Finset.mem_sdiff, Finset.mem_union]
    tauto

/-- `Nbr_{H-F'}(U) ⊆ Nbr_{H-F}(U)` for `F ⊆ F'`. -/
theorem nbrSet_deleteEdges_anti {F F' : Finset (Sym2 V)} (h : F ⊆ F') (U : Finset V) :
    (H.deleteEdges F').nbrSet U ⊆ (H.deleteEdges F).nbrSet U :=
  nbrSet_mono (deleteEdges_anti h) U

/-- Deleting all edges at `v` leaves `{v}` without outside neighbours. -/
theorem nbrSet_deleteEdges_edgesAt_eq_empty (v : V) :
    (H.deleteEdges (edgesAt H.edges v)).nbrSet {v} = ∅ := by
  rw [nbrSet_singleton]
  refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
  rw [mem_nbrs, deleteEdges_adj, mem_edgesAt] at hw
  exact hw.2 ⟨hw.1, Sym2.mem_mk_left v w⟩

/-- Deleting `F` lowers the degree of `v` by at most `deg_F(v)`. -/
theorem deg_le_deg_deleteEdges_add (F : Finset (Sym2 V)) (v : V) :
    H.deg v ≤ (H.deleteEdges F).deg v + degE F v := by
  rw [deg_eq_degE, deg_eq_degE, deleteEdges_edges, degE, degE, degE]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro e he
  rw [mem_edgesAt] at he
  rw [Finset.mem_union, mem_edgesAt, mem_edgesAt, Finset.mem_sdiff]
  by_cases heF : e ∈ F
  · exact Or.inr ⟨heF, he.2⟩
  · exact Or.inl ⟨⟨he.1, heF⟩, he.2⟩

theorem deg_deleteEdges_le (F : Finset (Sym2 V)) (v : V) : (H.deleteEdges F).deg v ≤ H.deg v :=
  deg_mono (deleteEdges_le F) v

/-- An edge of `H` has exactly two ends in `V(H)`. -/
theorem card_filter_mem_of_mem_edges {e : Sym2 V} (he : e ∈ H.edges) :
    (H.verts.filter (fun v => v ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := fun h => H.loopless _ he (Sym2.mk_isDiag_iff.2 h)
    have : H.verts.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v
      rw [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with rfl | rfl
        · exact H.edge_verts _ he v (Sym2.mem_mk_left v b)
        · exact H.edge_verts _ he v (Sym2.mem_mk_right a v)
    rw [this, Finset.card_pair hab]

/-- The handshake lemma: `∑_{v ∈ V(H)} d_H(v) = 2 |E(H)|`. -/
theorem sum_deg_eq_two_mul_card_edges : ∑ v ∈ H.verts, H.deg v = 2 * H.edges.card := by
  simp_rw [deg_eq_degE, degE, edgesAt, Finset.card_filter]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [← Finset.card_filter, card_filter_mem_of_mem_edges he, mul_one]

/-! ### Spanning subgraphs `H ∩ F` -/

@[simp] theorem restrictEdges_verts (F : Finset (Sym2 V)) :
    (H.restrictEdges F).verts = H.verts := rfl

@[simp] theorem mem_restrictEdges_edges {F : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ (H.restrictEdges F).edges ↔ e ∈ H.edges ∧ e ∈ F := Finset.mem_filter

theorem restrictEdges_le (F : Finset (Sym2 V)) : H.restrictEdges F ≤ H :=
  ⟨subset_rfl, Finset.filter_subset _ _⟩

theorem restrictEdges_eq_deleteEdges (F : Finset (Sym2 V)) :
    H.restrictEdges F = H.deleteEdges (H.edges \ F) := by
  ext e
  · rfl
  · simp only [mem_restrictEdges_edges, deleteEdges_edges, Finset.mem_sdiff]
    tauto

/-! ### Induced subgraphs `H[U]`, `H - U` -/

@[simp] theorem induce_verts (U : Finset V) : (H.induce U).verts = H.verts ∩ U := rfl

@[simp] theorem mem_induce_edges {U : Finset V} {e : Sym2 V} :
    e ∈ (H.induce U).edges ↔ e ∈ H.edges ∧ ∀ v ∈ e, v ∈ U := by
  unfold induce
  rw [Finset.mem_filter, Finset.mem_sym2_iff]

@[simp] theorem induce_adj {U : Finset V} {u v : V} :
    (H.induce U).Adj u v ↔ H.Adj u v ∧ u ∈ U ∧ v ∈ U := by
  rw [adj_iff, mem_induce_edges, adj_iff]
  constructor
  · rintro ⟨h, hU⟩
    exact ⟨h, hU u (Sym2.mem_mk_left u v), hU v (Sym2.mem_mk_right u v)⟩
  · rintro ⟨h, hu, hv⟩
    refine ⟨h, fun w hw => ?_⟩
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · exact hu
    · exact hv

theorem induce_verts_of_subset {U : Finset V} (hU : U ⊆ H.verts) : (H.induce U).verts = U :=
  Finset.inter_eq_right.2 hU

theorem induce_le (U : Finset V) : H.induce U ≤ H :=
  ⟨Finset.inter_subset_left, Finset.filter_subset _ _⟩

@[simp] theorem deleteVerts_verts (U : Finset V) : (H.deleteVerts U).verts = H.verts \ U := by
  unfold deleteVerts
  rw [induce_verts, Finset.inter_eq_right.2 Finset.sdiff_subset]

@[simp] theorem deleteVerts_adj {U : Finset V} {u v : V} :
    (H.deleteVerts U).Adj u v ↔ H.Adj u v ∧ u ∉ U ∧ v ∉ U := by
  unfold deleteVerts
  rw [induce_adj, Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · rintro ⟨h, ⟨-, hu⟩, ⟨-, hv⟩⟩
    exact ⟨h, hu, hv⟩
  · rintro ⟨h, hu, hv⟩
    exact ⟨h, ⟨h.mem_verts_left, hu⟩, ⟨h.mem_verts_right, hv⟩⟩

theorem deleteVerts_le (U : Finset V) : H.deleteVerts U ≤ H := induce_le _

/-! ### `E_H(A, B)` -/

@[simp] theorem mem_edgesBetween {A B : Finset V} {e : Sym2 V} :
    e ∈ H.edgesBetween A B ↔ e ∈ H.edges ∧ ∃ a ∈ A, ∃ b ∈ B, s(a, b) = e :=
  Finset.mem_filter

theorem edgesBetween_subset (A B : Finset V) : H.edgesBetween A B ⊆ H.edges :=
  Finset.filter_subset _ _

theorem edgesBetween_comm (A B : Finset V) : H.edgesBetween A B = H.edgesBetween B A := by
  ext e
  simp only [mem_edgesBetween]
  constructor
  · rintro ⟨he, a, ha, b, hb, rfl⟩
    exact ⟨he, b, hb, a, ha, Sym2.eq_swap⟩
  · rintro ⟨he, b, hb, a, ha, rfl⟩
    exact ⟨he, a, ha, b, hb, Sym2.eq_swap⟩

theorem eBetween_le (A B : Finset V) : H.eBetween A B ≤ H.edges.card :=
  Finset.card_le_card (edgesBetween_subset A B)

/-! ### `ofEdges` -/

@[simp] theorem ofEdges_verts (W : Finset V) (F : Finset (Sym2 V)) :
    (ofEdges W F).verts = W := rfl

@[simp] theorem mem_ofEdges_edges {W : Finset V} {F : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ (ofEdges W F).edges ↔ e ∈ F ∧ ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ W := by
  unfold ofEdges
  rw [Finset.mem_filter, Finset.mem_sym2_iff]

@[simp] theorem ofEdges_adj {W : Finset V} {F : Finset (Sym2 V)} {u v : V} :
    (ofEdges W F).Adj u v ↔ s(u, v) ∈ F ∧ u ≠ v ∧ u ∈ W ∧ v ∈ W := by
  rw [adj_iff, mem_ofEdges_edges, Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨h, hne, hW⟩
    exact ⟨h, hne, hW u (Sym2.mem_mk_left u v), hW v (Sym2.mem_mk_right u v)⟩
  · rintro ⟨h, hne, hu, hv⟩
    refine ⟨h, hne, fun w hw => ?_⟩
    rcases Sym2.mem_iff.1 hw with rfl | rfl
    · exact hu
    · exact hv

theorem ofEdges_edges_of_subset {W : Finset V} {F : Finset (Sym2 V)}
    (hF : ∀ e ∈ F, ¬ e.IsDiag) (hW : ∀ e ∈ F, ∀ v ∈ e, v ∈ W) : (ofEdges W F).edges = F := by
  ext e
  rw [mem_ofEdges_edges]
  exact ⟨fun h => h.1, fun h => ⟨h, hF e h, hW e h⟩⟩

@[simp] theorem ofEdges_self : ofEdges H.verts H.edges = H := by
  ext e
  · rfl
  · rw [ofEdges_edges_of_subset H.loopless H.edge_verts]

end DecEq

/-! ### Mathlib `SimpleGraph`s -/

section OfSimpleGraph

variable [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]

@[simp] theorem ofSimpleGraph_verts : (ofSimpleGraph G).verts = Finset.univ := rfl

@[simp] theorem ofSimpleGraph_edges : (ofSimpleGraph G).edges = G.edgeFinset := rfl

@[simp] theorem ofSimpleGraph_card : (ofSimpleGraph G).card = Fintype.card V := rfl

@[simp] theorem ofSimpleGraph_adj {u v : V} : (ofSimpleGraph G).Adj u v ↔ G.Adj u v := by
  rw [adj_iff, ofSimpleGraph_edges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]

theorem ofSimpleGraph_nbrs [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    (ofSimpleGraph G).nbrs v = G.neighborFinset v := by
  ext w
  rw [mem_nbrs, ofSimpleGraph_adj, SimpleGraph.mem_neighborFinset]

theorem ofSimpleGraph_deg [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    (ofSimpleGraph G).deg v = G.degree v := by
  rw [deg_def, ofSimpleGraph_nbrs, SimpleGraph.card_neighborFinset_eq_degree]

theorem coe_ofSimpleGraph_edges : ((ofSimpleGraph G).edges : Set (Sym2 V)) = G.edgeSet := by
  rw [ofSimpleGraph_edges, SimpleGraph.coe_edgeFinset]

end OfSimpleGraph

/-! ### The converse `toSimpleGraph` -/

section ToSimpleGraph

@[simp] theorem toSimpleGraph_adj {u v : V} : H.toSimpleGraph.Adj u v ↔ H.Adj u v := Iff.rfl

/-- The edge set of `H.toSimpleGraph` is `E(H)`. -/
@[simp] theorem edgeSet_toSimpleGraph : H.toSimpleGraph.edgeSet = (H.edges : Set (Sym2 V)) := by
  ext e
  induction e using Sym2.ind with
  | h u v => rw [SimpleGraph.mem_edgeSet, toSimpleGraph_adj, adj_iff, Finset.mem_coe]

/-- Round trip `SimpleGraph → FGraph → SimpleGraph`. -/
@[simp] theorem toSimpleGraph_ofSimpleGraph [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    (ofSimpleGraph G).toSimpleGraph = G := by
  ext u v
  rw [toSimpleGraph_adj, ofSimpleGraph_adj]

/-- Round trip `FGraph → SimpleGraph → FGraph`, for a graph whose vertex set is the whole
(finite) type. -/
theorem ofSimpleGraph_toSimpleGraph [Fintype V] [Fintype H.toSimpleGraph.edgeSet]
    (hV : H.verts = Finset.univ) : ofSimpleGraph H.toSimpleGraph = H := by
  ext e
  · rw [ofSimpleGraph_verts, hV]
  · rw [ofSimpleGraph_edges, SimpleGraph.mem_edgeFinset, edgeSet_toSimpleGraph, Finset.mem_coe]

theorem toSimpleGraph_mono {H' : FGraph V} (hle : H ≤ H') : H.toSimpleGraph ≤ H'.toSimpleGraph :=
  fun _ _ h => Adj.mono hle h

theorem toSimpleGraph_neighborFinset [Fintype V] [DecidableEq V] (v : V) :
    H.toSimpleGraph.neighborFinset v = H.nbrs v := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, toSimpleGraph_adj, mem_nbrs]

/-- The Mathlib degree of `v` in `H.toSimpleGraph` is `d_H(v)`. -/
theorem toSimpleGraph_degree [Fintype V] [DecidableEq V] (v : V) :
    H.toSimpleGraph.degree v = H.deg v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, toSimpleGraph_neighborFinset, deg_def]

end ToSimpleGraph

end FGraph

/-! ## Paths -/

section Walk

@[simp] theorem walkEdges_nil : walkEdges ([] : List V) = [] := rfl

@[simp] theorem walkEdges_singleton (v : V) : walkEdges [v] = [] := rfl

@[simp] theorem walkEdges_cons_cons (a b : V) (l : List V) :
    walkEdges (a :: b :: l) = s(a, b) :: walkEdges (b :: l) := rfl

@[simp] theorem pathLength_nil : pathLength ([] : List V) = 0 := rfl

@[simp] theorem pathLength_cons (a : V) (l : List V) : pathLength (a :: l) = l.length := by
  simp [pathLength]

theorem length_walkEdges (p : List V) : (walkEdges p).length = pathLength p := by
  simp [walkEdges, pathLength, List.length_zipWith]

/-- Every end of an edge of the walk `p` is a vertex of `p`. -/
theorem mem_of_mem_walkEdges {p : List V} {e : Sym2 V} (he : e ∈ walkEdges p) {v : V}
    (hv : v ∈ e) : v ∈ p := by
  induction p with
  | nil => simp at he
  | cons a t ih =>
    cases t with
    | nil => simp at he
    | cons b t =>
      rw [walkEdges_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rcases Sym2.mem_iff.1 hv with rfl | rfl <;> simp
      · exact List.mem_cons_of_mem _ (ih he)

/-- Every vertex of a walk with at least one edge lies on one of its edges. -/
theorem exists_mem_walkEdges_of_mem :
    ∀ {p : List V}, 2 ≤ p.length → ∀ {v : V}, v ∈ p → ∃ e ∈ walkEdges p, v ∈ e
  | [], h, _, _ => by simp at h
  | [_], h, _, _ => by simp at h
  | a :: b :: t, _, v, hv => by
    rw [walkEdges_cons_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨s(v, b), List.mem_cons_self .., Sym2.mem_mk_left _ _⟩
    · cases t with
      | nil =>
        rw [List.mem_singleton] at hv
        subst hv
        exact ⟨s(a, v), List.mem_cons_self .., Sym2.mem_mk_right _ _⟩
      | cons c t =>
        obtain ⟨e, he, hve⟩ := exists_mem_walkEdges_of_mem (p := b :: c :: t) (by simp) hv
        exact ⟨e, List.mem_cons_of_mem _ he, hve⟩

/-- The edges of a path are pairwise distinct. -/
theorem nodup_walkEdges {p : List V} (hp : p.Nodup) : (walkEdges p).Nodup := by
  induction p with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t =>
      rw [walkEdges_cons_cons, List.nodup_cons]
      rw [List.nodup_cons] at hp
      exact ⟨fun h => hp.1 (mem_of_mem_walkEdges h (Sym2.mem_mk_left a b)), ih hp.2⟩

theorem walkEdges_concat (l : List V) (a : V) :
    walkEdges (l ++ [a]) = walkEdges l ++ (l.getLast?.map (fun b => s(b, a))).toList := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    cases l with
    | nil => rfl
    | cons d l =>
      rw [List.cons_append, List.cons_append, walkEdges_cons_cons, ← List.cons_append, ih,
        walkEdges_cons_cons, List.getLast?_cons_cons, List.cons_append]

theorem walkEdges_reverse (p : List V) : walkEdges p.reverse = (walkEdges p).reverse := by
  induction p with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, walkEdges_concat, ih, List.getLast?_reverse]
    cases t with
    | nil => rfl
    | cons b t =>
      rw [walkEdges_cons_cons, List.reverse_cons, List.head?_cons]
      simp [Sym2.eq_swap]

@[simp] theorem pathLength_reverse (p : List V) : pathLength p.reverse = pathLength p := by
  simp [pathLength]

theorem interior_reverse (p : List V) : interior p.reverse = (interior p).reverse := by
  simp [interior, List.tail_dropLast]

@[simp] theorem interior_nil : interior ([] : List V) = [] := rfl

@[simp] theorem interior_singleton (v : V) : interior [v] = [] := rfl

@[simp] theorem interior_pair (u v : V) : interior [u, v] = [] := rfl

theorem interior_subset (p : List V) : interior p ⊆ p := fun _ hv =>
  List.mem_of_mem_tail (List.dropLast_subset _ hv)

variable {E E' : Finset (Sym2 V)} {W W' : Finset V} {p : List V} {x y : V}

theorem IsPathIn.ne_nil (h : IsPathIn E p) : p ≠ [] := h.1

theorem IsPathIn.nodup (h : IsPathIn E p) : p.Nodup := h.2.1

theorem IsPathIn.edges_mem (h : IsPathIn E p) {e : Sym2 V} (he : e ∈ walkEdges p) : e ∈ E :=
  h.2.2 e he

theorem IsPathIn.mono (h : IsPathIn E p) (hE : E ⊆ E') : IsPathIn E' p :=
  ⟨h.1, h.2.1, fun e he => hE (h.2.2 e he)⟩

theorem IsPathIn.reverse (h : IsPathIn E p) : IsPathIn E p.reverse := by
  refine ⟨by simpa using h.1, List.nodup_reverse.2 h.2.1, fun e he => h.2.2 e ?_⟩
  rw [walkEdges_reverse, List.mem_reverse] at he
  exact he

theorem isPathIn_singleton (v : V) : IsPathIn E [v] :=
  ⟨List.cons_ne_nil _ _, List.nodup_singleton v, by simp⟩

theorem isPathIn_pair {u v : V} : IsPathIn E [u, v] ↔ u ≠ v ∧ s(u, v) ∈ E := by
  simp [IsPathIn]

/-- The vertices of a path with at least one edge in `E(H)` are vertices of `H`. -/
theorem IsPathIn.mem_verts {H : FGraph V} (h : IsPathIn H.edges p) (hlen : 1 ≤ pathLength p)
    {v : V} (hv : v ∈ p) : v ∈ H.verts := by
  have h2 : 2 ≤ p.length := by unfold pathLength at hlen; omega
  obtain ⟨e, he, hve⟩ := exists_mem_walkEdges_of_mem h2 hv
  exact H.edge_verts e (h.edges_mem he) v hve

theorem IsPathBetween.mono (h : IsPathBetween E x y p) (hE : E ⊆ E') :
    IsPathBetween E' x y p :=
  ⟨h.1.mono hE, h.2⟩

theorem IsPathBetween.reverse (h : IsPathBetween E x y p) : IsPathBetween E y x p.reverse :=
  ⟨h.1.reverse, by rw [List.head?_reverse]; exact h.2.2, by rw [List.getLast?_reverse]; exact h.2.1⟩

theorem IsPathBetween.left_mem (h : IsPathBetween E x y p) : x ∈ p :=
  List.mem_of_mem_head? h.2.1

theorem IsPathBetween.right_mem (h : IsPathBetween E x y p) : y ∈ p :=
  List.mem_of_getLast? h.2.2

/-- An `xy`-path with `x ≠ y` has at least one edge. -/
theorem IsPathBetween.one_le_pathLength (h : IsPathBetween E x y p) (hxy : x ≠ y) :
    1 ≤ pathLength p := by
  match p, h with
  | [], h => exact absurd rfl h.1.1
  | [a], h =>
    have hx : a = x := by simpa using h.2.1
    have hy : a = y := by simpa using h.2.2
    exact absurd (hx.symm.trans hy) hxy
  | _ :: _ :: t, _ => simp

/-- An `xy`-path with `x ≠ y` and at most one edge is the single edge `xy`. -/
theorem IsPathBetween.eq_pair (h : IsPathBetween E x y p) (hxy : x ≠ y)
    (hl : pathLength p ≤ 1) : p = [x, y] := by
  match p, h, hl with
  | [], h, _ => exact absurd rfl h.1.1
  | [a], h, _ =>
    have hx : a = x := by simpa using h.2.1
    have hy : a = y := by simpa using h.2.2
    exact absurd (hx.symm.trans hy) hxy
  | [a, b], h, _ =>
    have hx : a = x := by simpa using h.2.1
    have hy : b = y := by simpa using h.2.2
    rw [hx, hy]
  | _ :: _ :: _ :: _, _, hl => simp at hl

/-- The first edge of an `xy`-path with `x ≠ y` is an edge `xb` of the path lying in `E`. -/
theorem IsPathBetween.exists_first_edge (h : IsPathBetween E x y p) (hxy : x ≠ y) :
    ∃ b, s(x, b) ∈ walkEdges p ∧ s(x, b) ∈ E := by
  match p, h with
  | [], h => exact absurd rfl h.1.1
  | [a], h =>
    have hx : a = x := by simpa using h.2.1
    have hy : a = y := by simpa using h.2.2
    exact absurd (hx.symm.trans hy) hxy
  | a :: b :: t, h =>
    have hx : a = x := by simpa using h.2.1
    subst hx
    have he : s(a, b) ∈ walkEdges (a :: b :: t) := by simp
    exact ⟨b, he, h.1.edges_mem he⟩

theorem isPathBetween_pair {u v : V} :
    IsPathBetween E u v [u, v] ↔ u ≠ v ∧ s(u, v) ∈ E := by
  simp [IsPathBetween, isPathIn_pair]

theorem IsThrough.mono (h : IsThrough W p) (hW : W ⊆ W') : IsThrough W' p :=
  fun v hv => hW (h v hv)

theorem IsThrough.reverse (h : IsThrough W p) : IsThrough W p.reverse := by
  intro v hv
  rw [interior_reverse, List.mem_reverse] at hv
  exact h v hv

@[simp] theorem isThrough_singleton (v : V) : IsThrough W [v] := by simp [IsThrough]

@[simp] theorem isThrough_pair (u v : V) : IsThrough W [u, v] := by simp [IsThrough]

/-- The edges of `p` are pairwise distinct edges of `E`, so a path has at most `|E|` edges. -/
theorem IsPathIn.pathLength_le_card (h : IsPathIn E p) : pathLength p ≤ E.card := by
  classical
  rw [← length_walkEdges, ← List.toFinset_card_of_nodup (nodup_walkEdges h.nodup)]
  exact Finset.card_le_card fun e he => h.edges_mem (List.mem_toFinset.1 he)

/-- The ends of an `xy`-path with `x ≠ y` in `E(H)` are vertices of `H`. (For `x = y` the path
may be `[x]` with `x ∉ V(H)`.) -/
theorem IsPathBetween.left_mem_verts {H : FGraph V} (h : IsPathBetween H.edges x y p)
    (hxy : x ≠ y) : x ∈ H.verts :=
  h.1.mem_verts (h.one_le_pathLength hxy) h.left_mem

theorem IsPathBetween.right_mem_verts {H : FGraph V} (h : IsPathBetween H.edges x y p)
    (hxy : x ≠ y) : y ∈ H.verts :=
  h.1.mem_verts (h.one_le_pathLength hxy) h.right_mem

/-! ### Mathlib walks -/

/-- The list `walkEdges` of the support of a Mathlib walk is its edge list. -/
theorem walkEdges_support {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    walkEdges w.support = w.edges := by
  induction w with
  | nil => rfl
  | @cons a b c h q ih =>
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons, ← ih,
      ← SimpleGraph.Walk.cons_tail_support q, walkEdges_cons_cons]

theorem pathLength_support {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    pathLength w.support = w.length := by
  rw [pathLength, SimpleGraph.Walk.length_support, Nat.add_sub_cancel]

/-- A Mathlib path in `H.toSimpleGraph` gives a list path in `E(H)` with the same ends. -/
theorem isPathBetween_support {H : FGraph V} {w : H.toSimpleGraph.Walk x y} (hw : w.IsPath) :
    IsPathBetween H.edges x y w.support := by
  refine ⟨⟨w.support_ne_nil, hw.support_nodup, fun e he => ?_⟩, ?_, ?_⟩
  · rw [walkEdges_support] at he
    have := w.edges_subset_edgeSet he
    rwa [FGraph.edgeSet_toSimpleGraph, Finset.mem_coe] at this
  · rw [← SimpleGraph.Walk.cons_tail_support w, List.head?_cons]
  · rw [List.getLast?_eq_some_getLast w.support_ne_nil, SimpleGraph.Walk.getLast_support]

/-- A list `xy`-path in `E(H)` is the support of a Mathlib path in `H.toSimpleGraph`, with the
same length. -/
theorem IsPathBetween.exists_walk {H : FGraph V} (h : IsPathBetween H.edges x y p) :
    ∃ w : H.toSimpleGraph.Walk x y, w.IsPath ∧ w.support = p ∧ w.length = pathLength p := by
  suffices ∃ w : H.toSimpleGraph.Walk x y, w.IsPath ∧ w.support = p by
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨w, hw, rfl, (pathLength_support w).symm⟩
  induction p generalizing x with
  | nil => exact absurd rfl h.1.1
  | cons a t ih =>
    have hx : a = x := by simpa using h.2.1
    subst hx
    cases t with
    | nil =>
      have hy : a = y := by simpa using h.2.2
      subst hy
      exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, rfl⟩
    | cons b t =>
      have hnd := h.1.nodup
      rw [List.nodup_cons] at hnd
      have hab : H.toSimpleGraph.Adj a b := h.1.edges_mem (by simp)
      have h' : IsPathBetween H.edges b y (b :: t) := by
        refine ⟨⟨List.cons_ne_nil _ _, hnd.2, fun e he => h.1.edges_mem ?_⟩, rfl, ?_⟩
        · rw [walkEdges_cons_cons]; exact List.mem_cons_of_mem _ he
        · rw [← h.2.2, List.getLast?_cons_cons]
      obtain ⟨w, hw, hws⟩ := ih h'
      refine ⟨SimpleGraph.Walk.cons hab w, hw.cons (by rw [hws]; exact hnd.1), ?_⟩
      rw [SimpleGraph.Walk.support_cons, hws]

end Walk

/-! ## Balls `B^i_H(U, W)` -/

section Ball

variable {H H' : FGraph V} {i j : ℕ} {U U' W W' : Finset V} {w : V}

theorem mem_ball : w ∈ ball H i U W ↔ w ∈ W ∧ ∃ u ∈ U, ∃ p : List V,
    IsPathBetween H.edges u w p ∧ IsThrough W p ∧ pathLength p ≤ i := by
  classical
  unfold ball
  simp only [Finset.mem_filter]

/-- `B^i_H(U, W) ⊆ W`. -/
theorem ball_subset : ball H i U W ⊆ W := fun _ hw => (mem_ball.1 hw).1

/-- `B^i_H(U, W) ⊆ V(H)` when `W ⊆ V(H)` (as in the manuscript, where `U, V ⊆ V(H)`). Without
`W ⊆ V(H)` the ball can contain non-vertices of `U ∩ W` (paths `[u]` of length `0`). -/
theorem ball_subset_verts (hW : W ⊆ H.verts) : ball H i U W ⊆ H.verts := ball_subset.trans hW

theorem ball_mono_radius (hij : i ≤ j) : ball H i U W ⊆ ball H j U W := by
  intro w hw
  obtain ⟨hwW, u, hu, p, hp, hpW, hpl⟩ := mem_ball.1 hw
  exact mem_ball.2 ⟨hwW, u, hu, p, hp, hpW, hpl.trans hij⟩

theorem ball_mono_left (hU : U ⊆ U') : ball H i U W ⊆ ball H i U' W := by
  intro w hw
  obtain ⟨hwW, u, hu, p, hp, hpW, hpl⟩ := mem_ball.1 hw
  exact mem_ball.2 ⟨hwW, u, hU hu, p, hp, hpW, hpl⟩

theorem ball_mono_right (hW : W ⊆ W') : ball H i U W ⊆ ball H i U W' := by
  intro w hw
  obtain ⟨hwW, u, hu, p, hp, hpW, hpl⟩ := mem_ball.1 hw
  exact mem_ball.2 ⟨hW hwW, u, hu, p, hp, hpW.mono hW, hpl⟩

theorem ball_mono_edges (hE : H.edges ⊆ H'.edges) : ball H i U W ⊆ ball H' i U W := by
  intro w hw
  obtain ⟨hwW, u, hu, p, hp, hpW, hpl⟩ := mem_ball.1 hw
  exact mem_ball.2 ⟨hwW, u, hu, p, hp.mono hE, hpW, hpl⟩

theorem ball_mono (hle : H ≤ H') : ball H i U W ⊆ ball H' i U W := ball_mono_edges hle.2

/-- The vertices of `U ∩ W` lie in every ball (paths of length `0`). -/
theorem inter_subset_ball [DecidableEq V] : U ∩ W ⊆ ball H i U W := by
  intro w hw
  rw [Finset.mem_inter] at hw
  exact mem_ball.2 ⟨hw.2, w, hw.1, [w], ⟨isPathIn_singleton w, rfl, rfl⟩, isThrough_singleton w,
    by simp⟩

end Ball

/-! ## Expanders ([s1:citDef11]) -/

namespace FGraph

variable [DecidableEq V] {G : FGraph V} {ε s ε' s' : ℝ}

/-- Expansion becomes weaker when `ε` or `s` decrease ([s3:lemMonotone] (i), second claim). -/
theorem IsExpander.mono (hG : G.IsExpander ε s) (hε : ε' ≤ ε) (hs : s' ≤ s) :
    G.IsExpander ε' s' := by
  intro U F hU hF h1 h2 h3
  have key := hG U F hU hF h1 h2
    (h3.trans (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)))
  refine le_trans ?_ key
  gcongr

/-- Adding edges (keeping the vertex set) preserves expansion ([s3:lemMonotone] (i), first
claim). -/
theorem IsExpander.of_le {H : FGraph V} (hG : G.IsExpander ε s) (hle : G ≤ H)
    (hV : G.verts = H.verts) : H.IsExpander ε s := by
  intro U F hU hF h1 h2 h3
  have hcard : G.card = H.card := by rw [card_def, card_def, hV]
  have hFc : ((F ∩ G.edges).card : ℝ) ≤ F.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have key := hG U (F ∩ G.edges) (hV ▸ hU) Finset.inter_subset_right h1 (by rw [hcard]; exact h2)
    (hFc.trans h3)
  rw [hcard] at key
  refine key.trans ?_
  gcongr
  refine nbrSet_mono ⟨?_, ?_⟩ U
  · rw [deleteEdges_verts, deleteEdges_verts, hV]
  · intro e he
    rw [deleteEdges_edges, Finset.mem_sdiff, Finset.mem_inter] at he
    rw [deleteEdges_edges, Finset.mem_sdiff]
    exact ⟨hle.2 he.1, fun heF => he.2 ⟨heF, he.1⟩⟩

/-- A graph with at most one vertex is an `(ε,s)`-expander for all `ε`, `s` (no `U` satisfies
`1 ≤ |U| ≤ 2n/3`). -/
theorem isExpander_of_card_le_one (hn : G.card ≤ 1) : G.IsExpander ε s := by
  intro U F _ _ h1 h2 _
  exfalso
  have h1' : (1 : ℝ) ≤ U.card := by exact_mod_cast h1
  have hn' : (G.card : ℝ) ≤ 1 := by exact_mod_cast hn
  linarith

/-- For `ε ≤ 0` the expansion condition is empty: every graph is an `(ε,s)`-expander. (This is
why `EG.FGraph.IsExpander.lt_deg` needs `0 < ε`.) -/
theorem isExpander_of_nonpos (hε : ε ≤ 0) : G.IsExpander ε s := by
  intro U F _ _ _ _ _
  have : ε * U.card / Real.logb 2 G.card ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hε (Nat.cast_nonneg _))
      (sq_nonneg _)
  exact this.trans (Nat.cast_nonneg _)

/-- [s1:citDef11] Remark of B–M: "if `n ≥ 2` then, for every `v ∈ V(G)`, the pair `U = {v}`,
`F = {edges at v}` violates this inequality, so necessarily `|F| > s`; hence `δ(G) > s` for every
`(ε,s)`-expander `G` on at least two vertices." (With `0 < ε`, implicit in B–M; see
`EG.FGraph.isExpander_of_nonpos`.) -/
theorem IsExpander.lt_deg (hG : G.IsExpander ε s) (hε : 0 < ε) (hn : 2 ≤ G.card) {v : V}
    (hv : v ∈ G.verts) : s < G.deg v := by
  by_contra hcon
  rw [not_lt] at hcon
  have hU1 : ({v} : Finset V).card = 1 := Finset.card_singleton v
  have hn' : (2 : ℝ) ≤ G.card := by exact_mod_cast hn
  have key := hG {v} (edgesAt G.edges v) (Finset.singleton_subset_iff.2 hv)
    (edgesAt_subset _ _) (by rw [hU1]) (by rw [hU1]; push_cast; linarith)
    (by rw [hU1, Nat.cast_one, mul_one]; rw [deg_eq_degE] at hcon; exact hcon)
  rw [nbrSet_deleteEdges_edgesAt_eq_empty, Finset.card_empty, hU1] at key
  have hlog : 0 < Real.logb 2 G.card := Real.logb_pos (by norm_num) (by linarith)
  have hpos : 0 < ε * ((1 : ℕ) : ℝ) / Real.logb 2 G.card ^ 2 := by
    rw [Nat.cast_one, mul_one]; positivity
  push_cast at key hpos
  linarith

/-- [s1:citDef11] Remark of B–M, in the form `δ(G) > s`. -/
theorem IsExpander.lt_minDeg (hG : G.IsExpander ε s) (hε : 0 < ε) (hn : 2 ≤ G.card) :
    s < G.minDeg := by
  have hne : G.verts.Nonempty := Finset.card_pos.1 (by rw [← card_def]; omega)
  exact (lt_minDeg_iff hne).2 fun v hv => hG.lt_deg hε hn hv

/-! ## Path connectivity ([s1:citDef7]) -/

variable {ℓ ℓ' t t' : ℝ} {W W' : Finset V}

/-- Definition 7 ([s1:citDef7]) applied to a multiset of pairs indexed by a finite type in any
universe. -/
theorem IsPathConnected.exists_paths (hG : G.IsPathConnected ℓ t W) {ι : Type*} [Fintype ι]
    (P : ι → V × V) (hP : ∀ i, (P i).1 ∈ G.verts ∧ (P i).2 ∈ G.verts ∧ (P i).1 ≠ (P i).2)
    (ht : ∀ v : V, ((Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤ t) :
    ∃ Q : ι → List V,
      (∀ i, IsPathBetween G.edges (P i).1 (P i).2 (Q i) ∧ IsThrough W (Q i) ∧
        (pathLength (Q i) : ℝ) ≤ ℓ) ∧
      ∀ i j, i ≠ j → (walkEdges (Q i)).Disjoint (walkEdges (Q j)) := by
  let e := Fintype.equivFin ι
  obtain ⟨Q, hQ, hdisj⟩ := hG (Fin (Fintype.card ι)) (fun k => P (e.symm k))
    (fun k => hP (e.symm k)) (fun v => by
      refine le_trans (le_of_eq ?_) (ht v)
      congr 1
      refine Finset.card_equiv e.symm fun k => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  refine ⟨fun i => Q (e i), fun i => ?_, fun i j hij => hdisj _ _ (e.injective.ne hij)⟩
  have := hQ (e i)
  simp only [e, Equiv.symm_apply_apply] at this
  exact this

/-- Joint routing ([s3:lemMonotone] (iii)): "If several multisets `𝒫_1, …, 𝒫_q` are given and
every vertex lies in at most `t` pairs of the union multiset `𝒫_1 + ⋯ + 𝒫_q`, then one
application of the property to this union joins all their pairs by pairwise edge-disjoint paths
through `V` of length at most `ℓ`." The multisets are families `P k : ι k → V × V`, `k : κ`; the
multiplicity of `v` in the union is the sum over `k` of its multiplicities. -/
theorem IsPathConnected.exists_paths_sigma (hG : G.IsPathConnected ℓ t W) {κ : Type*}
    [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] (P : ∀ k, ι k → V × V)
    (hP : ∀ k i, (P k i).1 ∈ G.verts ∧ (P k i).2 ∈ G.verts ∧ (P k i).1 ≠ (P k i).2)
    (ht : ∀ v : V,
      ((∑ k, (Finset.univ.filter (fun i => (P k i).1 = v ∨ (P k i).2 = v)).card : ℕ) : ℝ) ≤ t) :
    ∃ Q : ∀ k, ι k → List V,
      (∀ k i, IsPathBetween G.edges (P k i).1 (P k i).2 (Q k i) ∧ IsThrough W (Q k i) ∧
        (pathLength (Q k i) : ℝ) ≤ ℓ) ∧
      ∀ k i k' j, (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ →
        (walkEdges (Q k i)).Disjoint (walkEdges (Q k' j)) := by
  classical
  obtain ⟨Q, hQ, hdisj⟩ := hG.exists_paths (fun x : Σ k, ι k => P x.1 x.2)
    (fun x => hP x.1 x.2) (fun v => by
      refine le_trans (le_of_eq ?_) (ht v)
      congr 1
      rw [Finset.card_filter, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.card_filter])
  exact ⟨fun k i => Q ⟨k, i⟩, fun k i => hQ ⟨k, i⟩, fun k i k' j h => hdisj _ _ h⟩

/-- Path connectivity is monotone ([s3:lemMonotone] (ii)): for `G ≤ G'` with `V(G) = V(G')`,
`W ⊆ W'`, `ℓ ≤ ℓ'` and `t' ≤ t`, `(ℓ,t)`-path connectivity of `G` through `W` implies
`(ℓ',t')`-path connectivity of `G'` through `W'`. -/
theorem IsPathConnected.mono {G' : FGraph V} (hG : G.IsPathConnected ℓ t W) (hle : G ≤ G')
    (hV : G.verts = G'.verts) (hW : W ⊆ W') (hℓ : ℓ ≤ ℓ') (ht : t' ≤ t) :
    G'.IsPathConnected ℓ' t' W' := by
  intro ι _ P hP hPt
  obtain ⟨Q, hQ, hdisj⟩ := hG ι P (fun i => by rw [hV]; exact hP i) (fun v => (hPt v).trans ht)
  exact ⟨Q, fun i => ⟨(hQ i).1.mono hle.2, (hQ i).2.1.mono hW, (hQ i).2.2.trans hℓ⟩, hdisj⟩

/-- The multiplicity bound only matters through `⌊t⌋₊`: for real `t ≥ 0`, `(ℓ,t)`-path
connectivity is `(ℓ,⌊t⌋₊)`-path connectivity (a count is at most `t` iff it is at most
`⌊t⌋₊`). -/
theorem isPathConnected_natFloor_iff (ht : 0 ≤ t) :
    G.IsPathConnected ℓ t W ↔ G.IsPathConnected ℓ (⌊t⌋₊ : ℝ) W := by
  have key : ∀ n : ℕ, (n : ℝ) ≤ t ↔ (n : ℝ) ≤ (⌊t⌋₊ : ℝ) := fun n => by
    rw [Nat.cast_le, Nat.le_floor_iff ht]
  unfold IsPathConnected
  simp only [key]

/-- For `t < 1` path connectivity holds trivially: no non-empty family of pairs has all
multiplicities `≤ t`. (The manuscript only uses `t ≥ 1`.) -/
theorem isPathConnected_of_lt_one (ht : t < 1) : G.IsPathConnected ℓ t W := by
  intro ι _ P _ hPt
  by_cases hι : IsEmpty ι
  · exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  · exfalso
    obtain ⟨i⟩ := not_isEmpty_iff.1 hι
    have hpos : 1 ≤ (Finset.univ.filter (fun j => (P j).1 = (P i).1 ∨ (P j).2 = (P i).1)).card :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, Or.inl rfl⟩⟩
    have := hPt (P i).1
    have hpos' : (1 : ℝ) ≤ _ := Nat.one_le_cast.2 hpos
    linarith

end FGraph

end EG
