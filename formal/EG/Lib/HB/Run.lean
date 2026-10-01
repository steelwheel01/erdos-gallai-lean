module

public import EG.Defs.HB.Run
public import EG.Lib.HB.SplitTree

/-!
# Rounds and runs of `HB*^{τ+}`: basic API (companion of `EG.Defs.HB.Round`, `EG.Defs.HB.Run`)

Round level (`EG.HB.Round`):
* `G'_l ≤ G_l`, `G_{l+1} ≤ G'_l`, `V(G_{l+1}) = V(G_l)`, `E(G_{l+1})` = the passed edges;
* (R5) as one assignment function: `mem_E`, `mem_passed`, `E` of distinct addresses are
  disjoint, an edge of `G'_l` is passed down or in exactly the `E` of its assigned address, and
  `assign` returns only pre-part addresses;
* `D_l = {v : μ_l(v) ≥ 2}` (`Round.mem_D`); `S_Z ⊆ Z^0`, `V(Z) ⊆ Z^0`; `mem_Std`;
* `X^0_Z ≤ G'_l ≤ G_l`, `Z^0 ⊆ V(G_l)`, `X_Z ≤ X^0_Z`, `V(partGraph) = V(Z)`, and
  `E_l(Z) ⊆ V(Z)^{(2)}` (`E_subset_sym2`, checked through the three steps of `assign`);
* pieces: `bigPieceAddrs` (`|𝒫| ≥ P_l`), `X0_append` (graft), and the first form of the pre-parts
  (`exists_tauRun_leaf_of_mem_prePartAddrs`: a pre-part is `q ++ b` for its big piece
  `q = pieceOf a` and a leaf `b` of the `τ`-run of `q`, with
  `X^0 = (tauRun q).graphAtD (piece q) b`; converse `append_mem_prePartAddrs`),
  `pieceOf_mem_pieceAddrs`, `pieceOf_mem_bigPieceAddrs`;
* the two-level recursion: `wf_twoLevel`, `deleted_twoLevel` (the deleted edges are those of the
  `τ`-runs of the big pieces), `tree0_dup_subset_DupStar`, `tauRun_dup_subset_DupStar`,
  `existsUnique_piece_of_notMem_DupStar`; (GC) as `eBetween` (`isGC_iff_eBetween`).

Run level (`EG.HB.Run`):
* the recursion of `G_l`: `graph_one`, `graph_succ_of_isRound`, `graph_succ_of_not_isRound`;
  `V(G_l) = V(G)` (`graph_verts`), so `d_l = 2|E(G_l)|/n`; edges are antitone in `l`
  (`graph_edges_subset_of_le`) and `G_l` is stationary for `l ≥ R + 1` (`graph_of_R_lt`);
* the guarded objects vanish outside `[1,R]`;
* parts and ancestors: `mem_parts`, `mem_lightParts`, `mem_anc`, `anc_eq_empty_of_le_two`
  (TRIAGE §2.1 test "`anc G l x = ∅` for `l ≤ 2`"), `nuAnc_eq_zero_of_le_two`,
  `fresh_eq_ports_of_le_two`, `mem_D_iff` (`D_r = {w : μ_r(w) ≥ 2}`), `mult_le_mu`;
* the run-level versions of the round lemmas above (`Z0_subset_verts : Z^0 ⊆ V(G)`,
  `X0_le_graph'`, `E_subset_sym2`, `pieceOf_mem_bigPieceAddrs`,
  `exists_tauRun_leaf_of_mem_prePartAddrs`, …), `Valid.isTauRun` (the `τ`-run of a big piece),
  `thetaGC_eq` (address form of `θ^GC`), `ancEps_of_isLight` (`ε_Y = ε/2`),
  `ancEps_of_not_isLight` (`ε_Y = ε`);
* `E(Cyc_l)`: `cycEdges_of_isRound`, `graph'_eq_deleteEdges`, `cycEdges_subset_graph_edges`;
  run-level `Valid.wf_twoLevel`, `Valid.deleted_twoLevel`, `tauRun_dup_subset_DupStar`,
  `tree0_dup_subset_DupStar`, `existsUnique_piece_of_notMem_DupStar`, `isGC_iff_eBetween`;
* the run without rounds: `valid_nil_iff`.

Reading rule: `run.tauRun l q` is meaningful only for `q ∈ run.bigPieceAddrs G l`; elsewhere it
is an unconstrained choice.
-/

public section

namespace EG.HB

variable {V : Type*} [DecidableEq V]

namespace Round

variable (H : FGraph V) (c : RoundChoice V)

@[simp] theorem graph'_verts : (graph' H c).verts = H.verts := rfl

theorem graph'_le : graph' H c ≤ H := H.deleteEdges_le _

@[simp] theorem next_verts : (next H c).verts = H.verts := rfl

@[simp] theorem next_edges : (next H c).edges = passed H c := rfl

theorem mem_E {a : Addr} {e : Sym2 V} :
    e ∈ E H c a ↔ e ∈ (graph' H c).edges ∧ assign H c e = some a := Finset.mem_filter

theorem mem_passed {e : Sym2 V} :
    e ∈ passed H c ↔ e ∈ (graph' H c).edges ∧ assign H c e = none := Finset.mem_filter

theorem passed_subset : passed H c ⊆ (graph' H c).edges := Finset.filter_subset _ _

theorem E_subset (a : Addr) : E H c a ⊆ (graph' H c).edges := Finset.filter_subset _ _

theorem next_le_graph' : next H c ≤ graph' H c := ⟨subset_rfl, passed_subset H c⟩

theorem next_le : next H c ≤ H := le_trans (next_le_graph' H c) (graph'_le H c)

/-- (R5): the sets `E_l(Z)` of distinct pre-parts are disjoint. -/
theorem disjoint_E {a b : Addr} (hab : a ≠ b) : Disjoint (E H c a) (E H c b) := by
  rw [Finset.disjoint_left]
  intro e ha hb
  rw [mem_E] at ha hb
  exact hab (Option.some_injective _ (ha.2.symm.trans hb.2))

/-- (R5): an edge of `G'_l` passes down or is assigned (to exactly one address). -/
theorem mem_passed_or_mem_E {e : Sym2 V} (he : e ∈ (graph' H c).edges) :
    e ∈ passed H c ∨ ∃ a, e ∈ E H c a := by
  cases h : assign H c e with
  | none => exact Or.inl ((mem_passed H c).2 ⟨he, h⟩)
  | some a => exact Or.inr ⟨a, (mem_E H c).2 ⟨he, h⟩⟩

theorem disjoint_passed_E (a : Addr) : Disjoint (passed H c) (E H c a) := by
  rw [Finset.disjoint_left]
  intro e hp hE
  rw [mem_passed] at hp
  rw [mem_E] at hE
  rw [hp.2] at hE
  simp at hE

/-- (R5) assigns edges only to pre-parts (listed in the home order). -/
theorem assign_mem {e : Sym2 V} {a : Addr} (h : assign H c e = some a) :
    a ∈ prePartAddrs H c ∧ a ∈ c.homeOrder := by
  unfold assign at h
  rcases Option.or_eq_some_iff.1 h with h1 | ⟨-, h2⟩
  · have := List.find?_some h1
    simp only [decide_eq_true_eq] at this
    exact ⟨this.1, List.mem_of_find?_eq_some h1⟩
  · rcases Option.or_eq_some_iff.1 h2 with h3 | ⟨-, h4⟩
    · have := List.find?_some h3
      simp only [decide_eq_true_eq] at this
      exact ⟨this.1, List.mem_of_find?_eq_some h3⟩
    · have := List.find?_some h4
      simp only [decide_eq_true_eq] at this
      exact ⟨this.1, List.mem_of_find?_eq_some h4⟩

theorem mem_prePartAddrs_of_mem_E {a : Addr} {e : Sym2 V} (he : e ∈ E H c a) :
    a ∈ prePartAddrs H c := (assign_mem H c ((mem_E H c).1 he).2).1

/-- [s2:defAncestors] "so `D_r = {w : μ_r(w) ≥ 2}`". -/
theorem mem_D {v : V} : v ∈ D H c ↔ 2 ≤ mu H c v := by
  unfold D
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hpos : 0 < ((prePartAddrs H c).filter (fun a => v ∈ Z0 H c a)).card := by
    unfold mu at h; omega
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_filter] at ha
  exact Finset.mem_biUnion.2 ⟨a, ha.1, ha.2⟩

theorem guests_subset (a : Addr) : guests H c a ⊆ Z0 H c a := fun _ hv =>
  (Finset.mem_inter.1 (Finset.mem_filter.1 hv).1).1

theorem partVerts_subset (a : Addr) : partVerts H c a ⊆ Z0 H c a := by
  unfold partVerts
  split_ifs
  · exact Finset.sdiff_subset
  · exact subset_rfl

theorem mem_Std {a : Addr} : a ∈ Std H c ↔ a ∈ prePartAddrs H c ∧ ¬ isLight H c a := by
  classical
  simp only [Std, Finset.mem_filter]

/-! #### Leaf graphs, part graphs and `E_l(Z)` -/

/-- `X^0_Z` is a subgraph of `G'_l` (a node graph of the two-level recursion on `G'_l`). -/
theorem X0_le_graph' (a : Addr) : X0 H c a ≤ graph' H c := STree.graphAtD_le _ _ _

theorem X0_le (a : Addr) : X0 H c a ≤ H := le_trans (X0_le_graph' H c a) (graph'_le H c)

@[simp] theorem X0_verts (a : Addr) : (X0 H c a).verts = Z0 H c a := rfl

/-- `Z^0 ⊆ V(G_l)`. -/
theorem Z0_subset_verts (a : Addr) : Z0 H c a ⊆ H.verts := (X0_le H c a).1

theorem X_le_X0 (a : Addr) : X H c a ≤ X0 H c a := (X0 H c a).deleteVerts_le _

@[simp] theorem X_verts (a : Addr) : (X H c a).verts = Z0 H c a \ guests H c a := by
  rw [X, FGraph.deleteVerts_verts]; rfl

/-- The part graph (`X_Z` or `X^0_Z`) has vertex set `V(Z)`. -/
@[simp] theorem partGraph_verts (a : Addr) : (partGraph H c a).verts = partVerts H c a := by
  classical
  unfold partGraph partVerts
  split_ifs
  · exact X_verts H c a
  · rfl

theorem partGraph_le_X0 (a : Addr) : partGraph H c a ≤ X0 H c a := by
  classical
  unfold partGraph
  split_ifs
  · exact X_le_X0 H c a
  · exact le_rfl

theorem partGraph_le_graph' (a : Addr) : partGraph H c a ≤ graph' H c :=
  le_trans (partGraph_le_X0 H c a) (X0_le_graph' H c a)

/-- (R5): the edges assigned to a part have both ends in the part: `E_l(Z) ⊆ V(Z)^{(2)}` (light
part: both ends in `Z^0 \ S_Z`; standalone pre-part: both ends in `Z^0`). Checked through the
three steps of `assign`. -/
theorem E_subset_sym2 (a : Addr) : E H c a ⊆ (partVerts H c a).sym2 := by
  classical
  intro e he
  have h := ((mem_E H c).1 he).2
  unfold assign at h
  rcases Option.or_eq_some_iff.1 h with h1 | ⟨-, h2⟩
  · have := List.find?_some h1
    simp only [decide_eq_true_eq] at this
    rw [← partGraph_verts]
    exact FGraph.edges_subset_sym2 this.2
  · rcases Option.or_eq_some_iff.1 h2 with h3 | ⟨-, h4⟩
    · have := List.find?_some h3
      simp only [decide_eq_true_eq] at this
      exact this.2.2
    · have := List.find?_some h4
      simp only [decide_eq_true_eq] at this
      unfold partVerts
      rw [if_neg this.2.1]
      exact this.2.2

/-- The ends of an edge of `E_l(Z)` lie in `V(Z)`. -/
theorem mem_partVerts_of_mem_E {a : Addr} {e : Sym2 V} (he : e ∈ E H c a) {v : V} (hv : v ∈ e) :
    v ∈ partVerts H c a :=
  Finset.mem_sym2_iff.1 (E_subset_sym2 H c a he) v hv

/-! #### Pieces and pre-parts (the two levels of (R3)) -/

theorem mem_bigPieceAddrs {q : Addr} :
    q ∈ bigPieceAddrs H c ↔ q ∈ pieceAddrs c ∧ POf (d H) ≤ (piece H c q).card :=
  Finset.mem_filter

theorem bigPieceAddrs_subset : bigPieceAddrs H c ⊆ pieceAddrs c := Finset.filter_subset _ _

theorem prePartAddrs_subset_leafAddrs : prePartAddrs H c ⊆ (twoLevel H c).leafAddrs :=
  Finset.filter_subset _ _

/-- The node graph of the two-level recursion at `q ++ b`, below the piece `q`, is the node
graph at `b` of the tree grafted at `q` (the `τ`-run if `q` is big, the one-leaf tree otherwise),
rooted at the piece graph. -/
theorem X0_append {q : Addr} (hq : q ∈ pieceAddrs c) (b : Addr) :
    X0 H c (q ++ b) = (if POf (d H) ≤ (piece H c q).card then c.tauRun q else .nil).graphAtD
      (piece H c q) b := by
  unfold X0 twoLevel
  rw [STree.graphAtD_graft_append hq]
  rfl

/-- Below a big piece `q`, the leaf graphs of the two-level recursion are those of the `τ`-run
of `q` (rooted at the piece graph). -/
theorem X0_append_of_mem_bigPieceAddrs {q : Addr} (hq : q ∈ bigPieceAddrs H c) (b : Addr) :
    X0 H c (q ++ b) = (c.tauRun q).graphAtD (piece H c q) b := by
  rw [mem_bigPieceAddrs] at hq
  rw [X0_append H c hq.1, if_pos hq.2]

/-- The piece above a leaf of the two-level recursion is an `s = 0` piece. -/
theorem pieceOf_mem_pieceAddrs {a : Addr} (ha : a ∈ (twoLevel H c).leafAddrs) :
    pieceOf c a ∈ pieceAddrs c :=
  STree.leafPrefix_mem_of_mem_leafAddrs_graft ha

/-- [s2:defHBtp] (R3) "The *round-`l` pre-parts* are the leaves of the `τ`-runs with at least
`P_l` vertices" (the first form; `prePartAddrs` is defined by the second, "equivalently" form):
a pre-part `a` lies below the big piece `q = pieceOf c a`, `a = q ++ b` for a leaf `b` of the
`τ`-run of `q`, and `X^0_Z` is the leaf graph of that `τ`-run at `b`. -/
theorem exists_tauRun_leaf_of_mem_prePartAddrs {a : Addr} (ha : a ∈ prePartAddrs H c) :
    pieceOf c a ∈ bigPieceAddrs H c ∧ ∃ b ∈ (c.tauRun (pieceOf c a)).leafAddrs,
      a = pieceOf c a ++ b ∧
        X0 H c a = (c.tauRun (pieceOf c a)).graphAtD (piece H c (pieceOf c a)) b := by
  have hP := (Finset.mem_filter.1 ha).2
  obtain ⟨q, hq, b, hb, rfl⟩ := STree.mem_leafAddrs_graft.1 (Finset.mem_filter.1 ha).1
  have hpq : pieceOf c (q ++ b) = q := STree.leafPrefix_append hq b
  rw [hpq]
  by_cases hbig : POf (d H) ≤ (piece H c q).card
  · have hqb : q ∈ bigPieceAddrs H c := (mem_bigPieceAddrs H c).2 ⟨hq, hbig⟩
    rw [if_pos hbig] at hb
    exact ⟨hqb, b, hb, rfl, X0_append_of_mem_bigPieceAddrs H c hqb b⟩
  · exfalso
    rw [if_neg hbig] at hb
    simp only [STree.leafAddrs_nil, Finset.mem_singleton] at hb
    subst hb
    rw [X0_append H c hq, if_neg hbig, STree.graphAtD_nil] at hP
    exact hbig hP

/-- Conversely, a leaf of the `τ`-run of a big piece with at least `P_l` vertices is a
pre-part. -/
theorem append_mem_prePartAddrs {q b : Addr} (hq : q ∈ bigPieceAddrs H c)
    (hb : b ∈ (c.tauRun q).leafAddrs)
    (hP : POf (d H) ≤ ((c.tauRun q).graphAtD (piece H c q) b).card) :
    q ++ b ∈ prePartAddrs H c := by
  have hq' := (mem_bigPieceAddrs H c).1 hq
  refine Finset.mem_filter.2 ⟨STree.mem_leafAddrs_graft.2 ⟨q, hq'.1, b, ?_, rfl⟩, ?_⟩
  · simp only [if_pos hq'.2]; exact hb
  · rw [X0_append_of_mem_bigPieceAddrs H c hq]; exact hP

theorem pieceOf_mem_bigPieceAddrs {a : Addr} (ha : a ∈ prePartAddrs H c) :
    pieceOf c a ∈ bigPieceAddrs H c :=
  (exists_tauRun_leaf_of_mem_prePartAddrs H c ha).1

/-! #### The two-level recursion: `WF`, deleted edges, `Dup*` (fix round 2) -/

/-- On a valid round, the two-level recursion is a split recursion on `G'_l`. -/
theorem wf_twoLevel (h : Valid H c) : (twoLevel H c).WF (graph' H c) := by
  refine STree.wf_graft h.2.1.1 fun a ha => ?_
  by_cases hP : POf (d H) ≤ (piece H c a).card
  · simp only [if_pos hP]
    exact (h.2.2.2.1 a ha hP).1
  · simp only [if_neg hP]
    exact STree.wf_nil _

/-- The deleted edges of the two-level recursion are those of the `τ`-runs of the big pieces
(the first level is an `s = 0` recursion and deletes nothing). -/
theorem deleted_twoLevel {ε : ℝ} (h0 : c.tree0.IsS0Rec ε (graph' H c)) :
    (twoLevel H c).deleted (graph' H c) =
      (bigPieceAddrs H c).biUnion (fun q => (c.tauRun q).deleted (piece H c q)) := by
  rw [twoLevel, STree.deleted_graft, STree.deleted_eq_empty_of_isS0Rec h0, Finset.empty_union]
  ext e
  simp only [Finset.mem_biUnion, bigPieceAddrs, Finset.mem_filter, pieceAddrs]
  constructor
  · rintro ⟨q, hq, he⟩
    by_cases hP : POf (d H) ≤ (piece H c q).card
    · rw [if_pos hP] at he
      exact ⟨q, ⟨hq, hP⟩, he⟩
    · rw [if_neg hP] at he
      simp at he
  · rintro ⟨q, ⟨hq, hP⟩, he⟩
    exact ⟨q, hq, by rw [if_pos hP]; exact he⟩

/-- Vertices duplicated by the `s = 0` recursion are in `Dup*_l`. -/
theorem tree0_dup_subset_DupStar : c.tree0.dup (graph' H c) ⊆ DupStar H c :=
  STree.dup_subset_dup_graft _ _ _

/-- Vertices duplicated by the `τ`-run of a big piece are in `Dup*_l` (s2:propOrigin,
`Dup_{𝒫} ⊆ Dup*_l`). -/
theorem tauRun_dup_subset_DupStar {q : Addr} (hq : q ∈ bigPieceAddrs H c) :
    (c.tauRun q).dup (piece H c q) ⊆ DupStar H c := by
  have hq' := (mem_bigPieceAddrs H c).1 hq
  have h := STree.dup_subset_dup_graft_of_mem_leafAddrs hq'.1
    (fun a => if POf (d H) ≤ (piece H c a).card then c.tauRun a else .nil) (graph' H c)
  rw [if_pos hq'.2] at h
  exact h

/-- A vertex of `G_l` outside `Dup*_l` lies in exactly one `s = 0` piece. -/
theorem existsUnique_piece_of_notMem_DupStar {u : V} (hu : u ∈ H.verts)
    (hD : u ∉ DupStar H c) : ∃! q, q ∈ pieceAddrs c ∧ u ∈ (piece H c q).verts := by
  obtain ⟨q, hq, huq⟩ := c.tree0.exists_mem_leafAddrs_mem_verts (H := graph' H c) hu
  refine ⟨q, ⟨hq, huq⟩, ?_⟩
  rintro q' ⟨hq', huq'⟩
  by_contra hne
  exact hD (tree0_dup_subset_DupStar H c
    (STree.mem_dup_iff_exists.2 ⟨q', hq', q, hq, hne, huq', huq⟩))

/-- (GC) with the neighbour count written as `e_{X^0_Z}({x}, Z^0 \ S_Z)` (s2:lemGC sketches). -/
theorem isGC_iff_eBetween (a : Addr) :
    isGC H c a ↔ ∀ x ∈ guests H c a,
      (X0 H c a).eBetween {x} (Z0 H c a \ guests H c a) < thetaGC (d H) (Z0 H c a).card := by
  simp only [isGC, FGraph.card_nbrs_inter_eq_eBetween]

end Round

namespace Run

variable (run : Run V) (G : FGraph V)

@[simp] theorem graph_zero : run.graph G 0 = G := rfl

@[simp] theorem graph_one : run.graph G 1 = G := by
  simp [graph, IsRound]

theorem graph_succ_of_isRound {l : ℕ} (hl : run.IsRound l) :
    run.graph G (l + 1) = Round.next (run.graph G l) (run.choice l) := by
  simp [graph, hl]

theorem graph_succ_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) :
    run.graph G (l + 1) = run.graph G l := by
  simp [graph, hl]

/-- [s2:defHBtp] "All graphs `G_l`, `G'_l` below have vertex set `V(G)`". -/
@[simp] theorem graph_verts (l : ℕ) : (run.graph G l).verts = G.verts := by
  induction l with
  | zero => rfl
  | succ l ih =>
    by_cases hl : run.IsRound l
    · rw [graph_succ_of_isRound run G hl, Round.next_verts, ih]
    · rw [graph_succ_of_not_isRound run G hl, ih]

@[simp] theorem card_graph (l : ℕ) : (run.graph G l).card = G.card := by
  simp [FGraph.card]

@[simp] theorem graph'_verts (l : ℕ) : (run.graph' G l).verts = G.verts := by
  simp [graph']

/-- [s2:defHBtp] (R0) "`d_l := 2|E(G_l)|/n`" with `n = |V(G)|`. -/
theorem d_eq (l : ℕ) : run.d G l = 2 * ((run.graph G l).edges.card : ℝ) / G.card := by
  simp [d, Round.d]

theorem graph_succ_le (l : ℕ) : run.graph G (l + 1) ≤ run.graph G l := by
  by_cases hl : run.IsRound l
  · rw [graph_succ_of_isRound run G hl]; exact Round.next_le _ _
  · rw [graph_succ_of_not_isRound run G hl]

/-- Edges only disappear: `E(G_l) ⊆ E(G_j)` for `j ≤ l`. -/
theorem graph_le_of_le {j l : ℕ} (hjl : j ≤ l) : run.graph G l ≤ run.graph G j := by
  induction hjl with
  | refl => exact le_rfl
  | step _ ih => exact le_trans (graph_succ_le run G _) ih

theorem graph_edges_subset_of_le {j l : ℕ} (hjl : j ≤ l) :
    (run.graph G l).edges ⊆ (run.graph G j).edges := (graph_le_of_le run G hjl).2

/-- Stationarity: `G_l = G_{R+1}` for `l ≥ R + 1`. -/
theorem graph_of_R_lt {l : ℕ} (hl : run.R + 1 ≤ l) : run.graph G l = run.graph G (run.R + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, graph_succ_of_not_isRound run G (fun h' => by
      simp only [IsRound] at h'; omega), ih (Nat.le_add_right _ _)]

variable {run G}

theorem isRound_of_mem_prePartAddrs {l : ℕ} {a : Addr} (ha : a ∈ run.prePartAddrs G l) :
    run.IsRound l := by
  unfold prePartAddrs at ha
  split_ifs at ha with h
  · exact h
  · simp at ha

variable (run G)

theorem prePartAddrs_of_isRound {l : ℕ} (hl : run.IsRound l) :
    run.prePartAddrs G l = Round.prePartAddrs (run.graph G l) (run.choice l) := if_pos hl

@[simp] theorem prePartAddrs_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) :
    run.prePartAddrs G l = ∅ := if_neg hl

omit [DecidableEq V] in
@[simp] theorem pieceAddrs_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) :
    run.pieceAddrs l = ∅ := if_neg hl

@[simp] theorem D_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) : run.D G l = ∅ := if_neg hl

@[simp] theorem DupStar_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) : run.DupStar G l = ∅ :=
  if_neg hl

@[simp] theorem mu_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) (w : V) : run.mu G l w = 0 :=
  if_neg hl

@[simp] theorem E_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) (a : Addr) : run.E G l a = ∅ :=
  if_neg hl

@[simp] theorem assign_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) (e : Sym2 V) :
    run.assign G l e = none := if_neg hl

omit [DecidableEq V] in
@[simp] theorem cycles_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) : run.cycles l = [] :=
  if_neg hl

@[simp] theorem Std_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) : run.Std G l = ∅ := by
  simp [Std, hl]

/-- [s2:defAncestors] "so `D_r = {w : μ_r(w) ≥ 2}`". -/
theorem mem_D_iff {l : ℕ} {v : V} : v ∈ run.D G l ↔ 2 ≤ run.mu G l v := by
  by_cases hl : run.IsRound l
  · simp only [D, mu, hl, if_true, Round.mem_D]
  · simp [hl]

theorem mem_Std_iff {l : ℕ} {a : Addr} :
    a ∈ run.Std G l ↔ a ∈ run.prePartAddrs G l ∧ ¬ run.isLight G l a := by
  classical
  simp only [Std, Finset.mem_filter]

/-! ### Parts and ancestors -/

theorem mem_parts {Y : PartId} : Y ∈ run.parts G ↔ Y.2 ∈ run.prePartAddrs G Y.1 := by
  unfold parts
  constructor
  · intro h
    obtain ⟨l, -, hY⟩ := Finset.mem_biUnion.1 h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hY
    exact ha
  · intro h
    have hr := isRound_of_mem_prePartAddrs h
    exact Finset.mem_biUnion.2 ⟨Y.1, Finset.mem_Icc.2 hr, Finset.mem_image.2 ⟨Y.2, h, rfl⟩⟩

theorem mem_ancestors {Y : PartId} : Y ∈ run.ancestors G ↔ Y.2 ∈ run.prePartAddrs G Y.1 :=
  mem_parts run G

theorem isRound_of_mem_parts {Y : PartId} (hY : Y ∈ run.parts G) : run.IsRound Y.1 :=
  isRound_of_mem_prePartAddrs ((mem_parts run G).1 hY)

theorem mem_lightParts {Y : PartId} :
    Y ∈ run.lightParts G ↔ Y.2 ∈ run.prePartAddrs G Y.1 ∧ run.isLight G Y.1 Y.2 := by
  classical
  simp only [lightParts, Finset.mem_filter, mem_parts]

theorem mem_stdParts {Y : PartId} : Y ∈ run.stdParts G ↔ Y.2 ∈ run.Std G Y.1 := by
  classical
  simp only [stdParts, Finset.mem_filter, mem_parts, mem_Std_iff]

theorem mem_anc {l : ℕ} {x : V} {Y : PartId} :
    Y ∈ run.anc G l x ↔ Y ∈ run.ancestors G ∧ Y.1 + 2 ≤ l ∧ x ∈ run.ancVerts G Y := by
  unfold anc; rw [Finset.mem_filter]

/-- [s2:defAncestors] "`anc_l(x) := ∅` for `l ≤ 2`" (rounds start at `1`). -/
theorem anc_eq_empty_of_le_two {l : ℕ} (hl : l ≤ 2) (x : V) : run.anc G l x = ∅ := by
  ext Y
  simp only [mem_anc, Finset.notMem_empty, iff_false, not_and]
  intro hY h2
  have := (isRound_of_mem_parts run G hY).1
  omega

/-- [s2:defAncestors] "(so all ports are fresh for `l ≤ 2`)". -/
theorem fresh_eq_ports_of_le_two {l : ℕ} (hl : l ≤ 2) (a : Addr) :
    run.fresh G l a = run.ports G l a := by
  unfold fresh
  simp [anc_eq_empty_of_le_two run G hl]

theorem nuAnc_eq_zero_of_le_two {l : ℕ} (hl : l ≤ 2) : run.nuAnc G l = 0 := by
  unfold nuAnc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro Y hY h2
  have := (isRound_of_mem_parts run G hY).1
  omega

theorem partVerts_subset_Z0 (l : ℕ) (a : Addr) : run.partVerts G l a ⊆ run.Z0 G l a :=
  Round.partVerts_subset _ _ a

/-- [s2:propOV] (F11) "`mult_r(w) ≤ μ_r(w)` for every vertex `w`" (definitional part: each
ancestor sits inside its pre-part). -/
theorem mult_le_mu (r : ℕ) (w : V) : run.mult G r w ≤ run.mu G r w := by
  by_cases hr : run.IsRound r
  · have hmu : run.mu G r w = ((run.prePartAddrs G r).filter (fun a => w ∈ run.Z0 G r a)).card := by
      simp only [mu, if_pos hr, Round.mu, prePartAddrs_of_isRound run G hr, Z0]
    rw [hmu, mult]
    refine Finset.card_le_card (fun a ha => ?_)
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, partVerts_subset_Z0 run G r a ha.2⟩
  · simp [mult, hr]

/-! ### Leaf graphs, part graphs, `E_l(Z)`, pieces (run level) -/

theorem X0_le_graph' (l : ℕ) (a : Addr) : run.X0 G l a ≤ run.graph' G l :=
  Round.X0_le_graph' _ _ a

theorem X0_le_graph (l : ℕ) (a : Addr) : run.X0 G l a ≤ run.graph G l := Round.X0_le _ _ a

/-- `Z^0 ⊆ V(G)`. -/
theorem Z0_subset_verts (l : ℕ) (a : Addr) : run.Z0 G l a ⊆ G.verts := by
  have := Round.Z0_subset_verts (run.graph G l) (run.choice l) a
  rwa [graph_verts] at this

@[simp] theorem X0_verts (l : ℕ) (a : Addr) : (run.X0 G l a).verts = run.Z0 G l a := rfl

@[simp] theorem partGraph_verts (l : ℕ) (a : Addr) :
    (run.partGraph G l a).verts = run.partVerts G l a := Round.partGraph_verts _ _ a

theorem partGraph_le_X0 (l : ℕ) (a : Addr) : run.partGraph G l a ≤ run.X0 G l a :=
  Round.partGraph_le_X0 _ _ a

theorem partGraph_le_graph' (l : ℕ) (a : Addr) : run.partGraph G l a ≤ run.graph' G l :=
  Round.partGraph_le_graph' _ _ a

/-- [s2:defAncestors] `H_Y` is a graph on `V(Y)`. -/
@[simp] theorem ancGraph_verts (Y : PartId) : (run.ancGraph G Y).verts = run.ancVerts G Y :=
  partGraph_verts run G Y.1 Y.2

theorem E_subset_graph'_edges (l : ℕ) (a : Addr) : run.E G l a ⊆ (run.graph' G l).edges := by
  by_cases hl : run.IsRound l
  · simp only [E, if_pos hl]; exact Round.E_subset _ _ a
  · simp [hl]

/-- (R5): `E_l(Z) ⊆ V(Z)^{(2)}`: the edges assigned to a part have both ends in the part. -/
theorem E_subset_sym2 (l : ℕ) (a : Addr) : run.E G l a ⊆ (run.partVerts G l a).sym2 := by
  by_cases hl : run.IsRound l
  · simp only [E, if_pos hl]; exact Round.E_subset_sym2 _ _ a
  · simp [hl]

theorem mem_partVerts_of_mem_E {l : ℕ} {a : Addr} {e : Sym2 V} (he : e ∈ run.E G l a) {v : V}
    (hv : v ∈ e) : v ∈ run.partVerts G l a :=
  Finset.mem_sym2_iff.1 (E_subset_sym2 run G l a he) v hv

/-- [s2:defHBtp] (GC) the address form of `θ^GC_l(Z^0)`. -/
theorem thetaGC_eq (l : ℕ) (a : Addr) :
    run.thetaGC G l a = EG.HB.thetaGC (run.d G l) (run.Z0 G l a).card := rfl

theorem mem_bigPieceAddrs {l : ℕ} {q : Addr} :
    q ∈ run.bigPieceAddrs G l ↔ q ∈ run.pieceAddrs l ∧ run.P G l ≤ (run.piece G l q).card :=
  Finset.mem_filter

theorem bigPieceAddrs_subset (l : ℕ) : run.bigPieceAddrs G l ⊆ run.pieceAddrs l :=
  Finset.filter_subset _ _

theorem bigPieceAddrs_of_isRound {l : ℕ} (hl : run.IsRound l) :
    run.bigPieceAddrs G l = Round.bigPieceAddrs (run.graph G l) (run.choice l) := by
  simp only [bigPieceAddrs, pieceAddrs, if_pos hl]
  rfl

@[simp] theorem bigPieceAddrs_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) :
    run.bigPieceAddrs G l = ∅ := by
  simp [bigPieceAddrs, hl]

omit [DecidableEq V] in
theorem pieceAddrs_of_isRound {l : ℕ} (hl : run.IsRound l) :
    run.pieceAddrs l = Round.pieceAddrs (run.choice l) := if_pos hl

/-- The piece above a pre-part is an `s = 0` piece of its round. -/
theorem pieceOf_mem_pieceAddrs {l : ℕ} {a : Addr} (ha : a ∈ run.prePartAddrs G l) :
    run.pieceOf l a ∈ run.pieceAddrs l := by
  have hl := isRound_of_mem_prePartAddrs ha
  rw [prePartAddrs_of_isRound run G hl] at ha
  rw [pieceAddrs_of_isRound run hl]
  exact Round.pieceOf_mem_pieceAddrs _ _ (Round.prePartAddrs_subset_leafAddrs _ _ ha)

/-- The piece above a pre-part is a big piece (`|𝒫| ≥ P_l`). -/
theorem pieceOf_mem_bigPieceAddrs {l : ℕ} {a : Addr} (ha : a ∈ run.prePartAddrs G l) :
    run.pieceOf l a ∈ run.bigPieceAddrs G l := by
  have hl := isRound_of_mem_prePartAddrs ha
  rw [prePartAddrs_of_isRound run G hl] at ha
  rw [bigPieceAddrs_of_isRound run G hl]
  exact Round.pieceOf_mem_bigPieceAddrs _ _ ha

/-- [s2:defHBtp] (R3) "The *round-`l` pre-parts* are the leaves of the `τ`-runs with at least
`P_l` vertices": a pre-part `a` of round `l` is `q ++ b` for its (big) piece `q = pieceOf l a`
and a leaf `b` of the `τ`-run of `q`, and `X^0_Z` is the leaf graph of that `τ`-run at `b`
(blueprint HB-DATAMODEL; D-HB-9). -/
theorem exists_tauRun_leaf_of_mem_prePartAddrs {l : ℕ} {a : Addr}
    (ha : a ∈ run.prePartAddrs G l) :
    ∃ b ∈ (run.tauRun l (run.pieceOf l a)).leafAddrs, a = run.pieceOf l a ++ b ∧
      run.X0 G l a = (run.tauRun l (run.pieceOf l a)).graphAtD
        (run.piece G l (run.pieceOf l a)) b := by
  have hl := isRound_of_mem_prePartAddrs ha
  rw [prePartAddrs_of_isRound run G hl] at ha
  exact (Round.exists_tauRun_leaf_of_mem_prePartAddrs _ _ ha).2

/-- Conversely, a leaf of the `τ`-run of a big piece with at least `P_l` vertices is a
pre-part. -/
theorem append_mem_prePartAddrs {l : ℕ} {q b : Addr} (hq : q ∈ run.bigPieceAddrs G l)
    (hb : b ∈ (run.tauRun l q).leafAddrs)
    (hP : run.P G l ≤ ((run.tauRun l q).graphAtD (run.piece G l q) b).card) :
    q ++ b ∈ run.prePartAddrs G l := by
  have hl : run.IsRound l := by
    by_contra hl; simp [hl] at hq
  rw [bigPieceAddrs_of_isRound run G hl] at hq
  rw [prePartAddrs_of_isRound run G hl]
  exact Round.append_mem_prePartAddrs _ _ hq hb hP

/-- Below a big piece `q`, the leaf graphs of the two-level recursion are those of the `τ`-run
of `q`. -/
theorem X0_append_of_mem_bigPieceAddrs {l : ℕ} {q : Addr} (hq : q ∈ run.bigPieceAddrs G l)
    (b : Addr) : run.X0 G l (q ++ b) = (run.tauRun l q).graphAtD (run.piece G l q) b := by
  have hl : run.IsRound l := by
    by_contra hl; simp [hl] at hq
  rw [bigPieceAddrs_of_isRound run G hl] at hq
  exact Round.X0_append_of_mem_bigPieceAddrs _ _ hq b

/-- On a valid run, the tree grafted at a big piece is a `τ`-run of that piece with parameters
`(ε, s_l, τ_l)` ((R3), second level). -/
theorem Valid.isTauRun {Dstar : ℝ} (h : run.Valid G Dstar) {l : ℕ} {q : Addr}
    (hq : q ∈ run.bigPieceAddrs G l) :
    (run.tauRun l q).IsTauRun epsC (run.s G l) (run.tau G l) (run.piece G l q) := by
  have hl : run.IsRound l := by
    by_contra hl; simp [hl] at hq
  rw [mem_bigPieceAddrs, pieceAddrs_of_isRound run hl] at hq
  exact (h.1 l (Finset.mem_Icc.2 hl)).2.2.2.2.1 q hq.1 hq.2

/-! ### `ε_Y` -/

/-- [s2:defAncestors] `ε_Y = 2^{-6} = ε/2` for a light part. -/
theorem ancEps_of_isLight {Y : PartId} (hY : run.isLight G Y.1 Y.2) :
    run.ancEps G Y = epsC / 2 := by
  classical
  rw [ancEps, if_pos hY, epsC]
  norm_num

/-- [s2:defAncestors] `ε_Y = 2^{-5} = ε` for a standalone pre-part. -/
theorem ancEps_of_not_isLight {Y : PartId} (hY : ¬ run.isLight G Y.1 Y.2) :
    run.ancEps G Y = epsC := by
  classical
  rw [ancEps, if_neg hY, epsC]

/-! ### Validity -/

theorem Valid.dstar_le {Dstar : ℝ} (h : run.Valid G Dstar) {l : ℕ} (hl : run.IsRound l) :
    Dstar ≤ run.d G l := (h.1 l (Finset.mem_Icc.2 hl)).1

theorem Valid.round {Dstar : ℝ} (h : run.Valid G Dstar) {l : ℕ} (hl : run.IsRound l) :
    Round.Valid (run.graph G l) (run.choice l) := (h.1 l (Finset.mem_Icc.2 hl)).2

theorem Valid.stop {Dstar : ℝ} (h : run.Valid G Dstar) : run.d G (run.R + 1) < Dstar := h.2

/-- The run without rounds is valid iff `d_1 < D_*` (then `R = 0` and `E_0 = E(G)`). -/
theorem valid_nil_iff (Dstar : ℝ) :
    (⟨[]⟩ : Run V).Valid G Dstar ↔ Round.d G < Dstar := by
  simp [Valid, R, d]

/-! ### `E(Cyc_l)`, the two-level recursion, `Dup*`, (GC) (fix round 2) -/

theorem cycEdges_of_isRound {l : ℕ} (hl : run.IsRound l) :
    run.cycEdges l = Round.cycEdges (run.choice l) := by
  simp only [cycEdges, cycles, if_pos hl, Round.cycEdges]

@[simp] theorem cycEdges_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) : run.cycEdges l = ∅ := by
  simp [cycEdges, hl]

/-- (R1) `G'_l = G_l - E(Cyc_l)` at a round `l`. -/
theorem graph'_eq_deleteEdges {l : ℕ} (hl : run.IsRound l) :
    run.graph' G l = (run.graph G l).deleteEdges (run.cycEdges l) := by
  rw [cycEdges_of_isRound run hl]
  rfl

theorem cycEdges_subset_graph_edges {Dstar : ℝ} (h : run.Valid G Dstar) (l : ℕ) :
    run.cycEdges l ⊆ (run.graph G l).edges := by
  by_cases hl : run.IsRound l
  · rw [cycEdges_of_isRound run hl]
    intro e he
    simp only [Round.cycEdges, List.mem_toFinset, List.mem_flatMap] at he
    obtain ⟨cyc, hcyc, he⟩ := he
    exact ((Valid.round run G h hl).1.1 cyc hcyc).2.1 e he
  · simp [hl]

/-- On a valid run, the two-level recursion of a round is a split recursion on `G'_l`. -/
theorem Valid.wf_twoLevel {Dstar : ℝ} (h : run.Valid G Dstar) {l : ℕ} (hl : run.IsRound l) :
    (run.twoLevel G l).WF (run.graph' G l) :=
  Round.wf_twoLevel _ _ (Valid.round run G h hl)

/-- On a valid run, the deleted edges of the two-level recursion of round `l` are those of the
`τ`-runs of the big pieces. -/
theorem Valid.deleted_twoLevel {Dstar : ℝ} (h : run.Valid G Dstar) {l : ℕ} (hl : run.IsRound l) :
    (run.twoLevel G l).deleted (run.graph' G l) =
      (run.bigPieceAddrs G l).biUnion (fun q => (run.tauRun l q).deleted (run.piece G l q)) := by
  rw [bigPieceAddrs_of_isRound run G hl]
  exact Round.deleted_twoLevel _ _ (Valid.round run G h hl).2.1

/-- Vertices duplicated by the `τ`-run of a big piece are in `Dup*_l`. -/
theorem tauRun_dup_subset_DupStar {l : ℕ} {q : Addr} (hq : q ∈ run.bigPieceAddrs G l) :
    (run.tauRun l q).dup (run.piece G l q) ⊆ run.DupStar G l := by
  have hl : run.IsRound l := by
    by_contra hl; simp [hl] at hq
  rw [bigPieceAddrs_of_isRound run G hl] at hq
  rw [DupStar, if_pos hl]
  exact Round.tauRun_dup_subset_DupStar _ _ hq

/-- Vertices duplicated by the `s = 0` recursion of round `l` are in `Dup*_l`. -/
theorem tree0_dup_subset_DupStar {l : ℕ} (hl : run.IsRound l) :
    (run.tree0 l).dup (run.graph' G l) ⊆ run.DupStar G l := by
  rw [DupStar, if_pos hl]
  exact Round.tree0_dup_subset_DupStar _ _

/-- At a round `l`, a vertex outside `Dup*_l` lies in exactly one `s = 0` piece. -/
theorem existsUnique_piece_of_notMem_DupStar {l : ℕ} (hl : run.IsRound l) {u : V}
    (hu : u ∈ G.verts) (hD : u ∉ run.DupStar G l) :
    ∃! q, q ∈ run.pieceAddrs l ∧ u ∈ (run.piece G l q).verts := by
  rw [DupStar, if_pos hl] at hD
  rw [pieceAddrs_of_isRound run hl]
  exact Round.existsUnique_piece_of_notMem_DupStar _ _ (by simpa using hu) hD

/-- (GC) with the neighbour count written as `e_{X^0_Z}({x}, Z^0 \ S_Z)`. -/
theorem isGC_iff_eBetween (l : ℕ) (a : Addr) :
    run.isGC G l a ↔ ∀ x ∈ run.guests G l a,
      (run.X0 G l a).eBetween {x} (run.Z0 G l a \ run.guests G l a) < run.thetaGC G l a :=
  Round.isGC_iff_eBetween _ _ a

end Run

end EG.HB
