import EG.Lib.HB.Run

/-! Unit tests for `EG.Defs.HB.Witness`, `EG.Defs.HB.SplitTree`, `EG.Defs.HB.Round` and
`EG.Defs.HB.Run` ([s2:defWitness], [s2:defTauRules], [s2:lemSEP], [s2:lem14tau],
[s2:defHBtp], [s2:defAncestors]):
* round parameters at `d = 2` (`M = 2^{40}`, `Λ = 40`, `s = 40^{100}`, `P = 1`, `T = 2`);
* the run without rounds is valid iff `d_1 < D_*`;
* **non-vacuity of `Run.Valid` with one round**: a hand-built valid run on the triangle `K_3`
  with `D_* = 1` (the long cycle `012` is removed in (R1), the `s = 0` recursion splits the
  empty graph on three vertices into three one-vertex pieces, which are pre-parts, `R = 1`);
* negative tests: the same run without the long cycle is not valid ((R1) maximality); a tree that
  stops at a non-expander violates the stopping rule; a `τ`-run cannot be a leaf at a
  non-expander;
* pieces of the valid run (`bigPieceAddrs`, `pieceOf`, address-form `thetaGC`);
* a genuine `τ`-run (two disjoint edges, `s = 1`, `τ = 2`): the split clause of `IsTauRun`, the
  `τ`-rule labels and the deleted edges (fix round 1, review issue 4);
* (R4)/(R5) on overlapping pre-parts of `K_3`: `D = {1}`, a guest, a light part whose graph
  loses the guest edge, `assign 01 = some [false]`, `assign 12 = none`, `E ⊆ V(Z)^{(2)}`;
* `Run.cycEdges` on the valid run (guarded outside `[1,R]`, fix round 2);
* (R4)/(R5) on a 5-vertex example with two home orders (`StandaloneTest`, fix round 2): a
  standalone pre-part (`Std ≠ ∅`), `Dup*`, a `τ`-run deletion inside a round, steps (2) and (3)
  of (R5), a passed-down guest–core edge and the next graph. -/

namespace EGTest.HB

open EG EG.HB

/-! ## Round parameters at `d = 2` -/

theorem logb_two_two : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)

example : tHBOf 2 = 1 := by simp [tHBOf]

theorem TOf_two : TOf 2 = 2 := by simp [TOf, tHBOf]

theorem MOf_two : MOf 2 = 2 ^ 40 := by
  unfold MOf
  rw [TOf_two, logb_two_two]
  norm_num

theorem LamOf_two : LamOf 2 = 40 := by
  unfold LamOf
  rw [MOf_two, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, logb_two_two]
  norm_num

example : sOf 2 = 40 ^ 100 := by
  unfold sOf
  rw [LamOf_two, show sigmaC = 100 from rfl]
  exact_mod_cast Nat.ceil_natCast (40 ^ 100)

theorem POf_two : POf 2 = 1 := by
  simp [POf, lamOf]

/-! ## The run without rounds -/

/-- The graph on `Fin 2` without edges. -/
def E2 : FGraph (Fin 2) := FGraph.ofEdges Finset.univ ∅

example : (⟨[]⟩ : Run (Fin 2)).Valid E2 1 := by
  rw [Run.valid_nil_iff]
  simp [Round.d, E2, FGraph.ofEdges]

example : ¬ (⟨[]⟩ : Run (Fin 2)).Valid E2 0 := by
  rw [Run.valid_nil_iff]
  simp [Round.d, E2, FGraph.ofEdges]

/-! ## A valid run with one round on the triangle -/

/-- The triangle `K_3` on `Fin 3`. -/
def K3 : FGraph (Fin 3) := FGraph.ofEdges Finset.univ {s(0, 1), s(1, 2), s(0, 2)}

theorem K3_edges : K3.edges = {s(0, 1), s(1, 2), s(0, 2)} := by decide

theorem K3_card : K3.card = 3 := rfl

theorem d_K3 : Round.d K3 = 2 := by
  rw [Round.d, K3_edges, K3_card]
  norm_num [show ({s(0, 1), s(1, 2), s(0, 2)} : Finset (Sym2 (Fin 3))).card = 3 from by decide]

/-- The long cycle `0 1 2` of (R1). -/
def cyc : List (Fin 3) := [0, 1, 2]

/-- The `s = 0` recursion: split off `{0}`, then `{1}` (witnesses `U = {0}`, `U = {1}`, `N = ∅`). -/
def tree0 : STree (Fin 3) := .node ({0}, ∅) .nil (.node ({1}, ∅) .nil .nil)

/-- The choices of round 1. -/
def c1 : RoundChoice (Fin 3) :=
  ⟨[cyc], tree0, fun _ => .nil, [[false], [true, false], [true, true]]⟩

/-- The run. -/
def run1 : Run (Fin 3) := ⟨[c1]⟩

/-- `G'_1` has no edges. -/
theorem graph'_edges : (Round.graph' K3 c1).edges = ∅ := by decide

theorem graph'_verts : (Round.graph' K3 c1).verts = Finset.univ := rfl


/-! ### Generic helpers: graphs without edges -/

theorem nbrSet_eq_empty {W : Type*} [DecidableEq W] {H : FGraph W} (hE : H.edges = ∅)
    (U : Finset W) : H.nbrSet U = ∅ := by
  ext v
  simp only [FGraph.mem_nbrSet, Finset.notMem_empty, iff_false, not_and, not_exists]
  intro _ _ u _ h
  rw [FGraph.adj_iff, hE] at h
  simp at h

/-- In a graph without edges on at least two vertices, `({v}, ∅)` is a witness with parameter
`0` ([s2:defWitness]). -/
theorem isWitness_singleton {W : Type*} [DecidableEq W] {H : FGraph W} (hE : H.edges = ∅)
    (h2 : 2 ≤ H.card) {v : W} (hv : v ∈ H.verts) : IsWitness H epsC 0 {v} ∅ := by
  have h2' : (2 : ℝ) ≤ H.card := by exact_mod_cast h2
  have hlog : 0 < Real.logb 2 (H.card : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  refine ⟨Finset.singleton_subset_iff.2 hv, by simp, by simp, ?_, by simp, ?_⟩
  · simp only [Finset.card_singleton, Nat.cast_one]; linarith
  · rw [FGraph.deleteEdges_empty, nbrSet_eq_empty hE]
    simp only [Finset.card_empty, Nat.cast_zero, Finset.card_singleton, Nat.cast_one, mul_one]
    have : (0 : ℝ) < epsC := by unfold epsC; positivity
    positivity

theorem not_isExpander_of_noEdges {W : Type*} [DecidableEq W] {H : FGraph W}
    (hE : H.edges = ∅) (h2 : 2 ≤ H.card) : ¬ H.IsExpander epsC 0 := by
  obtain ⟨v, hv⟩ : H.verts.Nonempty := Finset.card_pos.1 (by rw [FGraph.card_def] at h2; omega)
  rw [not_isExpander_iff_exists_isWitness]
  exact ⟨{v}, ∅, isWitness_singleton hE h2 hv⟩

/-! ### The node graphs of the `s = 0` recursion -/

/-- `G'_1`: the empty graph on `Fin 3`. -/
abbrev E3 : FGraph (Fin 3) := Round.graph' K3 c1

theorem tree0_edges (a : Addr) : (tree0.graphAtD E3 a).edges = ∅ :=
  Finset.subset_empty.1 (graph'_edges ▸ STree.graphAtD_edges_subset tree0 E3 a)

theorem tree0_nodeAddrs :
    tree0.nodeAddrs = {[], [false], [true], [true, false], [true, true]} := by decide

theorem tree0_leafAddrs : tree0.leafAddrs = {[false], [true, false], [true, true]} := by
  decide

theorem tree0_internalAddrs : tree0.internalAddrs = {[], [true]} := by decide

theorem verts_root : (tree0.graphAtD E3 []).verts = Finset.univ := rfl

theorem verts_F : (tree0.graphAtD E3 [false]).verts = {0} := by decide

theorem verts_T : (tree0.graphAtD E3 [true]).verts = {1, 2} := by decide

theorem verts_TF : (tree0.graphAtD E3 [true, false]).verts = {1} := by decide

theorem verts_TT : (tree0.graphAtD E3 [true, true]).verts = {2} := by decide

theorem card_leaf {a : Addr} (ha : a ∈ tree0.leafAddrs) : (tree0.graphAtD E3 a).card = 1 := by
  rw [tree0_leafAddrs] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> simp only [FGraph.card, verts_F, verts_TF, verts_TT] <;> rfl

theorem card_internal {a : Addr} (ha : a ∈ tree0.internalAddrs) :
    2 ≤ (tree0.graphAtD E3 a).card := by
  rw [tree0_internalAddrs] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> simp only [FGraph.card, verts_root, verts_T] <;> decide


/-! ### The conditions of `Round.Valid` -/

theorem cycles_valid : Round.CyclesValid K3 c1 := by
  refine ⟨?_, by decide, ?_⟩
  · intro cy hcy
    simp only [c1, List.mem_singleton] at hcy
    subst hcy
    refine ⟨show cyc.Nodup ∧ 3 ≤ cyc.length by decide, by rw [K3_edges]; decide, ?_⟩
    rw [d_K3, TOf_two]
    norm_num [cyc]
  · intro cy hwf hE
    exfalso
    have hlen : 3 ≤ cy.length := hwf.2
    have hne : cycleEdges cy ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [cycleEdges, List.length_zipWith, List.length_rotate, min_self,
        List.length_nil] at this
      omega
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    have := hE e he
    rw [graph'_edges] at this
    simp at this

theorem wf_tree0 : tree0.WF E3 := by
  intro a ha
  rw [tree0_internalAddrs] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩ <;> decide
  · refine ⟨?_, ?_, ?_⟩ <;> decide

theorem isS0Rec_tree0 : tree0.IsS0Rec epsC E3 := by
  refine ⟨wf_tree0, ?_⟩
  intro a ha
  have h2 := card_internal ha
  rw [tree0_internalAddrs] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · refine ⟨{0}, ∅, isWitness_singleton (tree0_edges _) h2 (by rw [verts_root]; simp), ?_⟩
    rw [nbrSet_eq_empty (tree0_edges _)]
    rfl
  · refine ⟨{1}, ∅, isWitness_singleton (tree0_edges _) h2 (by rw [verts_T]; simp), ?_⟩
    rw [nbrSet_eq_empty (tree0_edges _)]
    rfl

theorem stopsAt_tree0 : tree0.StopsAt E3 (fun Q => Q.IsExpander epsC 0) := by
  intro a ha
  rw [STree.nodeAddrs_eq_union, Finset.mem_union] at ha
  rcases ha with hl | hi
  · simp only [hl, true_iff]
    exact FGraph.isExpander_of_card_le_one (card_leaf hl).le
  · have hnl : a ∉ tree0.leafAddrs := fun h =>
      Finset.disjoint_left.1 (STree.disjoint_leafAddrs_internalAddrs tree0) h hi
    simp only [hnl, false_iff]
    exact not_isExpander_of_noEdges (tree0_edges a) (card_internal hi)

theorem twoLevel_eq : Round.twoLevel K3 c1 = tree0 := by
  have h : (fun a => if POf (Round.d K3) ≤ (Round.piece K3 c1 a).card then c1.tauRun a
      else (STree.nil : STree (Fin 3))) = fun _ => STree.nil :=
    funext fun a => by split_ifs <;> rfl
  unfold Round.twoLevel
  rw [h]
  exact STree.graft_nil_fun tree0

theorem prePartAddrs_eq : Round.prePartAddrs K3 c1 = tree0.leafAddrs := by
  unfold Round.prePartAddrs
  rw [twoLevel_eq]
  apply Finset.filter_true_of_mem
  intro a ha
  rw [Round.X0, twoLevel_eq, card_leaf ha, d_K3, POf_two]

theorem round_valid : Round.Valid K3 c1 := by
  refine ⟨cycles_valid, isS0Rec_tree0, stopsAt_tree0, ?_, by decide, ?_⟩
  · intro a ha _
    show (STree.nil : STree (Fin 3)).IsTauRun _ _ _ _
    rw [STree.isTauRun_nil_iff]
    exact FGraph.isExpander_of_card_le_one (card_leaf ha).le
  · rw [prePartAddrs_eq, tree0_leafAddrs]
    decide

/-- **Non-vacuity of `Run.Valid`** ([s2:defHBtp]): a valid run with one round. -/
theorem run1_valid : run1.Valid K3 1 := by
  have hR : run1.R = 1 := rfl
  have hr1 : run1.IsRound 1 := ⟨le_rfl, le_rfl⟩
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [hR, Finset.Icc_self, Finset.mem_singleton] at hl
    subst hl
    refine ⟨?_, ?_⟩
    · rw [Run.d, Run.graph_one, d_K3]; norm_num
    · rw [Run.graph_one]; exact round_valid
  · rw [hR, Run.d, Run.graph_succ_of_isRound run1 K3 hr1, Run.graph_one]
    have hp : Round.passed K3 (run1.choice 1) = ∅ :=
      Finset.subset_empty.1 (graph'_edges ▸ Round.passed_subset K3 c1)
    simp [Round.d, hp]

/-! ### Objects of the valid run -/

example : run1.R = 1 := rfl

example : run1.prePartAddrs K3 1 = {[false], [true, false], [true, true]} := by
  rw [Run.prePartAddrs_of_isRound run1 K3 ⟨le_rfl, le_rfl⟩, Run.graph_one]
  exact prePartAddrs_eq.trans tree0_leafAddrs

example : run1.prePartAddrs K3 2 = ∅ :=
  Run.prePartAddrs_of_not_isRound run1 K3 (by simp [Run.IsRound, Run.R, run1])

/-- `anc_l(x) = ∅` for `l ≤ 2` (TRIAGE §2.1 test). -/
example (x : Fin 3) : run1.anc K3 2 x = ∅ := Run.anc_eq_empty_of_le_two run1 K3 le_rfl x

example : run1.E0 K3 = ∅ := by
  have hr1 : run1.IsRound 1 := ⟨le_rfl, le_rfl⟩
  rw [Run.E0, show run1.R + 1 = 1 + 1 from rfl, Run.graph_succ_of_isRound run1 K3 hr1,
    Run.graph_one, Round.next_edges]
  exact Finset.subset_empty.1 (graph'_edges ▸ Round.passed_subset K3 c1)

/-! ### (R4) on the valid run: every vertex lies in exactly one pre-part, so `D_1 = ∅`, there
are no guests and all three pre-parts are light -/

theorem Z0_eq (a : Addr) : Round.Z0 K3 c1 a = (tree0.graphAtD E3 a).verts := by
  rw [Round.Z0, Round.X0, twoLevel_eq]

theorem D_eq : Round.D K3 c1 = ∅ := by
  ext v
  rw [Round.mem_D]
  simp only [Round.mu, prePartAddrs_eq, tree0_leafAddrs, Z0_eq, Finset.notMem_empty, iff_false]
  revert v
  decide

theorem guests_eq (a : Addr) : Round.guests K3 c1 a = ∅ := by
  simp [Round.guests, D_eq]

theorem isLight_c1 (a : Addr) : Round.isLight K3 c1 a := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guests_eq]
  · intro u _
    simp only [guests_eq, Finset.inter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  · intro x hx
    simp [guests_eq] at hx

example : Round.Std K3 c1 = ∅ := by
  ext a
  simp [Round.mem_Std, isLight_c1]

example : run1.lightParts K3 = {(1, [false]), (1, [true, false]), (1, [true, true])} := by
  ext Y
  rw [Run.mem_lightParts]
  constructor
  · rintro ⟨h, -⟩
    have hr := (Run.isRound_of_mem_prePartAddrs h)
    have h1 : Y.1 = 1 := le_antisymm hr.2 hr.1
    rw [h1, Run.prePartAddrs_of_isRound run1 K3 ⟨le_rfl, le_rfl⟩, Run.graph_one] at h
    change Y.2 ∈ Round.prePartAddrs K3 c1 at h
    rw [prePartAddrs_eq, tree0_leafAddrs] at h
    obtain ⟨y1, y2⟩ := Y
    simp only at h1 h
    subst h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with rfl | rfl | rfl <;> simp
  · intro h
    have h1 : Y.1 = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl <;> rfl
    obtain ⟨y1, y2⟩ := Y
    simp only at h1
    subst h1
    refine ⟨?_, isLight_c1 y2⟩
    rw [Run.prePartAddrs_of_isRound run1 K3 ⟨le_rfl, le_rfl⟩, Run.graph_one]
    change y2 ∈ Round.prePartAddrs K3 c1
    rw [prePartAddrs_eq, tree0_leafAddrs]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, true_and] at h ⊢
    exact h

/-! ### Negative tests -/

/-- Without removing the long cycle `012`, (R1) maximality fails. -/
example : ¬ Round.CyclesValid K3 { c1 with cycles := [] } := by
  rintro ⟨-, -, h⟩
  have := h cyc (show cyc.Nodup ∧ 3 ≤ cyc.length by decide) (by
    intro e he
    simp only [Round.graph', Round.cycEdges, List.flatMap_nil, List.toFinset_nil,
      FGraph.deleteEdges_empty]
    rw [K3_edges]
    revert e he
    decide)
  rw [d_K3, TOf_two] at this
  norm_num [cyc] at this

/-- A tree that stops at the (non-expander) root violates the stopping rule of (R3). -/
example : ¬ (STree.nil : STree (Fin 3)).StopsAt E3 (fun Q => Q.IsExpander epsC 0) := by
  rw [STree.stopsAt_nil_iff]
  exact not_isExpander_of_noEdges graph'_edges (by decide)

/-- A `τ`-run cannot be a single leaf at a non-expander. -/
example (s : ℕ) (τ : ℝ) : ¬ (STree.nil : STree (Fin 3)).IsTauRun epsC s τ E3 := by
  rw [STree.isTauRun_nil_iff]
  intro h
  exact not_isExpander_of_noEdges graph'_edges (by decide)
    (h.mono le_rfl (by positivity))

/-! ### Pieces of the valid run: all three pieces are big (`P_1 = 1`), each pre-part is its own
piece, and the address-form wrappers -/

example : run1.bigPieceAddrs K3 1 = {[false], [true, false], [true, true]} := by
  rw [Run.bigPieceAddrs_of_isRound run1 K3 ⟨le_rfl, le_rfl⟩, Run.graph_one]
  show Round.bigPieceAddrs K3 c1 = _
  rw [← tree0_leafAddrs]
  apply Finset.filter_true_of_mem
  intro a ha
  rw [Round.piece, d_K3, POf_two]
  exact (card_leaf ha).ge

example : run1.pieceOf 1 [true, false] = [true, false] := rfl

example (a : Addr) (ha : a ∈ run1.prePartAddrs K3 1) : run1.pieceOf 1 a ∈ run1.bigPieceAddrs K3 1 :=
  Run.pieceOf_mem_bigPieceAddrs run1 K3 ha

example (a : Addr) : run1.thetaGC K3 1 a = thetaGC (run1.d K3 1) (run1.Z0 K3 1 a).card := rfl

/-! ## A genuine `τ`-run (the split clause of `IsTauRun`)

`H₂` = two disjoint edges `01`, `23` on `Fin 4`, `s = 1`, `τ = 2`. The tree splits the root with
label `({0,1}, ∅)`, then `[false]` with `({0}, ∅)` and `[true]` with `({2}, ∅)`, from the
witnesses `({0,1}, ∅)`, `({0}, {01})`, `({2}, {23})` (parameter `1`); the τ-rules are idle
(`H_out = H_in = ∅`), so the labels are `(U, N)`. Both deleted sets `E(U', V∖(U'∪N''))` are
nonempty at `[false]` and `[true]`: the τ-run deletes `01` and `23`. -/

namespace TauRunTest

/-- Two disjoint edges 01, 23. -/
def H2 : FGraph (Fin 4) := FGraph.ofEdges Finset.univ {s(0, 1), s(2, 3)}

def t : STree (Fin 4) :=
  .node ({0, 1}, ∅) (.node ({0}, ∅) .nil .nil) (.node ({2}, ∅) .nil .nil)

theorem t_internal : t.internalAddrs = {[], [false], [true]} := by decide

theorem t_leaves : t.leafAddrs = {[false, false], [false, true], [true, false], [true, true]} := by
  decide

/-- With all degrees in `F₀` and in `F'` at most `1 < τ = 2`, the τ-rules are idle. -/
theorem tau_idle {W : Type} [DecidableEq W] (K : FGraph W) (U N : Finset W)
    (h0 : ∀ v, degE (witF0 K U N) v ≤ 1)
    (h1 : ∀ v, degE (K.edgesBetween U (K.verts \ (U ∪ N))) v ≤ 1) :
    tauU1 K U N 2 = U ∧ tauN2 K U N 2 = N := by
  have hout : tauHout K U N 2 = ∅ := by
    unfold tauHout
    apply Finset.filter_false_of_mem
    intro v _ hv
    have : ((degE (witF0 K U N) v : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h0 v
    linarith
  have hU : tauU1 K U N 2 = U := by simp [tauU1, hout]
  have hN1 : tauN1 K U N 2 = N := by simp [tauN1, hout]
  have hF1 : tauF1 K U N 2 = K.edgesBetween U (K.verts \ (U ∪ N)) := by
    simp only [tauF1, hU, hN1]
  have hin : tauHin K U N 2 = ∅ := by
    unfold tauHin
    apply Finset.filter_false_of_mem
    intro v _ hv
    rw [hF1] at hv
    have : ((degE (K.edgesBetween U (K.verts \ (U ∪ N))) v : ℕ) : ℝ) ≤ 1 := by
      exact_mod_cast h1 v
    linarith
  refine ⟨hU, ?_⟩
  simp [tauN2, hN1, hin]

theorem wit_of {W : Type} [DecidableEq W] (K : FGraph W) (U : Finset W) (F : Finset (Sym2 W))
    (hU : U ⊆ K.verts) (hF : F ⊆ K.edges) (h1 : 1 ≤ U.card) (h23 : 3 * U.card ≤ 2 * K.card)
    (hFs : F.card ≤ U.card) (hN : (K.deleteEdges F).nbrSet U = ∅) (hK : 2 ≤ K.card) :
    IsWitness K epsC 1 U F := by
  refine ⟨hU, hF, h1, ?_, ?_, ?_⟩
  · have : (3 * U.card : ℝ) ≤ 2 * K.card := by exact_mod_cast h23
    linarith
  · have : (F.card : ℝ) ≤ U.card := by exact_mod_cast hFs
    linarith
  · rw [hN]
    have hK' : (2 : ℝ) ≤ K.card := by exact_mod_cast hK
    have hlog : 0 < Real.logb 2 (K.card : ℝ) := Real.logb_pos (by norm_num) (by linarith)
    have hU' : (0 : ℝ) < U.card := by exact_mod_cast h1
    have : (0 : ℝ) < epsC := by unfold epsC; positivity
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem wit_root : IsWitness (t.graphAtD H2 []) epsC 1 {0, 1} ∅ :=
  wit_of _ _ _ (by decide) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem wit_F : IsWitness (t.graphAtD H2 [false]) epsC 1 {0} {s(0, 1)} :=
  wit_of _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem wit_T : IsWitness (t.graphAtD H2 [true]) epsC 1 {2} {s(2, 3)} :=
  wit_of _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A non-trivial `τ`-run (`s = 1`, `τ = 2`): three splits (witness parameter `(1 : ℕ)` cast to
`ℝ`, bridged by `Nat.cast_one`). -/
theorem t_isTauRun : t.IsTauRun epsC 1 2 H2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [t_internal] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> decide
  · intro a ha
    rw [STree.nodeAddrs_eq_union, Finset.mem_union] at ha
    rcases ha with hl | hi
    · simp only [hl, true_iff]
      apply FGraph.isExpander_of_card_le_one
      rw [t_leaves] at hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> decide
    · have hnl : a ∉ t.leafAddrs := fun h =>
        Finset.disjoint_left.1 (STree.disjoint_leafAddrs_internalAddrs t) h hi
      simp only [hnl, false_iff]
      rw [not_isExpander_iff_exists_isWitness]
      rw [t_internal] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact ⟨_, _, by rw [Nat.cast_one]; exact wit_root⟩
      · exact ⟨_, _, by rw [Nat.cast_one]; exact wit_F⟩
      · exact ⟨_, _, by rw [Nat.cast_one]; exact wit_T⟩
  · intro a ha
    rw [t_internal] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · refine ⟨{0, 1}, ∅, by rw [Nat.cast_one]; exact wit_root, ?_⟩
      have hN : witN (t.graphAtD H2 []) {0, 1} ∅ = ∅ := by decide
      obtain ⟨h1, h2⟩ := tau_idle (t.graphAtD H2 []) {0, 1} ∅ (by decide) (by decide)
      rw [hN, h1, h2]; rfl
    · refine ⟨{0}, {s(0, 1)}, by rw [Nat.cast_one]; exact wit_F, ?_⟩
      have hN : witN (t.graphAtD H2 [false]) {0} {s(0, 1)} = ∅ := by decide
      obtain ⟨h1, h2⟩ := tau_idle (t.graphAtD H2 [false]) {0} ∅ (by decide) (by decide)
      rw [hN, h1, h2]; rfl
    · refine ⟨{2}, {s(2, 3)}, by rw [Nat.cast_one]; exact wit_T, ?_⟩
      have hN : witN (t.graphAtD H2 [true]) {2} {s(2, 3)} = ∅ := by decide
      obtain ⟨h1, h2⟩ := tau_idle (t.graphAtD H2 [true]) {2} ∅ (by decide) (by decide)
      rw [hN, h1, h2]; rfl

/-- The deleted edges are exactly `01` and `23`. -/
example : t.deleted H2 = {s(0, 1), s(2, 3)} := by decide

/-- The four leaves are pairwise disjoint: no duplicated vertex. -/
example : t.dup H2 = ∅ := by decide

end TauRunTest

/-! ## (R4)/(R5) on overlapping pre-parts: a guest, a light part losing it, a passed-down edge

`G = K₃` (`d = 2`, `P = 1`, `s = 40^{100}`); the choice splits the root with `({0}, {1})`, so the
two leaves `[false]` (vertices `{0,1}`) and `[true]` (vertices `{1,2}`) overlap in `1`. This is
not a valid round (the `s = 0` recursion would need a witness); only the functions of (R4) and
(R5) are exercised. Home order `[false], [true]`: `home(1) = [false]`, so `1` is a guest of
`[true]`, `D = {1}`. -/

namespace OverlapTest

def tr : STree (Fin 3) := .node ({0}, {1}) .nil .nil

def c : RoundChoice (Fin 3) := ⟨[], tr, fun _ => .nil, [[false], [true]]⟩

theorem sOf_two' : sOf 2 = 40 ^ 100 := by
  unfold sOf; rw [LamOf_two, show sigmaC = 100 from rfl]
  exact_mod_cast Nat.ceil_natCast (40 ^ 100)

theorem twoLevel_eq : Round.twoLevel K3 c = tr := by
  have h : (fun a => if POf (Round.d K3) ≤ (Round.piece K3 c a).card then c.tauRun a
      else (STree.nil : STree (Fin 3))) = fun _ => STree.nil :=
    funext fun a => by split_ifs <;> rfl
  unfold Round.twoLevel; rw [h]; exact STree.graft_nil_fun tr

theorem g'_eq : Round.graph' K3 c = K3 := by
  simp [Round.graph', Round.cycEdges, c]

theorem X0_eq (a : Addr) : Round.X0 K3 c a = tr.graphAtD K3 a := by
  rw [Round.X0, twoLevel_eq, g'_eq]

theorem pre_eq : Round.prePartAddrs K3 c = {[false], [true]} := by
  unfold Round.prePartAddrs
  rw [twoLevel_eq, d_K3, POf_two]
  simp only [X0_eq]
  decide

theorem Z0_F : Round.Z0 K3 c [false] = {0, 1} := by rw [Round.Z0, X0_eq]; decide

theorem Z0_T : Round.Z0 K3 c [true] = {1, 2} := by rw [Round.Z0, X0_eq]; decide

theorem D_eq : Round.D K3 c = {1} := by
  ext v
  rw [Round.mem_D]
  simp only [Round.mu, pre_eq]
  fin_cases v <;> simp [Finset.filter_insert, Finset.filter_singleton, Z0_F, Z0_T]

theorem home_eq (v : Fin 3) : Round.home K3 c v =
    if v = 2 then some [true] else some [false] := by
  unfold Round.home
  rw [pre_eq, show c.homeOrder = [[false], [true]] from rfl]
  fin_cases v <;> simp [Z0_F, Z0_T]

theorem guests_F : Round.guests K3 c [false] = ∅ := by
  unfold Round.guests; rw [D_eq, Z0_F]; simp [home_eq]

theorem guests_T : Round.guests K3 c [true] = {1} := by
  unfold Round.guests; rw [D_eq, Z0_T]; simp [home_eq]

theorem thetaGC_2 : thetaGC 2 2 = 2 := by simp [thetaGC, lamOf]

/-- `[true]` is light: (L1) `2·1 ≤ 2`; (L2) at most one guest neighbour `≤ s/2`; (GC) the guest
`1` has one neighbour (`2`) in `Z^0 \ S = {2}`, fewer than `θ^GC = ⌈2 · 1^{-1/2}⌉ = 2`. -/
theorem light_T : Round.isLight K3 c [true] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guests_T, Z0_T]
  · intro u _
    have : ((((Round.graph' K3 c).induce (Round.Z0 K3 c [true])).nbrs u ∩
        Round.guests K3 c [true]).card : ℝ) ≤ 1 := by
      rw [guests_T]
      exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
    have hs : (1 : ℝ) ≤ (sOf (Round.d K3) : ℝ) / 2 := by
      rw [d_K3, sOf_two']; norm_num
    linarith
  · intro x hx
    rw [guests_T] at hx
    simp only [Finset.mem_singleton] at hx; subst hx
    rw [d_K3, guests_T, Z0_T, show ({1, 2} : Finset (Fin 3)).card = 2 from rfl, thetaGC_2,
      X0_eq]
    decide

theorem light_F : Round.isLight K3 c [false] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guests_F]
  · intro u _
    rw [guests_F]
    simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  · intro x hx; rw [guests_F] at hx; simp at hx

theorem partVerts_T : Round.partVerts K3 c [true] = {2} := by
  rw [Round.partVerts, if_pos light_T, Z0_T, guests_T]; decide

theorem partVerts_F : Round.partVerts K3 c [false] = {0, 1} := by
  rw [Round.partVerts, if_pos light_F, Z0_F, guests_F]; rfl

/-- The light part `[true]` loses the guest edge `12`: `X_Z = X^0_Z - S_Z` has no edge. -/
theorem partGraph_T_edges : (Round.partGraph K3 c [true]).edges = ∅ := by
  rw [Round.partGraph, if_pos light_T, Round.X, X0_eq, guests_T]; decide

theorem partGraph_F_edges : (Round.partGraph K3 c [false]).edges = {s(0, 1)} := by
  rw [Round.partGraph, if_pos light_F, Round.X, X0_eq, guests_F]; decide

/-- (R5) step (1): `01` goes to `[false]`. -/
theorem assign_01 : Round.assign K3 c s(0, 1) = some [false] := by
  unfold Round.assign
  rw [pre_eq, show c.homeOrder = [[false], [true]] from rfl]
  simp [partGraph_F_edges]

/-- (R5): `12` lies in `X^0` of `[true]` but meets its guest `1`, and no light part contains
both ends, so it passes down (step (4)). -/
theorem assign_12 : Round.assign K3 c s(1, 2) = none := by
  unfold Round.assign
  rw [pre_eq, show c.homeOrder = [[false], [true]] from rfl]
  simp [partGraph_F_edges, partGraph_T_edges, partVerts_F, partVerts_T, light_F, light_T]
  decide

example : s(1, 2) ∈ Round.passed K3 c :=
  (Round.mem_passed K3 c).2 ⟨by rw [g'_eq]; decide, assign_12⟩

example : s(0, 1) ∈ Round.E K3 c [false] :=
  (Round.mem_E K3 c).2 ⟨by rw [g'_eq]; decide, assign_01⟩

/-- `E_l(Z) ⊆ V(Z)^{(2)}`: the light part `[true]` (one vertex) receives no edge. -/
example : Round.E K3 c [true] = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  have h1 := Round.E_subset_sym2 K3 c [true] he
  have h2 := Round.E_subset K3 c [true] he
  rw [partVerts_T] at h1
  rw [g'_eq, K3_edges] at h2
  revert h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h2
  rcases h2 with rfl | rfl | rfl <;> decide

end OverlapTest

/-! ## `Run.cycEdges` (fix round 2, review issue 2) -/

example : run1.cycEdges 1 = {s(0, 1), s(1, 2), s(0, 2)} := by decide
example : run1.cycEdges 0 = ∅ := by decide
example : run1.cycEdges 2 = ∅ := by decide
example : run1.graph' K3 1 = (run1.graph K3 1).deleteEdges (run1.cycEdges 1) :=
  Run.graph'_eq_deleteEdges run1 K3 (by decide)


/-! ## (R4)/(R5) with a standalone pre-part, `Dup*`, a `τ`-run deletion, steps (2) and (3)
(fix round 2, review issue 5; from the round-2 reviewer's scratch test)

`G5` on `Fin 5` with edges `01, 03, 14, 02, 12` (`d = 2`, so `λ = 1`, `P = 1`, `θ^GC(z) = z`,
`s = 40^{100}`). First level: root split `({3,4}, {0,1})`, pieces `[false] = G5[{0,1,3,4}]`
(edges `01, 03, 14`) and `[true] = G5[{0,1,2}] − E(G5[{0,1}])` (edges `02, 12`). Second level:
the `τ`-run at `[false]` splits `({0,3}, ∅)`, deleting `01`; leaves `[false,false] = {0,3}`,
`[false,true] = {1,4}`. Pre-parts `[false,false]`, `[false,true]`, `[true]`; `Dup* = D = {0,1}`.
Not a valid round (only the functions of (R3)–(R5) are exercised).
* Order A `[ff, ft, t]`: `home 0 = ff`, `home 1 = ft`, so `S_t = {0,1}`, `|Z⁰_t| = 3`, (L1)
  fails, `Std = {[true]}`; the deleted edge `01` is assigned to `[true]` by **step (3)**;
  nothing passes down; hubs `{0,1}`, ports `{2}` of `[true]`.
* Order B `[t, ff, ft]`: `S_t = ∅`, `[true]` light with `V = {0,1,2}`; `01` goes to `[true]` by
  **step (2)**; the guest–core edge `03` of `[false,false]` passes down; `E(next) = {03, 14}`. -/

namespace StandaloneTest

def G5 : FGraph (Fin 5) := FGraph.ofEdges Finset.univ {s(0, 1), s(0, 3), s(1, 4), s(0, 2), s(1, 2)}

theorem G5_edges : G5.edges = {s(0, 1), s(0, 3), s(1, 4), s(0, 2), s(1, 2)} := by decide

theorem d_G5 : Round.d G5 = 2 := by
  rw [Round.d, G5_edges, show G5.card = 5 from rfl]
  norm_num [show ({s(0, 1), s(0, 3), s(1, 4), s(0, 2), s(1, 2)} : Finset (Sym2 (Fin 5))).card = 5
    from by decide]

theorem thetaGC_two (z : ℕ) : thetaGC 2 z = z := by
  simp [thetaGC, lamOf]

def t0 : STree (Fin 5) := .node ({3, 4}, {0, 1}) .nil .nil

def tauF : STree (Fin 5) := .node ({0, 3}, ∅) .nil .nil

def tauS : Addr → STree (Fin 5)
  | [false] => tauF
  | _ => .nil

def cA : RoundChoice (Fin 5) := ⟨[], t0, tauS, [[false, false], [false, true], [true]]⟩
def cB : RoundChoice (Fin 5) := ⟨[], t0, tauS, [[true], [false, false], [false, true]]⟩

/-- The two-level tree. -/
def two : STree (Fin 5) := .node ({3, 4}, {0, 1}) tauF .nil

theorem g'A : Round.graph' G5 cA = G5 := by simp [Round.graph', Round.cycEdges, cA]
theorem g'B : Round.graph' G5 cB = G5 := by simp [Round.graph', Round.cycEdges, cB]

theorem pieceA_F : 1 ≤ (Round.piece G5 cA [false]).card := by decide
theorem pieceA_T : 1 ≤ (Round.piece G5 cA [true]).card := by decide

theorem twoLevelA : Round.twoLevel G5 cA = two := by
  unfold Round.twoLevel
  simp only [d_G5, POf_two]
  change STree.graft t0 _ = two
  unfold t0
  simp only [STree.graft]
  rw [if_pos pieceA_F, if_pos pieceA_T]
  rfl

theorem twoLevelB : Round.twoLevel G5 cB = two := by
  unfold Round.twoLevel
  simp only [d_G5, POf_two]
  have h1 : 1 ≤ (Round.piece G5 cB [false]).card := by decide
  have h2 : 1 ≤ (Round.piece G5 cB [true]).card := by decide
  change STree.graft t0 _ = two
  unfold t0
  simp only [STree.graft]
  rw [if_pos h1, if_pos h2]
  rfl

/-- The τ-run at the big piece `[false]` deletes exactly `01`. -/
example : (cA.tauRun [false]).deleted (Round.piece G5 cA [false]) = {s(0, 1)} := by decide

/-- The deleted edge is an edge of `G'`, lies in no leaf of the two-level recursion. -/
example : ∀ a ∈ two.leafAddrs, s(0, 1) ∉ (two.graphAtD G5 a).edges := by decide

theorem X0A (a : Addr) : Round.X0 G5 cA a = two.graphAtD G5 a := by rw [Round.X0, twoLevelA, g'A]
theorem X0B (a : Addr) : Round.X0 G5 cB a = two.graphAtD G5 a := by rw [Round.X0, twoLevelB, g'B]

theorem preA : Round.prePartAddrs G5 cA = {[false, false], [false, true], [true]} := by
  unfold Round.prePartAddrs
  rw [twoLevelA, d_G5, POf_two]
  simp only [X0A]
  decide

theorem preB : Round.prePartAddrs G5 cB = {[false, false], [false, true], [true]} := by
  unfold Round.prePartAddrs
  rw [twoLevelB, d_G5, POf_two]
  simp only [X0B]
  decide

theorem Z0A_ff : Round.Z0 G5 cA [false, false] = {0, 3} := by rw [Round.Z0, X0A]; decide
theorem Z0A_ft : Round.Z0 G5 cA [false, true] = {1, 4} := by rw [Round.Z0, X0A]; decide
theorem Z0A_t : Round.Z0 G5 cA [true] = {0, 1, 2} := by rw [Round.Z0, X0A]; decide
theorem Z0B_ff : Round.Z0 G5 cB [false, false] = {0, 3} := by rw [Round.Z0, X0B]; decide
theorem Z0B_ft : Round.Z0 G5 cB [false, true] = {1, 4} := by rw [Round.Z0, X0B]; decide
theorem Z0B_t : Round.Z0 G5 cB [true] = {0, 1, 2} := by rw [Round.Z0, X0B]; decide

/-- `Dup*` = the vertices `0, 1` duplicated at the first level. -/
example : Round.DupStar G5 cA = {0, 1} := by
  rw [Round.DupStar, twoLevelA, g'A]; decide

theorem DA : Round.D G5 cA = {0, 1} := by
  ext v
  rw [Round.mem_D]
  simp only [Round.mu, preA]
  fin_cases v <;> simp [Finset.filter_insert, Finset.filter_singleton, Z0A_ff, Z0A_ft, Z0A_t]

theorem DB : Round.D G5 cB = {0, 1} := by
  ext v
  rw [Round.mem_D]
  simp only [Round.mu, preB]
  fin_cases v <;> simp [Finset.filter_insert, Finset.filter_singleton, Z0B_ff, Z0B_ft, Z0B_t]

/-- `μ(0) = 2`, `μ(2) = 1`, `μ` counts pre-parts by address. -/
example : Round.mu G5 cA 0 = 2 := by
  simp [Round.mu, preA, Finset.filter_insert, Finset.filter_singleton, Z0A_ff, Z0A_ft, Z0A_t]

/-! ### Order A: `[true]` is standalone (fails (L1)); step (3) -/

theorem homeA (v : Fin 5) : Round.home G5 cA v =
    if v = 0 ∨ v = 3 then some [false, false]
    else if v = 1 ∨ v = 4 then some [false, true] else some [true] := by
  unfold Round.home
  rw [preA, show cA.homeOrder = [[false, false], [false, true], [true]] from rfl]
  fin_cases v <;> simp [Z0A_ff, Z0A_ft, Z0A_t]

theorem guestsA_t : Round.guests G5 cA [true] = {0, 1} := by
  unfold Round.guests; rw [DA, Z0A_t]; simp [homeA]

theorem guestsA_ff : Round.guests G5 cA [false, false] = ∅ := by
  unfold Round.guests; rw [DA, Z0A_ff]; simp [homeA]

theorem guestsA_ft : Round.guests G5 cA [false, true] = ∅ := by
  unfold Round.guests; rw [DA, Z0A_ft]; simp [homeA]

/-- `[true]` fails (L1): `2·2 > 3`. -/
theorem notL1A_t : ¬ Round.isL1 G5 cA [true] := by
  simp [Round.isL1, guestsA_t, Z0A_t]

theorem notLightA_t : ¬ Round.isLight G5 cA [true] := fun h => notL1A_t h.1

theorem lightA_of_noGuests (a : Addr) (h : Round.guests G5 cA a = ∅) : Round.isLight G5 cA a := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, h]
  · intro u _
    rw [h]; simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero]; positivity
  · intro x hx; rw [h] at hx; simp at hx

theorem lightA_ff : Round.isLight G5 cA [false, false] := lightA_of_noGuests _ guestsA_ff
theorem lightA_ft : Round.isLight G5 cA [false, true] := lightA_of_noGuests _ guestsA_ft

/-- `Std = {[true]}`. -/
example : Round.Std G5 cA = {[true]} := by
  ext a
  rw [Round.mem_Std, preA]
  constructor
  · rintro ⟨ha, hl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact absurd lightA_ff hl
    · exact absurd lightA_ft hl
    · simp
  · intro ha
    simp only [Finset.mem_singleton] at ha; subst ha
    exact ⟨by simp, notLightA_t⟩

theorem partGraphA_t : (Round.partGraph G5 cA [true]).edges = {s(0, 2), s(1, 2)} := by
  rw [Round.partGraph, if_neg notLightA_t, X0A]; decide

theorem partGraphA_ff : (Round.partGraph G5 cA [false, false]).edges = {s(0, 3)} := by
  rw [Round.partGraph, if_pos lightA_ff, Round.X, X0A, guestsA_ff]; decide

theorem partGraphA_ft : (Round.partGraph G5 cA [false, true]).edges = {s(1, 4)} := by
  rw [Round.partGraph, if_pos lightA_ft, Round.X, X0A, guestsA_ft]; decide

theorem partVertsA_ff : Round.partVerts G5 cA [false, false] = {0, 3} := by
  rw [Round.partVerts, if_pos lightA_ff, Z0A_ff, guestsA_ff]; rfl

theorem partVertsA_ft : Round.partVerts G5 cA [false, true] = {1, 4} := by
  rw [Round.partVerts, if_pos lightA_ft, Z0A_ft, guestsA_ft]; rfl

theorem partVertsA_t : Round.partVerts G5 cA [true] = {0, 1, 2} := by
  rw [Round.partVerts, if_neg notLightA_t, Z0A_t]

/-- **(R5) step (3)**: the deleted edge `01` lies in no part graph and in no light part, but
inside `Z⁰` of the standalone pre-part `[true]`. -/
theorem assignA_01 : Round.assign G5 cA s(0, 1) = some [true] := by
  unfold Round.assign
  rw [preA, show cA.homeOrder = [[false, false], [false, true], [true]] from rfl]
  simp [partGraphA_ff, partGraphA_ft, partGraphA_t, partVertsA_ff, partVertsA_ft, partVertsA_t,
    lightA_ff, lightA_ft, notLightA_t, Z0A_t]

/-- Step (1) still applies to `03`, `14`, `02`. -/
example : Round.assign G5 cA s(0, 3) = some [false, false] := by
  unfold Round.assign
  rw [preA, show cA.homeOrder = [[false, false], [false, true], [true]] from rfl]
  simp [partGraphA_ff]

example : Round.assign G5 cA s(0, 2) = some [true] := by
  unfold Round.assign
  rw [preA, show cA.homeOrder = [[false, false], [false, true], [true]] from rfl]
  simp [partGraphA_ff, partGraphA_ft, partGraphA_t]

/-- Nothing passes down in order A. -/
example : Round.passed G5 cA = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  rw [Round.mem_passed, g'A, G5_edges] at he
  obtain ⟨he, hn⟩ := he
  revert hn
  unfold Round.assign
  rw [preA, show cA.homeOrder = [[false, false], [false, true], [true]] from rfl]
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simp [partGraphA_ff, partGraphA_ft, partGraphA_t, partVertsA_ff, partVertsA_ft, partVertsA_t,
      lightA_ff, lightA_ft, notLightA_t, Z0A_t]

/-- Hubs and ports of the standalone pre-part `[true]`: `A = {0,1}`, `U = {2}`. -/
example : Round.Z0 G5 cA [true] ∩ Round.D G5 cA = {0, 1} := by rw [Z0A_t, DA]; decide
example : Round.Z0 G5 cA [true] \ Round.D G5 cA = {2} := by rw [Z0A_t, DA]; decide

/-! ### Order B: `[true]` is light; step (2); a guest–core edge passes down -/

theorem homeB (v : Fin 5) : Round.home G5 cB v =
    if v = 0 ∨ v = 1 ∨ v = 2 then some [true]
    else if v = 3 then some [false, false] else some [false, true] := by
  unfold Round.home
  rw [preB, show cB.homeOrder = [[true], [false, false], [false, true]] from rfl]
  fin_cases v <;> simp [Z0B_ff, Z0B_ft, Z0B_t]

theorem guestsB_t : Round.guests G5 cB [true] = ∅ := by
  unfold Round.guests; rw [DB, Z0B_t]; simp [homeB]

theorem guestsB_ff : Round.guests G5 cB [false, false] = {0} := by
  unfold Round.guests; rw [DB, Z0B_ff]; simp [homeB]

theorem guestsB_ft : Round.guests G5 cB [false, true] = {1} := by
  unfold Round.guests; rw [DB, Z0B_ft]; simp [homeB]

theorem lightB_t : Round.isLight G5 cB [true] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guestsB_t]
  · intro u _
    rw [guestsB_t]; simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero]; positivity
  · intro x hx; rw [guestsB_t] at hx; simp at hx

/-- `[false,false]` is light with the guest `0`: (L1) `2 ≤ 2`, (L2) one guest neighbour,
(GC) the guest `0` has one neighbour (`3`) in `{3}`, fewer than `θ = ⌈2·1⌉ = 2`. -/
theorem lightB_ff : Round.isLight G5 cB [false, false] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guestsB_ff, Z0B_ff]
  · intro u _
    have : ((((Round.graph' G5 cB).induce (Round.Z0 G5 cB [false, false])).nbrs u ∩
        Round.guests G5 cB [false, false]).card : ℝ) ≤ 1 := by
      rw [guestsB_ff]
      exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
    have hs : (1 : ℝ) ≤ (sOf (Round.d G5) : ℝ) / 2 := by rw [d_G5, OverlapTest.sOf_two']; norm_num
    linarith
  · intro x hx
    rw [guestsB_ff] at hx
    simp only [Finset.mem_singleton] at hx; subst hx
    rw [d_G5, guestsB_ff, Z0B_ff, show ({0, 3} : Finset (Fin 5)).card = 2 from rfl, thetaGC_two,
      X0B]
    decide

theorem lightB_ft : Round.isLight G5 cB [false, true] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Round.isL1, guestsB_ft, Z0B_ft]
  · intro u _
    have : ((((Round.graph' G5 cB).induce (Round.Z0 G5 cB [false, true])).nbrs u ∩
        Round.guests G5 cB [false, true]).card : ℝ) ≤ 1 := by
      rw [guestsB_ft]
      exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
    have hs : (1 : ℝ) ≤ (sOf (Round.d G5) : ℝ) / 2 := by rw [d_G5, OverlapTest.sOf_two']; norm_num
    linarith
  · intro x hx
    rw [guestsB_ft] at hx
    simp only [Finset.mem_singleton] at hx; subst hx
    rw [d_G5, guestsB_ft, Z0B_ft, show ({1, 4} : Finset (Fin 5)).card = 2 from rfl, thetaGC_two,
      X0B]
    decide

theorem partGraphB_t : (Round.partGraph G5 cB [true]).edges = {s(0, 2), s(1, 2)} := by
  rw [Round.partGraph, if_pos lightB_t, Round.X, X0B, guestsB_t]; decide

theorem partGraphB_ff : (Round.partGraph G5 cB [false, false]).edges = ∅ := by
  rw [Round.partGraph, if_pos lightB_ff, Round.X, X0B, guestsB_ff]; decide

theorem partGraphB_ft : (Round.partGraph G5 cB [false, true]).edges = ∅ := by
  rw [Round.partGraph, if_pos lightB_ft, Round.X, X0B, guestsB_ft]; decide

theorem partVertsB_t : Round.partVerts G5 cB [true] = {0, 1, 2} := by
  rw [Round.partVerts, if_pos lightB_t, Z0B_t, guestsB_t]; rfl

theorem partVertsB_ff : Round.partVerts G5 cB [false, false] = {3} := by
  rw [Round.partVerts, if_pos lightB_ff, Z0B_ff, guestsB_ff]; decide

theorem partVertsB_ft : Round.partVerts G5 cB [false, true] = {4} := by
  rw [Round.partVerts, if_pos lightB_ft, Z0B_ft, guestsB_ft]; decide

/-- **(R5) step (2)**: the deleted edge `01` is in no part graph; both ends lie in the light part
`[true]`. -/
theorem assignB_01 : Round.assign G5 cB s(0, 1) = some [true] := by
  unfold Round.assign
  rw [preB, show cB.homeOrder = [[true], [false, false], [false, true]] from rfl]
  simp [partGraphB_t, partGraphB_ff, partGraphB_ft, partVertsB_t, lightB_t]

/-- The guest–core edge `03` of `[false,false]` (type (α) of s2:propOrigin) passes down. -/
theorem assignB_03 : Round.assign G5 cB s(0, 3) = none := by
  unfold Round.assign
  rw [preB, show cB.homeOrder = [[true], [false, false], [false, true]] from rfl]
  simp [partGraphB_t, partGraphB_ff, partGraphB_ft, partVertsB_t, partVertsB_ff, partVertsB_ft,
    lightB_t, lightB_ff, lightB_ft]

example : s(0, 3) ∈ Round.passed G5 cB :=
  (Round.mem_passed G5 cB).2 ⟨by rw [g'B]; decide, assignB_03⟩

example : s(0, 1) ∈ Round.E G5 cB [true] :=
  (Round.mem_E G5 cB).2 ⟨by rw [g'B]; decide, assignB_01⟩

/-- The next graph keeps `03` and `14` only. -/
example : (Round.next G5 cB).edges = {s(0, 3), s(1, 4)} := by
  rw [Round.next_edges]
  ext e
  rw [Round.mem_passed, g'B, G5_edges]
  constructor
  · rintro ⟨he, hn⟩
    revert hn
    unfold Round.assign
    rw [preB, show cB.homeOrder = [[true], [false, false], [false, true]] from rfl]
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [partGraphB_t, partGraphB_ff, partGraphB_ft, partVertsB_t, partVertsB_ff,
        partVertsB_ft, lightB_t, lightB_ff, lightB_ft]
  · intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨by decide, assignB_03⟩
    · refine ⟨by decide, ?_⟩
      unfold Round.assign
      rw [preB, show cB.homeOrder = [[true], [false, false], [false, true]] from rfl]
      simp [partGraphB_t, partGraphB_ff, partGraphB_ft, partVertsB_t, partVertsB_ff,
        partVertsB_ft, lightB_t, lightB_ff, lightB_ft]


/-- The deleted edges of the two-level recursion: exactly `01`, from the `τ`-run at `[false]`
(`STree.deleted_graft`). -/
example : (Round.twoLevel G5 cA).deleted (Round.graph' G5 cA) = {s(0, 1)} := by
  rw [twoLevelA, g'A]; decide

/-- (GC) through `eBetween` (`FGraph.card_nbrs_inter_eq_eBetween`): in order B the guest `0` of
`[false,false]` has one edge to `Z⁰ \ S = {3}`. -/
example : (Round.X0 G5 cB [false, false]).eBetween {0} ({0, 3} \ {0}) = 1 := by
  rw [X0B]; decide

end StandaloneTest

end EGTest.HB
