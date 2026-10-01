import EG.Lib.Found.Graph

/-! Unit tests for `EG.Defs.Graph`, `EG.Defs.Walk`, `EG.Defs.Expander` (plan §8 Q1: definition
unit tests and non-vacuity). -/

namespace EGTest

open EG FGraph

/-! ## The path `0 - 1 - 2` -/

/-- The path on the three vertices `0, 1, 2`. -/
def P3 : FGraph ℕ := ofEdges {0, 1, 2} {s(0, 1), s(1, 2)}

example : P3.card = 3 := by decide
example : P3.edges.card = 2 := by decide
example : P3.Adj 0 1 ∧ P3.Adj 1 0 ∧ ¬ P3.Adj 0 2 ∧ ¬ P3.Adj 1 1 := by decide
example : P3.nbrs 1 = {0, 2} := by decide
example : P3.deg 0 = 1 ∧ P3.deg 1 = 2 ∧ P3.deg 2 = 1 := by decide
example : degE P3.edges 1 = 2 := by decide
example : P3.minDeg = 1 ∧ P3.maxDeg = 2 := by decide
example : P3.nbrSet {0} = {1} := by decide
example : P3.nbrSet {0, 1} = {2} := by decide
example : P3.nbrSet {0, 2} = {1} := by decide
example : P3.nbrSet {0, 1, 2} = ∅ := by decide
example : (P3.deleteEdges {s(0, 1)}).nbrSet {0} = ∅ := by decide
example : (P3.deleteEdges {s(0, 1)}).deg 1 = 1 := by decide
example : (P3.induce {0, 1}).edges = {s(0, 1)} := by decide
example : (P3.deleteVerts {1}).edges = ∅ := by decide
example : (P3.deleteVerts {1}).verts = {0, 2} := by decide
example : P3.edgesBetween {0} {1, 2} = {s(0, 1)} := by decide
example : P3.eBetween {1} {0, 2} = 2 := by decide
-- loops and edges leaving the vertex set are discarded by `ofEdges`
example : (ofEdges ({0, 1} : Finset ℕ) {s(0, 0), s(0, 1), s(1, 5)}).edges = {s(0, 1)} := by decide

/-! ### Paths in `P3` -/

example : walkEdges [0, 1, 2] = [s((0 : ℕ), 1), s(1, 2)] := rfl
example : pathLength [0, 1, 2] = (2 : ℕ) := rfl
example : interior [0, 1, 2] = [(1 : ℕ)] := rfl

example : IsPathBetween P3.edges 0 2 [0, 1, 2] :=
  ⟨⟨by simp, by decide, by decide⟩, rfl, rfl⟩

example : IsThrough {1} [0, 1, 2] := by decide
example : ¬ IsThrough {2} [0, 1, 2] := by decide
-- the ends of a path through `W` are unrestricted
example : IsThrough ∅ [0, 1] := by decide

-- a repeated vertex is not allowed
example : ¬ IsPathIn P3.edges [0, 1, 0] := fun h => by
  have := h.nodup
  simp at this

-- `0 2` is not an edge
example : ¬ IsPathIn P3.edges [0, 2] := by
  rw [isPathIn_pair]
  decide

/-- Every `02`-path in `P3` has `1` as an interior vertex. -/
theorem P3_path_0_2 {p : List ℕ} (hp : IsPathBetween P3.edges 0 2 p) : 1 ∈ interior p := by
  obtain ⟨b, hb, hbE⟩ := hp.exists_first_edge (by decide)
  have hb1 : b = 1 := by
    simp [P3, ofEdges, Finset.mem_filter] at hbE
    exact hbE.1
  subst hb1
  match p, hp, hb with
  | [], hp, _ => exact absurd rfl hp.1.1
  | [_], _, hb => simp at hb
  | [a, c], hp, hb =>
    have ha : a = 0 := by simpa using hp.2.1
    have hc : c = 2 := by simpa using hp.2.2
    subst ha hc
    simp at hb
  | a :: c :: d :: t, hp, hb =>
    have ha : a = 0 := by simpa using hp.2.1
    subst ha
    have hnd := hp.1.nodup
    -- the first edge `0c` is `01`, so `c = 1` (the edge `01` occurs only once in a path)
    have hc : c = 1 := by
      rw [walkEdges_cons_cons, List.mem_cons] at hb
      rcases hb with h | h
      · exact (Sym2.congr_right.1 h).symm
      · exfalso
        have h0 := mem_of_mem_walkEdges h (Sym2.mem_mk_left 0 1)
        simp only [List.nodup_cons] at hnd
        exact hnd.1 h0
    subst hc
    simp [EG.interior]

/-! ### Balls in `P3` -/

example : 1 ∈ ball P3 1 {0} {1, 2} :=
  mem_ball.2 ⟨by decide, 0, by decide, [0, 1], ⟨⟨by simp, by decide, by decide⟩, rfl, rfl⟩,
    by decide, by decide⟩

example : 2 ∈ ball P3 2 {0} {1, 2} :=
  mem_ball.2 ⟨by decide, 0, by decide, [0, 1, 2], ⟨⟨by simp, by decide, by decide⟩, rfl, rfl⟩,
    by decide, by decide⟩

-- radius `1` does not reach `2`
example : 2 ∉ ball P3 1 {0} {1, 2} := by
  intro h
  obtain ⟨-, u, hu, p, hp, -, hl⟩ := mem_ball.1 h
  rw [Finset.mem_singleton] at hu
  subst hu
  have := hp.eq_pair (by decide) hl
  subst this
  exact absurd hp.1 (by rw [isPathIn_pair]; decide)

-- `2` cannot be reached through `{2}`: the interior vertex `1` is not in `{2}`
example : 2 ∉ ball P3 5 {0} {2} := by
  intro h
  obtain ⟨-, u, hu, p, hp, hpW, -⟩ := mem_ball.1 h
  rw [Finset.mem_singleton] at hu
  subst hu
  have := hpW 1 (P3_path_0_2 hp)
  simp at this

-- the start need not lie in `W`, but the reached vertex must
example : 1 ∈ ball P3 1 {0} {1} :=
  mem_ball.2 ⟨by decide, 0, by decide, [0, 1], ⟨⟨by simp, by decide, by decide⟩, rfl, rfl⟩,
    by decide, by decide⟩
example : 0 ∉ ball P3 3 {0} {1} := fun h => by
  have := ball_subset h
  simp at this

/-! ## The complete graph `K₄` -/

/-- `K₄` from Mathlib's `⊤ : SimpleGraph (Fin 4)`. -/
def K4 : FGraph (Fin 4) := ofSimpleGraph ⊤

example : K4.card = 4 := by decide
example : K4.edges.card = 6 := by decide
example (v : Fin 4) : K4.deg v = 3 := by
  rw [K4, ofSimpleGraph_deg, SimpleGraph.complete_graph_degree, Fintype.card_fin]
example : K4.minDeg = 3 := by decide
example : K4.nbrSet {0} = {1, 2, 3} := by decide
example : K4.nbrSet {0, 1} = {2, 3} := by decide

/-- In a graph in which any two distinct vertices are adjacent, `Nbr(U) = V \ U` for every
non-empty `U ⊆ V`. -/
theorem nbrSet_of_complete {V : Type*} [DecidableEq V] {H : FGraph V}
    (hK : ∀ u ∈ H.verts, ∀ v ∈ H.verts, u ≠ v → H.Adj u v) {U : Finset V}
    (hU : U ⊆ H.verts) (hne : U.Nonempty) : H.nbrSet U = H.verts \ U := by
  ext v
  rw [mem_nbrSet, Finset.mem_sdiff]
  constructor
  · rintro ⟨hv, hvU, -⟩
    exact ⟨hv, hvU⟩
  · rintro ⟨hv, hvU⟩
    obtain ⟨u, hu⟩ := hne
    exact ⟨hv, hvU, u, hu, hK u (hU hu) v hv fun h => hvU (h ▸ hu)⟩

/-- Non-vacuity of Definition 11: `K₄` is a `(1, 0)`-expander. -/
theorem K4_isExpander : K4.IsExpander 1 0 := by
  intro U F hU hF h1 h2 h3
  have hF0 : F = ∅ := by
    rw [zero_mul] at h3
    exact Finset.card_eq_zero.1 (by exact_mod_cast le_antisymm h3 (Nat.cast_nonneg _))
  subst hF0
  have hK : ∀ u ∈ K4.verts, ∀ v ∈ K4.verts, u ≠ v → K4.Adj u v := fun u _ v _ huv => by
    rw [K4, ofSimpleGraph_adj]; exact huv
  rw [deleteEdges_empty, nbrSet_of_complete hK hU (Finset.card_pos.1 (by omega)),
    Finset.card_sdiff_of_subset hU]
  have hcard : K4.verts.card = 4 := by decide
  have hlog : Real.logb 2 (K4.card : ℝ) = 2 := by
    rw [card_def, hcard]
    rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one]
    · norm_num
    · norm_num
  rw [hlog, hcard]
  rw [card_def, hcard] at h2
  have hU2 : U.card ≤ 2 := by
    have : (U.card : ℝ) < 3 := by push_cast at h2; linarith
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
  have : ((4 - U.card : ℕ) : ℝ) ≥ 2 := by
    have : 2 ≤ 4 - U.card := by omega
    exact_mod_cast this
  have : (U.card : ℝ) ≤ 2 := by exact_mod_cast hU2
  norm_num
  linarith

-- consistent with the B–M remark: `δ(K₄) = 3 > 0`
example : (0 : ℝ) < K4.minDeg := K4_isExpander.lt_minDeg one_pos (by decide)

/-! ## Long paths are not expanders -/

/-- The path `0 - 1 - ⋯ - (n-1)` on `n` vertices. -/
def pathGraph (n : ℕ) : FGraph ℕ :=
  ofEdges (Finset.range n) ((Finset.range (n - 1)).image fun i => s(i, i + 1))

example : (pathGraph 3).edges = P3.edges := by decide
example : (pathGraph 5).deg 0 = 1 ∧ (pathGraph 5).deg 2 = 2 := by decide

theorem pathGraph_adj {n u v : ℕ} (h : (pathGraph n).Adj u v) : v = u + 1 ∨ u = v + 1 := by
  rw [pathGraph, ofEdges_adj, Finset.mem_image] at h
  obtain ⟨⟨i, -, hi⟩, -⟩ := h
  rcases Sym2.eq_iff.1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; rfl
  · right; rfl

/-- The path on `60` vertices is not a `(1, 0)`-expander: `U = {0, …, 39}` has the single
outside neighbour `40`, while `|U| / log² 60 > 40 / 36 > 1`. -/
theorem pathGraph60_not_isExpander : ¬ (pathGraph 60).IsExpander 1 0 := by
  intro h
  have hcard : (pathGraph 60).card = 60 := by
    rw [card_def, pathGraph, ofEdges_verts, Finset.card_range]
  have hU : (Finset.range 40).card = 40 := Finset.card_range 40
  have key := h (Finset.range 40) ∅
    (by rw [pathGraph, ofEdges_verts]; exact Finset.range_subset_range.2 (by norm_num))
    (Finset.empty_subset _) (by rw [hU]; norm_num) (by rw [hU, hcard]; norm_num)
    (by simp)
  rw [deleteEdges_empty, hU, hcard] at key
  push_cast at key
  -- `Nbr(U) ⊆ {40}`
  have hsub : (pathGraph 60).nbrSet (Finset.range 40) ⊆ {40} := by
    intro v hv
    obtain ⟨-, hvU, u, hu, huv⟩ := mem_nbrSet.1 hv
    rw [Finset.mem_range] at hvU hu
    rw [Finset.mem_singleton]
    rcases pathGraph_adj huv with h | h <;> omega
  have hle : (((pathGraph 60).nbrSet (Finset.range 40)).card : ℝ) ≤ 1 := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
  -- `0 < log₂ 60 < 6`
  have hlog6 : Real.logb 2 (60 : ℝ) < 6 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hlog0 : 0 < Real.logb 2 (60 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)
  have hsq : Real.logb 2 (60 : ℝ) ^ 2 < 36 := by nlinarith
  have hpos : 0 < Real.logb 2 (60 : ℝ) ^ 2 := by positivity
  have h1 : 1 < 1 * (40 : ℝ) / Real.logb 2 (60 : ℝ) ^ 2 := by
    rw [lt_div_iff₀ hpos]
    linarith
  linarith

/-- Via the B–M remark: a path on `n ≥ 2` vertices has an end of degree `1`, so it is not an
`(ε, 1)`-expander for any `ε > 0`. -/
example : ¬ (pathGraph 5).IsExpander (1 / 2) 1 := fun h => by
  have := h.lt_deg (by norm_num) (by decide) (v := 0) (by decide)
  have h0 : (pathGraph 5).deg 0 = 1 := by decide
  rw [h0] at this
  norm_num at this

-- the hypothesis `0 < ε` of the remark is needed
example : (pathGraph 5).IsExpander 0 100 := isExpander_of_nonpos le_rfl
-- one-vertex graphs are expanders for all parameters
example : (pathGraph 1).IsExpander 1 1000 := isExpander_of_card_le_one (by decide)

/-! ## Path connectivity (Definition 7) -/

/-- Non-vacuity of Definition 7: a complete graph is `(1,1)`-path connected through any `W`
(pairs of a family in which every vertex lies in at most one pair are disjoint, so the edges
`x_i y_i` are distinct). -/
theorem complete_isPathConnected {V : Type*} [DecidableEq V] {H : FGraph V}
    (hK : ∀ u ∈ H.verts, ∀ v ∈ H.verts, u ≠ v → H.Adj u v) (W : Finset V) :
    H.IsPathConnected 1 1 W := by
  classical
  intro ι _ P hP ht
  refine ⟨fun i => [(P i).1, (P i).2], fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨h1, h2, hne⟩ := hP i
    exact ⟨isPathBetween_pair.2 ⟨hne, hK _ h1 _ h2 hne⟩, isThrough_pair _ _, by simp⟩
  · simp only [walkEdges_cons_cons, walkEdges_singleton, List.disjoint_singleton,
      List.mem_singleton]
    intro heq
    -- the vertex `(P i).1` lies in the pairs `i` and `j`
    have hmem : (P i).1 = (P j).1 ∨ (P i).1 = (P j).2 := by
      rcases Sym2.eq_iff.1 heq with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have h2 : 2 ≤ (Finset.univ.filter (fun k => (P k).1 = (P i).1 ∨ (P k).2 = (P i).1)).card := by
      have hsub : ({i, j} : Finset ι) ⊆
          Finset.univ.filter (fun k => (P k).1 = (P i).1 ∨ (P k).2 = (P i).1) := by
        intro k hk
        rw [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases hk with rfl | rfl
        · exact Or.inl rfl
        · rcases hmem with h | h
          · exact Or.inl h.symm
          · exact Or.inr h.symm
      calc 2 = ({i, j} : Finset ι).card := (Finset.card_pair hij).symm
        _ ≤ _ := Finset.card_le_card hsub
    have h1 := ht (P i).1
    norm_cast at h1
    omega

example : K4.IsPathConnected 1 1 ∅ :=
  complete_isPathConnected (fun u _ v _ huv => by rw [K4, ofSimpleGraph_adj]; exact huv) ∅

/-- `P3` is not `(1,1)`-path connected (through any `W`): the pair `{0, 2}` needs a path of
length `≤ 1`. -/
example (W : Finset ℕ) : ¬ P3.IsPathConnected 1 1 W := by
  intro h
  obtain ⟨Q, hQ, -⟩ := h Unit (fun _ => (0, 2)) (fun _ => by decide) (fun v => by
    norm_cast
    exact (Finset.card_le_univ _).trans (by simp))
  obtain ⟨hp, -, hl⟩ := hQ ()
  have hl' : pathLength (Q ()) ≤ 1 := by exact_mod_cast hl
  have := hp.eq_pair (by decide) hl'
  rw [this] at hp
  exact absurd hp.1 (by rw [isPathIn_pair]; decide)

/-- The single edge `01`. -/
def K2 : FGraph ℕ := ofEdges {0, 1} {s(0, 1)}

/-- The multiset clause matters: the pair `{0,1}` taken twice needs two edge-disjoint `01`-paths,
which the single edge `01` does not have. So `K2` is not `(ℓ, 2)`-path connected, for every `ℓ`
and `W` (while it is `(1,1)`-path connected). -/
example (ℓ : ℝ) (W : Finset ℕ) : ¬ K2.IsPathConnected ℓ 2 W := by
  intro h
  obtain ⟨Q, hQ, hdisj⟩ := h (Fin 2) (fun _ => (0, 1)) (fun _ => by decide) (fun v => by
    norm_cast
    exact (Finset.card_le_univ _).trans (by simp))
  have hfirst : ∀ i, s(0, 1) ∈ walkEdges (Q i) := fun i => by
    obtain ⟨b, hb, hbE⟩ := (hQ i).1.exists_first_edge (by decide)
    have hb1 : b = 1 := by
      simp [K2, ofEdges, Finset.mem_filter] at hbE
      exact hbE.1
    rw [hb1] at hb
    exact hb
  exact hdisj 0 1 (by decide) (hfirst 0) (hfirst 1)

theorem K2_isPathConnected : K2.IsPathConnected 1 1 ∅ :=
  complete_isPathConnected (fun u hu v hv huv => by
    rw [K2, ofEdges_adj]
    simp only [K2, ofEdges_verts, Finset.mem_insert, Finset.mem_singleton] at hu hv
    refine ⟨?_, huv, by simp [hu, hv]⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all [Sym2.eq_swap]) ∅

/-- A real multiplicity (as `𝗍 = 2^{10}L^8` in s4): `(ℓ, 3/2)`-path connectivity is
`(ℓ, ⌊3/2⌋₊) = (ℓ, 1)`-path connectivity, so `K₂` is `(1, 3/2)`-path connected ... -/
example : K2.IsPathConnected 1 (3 / 2) ∅ := by
  have hfl : ⌊(3 / 2 : ℝ)⌋₊ = 1 := by rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  rw [isPathConnected_natFloor_iff (by norm_num), hfl, Nat.cast_one]
  exact K2_isPathConnected

/-- ... but not `(ℓ, t)`-path connected for any real `t ≥ 2`. -/
example (ℓ t : ℝ) (ht : 2 ≤ t) (W : Finset ℕ) : ¬ K2.IsPathConnected ℓ t W := by
  intro h
  obtain ⟨Q, hQ, hdisj⟩ := h (Fin 2) (fun _ => (0, 1)) (fun _ => by decide) (fun v => by
    refine le_trans ?_ ht
    norm_cast
    exact (Finset.card_le_univ _).trans (by simp))
  have hfirst : ∀ i, s(0, 1) ∈ walkEdges (Q i) := fun i => by
    obtain ⟨b, hb, hbE⟩ := (hQ i).1.exists_first_edge (by decide)
    have hb1 : b = 1 := by
      simp [K2, ofEdges, Finset.mem_filter] at hbE
      exact hbE.1
    rw [hb1] at hb
    exact hb
  exact hdisj 0 1 (by decide) (hfirst 0) (hfirst 1)

-- every graph is `(ℓ, t)`-path connected for `t < 1` (no admissible non-empty family)
example : P3.IsPathConnected 0 (1 / 2) ∅ := isPathConnected_of_lt_one (by norm_num)

/-! ## `K₂` pins the base of the logarithm -/

/-- `K₂` is a `(1, 1/2)`-expander: `n = 2`, so `U` is a single vertex, `F = ∅`, and
`|Nbr(U)| = 1 ≥ 1·1/log₂²2 = 1`. With the natural logarithm the bound would be
`1/ln²2 ≈ 2.08 > 1`, so this test fixes `log = log₂`; it is also a non-vacuity witness of
Definition 11 with `s > 0`. -/
theorem K2_isExpander : K2.IsExpander 1 (1 / 2) := by
  intro U F hU hF h1 h2 h3
  have hc : K2.card = 2 := by decide
  rw [hc] at h2 ⊢
  have hU1 : U.card = 1 := by
    have : (U.card : ℝ) < 2 := by push_cast at h2; linarith
    have : U.card < 2 := by exact_mod_cast this
    omega
  have hF0 : F = ∅ := by
    rw [hU1] at h3
    have : (F.card : ℝ) < 1 := by push_cast at h3; linarith
    have : F.card < 1 := by exact_mod_cast this
    exact Finset.card_eq_zero.1 (by omega)
  subst hF0
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hU1
  have ha : a = 0 ∨ a = 1 := by
    have := hU (Finset.mem_singleton_self a)
    simpa [K2] using this
  have hN : ((K2.deleteEdges ∅).nbrSet {a}).card = 1 := by
    rcases ha with rfl | rfl <;> decide
  have hlog : Real.logb 2 ((2 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_ofNat]; exact Real.logb_self_eq_one (by norm_num)
  rw [hN, Finset.card_singleton, hlog]
  norm_num

/-- The remark after Definition 11 for `K₂`: `s < δ(K₂) = 1`. -/
example : ((1 / 2 : ℝ)) < K2.minDeg := K2_isExpander.lt_minDeg one_pos (by decide)

-- `K₂` is not a `(1, 1)`-expander (`δ(K₂) = 1` is not `> 1`)
example : ¬ K2.IsExpander 1 1 := fun h => by
  have := h.lt_minDeg one_pos (by decide)
  have h1 : K2.minDeg = 1 := by decide
  rw [h1] at this
  norm_num at this

/-- `K₂` is not a `(2, 0)`-expander: `|Nbr({0})| = 1 < 2·1/log₂²2 = 2`. -/
example : ¬ K2.IsExpander 2 0 := fun h => by
  have key := h {0} ∅ (by decide) (Finset.empty_subset _) (by decide)
    (by rw [show K2.card = 2 by decide]; norm_num) (by simp)
  have hN : ((K2.deleteEdges ∅).nbrSet {0}).card = 1 := by decide
  have hlog : Real.logb 2 ((K2.card : ℕ) : ℝ) = 1 := by
    rw [show K2.card = 2 by decide, Nat.cast_ofNat]; exact Real.logb_self_eq_one (by norm_num)
  rw [hN, hlog, Finset.card_singleton] at key
  norm_num at key

/-! ## Mathlib `SimpleGraph` and walks -/

example : K4.toSimpleGraph = ⊤ := toSimpleGraph_ofSimpleGraph _

example : ofSimpleGraph K4.toSimpleGraph = K4 := ofSimpleGraph_toSimpleGraph (by decide)

-- the list path `0 1 2` of `P3` is a Mathlib path of length 2 ...
example : ∃ w : P3.toSimpleGraph.Walk 0 2, w.IsPath ∧ w.length = 2 := by
  have hp : IsPathBetween P3.edges 0 2 [0, 1, 2] := ⟨⟨by simp, by decide, by decide⟩, rfl, rfl⟩
  obtain ⟨w, hw, -, hl⟩ := hp.exists_walk
  exact ⟨w, hw, hl⟩

-- ... and every Mathlib path of `P3.toSimpleGraph` from `0` to `2` passes through `1`
example (w : P3.toSimpleGraph.Walk 0 2) (hw : w.IsPath) : 1 ∈ w.support :=
  interior_subset _ (P3_path_0_2 (isPathBetween_support hw))

end EGTest
