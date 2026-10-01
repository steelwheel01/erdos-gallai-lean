module

public import EG.Defs.Chain.JSet
public import EG.Lib.Chain.Lending

/-!
# The J-interface: basic API (companion of `EG.Defs.Chain.JSet`)

* every typed J-edge lies in some `E_l(Z)`, `Z ∈ Std_l`, hence in `E(G)`; under `JPlusProps`,
  `J_l ⊆ ⋃_Z E_l(Z) ⊆ E(G)` (`JPlusProps.subset_E`, `JPlusProps.subset_edges`) and `J_l = ∅` for
  `l ≤ 2` (`JPlusProps.eq_empty_of_le_two`);
* (i), **exclusive** part (independent of `J_l`): no edge has two types
  (`IsJparEdge.not_isJhubEdge`, …, `IsJfrEdge.not_isJlostEdge`), and the centre and the class of
  a centre–port J-edge are unique (`IsJhubEdge.unique`, `IsJfrEdge.unique`,
  `IsJlostEdge.unique`); so `J_l = J^lost ⊔ J^hub ⊔ J^fr ⊔ J^par` (`JPlusProps.union_types`);
* the centre of a `J^hub`-edge is in `D_l`, of a `J^fr`-edge a fresh centre, of a `J^lost`-edge a
  lost centre, and the port end is in `⋃_Z Q*_Z`;
* (J1) for every vertex (`JPlusProps.J1hub_all`, `J1fr_all`, `J1lost_all`: the filters are empty
  at vertices that are not centres of the type);
* the right side of (s6:eqJbound) vanishes for `l ≤ 2` (`jBound_of_le_two`);
* class data of typed J-edges (s7:lemPay (a2), s7:lemEXprime): `IsJhubEdge.one_le_classDeg`,
  `IsJhubEdge.mem_cAggClasses`, `IsJhubEdge.one_le_cAgg`, `IsJfrEdge.one_le_cFresh`,
  `IsJhubEdge.mem_Bead`, `IsJhubEdge.isGiant_of_gammaL_eq_zero`;
* the s7 `RoundInput.Valid` shapes of (J1) and (J2): `JPlusProps.J1hub_ports`,
  `JPlusProps.degE_types_le`;
* non-vacuity: `∅` satisfies `JPlusProps` (`jPlusProps_empty`), and so does every one-edge
  `J^hub` set when `M_l ≥ 2` (`IsJhubEdge.jPlusProps_singleton`).
-/

public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

theorem disjoint_hubs_qs (l : ℕ) (a b : Addr) : Disjoint (run.hubs G l a) (qs run G δ S l b) :=
  Finset.disjoint_of_subset_right
    ((qs_subset_classed run G δ S l b).trans (classed_subset_ports run G l b))
    (disjoint_hubs_ports run G l a b)

theorem disjoint_fresh_qs (l : ℕ) (a : Addr) : Disjoint (run.fresh G l a) (qs run G δ S l a) :=
  Finset.disjoint_of_subset_right (qs_subset_classed run G δ S l a)
    (disjoint_fresh_classed run G l a)

/-! ### Every J-edge lies in some `E_l(Z)` -/

variable {run G δ S}

theorem IsJparEdge.exists_mem_E {l : ℕ} {e : Sym2 V} (h : IsJparEdge run G δ S l e) :
    ∃ a ∈ run.Std G l, e ∈ run.E G l a := by
  obtain ⟨a, ha, he, -⟩ := h; exact ⟨a, ha, he⟩

theorem IsJhubEdge.exists_mem_E {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJhubEdge run G δ S l h Y e) : ∃ a ∈ run.Std G l, e ∈ run.E G l a := by
  obtain ⟨a, ha, he, -⟩ := hh; exact ⟨a, ha, he⟩

theorem IsJfrEdge.exists_mem_E {l : ℕ} {x : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJfrEdge run G δ S l x Y e) : ∃ a ∈ run.Std G l, e ∈ run.E G l a := by
  obtain ⟨a, ha, he, -⟩ := hh; exact ⟨a, ha, he⟩

theorem IsJlostEdge.exists_mem_E {l : ℕ} {v : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJlostEdge run G δ S l v Y e) : ∃ a ∈ run.Std G l, e ∈ run.E G l a := by
  obtain ⟨a, ha, he, -⟩ := hh; exact ⟨a, ha, he⟩

/-- Under `JPlusProps`, `J_l ⊆ ⋃_{Z ∈ Std_l} E_l(Z)`. -/
theorem JPlusProps.exists_mem_E {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J)
    {e : Sym2 V} (he : e ∈ J) : ∃ a ∈ run.Std G l, e ∈ run.E G l a := by
  rcases hJ.types e he with h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
  · exact h.exists_mem_E
  · exact h.exists_mem_E
  · exact h.exists_mem_E
  · exact h.exists_mem_E

theorem JPlusProps.subset_E {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J) :
    J ⊆ (run.Std G l).biUnion (run.E G l) := fun _ he =>
  Finset.mem_biUnion.2 (hJ.exists_mem_E he)

/-- Under `JPlusProps`, `J_l ⊆ E(G)`. -/
theorem JPlusProps.subset_edges {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J) :
    J ⊆ G.edges := fun e he => by
  obtain ⟨a, -, hea⟩ := hJ.exists_mem_E he
  exact E_subset_edges run G l a hea

/-- The edges of a set with `JPlusProps` are not loops. -/
theorem JPlusProps.not_isDiag {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J)
    {e : Sym2 V} (he : e ∈ J) : ¬ e.IsDiag :=
  G.loopless e (hJ.subset_edges he)

/-- Every typed J-edge has an end in `Q*_Z` (for its part), so there are none for `l ≤ 2`. -/
theorem JPlusProps.eq_empty_of_le_two {l : ℕ} (hl : l ≤ 2) {J : Finset (Sym2 V)}
    (hJ : JPlusProps run G δ S l J) : J = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  obtain ⟨a, ha, hea⟩ := hJ.exists_mem_E he
  obtain ⟨u, hu, -⟩ := hJ.J2end a ha e he hea
  rw [qs_of_le_two run G δ S hl] at hu
  exact Finset.notMem_empty u hu

/-! ### (i), exclusive part -/

omit [DecidableEq V] in
/-- A vertex of a role set disjoint from `Q` that lies on an edge `cu` with `u ∈ Q` is `c`. -/
theorem centre_eq_of_eq {Q R : Finset V} (hRQ : Disjoint R Q) {c c' u u' : V} (hu : u ∈ Q)
    (hc' : c' ∈ R) (he : s(c, u) = s(c', u')) : c' = c ∧ u' = u := by
  have hmem : c' ∈ s(c, u) := he ▸ Sym2.mem_mk_left c' u'
  rcases Sym2.mem_iff.1 hmem with rfl | rfl
  · exact ⟨rfl, (Sym2.congr_right.1 he).symm⟩
  · exact absurd hu (Finset.disjoint_left.1 hRQ hc')

theorem IsJparEdge.not_isJhubEdge {l : ℕ} {e : Sym2 V} (hp : IsJparEdge run G δ S l e)
    {h : V} {Y : PartId} : ¬ IsJhubEdge run G δ S l h Y e := by
  rintro ⟨b, hb, heb, u', rfl, hh, -, -⟩
  obtain ⟨a, ha, hea, u, v, he, hu, hv, -⟩ := hp
  obtain rfl := eq_of_mem_E run G hea heb
  have hmem : h ∈ s(u, v) := he ▸ Sym2.mem_mk_left h u'
  rcases Sym2.mem_iff.1 hmem with rfl | rfl
  · exact Finset.disjoint_left.1 (disjoint_hubs_qs run G δ S l a a) hh hu
  · exact Finset.disjoint_left.1 (disjoint_hubs_qs run G δ S l a a) hh hv

theorem IsJparEdge.not_isJfrEdge {l : ℕ} {e : Sym2 V} (hp : IsJparEdge run G δ S l e)
    {x : V} {Y : PartId} : ¬ IsJfrEdge run G δ S l x Y e := by
  rintro ⟨b, hb, heb, u', rfl, hx, -, -⟩
  obtain ⟨a, ha, hea, u, v, he, hu, hv, -⟩ := hp
  obtain rfl := eq_of_mem_E run G hea heb
  have hmem : x ∈ s(u, v) := he ▸ Sym2.mem_mk_left x u'
  rcases Sym2.mem_iff.1 hmem with rfl | rfl
  · exact Finset.disjoint_left.1 (disjoint_fresh_qs run G δ S l a) hx hu
  · exact Finset.disjoint_left.1 (disjoint_fresh_qs run G δ S l a) hx hv

theorem IsJparEdge.not_isJlostEdge {l : ℕ} {e : Sym2 V} (hp : IsJparEdge run G δ S l e)
    {w : V} {Y : PartId} : ¬ IsJlostEdge run G δ S l w Y e := by
  rintro ⟨b, hb, heb, u', rfl, hw, -, -⟩
  obtain ⟨a, ha, hea, u, v, he, hu, hv, -⟩ := hp
  obtain rfl := eq_of_mem_E run G hea heb
  have hmem : w ∈ s(u, v) := he ▸ Sym2.mem_mk_left w u'
  rcases Sym2.mem_iff.1 hmem with rfl | rfl
  · exact Finset.disjoint_left.1 (disjoint_lost_qs run G δ S l a) hw hu
  · exact Finset.disjoint_left.1 (disjoint_lost_qs run G δ S l a) hw hv

theorem IsJhubEdge.not_isJfrEdge {l : ℕ} {e : Sym2 V} {h : V} {Y : PartId}
    (hh : IsJhubEdge run G δ S l h Y e) {x : V} {Y' : PartId} :
    ¬ IsJfrEdge run G δ S l x Y' e := by
  rintro ⟨b, hb, heb, u', rfl, hx, hu', -⟩
  obtain ⟨a, ha, hea, u, he, hh, hu, -⟩ := hh
  obtain rfl := eq_of_mem_E run G hea heb
  obtain ⟨rfl, -⟩ := centre_eq_of_eq (disjoint_fresh_qs run G δ S l a) hu hx he.symm
  exact Finset.disjoint_left.1 (disjoint_hubs_fresh run G l a) hh hx

theorem IsJhubEdge.not_isJlostEdge {l : ℕ} {e : Sym2 V} {h : V} {Y : PartId}
    (hh : IsJhubEdge run G δ S l h Y e) {w : V} {Y' : PartId} :
    ¬ IsJlostEdge run G δ S l w Y' e := by
  rintro ⟨b, hb, heb, u', rfl, hw, hu', -⟩
  obtain ⟨a, ha, hea, u, he, hh, hu, -⟩ := hh
  obtain rfl := eq_of_mem_E run G hea heb
  obtain ⟨rfl, -⟩ := centre_eq_of_eq (disjoint_lost_qs run G δ S l a) hu hw he.symm
  exact Finset.disjoint_left.1 (disjoint_hubs_lost run G δ S l a) hh hw

theorem IsJfrEdge.not_isJlostEdge {l : ℕ} {e : Sym2 V} {x : V} {Y : PartId}
    (hx : IsJfrEdge run G δ S l x Y e) {w : V} {Y' : PartId} :
    ¬ IsJlostEdge run G δ S l w Y' e := by
  rintro ⟨b, hb, heb, u', rfl, hw, hu', -⟩
  obtain ⟨a, ha, hea, u, he, hx, hu, -⟩ := hx
  obtain rfl := eq_of_mem_E run G hea heb
  obtain ⟨rfl, -⟩ := centre_eq_of_eq (disjoint_lost_qs run G δ S l a) hu hw he.symm
  exact Finset.disjoint_left.1 (disjoint_fresh_lost run G δ S l a) hx hw

/-- The centre and the class of a `J^hub`-edge are unique. -/
theorem IsJhubEdge.unique {l : ℕ} {e : Sym2 V} {h h' : V} {Y Y' : PartId}
    (h1 : IsJhubEdge run G δ S l h Y e) (h2 : IsJhubEdge run G δ S l h' Y' e) :
    h' = h ∧ Y' = Y := by
  obtain ⟨a, ha, hea, u, rfl, hh, hu, rfl⟩ := h1
  obtain ⟨b, hb, heb, u', he, hh', hu', rfl⟩ := h2
  obtain rfl := eq_of_mem_E run G hea heb
  obtain ⟨rfl, rfl⟩ := centre_eq_of_eq (disjoint_hubs_qs run G δ S l a a) hu hh' he
  exact ⟨rfl, rfl⟩

/-- The centre and the class of a `J^fr`-edge are unique. -/
theorem IsJfrEdge.unique {l : ℕ} {e : Sym2 V} {x x' : V} {Y Y' : PartId}
    (h1 : IsJfrEdge run G δ S l x Y e) (h2 : IsJfrEdge run G δ S l x' Y' e) :
    x' = x ∧ Y' = Y := by
  obtain ⟨a, ha, hea, u, rfl, hx, hu, rfl⟩ := h1
  obtain ⟨b, hb, heb, u', he, hx', hu', rfl⟩ := h2
  obtain rfl := eq_of_mem_E run G hea heb
  obtain ⟨rfl, rfl⟩ := centre_eq_of_eq (disjoint_fresh_qs run G δ S l a) hu hx' he
  exact ⟨rfl, rfl⟩

/-- The centre and the class of a `J^lost`-edge are unique. -/
theorem IsJlostEdge.unique {l : ℕ} {e : Sym2 V} {v v' : V} {Y Y' : PartId}
    (h1 : IsJlostEdge run G δ S l v Y e) (h2 : IsJlostEdge run G δ S l v' Y' e) :
    v' = v ∧ Y' = Y := by
  obtain ⟨a, ha, hea, u, rfl, hv, hu, rfl⟩ := h1
  obtain ⟨b, hb, heb, u', he, hv', hu', rfl⟩ := h2
  obtain rfl := eq_of_mem_E run G hea heb
  obtain ⟨rfl, rfl⟩ := centre_eq_of_eq (disjoint_lost_qs run G δ S l a) hu hv' he
  exact ⟨rfl, rfl⟩

/-- (i): under `JPlusProps`, `J_l = J^lost ∪ J^hub ∪ J^fr ∪ J^par` (a disjoint union by the
exclusivity lemmas above). -/
theorem JPlusProps.union_types {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J) :
    Jlost run G δ S l J ∪ Jhub run G δ S l J ∪ Jfr run G δ S l J ∪ Jpar run G δ S l J = J := by
  classical
  ext e
  simp only [Jlost, Jhub, Jfr, Jpar, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (((⟨he, -⟩ | ⟨he, -⟩) | ⟨he, -⟩) | ⟨he, -⟩) <;> exact he
  · intro he
    rcases hJ.types e he with h | h | h | h
    · exact Or.inr ⟨he, h⟩
    · exact Or.inl (Or.inl (Or.inr ⟨he, h⟩))
    · exact Or.inl (Or.inr ⟨he, h⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨he, h⟩))

/-! ### Roles of the ends -/

theorem IsJhubEdge.mem_D {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJhubEdge run G δ S l h Y e) : h ∈ run.D G l := by
  obtain ⟨a, -, -, -, -, hh, -⟩ := hh
  exact hubs_subset_D run G l a hh

theorem IsJfrEdge.mem_freshCentres {l : ℕ} {x : V} {Y : PartId} {e : Sym2 V}
    (hx : IsJfrEdge run G δ S l x Y e) : x ∈ freshCentres run G l := by
  obtain ⟨a, ha, -, -, -, hx, -⟩ := hx
  exact (_root_.EG.Chain.mem_freshCentres run G).2 ⟨a, ha, hx⟩

theorem IsJlostEdge.mem_lostRound {l : ℕ} {v : V} {Y : PartId} {e : Sym2 V}
    (hv : IsJlostEdge run G δ S l v Y e) : v ∈ lostRound run G δ S l := by
  obtain ⟨a, ha, -, -, -, hv, -⟩ := hv
  exact (_root_.EG.Chain.mem_lostRound run G δ S).2 ⟨a, ha, hv⟩

/-! ### (J1) at every vertex -/

open Classical in
theorem JPlusProps.J1hub_all {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J)
    (h : V) (Y : PartId) : (J.filter (IsJhubEdge run G δ S l h Y)).card ≤ 1 := by
  classical
  by_cases hD : h ∈ run.D G l
  · exact hJ.J1hub h hD Y
  · rw [Finset.card_le_one]
    intro e he
    exact absurd (Finset.mem_filter.1 he).2.mem_D hD

open Classical in
theorem JPlusProps.J1fr_all {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J)
    (x : V) (Y : PartId) : (J.filter (IsJfrEdge run G δ S l x Y)).card ≤ 1 := by
  classical
  by_cases hx : x ∈ freshCentres run G l
  · exact hJ.J1fr x hx Y
  · rw [Finset.card_le_one]
    intro e he
    exact absurd (Finset.mem_filter.1 he).2.mem_freshCentres hx

open Classical in
theorem JPlusProps.J1lost_all {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J)
    (v : V) (Y : PartId) : (J.filter (IsJlostEdge run G δ S l v Y)).card ≤ 1 := by
  classical
  by_cases hv : v ∈ lostRound run G δ S l
  · exact hJ.J1lost v hv Y
  · rw [Finset.card_le_one]
    intro e he
    exact absurd (Finset.mem_filter.1 he).2.mem_lostRound hv

/-! ### Class data witnessed by typed J-edges (s7:lemPay (a2), s7:lemEXprime) -/

/-- A `J^hub`-edge of class `Y` at `h` witnesses `d_{Y,l}(h) ≥ 1` (s7:lemPay (a2)). -/
theorem IsJhubEdge.one_le_classDeg {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJhubEdge run G δ S l h Y e) : 1 ≤ classDeg run G δ Y l h := by
  obtain ⟨a, ha, hea, u, rfl, -, hu, hY⟩ := hh
  have huc : u ∈ run.classed G l a := qs_subset_classed run G δ S l a hu
  unfold classDeg
  apply Finset.card_pos.2
  exact ⟨s(h, u), Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_filter.2 ⟨hea, u, huc, rfl, hY⟩⟩⟩

/-- A `J^hub`-edge of class `Y` at `h` puts `Y` among the classes counted by `c^agg_{h,l}`
(s7:lemPay (a2), s7:lemEXprime). -/
theorem IsJhubEdge.mem_cAggClasses {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJhubEdge run G δ S l h Y e) : Y ∈ cAggClasses run G δ h l := by
  obtain ⟨a, ha, hea, u, rfl, -, hu, hY⟩ := hh
  have huc : u ∈ run.classed G l a := qs_subset_classed run G δ S l a hu
  unfold cAggClasses
  exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_filter.2 ⟨huc, hea⟩⟩, hY⟩

/-- A `J^hub`-edge at `h` gives `c^agg_{h,l} ≥ 1`. -/
theorem IsJhubEdge.one_le_cAgg {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJhubEdge run G δ S l h Y e) : 1 ≤ cAgg run G δ h l :=
  Finset.card_pos.2 ⟨Y, hh.mem_cAggClasses⟩

/-- A `J^fr`-edge of class `Y` at `x` lies in a part `Z ∈ Std_l` with `x ∈ F_Z`, and there
`Y` is one of the classes counted by `c_x(Z)`, so `c_x(Z) ≥ 1`. -/
theorem IsJfrEdge.one_le_cFresh {l : ℕ} {x : V} {Y : PartId} {e : Sym2 V}
    (hx : IsJfrEdge run G δ S l x Y e) :
    ∃ a ∈ run.Std G l, x ∈ run.fresh G l a ∧ 1 ≤ cFresh run G δ l a x := by
  obtain ⟨a, ha, hea, u, rfl, hxa, hu, hY⟩ := hx
  have huc : u ∈ run.classed G l a := qs_subset_classed run G δ S l a hu
  refine ⟨a, ha, hxa, Finset.card_pos.2 ⟨Y, ?_⟩⟩
  exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨huc, hea⟩, hY⟩

open Classical in
/-- (J1) in the shape of s7's `RoundInput.Valid` (blueprint s7a): at **every** vertex `h`, at
most one `J^hub`-edge `hu` of `J_l` has its port end `u ∈ ⋃_Z Q*_Z` of class `Y`. (The port end
is determined: `u ∉ D_l ∋ h`, so `s(h,u)` cannot be read the other way round.) -/
theorem JPlusProps.J1hub_ports {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J)
    (h : V) (Y : PartId) :
    ((Jhub run G δ S l J).filter
      (fun e => ∃ u ∈ qsRound run G δ S l, e = s(h, u) ∧ δ l u = Y)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card ?_) (hJ.J1hub_all h Y)
  intro e he
  simp only [Jhub, Finset.mem_filter] at he ⊢
  obtain ⟨⟨heJ, h', Y', hh'⟩, u, hu, rfl, hY⟩ := he
  refine ⟨heJ, ?_⟩
  obtain ⟨a, ha, hea, u', he', hh'a, hu', hY'⟩ := hh'
  have hD : h' ∈ run.D G l := hubs_subset_D run G l a hh'a
  rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, ha, hea, u, rfl, hh'a, hu', hY⟩
  · exact absurd hu (Finset.disjoint_left.1 (disjoint_D_qsRound run G δ S l) hD)

/-- (J2) in the shape of s7's `RoundInput.Valid` (blueprint s7a): a vertex outside `D_l` carries
at most `M_l − 1` edges of `J^lost ∪ J^hub ∪ J^fr ∪ J^par`. -/
theorem JPlusProps.degE_types_le {l : ℕ} {J : Finset (Sym2 V)} (hJ : JPlusProps run G δ S l J)
    {v : V} (hv : v ∉ run.D G l) :
    degE (Jlost run G δ S l J ∪ Jhub run G δ S l J ∪ Jfr run G δ S l J ∪ Jpar run G δ S l J) v
      ≤ run.M G l - 1 := by
  rw [hJ.union_types]
  exact hJ.J2out v hv

/-! ### The bound (s6:eqJbound) -/

variable (run G δ S) in
/-- The right side of (s6:eqJbound) vanishes for `l ≤ 2` (no classed ports). -/
theorem jBound_of_le_two {l : ℕ} (hl : l ≤ 2) : jBound run G δ S l = 0 := by
  unfold jBound
  simp [cAgg_eq_zero_of_le_two run G δ hl, cFresh, cPP, classed_eq_empty_of_le_two run G hl,
    lost_of_le_two run G δ S hl]

/-! ### Non-vacuity -/

variable (run G δ S) in
/-- The empty set satisfies the J-interface (non-vacuity of `JPlusProps`). -/
theorem jPlusProps_empty (l : ℕ) : JPlusProps run G δ S l ∅ where
  types := by simp
  J1hub := by simp
  J1fr := by simp
  J1lost := by simp
  J2end := by simp
  J2cap := by simp
  J2out := by simp [degE, edgesAt]
  J2card := by simp
  freshCap := by simp

/-- A `J^hub`-edge of class `Y` is a bead edge of `(Y,l)` (its centre is a hub, not a classed
port; design review 2, MINOR-D). -/
theorem IsJhubEdge.mem_Bead {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJhubEdge run G δ S l h Y e) : e ∈ Bead run G δ Y l := by
  classical
  obtain ⟨a, ha, hea, u, rfl, hh, hu, hY⟩ := hh
  have huc : u ∈ run.classed G l a := qs_subset_classed run G δ S l a hu
  have hhc : h ∉ run.classed G l a := fun hc =>
    Finset.disjoint_left.1 (disjoint_hubs_ports run G l a a) hh (classed_subset_ports run G l a hc)
  unfold Bead
  exact Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_filter.2 ⟨hea, h, u, rfl, huc, hY, Or.inl hhc⟩⟩

/-- If `γ_l = 0`, a `J^hub`-edge of class `Y` makes `(Y,l)` giant. -/
theorem IsJhubEdge.isGiant_of_gammaL_eq_zero {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (hh : IsJhubEdge run G δ S l h Y e) (hγ : gammaL run G l = 0) : IsGiant run G δ Y l := by
  have hB := hh.mem_Bead
  obtain ⟨a, -, -, u, rfl, hha, hu, -⟩ := hh
  have hne : h ≠ u := fun hEq =>
    Finset.disjoint_left.1 (disjoint_hubs_qs run G δ S l a a) hha (hEq ▸ hu)
  exact isGiant_of_mem_Bead_of_gammaL_eq_zero run G δ hB hne hγ

/-- Non-vacuity beyond `∅` (design review 2, Check A; review items MINOR-1/MINOR-D): a single
`J^hub`-edge satisfies all nine fields of `JPlusProps` as soon as `M_l ≥ 2`. So the fields are
jointly satisfiable on a nonempty `J`, and `JPlusProps` is not a predicate that only `∅`
satisfies. -/
theorem IsJhubEdge.jPlusProps_singleton {l : ℕ} {h : V} {Y : PartId} {e : Sym2 V}
    (he : IsJhubEdge run G δ S l h Y e) (hM : 2 ≤ run.M G l) :
    JPlusProps run G δ S l {e} := by
  classical
  have hM1 : 1 ≤ run.M G l - 1 := by omega
  obtain ⟨a, ha, hea, u, rfl, hh, hu, hY⟩ := he
  have he' : IsJhubEdge run G δ S l h Y s(h, u) := ⟨a, ha, hea, u, rfl, hh, hu, hY⟩
  have hGpos : 1 ≤ G.card := by
    have := E_subset_edges run G l a hea
    have hv : h ∈ G.verts := G.edge_verts _ this h (Sym2.mem_mk_left h u)
    exact Finset.card_pos.2 ⟨h, hv⟩
  refine
    { types := ?_, J1hub := ?_, J1fr := ?_, J1lost := ?_, J2end := ?_, J2cap := ?_,
      J2out := ?_, J2card := ?_, freshCap := ?_ }
  · intro e he
    rw [Finset.mem_singleton] at he
    subst he
    exact Or.inr (Or.inl ⟨h, Y, he'⟩)
  · intro _ _ _
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  · intro _ _ _
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  · intro _ _ _
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  · intro b hb e he heb
    rw [Finset.mem_singleton] at he
    subst he
    obtain rfl := eq_of_mem_E run G hea heb
    exact ⟨u, hu, Sym2.mem_mk_right h u⟩
  · intro _ _ _
    exact ((Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)).trans hM1
  · intro v _
    unfold degE edgesAt
    exact ((Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)).trans hM1
  · simp only [Finset.card_singleton]
    calc 1 = 1 * 1 := by ring
      _ ≤ G.card * (run.M G l - 1) := Nat.mul_le_mul hGpos hM1
  · intro _ _
    exact ((Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)).trans hM1

end EG.Chain
