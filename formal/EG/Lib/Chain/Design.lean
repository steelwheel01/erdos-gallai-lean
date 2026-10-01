module

public import EG.Defs.Chain.Design
public import EG.Lib.HB.Run
public import EG.Lib.Found.Components
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Designations and class data: basic API (companion of `EG.Defs.Chain.Design`)

* ports and classed ports: `mem_ports_iff`, `mem_classed_iff`, `classed_subset_Z0`,
  `classed_eq_empty_of_le_two` (no classed ports for `l ≤ 2`);
* a vertex outside `D_l` lies in at most one round-`l` pre-part (`eq_of_mem_Z0_of_notMem_D`), so
  the port sets (and classed port sets) of distinct pre-parts of one round are disjoint
  (`ports_disjoint`, `classed_disjoint`; s6:defDesign "Every classed port `u` of round `l` lies
  in `Q_Z` for exactly one `Z ∈ Std_l`");
* designations: existence (`exists_isDesignation`, from `anc_l(u) ≠ ∅` for classed `u`), and
  `u ∈ V(Y(u))`, `r(Y(u)) + 2 ≤ l`, `Y(u)` is an ancestor (s6:defDesign "Since `Y(u) ∈ anc_l(u)`,
  we have `u ∈ V(Y(u))` and `r(Y(u)) ≤ l − 2`"; s6:lemJplus (iv));
* the class data vanish for `l ≤ 2` and outside `[1, R]` (s6:defDesign "For `l ≤ 2` there are no
  classed ports … and all these quantities vanish");
* `d_{Y,l}(h) ≤ m_{Y,l}` for `h ∈ V(G)`; the port-counting form of `d_{Y,l}(h)`
  (`classDeg_eq_card_ports`); `Y ∈ cAggClasses h l ↔ d_{Y,l}(h) ≥ 1`;
  `γ_l = P_{l-2} / M_l` in `ℕ`; `Bead_{Y,l} ⊆ ⋃_Z E_l(Z)`;
* positive forms (design review 2): `isGiant_of_mem_Bead_of_gammaL_eq_zero`, `one_le_alphaY`.
-/

public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)

/-- A `biUnion` all of whose pieces are empty is empty. -/
theorem biUnion_eq_empty_of {α β : Type*} [DecidableEq β] {s : Finset α} {t : α → Finset β}
    (h : ∀ a ∈ s, t a = ∅) : s.biUnion t = ∅ := by
  ext x
  simp only [Finset.mem_biUnion, Finset.notMem_empty, iff_false, not_exists, not_and]
  intro a ha hx
  rw [h a ha] at hx
  exact Finset.notMem_empty x hx

/-! ### Ports and classed ports -/

theorem mem_ports_iff {l : ℕ} {a : Addr} {u : V} :
    u ∈ run.ports G l a ↔ u ∈ run.Z0 G l a ∧ u ∉ run.D G l := by
  unfold Run.ports; rw [Finset.mem_sdiff]

theorem mem_fresh_iff {l : ℕ} {a : Addr} {u : V} :
    u ∈ run.fresh G l a ↔ u ∈ run.ports G l a ∧ run.anc G l u = ∅ := by
  unfold Run.fresh; rw [Finset.mem_filter]

theorem mem_classed_iff {l : ℕ} {a : Addr} {u : V} :
    u ∈ run.classed G l a ↔ u ∈ run.ports G l a ∧ run.anc G l u ≠ ∅ := by
  unfold Run.classed
  rw [Finset.mem_sdiff, mem_fresh_iff]
  tauto

theorem mem_hubs_iff {l : ℕ} {a : Addr} {u : V} :
    u ∈ run.hubs G l a ↔ u ∈ run.Z0 G l a ∧ u ∈ run.D G l := by
  unfold Run.hubs; rw [Finset.mem_inter]

theorem classed_subset_ports (l : ℕ) (a : Addr) : run.classed G l a ⊆ run.ports G l a :=
  Finset.sdiff_subset

theorem fresh_subset_ports (l : ℕ) (a : Addr) : run.fresh G l a ⊆ run.ports G l a :=
  Finset.filter_subset _ _

theorem ports_subset_Z0 (l : ℕ) (a : Addr) : run.ports G l a ⊆ run.Z0 G l a :=
  Finset.sdiff_subset

theorem classed_subset_Z0 (l : ℕ) (a : Addr) : run.classed G l a ⊆ run.Z0 G l a :=
  (classed_subset_ports run G l a).trans (ports_subset_Z0 run G l a)

theorem hubs_subset_D (l : ℕ) (a : Addr) : run.hubs G l a ⊆ run.D G l :=
  Finset.inter_subset_right

theorem not_mem_D_of_mem_ports {l : ℕ} {a : Addr} {u : V} (hu : u ∈ run.ports G l a) :
    u ∉ run.D G l :=
  ((mem_ports_iff run G).1 hu).2

theorem disjoint_fresh_classed (l : ℕ) (a : Addr) :
    Disjoint (run.fresh G l a) (run.classed G l a) :=
  Finset.disjoint_sdiff

/-- For `l ≤ 2` there are no classed ports (`anc_l = ∅`). -/
theorem classed_eq_empty_of_le_two {l : ℕ} (hl : l ≤ 2) (a : Addr) : run.classed G l a = ∅ := by
  unfold Run.classed
  rw [Run.fresh_eq_ports_of_le_two run G hl, Finset.sdiff_self]

theorem anc_ne_empty_of_mem_classed {l : ℕ} {a : Addr} {u : V} (hu : u ∈ run.classed G l a) :
    run.anc G l u ≠ ∅ :=
  ((mem_classed_iff run G).1 hu).2

/-! ### One pre-part per vertex outside `D_l` -/

theorem mu_eq_card {l : ℕ} (hl : run.IsRound l) (w : V) :
    run.mu G l w = ((run.prePartAddrs G l).filter (fun a => w ∈ run.Z0 G l a)).card := by
  simp only [Run.mu, if_pos hl, Round.mu, Run.prePartAddrs_of_isRound run G hl, Run.Z0]

/-- A vertex outside `D_l` lies in at most one round-`l` pre-part (s2:propStructure (iv); here
directly from the definition of `D_l`). -/
theorem eq_of_mem_Z0_of_notMem_D {l : ℕ} {a b : Addr} (ha : a ∈ run.prePartAddrs G l)
    (hb : b ∈ run.prePartAddrs G l) {u : V} (hua : u ∈ run.Z0 G l a) (hub : u ∈ run.Z0 G l b)
    (hu : u ∉ run.D G l) : a = b := by
  by_contra hab
  apply hu
  have hl := Run.isRound_of_mem_prePartAddrs ha
  rw [Run.mem_D_iff, mu_eq_card run G hl]
  have hsub : ({a, b} : Finset Addr) ⊆
      (run.prePartAddrs G l).filter (fun c => u ∈ run.Z0 G l c) := by
    intro c hc
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact Finset.mem_filter.2 ⟨ha, hua⟩
    · rw [Finset.mem_singleton.1 hc]; exact Finset.mem_filter.2 ⟨hb, hub⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hab] at this

theorem Std_subset_prePartAddrs (l : ℕ) : run.Std G l ⊆ run.prePartAddrs G l := by
  classical
  intro a ha; exact ((Run.mem_Std_iff run G).1 ha).1

/-- The port sets `U_Z` of distinct pre-parts of one round are disjoint. -/
theorem ports_disjoint {l : ℕ} {a b : Addr} (ha : a ∈ run.prePartAddrs G l)
    (hb : b ∈ run.prePartAddrs G l) (hab : a ≠ b) :
    Disjoint (run.ports G l a) (run.ports G l b) := by
  rw [Finset.disjoint_left]
  intro u hua hub
  exact hab (eq_of_mem_Z0_of_notMem_D run G ha hb (ports_subset_Z0 run G l a hua)
    (ports_subset_Z0 run G l b hub) (not_mem_D_of_mem_ports run G hua))

/-- [s6:defDesign] "Every classed port `u` of round `l` lies in `Q_Z` for exactly one
`Z ∈ Std_l` (port sets of one round are disjoint)". -/
theorem classed_disjoint {l : ℕ} {a b : Addr} (ha : a ∈ run.prePartAddrs G l)
    (hb : b ∈ run.prePartAddrs G l) (hab : a ≠ b) :
    Disjoint (run.classed G l a) (run.classed G l b) :=
  Finset.disjoint_of_subset_left (classed_subset_ports run G l a)
    (Finset.disjoint_of_subset_right (classed_subset_ports run G l b) (ports_disjoint run G ha hb hab))

theorem eq_of_mem_classed {l : ℕ} {a b : Addr} (ha : a ∈ run.Std G l) (hb : b ∈ run.Std G l)
    {u : V} (hua : u ∈ run.classed G l a) (hub : u ∈ run.classed G l b) : a = b := by
  by_contra hab
  exact Finset.disjoint_left.1 (classed_disjoint run G (Std_subset_prePartAddrs run G l ha)
    (Std_subset_prePartAddrs run G l hb) hab) hua hub

/-- The sets `E_l(Z)` of distinct addresses are disjoint (run level of `Round.disjoint_E`). -/
theorem E_disjoint {l : ℕ} {a b : Addr} (hab : a ≠ b) : Disjoint (run.E G l a) (run.E G l b) := by
  by_cases hl : run.IsRound l
  · simp only [Run.E, if_pos hl]; exact Round.disjoint_E _ _ hab
  · simp [Run.E_of_not_isRound run G hl]

theorem eq_of_mem_E {l : ℕ} {a b : Addr} {e : Sym2 V} (ha : e ∈ run.E G l a)
    (hb : e ∈ run.E G l b) : a = b := by
  by_contra hab
  exact Finset.disjoint_left.1 (E_disjoint run G hab) ha hb

/-- `E_l(Z) ⊆ E(G)`. -/
theorem E_subset_edges (l : ℕ) (a : Addr) : run.E G l a ⊆ G.edges := by
  refine (Run.E_subset_graph'_edges run G l a).trans ?_
  have h1 : run.graph' G l ≤ run.graph G l := Round.graph'_le _ _
  have h2 : run.graph G l ≤ G := by
    simpa using Run.graph_le_of_le run G (Nat.zero_le l)
  exact (le_trans h1 h2).2

/-! ### Designations -/

/-- [s6:defDesign] a designation exists ("`Y(u) ∈ anc_l(u)`" is non-empty for every classed port:
`Q_Z = U_Z \ F_Z` with `F_Z = {x ∈ U_Z : anc_l(x) = ∅}`); used by s7:thmMainProof. -/
theorem exists_isDesignation : ∃ δ : Designation V, IsDesignation run G δ := by
  classical
  refine ⟨fun l u => if h : (run.anc G l u).Nonempty then h.choose else default, ?_⟩
  intro l _ a _ u hu
  have hne : (run.anc G l u).Nonempty :=
    Finset.nonempty_iff_ne_empty.2 (anc_ne_empty_of_mem_classed run G hu)
  simp only [dif_pos hne]
  exact hne.choose_spec

variable {run G δ}

theorem IsDesignation.mem_anc (hδ : IsDesignation run G δ) {l : ℕ} (hl : 3 ≤ l) {a : Addr}
    (ha : a ∈ run.Std G l) {u : V} (hu : u ∈ run.classed G l a) : δ l u ∈ run.anc G l u :=
  hδ l hl a ha u hu

/-- [s6:defDesign] "Since `Y(u) ∈ anc_l(u)`, we have `u ∈ V(Y(u))`" (= s6:lemJplus (iv)). -/
theorem IsDesignation.mem_ancVerts (hδ : IsDesignation run G δ) {l : ℕ} (hl : 3 ≤ l) {a : Addr}
    (ha : a ∈ run.Std G l) {u : V} (hu : u ∈ run.classed G l a) :
    u ∈ run.ancVerts G (δ l u) :=
  ((Run.mem_anc run G).1 (hδ.mem_anc hl ha hu)).2.2

/-- [s6:defDesign] "… and `r(Y(u)) ≤ l − 2`". -/
theorem IsDesignation.round_add_two_le (hδ : IsDesignation run G δ) {l : ℕ} (hl : 3 ≤ l)
    {a : Addr} (ha : a ∈ run.Std G l) {u : V} (hu : u ∈ run.classed G l a) :
    (δ l u).1 + 2 ≤ l :=
  ((Run.mem_anc run G).1 (hδ.mem_anc hl ha hu)).2.1

theorem IsDesignation.mem_ancestors (hδ : IsDesignation run G δ) {l : ℕ} (hl : 3 ≤ l)
    {a : Addr} (ha : a ∈ run.Std G l) {u : V} (hu : u ∈ run.classed G l a) :
    δ l u ∈ run.ancestors G :=
  ((Run.mem_anc run G).1 (hδ.mem_anc hl ha hu)).1

/-- The round of a class is a round of the run: `1 ≤ r(Y(u))`. -/
theorem IsDesignation.one_le_round (hδ : IsDesignation run G δ) {l : ℕ} (hl : 3 ≤ l)
    {a : Addr} (ha : a ∈ run.Std G l) {u : V} (hu : u ∈ run.classed G l a) :
    1 ≤ (δ l u).1 :=
  (Run.isRound_of_mem_parts run G (hδ.mem_ancestors hl ha hu)).1

variable (run G δ)

/-! ### Vanishing -/

theorem mem_classedPorts {l : ℕ} {u : V} :
    u ∈ classedPorts run G l ↔ ∃ a ∈ run.Std G l, u ∈ run.classed G l a := by
  unfold classedPorts; rw [Finset.mem_biUnion]

theorem classedPorts_eq_empty_of_le_two {l : ℕ} (hl : l ≤ 2) : classedPorts run G l = ∅ :=
  biUnion_eq_empty_of (fun a _ => classed_eq_empty_of_le_two run G hl a)

theorem classedPorts_eq_empty_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) :
    classedPorts run G l = ∅ := by
  unfold classedPorts; simp [Run.Std_of_not_isRound run G hl]

theorem classDeg_eq_zero_of_le_two {l : ℕ} (hl : l ≤ 2) (Y : PartId) (h : V) :
    classDeg run G δ Y l h = 0 := by
  unfold classDeg
  rw [biUnion_eq_empty_of (fun a _ => by simp [classed_eq_empty_of_le_two run G hl]),
    Finset.card_empty]

theorem classDeg_eq_zero_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) (Y : PartId) (h : V) :
    classDeg run G δ Y l h = 0 := by
  unfold classDeg; simp [Run.Std_of_not_isRound run G hl]

theorem mY_eq_zero_of_le_two {l : ℕ} (hl : l ≤ 2) (Y : PartId) : mY run G δ Y l = 0 := by
  unfold mY; simp [classDeg_eq_zero_of_le_two run G δ hl]

theorem mY_eq_zero_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) (Y : PartId) :
    mY run G δ Y l = 0 := by
  unfold mY; simp [classDeg_eq_zero_of_not_isRound run G δ hl]

theorem dStar_eq_zero_of_le_two {l : ℕ} (hl : l ≤ 2) (Y : PartId) : dStar run G δ Y l = 0 := by
  unfold dStar; simp [classedPorts_eq_empty_of_le_two run G hl]

theorem dStar_eq_zero_of_not_isRound {l : ℕ} (hl : ¬ run.IsRound l) (Y : PartId) :
    dStar run G δ Y l = 0 := by
  unfold dStar; simp [classedPorts_eq_empty_of_not_isRound run G hl]

theorem cAgg_eq_zero_of_le_two {l : ℕ} (hl : l ≤ 2) (h : V) : cAgg run G δ h l = 0 := by
  unfold cAgg cAggClasses
  rw [biUnion_eq_empty_of (fun a _ => by simp [classed_eq_empty_of_le_two run G hl]),
    Finset.image_empty, Finset.card_empty]

theorem Bead_eq_empty_of_le_two {l : ℕ} (hl : l ≤ 2) (Y : PartId) : Bead run G δ Y l = ∅ := by
  classical
  unfold Bead
  refine biUnion_eq_empty_of (fun a _ => ?_)
  rw [Finset.filter_eq_empty_iff]
  rintro e - ⟨h, u, -, hu, -⟩
  rw [classed_eq_empty_of_le_two run G hl] at hu
  exact Finset.notMem_empty u hu

/-- On a designation, `d_{Y,l}(h) = 0` unless `r(Y) + 2 ≤ l` and `Y` is an ancestor
(s6:thmCONCL (iv) "for other `l`, `m_{Y,l} = 0`"). -/
theorem classDeg_eq_zero_of_not_anc (hδ : IsDesignation run G δ) {l : ℕ} {Y : PartId}
    (hY : ¬ (Y ∈ run.ancestors G ∧ Y.1 + 2 ≤ l)) (h : V) : classDeg run G δ Y l h = 0 := by
  by_cases hl : l ≤ 2
  · exact classDeg_eq_zero_of_le_two run G δ hl Y h
  unfold classDeg
  rw [Finset.card_eq_zero]
  refine biUnion_eq_empty_of (fun a ha => ?_)
  rw [Finset.filter_eq_empty_iff]
  rintro e - ⟨u, hu, -, rfl⟩
  exact hY ⟨hδ.mem_ancestors (by omega) ha hu, hδ.round_add_two_le (by omega) ha hu⟩

theorem mY_eq_zero_of_not_anc (hδ : IsDesignation run G δ) {l : ℕ} {Y : PartId}
    (hY : ¬ (Y ∈ run.ancestors G ∧ Y.1 + 2 ≤ l)) : mY run G δ Y l = 0 := by
  unfold mY; simp [classDeg_eq_zero_of_not_anc run G δ hδ hY]

/-! ### Class degrees -/

theorem classDeg_le_mY {Y : PartId} {l : ℕ} {h : V} (hh : h ∈ G.verts) :
    classDeg run G δ Y l h ≤ mY run G δ Y l :=
  Finset.le_sup (f := classDeg run G δ Y l) hh

theorem mem_classDeg_set {Y : PartId} {l : ℕ} {h : V} {e : Sym2 V} :
    e ∈ (run.Std G l).biUnion (fun a => (run.E G l a).filter
      (fun e => ∃ u ∈ run.classed G l a, e = s(h, u) ∧ δ l u = Y)) ↔
    ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧ ∃ u ∈ run.classed G l a, e = s(h, u) ∧ δ l u = Y := by
  simp only [Finset.mem_biUnion, Finset.mem_filter]

/-- [s6:defDesign] the port-counting form of the class-`Y` degree: at fixed `h`,
`d_{Y,l}(h) = #{u : u a classed port of round l, Y(u) = Y, hu ∈ E_l(Z_u)}` (the map `u ↦ hu` is a
bijection; blueprint DES-COUNT-EDGES-VS-PORTS). -/
theorem classDeg_eq_card_ports (Y : PartId) (l : ℕ) (h : V) :
    classDeg run G δ Y l h = ((classedPorts run G l).filter (fun u => δ l u = Y ∧
      ∃ a ∈ run.Std G l, u ∈ run.classed G l a ∧ s(h, u) ∈ run.E G l a)).card := by
  unfold classDeg
  symm
  refine Finset.card_bij (fun u _ => s(h, u)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter] at hu
    obtain ⟨-, hY, a, ha, hua, he⟩ := hu
    exact (mem_classDeg_set run G δ).2 ⟨a, ha, he, u, hua, rfl, hY⟩
  · intro u _ v _ huv
    exact (Sym2.congr_right.1 huv)
  · intro e he
    obtain ⟨a, ha, he, u, hua, rfl, hY⟩ := (mem_classDeg_set run G δ).1 he
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_filter]
    exact ⟨(mem_classedPorts run G).2 ⟨a, ha, hua⟩, hY, a, ha, hua, he⟩

/-- [s6:defDesign] "`c^agg_{h,l} := #{Y : d_{Y,l}(h) ≥ 1}`": the classes counted by `cAgg` are
exactly the `Y` with `d_{Y,l}(h) ≥ 1`. -/
theorem mem_cAggClasses_iff {h : V} {l : ℕ} {Y : PartId} :
    Y ∈ cAggClasses run G δ h l ↔ 1 ≤ classDeg run G δ Y l h := by
  rw [Nat.one_le_iff_ne_zero, Ne, classDeg, Finset.card_eq_zero, ← Ne,
    ← Finset.nonempty_iff_ne_empty]
  unfold cAggClasses
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨a, ha, hua, he⟩, rfl⟩
    exact ⟨s(h, u), (mem_classDeg_set run G δ).2 ⟨a, ha, he, u, hua, rfl, rfl⟩⟩
  · rintro ⟨e, he⟩
    obtain ⟨a, ha, he, u, hua, rfl, hY⟩ := (mem_classDeg_set run G δ).1 he
    exact ⟨u, ⟨a, ha, hua, he⟩, hY⟩

/-- `γ_l = ⌊P_{l-2}/M_l⌋ = P_{l-2} / M_l` (division in `ℕ`). -/
theorem gammaL_eq_div (l : ℕ) : gammaL run G l = run.P G (l - 2) / run.M G l := by
  unfold gammaL
  exact Nat.floor_div_eq_div _ _

theorem Bead_subset (Y : PartId) (l : ℕ) :
    Bead run G δ Y l ⊆ (run.Std G l).biUnion (run.E G l) := by
  classical
  intro e he
  unfold Bead at he
  simp only [Finset.mem_biUnion, Finset.mem_filter] at he
  obtain ⟨a, ha, he, -⟩ := he
  exact Finset.mem_biUnion.2 ⟨a, ha, he⟩

/-- Positive test of `IsGiant` (design review 2, MINOR-D): if `γ_l = 0`, a single non-loop bead
edge makes `(Y,l)` giant (its component has `1 > 2γ_l` edges). -/
theorem isGiant_of_mem_Bead_of_gammaL_eq_zero {Y : PartId} {l : ℕ} {u v : V}
    (he : s(u, v) ∈ Bead run G δ Y l) (huv : u ≠ v) (hγ : gammaL run G l = 0) :
    IsGiant run G δ Y l := by
  refine ⟨(edgeGraph (Bead run G δ Y l)).connectedComponentMk u, ?_, ?_⟩
  · exact mem_edgeComps.2 ⟨u, mem_edgeVerts.2 ⟨_, he, Sym2.mem_mk_left u v⟩, rfl⟩
  · rw [hγ]
    exact Finset.card_pos.2 ⟨_, mem_compEdges_of_mem he huv⟩

/-- Positive test of `alphaY` (design review 2, MINOR-D): a guest `x ∈ S_Y` adjacent in
`E_l(Z)` to a classed port `u ∈ Q_Z ∩ (V(Y) \ Dup*_r)` of class `Y` gives `α_{Y,l} ≥ 1`. -/
theorem one_le_alphaY {Y : PartId} {l : ℕ} {x u : V} {a : Addr}
    (hx : x ∈ run.guests G Y.1 Y.2) (hu : u ∈ run.ancVerts G Y) (hu' : u ∉ run.DupStar G Y.1)
    (ha : a ∈ run.Std G l) (huc : u ∈ run.classed G l a) (hY : δ l u = Y)
    (he : s(x, u) ∈ run.E G l a) : 1 ≤ alphaY run G δ Y l := by
  classical
  unfold alphaY
  exact Finset.le_sup_of_le hx (Finset.card_pos.2
    ⟨u, Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hu, hu'⟩, a, ha, huc, hY, he⟩⟩)

end EG.Chain
