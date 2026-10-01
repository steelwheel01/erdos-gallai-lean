import EG.Lib.Chain.JConsumer
import EG.Lib.Chain.Constants
import EGTest.HB

/-! Unit tests for `EG.Defs.Chain.Design` ([s6:defDesign]), `EG.Defs.Chain.Lending`
([s6:defLending]), `EG.Defs.Chain.JSet` ([s6:lemJplus]), `EG.Defs.Chain.JConsumer`
([s6:defJconsumer]) and `EG.Defs.Chain.Constants` (`ε_CONC`, `ε_K`, `ε_M`).

* **A run with a classed port.** The three-round run `run3 = ⟨[cA, cA, cA]⟩` on the 5-vertex
  graph `G5` of `EGTest.HB.StandaloneTest`. Round 1 is the example there (pre-parts
  `[false,false] = {0,3}`, `[false,true] = {1,4}`, `[true] = {0,1,2}` standalone, `D_1 = {0,1}`),
  and it assigns every edge, so `G_2 = G_3` is the edgeless graph `Gz` on `Fin 5`. On `Gz` the
  same choices give the same vertex sets (`P = 0`, all leaves are pre-parts), `D_3 = {0,1}`, and
  `[true]` is again standalone (its guests are `{0,1}`). At round 3 the port `2` of `[true]` has
  `anc_3(2) ∋ (1,[true])`, so it is **classed**: `Q_{[true]} = {2}`.
  - a designation (`δ3`) exists and is checked; `dStar`, `classDeg`, `mY`, `Bead`, `cAgg` at
    round 3 (all edges are gone, so the degrees are `0`); `d*`: `2 ∉ Dup*_1`;
  - lending: with good stage data the port `2` is not lost (`Q* = {2}`, `Ret = {0,1}`); with the
    label `lab ≠ *`, or with `COL(b)` failing for its class, it is lost (`Lost = {2}`, `Q* = ∅`,
    `Ret = Z^0`); `O_Z` switches to `X^0_Z` for a lend-bad `Z`; `X_U`;
  - `Lost_l`, `Q*` at `l ≤ 2`.
* **J-interface.** `∅` satisfies `JPlusProps`; a set containing an edge that lies in no `E_l(Z)`
  does not (negative test); at `l ≤ 2` only `∅` does; the trivial J-consumer.
* **Constants.** `ε_M` unfolds; `ε_CONC ≥ 0` at `D_* = 4`. -/

namespace EGTest.Design

open EG EG.HB EG.Chain EGTest.HB EGTest.HB.StandaloneTest

/-! ## Round 3 on the edgeless graph -/

/-- The edgeless graph on `Fin 5`. -/
def Gz : FGraph (Fin 5) := FGraph.ofEdges Finset.univ ∅

theorem Gz_edges : Gz.edges = ∅ := by decide

theorem d_Gz : Round.d Gz = 0 := by simp [Round.d, Gz_edges]

theorem POf_zero : POf 0 = 0 := by simp [POf, lamOf, Cp]

theorem g'z : Round.graph' Gz cA = Gz := by simp [Round.graph', Round.cycEdges, cA]

theorem twoLevelz : Round.twoLevel Gz cA = two := by
  unfold Round.twoLevel
  simp only [d_Gz, POf_zero, Nat.zero_le, if_true]
  rfl

theorem X0z (a : Addr) : Round.X0 Gz cA a = two.graphAtD Gz a := by
  rw [Round.X0, twoLevelz, g'z]

theorem prez : Round.prePartAddrs Gz cA = {[false, false], [false, true], [true]} := by
  unfold Round.prePartAddrs
  rw [twoLevelz, d_Gz, POf_zero]
  simp only [Nat.zero_le, Finset.filter_true]
  decide

theorem Z0z_ff : Round.Z0 Gz cA [false, false] = {0, 3} := by rw [Round.Z0, X0z]; decide
theorem Z0z_ft : Round.Z0 Gz cA [false, true] = {1, 4} := by rw [Round.Z0, X0z]; decide
theorem Z0z_t : Round.Z0 Gz cA [true] = {0, 1, 2} := by rw [Round.Z0, X0z]; decide

theorem Dz : Round.D Gz cA = {0, 1} := by
  ext v
  rw [Round.mem_D]
  simp only [Round.mu, prez]
  fin_cases v <;> simp [Finset.filter_insert, Finset.filter_singleton, Z0z_ff, Z0z_ft, Z0z_t]

theorem homez (v : Fin 5) : Round.home Gz cA v =
    if v = 0 ∨ v = 3 then some [false, false]
    else if v = 1 ∨ v = 4 then some [false, true] else some [true] := by
  unfold Round.home
  rw [prez, show cA.homeOrder = [[false, false], [false, true], [true]] from rfl]
  fin_cases v <;> simp [Z0z_ff, Z0z_ft, Z0z_t]

theorem guestsz_t : Round.guests Gz cA [true] = {0, 1} := by
  unfold Round.guests; rw [Dz, Z0z_t]; simp [homez]

theorem notLightz_t : ¬ Round.isLight Gz cA [true] := fun h => by
  have := h.1
  simp [Round.isL1, guestsz_t, Z0z_t] at this


/-! ## The run `run3 = ⟨[cA, cA, cA]⟩` on `G5` -/

/-- Three rounds with the choices `cA` of `EGTest.HB.StandaloneTest` (not a valid run: only the
definitions are exercised). -/
def run3 : Run (Fin 5) := ⟨[cA, cA, cA]⟩

theorem run3_R : run3.R = 3 := rfl

theorem isRound3 {l : ℕ} (h1 : 1 ≤ l) (h3 : l ≤ 3) : run3.IsRound l := ⟨h1, h3⟩

theorem choice3 {l : ℕ} (h1 : 1 ≤ l) (h3 : l ≤ 3) : run3.choice l = cA := by
  obtain rfl | rfl | rfl : l = 1 ∨ l = 2 ∨ l = 3 := by omega
  all_goals rfl

/-- Round 1 assigns every edge (order A of `EGTest.HB.StandaloneTest`). -/
theorem passedA : Round.passed G5 cA = ∅ := by
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

theorem next_G5 : Round.next G5 cA = Gz :=
  FGraph.ext rfl (by rw [Round.next_edges, passedA, Gz_edges])

theorem next_Gz : Round.next Gz cA = Gz := by
  refine FGraph.ext rfl ?_
  rw [Round.next_edges, Gz_edges]
  exact Finset.subset_empty.1 ((Round.passed_subset Gz cA).trans (by rw [g'z, Gz_edges]))

theorem graph3_one : run3.graph G5 1 = G5 := Run.graph_one run3 G5

theorem graph3_two : run3.graph G5 2 = Gz := by
  rw [Run.graph_succ_of_isRound run3 G5 (isRound3 le_rfl (by norm_num)), graph3_one,
    choice3 le_rfl (by norm_num), next_G5]

theorem graph3_three : run3.graph G5 3 = Gz := by
  rw [Run.graph_succ_of_isRound run3 G5 (isRound3 (by norm_num) (by norm_num)), graph3_two,
    choice3 (by norm_num) (by norm_num), next_Gz]

/-! ### Round-1 and round-3 objects of `run3` -/

theorem pre3_one : run3.prePartAddrs G5 1 = {[false, false], [false, true], [true]} := by
  rw [Run.prePartAddrs_of_isRound run3 G5 (isRound3 le_rfl (by norm_num)), graph3_one,
    choice3 le_rfl (by norm_num), preA]

theorem pre3_three : run3.prePartAddrs G5 3 = {[false, false], [false, true], [true]} := by
  rw [Run.prePartAddrs_of_isRound run3 G5 (isRound3 (by norm_num) le_rfl), graph3_three,
    choice3 (by norm_num) le_rfl, prez]

theorem partVerts3_one (a : Addr) : run3.partVerts G5 1 a = Round.partVerts G5 cA a := by
  rw [Run.partVerts, graph3_one, choice3 le_rfl (by norm_num)]

theorem Z03_three (a : Addr) : run3.Z0 G5 3 a = Round.Z0 Gz cA a := by
  rw [Run.Z0, graph3_three, choice3 (by norm_num) le_rfl]

theorem D3_three : run3.D G5 3 = {0, 1} := by
  rw [Run.D, if_pos (isRound3 (by norm_num) le_rfl), graph3_three, choice3 (by norm_num) le_rfl,
    Dz]

theorem D3_one : run3.D G5 1 = {0, 1} := by
  rw [Run.D, if_pos (isRound3 le_rfl (by norm_num)), graph3_one, choice3 le_rfl (by norm_num), DA]

theorem DupStar3_one : run3.DupStar G5 1 = {0, 1} := by
  rw [Run.DupStar, if_pos (isRound3 le_rfl (by norm_num)), graph3_one,
    choice3 le_rfl (by norm_num), Round.DupStar, twoLevelA, g'A]
  decide

theorem E3_three (a : Addr) : run3.E G5 3 a = ∅ := by
  refine Finset.subset_empty.1 ((Run.E_subset_graph'_edges run3 G5 3 a).trans ?_)
  rw [Run.graph', graph3_three, choice3 (by norm_num) le_rfl, g'z, Gz_edges]

/-- `[true]` is standalone at round 3. -/
theorem t_mem_Std3 : [true] ∈ run3.Std G5 3 := by
  rw [Run.mem_Std_iff, pre3_three]
  refine ⟨by simp, ?_⟩
  rw [Run.isLight, graph3_three, choice3 (by norm_num) le_rfl]
  exact notLightz_t

/-- The round-1 pre-part `[true]` is an ancestor with `V = {0,1,2}` (standalone). -/
theorem mem_anc3 {u : Fin 5} {b : Addr} (hb : b ∈ ({[false, false], [false, true], [true]} :
    Finset Addr)) (hu : u ∈ Round.partVerts G5 cA b) : ((1, b) : PartId) ∈ run3.anc G5 3 u := by
  rw [Run.mem_anc, Run.mem_ancestors]
  refine ⟨by rw [pre3_one]; exact hb, le_rfl, ?_⟩
  rw [Run.ancVerts, partVerts3_one]
  exact hu

theorem ports3_t : run3.ports G5 3 [true] = {2} := by
  unfold Run.ports; rw [Z03_three, Z0z_t, D3_three]; decide

/-- **The port `2` of `[true]` is classed at round 3**: `Q_{[true]} = {2}`. -/
theorem classed3_t : run3.classed G5 3 [true] = {2} := by
  have h2 : run3.anc G5 3 2 ≠ ∅ :=
    Finset.ne_empty_of_mem (mem_anc3 (b := [true]) (by simp) (by rw [partVertsA_t]; decide))
  unfold Run.classed Run.fresh
  rw [ports3_t]
  ext u
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, fun h => h2 h.2⟩

/-! ### A designation -/

/-- `Y(3) = [false,false]`, `Y(4) = [false,true]`, all other classes `[true]` (round 1). -/
def δ3 : Designation (Fin 5) := fun _ u =>
  if u = 3 then (1, [false, false]) else if u = 4 then (1, [false, true]) else (1, [true])

theorem δ3_isDesignation : IsDesignation run3 G5 δ3 := by
  intro l hl a ha u hu
  have hR : l ≤ 3 := by
    by_contra h
    rw [Run.Std_of_not_isRound run3 G5 (fun hr => h hr.2)] at ha
    exact Finset.notMem_empty a ha
  obtain rfl : l = 3 := by omega
  have hpre := Std_subset_prePartAddrs run3 G5 3 ha
  rw [pre3_three] at hpre
  have hp := (mem_ports_iff run3 G5).1 (classed_subset_ports run3 G5 3 a hu)
  rw [Z03_three, D3_three] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpre
  rcases hpre with rfl | rfl | rfl
  · rw [Z0z_ff] at hp
    have key : ∀ v : Fin 5, v ∈ ({0, 3} : Finset (Fin 5)) ∧ v ∉ ({0, 1} : Finset (Fin 5)) →
        v = 3 := by decide
    obtain rfl := key u hp
    exact mem_anc3 (by simp) (by rw [partVertsA_ff]; decide)
  · rw [Z0z_ft] at hp
    have key : ∀ v : Fin 5, v ∈ ({1, 4} : Finset (Fin 5)) ∧ v ∉ ({0, 1} : Finset (Fin 5)) →
        v = 4 := by decide
    obtain rfl := key u hp
    exact mem_anc3 (by simp) (by rw [partVertsA_ft]; decide)
  · rw [Z0z_t] at hp
    have key : ∀ v : Fin 5, v ∈ ({0, 1, 2} : Finset (Fin 5)) ∧ v ∉ ({0, 1} : Finset (Fin 5)) →
        v = 2 := by decide
    obtain rfl := key u hp
    exact mem_anc3 (by simp) (by rw [partVertsA_t]; decide)

/-- `2` is a classed port of round 3 (of the standalone `[true]`). -/
example : 2 ∈ classedPorts run3 G5 3 :=
  (mem_classedPorts run3 G5).2 ⟨[true], t_mem_Std3, by rw [classed3_t]; simp⟩

/-- `u ∈ V(Y(u))` and `r(Y(u)) + 2 ≤ l` on the designation. -/
example : 2 ∈ run3.ancVerts G5 (δ3 3 2) ∧ (δ3 3 2).1 + 2 ≤ 3 :=
  ⟨δ3_isDesignation.mem_ancVerts le_rfl t_mem_Std3 (by rw [classed3_t]; simp),
    δ3_isDesignation.round_add_two_le le_rfl t_mem_Std3 (by rw [classed3_t]; simp)⟩

/-- `d*_{Y,3} = 0`: classed ports lie outside `D_3 = {0,1} = Dup*_1`. -/
example : dStar run3 G5 δ3 (1, [true]) 3 = 0 := by
  unfold dStar
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro u hu ⟨-, hD⟩
  obtain ⟨a, -, hua⟩ := (mem_classedPorts run3 G5).1 hu
  apply not_mem_D_of_mem_ports run3 G5 (classed_subset_ports run3 G5 3 a hua)
  rw [D3_three]; rw [DupStar3_one] at hD; exact hD

/-- All edges are gone at round 3: `d_{Y,3} = m_{Y,3} = 0`, `Bead_{Y,3} = ∅`, `c^agg = 0`. -/
example (Y : PartId) (h : Fin 5) : classDeg run3 G5 δ3 Y 3 h = 0 := by
  unfold classDeg
  rw [biUnion_eq_empty_of (fun a _ => by rw [E3_three]; rfl), Finset.card_empty]

example (Y : PartId) : Bead run3 G5 δ3 Y 3 = ∅ := by
  classical
  refine Finset.subset_empty.1 ((Bead_subset run3 G5 δ3 Y 3).trans ?_)
  rw [biUnion_eq_empty_of (fun a _ => E3_three a)]

example (Y : PartId) : ¬ IsGiant run3 G5 δ3 Y 3 := by
  classical
  rintro ⟨C, hC, -⟩
  have hB : Bead run3 G5 δ3 Y 3 = ∅ :=
    Finset.subset_empty.1 ((Bead_subset run3 G5 δ3 Y 3).trans
      (by rw [biUnion_eq_empty_of (fun a _ => E3_three a)]))
  unfold edgeComps at hC
  obtain ⟨v, hv, -⟩ := Finset.mem_image.1 hC
  unfold edgeVerts at hv
  rw [hB] at hv
  simp at hv

/-- The class data vanish for `l ≤ 2`. -/
example : mY run3 G5 δ3 (1, [true]) 2 = 0 := mY_eq_zero_of_le_two run3 G5 δ3 (by norm_num) _


/-! ## Lending -/

/-- Stage data in which every ancestor is lend-good and every label is `*`. -/
def Sgood : StageData (Fin 5) where
  colA _ := True
  colB _ := True
  demoted _ := False
  lab _ _ _ := none
  own _ := ∅
  ljs _ _ _ := ∅
  ljv _ _ := ∅
  dem := 7
  lp := 5

/-- As `Sgood`, but every JS label is `0` (`≠ *`). -/
def Slab : StageData (Fin 5) := { Sgood with lab := fun _ _ _ => some 0 }

/-- As `Sgood`, but COL(b) fails for the round-1 ancestor `[true]` (and for nothing else). -/
def Sbad : StageData (Fin 5) := { Sgood with colB := fun Y => Y ≠ (1, [true]) }

theorem lendBad_Sgood (Y : PartId) : ¬ lendBad run3 G5 Sgood Y := by
  simp [lendBad, Sgood]

theorem lendBad_Sbad : lendBad run3 G5 Sbad (1, [true]) := by
  simp [lendBad, Sbad]

theorem lost_Sgood (a : Addr) : lost run3 G5 δ3 Sgood 3 a = ∅ := by
  classical
  ext u
  rw [mem_lost_iff run3 G5 δ3 Sgood le_rfl]
  simp only [lendBad_Sgood, false_or, Finset.notMem_empty, iff_false, not_and]
  intro _
  simp [Sgood]

/-- Good stage data: the classed port `2` is not lost: `Q* = {2}`, `Ret = A ∪ F = {0,1}`. -/
example : qs run3 G5 δ3 Sgood 3 [true] = {2} := by
  rw [qs, lost_Sgood, classed3_t, Finset.sdiff_empty]

example : ret run3 G5 δ3 Sgood 3 [true] = {0, 1} := by
  have hf : run3.fresh G5 3 [true] = ∅ := by
    have := disjoint_fresh_classed run3 G5 3 [true]
    rw [classed3_t] at this
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    have hp := fresh_subset_ports run3 G5 3 [true] hu
    rw [ports3_t, Finset.mem_singleton] at hp
    subst hp
    exact Finset.disjoint_left.1 this hu (Finset.mem_singleton_self 2)
  rw [ret, lost_Sgood, hf, Finset.union_empty, Finset.union_empty]
  unfold Run.hubs; rw [Z03_three, Z0z_t, D3_three]; decide

/-- The class of `2` is a lend-good ancestor, and `2 ∉ T_j(Y(2), 3)`. -/
example : δ3 3 2 ∈ lendGoodAnc run3 G5 Sgood 3 :=
  mem_lendGoodAnc_of_mem_qs run3 G5 Sgood δ3_isDesignation t_mem_Std3
    (by rw [qs, lost_Sgood, classed3_t]; simp)

/-- A label `≠ *` makes the port lost: `Lost = {2}`, `Q* = ∅`, `Ret = Z^0`. -/
theorem lost_Slab : lost run3 G5 δ3 Slab 3 [true] = {2} := by
  classical
  ext u
  rw [mem_lost_iff run3 G5 δ3 Slab le_rfl, classed3_t]
  simp [Slab]

example : qs run3 G5 δ3 Slab 3 [true] = ∅ := by
  rw [qs, lost_Slab, classed3_t, Finset.sdiff_self]

example : ret run3 G5 δ3 Slab 3 [true] = run3.Z0 G5 3 [true] := by
  rw [← ret_union_qs run3 G5 δ3 Slab 3 [true], qs, lost_Slab, classed3_t, Finset.sdiff_self,
    Finset.union_empty]

/-- A lend-bad class (COL(b) fails) makes the port lost. -/
example : lost run3 G5 δ3 Sbad 3 [true] = {2} := by
  classical
  ext u
  rw [mem_lost_iff run3 G5 δ3 Sbad le_rfl, classed3_t]
  simp only [Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl
    exact ⟨rfl, Or.inl (by simpa [δ3] using lendBad_Sbad)⟩

/-- `O_Z` is `X^0_Z` for a lend-bad `Z`, and `Own_Z` (as a graph on `Z^0`) for a lend-good one. -/
example : OZ run3 G5 { Sgood with colA := fun _ => False } 3 [true] = run3.X0 G5 3 [true] :=
  OZ_of_lendBad run3 G5 _ (by simp [lendBad])

example : (OZ run3 G5 Sgood 3 [true]).edges = ∅ := by
  rw [OZ_of_not_lendBad run3 G5 Sgood (lendBad_Sgood _)]
  rfl

/-- `X_U = 80 dem + 369 lp` when nothing is lost. -/
example : XU run3 G5 δ3 Sgood = 80 * 7 + 369 * 5 := by
  have h : ∀ l, lostRound run3 G5 δ3 Sgood l = ∅ := by
    intro l
    by_cases hl : l ≤ 2
    · exact lostRound_of_le_two run3 G5 δ3 Sgood hl
    · refine biUnion_eq_empty_of (fun a _ => ?_)
      classical
      ext u
      rw [mem_lost_iff run3 G5 δ3 Sgood (by omega)]
      simp only [lendBad_Sgood, false_or, Finset.notMem_empty, iff_false, not_and]
      intro _
      simp [Sgood]
  rw [XU]
  simp only [h, Finset.card_empty, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- For `l ≤ 2` nothing is lost and there are no non-lost classed ports. -/
example (a : Addr) : lost run3 G5 δ3 Slab 1 a = ∅ ∧ qs run3 G5 δ3 Slab 1 a = ∅ :=
  ⟨lost_of_le_two run3 G5 δ3 Slab (by norm_num) a, qs_of_le_two run3 G5 δ3 Slab (by norm_num) a⟩

/-! ## The J-interface and J-consumers -/

/-- Non-vacuity: `∅` satisfies `JPlusProps`. -/
example : JPlusProps run3 G5 δ3 Sgood 3 ∅ := jPlusProps_empty run3 G5 δ3 Sgood 3

/-- Negative test: an edge that lies in no `E_3(Z)` cannot be a J-edge. -/
example : ¬ JPlusProps run3 G5 δ3 Sgood 3 {s(0, 2)} := by
  intro hJ
  obtain ⟨a, -, ha⟩ := hJ.exists_mem_E (Finset.mem_singleton_self _)
  rw [E3_three] at ha
  exact Finset.notMem_empty _ ha

/-- For `l ≤ 2` only `∅` satisfies `JPlusProps`. -/
example (J : Finset (Sym2 (Fin 5))) (hJ : JPlusProps run3 G5 δ3 Sgood 2 J) : J = ∅ :=
  hJ.eq_empty_of_le_two (by norm_num)

/-- (s6:eqJbound): the bound vanishes at `l = 1`. -/
example : jBound run3 G5 δ3 Sgood 1 = 0 := jBound_of_le_two run3 G5 δ3 Sgood (by norm_num)

/-- The trivial J-consumer outputs the edges of `J` as single edges and lends nothing. -/
example : (trivialConsumer run3 G5 δ3 Sgood).out 3 ∅ = ([], ∅) := by
  simp [trivialConsumer]

example : Nonempty (JConsumer run3 G5 δ3 Sgood) := nonempty_jConsumer run3 G5 δ3 Sgood

/-! ## Constants -/

example (D : ℝ) : epsM D = epsK D + 169 * HB.epsA D + 252 / D := epsM_eq D

example : 0 ≤ epsCONC 4 := epsCONC_nonneg le_rfl

/-- The parse of `ε_CONC` (all parentheses explicit; `σ + 15 = 115`, `ε = 2^{-5}`, `C' = 103`). -/
example (D : ℝ) : epsCONC D =
    ((2 : ℝ) ^ (115 : ℕ) * (logStar D : ℝ)) / Real.logb 2 D
      + (200 * (2 : ℝ) ^ (-5 : ℤ) * (logStar D : ℝ)) / (((103 : ℕ) : ℝ) * Real.logb 2 (Real.logb 2 D))
      + (4 * (2 * (logStar D : ℝ) + 2)) / ((Real.logb 2 D) ^ ((1 : ℝ) / 2)) := rfl

/-- The parse of `ε_K = ε_ch` (`A = 105`). -/
example (D : ℝ) : epsK D =
    614 / D + Real.logb 2 (2 * ((105 : ℕ) : ℝ) * Real.logb 2 (((105 : ℕ) : ℝ) *
      Real.logb 2 (Real.logb 2 D))) / (371 * (Real.logb 2 (Real.logb 2 D)) ^ 2) := rfl

end EGTest.Design
