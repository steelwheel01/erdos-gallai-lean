module

public import EG.Defs.Chain.Lending
public import EG.Lib.Chain.Design
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lending statuses and lost ports: basic API (companion of `EG.Defs.Chain.Lending`)

* the case `l ≤ 2` of s6:defLending ("For `l ≤ 2` put `Lost_Z := ∅`, `Ret_Z := A_Z ∪ F_Z = Z^0` and
  `Q*_Z := ∅`"): `lost_of_le_two`, `qs_of_le_two`, `ret_of_le_two`;
* "`Z^0 = Ret_Z ⊔ Q*_Z`, and `A_Z, F_Z, Lost_Z` are pairwise disjoint": `ret_union_qs`,
  `disjoint_ret_qs`, `disjoint_hubs_fresh`, `disjoint_hubs_lost`, `disjoint_fresh_lost`;
* "For every classed port `u ∈ Q*_Z`, the class `Y(u)` is lend-good and
  `u ∉ ⋃_j T_j(Y(u), l)`": `not_lendBad_of_mem_qs`, `lab_eq_none_of_mem_qs`,
  `notMem_Tj_of_mem_qs`, and (on a designation) `mem_lendGoodAnc_of_mem_qs`; the junction sets
  `T_j(Y,l)` of distinct `j` are disjoint (`Tj_disjoint`);
* `O_Z` is a graph on `Z^0` (`OZ_verts`);
* `|Lost_l| = Σ_{Z ∈ Std_l} |Lost_Z|` (`card_lostRound`; the `Lost_Z` of one round are disjoint);
* (J3) of s6:lemJplus, which does not mention `J_l`: the role sets `D_l`, `⋃_Z F_Z`,
  `⋃_Z Q*_Z` (and `Lost_l`) of one round are pairwise disjoint, for every run
  (`disjoint_D_freshCentres`, `disjoint_D_qsRound`, `disjoint_freshCentres_qsRound`,
  `disjoint_D_lostRound`, `disjoint_freshCentres_lostRound`, `disjoint_qsRound_lostRound`).
-/

public section

namespace EG.Chain

open EG.HB

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

/-! ### Lost, retired and non-lost ports of one part -/

theorem lost_of_le_two {l : ℕ} (hl : l ≤ 2) (a : Addr) : lost run G δ S l a = ∅ := by
  unfold lost; rw [if_neg (by omega)]

theorem mem_lost_iff {l : ℕ} (hl : 3 ≤ l) {a : Addr} {u : V} :
    u ∈ lost run G δ S l a ↔ u ∈ run.classed G l a ∧
      (lendBad run G S (δ l u) ∨ S.lab (δ l u) l u ≠ none) := by
  classical
  unfold lost; rw [if_pos hl, Finset.mem_filter]

theorem lost_subset_classed (l : ℕ) (a : Addr) : lost run G δ S l a ⊆ run.classed G l a := by
  classical
  unfold lost
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem qs_subset_classed (l : ℕ) (a : Addr) : qs run G δ S l a ⊆ run.classed G l a :=
  Finset.sdiff_subset

theorem mem_qs_iff' {l : ℕ} {a : Addr} {u : V} :
    u ∈ qs run G δ S l a ↔ u ∈ run.classed G l a ∧ u ∉ lost run G δ S l a := by
  unfold qs; rw [Finset.mem_sdiff]

theorem mem_qs_iff {l : ℕ} (hl : 3 ≤ l) {a : Addr} {u : V} :
    u ∈ qs run G δ S l a ↔ u ∈ run.classed G l a ∧ ¬ lendBad run G S (δ l u) ∧
      S.lab (δ l u) l u = none := by
  rw [mem_qs_iff', mem_lost_iff run G δ S hl]
  tauto

/-- [s6:defLending] "For `l ≤ 2` put … `Q*_Z := ∅`". -/
theorem qs_of_le_two {l : ℕ} (hl : l ≤ 2) (a : Addr) : qs run G δ S l a = ∅ := by
  unfold qs; rw [classed_eq_empty_of_le_two run G hl, Finset.empty_sdiff]

/-- [s6:defLending] "For `l ≤ 2` put … `Ret_Z := A_Z ∪ F_Z = Z^0`". -/
theorem ret_of_le_two {l : ℕ} (hl : l ≤ 2) (a : Addr) : ret run G δ S l a = run.Z0 G l a := by
  unfold ret
  rw [lost_of_le_two run G δ S hl, Finset.union_empty, Run.fresh_eq_ports_of_le_two run G hl]
  unfold Run.hubs Run.ports
  rw [Finset.union_comm]
  exact Finset.sdiff_union_inter _ _

theorem three_le_of_mem_qs {l : ℕ} {a : Addr} {u : V} (hu : u ∈ qs run G δ S l a) : 3 ≤ l := by
  by_contra hl
  rw [qs_of_le_two run G δ S (by omega)] at hu
  exact Finset.notMem_empty u hu

/-- [s6:defLending] "For every classed port `u ∈ Q*_Z`, the class `Y(u)` is lend-good". -/
theorem not_lendBad_of_mem_qs {l : ℕ} {a : Addr} {u : V} (hu : u ∈ qs run G δ S l a) :
    ¬ lendBad run G S (δ l u) :=
  ((mem_qs_iff run G δ S (three_le_of_mem_qs run G δ S hu)).1 hu).2.1

/-- [s6:defLending] for `u ∈ Q*_Z`, `lab_{Y(u),l}(u) = *`. -/
theorem lab_eq_none_of_mem_qs {l : ℕ} {a : Addr} {u : V} (hu : u ∈ qs run G δ S l a) :
    S.lab (δ l u) l u = none :=
  ((mem_qs_iff run G δ S (three_le_of_mem_qs run G δ S hu)).1 hu).2.2

/-- [s6:defLending] "For every classed port `u ∈ Q*_Z`, … `u ∉ ⋃_j T_j(Y(u), l)`". -/
theorem notMem_Tj_of_mem_qs {l : ℕ} {a : Addr} {u : V} (hu : u ∈ qs run G δ S l a) (j : ℕ) :
    u ∉ Tj run G S (δ l u) l j := by
  intro h
  unfold Tj at h
  rw [Finset.mem_filter, lab_eq_none_of_mem_qs run G δ S hu] at h
  exact absurd h.2 (by simp)

/-- The junction sets `T_j(Y,l)`, `j ≠ j'`, are disjoint on every record (the label is a
function; used by JS-LC Step 7; design review 2, Check F). -/
theorem Tj_disjoint (Y : PartId) (l : ℕ) {j j' : ℕ} (hjj : j ≠ j') :
    Disjoint (Tj run G S Y l j) (Tj run G S Y l j') := by
  classical
  rw [Finset.disjoint_left]
  intro y h1 h2
  unfold Tj at h1 h2
  rw [Finset.mem_filter] at h1 h2
  rw [h1.2] at h2
  exact hjj (Option.some_injective _ h2.2)

/-- On a designation, the class of a non-lost port is a lend-good ancestor of a round `≤ l − 2`. -/
theorem mem_lendGoodAnc_of_mem_qs {δ} (hδ : IsDesignation run G δ) {l : ℕ} {a : Addr}
    (ha : a ∈ run.Std G l) {u : V} (hu : u ∈ qs run G δ S l a) :
    δ l u ∈ lendGoodAnc run G S l := by
  classical
  have hl := three_le_of_mem_qs run G δ S hu
  have huc := qs_subset_classed run G δ S l a hu
  unfold lendGoodAnc
  rw [Finset.mem_filter]
  exact ⟨hδ.mem_ancestors hl ha huc, hδ.round_add_two_le hl ha huc,
    not_lendBad_of_mem_qs run G δ S hu⟩

/-- [s6:defLending] "we have `Z^0 = Ret_Z ⊔ Q*_Z`" (union part). -/
theorem ret_union_qs (l : ℕ) (a : Addr) :
    ret run G δ S l a ∪ qs run G δ S l a = run.Z0 G l a := by
  ext u
  have hlc := @lost_subset_classed _ _ run G δ S l a u
  simp only [ret, Finset.mem_union, mem_qs_iff', mem_hubs_iff, mem_fresh_iff, mem_classed_iff,
    mem_ports_iff] at hlc ⊢
  by_cases hD : u ∈ run.D G l <;> by_cases hA : run.anc G l u = ∅ <;>
    by_cases hL : u ∈ lost run G δ S l a <;> simp_all

/-- [s6:defLending] "we have `Z^0 = Ret_Z ⊔ Q*_Z`" (disjointness part). -/
theorem disjoint_ret_qs (l : ℕ) (a : Addr) :
    Disjoint (ret run G δ S l a) (qs run G δ S l a) := by
  rw [Finset.disjoint_left]
  intro u hr hq
  rw [mem_qs_iff'] at hq
  have hq' := mem_classed_iff run G |>.1 hq.1
  simp only [ret, Finset.mem_union] at hr
  rcases hr with (hh | hf) | hl
  · exact not_mem_D_of_mem_ports run G hq'.1 (hubs_subset_D run G l a hh)
  · exact Finset.disjoint_left.1 (disjoint_fresh_classed run G l a) hf hq.1
  · exact hq.2 hl

theorem disjoint_hubs_ports (l : ℕ) (a b : Addr) :
    Disjoint (run.hubs G l a) (run.ports G l b) := by
  rw [Finset.disjoint_left]
  intro u hh hp
  exact not_mem_D_of_mem_ports run G hp (hubs_subset_D run G l a hh)

/-- [s6:defLending] "`A_Z, F_Z, Lost_Z` are pairwise disjoint" (`A_Z`, `F_Z`). -/
theorem disjoint_hubs_fresh (l : ℕ) (a : Addr) : Disjoint (run.hubs G l a) (run.fresh G l a) :=
  Finset.disjoint_of_subset_right (fresh_subset_ports run G l a) (disjoint_hubs_ports run G l a a)

/-- [s6:defLending] "`A_Z, F_Z, Lost_Z` are pairwise disjoint" (`A_Z`, `Lost_Z`). -/
theorem disjoint_hubs_lost (l : ℕ) (a : Addr) :
    Disjoint (run.hubs G l a) (lost run G δ S l a) :=
  Finset.disjoint_of_subset_right
    ((lost_subset_classed run G δ S l a).trans (classed_subset_ports run G l a))
    (disjoint_hubs_ports run G l a a)

/-- [s6:defLending] "`A_Z, F_Z, Lost_Z` are pairwise disjoint" (`F_Z`, `Lost_Z`). -/
theorem disjoint_fresh_lost (l : ℕ) (a : Addr) :
    Disjoint (run.fresh G l a) (lost run G δ S l a) :=
  Finset.disjoint_of_subset_right (lost_subset_classed run G δ S l a)
    (disjoint_fresh_classed run G l a)

theorem disjoint_lost_qs (l : ℕ) (a : Addr) : Disjoint (lost run G δ S l a) (qs run G δ S l a) :=
  Finset.disjoint_sdiff

/-! ### `O_Z` -/

theorem OZ_of_lendBad {l : ℕ} {a : Addr} (h : lendBad run G S (l, a)) :
    OZ run G S l a = run.X0 G l a := by
  classical
  unfold OZ; rw [if_pos h]

theorem OZ_of_not_lendBad {l : ℕ} {a : Addr} (h : ¬ lendBad run G S (l, a)) :
    OZ run G S l a = FGraph.ofEdges (run.Z0 G l a) (S.own (l, a)) := by
  classical
  unfold OZ; rw [if_neg h]

/-- `O_Z` is a graph on `Z^0`. -/
@[simp] theorem OZ_verts (l : ℕ) (a : Addr) : (OZ run G S l a).verts = run.Z0 G l a := by
  classical
  unfold OZ
  split_ifs <;> rfl

/-! ### `Lost_l` and the role sets of a round -/

theorem mem_lostRound {l : ℕ} {u : V} :
    u ∈ lostRound run G δ S l ↔ ∃ a ∈ run.Std G l, u ∈ lost run G δ S l a := by
  unfold lostRound; rw [Finset.mem_biUnion]

theorem mem_freshCentres {l : ℕ} {u : V} :
    u ∈ freshCentres run G l ↔ ∃ a ∈ run.Std G l, u ∈ run.fresh G l a := by
  unfold freshCentres; rw [Finset.mem_biUnion]

theorem mem_qsRound {l : ℕ} {u : V} :
    u ∈ qsRound run G δ S l ↔ ∃ a ∈ run.Std G l, u ∈ qs run G δ S l a := by
  unfold qsRound; rw [Finset.mem_biUnion]

theorem lostRound_of_le_two {l : ℕ} (hl : l ≤ 2) : lostRound run G δ S l = ∅ :=
  biUnion_eq_empty_of (fun a _ => lost_of_le_two run G δ S hl a)

theorem qsRound_of_le_two {l : ℕ} (hl : l ≤ 2) : qsRound run G δ S l = ∅ :=
  biUnion_eq_empty_of (fun a _ => qs_of_le_two run G δ S hl a)

/-- `|Lost_l| = Σ_{Z ∈ Std_l} |Lost_Z|` (the `Lost_Z ⊆ U_Z` of one round are disjoint). -/
theorem card_lostRound (l : ℕ) :
    (lostRound run G δ S l).card = ∑ a ∈ run.Std G l, (lost run G δ S l a).card := by
  unfold lostRound
  refine Finset.card_biUnion (fun a ha b hb hab => ?_)
  exact Finset.disjoint_of_subset_left (lost_subset_classed run G δ S l a)
    (Finset.disjoint_of_subset_right (lost_subset_classed run G δ S l b)
      (classed_disjoint run G (Std_subset_prePartAddrs run G l ha)
        (Std_subset_prePartAddrs run G l hb) hab))

/-- (J3) `D_l` (hubs) and `⋃_Z F_Z` (fresh centres) are disjoint. -/
theorem disjoint_D_freshCentres (l : ℕ) : Disjoint (run.D G l) (freshCentres run G l) := by
  rw [Finset.disjoint_left]
  intro u hD hf
  obtain ⟨a, -, hf⟩ := (mem_freshCentres run G).1 hf
  exact not_mem_D_of_mem_ports run G (fresh_subset_ports run G l a hf) hD

/-- (J3) `D_l` (hubs) and `⋃_Z Q*_Z` (classed non-lost ports) are disjoint. -/
theorem disjoint_D_qsRound (l : ℕ) : Disjoint (run.D G l) (qsRound run G δ S l) := by
  rw [Finset.disjoint_left]
  intro u hD hq
  obtain ⟨a, -, hq⟩ := (mem_qsRound run G δ S).1 hq
  exact not_mem_D_of_mem_ports run G
    (classed_subset_ports run G l a (qs_subset_classed run G δ S l a hq)) hD

/-- `D_l` and the lost centres `Lost_l` are disjoint. -/
theorem disjoint_D_lostRound (l : ℕ) : Disjoint (run.D G l) (lostRound run G δ S l) := by
  rw [Finset.disjoint_left]
  intro u hD hq
  obtain ⟨a, -, hq⟩ := (mem_lostRound run G δ S).1 hq
  exact not_mem_D_of_mem_ports run G
    (classed_subset_ports run G l a (lost_subset_classed run G δ S l a hq)) hD

/-- Two ports of round `l` lying in `U_Z` and `U_{Z'}` of standalone pre-parts: `Z = Z'`. -/
theorem eq_of_mem_ports {l : ℕ} {a b : Addr} (ha : a ∈ run.Std G l) (hb : b ∈ run.Std G l)
    {u : V} (hua : u ∈ run.ports G l a) (hub : u ∈ run.ports G l b) : a = b :=
  eq_of_mem_Z0_of_notMem_D run G (Std_subset_prePartAddrs run G l ha)
    (Std_subset_prePartAddrs run G l hb) (ports_subset_Z0 run G l a hua)
    (ports_subset_Z0 run G l b hub) (not_mem_D_of_mem_ports run G hua)

/-- (J3) `⋃_Z F_Z` (fresh centres) and `⋃_Z Q*_Z` (classed non-lost ports) are disjoint. -/
theorem disjoint_freshCentres_qsRound (l : ℕ) :
    Disjoint (freshCentres run G l) (qsRound run G δ S l) := by
  rw [Finset.disjoint_left]
  intro u hf hq
  obtain ⟨a, ha, hf⟩ := (mem_freshCentres run G).1 hf
  obtain ⟨b, hb, hq⟩ := (mem_qsRound run G δ S).1 hq
  have hqc := qs_subset_classed run G δ S l b hq
  obtain rfl := eq_of_mem_ports run G ha hb (fresh_subset_ports run G l a hf)
    (classed_subset_ports run G l b hqc)
  exact Finset.disjoint_left.1 (disjoint_fresh_classed run G l a) hf hqc

/-- The fresh centres and the lost centres of round `l` are disjoint. -/
theorem disjoint_freshCentres_lostRound (l : ℕ) :
    Disjoint (freshCentres run G l) (lostRound run G δ S l) := by
  rw [Finset.disjoint_left]
  intro u hf hq
  obtain ⟨a, ha, hf⟩ := (mem_freshCentres run G).1 hf
  obtain ⟨b, hb, hq⟩ := (mem_lostRound run G δ S).1 hq
  have hqc := lost_subset_classed run G δ S l b hq
  obtain rfl := eq_of_mem_ports run G ha hb (fresh_subset_ports run G l a hf)
    (classed_subset_ports run G l b hqc)
  exact Finset.disjoint_left.1 (disjoint_fresh_classed run G l a) hf hqc

/-- The classed non-lost ports and the lost centres of round `l` are disjoint. -/
theorem disjoint_qsRound_lostRound (l : ℕ) :
    Disjoint (qsRound run G δ S l) (lostRound run G δ S l) := by
  rw [Finset.disjoint_left]
  intro u hq hL
  obtain ⟨a, ha, hq⟩ := (mem_qsRound run G δ S).1 hq
  obtain ⟨b, hb, hL⟩ := (mem_lostRound run G δ S).1 hL
  obtain rfl := eq_of_mem_classed run G ha hb (qs_subset_classed run G δ S l a hq)
    (lost_subset_classed run G δ S l b hL)
  exact Finset.disjoint_left.1 (disjoint_lost_qs run G δ S l a) hL hq

end EG.Chain
