module

public import EG.Lib.HB.Run
public import EG.Lib.HB.SEP

/-!
# Rule GC: round-level lemmas (manuscript s2:lemGC (ii), (iii))

Unit P3A, proof round 1.

For a valid round (`Round.Valid H c`):
* `Round.assign_ne_none_of_not_isLight`: an edge with both ends in `Z^0` of a standalone
  pre-part `Z` is assigned ((R5) step (3), or an earlier step);
* `Round.assign_eq_of_mem_X0`: an edge of `X^0_Z` of a standalone pre-part is assigned to `Z`
  ((R5) step (1): the leaf graphs of the two-level recursion are edge-disjoint, SEP (i));
* `Round.D_subset_DupStar`: `D_l ⊆ Dup*_l` (pre-parts are distinct leaves);
* `Round.guests_subset_D`;
* `Round.assign_ne_none_of_mem_partVerts`: an edge with both ends in `V(Z)` of any pre-part `Z`
  (light or standalone) is assigned ((R5) steps (2), (3)); this gives Lemma EL
  (`EG.edgeLaminarity`, `EG/Proof/HB/EL.lean`).

These do not use Lemma EL: "no edge of `G_{l+1}` has both ends in `Z^0`" follows from the first
item, since `E(G_{l+1})` is the set of edges of `G'_l` that are not assigned.
-/

public section

namespace EG.HB

variable {V : Type*} [DecidableEq V]

namespace Round

variable {H : FGraph V} {c : RoundChoice V}

theorem mem_homeOrder_of_valid (hv : Valid H c) {a : Addr} (ha : a ∈ prePartAddrs H c) :
    a ∈ c.homeOrder := by
  rw [← List.mem_toFinset, hv.2.2.2.2.2]
  exact ha

theorem partGraph_of_not_isLight {a : Addr} (hl : ¬ isLight H c a) :
    partGraph H c a = X0 H c a := by
  classical
  unfold partGraph
  rw [if_neg hl]

theorem partVerts_of_not_isLight {a : Addr} (hl : ¬ isLight H c a) :
    partVerts H c a = Z0 H c a := by
  classical
  unfold partVerts
  rw [if_neg hl]

/-- (R5) An edge with both ends in `Z^0` of a standalone pre-part `Z` is assigned. -/
theorem assign_ne_none_of_not_isLight (hv : Valid H c) {a : Addr} (ha : a ∈ prePartAddrs H c)
    (hl : ¬ isLight H c a) {e : Sym2 V} (he : e ∈ (Z0 H c a).sym2) : assign H c e ≠ none := by
  classical
  unfold assign
  rw [Ne, Option.or_eq_none_iff, Option.or_eq_none_iff, List.find?_eq_none]
  rintro ⟨-, -, h3⟩
  rw [List.find?_eq_none] at h3
  apply h3 a (mem_homeOrder_of_valid hv ha)
  simp only [decide_eq_true_eq]
  exact ⟨ha, hl, he⟩

/-- (R5) steps (2), (3): an edge with both ends in the part vertex set `V(Z)` of a pre-part `Z`
(`Z^0 \ S_Z` if light, `Z^0` if standalone) is assigned. This is the round-level content of
Lemma EL (s2:lemEL). -/
theorem assign_ne_none_of_mem_partVerts (hv : Valid H c) {a : Addr} (ha : a ∈ prePartAddrs H c)
    {e : Sym2 V} (he : e ∈ (partVerts H c a).sym2) : assign H c e ≠ none := by
  classical
  by_cases hl : isLight H c a
  · unfold assign
    rw [Ne, Option.or_eq_none_iff, Option.or_eq_none_iff]
    rintro ⟨-, h2, -⟩
    rw [List.find?_eq_none] at h2
    apply h2 a (mem_homeOrder_of_valid hv ha)
    simp only [decide_eq_true_eq]
    exact ⟨ha, hl, he⟩
  · rw [partVerts_of_not_isLight hl] at he
    exact assign_ne_none_of_not_isLight hv ha hl he

/-- Two pre-parts whose leaf graphs share an edge are equal (SEP (i) on the two-level
recursion). -/
theorem eq_of_mem_X0_edges {a b : Addr} (ha : a ∈ prePartAddrs H c) (hb : b ∈ prePartAddrs H c)
    {e : Sym2 V} (hea : e ∈ (X0 H c a).edges) (heb : e ∈ (X0 H c b).edges) : a = b := by
  have he' : e ∈ (graph' H c).edges := (X0_le_graph' H c a).2 hea
  have hcount := STree.sep_count (twoLevel H c) he'
  have hle : ((twoLevel H c).leafAddrs.filter
      (fun L => e ∈ ((twoLevel H c).graphAtD (graph' H c) L).edges)).card ≤ 1 := by omega
  exact Finset.card_le_one.1 hle a
    (Finset.mem_filter.2 ⟨prePartAddrs_subset_leafAddrs H c ha, hea⟩) b
    (Finset.mem_filter.2 ⟨prePartAddrs_subset_leafAddrs H c hb, heb⟩)

/-- (R5) step (1): an edge of `X^0_Z` of a standalone pre-part `Z` is assigned to `Z`. -/
theorem assign_eq_of_mem_X0 (hv : Valid H c) {a : Addr} (ha : a ∈ prePartAddrs H c)
    (hl : ¬ isLight H c a) {e : Sym2 V} (he : e ∈ (X0 H c a).edges) : assign H c e = some a := by
  classical
  have hfind : c.homeOrder.find?
      (fun b => decide (b ∈ prePartAddrs H c ∧ e ∈ (partGraph H c b).edges)) = some a := by
    have hsome : (c.homeOrder.find?
        (fun b => decide (b ∈ prePartAddrs H c ∧ e ∈ (partGraph H c b).edges))).isSome := by
      rw [List.find?_isSome]
      refine ⟨a, mem_homeOrder_of_valid hv ha, ?_⟩
      simp only [decide_eq_true_eq]
      exact ⟨ha, by rw [partGraph_of_not_isLight hl]; exact he⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
    have hpb := List.find?_some hb
    simp only [decide_eq_true_eq] at hpb
    have heb : e ∈ (X0 H c b).edges := (partGraph_le_X0 H c b).2 hpb.2
    rw [hb, eq_of_mem_X0_edges hpb.1 ha heb he]
  unfold assign
  rw [hfind]
  rfl

/-- `D_l ⊆ Dup*_l`: a vertex in two pre-parts lies in two leaves of the two-level recursion. -/
theorem D_subset_DupStar : D H c ⊆ DupStar H c := by
  intro v hv
  rw [mem_D] at hv
  unfold mu at hv
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1
    (by omega : 1 < ((prePartAddrs H c).filter (fun a => v ∈ Z0 H c a)).card)
  rw [Finset.mem_filter] at ha hb
  exact STree.mem_dup_iff_exists.2 ⟨a, prePartAddrs_subset_leafAddrs H c ha.1, b,
    prePartAddrs_subset_leafAddrs H c hb.1, hab, ha.2, hb.2⟩

theorem guests_subset_D (a : Addr) : guests H c a ⊆ D H c := fun _ hv =>
  (Finset.mem_inter.1 (Finset.mem_filter.1 hv).1).2

end Round

end EG.HB
