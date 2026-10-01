module

public import EG.Defs.Chain.Cluster
public import EG.Lib.Found.Orient
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Clusters: basic API (companion of `EG.Defs.Chain.Cluster`)

* excess: `exc = exc⁺ − exc⁻`, the casts of `excPos` / `excNeg` are `max(±exc, 0)`;
* vertex sets and beads: every bead has an end at a port (`Cluster.exists_port_of_mem_beads`),
  bead neighbours of a vertex are counted by `deg_{B_𝒦}` (`Cluster.card_beadNbrs`);
* an admissible orientation forces even hub degrees (`Cluster.IsAdmissible.parityClean`), and
  the bead count is a natural number for parity-clean clusters
  (`Cluster.beadCount_eq_natCast`);
* membership in the median orientation (`Cluster.mem_medOrient`).
-/

public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V]

theorem excPos_cast (O : Finset (V × V)) (u : V) : (excPos O u : ℤ) = max (exc O u) 0 :=
  Int.toNat_eq_max _

theorem excNeg_cast (O : Finset (V × V)) (u : V) : (excNeg O u : ℤ) = max (-exc O u) 0 :=
  Int.toNat_eq_max _

theorem exc_eq_excPos_sub_excNeg (O : Finset (V × V)) (u : V) :
    exc O u = (excPos O u : ℤ) - excNeg O u := by
  rw [excPos_cast, excNeg_cast]; omega

theorem excPos_eq_zero_or_excNeg_eq_zero (O : Finset (V × V)) (u : V) :
    excPos O u = 0 ∨ excNeg O u = 0 := by
  have h1 := excPos_cast O u
  have h2 := excNeg_cast O u
  omega

namespace Cluster

variable (K : Cluster V)

@[simp] theorem mem_verts {v : V} : v ∈ K.verts ↔ v ∈ K.hubs ∨ v ∈ K.ports :=
  Finset.mem_union

theorem hubs_subset_verts : K.hubs ⊆ K.verts := Finset.subset_union_left

theorem ports_subset_verts : K.ports ⊆ K.verts := Finset.subset_union_right

omit [DecidableEq V] in
theorem not_mem_ports_of_mem_hubs {v : V} (hv : v ∈ K.hubs) : v ∉ K.ports :=
  Finset.disjoint_left.1 K.disjoint hv

theorem mem_verts_of_mem_beads {e : Sym2 V} (he : e ∈ K.beads) {v : V} (hv : v ∈ e) :
    v ∈ K.verts :=
  (K.mem_verts).2 (K.ends_mem e he v hv)

omit [DecidableEq V] in
/-- Every bead has an end at a port ("no bead has both ends in `A_𝒦`"). -/
theorem exists_port_of_mem_beads {e : Sym2 V} (he : e ∈ K.beads) : ∃ v ∈ e, v ∈ K.ports := by
  by_contra h
  exact K.no_hub_hub e he fun v hv =>
    (K.ends_mem e he v hv).resolve_right fun hp => h ⟨v, hv, hp⟩

@[simp] theorem mem_portBeads {e : Sym2 V} :
    e ∈ K.portBeads ↔ e ∈ K.beads ∧ ∀ v ∈ e, v ∈ K.ports := by
  simp [portBeads, Finset.mem_sym2_iff]

@[simp] theorem mem_beadNbrs {h w : V} : w ∈ K.beadNbrs h ↔ w ∈ K.verts ∧ s(h, w) ∈ K.beads :=
  Finset.mem_filter

/-- The number of `B_𝒦`-neighbours of `h` is `deg_{B_𝒦}(h)` (beads are not loops). -/
theorem card_beadNbrs (h : V) : (K.beadNbrs h).card = degE K.beads h := by
  unfold degE edgesAt
  have himg : (K.beadNbrs h).image (fun w => s(h, w)) = K.beads.filter (fun e => h ∈ e) := by
    ext e
    simp only [Finset.mem_image, mem_beadNbrs, Finset.mem_filter]
    constructor
    · rintro ⟨w, ⟨-, hw⟩, rfl⟩
      exact ⟨hw, Sym2.mem_mk_left h w⟩
    · rintro ⟨he, hh⟩
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hh
      exact ⟨w, ⟨K.mem_verts_of_mem_beads he (Sym2.mem_mk_right h w), he⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injective _ (fun a b hab => Sym2.congr_right.1 hab)]

/-- An admissible orientation forces even hub degrees: `deg_{B_𝒦}(h) = d⁺(h) + d⁻(h) = 2d⁺(h)`.
(So hypothesis (P) of HCC-P follows from admissibility; blueprint note HCCP-P-REDUNDANT.) -/
theorem IsAdmissible.parityClean {K : Cluster V} {O : Finset (V × V)} (hO : K.IsAdmissible O) :
    K.ParityClean := by
  intro h hh
  have h1 := hO.orient.outDeg_add_inDeg h
  have h2 := hO.hub_bal h hh
  exact ⟨outDeg O h, by omega⟩

/-- For a parity-clean cluster the bead count `b(𝒦)` is the natural number
`∑_h deg_{B_𝒦}(h)/2 + e(B_𝒦[U_𝒦])` (with exact division). -/
theorem beadCount_eq_natCast (hK : K.ParityClean) :
    K.beadCount = ((∑ h ∈ K.hubs, degE K.beads h / 2 + K.portBeads.card : ℕ) : ℝ) := by
  unfold beadCount
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  obtain ⟨r, hr⟩ := hK h hh
  rw [hr, show r + r = 2 * r by ring, Nat.mul_div_cancel_left r (by norm_num)]
  push_cast
  ring

/-- The load as an integer: `Φ(𝒦) = ∑_{u∈U_𝒦} max(exc(u), 0)`. -/
theorem load_cast (O : Finset (V × V)) :
    (K.load O : ℤ) = ∑ u ∈ K.ports, max (exc O u) 0 := by
  unfold load
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun u _ => excPos_cast O u

theorem mem_medOrient {rk : V → ℕ} {a : V × V} :
    a ∈ K.medOrient rk ↔ s(a.1, a.2) ∈ K.beads ∧ K.medRule rk a.1 a.2 := by
  unfold medOrient
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨K.mem_verts_of_mem_beads h.1 (Sym2.mem_mk_left _ _),
      K.mem_verts_of_mem_beads h.1 (Sym2.mem_mk_right _ _)⟩, h⟩

end Cluster

end EG.Chain
