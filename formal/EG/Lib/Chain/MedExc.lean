module

public import EG.Lib.Chain.Cluster

/-!
# Lemma MED (b): excess bounds for every admissible orientation (manuscript s6:lemMED)

Probe unit P2E (probe P-2, part 1), proof round 1. For a cluster `𝒦` and an admissible
orientation `O` (acyclicity is not used):
* `|exc(u)| ≤ deg_{B_𝒦}(u)` and `exc(u) ≡ deg_{B_𝒦}(u) (mod 2)` (`Cluster.abs_exc_le`,
  `Cluster.even_exc_sub_deg`): "`exc(u)` is a sum of `±1` over the `deg_{B_𝒦}(u)` beads at `u`";
* `∑_{u∈U_𝒦} exc(u) = 0` (`Cluster.sum_ports_exc`): handshake plus hub balance;
* `Φ(𝒦) ≤ b(𝒦)` (`Cluster.load_le_beadCount`), via
  `∑_{u∈U_𝒦} d⁺(u) = #{arcs port → hub} + e(B_𝒦[U_𝒦]) = ∑_h d⁻(h) + e(B_𝒦[U_𝒦])`.
-/

public section

namespace EG.Chain

variable {V : Type*} [DecidableEq V]

namespace Cluster

variable {K : Cluster V} {O : Finset (V × V)}

/-- Both ends of an arc of an orientation of the beads lie in `V(𝒦)`. -/
theorem fst_mem_verts_of_orient (hO : IsOrientation K.beads O) {a : V × V} (ha : a ∈ O) :
    a.1 ∈ K.verts :=
  K.mem_verts_of_mem_beads (hO.mem a ha) (Sym2.mem_mk_left _ _)

theorem snd_mem_verts_of_orient (hO : IsOrientation K.beads O) {a : V × V} (ha : a ∈ O) :
    a.2 ∈ K.verts :=
  K.mem_verts_of_mem_beads (hO.mem a ha) (Sym2.mem_mk_right _ _)

/-- [s6:lemMED] (b) "`exc(u)` is a sum of `±1` over the `deg_{B_𝒦}(u)` beads at `u`, which
gives the bound `|exc(u)| ≤ deg_{B_𝒦}(u)`". -/
theorem abs_exc_le (hO : IsOrientation K.beads O) (u : V) :
    |exc O u| ≤ (degE K.beads u : ℤ) := by
  have h := hO.outDeg_add_inDeg u
  unfold exc
  rw [abs_le]
  constructor <;> omega

/-- [s6:lemMED] (b) "... and the parity claim" `exc(u) ≡ deg_{B_𝒦}(u) (mod 2)`. -/
theorem even_exc_sub_deg (hO : IsOrientation K.beads O) (u : V) :
    Even (exc O u - (degE K.beads u : ℤ)) := by
  have h := hO.outDeg_add_inDeg u
  unfold exc
  refine ⟨-(inDeg O u : ℤ), ?_⟩
  omega

/-- The excess as a natural-number statement: `|exc(u)|` (`natAbs`) is at most `deg_{B_𝒦}(u)`. -/
theorem natAbs_exc_le (hO : IsOrientation K.beads O) (u : V) :
    (exc O u).natAbs ≤ degE K.beads u := by
  have := abs_exc_le hO u
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this

/-- Handshake: `∑_{v ∈ V(𝒦)} (d⁺(v) − d⁻(v)) = 0` ("Every arc contributes `+1` to `d⁺ − d⁻` at
its tail and `−1` at its head"). -/
theorem sum_verts_exc (hO : IsOrientation K.beads O) : ∑ v ∈ K.verts, exc O v = 0 := by
  unfold exc
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum,
    sum_outDeg_eq_card (fun a ha => fst_mem_verts_of_orient hO ha),
    sum_inDeg_eq_card (fun a ha => snd_mem_verts_of_orient hO ha), sub_self]

/-- [s6:lemMED] (b) "Hubs contribute `0`, hence `∑_{u∈U_𝒦} exc(u) = 0`." -/
theorem sum_ports_exc (hO : K.IsAdmissible O) : ∑ u ∈ K.ports, exc O u = 0 := by
  have h := sum_verts_exc hO.orient
  unfold verts at h
  rw [Finset.sum_union K.disjoint] at h
  have h0 : ∑ v ∈ K.hubs, exc O v = 0 :=
    Finset.sum_eq_zero fun v hv => by unfold exc; rw [hO.hub_bal v hv, sub_self]
  rw [h0, zero_add] at h
  exact h

/-- `∑_{u ∈ S} d⁺(u)` counts the arcs with tail in `S`. -/
theorem sum_outDeg_eq_card_filter (O : Finset (V × V)) (S : Finset V) :
    ∑ u ∈ S, outDeg O u = (O.filter (fun a => a.1 ∈ S)).card := by
  rw [← sum_outDeg_eq_card (A := O.filter (fun a => a.1 ∈ S)) (S := S)
    (fun a ha => (Finset.mem_filter.1 ha).2)]
  refine Finset.sum_congr rfl fun u hu => ?_
  unfold outDeg
  rw [Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, rfl⟩; exact ⟨ha, hu, rfl⟩
  · rintro ⟨ha, -, h⟩; exact ⟨ha, h⟩

/-- `∑_{h ∈ S} d⁻(h)` counts the arcs with head in `S`. -/
theorem sum_inDeg_eq_card_filter (O : Finset (V × V)) (S : Finset V) :
    ∑ u ∈ S, inDeg O u = (O.filter (fun a => a.2 ∈ S)).card := by
  rw [← sum_inDeg_eq_card (A := O.filter (fun a => a.2 ∈ S)) (S := S)
    (fun a ha => (Finset.mem_filter.1 ha).2)]
  refine Finset.sum_congr rfl fun u hu => ?_
  unfold inDeg
  rw [Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, rfl⟩; exact ⟨ha, hu, rfl⟩
  · rintro ⟨ha, -, h⟩; exact ⟨ha, h⟩

/-- An arc into a hub comes from a port ("no bead has both ends in `A_𝒦`"). -/
theorem fst_mem_ports_of_snd_mem_hubs (hO : IsOrientation K.beads O) {a : V × V} (ha : a ∈ O)
    (h2 : a.2 ∈ K.hubs) : a.1 ∈ K.ports := by
  rcases (K.mem_verts).1 (fst_mem_verts_of_orient hO ha) with h1 | h1
  · exfalso
    apply K.no_hub_hub _ (hO.mem a ha)
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact h1
    · exact h2
  · exact h1

/-- The port–port arcs are in bijection with the port–port beads `B_𝒦[U_𝒦]`. -/
theorem card_filter_ports_ports (hO : IsOrientation K.beads O) :
    (O.filter (fun a => a.1 ∈ K.ports ∧ a.2 ∈ K.ports)).card = K.portBeads.card := by
  have himg : (O.filter (fun a => a.1 ∈ K.ports ∧ a.2 ∈ K.ports)).image
      (fun a => s(a.1, a.2)) = K.portBeads := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter, mem_portBeads]
    constructor
    · rintro ⟨a, ⟨ha, h1, h2⟩, rfl⟩
      refine ⟨hO.mem a ha, fun v hv => ?_⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact h1
      · exact h2
    · rintro ⟨he, hp⟩
      obtain ⟨a, ha, rfl⟩ := hO.exists_mem he
      exact ⟨a, ⟨ha, hp _ (Sym2.mem_mk_left _ _), hp _ (Sym2.mem_mk_right _ _)⟩, rfl⟩
  rw [← himg, Finset.card_image_of_injOn]
  intro x hx y hy h
  exact hO.inj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hy).1 h

/-- [s6:lemMED] (b) (proof) "`∑_{u∈U_𝒦} d⁺(u) = #{arcs port → hub} + e(B_𝒦[U_𝒦])
= ∑_{h∈A_𝒦} d⁻(h) + e(B_𝒦[U_𝒦])`" ("every arc with tail at a port ends at a hub or at a
port"). -/
theorem sum_ports_outDeg (hO : IsOrientation K.beads O) :
    ∑ u ∈ K.ports, outDeg O u = ∑ h ∈ K.hubs, inDeg O h + K.portBeads.card := by
  rw [sum_outDeg_eq_card_filter, sum_inDeg_eq_card_filter, ← card_filter_ports_ports hO,
    ← Finset.card_filter_add_card_filter_not (p := fun a : V × V => a.2 ∈ K.hubs),
    Finset.filter_filter, Finset.filter_filter]
  congr 1
  · congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, -, h2⟩; exact ⟨ha, h2⟩
    · rintro ⟨ha, h2⟩; exact ⟨ha, fst_mem_ports_of_snd_mem_hubs hO ha h2, h2⟩
  · congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, h1, h2⟩
      refine ⟨ha, h1, ?_⟩
      rcases (K.mem_verts).1 (snd_mem_verts_of_orient hO ha) with h | h
      · exact absurd h h2
      · exact h
    · rintro ⟨ha, h1, h2⟩
      exact ⟨ha, h1, fun hh => K.not_mem_ports_of_mem_hubs hh h2⟩

/-- `exc(u)^+ ≤ d⁺(u)`. -/
theorem excPos_le_outDeg (O : Finset (V × V)) (u : V) : excPos O u ≤ outDeg O u := by
  unfold excPos exc
  omega

/-- [s6:lemMED] (b) "`Φ(𝒦) = ∑_u exc(u)^+ ≤ ∑_{u∈U_𝒦} d⁺(u) = … = b(𝒦)`", using
`d⁻(h) = deg_{B_𝒦}(h)/2` at every hub. -/
theorem load_le_beadCount (hO : K.IsAdmissible O) : ((K.load O : ℕ) : ℝ) ≤ K.beadCount := by
  have h1 : K.load O ≤ ∑ u ∈ K.ports, outDeg O u :=
    Finset.sum_le_sum fun u _ => excPos_le_outDeg O u
  rw [sum_ports_outDeg hO.orient] at h1
  have h2 : K.beadCount = ((∑ h ∈ K.hubs, inDeg O h + K.portBeads.card : ℕ) : ℝ) := by
    unfold beadCount
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun h hh => ?_
    have := hO.orient.outDeg_add_inDeg h
    rw [hO.hub_bal h hh] at this
    rw [← this]
    push_cast
    ring
  rw [h2]
  exact_mod_cast h1

end Cluster

end EG.Chain
