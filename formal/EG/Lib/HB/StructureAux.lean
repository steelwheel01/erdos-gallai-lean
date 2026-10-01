module

public import EG.Lib.HB.Run

/-!
# Helpers for Proposition s2:propStructure (iv) (manuscript s2:propStructure)

Round-level facts about `home`, `D` and the light parts (unit P3-s2):
* `Round.home_spec`: `home(v) = Z` implies `Z` is a pre-part containing `v`;
* `Round.mu_le_one_of_notMem_D`: a vertex outside `D_l` lies in at most one pre-part;
* `Round.home_eq_of_mem_partVerts`: "Let `v` lie in the light part of a light pre-part `Z` … If
  `v ∈ D_l` then, as `v ∉ S_Z`, `home_l(v) = Z`. If `v ∉ D_l` then `Z` is the only round-`l`
  pre-part containing `v`, so again `home_l(v) = Z`".
-/

public section

namespace EG.HB

namespace Round

variable {V : Type*} [DecidableEq V] (H : FGraph V) (c : RoundChoice V)

theorem home_spec {v : V} {a : Addr} (h : home H c v = some a) :
    a ∈ prePartAddrs H c ∧ v ∈ Z0 H c a := by
  have := List.find?_some h
  simpa using this

theorem mu_le_one_of_notMem_D {v : V} (hv : v ∉ D H c) : mu H c v ≤ 1 := by
  by_contra hcon
  push Not at hcon
  apply hv
  unfold D
  rw [Finset.mem_filter]
  refine ⟨?_, hcon⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < mu H c v)
  rw [Finset.mem_filter] at ha
  exact Finset.mem_biUnion.2 ⟨a, ha.1, ha.2⟩

theorem eq_of_notMem_D {v : V} (hv : v ∉ D H c) {a b : Addr} (ha : a ∈ prePartAddrs H c)
    (hb : b ∈ prePartAddrs H c) (hva : v ∈ Z0 H c a) (hvb : v ∈ Z0 H c b) : a = b := by
  have h := mu_le_one_of_notMem_D H c hv
  unfold mu at h
  exact Finset.card_le_one.1 h a (Finset.mem_filter.2 ⟨ha, hva⟩) b (Finset.mem_filter.2 ⟨hb, hvb⟩)

theorem home_isSome (hv : Valid H c) {v : V} {a : Addr} (ha : a ∈ prePartAddrs H c)
    (hva : v ∈ Z0 H c a) : ∃ b, home H c v = some b := by
  have hmem : a ∈ c.homeOrder := by
    rw [← List.mem_toFinset, hv.2.2.2.2.2]; exact ha
  have : (home H c v).isSome := by
    unfold home
    rw [List.find?_isSome]
    exact ⟨a, hmem, by simp [ha, hva]⟩
  exact Option.isSome_iff_exists.1 this

theorem home_eq_of_mem_partVerts (hv : Valid H c) {v : V} {a : Addr} (ha : a ∈ prePartAddrs H c)
    (hl : isLight H c a) (hva : v ∈ partVerts H c a) : home H c v = some a := by
  classical
  unfold partVerts at hva
  rw [if_pos hl, Finset.mem_sdiff] at hva
  obtain ⟨hvZ, hvS⟩ := hva
  by_cases hD : v ∈ D H c
  · by_contra hne
    apply hvS
    unfold guests
    rw [Finset.mem_filter, Finset.mem_inter]
    exact ⟨⟨hvZ, hD⟩, hne⟩
  · obtain ⟨b, hb⟩ := home_isSome H c hv ha hvZ
    obtain ⟨hbP, hvb⟩ := home_spec H c hb
    rw [hb, eq_of_notMem_D H c hD hbP ha hvb hvZ]

end Round

end EG.HB
