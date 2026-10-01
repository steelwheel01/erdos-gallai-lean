module

public import EG.Lib.Found.Graph

/-!
# API for `FGraph.nbrSetDeg` (`N_{H,d}(U)`, s1:citProp12) and `FGraph.IsWellExpanding` (s3:lemL17s)

* `mem_nbrSetDeg`, `nbrSetDeg_natCast`, `mem_nbrSetDeg_iff_ceil` (the real threshold as a
  natural-number ceiling),
  `nbrSetDeg_subset_sdiff`, `nbrSetDeg_subset_verts`, `disjoint_nbrSetDeg`,
  `nbrSetDeg_subset_nbrSet` (for `d > 0`: `N_{H,d}(U) ⊆ Nbr_H(U)`), `nbrSetDeg_anti`;
* `isWellExpanding_iff`, `isWellExpanding_empty`, `IsWellExpanding.anti` (in `θ`).
-/

public section


namespace EG

namespace FGraph

variable {V : Type*} [DecidableEq V] (H : FGraph V)

theorem mem_nbrSetDeg {U : Finset V} {d : ℝ} {v : V} :
    v ∈ H.nbrSetDeg U d ↔ v ∈ H.verts ∧ v ∉ U ∧ d ≤ ((H.nbrs v ∩ U).card : ℝ) := by
  simp [nbrSetDeg, and_assoc]

/-- The real threshold `d ≤ |N_H(v) ∩ U|` is `⌈d⌉₊ ≤ |N_H(v) ∩ U|` (useful for computation). -/
theorem mem_nbrSetDeg_iff_ceil {U : Finset V} {d : ℝ} {v : V} :
    v ∈ H.nbrSetDeg U d ↔ v ∈ H.verts ∧ v ∉ U ∧ ⌈d⌉₊ ≤ (H.nbrs v ∩ U).card := by
  rw [mem_nbrSetDeg, Nat.ceil_le]

/-- For an integer threshold `d = k` (the case of s3:propP13s), `N_{H,k}(U)` is a decidable
filter. -/
theorem nbrSetDeg_natCast (U : Finset V) (k : ℕ) :
    H.nbrSetDeg U (k : ℝ) = (H.verts \ U).filter (fun v => k ≤ (H.nbrs v ∩ U).card) := by
  ext v
  simp [nbrSetDeg]

theorem nbrSetDeg_subset_sdiff (U : Finset V) (d : ℝ) : H.nbrSetDeg U d ⊆ H.verts \ U :=
  Finset.filter_subset _ _

theorem nbrSetDeg_subset_verts (U : Finset V) (d : ℝ) : H.nbrSetDeg U d ⊆ H.verts :=
  (H.nbrSetDeg_subset_sdiff U d).trans Finset.sdiff_subset

theorem disjoint_nbrSetDeg (U : Finset V) (d : ℝ) : Disjoint U (H.nbrSetDeg U d) :=
  Finset.disjoint_of_subset_right (H.nbrSetDeg_subset_sdiff U d) Finset.disjoint_sdiff

/-- For `d > 0`, a vertex with at least `d` neighbours in `U` has a neighbour in `U`:
`N_{H,d}(U) ⊆ Nbr_H(U)`. -/
theorem nbrSetDeg_subset_nbrSet (U : Finset V) {d : ℝ} (hd : 0 < d) :
    H.nbrSetDeg U d ⊆ H.nbrSet U := by
  intro v hv
  rw [mem_nbrSetDeg] at hv
  obtain ⟨hvV, hvU, hdv⟩ := hv
  have hpos : 0 < (H.nbrs v ∩ U).card := by exact_mod_cast hd.trans_le hdv
  obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_inter] at hu
  simp only [nbrSet, Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨⟨hvV, hvU⟩, u, hu.2, ((Finset.mem_filter.1 hu.1).2).symm⟩

/-- `N_{H,d}(U)` is antitone in the threshold `d`. -/
theorem nbrSetDeg_anti (U : Finset V) {d d' : ℝ} (h : d ≤ d') :
    H.nbrSetDeg U d' ⊆ H.nbrSetDeg U d := by
  intro v hv
  rw [mem_nbrSetDeg] at hv ⊢
  exact ⟨hv.1, hv.2.1, h.trans hv.2.2⟩

theorem isWellExpanding_iff {θ : ℝ} {U : Finset V} :
    H.IsWellExpanding θ U ↔ θ * (U.card : ℝ) ≤ ((H.nbrSet U).card : ℝ) := Iff.rfl

@[simp] theorem isWellExpanding_empty (θ : ℝ) : H.IsWellExpanding θ ∅ := by
  simp [IsWellExpanding]

/-- Well-expanding for a threshold `θ'` implies well-expanding for every `θ ≤ θ'`. -/
theorem IsWellExpanding.anti {θ θ' : ℝ} {U : Finset V} (h : H.IsWellExpanding θ' U)
    (hθ : θ ≤ θ') : H.IsWellExpanding θ U :=
  le_trans (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)) h

end FGraph

end EG
