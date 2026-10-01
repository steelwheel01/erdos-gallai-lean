module

public import EG.Defs.Stage1.Zones
public import EG.Lib.Stage1.COL

/-!
# API for the zones (s5:defZones, s5:lemZones)

Lemmas about `EG/Defs/Stage1/Zones.lean`:
* `ancVerts_subset_verts` (`V(Y) ⊆ V(G)`);
* the law under its guard: `zoneLabelLaw_w_of_le`, `prob_zoneLabelLaw_none`,
  `prob_zoneLabelLaw_some` (`P(label(v) = (Y,l,c,σ)) = ρ_Y`), `rhoY_eq_zp_div_card`;
* membership in zones (`mem_Zone`, `Zone_subset`), [s5:lemZones] (iii) `disjoint_Zone`
  (deterministic: every vertex has one label); `zonePhase_eq_some_iff`, `zonePhase_eq_none_iff`
  (the phase read off the label);
* [s5:lemZones] (ii) in law form: `isRSubset_Zone` (`Zone_{Y,l,c,σ}` is a `ρ_Y`-random subset of
  `V(Y)` under `zoneLaw`, given the guards `Σ zp ≤ 1` at the vertices of `Y`).
The numeric facts (s5:eqZp) that discharge the guards, and `ρ_Y ≥ 1/(12L_Y^5)`, are s5 Specs.
-/

public section

namespace EG.Stage1

open EG.HB EG.FinDist Finset

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

theorem ancVerts_subset_verts (Y : PartId) : run.ancVerts G Y ⊆ G.verts :=
  (run.partVerts_subset_Z0 G Y.1 Y.2).trans (run.Z0_subset_verts G Y.1 Y.2)

theorem zoneLabelLaw_w_of_le {v : V} (h : zpSum G run v ≤ 1) (o : Option ZIdx) :
    (zoneLabelLaw G run v).w o = zoneWeight G run v o := by
  unfold zoneLabelLaw
  rw [dif_pos h]
  rfl

theorem prob_zoneLabelLaw_none {v : V} (h : zpSum G run v ≤ 1) :
    (zoneLabelLaw G run v).prob {none} = 1 - zpSum G run v := by
  rw [prob_singleton, zoneLabelLaw_w_of_le G run h]
  rfl

/-- For a light part `Y` of round `r ≤ R - 2`, `ρ_Y = zp_Y / |I^U(Y)|`. -/
theorem rhoY_eq_zp_div_card {Y : PartId} (hY : run.isLight G Y.1 Y.2) (hR : Y.1 + 2 ≤ run.R) :
    rhoY G run Y = zp G run Y / (IU G run Y).card := by
  have hc : ((run.R + 1 - (Y.1 + 2) : ℕ) : ℝ) = (run.R : ℝ) - (Y.1 : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [rhoY, card_IU_of_isLight hY, Nat.cast_mul, Nat.cast_mul, hc]
  norm_num

/-- [s5:lemZones] (ii) (one vertex) "`P(v ∈ Zone_{Y,l,c,σ}) = zp_Y/((R-r-1)·4·T^sl_Y) = ρ_Y`". -/
theorem prob_zoneLabelLaw_some {v : V} (h : zpSum G run v ≤ 1) {Y : PartId}
    (hY : Y ∈ availParts G run v) {i : LentTag} (hi : i ∈ IU G run Y) :
    (zoneLabelLaw G run v).prob {some (Y, i)} = rhoY G run Y := by
  classical
  rw [prob_singleton, zoneLabelLaw_w_of_le G run h]
  have hlight : run.isLight G Y.1 Y.2 := by
    simp only [availParts, Run.lightParts, Finset.mem_filter] at hY
    exact hY.1.2
  have hR : Y.1 + 2 ≤ run.R := by
    simp only [availParts, Finset.mem_filter] at hY
    exact hY.2.2
  rw [rhoY_eq_zp_div_card G run hlight hR]
  simp [zoneWeight, hY, hi]

/-- The two-step form of [s5:defZones]: "`P(choice(v) = Y) = zp_Y`" for every available `Y`. -/
theorem prob_zoneLabelLaw_choice {v : V} (h : zpSum G run v ≤ 1) {Y : PartId}
    (hY : Y ∈ availParts G run v) :
    (zoneLabelLaw G run v).prob {o | ∃ i, o = some (Y, i)} = zp G run Y := by
  classical
  have e : (zoneLabelLaw G run v).prob {o | ∃ i, o = some (Y, i)} =
      (zoneLabelLaw G run v).prob ↑((IU G run Y).image fun i => some (Y, i)) := by
    refine prob_congr _ fun o ho => ?_
    rw [zoneLabelLaw_w_of_le G run h] at ho
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hi
      simp [zoneWeight, hi] at ho
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
  rw [e, prob_coe_finset, Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
  have : ∀ i ∈ IU G run Y, (zoneLabelLaw G run v).w (some (Y, i)) =
      zp G run Y / (IU G run Y).card := by
    intro i hi
    rw [zoneLabelLaw_w_of_le G run h]
    simp [zoneWeight, hY, hi]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rcases (IU G run Y).eq_empty_or_nonempty with he | hne
  · rw [he, zp_eq_zero_of_IU_eq_empty G run hY he]; simp
  · have : ((IU G run Y).card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
    field_simp

variable {G run}

theorem mem_Zone {ζ : ↥G.verts → Option ZIdx} {Y : PartId} {i : LentTag} {v : V} :
    v ∈ Zone G run ζ Y i ↔ v ∈ run.ancVerts G Y ∧ zoneOf ζ v = some (Y, i) := by
  simp [Zone]

theorem Zone_subset (ζ : ↥G.verts → Option ZIdx) (Y : PartId) (i : LentTag) :
    Zone G run ζ Y i ⊆ run.ancVerts G Y :=
  Finset.filter_subset _ _

/-- [s5:lemZones] (iii) "All zones `Zone_{Y,l,c,σ}`, over all light parts `Y` and all sublabels
`(l,c,σ)` of `Y`, are pairwise disjoint" (for every outcome). -/
theorem disjoint_Zone (ζ : ↥G.verts → Option ZIdx) {Y Y' : PartId} {i i' : LentTag}
    (h : (Y, i) ≠ (Y', i')) : Disjoint (Zone G run ζ Y i) (Zone G run ζ Y' i') := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  rw [mem_Zone] at h1 h2
  rw [h1.2] at h2
  exact h (Option.some.inj h2.2)

/-- `zonePhase` read off the label: `v` carries a round-`l` zone of phase `c` iff its label is
`(Y, (l,c,σ))` for some `Y`, `σ` (for every assignment of labels; the form with `v ∈ Zone` needs
the support, `zonePhase_eq_some_iff_mem_Zone` in `EG.Lib.Stage1.Law`). -/
theorem zonePhase_eq_some_iff (ζ : ↥G.verts → Option ZIdx) (l : ℕ) (v : V) (c : Fin 4) :
    zonePhase ζ l v = some c ↔ ∃ Y σ, zoneOf ζ v = some (Y, LentTag.U l c σ) := by
  unfold zonePhase
  rcases h : zoneOf ζ v with _ | ⟨Y, i⟩
  · simp
  · rcases i with ⟨l', c', σ⟩ | ⟨l', j⟩ | l'
    · simp only [Option.some.injEq, Prod.mk.injEq, LentTag.U.injEq]
      constructor
      · intro h'
        split_ifs at h' with hl
        · exact ⟨Y, σ, rfl, hl, Option.some.inj h', rfl⟩
      · rintro ⟨Y', σ', -, rfl, rfl, -⟩
        simp
    · simp
    · simp

/-- `zonePhase ζ l v = none` iff no label of `v` is a round-`l` sublabel. -/
theorem zonePhase_eq_none_iff (ζ : ↥G.verts → Option ZIdx) (l : ℕ) (v : V) :
    zonePhase ζ l v = none ↔ ∀ Y c σ, zoneOf ζ v ≠ some (Y, LentTag.U l c σ) := by
  constructor
  · intro h Y c σ hz
    have := (zonePhase_eq_some_iff ζ l v c).2 ⟨Y, σ, hz⟩
    rw [h] at this
    cases this
  · intro h
    rcases hp : zonePhase ζ l v with _ | c
    · rfl
    · obtain ⟨Y, σ, hz⟩ := (zonePhase_eq_some_iff ζ l v c).1 hp
      exact absurd hz (h Y c σ)

variable (G run)

/-- [s5:lemZones] (ii) "the set `Zone_{Y,l,c,σ}` is exactly a `ρ_Y`-random subset of `Y` (each
vertex of `Y` independently, product measure)", under the guard `Σ_{Y'∋v} zp_{Y'} ≤ 1` at every
vertex `v` of `Y` (the law of (1b) as defined; (s5:eqZp) discharges the guard). -/
theorem isRSubset_Zone {Y : PartId} (hY : Y ∈ run.lightParts G) (hR : Y.1 + 2 ≤ run.R)
    (hg : ∀ v ∈ run.ancVerts G Y, zpSum G run v ≤ 1) {i : LentTag} (hi : i ∈ IU G run Y) :
    (zoneLaw G run).IsRSubset (fun ζ => Zone G run ζ Y i) (run.ancVerts G Y) (rhoY G run Y) := by
  classical
  have hV := ancVerts_subset_verts G run Y
  have hav : ∀ v ∈ run.ancVerts G Y, Y ∈ availParts G run v := fun v hv =>
    Finset.mem_filter.2 ⟨hY, hv, hR⟩
  let b : ↥(run.ancVerts G Y) → (↥G.verts → Option ZIdx) → Bool := fun y ζ =>
    decide (ζ ⟨y, hV y.2⟩ = some (Y, i))
  have e : (fun ζ => Zone G run ζ Y i) =
      fun ζ => FinDist.selectSet (run.ancVerts G Y) fun y => b y ζ := by
    funext ζ
    ext y
    rw [mem_Zone, mem_selectSet]
    constructor
    · rintro ⟨hy, h⟩
      refine ⟨hy, ?_⟩
      simp only [zoneOf, hV hy, dif_pos] at h
      simp [b, h]
    · rintro ⟨hy, h⟩
      refine ⟨hy, ?_⟩
      simp only [b, decide_eq_true_eq] at h
      simp [zoneOf, hV hy, h]
  -- the value `ρ_Y` is a probability
  obtain ⟨v₀, hv₀⟩ : (run.ancVerts G Y).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hT : Tslot G run Y = 0 := by
      simp [Tslot, Run.LY, hne]
    have : (IU G run Y) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      obtain ⟨-, l, c, σ, -, -, hσ⟩ := mem_IU.1 hj
      omega
    rw [this] at hi
    exact Finset.notMem_empty _ hi
  have hp : ∀ v ∈ run.ancVerts G Y, (zoneLabelLaw G run v).prob {some (Y, i)} = rhoY G run Y :=
    fun v hv => prob_zoneLabelLaw_some G run (hg v hv) (hav v hv) hi
  have h1 : rhoY G run Y ≤ 1 := hp v₀ hv₀ ▸ prob_le_one _ _
  have h0 : 0 ≤ rhoY G run Y := hp v₀ hv₀ ▸ prob_nonneg _ _
  rw [e]
  refine isRSubset_selectSet h0 h1 ?_ ?_
  · refine iIndepFun_pi_of_dependsOn _ (fun y => {⟨(y : V), hV y.2⟩}) ?_ b ?_
    · intro y y' hyy'
      simp only [Set.disjoint_singleton, ne_eq, Subtype.mk.injEq]
      exact fun h => hyy' (Subtype.ext h)
    · intro y f f' h
      simp only [b]
      rw [h _ rfl]
  · intro y
    have : {ζ : ↥G.verts → Option ZIdx | b y ζ = true} =
        {ζ | ζ ⟨(y : V), hV y.2⟩ ∈ ({some (Y, i)} : Set (Option ZIdx))} := by
      ext ζ
      simp [b]
    rw [this, zoneLaw, prob_pi_eval]
    exact hp y y.2

end EG.Stage1
