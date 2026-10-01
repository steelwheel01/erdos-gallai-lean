module

public import EG.Defs.Stage1.COL

/-!
# Stage 1b: vertex choices, sublabels and zones (manuscript s5:defZones)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s5.tex`, Definition [s5:defZones] (and `ρ_Y` of Lemma [s5:lemZones] (ii)).
Design note: `formal/work/p2d/stage1.md`. Namespace `EG.Stage1`; TRIAGE §2.7 (component (1b)),
§3 item 16.

Manuscript text ([s5:defZones]): "For a light part `Y` of round `r` put `zp_Y := L_Y^{-2}` and
`T^sl_Y := ⌈L_Y^2⌉` (as in Definition [s3:defCOL]). Independently for every vertex `v` of `G`,
and independently of all other stage-1 data …, draw
`choice(v) ∈ {none} ∪ {Y : Y a light part with v ∈ Y and r(Y) ≤ R-2}`, with
`P(choice(v) = Y) = zp_Y` for each such `Y` and `choice(v) = none` with the remaining probability
…. If `choice(v) = Y`, the vertex `v` also draws, independently and uniformly, a sublabel
`(l,c,σ)` with `r(Y)+2 ≤ l ≤ R, c ∈ [4], σ ∈ [T^sl_Y]`. The sublabels available to `Y` are
exactly the indices of the family `I^U` of `Y` in Definition [s3:defCOL] (ii). For such an index
put `Zone_{Y,l,c,σ} := {v ∈ Y : choice(v) = Y and the sublabel of v is (l,c,σ)}`. …"

Data model (TRIAGE §2.7 "1b zone"; blueprint s5 ZONE-TWO-STEP, ZONE-LAW-WELLDEF):
* the zone label of `v` is one value `Option ZIdx`, `ZIdx = PartId × LentTag`: `none` for
  `choice(v) = none`, `some (Y, i)` for `choice(v) = Y` with sublabel `i ∈ I^U(Y)` (the U-tag of
  `EG.Stage1.LentTag`, so that "the sublabels available to `Y` are exactly the indices of `I^U`"
  is definitional);
* one-step law: `some (Y, i)` has weight `zp_Y / |I^U(Y)|` (= `P(choice = Y) · P(sublabel = i)`,
  the sublabel being uniform on `I^U(Y)`), `none` has weight `1 - Σ_{Y ∈ A(v)} zp_Y`, where
  `A(v) = availParts G run v` are the light parts `Y ∋ v` with `r(Y) + 2 ≤ R`. The two-step and
  the one-step forms have the same law of `(choice, sublabel)`;
* the law is a probability distribution only if `Σ_{Y ∈ A(v)} zp_Y ≤ 1` (eq. (s5:eqZp), a theorem
  about valid runs under Γ). The definition is total through a `dite` whose guard is **exactly**
  `zpSum G run v ≤ 1`, with the fallback `dirac none` (TRIAGE §2.7, §2.12 "Stage-1 `dite` guards").
  An `A(v)`-part `Y` with `I^U(Y) = ∅` has `T^sl_Y = 0`, hence `L_Y = 0` and `zp_Y = 0⁻¹ = 0` in
  Lean, so the weights sum to `1` exactly under the guard (`zoneWeight_sum`);
* the labels are indexed by `↥G.verts` (TRIAGE §2.5); `zoneOf G ζ v` reads the label of any
  `v : V` (`none` off `V(G)`).
-/

@[expose] public section

namespace EG.Stage1

open EG.HB

/-- A zone index `(Y, (l,c,σ))`: the light part chosen by a vertex and its sublabel, a U-tag
`LentTag.U l c σ` ([s5:defZones] "The sublabels available to `Y` are exactly the indices of the
family `I^U` of `Y`"). -/
abbrev ZIdx : Type := PartId × LentTag

variable {V : Type*} [DecidableEq V] (G : FGraph V) (run : Run V)

/-- [s5:defZones] "For a light part `Y` of round `r` put `zp_Y := L_Y^{-2}`" (a real number;
`= 0` in Lean if `L_Y = 0`). -/
noncomputable def zp (Y : PartId) : ℝ := run.LY G Y ^ (-2 : ℤ)

/-- [s5:defZones] the light parts available to `choice(v)`: "`Y` a light part with `v ∈ Y` and
`r(Y) ≤ R-2`" (written `r(Y) + 2 ≤ R`). -/
noncomputable def availParts (v : V) : Finset PartId :=
  (run.lightParts G).filter (fun Y => v ∈ run.ancVerts G Y ∧ Y.1 + 2 ≤ run.R)

/-- `Σ_{Y ∈ A(v)} zp_Y`, the total probability of `choice(v) ≠ none` ([s5:defZones]: the
remaining probability `1 - Σ_Y zp_Y` "is at least `1/2`, since `Σ_Y zp_Y ≤ Σ_{Y∋v} L_Y^{-2} < 1/2`
by (s5:eqZp)"). -/
noncomputable def zpSum (v : V) : ℝ := ∑ Y ∈ availParts G run v, zp G run Y

open Classical in
/-- The weights of the zone label of `v` ([s5:defZones], one-step form):
`some (Y, i) ↦ zp_Y / |I^U(Y)|` for `Y ∈ A(v)`, `i ∈ I^U(Y)` (`P(choice(v) = Y) = zp_Y`, then a
uniform sublabel), `none ↦ 1 - Σ_{Y ∈ A(v)} zp_Y` ("`choice(v) = none` with the remaining
probability"), and `0` otherwise. -/
noncomputable def zoneWeight (v : V) : Option ZIdx → ℝ
  | none => 1 - zpSum G run v
  | some (Y, i) =>
    if Y ∈ availParts G run v ∧ i ∈ IU G run Y then zp G run Y / (IU G run Y).card else 0

/-- The support of the zone label law of `v`: `none` and the pairs `(Y, i)`, `Y ∈ A(v)`,
`i ∈ I^U(Y)`. -/
noncomputable def zoneSupport (v : V) : Finset (Option ZIdx) :=
  insert none ((availParts G run v).biUnion fun Y => (IU G run Y).image fun i => some (Y, i))

theorem zp_nonneg (Y : PartId) : 0 ≤ zp G run Y := by
  unfold zp
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  positivity

theorem zoneWeight_nonneg (v : V) (h : zpSum G run v ≤ 1) (o : Option ZIdx) :
    0 ≤ zoneWeight G run v o := by
  rcases o with _ | ⟨Y, i⟩
  · simp only [zoneWeight]; linarith
  · simp only [zoneWeight]
    split_ifs
    · exact div_nonneg (zp_nonneg G run Y) (Nat.cast_nonneg _)
    · exact le_refl 0

theorem zoneWeight_eq_zero (v : V) (o : Option ZIdx) (ho : o ∉ zoneSupport G run v) :
    zoneWeight G run v o = 0 := by
  rcases o with _ | ⟨Y, i⟩
  · simp [zoneSupport] at ho
  · simp only [zoneWeight]
    rw [if_neg]
    rintro ⟨hY, hi⟩
    exact ho (Finset.mem_insert_of_mem (Finset.mem_biUnion.2
      ⟨Y, hY, Finset.mem_image.2 ⟨i, hi, rfl⟩⟩))

/-- An available part with no sublabel has `zp_Y = 0` (then `T^sl_Y = ⌈L_Y^2⌉₊ = 0`, so
`L_Y = 0`). -/
theorem zp_eq_zero_of_IU_eq_empty {v : V} {Y : PartId} (hY : Y ∈ availParts G run v)
    (hIU : IU G run Y = ∅) : zp G run Y = 0 := by
  classical
  simp only [availParts, Finset.mem_filter] at hY
  have hlight : run.isLight G Y.1 Y.2 := by
    simp only [Run.lightParts, Finset.mem_filter] at hY
    exact hY.1.2
  have hT : Tslot G run Y = 0 := by
    by_contra hT
    have hmem : LentTag.U (Y.1 + 2) 0 0 ∈ IU G run Y := by
      simp only [IU, hlight, if_true]
      refine Finset.mem_image.2 ⟨(Y.1 + 2, 0, 0), ?_, rfl⟩
      simp only [lateRounds, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
        Finset.mem_range, true_and]
      exact ⟨⟨le_rfl, hY.2.2⟩, Nat.pos_of_ne_zero hT⟩
    rw [hIU] at hmem
    exact Finset.notMem_empty _ hmem
  have hL : run.LY G Y ^ 2 ≤ 0 := Nat.ceil_eq_zero.1 hT
  have hL0 : run.LY G Y ^ 2 = 0 := le_antisymm hL (sq_nonneg _)
  have : run.LY G Y = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hL0
  simp [zp, this]

theorem zoneWeight_sum (v : V) : ∑ o ∈ zoneSupport G run v, zoneWeight G run v o = 1 := by
  classical
  rw [zoneSupport, Finset.sum_insert (by simp)]
  rw [Finset.sum_biUnion]
  · have h : ∀ Y ∈ availParts G run v,
        ∑ o ∈ (IU G run Y).image (fun i => some (Y, i)), zoneWeight G run v o = zp G run Y := by
      intro Y hY
      rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
      have : ∀ i ∈ IU G run Y, zoneWeight G run v (some (Y, i)) =
          zp G run Y / (IU G run Y).card := by
        intro i hi
        simp [zoneWeight, hY, hi]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      rcases (IU G run Y).eq_empty_or_nonempty with he | hne
      · rw [he, zp_eq_zero_of_IU_eq_empty G run hY he]; simp
      · have : ((IU G run Y).card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
        field_simp
    rw [Finset.sum_congr rfl h]
    simp only [zoneWeight, zpSum]
    ring
  · intro Y _ Y' _ hYY'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro o h1 h2
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨i', _, h⟩ := Finset.mem_image.1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact hYY' h.1.symm

/-- [s5:defZones] the law of the zone label of the vertex `v`: `(choice(v), sublabel)` in the
one-step form (`zoneWeight`). Total by a `dite` whose guard is exactly `Σ_{Y ∈ A(v)} zp_Y ≤ 1`
(true for valid runs under Γ by (s5:eqZp)); fallback `dirac none` (TRIAGE §2.7). -/
noncomputable def zoneLabelLaw (v : V) : FinDist (Option ZIdx) :=
  if h : zpSum G run v ≤ 1 then
    FinDist.ofFinset (zoneSupport G run v) (zoneWeight G run v) (zoneWeight_nonneg G run v h)
      (zoneWeight_eq_zero G run v) (zoneWeight_sum G run v)
  else FinDist.dirac none

/-- [s5:defZones] component (1b) of stage 1: "Independently for every vertex `v` of `G`" draw the
zone label, i.e. the product over `V(G)` of `zoneLabelLaw`. -/
noncomputable def zoneLaw : FinDist (↥G.verts → Option ZIdx) :=
  FinDist.pi fun v => zoneLabelLaw G run v

variable {G} in
/-- The zone label of `v : V` in the outcome `ζ` of (1b) (`none` if `v ∉ V(G)`). -/
def zoneOf (ζ : ↥G.verts → Option ZIdx) (v : V) : Option ZIdx :=
  if h : v ∈ G.verts then ζ ⟨v, h⟩ else none

/-- [s5:defZones] "`Zone_{Y,l,c,σ} := {v ∈ Y : choice(v) = Y and the sublabel of v is (l,c,σ)}`",
for the sublabel `i = LentTag.U l c σ` (for other tags the set is empty on the support). -/
noncomputable def Zone (ζ : ↥G.verts → Option ZIdx) (Y : PartId) (i : LentTag) : Finset V :=
  (run.ancVerts G Y).filter (fun v => zoneOf ζ v = some (Y, i))

variable {G} in
/-- [s5:defZones] "we say that `v` carries a round-`l` zone if `choice(v) ≠ none` and the
sublabel of `v` has first coordinate `l`; the phase of that zone is then the second coordinate
`c`": `zonePhase ζ l v = some c` iff `v` carries a round-`l` zone of phase `c`, and `none` iff
`v` carries no round-`l` zone. -/
def zonePhase (ζ : ↥G.verts → Option ZIdx) (l : ℕ) (v : V) : Option (Fin 4) :=
  match zoneOf ζ v with
  | some (_, LentTag.U l' c _) => if l' = l then some c else none
  | _ => none

/-- [s5:lemZones] (ii) "`ρ_Y := zp_Y / ((R-r-1)·4·T^sl_Y)`" (real subtraction `R - r - 1`; the
number of sublabels of `Y` for `r ≤ R - 2`). -/
noncomputable def rhoY (Y : PartId) : ℝ :=
  zp G run Y / (((run.R : ℝ) - (Y.1 : ℝ) - 1) * 4 * (Tslot G run Y : ℝ))

end EG.Stage1
