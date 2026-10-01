import EG.Lib.Stage1.Law
import EGTest.HB

/-! Unit tests for `EG.Defs.Stage1.{COL, Zones, Pool, Law}` ([s3:defCOL], [s3:lemCOL],
[s5:defZones], [s5:lemZones], [s7:defPool], [s7:defSchedule] stage 1):
* the tags and the own-label bijection (`R_{j,c} ↦ 4j + c`, `M ↦ 4J`, and back);
* the JS label weights at `M = 2` (`1/16` on `0,…,3`, `3/4` on `∗`, `0` beyond) and
  `K^JS ρ = M^{-2}`;
* `π_{l,r}` values and `Σ_r π_{l,r} = 1 - 2^{-(l-2)}` at `l = 5`;
* on the valid one-round run `run1` on `K_3` (`R = 1`, three light pre-parts of round 1):
  `lentIdx = ∅`, `k_lend = 0`, the lent index is `none` (point mass), `k_own = 1`, no JS sites,
  no pool labels (`poolIdx = ∅`, mass `0`, `⊥` has probability `1`), no available parts for the
  zones (every vertex draws `none`), the marginals of the joint law, and COL(g) on its support;
* on a three-round choice list `run3` (`R = 3`; the Defs are total, validity is not needed): the
  round-1 ancestors have `JV 3 ∈ lentIdx`, `k_lend ≥ 1`, `poolIdx = {(3,1)}`, and
  `P(e ∈ LJV_{Y,3}) = p_Y`;
* generic facts: `T_j` disjoint, zones disjoint, pools disjoint, the stage-1 law is a
  probability distribution, and the independence lemmas instantiate;
* fix round 1: COL(g) on the support of `colLaw` and in the `μ.map D = colLaw` form, positivity
  of the zone label law (`0 < P(label(v) = (Y,i))` when `L_Y > 0`), the labels given the bits,
  and Own edges lie in no lent class;
* fix round 2: a non-degenerate pool law on `run3` (`P(plab = (3,1)) = q_3/2 > 0`), the support
  characterisation of the joint law (`mem_supp_law_iff`, `zone_mem_supp`, `pool_mem_supp`), the
  `zonePhase` characterisation, the own-class probability `1/(2k_own)`, the per-edge marginal and
  the mixed per-vertex independence shapes. -/

namespace EGTest.Stage1

open EG EG.HB EG.Stage1 EGTest.HB

/-! ## Tags and own labels -/

example : LentTag.JV 3 ≠ LentTag.JS 3 0 := by decide
example : LentTag.U 3 1 0 ≠ LentTag.U 3 2 0 := by decide

example : ((ownIdxOf 2) (some (1, 3)) : ℕ) = 7 := rfl
example : ((ownIdxOf 2) none : ℕ) = 8 := rfl
example : (ownIdxOf 2).symm ⟨8, by omega⟩ = none := by decide
example : (ownIdxOf 2).symm ⟨6, by omega⟩ = some (1, 2) := by decide
/-- With `J = 0` (tiny ancestors) the only own label is `M`. -/
example : (ownIdxOf 0).symm ⟨0, by omega⟩ = none := by decide

/-! ## JS label law -/

example : jsWeight 2 (some 3) = 1 / 16 := by norm_num [jsWeight]
example : jsWeight 2 (some 4) = 0 := by norm_num [jsWeight]
example : jsWeight 2 none = 3 / 4 := by norm_num [jsWeight]
example : ∑ o ∈ jsSupport 2, jsWeight 2 o = 1 := jsWeight_sum 2
/-- `M = 0` (junk) still gives a distribution: all mass on `∗`. -/
example : jsWeight 0 none = 1 := by norm_num [jsWeight]

/-! ## Pool weights -/

example : piPool 3 1 = 1 / 2 := by norm_num [piPool]
example : piPool 5 1 = 1 / 8 := by norm_num [piPool]
example : ∑ r ∈ (Finset.Icc 1 5).filter (fun r => r + 2 ≤ 5), piPool 5 r = 1 - 1 / 8 := by
  rw [sum_piPool 5 (by norm_num)]; norm_num

/-! ## The valid one-round run on `K_3` -/

theorem run1_R : run1.R = 1 := rfl

example : lateRounds run1 1 = ∅ := by decide

theorem lentIdx_run1 (Y : PartId) (hY : Y.1 = 1) : lentIdx K3 run1 Y = ∅ :=
  lentIdx_eq_empty_iff.2 (by rw [hY, run1_R]; norm_num)

example (Y : PartId) (hY : Y.1 = 1) : klend K3 run1 Y = 0 := by
  rw [klend_eq_card_lentIdx, lentIdx_run1 Y hY]; rfl

/-- `r ≥ R - 1`: the lent index is the point mass at `none`. -/
example (Y : PartId) (hY : Y.1 = 1) : idxLaw K3 run1 Y = FinDist.dirac none := by
  unfold idxLaw
  rw [dif_neg (by rw [lentIdx_run1 Y hY]; simp)]

/-- The parts of `run1` have one vertex, so `L_Y = 0`, `J_Y = 0` and `k_own = 1` (only `M`). -/
example (Y : PartId) (hY : (run1.ancVerts K3 Y).card = 1) : kown K3 run1 Y = 1 := by
  simp [kown, JY, hY, Vortex.pvJ, Vortex.L]

example (Y : PartId) (hY : Y.1 = 1) : jsSites K3 run1 Y = ∅ := by
  simp [jsSites, hY, lateRounds_eq_empty_iff, run1_R]

example : poolIdx run1 = ∅ := by decide

theorem poolMass_run1 : poolMass K3 run1 = 0 := by
  simp [poolMass, show poolIdx run1 = ∅ by decide]

example : (poolLabelLaw K3 run1).prob {none} = 1 := by
  rw [prob_poolLabelLaw_none K3 run1 (by rw [poolMass_run1]; norm_num), poolMass_run1]
  norm_num

theorem availParts_run1 (v : Fin 3) : availParts K3 run1 v = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro Y hY
  obtain ⟨hY, -, hR⟩ := Finset.mem_filter.1 hY
  have := Run.isRound_of_mem_parts run1 K3 (Finset.mem_filter.1 hY).1
  rw [run1_R] at hR
  omega

/-- No light part of round `≤ R - 2`: every vertex draws `choice(v) = none`. -/
example (v : Fin 3) : (zoneLabelLaw K3 run1 v).prob {none} = 1 := by
  have h0 : zpSum K3 run1 v = 0 := by simp [zpSum, availParts_run1]
  rw [prob_zoneLabelLaw_none K3 run1 (by rw [h0]; norm_num), h0]
  norm_num

/-- The stage-1 law is a probability distribution. -/
example : (law K3 run1).prob Set.univ = 1 := FinDist.prob_univ _

example : (law K3 run1).map Outcome.zone = zoneLaw K3 run1 := map_zone K3 run1
example : (law K3 run1).map Outcome.pool = poolLaw K3 run1 := map_pool K3 run1
example (Y : ↥(run1.ancestors K3)) :
    (law K3 run1).map (fun ω => ω.cOut Y) = colLaw K3 run1 Y := map_cOut K3 run1 Y

/-- COL(g) holds at every outcome of positive weight, for every ancestor of `run1`. -/
example (ω : Outcome K3 run1) (hω : ω ∈ (law K3 run1).supp) (Y : PartId)
    (hY : Y ∈ run1.ancestors K3) : COLg K3 run1 Y (ω.cOutAt Y) :=
  COLg_of_mem_supp_law K3 run1 hω hY

/-! ## A three-round choice list -/

/-- Three rounds (not a valid run; the Defs are total). -/
def run3 : Run (Fin 3) := ⟨[c1, default, default]⟩

theorem run3_R : run3.R = 3 := rfl

example : lateRounds run3 1 = {3} := by decide
example : poolIdx run3 = {(3, 1)} := by decide

example (Y : PartId) (hY : Y.1 = 1) : LentTag.JV 3 ∈ lentIdx K3 run3 Y :=
  mem_lentIdx.2 (Or.inr (Or.inr (JV_mem_IJV.2 (by rw [hY]; decide))))

example (Y : PartId) (hY : Y.1 = 1) : 0 < klend K3 run3 Y :=
  klend_pos_iff.2 (by rw [hY, run3_R])

example (Y : PartId) (hY : Y.1 = 2) : lentIdx K3 run3 Y = ∅ :=
  lentIdx_eq_empty_iff.2 (by rw [hY, run3_R]; norm_num)

/-- [s3:defCOL] "`p_Y` … is the probability that a fixed edge of `H_Y` lies in `LJV_{Y,l}`". -/
example (Y : PartId) (hY : Y.1 = 1) (e : ↥(run3.ancGraph K3 Y).edges) :
    (colouringLaw K3 run3 Y).prob {c | (e : Sym2 (Fin 3)) ∈ (LJV K3 run3 Y c 3).edges} =
      pY K3 run3 Y :=
  prob_mem_LJV K3 run3 Y (by rw [hY]; decide) e

/-- Fix round 2: the pool law of `run3` is not degenerate. `poolIdx run3 = {(3,1)}` has mass
`q_3 π_{3,1} ≤ 2^{-80}/2 ≤ 1`, and `P(plab = (3,1)) = q_3/2 > 0`. -/
theorem poolMass_run3_le : poolMass K3 run3 ≤ 1 := by
  rw [poolMass, show poolIdx run3 = {(3, 1)} by decide, Finset.sum_singleton]
  have h1 := qPool_le K3 run3 3
  have h2 : piPool 3 1 = 1 / 2 := by norm_num [piPool]
  rw [h2]
  have : (2 : ℝ) ^ (-80 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  linarith [qPool_pos K3 run3 3]

theorem pool_pos_run3 : 0 < (poolLabelLaw K3 run3).prob {some (3, 1)} := by
  rw [prob_poolLabelLaw_some K3 run3 poolMass_run3_le (by decide)]
  exact mul_pos (qPool_pos _ _ _) (piPool_pos _ _)

example : (poolLabelLaw K3 run3).prob {some (3, 1)} = qPool K3 run3 3 / 2 := by
  rw [prob_poolLabelLaw_some K3 run3 poolMass_run3_le (by decide)]
  norm_num [piPool]
  ring

/-- The own label `M` of `run3` has probability `1/(2k_own)` on a fixed edge. -/
example (Y : PartId) (e : ↥(run3.ancGraph K3 Y).edges) :
    (colouringLaw K3 run3 Y).prob {c | (e : Sym2 (Fin 3)) ∈ (ownM K3 run3 Y c).edges} =
      1 / (2 * (kown K3 run3 Y : ℝ)) :=
  prob_mem_ownM K3 run3 Y e

/-! ## Generic instances -/

section Generic

variable {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V)

example (Y : PartId) (lab : JSLabels G run Y) (l : ℕ) :
    Disjoint (Tj G run Y lab l 0) (Tj G run Y lab l 1) := disjoint_Tj G run Y lab l (by decide)

example (ζ : ↥G.verts → Option ZIdx) (Y : PartId) :
    Disjoint (Zone G run ζ Y (LentTag.U 3 0 0)) (Zone G run ζ Y (LentTag.U 3 1 0)) :=
  disjoint_Zone ζ (by simp)

example (π : ↥G.verts → Option (ℕ × ℕ)) : Disjoint (poolL G π 3) (poolL G π 4) :=
  disjoint_poolL π (by decide)

example (Y : ↥(run.ancestors G)) :
    (law G run).IndepFun (fun ω => ω.cOut Y) Outcome.zone := indepFun_cOut_zone G run Y

example : (law G run).IndepFun (fun ω => (ω.col, ω.zone, ω.js)) Outcome.pool :=
  indepFun_rest_pool G run

example : (law G run).iIndepFun fun (Y : ↥(run.ancestors G)) ω => ω.cOut Y := iIndepFun_cOut G run

/-- `T_j(Y,l)` is a `ρ_l`-random subset of `V(Y)`, `ρ_l = M_l^{-4}`. -/
example (Y : PartId) {l j : ℕ} (hl : l ∈ lateRounds run Y.1) (hj : j < KJS G run l) :
    (jsLaw G run Y).IsRSubset (fun lab => Tj G run Y lab l j) (run.ancVerts G Y)
      (rhoJS G run l) := isRSubset_Tj G run Y hl hj

example (l : ℕ) : (KJS G run l : ℝ) * rhoJS G run l = (run.M G l : ℝ) ^ (-2 : ℤ) :=
  KJS_mul_rhoJS G run l

/-! ### Fix round 1 (review M1, M4, M5) -/

/-- COL(g) holds at every outcome of positive weight of `colLaw` (support form of "Item (g)
always holds"). -/
example (Y : PartId) (ω : COLOut G run Y) (hω : ω ∈ (colLaw G run Y).supp) : COLg G run Y ω :=
  COLg_of_mem_supp_colLaw G run Y hω

/-- The hypothesis form of the lemCOL Specs: `μ.map D = colLaw` gives COL(g) at `D ω` for
`0 < μ.w ω`. -/
example (Y : PartId) {Ω : Type} (μ : FinDist Ω) (D : Ω → COLOut G run Y)
    (hD : μ.map D = colLaw G run Y) (ω : Ω) (hω : 0 < μ.w ω) : COLg G run Y (D ω) :=
  COLg_of_map_eq G run Y hD hω

/-- Non-vacuity of the zone law: a vertex lies in the zone `(Y, i)` with positive probability
`ρ_Y` when the guard holds, `Y` is available at `v`, `i ∈ I^U(Y)` and `L_Y > 0`. -/
example {v : V} (h : zpSum G run v ≤ 1) {Y : PartId} (hY : Y ∈ availParts G run v)
    {i : LentTag} (hi : i ∈ IU G run Y) (hL : 0 < run.LY G Y) :
    0 < (zoneLabelLaw G run v).prob {some (Y, i)} := by
  rw [prob_zoneLabelLaw_some G run h hY hi]
  have hIU : 0 < (IU G run Y).card := Finset.card_pos.2 ⟨i, hi⟩
  have hlight : run.isLight G Y.1 Y.2 := by
    simp only [availParts, Run.lightParts, Finset.mem_filter] at hY; exact hY.1.2
  have hR : Y.1 + 2 ≤ run.R := by
    simp only [availParts, Finset.mem_filter] at hY; exact hY.2.2
  rw [rhoY_eq_zp_div_card G run hlight hR]
  unfold zp
  positivity

/-- Given the bits, the own labels of the own edges are a uniform `k_own`-colouring and the
indices of the lent edges are independent with law `idxLaw` (COL-RANDOM-EDGESET). -/
example (Y : PartId) (β : ↥(run.ancGraph G Y).edges → Bool)
    (hβ : 0 < (colouringLaw G run Y).prob (edgeBits G run Y ⁻¹' {β})) :
    ((colouringLaw G run Y).cond (edgeBits G run Y ⁻¹' {β}) hβ).map
        (fun c (e : {e // β e = false}) => (c e).2.2) =
      FinDist.randColouring {e // β e = false} (kown G run Y) ∧
    ((colouringLaw G run Y).cond (edgeBits G run Y ⁻¹' {β}) hβ).map
        (fun c (e : {e // β e = true}) => (c e).2.1) =
      FinDist.pi fun _ : {e // β e = true} => idxLaw G run Y :=
  ⟨map_own_cond_edgeBits G run Y β hβ, map_idx_cond_edgeBits G run Y β hβ⟩

/-- An edge with bit `false` (an Own edge) is in no lent class, whatever its index. -/
example (Y : PartId) (c : Colouring G run Y) (e : ↥(run.ancGraph G Y).edges) (i : LentTag)
    (hb : (c e).1 = false) : (e : Sym2 V) ∉ (lentClass G run Y c i).edges := by
  intro h
  rw [mem_lentClass_edges] at h
  obtain ⟨he, h⟩ := h
  simp_all

/-! ### Fix round 2: support, zonePhase, own class, mixed shapes -/

example (ω : Outcome G run) :
    ω ∈ (law G run).supp ↔ ∀ c, ω.toCoords c ∈ (coordLaw G run c).supp :=
  mem_supp_law_iff G run ω

example {ω : Outcome G run} (hω : ω ∈ (law G run).supp) (v : ↥G.verts) :
    ω.zone v = none ∨
      ∃ Y i, ω.zone v = some (Y, i) ∧ Y ∈ availParts G run v ∧ i ∈ IU G run Y :=
  zone_mem_supp G run hω v

example {ω : Outcome G run} (hω : ω ∈ (law G run).supp) (v : ↥G.verts) :
    ω.pool v = none ∨ ∃ l r, ω.pool v = some (l, r) ∧ (l, r) ∈ poolIdx run :=
  pool_mem_supp G run hω v

/-- On the support, a JS-tagged zone is empty (zones carry U-sublabels only). -/
example {ω : Outcome G run} (hω : ω ∈ (law G run).supp) (Y : PartId) (l j : ℕ) :
    Zone G run ω.zone Y (LentTag.JS l j) = ∅ :=
  Zone_eq_empty_of_not_mem_IU G run hω (by simp [mem_IU])

/-- [s5:defZones] "Equivalently, …". -/
example {ω : Outcome G run} (hω : ω ∈ (law G run).supp) (l : ℕ) (v : V) (c : Fin 4) :
    zonePhase ω.zone l v = some c ↔ ∃ Y σ, v ∈ Zone G run ω.zone Y (LentTag.U l c σ) :=
  zonePhase_eq_some_iff_mem_Zone G run hω l v c

example (Y : ↥(run.ancestors G)) (e : ↥(run.ancGraph G Y).edges) :
    (law G run).map (fun ω => ω.col Y e) = edgeLaw G run Y :=
  map_col_apply G run Y e

example (Y : PartId) (e : ↥(run.ancGraph G Y).edges) (o : Fin (kown G run Y)) :
    (colouringLaw G run Y).prob {c | (e : Sym2 V) ∈ (ownClass G run Y c o).edges} =
      1 / (2 * (kown G run Y : ℝ)) :=
  prob_mem_ownClass G run Y e o

example (Y : ↥(run.ancestors G)) (u : V) :
    (law G run).iIndepFun
      (fun (w : {w : ↥G.verts // s(u, (w : V)) ∈ (run.ancGraph G Y).edges}) (ω : Outcome G run) =>
        (ω.col Y ⟨s(u, (w.1 : V)), w.2⟩, ω.pool w.1)) :=
  iIndepFun_edge_pool G run Y u

example (Y : ↥(run.ancestors G)) (w : V) :
    (law G run).iIndepFun
      (fun (u : {u : ↥G.verts // s(w, (u : V)) ∈ (run.ancGraph G Y).edges}) (ω : Outcome G run) =>
        (ω.col Y ⟨s(w, (u.1 : V)), u.2⟩, ω.zone u.1)) :=
  iIndepFun_edge_zone G run Y w

example (l : ℕ) : 0 < qPool G run l ∧ qPool G run l ≤ 2 ^ (-80 : ℤ) :=
  ⟨qPool_pos G run l, qPool_le G run l⟩

end Generic

end EGTest.Stage1
