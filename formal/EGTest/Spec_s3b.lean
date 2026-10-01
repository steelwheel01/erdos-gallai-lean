import EG.Spec.Link.L9rho
import EG.Spec.Link.HB
import EG.Spec.Link.T16sForced
import EG.Spec.Lend.COLJV
import EG.Spec.Lend.COLJVev
import EG.Spec.Stage1.COL
import EG.Lib.HB.Run
import EG.Lib.Stage1.COL
import EG.Lib.Gamma.Col3
import EG.Proof.Gamma.Sat

/-! Cheap non-vacuity checks for the s3b Specs written by the P2 s3b Spec unit
(`EG/Spec/Link/{L9rho, HB, T16sForced}.lean`, `EG/Spec/Lend/{COLJV, COLJVev}.lean`,
`EG/Spec/Stage1/COL.lean`; `formal/work/p2s/s3b.md`).

* `L9rhoStatement`: its hypotheses (before the ball condition) hold for the edgeless graph on
  `2^{30}` vertices with `W = V(G)`, `ρ = t = 1`.
* `HBStatement`: its conclusion `IsHBFamily` is satisfiable (the one-edge graph on `Fin 2`, `m = 1`,
  `b = 1`, `A w = N(w)`), and fails for `m = 2` there (so `|A(w)| = m` is not vacuous).
* `COLJVevTypeEStatement`: hypotheses satisfiable (`a = 1`, `b = c = 0`); `COLJVevRowsStatement`:
  the hypothesis `TypeE (triple i) μ` holds for row 4 at `μ = 10`, and `row 4` is the column-3
  inequality (not the junk `True`).
* `COLJVStatement` / `COLStatement`: the common hypotheses `Gamma1 D ∧ run.Valid G D` are
  satisfiable (the run without rounds on an edgeless graph, `D` from `EG.gammaSat`); on that run
  there is no ancestor, so this checks only the hypotheses. The item-(g) conjunct of
  `COLStatement` is already a theorem (`EG.Stage1.COLg_of_mem_supp_colLaw`), and the law
  hypothesis `μ.map D = colLaw` is satisfiable (`μ = colLaw`, `D = id`).
* The conjunctions `COLJVStatement`, `COLJVevStatement`, `COLLemmaStatement` elaborate and project
  to their parts.
* Fix-round bridges: `run.Valid` gives `D_* ≤ d_1` once an ancestor exists; for an ancestor,
  `Y ∈ run.lightParts G ↔ run.isLight G Y.1 Y.2`; `⌈2mL^2/2^{-6}⌉₊ = Vortex.pvB N` at `m = pvM N`.

Not checked: the expander hypotheses of `HBStatement` and `T16sForcedStatement` (no cheap
explicit expander with `N ≥ 2` in the library), and the ball condition of `L9rhoStatement`.
-/

namespace EGTest.Spec_s3b

open EG EG.HB Filter

/-! ### Lemma 9_ρ -/

/-- The edgeless graph on `2^{30}` vertices. -/
def Gbig : FGraph (Fin (2 ^ 30)) := FGraph.ofEdges Finset.univ ∅

theorem Gbig_card : Gbig.card = 2 ^ 30 := by
  simp [Gbig, FGraph.card, FGraph.ofEdges]

/-- The hypotheses of `L9rhoStatement` before the ball condition are satisfiable. -/
example :
    2 ^ 30 ≤ Gbig.card ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧ Gbig.verts ⊆ Gbig.verts ∧
      (1 : ℝ) * (Gbig.card : ℝ) / 2 ≤ (Gbig.verts.card : ℝ) ∧ 84 ≤ (1 : ℝ) * (Gbig.card : ℝ) := by
  have h : (Gbig.verts.card : ℝ) = (Gbig.card : ℝ) := rfl
  refine ⟨Gbig_card.ge, by norm_num, le_rfl, le_rfl, subset_rfl, ?_, ?_⟩
  · rw [h, one_mul]
    have : (0 : ℝ) ≤ Gbig.card := Nat.cast_nonneg _
    linarith
  · rw [Gbig_card]; norm_num

/-! ### Lemma HB -/

/-- The graph on `Fin 2` with one edge. -/
def K2 : FGraph (Fin 2) := FGraph.ofEdges Finset.univ {s(0, 1)}

/-- The conclusion `IsHBFamily` of Lemma HB is satisfiable. -/
example : IsHBFamily K2 1 1 K2.nbrs := by
  refine ⟨fun w _ => ⟨subset_rfl, ?_⟩, fun u => ?_⟩
  · revert w; decide
  · revert u; decide

/-- … and `|A(w)| = m` is not vacuous: no family with `m = 2` exists on `K2`. -/
example (A : Fin 2 → Finset (Fin 2)) : ¬ IsHBFamily K2 2 5 A := by
  rintro ⟨h, -⟩
  obtain ⟨hsub, hcard⟩ := h 0 (by decide)
  have : (K2.nbrs 0).card ≤ 1 := by decide
  have := Finset.card_le_card hsub
  omega

/-! ### Lemma COL-JV-ev -/

example : (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0 := by norm_num

/-- The hypothesis of (ii) for row 4 holds at `μ = 10`. -/
example : COLTable.TypeE (COLTable.triple 4).1 (COLTable.triple 4).2.1 (COLTable.triple 4).2.2 10 := by
  simp only [COLTable.TypeE, COLTable.triple]
  norm_num

/-- Row 4 is the column-3 inequality, not the junk value. -/
example (μ : ℝ) :
    COLTable.row 4 μ ↔ (2 : ℝ) ^ 193 * 12 ^ 5 ≤ COLTable.lam μ ^ (421 / 10 : ℝ) := Iff.rfl

/-- The conclusion of (ii) is satisfiable at a large `μ` (column 3 holds on a ray). -/
example : ∀ i : ℕ, 1 ≤ i → i ≤ 13 → COLTable.row i ((2 : ℝ) ^ 40) :=
  COLTable.col3_of_le le_rfl

/-! ### Lemma COL-JV and Lemma COL: the common hypotheses -/

/-- The edgeless graph on `Fin 2`. -/
def E2 : FGraph (Fin 2) := FGraph.ofEdges Finset.univ ∅

/-- `Gamma1 D ∧ run.Valid G D` is satisfiable (the run without rounds on `E2`). -/
example : ∃ D : ℝ, Gamma1 D ∧ (⟨[]⟩ : Run (Fin 2)).Valid E2 D := by
  obtain ⟨D, hD, hpos⟩ :=
    (((gammaSat 0).mono fun _ h => h.1).and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨D, hD, ?_⟩
  rw [Run.valid_nil_iff]
  simpa [Round.d, E2, FGraph.ofEdges] using hpos

/-- The law hypothesis of `COLStatement` is satisfiable, and its item-(g) conjunct is a
theorem of the Stage-1 library. -/
example {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V) (Y : PartId) :
    (Stage1.colLaw G run Y).map id = Stage1.colLaw G run Y ∧
      ∀ ω ∈ (Stage1.colLaw G run Y).supp, Stage1.COLg G run Y ω :=
  ⟨FinDist.map_id _, fun _ hω => Stage1.COLg_of_mem_supp_colLaw G run Y hω⟩

/-! ### Fix-round bridges (review items of `formal/work/p2s/s3b.md`, "Fix round") -/

/-- Item 1: the extra hypothesis `D_* ≤ d_1` of `COLcStatement` / `COLaProbStatement` is implied
by `run.Valid` as soon as an ancestor (in particular a light part) exists. -/
example {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V) (Dstar : ℝ)
    (hv : run.Valid G Dstar) {Y : PartId} (hY : Y ∈ run.ancestors G) : Dstar ≤ run.d G 1 := by
  have hr := Run.isRound_of_mem_parts run G hY
  exact (hv.1 1 (Finset.mem_Icc.2 ⟨le_rfl, le_trans hr.1 hr.2⟩)).1

/-- Item 2: for an ancestor, the light guard `Y ∈ run.lightParts G` (used by `COLStatement` and
`COLcStatement`) is `run.isLight G Y.1 Y.2`. -/
example {V : Type} [DecidableEq V] (G : FGraph V) (run : Run V) {Y : PartId}
    (hY : Y ∈ run.ancestors G) : Y ∈ run.lightParts G ↔ run.isLight G Y.1 Y.2 := by
  rw [Run.mem_lightParts, ← Run.mem_ancestors]
  exact ⟨fun h => h.2, fun h => ⟨hY, h⟩⟩

/-- Item 4: at `ε' = 2^{-6}` and `m = ⌈L^6⌉` the bound `⌈2mL^2/ε'⌉₊` of `HBStatement` is the
`b = ⌈2^7L^2m⌉₊` of s4:lemPV / s5:defStages (`Vortex.pvB`, `Light.vb`). -/
example (N : ℕ) :
    ⌈2 * (Vortex.pvM N : ℝ) * Real.logb 2 (N : ℝ) ^ 2 / (2 : ℝ) ^ (-6 : ℤ)⌉₊ = Vortex.pvB N := by
  unfold Vortex.pvB Vortex.L
  congr 1
  rw [zpow_neg, div_inv_eq_mul]
  norm_num
  ring

/-! ### The conjunctions elaborate and project -/

example (h : Spec.COLJVStatement.{0}) : Spec.COLJVCountStatement.{0} ∧ Spec.COLJVRow13Statement.{0} :=
  ⟨h.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

example (h : Spec.COLJVevStatement) : Spec.COLJVevRowsStatement := h.2.1

example (h : Spec.COLLemmaStatement.{0, 0}) : Spec.COLcStatement.{0, 0} := h.2

example : Spec.L9rhoStatement.{0} ↔ Spec.L9rhoStatement.{0} := Iff.rfl
example : Spec.HBStatement.{0} ↔ Spec.HBStatement.{0} := Iff.rfl
example : Spec.T16sForcedStatement.{0} ↔ Spec.T16sForcedStatement.{0} := Iff.rfl

end EGTest.Spec_s3b
