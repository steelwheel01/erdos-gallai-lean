module

public import EG.Defs.Quot.Cand
public import EG.Lib.Stage1.Pool
public import EG.Lib.Chain.StageInst

/-!
# API for candidates and JV-bad ports (s7:defCand)

Characterization lemmas for `EG.Quot.cand`, `EG.Quot.JVBad`, `EG.Quot.Hcd` (design note
`formal/work/p2d/quot.md`).
-/

public section

namespace EG.Quot

open EG.HB EG.Chain

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

theorem HcdOf_def (M : ℕ) (lam : ℝ) : HcdOf M lam = lam ^ 95 / (8 * (M : ℝ) ^ 2) := rfl

theorem Hcd_def (l : ℕ) : Hcd run G l = run.lam G (l - 2) ^ 95 / (8 * (run.M G l : ℝ) ^ 2) :=
  rfl

theorem thult_def (l : ℕ) : thult run G l = ⌊(run.M G l : ℝ) * Hcd run G l / 7⌋₊ := rfl

variable {run G δ S}

theorem mem_cand {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {u w : V} :
    w ∈ cand G δ S π l u ↔
      w ∈ Stage1.poolSet G π l (δ l u).1 ∧ s(u, w) ∈ S.ljv (δ l u) l :=
  Finset.mem_filter

/-- "`Cand_l(u) ⊆ Pool_{l,r(u)}`". -/
theorem cand_subset_poolSet (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (u : V) :
    cand G δ S π l u ⊆ Stage1.poolSet G π l (δ l u).1 :=
  Finset.filter_subset _ _

/-- For a class of round `1 ≤ r(u)` with `r(u) + 2 ≤ l`: `Cand_l(u) ⊆ Pool_l`. -/
theorem cand_subset_poolL (π : ↥G.verts → Option (ℕ × ℕ)) {l : ℕ} {u : V}
    (h1 : 1 ≤ (δ l u).1) (h2 : (δ l u).1 + 2 ≤ l) :
    cand G δ S π l u ⊆ Stage1.poolL G π l := by
  intro w hw
  have hw' := (Stage1.mem_poolSet).1 (cand_subset_poolSet π l u hw)
  exact Stage1.mem_poolL.2 ⟨hw'.1, _, h1, h2, hw'.2⟩

/-- [s7:defCand] "Since `LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)` …, automatically `Cand_l(u) ⊆ N_{H_Y}(u)`"
(for stage data of a stage-1 outcome, `StageData.Coherent`). -/
theorem cand_subset_nbrs (hS : S.Coherent run G) (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ)
    (u : V) : cand G δ S π l u ⊆ (run.ancGraph G (δ l u)).nbrs u := by
  intro w hw
  have he : s(u, w) ∈ (run.ancGraph G (δ l u)).edges := hS.ljv_sub _ _ (mem_cand.1 hw).2
  rw [FGraph.nbrs, Finset.mem_filter]
  exact ⟨(run.ancGraph G (δ l u)).edge_verts _ he w (Sym2.mem_mk_right u w), he⟩

/-- "`N_{H_Y}(u) ⊆ V(Y)`": candidates are vertices of the class graph. -/
theorem cand_subset_verts (hS : S.Coherent run G) (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ)
    (u : V) : cand G δ S π l u ⊆ (run.ancGraph G (δ l u)).verts := fun _ hw =>
  (Finset.mem_filter.1 (cand_subset_nbrs hS π l u hw)).1

/-- Only classed ports of round `l` are JV-bad. -/
theorem JVBad.mem_classedPorts {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {u : V}
    (h : JVBad run G δ S π l u) : u ∈ classedPorts run G l := h.1

/-- JV-good classed ports: `|Cand_l(u)| ≥ ½ E|Cand_l(u)|`. -/
theorem not_JVBad_iff {π : ↥G.verts → Option (ℕ × ℕ)} {l : ℕ} {u : V}
    (hu : u ∈ classedPorts run G l) :
    ¬ JVBad run G δ S π l u ↔ candMean run G δ l u / 2 ≤ ((cand G δ S π l u).card : ℝ) := by
  simp [JVBad, hu]

end EG.Quot
