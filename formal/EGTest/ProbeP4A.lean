import EG.Spec.Vortex.Observations
import EG.Spec.Vortex.PVCore
import EG.Spec.Vortex.PV
import EG.Spec.Ext.Cor22
import EG.Spec.HB.TowerB
import EG.Spec.Lend.COLJVCount
import EG.Spec.Lend.COLJVRows
import EG.Lib.Vortex.Params
import EG.Lib.Found.PathDecomp

/-! Non-vacuity checks for the statements of probe unit P4A (probe P-4, part 1; design note
`formal/work/p2b/P4A.md`). On small instances on `Fin n`:
* the hypotheses of `PVStepPhaseStatement` hold, and so does its conclusion, with the output of
  steps (iv)–(vi) computed by hand (one path `01`, one retiring vertex `0`, far ends `2`, `3`:
  the trail `2 0 1` becomes an arc, `03` a single edge);
* the hypotheses and a conclusion witness of `PVStripStatement` (the path `p x q` with `x`
  rooted: two stripped edges, nothing left);
* the inequality `pec ≤ deg_{H_0}` of `PVArcEndsDegStatement` is attained: a star at `0` on
  `Fin 5` split into four one-edge arcs has `4 = deg(0) = |Z| - 1` arcs ending at `0`. (This is an
  abstract path decomposition, not an output of the PV procedure; it shows only that the
  inequality can be an equality.)
* the finish-stripping scenario of CR1-PV (fix round 1, m1): the Corollary-22 paths `p_i 0 y_i`
  (`p_i ∈ Pl_J = {1,2,3}`, `0, y_i ∈ Rt`) have no end at the rooted vertex `0`, yet stripping them
  (`PVStripStatement`, one witness per path) leaves three arcs `0 y_i`, all ending at `0`. So the
  arc ends at a vertex are not bounded by its Corollary-22 end count; the degree bound of
  `PVArcEndsDegStatement` covers them (`3 ≤ deg_{H_0}(0) = 6`);
* the hypotheses of `Cor22Statement`, `PathEndsCountStatement`, `ClosingStatement`,
  `TrailSplitStatement` on small lists;
* the size hypothesis of `PVFinishStatement` at `N = 2^{1024}` (`L = 1024`).
Not cheap (recorded in the design note): the hypotheses `PVHyp` of Lemma PV (expanders with
`s' ≥ 2^{145}L^{41}` on `N ≥ 2^{1024}` vertices) and `Gamma1 D ∧ run.Valid G D` with an ancestor
(the rows of the COL-JV table), which need astronomically large graphs. -/

namespace EGTest.ProbeP4A

open EG

/-! ## One phase of a PV step -/

section StepPhase

/-- `Rt = {1,2,3}`, `W = {0}`, `Up = ∅`, `F = {01}`, `P = [[0,1]]`, far ends `u₁ 0 = 2`,
`u₂ 0 = 3`. -/
abbrev Rt : Finset (Fin 4) := {1, 2, 3}
abbrev W : Finset (Fin 4) := {0}
abbrev Up : Finset (Fin 4) := ∅
abbrev F : Finset (Sym2 (Fin 4)) := {s(0, 1)}
abbrev P : List (List (Fin 4)) := [[0, 1]]
abbrev u₁ : Fin 4 → Fin 4 := fun _ => 2
abbrev u₂ : Fin 4 → Fin 4 := fun _ => 3

theorem isPathDecomp_F : IsPathDecomp (F : Set (Sym2 (Fin 4))) P := by
  refine ⟨by decide, by decide, ?_⟩
  intro e
  simp [walkEdges]

example : Disjoint Rt W ∧ Disjoint Rt Up ∧ Disjoint W Up := by decide

example : (∀ e ∈ F, ¬ e.IsDiag) ∧ (∀ e ∈ F, ∀ v ∈ e, v ∈ Rt ∪ W ∪ Up) ∧
    (∀ e ∈ F, ∃ w ∈ W, w ∈ e) := by decide

example : ∀ v, pathEndCount P v ≤ 2 := by decide

example : ∀ w ∈ W, u₁ w ≠ u₂ w ∧ u₁ w ∈ Rt ∪ Up ∧ u₂ w ∈ Rt ∪ Up ∧
    s(w, u₁ w) ∉ F ∧ s(w, u₂ w) ∉ F := by decide

/-- The conclusion of `PVStepPhaseStatement` on this instance: `D = [03]` (the single edge
`e^{c,2}_0`), the arc `2 0 1` (the trail from appending `e^{c,1}_0 = 02` at `0`; both ends rooted,
not a cherry), no path to close. -/
example :
    let D : List (Obj (Fin 4)) := [.edge s(0, 3)]
    let A : List (List (Fin 4)) := [[2, 0, 1]]
    let Q : List (List (Fin 4)) := []
    (∀ o ∈ D, o.WF) ∧
    (D.flatMap Obj.edges ++ A.flatMap walkEdges ++ Q.flatMap walkEdges).Nodup ∧
    (∀ e, e ∈ D.flatMap Obj.edges ++ A.flatMap walkEdges ++ Q.flatMap walkEdges ↔
      e ∈ F ∨ ∃ w ∈ W, e = s(w, u₁ w) ∨ e = s(w, u₂ w)) ∧
    (∀ a ∈ A, a.Nodup ∧ 2 ≤ a.length ∧ (∃ x ∈ Rt, a.head? = some x) ∧
      (∃ y ∈ Rt, a.getLast? = some y) ∧
      ∀ x ∈ a, (∃ e ∈ F, x ∈ e) ∨ ∃ w ∈ W, x = u₁ w ∨ x = u₂ w) ∧
    A.length ≤ P.length ∧
    (∀ v, pathEndCount Q v ≤ 2 + (W.filter fun w => v = u₁ w ∨ v = u₂ w).card) ∧
    D.length + Q.length ≤ W.card + 3 * (2 * W.card + 2 * Up.card) := by
  intro D A Q
  refine ⟨?_, by decide, ?_, by decide, by decide, by decide, by decide⟩
  · intro o ho
    simp only [D, List.mem_singleton] at ho
    subst ho
    show ¬ s((0 : Fin 4), 3).IsDiag
    decide
  · intro e
    revert e
    decide

end StepPhase

/-! ## Stripping -/

section Strip

/-- `T = p x q = 0 1 2` with `Rt = {1}`, `Pl_J = {0, 2}`: both end edges are stripped and nothing
is left (`T' = [1]`). -/
example : Disjoint ({1} : Finset (Fin 3)) {0, 2} ∧ ([0, 1, 2] : List (Fin 3)).Nodup ∧
    (∀ x ∈ ([0, 1, 2] : List (Fin 3)), x ∈ ({1} : Finset (Fin 3)) ∪ {0, 2}) ∧
    (∀ e ∈ walkEdges ([0, 1, 2] : List (Fin 3)), ∃ x ∈ ({1} : Finset (Fin 3)), x ∈ e) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [walkEdges]

example :
    List.Perm ([s(0, 1), s(1, 2)] ++ walkEdges ([1] : List (Fin 3)))
      (walkEdges ([0, 1, 2] : List (Fin 3))) ∧
    [s((0 : Fin 3), 1), s(1, 2)].length ≤
      (({0, 2} : Finset (Fin 3)).filter fun p =>
        ([0, 1, 2] : List (Fin 3)).head? = some p ∨ ([0, 1, 2] : List (Fin 3)).getLast? = some p).card ∧
    ([1] : List (Fin 3)).IsInfix [0, 1, 2] ∧ ([1] : List (Fin 3)).length ≤ 1 := by
  refine ⟨by simp [walkEdges], by decide, ⟨[0], [2], rfl⟩, by decide⟩

end Strip

/-! ## The per-vertex bound of Lemma PV (c) is attained -/

section ArcEnds

/-- The star at `0` on `Fin 5`. -/
abbrev star : Finset (Sym2 (Fin 5)) := {s(0, 1), s(0, 2), s(0, 3), s(0, 4)}
abbrev starArcs : List (List (Fin 5)) := [[1, 0], [2, 0], [3, 0], [4, 0]]

theorem isPathDecomp_star : IsPathDecomp (star : Set (Sym2 (Fin 5))) starArcs := by
  refine ⟨by decide, by decide, ?_⟩
  intro e
  simp only [Finset.mem_coe]
  revert e
  decide

/-- Hypotheses of `PVArcEndsDegStatement` with `Z = Fin 5`, `H_0 = H^arc = star`. -/
example : (∀ e ∈ star, ¬ e.IsDiag) ∧ (∀ e ∈ star, ∀ v ∈ e, v ∈ (Finset.univ : Finset (Fin 5))) ∧
    star ⊆ star := by
  refine ⟨by decide, by simp, subset_rfl⟩

/-- Attained: `0` is an end of `4 = deg_{H_0}(0) = |Z| - 1` arcs. This star is an abstract path
decomposition, not a PV output: it shows only that `pec ≤ deg_{H_0}` can be an equality. -/
example : pathEndCount starArcs 0 = 4 ∧ degE star 0 = 4 ∧
    (Finset.univ : Finset (Fin 5)).card - 1 = 4 := by
  refine ⟨by decide, by decide, by simp⟩

end ArcEnds

/-! ## The finish-stripping scenario of CR1-PV (fix round 1, m1)

Manuscript (proof of (c)): "That count misses the arcs left by stripping in the finish: such an
arc can end at a vertex `x ∈ Rt` that is an interior vertex of its Corollary-22 path, and
Corollary 22 does not limit the number of such paths at `x`." On `Fin 7`: `Rt = {0,4,5,6}`,
`Pl_J = {1,2,3}`, one phase with `E_2 = {10, 04, 20, 05, 30, 06}` and the Corollary-22
decomposition `[1 0 4], [2 0 5], [3 0 6]`, in which `0` is an end of no path. Stripping each path
at its end in `Pl_J` leaves the arcs `[0 4], [0 5], [0 6]`, all ending at `0`. -/

section StripScenario

abbrev RtS : Finset (Fin 7) := {0, 4, 5, 6}
abbrev PlJS : Finset (Fin 7) := {1, 2, 3}
abbrev E2S : Finset (Sym2 (Fin 7)) :=
  {s(1, 0), s(0, 4), s(2, 0), s(0, 5), s(3, 0), s(0, 6)}
abbrev pathsS : List (List (Fin 7)) := [[1, 0, 4], [2, 0, 5], [3, 0, 6]]
abbrev arcsS : List (List (Fin 7)) := [[0, 4], [0, 5], [0, 6]]
abbrev HarcS : Finset (Sym2 (Fin 7)) := {s(0, 4), s(0, 5), s(0, 6)}

/-- The Corollary-22 decomposition of `E_2`: a path decomposition with every vertex an end of at
most two paths, and `0` an end of none of them. -/
theorem isPathDecomp_E2S : IsPathDecomp (E2S : Set (Sym2 (Fin 7))) pathsS := by
  refine ⟨by decide, by decide, ?_⟩
  intro e
  simp only [Finset.mem_coe]
  revert e
  decide

example : (∀ v, pathEndCount pathsS v ≤ 2) ∧ pathEndCount pathsS 0 = 0 := by
  refine ⟨by decide, by decide⟩

/-- The hypotheses of `PVStripStatement` hold for every path of the decomposition. -/
example : Disjoint RtS PlJS ∧
    ∀ T ∈ pathsS, T.Nodup ∧ 2 ≤ T.length ∧ (∀ x ∈ T, x ∈ RtS ∪ PlJS) ∧
      (∀ e ∈ walkEdges T, ∃ x ∈ RtS, x ∈ e) := by
  refine ⟨by decide, ?_⟩
  intro T hT
  simp only [pathsS, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl <;>
    refine ⟨by decide, by decide, by decide, ?_⟩ <;>
    simp [walkEdges]

/-- The conclusion of `PVStripStatement` for the path `p 0 y` (`p ∈ Pl_J`, `y ∈ Rt`): strip the
edge `p0` and keep the arc `0 y`, with both ends in `Rt`. -/
theorem strip_witness (p y : Fin 7) (hp : p ∈ PlJS) (hy : y ∈ RtS) :
    List.Perm ([s(p, 0)] ++ walkEdges [0, y]) (walkEdges [p, 0, y]) ∧
    [s(p, 0)].length ≤ (PlJS.filter fun q =>
      ([p, 0, y] : List (Fin 7)).head? = some q ∨ ([p, 0, y] : List (Fin 7)).getLast? = some q).card ∧
    ([0, y] : List (Fin 7)).IsInfix [p, 0, y] ∧
    (([0, y] : List (Fin 7)).length ≤ 1 ∨
      (2 ≤ ([0, y] : List (Fin 7)).length ∧ (∃ x ∈ RtS, ([0, y] : List (Fin 7)).head? = some x) ∧
        ∃ z ∈ RtS, ([0, y] : List (Fin 7)).getLast? = some z)) := by
  refine ⟨by simp [walkEdges], ?_, ⟨[p], [], rfl⟩, Or.inr ⟨by simp, ⟨0, by decide, rfl⟩, ⟨y, hy, rfl⟩⟩⟩
  have : p ∈ PlJS.filter fun q =>
      ([p, 0, y] : List (Fin 7)).head? = some q ∨ ([p, 0, y] : List (Fin 7)).getLast? = some q := by
    simp only [Finset.mem_filter]
    exact ⟨hp, Or.inl rfl⟩
  simpa using Finset.card_pos.mpr ⟨p, this⟩

/-- The three strip witnesses (`p 0 y` = `1 0 4`, `2 0 5`, `3 0 6`). -/
example : (∀ py ∈ ([(1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)), py.1 ∈ PlJS ∧ py.2 ∈ RtS) ∧
    pathsS = ([(1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)).map (fun py => [py.1, 0, py.2]) ∧
    arcsS = ([(1, 4), (2, 5), (3, 6)] : List (Fin 7 × Fin 7)).map (fun py => [0, py.2]) :=
  ⟨by decide, rfl, rfl⟩

example := strip_witness 1 4 (by decide) (by decide)
example := strip_witness 2 5 (by decide) (by decide)
example := strip_witness 3 6 (by decide) (by decide)

/-- The arcs left by stripping decompose `H^arc = {04, 05, 06}`, and the edges stripped plus the
arc edges are exactly `E_2`. -/
theorem isPathDecomp_arcsS : IsPathDecomp (HarcS : Set (Sym2 (Fin 7))) arcsS := by
  refine ⟨by decide, by decide, ?_⟩
  intro e
  simp only [Finset.mem_coe]
  revert e
  decide

example : HarcS ⊆ E2S ∧ E2S \ HarcS = {s(1, 0), s(2, 0), s(3, 0)} := by
  refine ⟨by decide, by decide⟩

/-- The rooted vertex `0` is an end of three arcs but of no Corollary-22 path; the degree bound
of `PVArcEndsDegStatement` (`H_0 = E_2`, `Z = Fin 7`) covers it: `3 ≤ deg_{H_0}(0) = 6 ≤ |Z| - 1`. -/
example : pathEndCount arcsS 0 = 3 ∧ pathEndCount pathsS 0 = 0 ∧ degE E2S 0 = 6 ∧
    (Finset.univ : Finset (Fin 7)).card - 1 = 6 := by
  refine ⟨by decide, by decide, by decide, by simp⟩

/-- The hypotheses of `PVArcEndsDegStatement` on this instance. -/
example : (∀ e ∈ E2S, ¬ e.IsDiag) ∧ (∀ e ∈ E2S, ∀ v ∈ e, v ∈ (Finset.univ : Finset (Fin 7))) ∧
    HarcS ⊆ E2S := by
  refine ⟨by decide, by simp, by decide⟩

end StripScenario

/-! ## Observations and Corollary 22: hypotheses on small instances -/

/-- `PathEndsCountStatement` / `Cor22Statement` input: the path `0 1 2` decomposes `{01, 12}`,
each vertex an end of at most one path, all ends in `W = {0,1,2}`. -/
example : IsPathDecomp (({s(0, 1), s(1, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))
      [[0, 1, 2]] ∧ (∀ v, pathEndCount ([[0, 1, 2]] : List (List (Fin 3))) v ≤ 2) := by
  refine ⟨⟨by decide, by decide, ?_⟩, by decide⟩
  intro e
  simp [walkEdges]

/-- `ClosingStatement` input: `Q = 0 1 2` (length 2) and `Q' = 0 3 2`. -/
example : ([0, 1, 2] : List (Fin 4)).Nodup ∧ 2 ≤ pathLength ([0, 1, 2] : List (Fin 4)) ∧
    ([0, 3, 2] : List (Fin 4)).Nodup ∧
    (∀ v ∈ interior ([0, 3, 2] : List (Fin 4)), v ∉ ([0, 1, 2] : List (Fin 4))) ∧
    (walkEdges ([0, 1, 2] : List (Fin 4))).Disjoint (walkEdges [0, 3, 2]) ∧
    (Obj.cycle (([0, 1, 2] : List (Fin 4)) ++ (interior ([0, 3, 2] : List (Fin 4))).reverse)).WF := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · unfold List.Disjoint
    decide
  show List.Nodup _ ∧ 3 ≤ List.length _
  decide

/-- `TrailSplitStatement` input: the trail `0 1 2 0 3` (a triangle and a pendant edge) in
`K_4`; `rep = 5 - 4 = 1`. -/
example : (walkEdges ([0, 1, 2, 0, 3] : List (Fin 4))).Nodup ∧
    (∀ e ∈ walkEdges ([0, 1, 2, 0, 3] : List (Fin 4)), ¬ e.IsDiag) ∧
    ([0, 1, 2, 0, 3] : List (Fin 4)).length - ([0, 1, 2, 0, 3] : List (Fin 4)).toFinset.card = 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## The size hypothesis of the finish -/

/-- `2^{10} ≤ L(2^{1024})` (`L = 1024`), the size hypothesis of `PVFinishStatement`. -/
example : (2 : ℝ) ^ 10 ≤ Vortex.L (2 ^ 1024) := by
  rw [Vortex.L_pow]; norm_num

end EGTest.ProbeP4A
