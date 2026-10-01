import EG.Spec.Found.EulerMulti
import EG.Spec.Link.T16s
import EG.Spec.Stage1.COLa
import EG.Spec.Stage1.COLc
import EG.Spec.HB.TowerBM
import EG.Spec.HB.StructureLight
import EG.Spec.Light.ParentSteps
import EG.Spec.Light.ParentRun
import EG.Proof.Found.EulerMulti
import EG.Proof.Link.T16s
import EG.Proof.Stage1.COLa
import EG.Proof.HB.TowerBM
import EG.Proof.HB.StructureLight
import EG.Proof.HB.Structure
import EG.Proof.Vortex.PV
import EG.Proof.Light.Setting
import EG.Proof.Light.Stages
import EG.Proof.Light.Zones
import EG.Lib.Found.Graph
import EG.Lib.Found.Gamma
import EG.Lib.Prob.Indep

/-!
# Non-vacuity checks for probe unit P4B (probe P-4, part 2)

Cheap checks that the hypotheses of the P4B statements can hold together and that their
conclusions are satisfiable, on small explicit instances (design note `formal/work/p2b/P4B.md`).

* `EulerMultiStatement`: a triangle with a loop (degrees even, loop counted twice) and its closed
  trail using every edge once.
* `ArcClassEulerStatement`, `TransitionClaimStatement`, `TransitionCountStatement`: two arcs
  `0–1`, `2–3` whose ends have parents `a = par 1 = par 2`, `b = par 3 = par 0`; the quotient is a
  2-cycle `b → a → b`; the closed trail, its transitions `(1,2)`, `(3,0)` (distinct vertices, equal
  parents) and the witness of the Steps 2–3 conclusion; the end count is attained at `v = 1`.
* `VisitCapStatement`: a trail of four arcs visiting the node `0` twice; with capacity `1` the
  witness is the split into two blocks, each re-closed by a new transition at node `0`
  (`(3, 0)` and `(7, 4)`).
* `ConnectorCycleStatement`: one arc `0 1 2` with connector `2 3 0` gives the 4-cycle; the
  degenerate case (arc `0 1`, connector `1 0`) violates the edge-disjointness hypothesis, which is
  what excludes a 2-cycle (manuscript: "As `G` is simple, these are the same edge").
* `T16sStatement`: its hypotheses hold together (degenerate instance `N = 1`).
* Not cheap (need Γ1, i.e. astronomically large runs): `COLaProbStatement`, `COLcIndexStatement`,
  `COLcStatement`, `TowerBMStatement`, `StructureLightStatement`, `BundleEndCountStatement`,
  `MlTyStatement`, `ParentBadProbStatement`, `EtaHalvingStatement`. Γ1 (a)–(e) is satisfiable
  (`EG.exists_gamma1core`, checked below); Γ1 in full is the GAMMA unit's `EG/Spec/Gamma/Sat.lean`.
* The declared-input stubs are referenced once each (they elaborate against their Specs).
-/

open EG EG.MTrail EG.Spec

namespace EGTest.ProbeP4B

/-! ### Euler (b), multigraph form -/

/-- A triangle `0 1 2` with a loop at `1`: edges `0: 0→1`, `1: 1→2`, `2: 2→0`, `3: 1→1`. -/
def triEnds : Fin 4 → Fin 3 × Fin 3 := ![(0, 1), (1, 2), (2, 0), (1, 1)]

example : ∀ x : Fin 3, Even (mdeg (Finset.univ : Finset (Fin 4)) triEnds x) := by
  unfold mdeg triEnds; decide

example : IsClosedTrail triEnds [(0, true), (3, true), (1, true), (2, true)] := by
  unfold IsClosedTrail transitions oSrc oTgt triEnds; decide

example : ∀ e : Fin 4, e ∈ [(0, true), (3, true), (1, true), (2, true)].map Prod.fst ↔
    e ∈ (Finset.univ : Finset (Fin 4)) := by decide

/-! ### Steps 2–3, transition claim, end count -/

/-- Two arcs `0: 0–1`, `1: 2–3`. -/
def arcEnds : Fin 2 → Fin 4 × Fin 4 := ![(0, 1), (2, 3)]

/-- Parents: `par 1 = par 2 = 1` (node `a`), `par 3 = par 0 = 0` (node `b`). -/
def par2 : Fin 4 → Fin 2 := ![0, 1, 1, 0]

def W2 : List (Fin 2 × Bool) := [(0, true), (1, true)]

example : IsClosedTrail (qEnds par2 arcEnds) W2 := by
  unfold IsClosedTrail transitions oSrc oTgt qEnds par2 arcEnds W2; decide

example : transitions arcEnds W2 = [(1, 2), (3, 0)] := by
  unfold transitions oSrc oTgt arcEnds W2; decide

/-- The conclusion of `ArcClassEulerStatement` on this instance (`A` both arcs, `Nd` both nodes):
`T = ∅`, one closed trail. -/
example : ∃ (T : Finset (Fin 2)) (Ws : List (List (Fin 2 × Bool))),
    T ⊆ Finset.univ ∧ T.card ≤ (Finset.univ : Finset (Fin 2)).card - 1 ∧
    Ws.length ≤ (Finset.univ : Finset (Fin 2)).card ∧
    (∀ W ∈ Ws, IsClosedTrail (qEnds par2 arcEnds) W) ∧ (trailEdges Ws).Nodup ∧
    ∀ a, a ∈ trailEdges Ws ↔ a ∈ (Finset.univ : Finset (Fin 2)) ∧ a ∉ T := by
  refine ⟨∅, [W2], ?_⟩
  unfold IsClosedTrail trailEdges transitions oSrc oTgt qEnds par2 arcEnds W2; decide

/-- The transition claim's conclusion holds (distinct vertices, equal parents). -/
example : ∀ t ∈ transitions arcEnds W2, t.1 ≠ t.2 ∧ par2 t.1 = par2 t.2 := by
  unfold transitions oSrc oTgt arcEnds W2 par2; decide

/-- The end count of `TransitionCountStatement` is attained at `v = 1`: one transition contains
`1`, and one arc has `1` as an end. -/
example : ([W2].flatMap (transitions arcEnds)).countP (fun t => t.1 = 1 ∨ t.2 = 1) = 1 ∧
    ((trailEdges [W2]).toFinset.filter fun a => (arcEnds a).1 = 1 ∨ (arcEnds a).2 = 1).card = 1 := by
  unfold transitions trailEdges oSrc oTgt arcEnds W2; decide

/-! ### Step 4, visit capping -/

/-- Four arcs `0: 0–1`, `1: 2–3`, `2: 4–5`, `3: 6–7`. -/
def ends4 : Fin 4 → Fin 8 × Fin 8 := ![(0, 1), (2, 3), (4, 5), (6, 7)]

/-- Parents: transitions `(1,2)` at node `1`, `(3,4)` at node `0`, `(5,6)` at node `2`,
`(7,0)` at node `0`. -/
def par4 : Fin 8 → Fin 3 := ![0, 1, 1, 0, 0, 2, 2, 0]

def W4 : List (Fin 4 × Bool) := [(0, true), (1, true), (2, true), (3, true)]

example : IsClosedTrail (qEnds par4 ends4) W4 ∧ vis par4 ends4 W4 0 = 2 := by
  unfold IsClosedTrail vis transitions oSrc oTgt qEnds par4 ends4 W4; decide

/-- With capacity `1` everywhere, the split into the blocks `a_0 a_1` and `a_2 a_3` (re-closed by
the new transitions `(3,0)` and `(7,4)` at node `0`) satisfies the combinatorial clauses of the
conclusion of `VisitCapStatement`. -/
example : (∀ W' ∈ [[(0, true), (1, true)], [(2, true), (3, true)]],
      IsClosedTrail (qEnds par4 ends4) (W' : List (Fin 4 × Bool))) ∧
    (trailEdges [[((0 : Fin 4), true), (1, true)], [(2, true), (3, true)]]).Perm
      (trailEdges [W4]) ∧
    (∀ W' ∈ [[((0 : Fin 4), true), (1, true)], [(2, true), (3, true)]], ∀ Y : Fin 3,
      vis par4 ends4 W' Y ≤ 1) := by
  unfold IsClosedTrail vis trailEdges transitions oSrc oTgt qEnds par4 ends4 W4; decide

/-! ### Step 7, the cycle claim -/

example : (Obj.cycle ([([0, 1, 2], [2, 3, 0])].flatMap fun s => s.1 ++ EG.interior s.2) :
      Obj (Fin 4)).WF ∧
    (cycleEdges ([([(0 : Fin 4), 1, 2], [2, 3, 0])].flatMap fun s => s.1 ++ EG.interior s.2)).Perm
      ([([(0 : Fin 4), 1, 2], [2, 3, 0])].flatMap fun s => walkEdges s.1 ++ walkEdges s.2) := by
  unfold Obj.WF cycleEdges EG.interior walkEdges; decide

/-- The hypotheses of `ConnectorCycleStatement` hold on the instance above. -/
example : let segs : List (List (Fin 4) × List (Fin 4)) := [([0, 1, 2], [2, 3, 0])]
    segs ≠ [] ∧ (∀ s ∈ segs, s.1.Nodup ∧ 2 ≤ s.1.length ∧ s.2.Nodup ∧ 2 ≤ s.2.length) ∧
    (∀ p ∈ List.zip segs (segs.rotate 1),
      p.1.2.head? = p.1.1.getLast? ∧ p.1.2.getLast? = p.2.1.head?) ∧
    (segs.flatMap Prod.fst).Nodup ∧ (segs.flatMap fun s => EG.interior s.2).Nodup ∧
    (∀ s ∈ segs, ∀ s' ∈ segs, ∀ x ∈ EG.interior s.2, x ∉ s'.1) ∧
    (segs.flatMap fun s => walkEdges s.1).Disjoint (segs.flatMap fun s => walkEdges s.2) := by
  intro segs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, List.disjoint_left.2 ?_⟩ <;>
    (simp only [segs, EG.interior, walkEdges]; decide)

/-- The degenerate 2-cycle (arc `0 1`, connector `1 0`) is excluded by the edge-disjointness
hypothesis. -/
example : ¬ (walkEdges [(0 : Fin 2), 1]).Disjoint (walkEdges [(1 : Fin 2), 0]) := by
  rw [List.disjoint_left]; unfold walkEdges; decide

/-! ### Theorem 16*: the hypotheses hold together (degenerate `N = 1`) -/

/-- The one-vertex graph. -/
def X1 : FGraph (Fin 1) := ⟨{0}, ∅, by simp, by simp⟩

example : (2 : ℝ) ^ (-7 : ℤ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧ X1.IsExpander (1 / 2) 0 ∧
    (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧
    (FinDist.rsubset X1.verts 1 zero_le_one le_rfl).IsRSubset (fun T => T) X1.verts 1 ∧
    Real.logb 2 (X1.card : ℝ) ^ 2 ≤ 1 * (X1.card : ℝ) ∧
    (2 : ℝ) ^ 135 * 1 * Real.logb 2 (X1.card : ℝ) ^ 28 * (1 : ℝ) ^ (-5 : ℤ) ≤ 0 := by
  have hc : X1.card = 1 := rfl
  have hc' : (X1.card : ℝ) = 1 := by rw [hc]; norm_num
  refine ⟨by norm_num, by norm_num, FGraph.isExpander_of_card_le_one (by rw [hc]),
    by norm_num, le_rfl, le_rfl, FinDist.isRSubset_rsubset _ _, ?_, ?_⟩
  · rw [hc']; simp
  · rw [hc']; simp

/-! ### Γ1 (a)–(e) is satisfiable -/

example : ∃ D : ℝ, Gamma1core D := exists_gamma1core

/-! ### The declared-input stubs elaborate against their Specs -/

example : EulerMultiStatement := eulerMulti
example : T16sStatement := t16s
example : COLaProbStatement := colaProb
example : TowerBMStatement := towerBM
example : StructureLightStatement := structureLight  -- derived (fix round)
example : StructureVertexStatement := structureVertex
example : PVStatement := pvLemma
example : EqLYStatement := eqLY
example : StagesHBStatement := stagesHB
example : LemZonesStatement := lemZones

end EGTest.ProbeP4B
