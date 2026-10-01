module

public import EG.Spec.Vortex.PV
public import EG.Lib.Vortex.PVProb
public import EG.Lib.Vortex.PVRunMain

/-!
# Lemma PV (the four-phase P-vortex): [s4:lemPV]

Formerly a declared input of probe unit P4B (probe P-4, part 2; design note
`formal/work/p2b/P4B.md`), used by s5:lemChild (`EG.Spec.LemChildStatement`). Proved in P3 by
unit P3-s4 (progress note `formal/work/p3/s4.md`):

* `EG.PVProb.exists_good` (`EG/Lib/Vortex/PVProb.lean`): labels in the good event `𝒢_PV` exist
  ((G2) by Theorem 16* and (MC), (G4) by (B), (G5) by Markov; `P(𝒢_PV) ≥ 1/2 − η_PV(N) > 0`);
* `EG.PVRun.core` (`EG/Lib/Vortex/PVRunMain.lean`): for such labels, every admissible `H_0`
  has the partition and the arcs of (a)–(d) (the steps `EG.PVRun.step`, with P4A's phase engine
  `EG.pvStepPhase`, the closing `EG.TPVRun.close_class`, P4A's finish `EG.pvFinish` and the
  per-vertex bound `EG.pvArcEndsDeg`).
-/

public section

namespace EG

/-- [s4:lemPV] Lemma PV (the four-phase P-vortex), deterministic form (`EG/Spec/Vortex/PV.lean`).
Proved in P3. -/
theorem pvLemma : EG.Spec.PVStatement := by
  intro V _ D hD H0 hH
  obtain ⟨lev, kap, hg, hG5a, hG5b⟩ := PVProb.exists_good hD
  exact PVRun.core hg hG5a hG5b hH

end EG
