module

public import EG.Spec.Chain.JSLCSteps
public import EG.Lib.Chain.StageInst
public import EG.Lib.Chain.Design
public import EG.Proof.HB.StructureHY

/-!
# Proof of the Step 7 disjointness checks of Lemma JS-LC (manuscript s6:lemJSLC, proof, Step 7)

Probe unit P2J (probe P-2, part 2; design note `formal/work/p2b/P2J.md`). An assembly of the
coherence facts of the stage data (`StageData.Coherent`: `LJS_{Y,l,j} ⊆ E(H_Y)`, the classes of
one ancestor pairwise disjoint, no class outside `r(Y)+2 ≤ l ≤ R`, `j < K^JS_l`), the Lib lemma
`EG.Chain.Tj_disjoint`, and `EG.structureHY` (s2:propStructure (iii)), as in
the manuscript: "All of them lie in `Lend_Y ⊆ E(H_Y) ⊆ E_r(Y)`, while beads lie in `⋃_Z E_l(Z)`.
These sets are disjoint by the partition of Proposition s2:propStructure(iii)."
-/

public section

namespace EG

open EG.HB EG.Chain

/-- [s6:lemJSLC:proof-step-7] the disjointness hypotheses of HCC-P and HCCglob in Step 7. -/
theorem jslcStep7Disj : EG.Spec.JslcStep7DisjStatement := by
  intro V _ G Dstar run S l hrun hS
  obtain ⟨hHY, -, hEdisj, hHdisj⟩ := EG.structureHY V G Dstar run hrun
  refine ⟨?_, ?_, fun Y j j' hjj => hS.ljs_disj Y l j l j' (by simpa using hjj),
    fun Y j j' hjj => Tj_disjoint run G S Y l hjj,
    fun Y j => Finset.filter_subset _ _⟩
  · intro Y hY j a ha
    by_cases hlate : l ∈ Stage1.lateRounds run Y.1 ∧ j < Stage1.KJS G run l
    · have hr : Y.1 + 2 ≤ l := ((Stage1.mem_lateRounds run).1 hlate.1).1
      have hne : Y ≠ (l, a) := fun h => by rw [h] at hr; simp at hr
      have hla : (l, a) ∈ run.ancestors G :=
        (Run.mem_ancestors run G).2 (Std_subset_prePartAddrs run G l ha)
      exact (hEdisj Y hY (l, a) hla hne).mono_left ((hS.ljs_sub Y l j).trans (hHY Y hY))
    · rw [hS.ljs_eq_empty Y l j hlate]; exact Finset.disjoint_empty_left _
  · intro Y hY Y' hY' hne j j'
    exact (hHdisj Y hY Y' hY' hne).mono (hS.ljs_sub Y l j) (hS.ljs_sub Y' l j')

end EG
