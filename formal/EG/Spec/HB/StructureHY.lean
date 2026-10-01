module

public import EG.Defs.HB.Run

/-!
# Statement of the edge-partition facts of s2:propStructure (iii) used by JS-LC and J⁺

Statement file (`EG/Spec/**`), unit P2J (probe P-2, part 2). This statement was first a DECLARED
INPUT of the probe; it is proved (`EG.structureHY`, `EG/Proof/HB/StructureHY.lean`, fix round 1 of
unit P2J, from `run.Valid G Dstar` alone). The proof of Lemma JS-LC [s6:lemJSLC] (Step 7: "All of
them lie in `Lend_Y ⊆ E(H_Y) ⊆ E_r(Y)`, while beads lie in `⋃_Z E_l(Z)`. These sets are disjoint by
the partition of Proposition s2:propStructure(iii)"; "for different `Y ≠ Y'`, because `E(H_Y) ∩
E(H_{Y'}) = ∅` (`E(H_Y) ⊆ E_{r(Y)}(Y)`, and these sets are disjoint by Proposition
s2:propStructure(iii))") and Lemma J⁺ [s6:lemJplus] (iii) ("(iii) is Proposition
s2:propStructure(iii)") cite it. Design note `formal/work/p2b/P2J.md`, "Declared inputs" and "Fix
round 1". The full Spec of s2:propStructure (iii) (s2 structure unit; blueprint s2b, with the
`EdgeSrc` partition of `E(G)`) must imply this statement.

Manuscript v6.1, `s2.tex`, Proposition [s2:propStructure] (iii) (the clauses used):
"`E(G) = ⨆_{l≤R} E(Cyc_l) ⊔ E_0 ⊔ ⨆_{Y light} E_{r(Y)}(Y) ⊔ ⨆_{l≤R} ⨆_{Z∈Std_l} E_l(Z)`
(disjoint unions); `E(H_Y) ⊆ E_{r(Y)}(Y)` for every ancestor `Y`; every edge of `E_{r(Y)}(Y)` has
both ends in `V(Y)`; the graphs `H_Y` of all ancestors `Y` of all rounds are pairwise
edge-disjoint".

Formal reading.
* Ancestors are `Y ∈ run.ancestors G` (`PartId = (round, pre-part address)`); `E_{r(Y)}(Y)` is
  `run.E G Y.1 Y.2`, `H_Y = run.ancGraph G Y`, `V(Y) = run.ancVerts G Y`. Every ancestor is a
  light part or a standalone pre-part, so "the sets `E_{r(Y)}(Y)` (`Y` light) and `E_l(Z)`
  (`Z ∈ Std_l`) are pairwise disjoint" (the part of the displayed partition used here) is
  pairwise disjointness of `run.E G Y.1 Y.2` over distinct ancestors.
* Hypotheses: only `run.Valid G Dstar`. The manuscript's hypotheses `n ≥ N_0`, `d_1 ≥ D_*` are
  unused (blueprint s2b STR-N0), and the clauses stated here need no condition on `D_*` (the
  clauses `Σ|Cyc_l| ≤ n`, `|E_0| < D_* n/2` of (iii), which do, are not stated). Dropping unused
  hypotheses strengthens the statement; the proof confirms they are unused (it reads only the
  home-order clause of `Round.Valid`).
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propStructure] (iii), the clauses used by JS-LC and J⁺: "`E(H_Y) ⊆ E_{r(Y)}(Y)` for every
ancestor `Y`; every edge of `E_{r(Y)}(Y)` has both ends in `V(Y)`; the graphs `H_Y` of all
ancestors `Y` of all rounds are pairwise edge-disjoint", and the pairwise disjointness of the sets
`E_{r(Y)}(Y)` (`Y` light) and `E_l(Z)` (`Z ∈ Std_l`) from the displayed disjoint union. -/
def StructureHYStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    run.Valid G Dstar →
      (∀ Y ∈ run.ancestors G, (run.ancGraph G Y).edges ⊆ run.E G Y.1 Y.2) ∧
      (∀ Y ∈ run.ancestors G, run.E G Y.1 Y.2 ⊆ (run.ancVerts G Y).sym2) ∧
      (∀ Y ∈ run.ancestors G, ∀ Y' ∈ run.ancestors G, Y ≠ Y' →
        Disjoint (run.E G Y.1 Y.2) (run.E G Y'.1 Y'.2)) ∧
      (∀ Y ∈ run.ancestors G, ∀ Y' ∈ run.ancestors G, Y ≠ Y' →
        Disjoint (run.ancGraph G Y).edges (run.ancGraph G Y').edges)

end EG.Spec
