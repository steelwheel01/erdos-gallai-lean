module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Full

/-!
# Statement of the light-part clause of s2:propStructure (iv), in the form used by probe P-4,
part 2

Statement file (`EG/Spec/**`), unit P4B (probe P-4, part 2). Written as a declared input of the
probe; since the P4B fix round it is DERIVED (`EG.structureLight_of_structureVertex`,
`EG/Proof/HB/StructureLight.lean`) from the first clause of the s2 unit's
`EG.Spec.StructureVertexStatement` (`EG/Spec/HB/Structure.lean`, which holds under `run.Valid`
alone), and the declared input is `EG.structureVertex`. This statement is kept as the consumer
form of Lemma [s5:lemParent] (F-c) "Light parts of round `l` are pairwise vertex-disjoint (Proposition
s2:propStructure(iv))", used in Step 1 ("Each class contains at most one arc of each `Z`, so by
(F-c) the arcs of one class are pairwise vertex-disjoint") and in Step 5 ("By (F-d) and (F-c), all
of them are arcs of the unique round-`l` light part `Z(v)` containing `v`"), i.e. in
`EG.Spec.BundleEndCountStatement` and `EG.Spec.LemParentStatement`. The other clauses of
propStructure used by P4B are Specs of other units: (i) for light parts and the Lemma-HB family
are `EG.Spec.StagesHBStatement` (s5 unit); the edge clauses of (iii) are
`EG.Spec.StructureHYStatement` (P2J); (ii) is `EG.Spec.CapPrePartStatement`; the clause
"`|Y| ≥ |Y^0|/2 ≥ P_r/2`" of (iv) is definitional in the locked HB model (P4A note, (B4)). The
proof of propStructure is the s2 unit's job. Design note `formal/work/p2b/P4B.md`.

Manuscript v6.1, `s2.tex`, Proposition [s2:propStructure]: "For every valid `HB^tp` run on a
graph `G` with `n ≥ N_0` and `d_1 ≥ D_*`: … (iv) light parts of one round are pairwise
vertex-disjoint, … and each vertex lies in at most one light part per round, …"

Formal reading: the setting "`n ≥ N_0`, `d_1 ≥ D_*`, `D_*` satisfies Γ" is `EG.RunHyp N0 Dstar G
run` (Γ1, Γ3, `N0Cond`, `N_0 ≤ n`, `D_* ≤ d_1`, validity; TRIAGE §2.6); a light part of round `l`
is `Z ∈ run.lightParts G` with `Z.1 = l` and vertex set `V(Z) = run.ancVerts G Z`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:propStructure] (iv) "light parts of one round are pairwise vertex-disjoint" (for every
valid run on a graph with `n ≥ N_0` and `d_1 ≥ D_*`). -/
def StructureLightStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ Z ∈ run.lightParts G, ∀ Z' ∈ run.lightParts G, Z.1 = Z'.1 → Z ≠ Z' →
      Disjoint (run.ancVerts G Z) (run.ancVerts G Z')

end EG.Spec
