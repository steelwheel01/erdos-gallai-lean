module

public import EG.Defs.Probe.P2E.Par
public import Mathlib.Data.Real.Basic

/-!
# Statement of Lemma PAR (manuscript s6:lemPAR)

Statement file of probe unit P2E (probe P-2, part 1; design note `formal/work/p2b/P2E.md`).

Manuscript v6.1, Lemma PAR (port–port parity) [s6:lemPAR]:
"Let `E_ab` be a bipartite graph with sides `V_a, V_b`, and let `V(E_ab)` be the set of vertices
incident with an edge of `E_ab`. Call a connected component of `E_ab` *odd* if it has an odd
number of edges. In each odd component choose one edge that is either a non-bridge or a pendant
edge (an edge with an end of degree `1`) of that component; such an edge exists. Let `J'` be the
set of chosen edges. Then, for *every* such choice,
`|J'| ≤ #{odd components} ≤ |V(E_ab)|/2`,
and there is a partition `E_ab ∖ J' = S_a ⊔ S_b` such that every vertex of `V_b` has even
`S_a`-degree and every vertex of `V_a` has even `S_b`-degree."

Formal reading:
* `E_ab` is an edge set `E : Finset (Sym2 V)`; "bipartite with sides `V_a, V_b`" is: `V_a`, `V_b`
  are disjoint and every edge of `E` is `s(a, b)` with `a ∈ V_a`, `b ∈ V_b` (so `E` is loopless;
  without disjointness the lemma is false, blueprint note PAR-SIDES-DISJOINT);
* components, `V(E_ab)`, non-bridges and pendant edges: `EG.Defs.Components` (a non-bridge or
  pendant edge "of that component" is the global predicate, `EG.isNonBridge_compEdges_iff`,
  `EG.isPendant_compEdges_iff`); odd components: `EG.Chain.oddComps`; an admissible choice `J'`:
  `EG.Chain.IsParChoice E J'` (new Defs file `EG.Defs.Probe.P2E.Par`);
* `ParExistsStatement`: "such an edge exists" (in every odd component), and hence an admissible
  choice `J'` exists;
* `ParStatement`: the conclusions, "for *every* such choice" (blueprint note PAR-FORALL-CHOICE).
  The partition `S_a ⊔ S_b` is two disjoint edge sets with union `E ∖ J'` (either part may be
  empty); degrees are `EG.degE`.
-/

@[expose] public section

namespace EG.Spec

open EG.Chain

universe u

/-- [s6:lemPAR] (existence) "Let `E_ab` be a bipartite graph with sides `V_a, V_b` ... In each
odd component choose one edge that is either a non-bridge or a pendant edge (an edge with an end
of degree `1`) of that component; such an edge exists."

Both the per-component existence and its consequence, the existence of an admissible choice
`J'` (`IsParChoice`). -/
def ParExistsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (E : Finset (Sym2 V)) (Va Vb : Finset V),
    Disjoint Va Vb → (∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) →
      (∀ C ∈ oddComps E, ∃ e ∈ compEdges E C, IsNonBridge E e ∨ IsPendant E e) ∧
      ∃ J' : Finset (Sym2 V), IsParChoice E J'

/-- [s6:lemPAR] "Let `E_ab` be a bipartite graph with sides `V_a, V_b`, and let `V(E_ab)` be the
set of vertices incident with an edge of `E_ab`. Call a connected component of `E_ab` *odd* if it
has an odd number of edges. In each odd component choose one edge that is either a non-bridge or
a pendant edge ... of that component ... Let `J'` be the set of chosen edges. Then, for *every*
such choice, `|J'| ≤ #{odd components} ≤ |V(E_ab)|/2`, and there is a partition
`E_ab ∖ J' = S_a ⊔ S_b` such that every vertex of `V_b` has even `S_a`-degree and every vertex of
`V_a` has even `S_b`-degree." -/
def ParStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (E : Finset (Sym2 V)) (Va Vb : Finset V),
    Disjoint Va Vb → (∀ e ∈ E, ∃ a ∈ Va, ∃ b ∈ Vb, e = s(a, b)) →
    ∀ J' : Finset (Sym2 V), IsParChoice E J' →
      J'.card ≤ (oddComps E).card ∧
      ((oddComps E).card : ℝ) ≤ ((edgeVerts E).card : ℝ) / 2 ∧
      ∃ Sa Sb : Finset (Sym2 V), Disjoint Sa Sb ∧ Sa ∪ Sb = E \ J' ∧
        (∀ v ∈ Vb, Even (degE Sa v)) ∧ ∀ u ∈ Va, Even (degE Sb u)

end EG.Spec
