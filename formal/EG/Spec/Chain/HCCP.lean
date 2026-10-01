module

public import EG.Defs.Chain.HCCP
public import EG.Defs.Objects

/-!
# Statements of Lemma HCC-P and of the union lemma (manuscript s6:lemHCCP, s6:lemHCCglob)

Statement file of probe unit P2E (probe P-2, part 1; design note `formal/work/p2b/P2E.md`).

Manuscript v6.1, Lemma HCC-P [s6:lemHCCP] (layered hub-cluster chaining with path junctions).
The data and hypotheses ("Let `k ≥ 1`, and suppose the following data are given ... Assume:
(D) ... (P) ... (JC-P) ...") are `S : EG.Chain.HccpData V` and `S.Valid G`
(`EG.Defs.Chain.HCCP`, quoted clause by clause there). The conclusions:
"Then:
(i) all `Φ_j` are equal to a common value `Φ`, and `Φ = |𝒫_j|` for every `j`;
(ii) there are sets `F_j ⊆ E(𝒫_j)` with `E(𝒫_j) ∖ F_j ⊆ E(G[T_j])` such that
`⋃_𝒦 B_𝒦 ∪ ⋃_j F_j` decomposes into at most `Φ` cycles of `G`, each of length at least
`max(3,k)`."

Manuscript v6.1, Lemma (union of systems) [s6:lemHCCglob]:
"Let `E_1, …, E_q ⊆ E(G)` be pairwise disjoint, and suppose each `E_i` decomposes into `a_i`
objects. Then `E_1 ∪ ⋯ ∪ E_q` decomposes into `∑_i a_i` objects.
In particular, suppose several systems satisfy the hypotheses of Lemma HCC-P separately, each
with its own layers, junction sets and path families, and the edge sets they decompose (their
beads together with their sets `F_j`) are pairwise disjoint. Then the union of these edge sets
decomposes into at most the sum of their values `Φ`. No vertex-disjointness across systems is
needed: a vertex may be a hub, a port or a junction vertex in several systems. Hypothesis (D) is
used only inside one system, through the potential `Ψ` of that system."

Formal reading:
* `|𝒫_j|` is the length of the list `S.P j` (a family, counted with multiplicity);
* `E(G[T_j])` is `(G.induce (S.T j)).edges` (the edges of `G` with both ends in `T_j`);
* "decomposes into at most `Φ` cycles of `G`, each of length at least `max(3,k)`": a list `D`
  of objects with `EG.IsDecomp` of the edge set, `|D| ≤ Φ`, and every object a cycle `c` (a
  vertex list; its length is its number of edges) with `max 3 k ≤ |c|` and all edges in `E(G)`;
  the length bound is part of the TeX statement and stays in this Spec although no consumer
  reads it (HCCP-LENGTH-UNUSED); a count-only form, if a consumer wants one, must be a corollary
  derived in Lib/Proof from `HccpStatement`, never a replacement Spec (reviews rounds 1 and 2);
* `HccUnionStatement` is the first paragraph of [s6:lemHCCglob] ("decomposes into `a_i`
  objects" = a decomposition list of length `a_i`);
* `HccGlobStatement` is the second paragraph, with the disjointness hypothesis stated at the
  **input level** (beads and all path edges of distinct systems are pairwise disjoint), as
  decided in TRIAGE (blueprint hazard GLOB-OUTPUT-LEVEL-HYP): the manuscript's hypothesis refers
  to the sets `F_j`, which are outputs of HCC-P; since `F_j ⊆ E(𝒫_j)`, input-level disjointness
  implies it, and it is exactly what the consumer (JS-LC Step 7) verifies. The common value `Φ`
  of a system is given in the `∃ Φ` form (`EG.Chain.HccpData.eq_of_forall_Phi_eq`: it is unique,
  `k ≥ 1`). The conclusion also records that the objects are cycles of `G` (the consumer, JS-LC
  Step 7, reads "the union decomposes into at most `∑_𝒮 Φ(𝒮)` cycles"; it holds because the
  decomposition is the concatenation of the HCC-P outputs). No cross-system vertex condition is
  assumed (blueprint note GLOB-NO-VERTEX-DISJ).
-/

@[expose] public section

namespace EG.Spec

open EG.Chain

universe u

/-- [s6:lemHCCP] "Let `k ≥ 1`, and suppose the following data are given. ... Assume: (D) ...;
(P) ...; (JC-P) ... Then:
(i) all `Φ_j` are equal to a common value `Φ`, and `Φ = |𝒫_j|` for every `j`;
(ii) there are sets `F_j ⊆ E(𝒫_j)` with `E(𝒫_j) ∖ F_j ⊆ E(G[T_j])` such that
`⋃_𝒦 B_𝒦 ∪ ⋃_j F_j` decomposes into at most `Φ` cycles of `G`, each of length at least
`max(3,k)`."

The hypotheses are `S.Valid G` (every clause quoted in `EG.Chain.HccpData.Valid`). -/
def HccpStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (S : HccpData V), S.Valid G →
    ∃ Φ : ℕ, (∀ j, S.Phi j = Φ ∧ (S.P j).length = Φ) ∧
      ∃ F : Fin S.k → Finset (Sym2 V),
        (∀ j, F j ⊆ S.pathEdges j ∧ S.pathEdges j \ F j ⊆ (G.induce (S.T j)).edges) ∧
        ∃ D : List (Obj V),
          IsDecomp ((S.beads ∪ Finset.univ.biUnion F : Finset (Sym2 V)) : Set (Sym2 V)) D ∧
          D.length ≤ Φ ∧
          ∀ o ∈ D, ∃ c : List V, o = Obj.cycle c ∧ max 3 S.k ≤ c.length ∧
            ∀ e ∈ cycleEdges c, e ∈ G.edges

/-- [s6:lemHCCglob] (first paragraph) "Let `E_1, …, E_q ⊆ E(G)` be pairwise disjoint, and
suppose each `E_i` decomposes into `a_i` objects. Then `E_1 ∪ ⋯ ∪ E_q` decomposes into
`∑_i a_i` objects." (`a_i` is the length of the given decomposition `D i`.) -/
def HccUnionStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (q : ℕ) (E : Fin q → Finset (Sym2 V))
    (D : Fin q → List (Obj V)),
    (∀ i, E i ⊆ G.edges) → (∀ i i', i ≠ i' → Disjoint (E i) (E i')) →
    (∀ i, IsDecomp (E i : Set (Sym2 V)) (D i)) →
      ∃ D' : List (Obj V),
        IsDecomp ((Finset.univ.biUnion E : Finset (Sym2 V)) : Set (Sym2 V)) D' ∧
        D'.length = ∑ i, (D i).length

/-- [s6:lemHCCglob] (second paragraph) "In particular, suppose several systems satisfy the
hypotheses of Lemma HCC-P separately, each with its own layers, junction sets and path families,
and the edge sets they decompose (their beads together with their sets `F_j`) are pairwise
disjoint. Then the union of these edge sets decomposes into at most the sum of their values `Φ`.
No vertex-disjointness across systems is needed: a vertex may be a hub, a port or a junction
vertex in several systems."

Input-level disjointness (TRIAGE, GLOB-OUTPUT-LEVEL-HYP; CONVENTIONS T0 row `T0-glob-input`):
the beads and path edges of distinct systems are pairwise disjoint. This is formally stronger than
the literal hypothesis (beads with the `F_j`, which are HCC-P outputs, since `F_j ⊆ E(𝒫_j)`), and
it is exactly what JS-LC Step 7 checks: "Their bead sets are pairwise disjoint ... Their path
edges are pairwise disjoint ... Path edges are disjoint from beads". Conclusion: common values `Φ s`, sets `F s j` as in HCC-P (ii) for
every system, and a decomposition of the union of the sets `B(𝒮_s) ∪ ⋃_j F s j` into at most
`∑_s Φ s` cycles of `G`. -/
def HccGlobStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (q : ℕ) (S : Fin q → HccpData V),
    (∀ s, (S s).Valid G) →
    (∀ s s', s ≠ s' →
      Disjoint ((S s).beads ∪ (S s).allPathEdges) ((S s').beads ∪ (S s').allPathEdges)) →
    ∃ Φ : Fin q → ℕ, (∀ s j, (S s).Phi j = Φ s) ∧
      ∃ F : (s : Fin q) → Fin (S s).k → Finset (Sym2 V),
        (∀ s j, F s j ⊆ (S s).pathEdges j ∧
          (S s).pathEdges j \ F s j ⊆ (G.induce ((S s).T j)).edges) ∧
        ∃ D : List (Obj V),
          IsDecomp ((Finset.univ.biUnion fun s => (S s).beads ∪ Finset.univ.biUnion (F s) :
            Finset (Sym2 V)) : Set (Sym2 V)) D ∧
          D.length ≤ ∑ s, Φ s ∧
          ∀ o ∈ D, ∃ c : List V, o = Obj.cycle c ∧ ∀ e ∈ cycleEdges c, e ∈ G.edges

end EG.Spec
