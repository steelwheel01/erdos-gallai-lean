module

public import EG.Defs.Graph

/-!
# Statement of the counting step of the remark on multisets (manuscript s3:remMultiset)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3a (`formal/work/p2s/s3a.md`; blueprint
`formal/work/p2/blueprint_s3a.md`, node `s3:remMultiset`). No proof here. Consumer: the counting
step inside the proof of Lemma 9_ρ ([s3:lemL9rho]).

Manuscript v6.1, `s3.tex`, Remark [s3:remMultiset] ("multisets; RT2-I14"):
"In [BM, Definition 7] (Cited result s1:citDef7), the collection `𝒫` is a *multiset* of pairs of
distinct vertices.
* The same pair may occur several times, and each occurrence needs a path of its own.
* The endpoints are arbitrary vertices of the graph; they need not lie in `V`.
* The proof of [BM, Lemma 9] (Cited result s1:citLem9) indexes the pairs by `i ∈ [r]`, so it
  applies verbatim to multisets.
* Its counting step also holds when pairs are counted with multiplicity. The step says that a
  maximal subfamily `I' ⊆ I` of pairwise vertex-disjoint pairs satisfies `2t|I'| ≥ |I|`. It holds
  because every pair of `I` meets one of the `2|I'|` vertices covered by `I'`, and each vertex lies
  in at most `t` pairs, counted with multiplicity.
All path-connectivity statements of this manuscript are meant in this multiset sense, and the
proofs of this subsection and the next treat the pairs as an indexed family. […]"

Formal reading. Items 1, 2 and the final sentence are built into the definition
`EG.FGraph.IsPathConnected` (`EG/Defs/Expander.lean`: indexed families, one path per index,
occurrence counts; endpoints only in `V(G)`), so they need no statement. Item 3 is commentary on
B-M's proof (B-M Lemma 9 is not used; Lemma 9_ρ re-proves it). The one mathematical claim is the
counting step of item 4, stated here:
* the family is `P : ι → V × V` over a finite index type (one index per occurrence), the pairs are
  of distinct vertices, and "each vertex lies in at most `t` pairs, counted with multiplicity" is
  the occurrence count over the whole family (`t` real, as in s1:citDef7);
* `I : Finset ι` is the subfamily `I`, and `I' ⊆ I` is maximal among the subfamilies of `I` whose
  pairs are pairwise vertex-disjoint: the vertex sets `{x_i, y_i}` (`i ∈ I'`) are pairwise
  disjoint, and adding any `i ∈ I \ I'` destroys this;
* the conclusion `2t|I'| ≥ |I|` is a real inequality.
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s3:remMultiset] (counting step) "The step says that a maximal subfamily `I' ⊆ I` of pairwise
vertex-disjoint pairs satisfies `2t|I'| ≥ |I|`. It holds because every pair of `I` meets one of the
`2|I'|` vertices covered by `I'`, and each vertex lies in at most `t` pairs, counted with
multiplicity." -/
def MultisetCountStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (ι : Type v) [Fintype ι] (P : ι → V × V) (t : ℝ)
    (I I' : Finset ι),
    (∀ i, (P i).1 ≠ (P i).2) →
    (∀ v : V, ((Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤ t) →
    I' ⊆ I →
    (I' : Set ι).PairwiseDisjoint (fun i => ({(P i).1, (P i).2} : Finset V)) →
    (∀ i ∈ I, i ∉ I' →
      ¬ (insert i (I' : Set ι)).PairwiseDisjoint
        (fun j => ({(P j).1, (P j).2} : Finset V))) →
    (I.card : ℝ) ≤ 2 * t * (I'.card : ℝ)

end EG.Spec
