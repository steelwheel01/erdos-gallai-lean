module

public import EG.Defs.Walk
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Robust sublinear expanders and path connectivity (manuscript s1:citDef11, s1:citDef7)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

* `EG.FGraph.IsExpander G ε s`: Definition 11 of Bucić–Montgomery ([s1:citDef11]), with
  `log = log₂` ([s1:convGraphs] (b)) of the number of vertices `n = |G|`.
* `EG.FGraph.IsPathConnected G ℓ t W`: Definition 7 of Bucić–Montgomery ([s1:citDef7]) including
  its multiset clause: the pairs form an indexed family `P : ι → V × V` over a finite index type
  `ι`, so the same pair may occur several times, and "every vertex lies in at most `t` pairs"
  counts indices (occurrences).

Parameter types: `ε s ℓ t : ℝ`. The manuscript uses real values such as `s_r/(16k)`,
`2^{12}L_Y^4` with `L_Y = log₂|Y|`, and the real multiplicities `𝗍 = 2^{10}L^8`, `2^9L^8` of s4
(passed as `t` to Theorem 16* [s3:thmT16s]). The multiplicity bound "at most `t` pairs" compares a
count with the real `t`; for integer `t` write `(k : ℝ)`, and
`EG.FGraph.isPathConnected_natFloor_iff` (in `EG.Lib.Found.Graph`) replaces a real `t ≥ 0` by
`⌊t⌋₊`.
-/

@[expose] public section


namespace EG

namespace FGraph

variable {V : Type*} [DecidableEq V]

/-- [s1:citDef11] "An `n`-vertex graph `G` is an *`(ε,s)`-expander* if for every `U ⊆ V(G)` and
every `F ⊆ E(G)` with `1 ≤ |U| ≤ 2n/3` and `|F| ≤ s|U|` we have
`|Nbr_{G-F}(U)| ≥ ε|U| / log² n`." Here `n = |G| = G.card` and `log = log₂`
([s1:convGraphs] (b)), i.e. `log² n = (Real.logb 2 n)^2`. -/
def IsExpander (G : FGraph V) (ε s : ℝ) : Prop :=
  ∀ U : Finset V, ∀ F : Finset (Sym2 V), U ⊆ G.verts → F ⊆ G.edges →
    1 ≤ U.card → (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 → (F.card : ℝ) ≤ s * U.card →
    ε * U.card / Real.logb 2 G.card ^ 2 ≤ ((G.deleteEdges F).nbrSet U).card

/-- [s1:citDef7] "A graph `G` is *`(ℓ,t)`-path connected through* a vertex set `V ⊆ V(G)` if, for
every collection `𝒫 ⊆ (V(G) choose 2)` in which every vertex lies in at most `t` pairs, there are
edge-disjoint paths `P_{x,y}`, `{x,y} ∈ 𝒫`, such that each `P_{x,y}` is an `xy`-path through `V`
of length at most `ℓ`.
*Multiset clause* ...: here `(V(G) choose 2)` denotes the *multiset* of pairs of distinct vertices
of `G`; in particular the same pair may occur several times in `𝒫`. Thus a pair occurring `k`
times receives `k` pairwise edge-disjoint paths, and the bound `t` counts occurrences. The ends
`x, y` are unrestricted (they need not lie in `V`); only interior vertices must lie in `V`."

Formalization: the multiset `𝒫` is an indexed family `P : ι → V × V` over a finite type `ι`
(the index `i` stands for one occurrence of the pair `{(P i).1, (P i).2}`); the two entries are
distinct vertices of `G`; every vertex `v` is an entry of at most `t` indices; the conclusion
gives one path per index, pairwise edge-disjoint for distinct indices. The parameters `ℓ` and
`t` are real numbers, and the length and multiplicity bounds are real inequalities (the
manuscript uses the real multiplicity `𝗍 = 2^{10}L^8` in s4). The index type ranges
over `Type`; `EG.FGraph.IsPathConnected.exists_paths` (in `EG.Lib.Found.Graph`) applies the
property to index types in any universe. -/
def IsPathConnected (G : FGraph V) (ℓ t : ℝ) (W : Finset V) : Prop :=
  ∀ (ι : Type) [Fintype ι] (P : ι → V × V),
    (∀ i, (P i).1 ∈ G.verts ∧ (P i).2 ∈ G.verts ∧ (P i).1 ≠ (P i).2) →
    (∀ v : V, ((Finset.univ.filter (fun i => (P i).1 = v ∨ (P i).2 = v)).card : ℝ) ≤ t) →
    ∃ Q : ι → List V,
      (∀ i, IsPathBetween G.edges (P i).1 (P i).2 (Q i) ∧ IsThrough W (Q i) ∧
        (pathLength (Q i) : ℝ) ≤ ℓ) ∧
      ∀ i j, i ≠ j → (walkEdges (Q i)).Disjoint (walkEdges (Q j))

end FGraph

end EG
