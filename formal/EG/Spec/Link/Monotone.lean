module

public import EG.Defs.Expander
public import EG.Defs.Prob.FinDist

/-!
# Statement of the monotonicity lemma (manuscript s3:lemMonotone)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3a (`formal/work/p2s/s3a.md`; blueprint
`formal/work/p2/blueprint_s3a.md`, node `s3:lemMonotone`). No proof here. The content is already
proved, sorry-free, as Lib lemmas in `EG/Lib/Found/Graph.lean`: `EG.FGraph.IsExpander.of_le`,
`EG.FGraph.IsExpander.mono` ((i)), `EG.FGraph.IsPathConnected.mono` ((ii)),
`EG.FGraph.IsPathConnected.exists_paths` and `exists_paths_sigma` ((iii)); consumers use those
lemmas directly. This Spec is the traceability statement of the lemma.

Manuscript v6.1, `s3.tex`, Lemma [s3:lemMonotone]:
"(i) Let `H` be an `(ε',s)`-expander and let `H' ⊇ H` be a graph with `V(H') = V(H)`. Then `H'`
is an `(ε',s)`-expander. Moreover, every `(ε',s)`-expander is an `(ε'',s')`-expander whenever
`ε'' ≤ ε'` and `s' ≤ s`.
(ii) Path connectivity is monotone. Let `G ⊆ G'` be graphs with `V(G) = V(G')`, let
`V ⊆ V' ⊆ V(G)`, and suppose `ℓ ≤ ℓ'` and `t' ≤ t`. If `G` is `(ℓ,t)`-path connected through `V`,
then `G'` is `(ℓ',t')`-path connected through `V'`.
(iii) Whether a graph `X` is `(ℓ,t)`-path connected through a set `V` depends only on the pair
`(X,V)`. On this event, required paths exist for *every* multiset `𝒫` of pairs of distinct
vertices of `X` in which each vertex lies in at most `t` pairs. In particular, `𝒫` may be chosen
after `X` and `V` are revealed, as an arbitrary function of them and of any further randomness
(adaptively). If several multisets `𝒫_1,…,𝒫_q` are given and every vertex lies in at most `t`
pairs of the union multiset `𝒫_1+⋯+𝒫_q`, then one application of the property to this union
joins all their pairs by pairwise edge-disjoint paths through `V` of length at most `ℓ` (joint
routing)."

Formal reading.
* Graphs are `EG.FGraph V`; "`H' ⊇ H` with `V(H') = V(H)`" is `H ≤ H'` and `H.verts = H'.verts`;
  expanders are `EG.FGraph.IsExpander` (s1:citDef11), path connectivity is
  `EG.FGraph.IsPathConnected` (s1:citDef7 with the multiset clause, s3:remMultiset). All
  parameters are real and carry no sign condition (none is stated).
* (ii): the manuscript's vertex sets `V ⊆ V'` are `W ⊆ W'`, with `W' ⊆ V(G)` kept as stated.
* (iii), first sentence ("depends only on the pair `(X,V)`"): in Lean the predicate is a function
  of `(X, W)`, so the deterministic content is automatic. Its probabilistic use (the event has the
  same probability on any two finite spaces on which `(X, W)` has the same law, so auxiliary
  randomness can be integrated out) is stated as the last conjunct (decision T0-MON-LAW,
  `formal/work/p2s/s3a.md`).
* (iii), second and last sentences: the multisets `𝒫_k` are indexed families
  `P k : ι k → V × V` over finite index types (one index per occurrence), `k` ranging over a finite
  type `κ` (the case of one multiset is `κ = Unit`); "every vertex lies in at most `t` pairs of the
  union multiset" is the SUM over `k` of the occurrence counts; the paths for all pairs of all
  `𝒫_k` are pairwise edge-disjoint (distinct elements of `Σ k, ι k`). "Chosen adaptively" is
  automatic: the conclusion is a `∀` over families.
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s3:lemMonotone] "(i) Let `H` be an `(ε',s)`-expander and let `H' ⊇ H` be a graph with
`V(H') = V(H)`. Then `H'` is an `(ε',s)`-expander. Moreover, every `(ε',s)`-expander is an
`(ε'',s')`-expander whenever `ε'' ≤ ε'` and `s' ≤ s`. (ii) Path connectivity is monotone. Let
`G ⊆ G'` be graphs with `V(G) = V(G')`, let `V ⊆ V' ⊆ V(G)`, and suppose `ℓ ≤ ℓ'` and `t' ≤ t`.
If `G` is `(ℓ,t)`-path connected through `V`, then `G'` is `(ℓ',t')`-path connected through `V'`.
(iii) Whether a graph `X` is `(ℓ,t)`-path connected through a set `V` depends only on the pair
`(X,V)`. On this event, required paths exist for *every* multiset `𝒫` of pairs of distinct
vertices of `X` in which each vertex lies in at most `t` pairs. […] If several multisets
`𝒫_1,…,𝒫_q` are given and every vertex lies in at most `t` pairs of the union multiset
`𝒫_1+⋯+𝒫_q`, then one application of the property to this union joins all their pairs by pairwise
edge-disjoint paths through `V` of length at most `ℓ` (joint routing)." -/
def MonotoneStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V],
    -- (i), first claim
    (∀ (H H' : FGraph V) (ε' s : ℝ), H ≤ H' → H.verts = H'.verts → H.IsExpander ε' s →
      H'.IsExpander ε' s) ∧
    -- (i), second claim
    (∀ (H : FGraph V) (ε' s ε'' s' : ℝ), ε'' ≤ ε' → s' ≤ s → H.IsExpander ε' s →
      H.IsExpander ε'' s') ∧
    -- (ii)
    (∀ (G G' : FGraph V) (W W' : Finset V) (ℓ ℓ' t t' : ℝ), G ≤ G' → G.verts = G'.verts →
      W ⊆ W' → W' ⊆ G.verts → ℓ ≤ ℓ' → t' ≤ t →
      G.IsPathConnected ℓ t W → G'.IsPathConnected ℓ' t' W') ∧
    -- (iii), joint routing (one multiset: `κ = Unit`)
    (∀ (X : FGraph V) (W : Finset V) (ℓ t : ℝ) (κ : Type) [Fintype κ] (ι : κ → Type)
        [∀ k, Fintype (ι k)] (P : ∀ k, ι k → V × V),
      X.IsPathConnected ℓ t W →
      (∀ k i, (P k i).1 ∈ X.verts ∧ (P k i).2 ∈ X.verts ∧ (P k i).1 ≠ (P k i).2) →
      (∀ v : V,
        ((∑ k, (Finset.univ.filter (fun i => (P k i).1 = v ∨ (P k i).2 = v)).card : ℕ) : ℝ) ≤ t) →
      ∃ Q : ∀ k, ι k → List V,
        (∀ k i, IsPathBetween X.edges (P k i).1 (P k i).2 (Q k i) ∧ IsThrough W (Q k i) ∧
          (pathLength (Q k i) : ℝ) ≤ ℓ) ∧
        ∀ k i k' j, (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ →
          (walkEdges (Q k i)).Disjoint (walkEdges (Q k' j))) ∧
    -- (iii), "depends only on the pair `(X,V)`" (probabilistic reading, T0-MON-LAW)
    (∀ (Ω Ω' : Type v) (μ : FinDist Ω) (μ' : FinDist Ω') (X : Ω → FGraph V) (W : Ω → Finset V)
        (X' : Ω' → FGraph V) (W' : Ω' → Finset V) (ℓ t : ℝ),
      μ.map (fun ω => (X ω, W ω)) = μ'.map (fun ω => (X' ω, W' ω)) →
      μ.prob {ω | (X ω).IsPathConnected ℓ t (W ω)} =
        μ'.prob {ω | (X' ω).IsPathConnected ℓ t (W' ω)})

end EG.Spec
