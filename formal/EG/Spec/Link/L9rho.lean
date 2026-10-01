module

public import EG.Defs.Expander
public import EG.Defs.Link.Star

/-!
# Statement of Lemma 9_ρ (multiset linking from ball expansion; manuscript s3:lemL9rho)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3b (`formal/work/p2s/s3b.md`; blueprint
`formal/work/p2/blueprint_s3b.md`, node `s3:lemL9rho`). No proof here. The proof (blueprint: stage
α) takes the locked `EG.Spec.HaxellStatement` (the `q²`-form, `EG/Spec/Ext/Haxell.lean`) and B-M
Proposition 8 as hypotheses of the proof term; the Spec itself is hypothesis-free. Consumer:
Theorem 16* ([s3:thmT16s], Step 4, with `G := X` and `W := V`).

Manuscript v6.1, `s3.tex`, Lemma [s3:lemL9rho]:
"Let `G` be an `n`-vertex graph with `n ≥ 2^{30}`, put `L := log n`, and let `t ≥ 1` and
`ρ ∈ (0,1]`. Take `ℓ_*`, `s̄_*` and `M_* = ⌈2.1/ρ⌉` from (s3:eqStar). Let `V ⊆ V(G)` with
`|V| ≥ ρn/2`, and suppose `ρn ≥ 84`. Then `|V| ≥ n/M_* + 2`. Suppose that
`|B^{ℓ_*}_{G-F}(U,V)| > |V|/2` for every nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with
`|F| ≤ s̄_*|U|`. Then `G` is `(2^{12}L^4,t)`-path connected through `V` in the multiset sense of
[BM, Definition 7] (Cited result s1:citDef7). That is, every multiset of pairs of distinct
vertices of `G` in which each vertex lies in at most `t` pairs can be joined by pairwise
edge-disjoint paths of length at most `2^{12}L^4` whose interior vertices lie in `V`."

Formal reading.
* `G : FGraph V`, `n = G.card`, `L = log₂ n` (`Real.logb 2`); the manuscript's vertex set `V` is
  `W : Finset V` (the letter `V` is the vertex type) with `W ⊆ G.verts`.
* The (eqStar) parameters are the locked `EG.Star.ell n` (`ℓ_* = ⌊2^{10}L^3⌋`, a natural number),
  `EG.Star.sbar n ρ t` (`s̄_* = 2^{28}tL^8/ρ`) and `EG.Star.M ρ` (`M_* = ⌈2.1/ρ⌉`, a natural
  number). None of them depends on `ε'`, so the (eqStar) domain condition `ε' ∈ [2^{-7},1]` is
  void here; the other domain conditions (`n ≥ 2`, `ρ ∈ (0,1]`, `t ≥ 1`) are hypotheses.
* The two conclusions are a conjunction: "`|V| ≥ n/M_* + 2`" (real inequality) unconditionally,
  and "if the ball condition holds, then `G` is path connected".
* "`B^{ℓ_*}_{G-F}(U,V)`" is `EG.ball (G.deleteEdges F) (Star.ell n) U W` (s1:convGraphs (d));
  "`|F| ≤ s̄_*|U|`" and "`> |V|/2`" are real inequalities.
* "`(2^{12}L^4,t)`-path connected through `V`" is `G.IsPathConnected (2^{12}L^4) t W`
  (s1:citDef7 with the multiset clause, the form spelled out in the lemma's last sentence).
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s3:lemL9rho] Lemma 9_ρ: "Let `G` be an `n`-vertex graph with `n ≥ 2^{30}`, put `L := log n`,
and let `t ≥ 1` and `ρ ∈ (0,1]`. Take `ℓ_*`, `s̄_*` and `M_* = ⌈2.1/ρ⌉` from (s3:eqStar). Let
`V ⊆ V(G)` with `|V| ≥ ρn/2`, and suppose `ρn ≥ 84`. Then `|V| ≥ n/M_* + 2`. Suppose that
`|B^{ℓ_*}_{G-F}(U,V)| > |V|/2` for every nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with
`|F| ≤ s̄_*|U|`. Then `G` is `(2^{12}L^4,t)`-path connected through `V` in the multiset sense of
[BM, Definition 7]." -/
def L9rhoStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (W : Finset V) (ρ t : ℝ),
    2 ^ 30 ≤ G.card → 0 < ρ → ρ ≤ 1 → 1 ≤ t →
    W ⊆ G.verts → ρ * (G.card : ℝ) / 2 ≤ (W.card : ℝ) → 84 ≤ ρ * (G.card : ℝ) →
    ((G.card : ℝ) / (Star.M ρ : ℝ) + 2 ≤ (W.card : ℝ)) ∧
    ((∀ U : Finset V, U.Nonempty → U ⊆ G.verts → ∀ F : Finset (Sym2 V), F ⊆ G.edges →
        (F.card : ℝ) ≤ Star.sbar G.card ρ t * (U.card : ℝ) →
        (W.card : ℝ) / 2 < ((ball (G.deleteEdges F) (Star.ell G.card) U W).card : ℝ)) →
      G.IsPathConnected ((2 : ℝ) ^ 12 * Real.logb 2 (G.card : ℝ) ^ 4) t W)

end EG.Spec
