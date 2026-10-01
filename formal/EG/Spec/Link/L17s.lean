module

public import EG.Defs.Expander
public import EG.Defs.Link.Star
public import EG.Defs.Prob.FinDist

/-!
# Statement of Lemma 17* (sprinkling at density ρ; manuscript s3:lemL17s)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3a (`formal/work/p2s/s3a.md`; blueprint
`formal/work/p2/blueprint_s3a.md`, node `s3:lemL17s`). No proof here. Consumer: Lemma 19*
([s3:lemP18s] (ii), union bound over pairs `(U', F')`). The numeric steps of the proof are the
separate statements of `EG/Spec/Num/L17s.lean` (unit NUM).

Manuscript v6.1, `s3.tex`, Lemma [s3:lemL17s]:
"Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, let
`ρ ∈ (0,1]`, take the parameters of (eqStar) with `L := log n`, and assume `s_1 ≥ 8d_*λ_*`.
Let `V_1,…,V_{ℓ_*}` be independent random subsets of `V(G)`, where `V_i` is `p_*`-random for
`i < ℓ_*` and `V_{ℓ_*}` is `q_*`-random, and put `V := V_1 ∪ ⋯ ∪ V_{ℓ_*}`. By (S2), `V` is a
`ρ`-random subset of `V(G)`. Call `U ⊆ V(G)` *well-expanding* if `|Nbr_G(U)| ≥ θ_*|U|`. Then for
every well-expanding `U` and every `F ⊆ E(G)` with `|F| ≤ |U|`,
  `P(|B^{ℓ_*}_{G−F}(U,V)| ≤ |V|/2) ≤ exp(−7|U|L)`.
Since this event depends only on `V`, the same bound holds for every `ρ`-random subset `V` of
`V(G)`."

Formal reading (decision L17-STATEMENT-FORM of the blueprint; T0-L17-FORM in
`formal/work/p2s/s3a.md`).
* The statement is the lemma's final sentence: "for every `ρ`-random subset `V` of `V(G)`", on any
  finite probability space (`μ : FinDist Ω`, `R : Ω → Finset V`, `μ.IsRSubset R G.verts ρ`). The
  layered set `V_1 ∪ ⋯ ∪ V_{ℓ_*}` is one such `R` (by (S2), `EG.Spec.StarUnionLawStatement`), so
  the first form is the special case; the layers are proof-internal.
* Quantifier order: `U` and `F` are fixed (deterministic) and then the probability is bounded; the
  probability is not of an event "for all `U`, `F`" (that is Lemma 19*).
* `n = G.card`, `L = log₂ n` (`Real.logb 2`), `exp` the natural exponential. The parameters are
  the locked `EG.Star.*` at `(n, ε', ρ)`: `ℓ_* = Star.ell n` (a natural number, used directly as the
  ball radius), `d_* = Star.d n ρ`, `λ_* = Star.lam n ρ`, `θ_* = Star.theta n ε' ρ`.
* "well-expanding" is `G.IsWellExpanding θ_* U` (neighbourhood in `G`), with `U ⊆ V(G)` as in the
  manuscript; `F ⊆ E(G)`, `|F| ≤ |U|` (natural numbers).
* `B^{ℓ_*}_{G−F}(U,V)` is `EG.ball (G.deleteEdges F) ℓ_* U (R ω)`; the event
  `|B| ≤ |V|/2` is a real inequality.
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s3:lemL17s] Lemma 17*: "Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and
`2^{-7} ≤ ε' ≤ 1`, let `ρ ∈ (0,1]`, take the parameters of (eqStar) with `L := log n`, and assume
`s_1 ≥ 8d_*λ_*`. […] Call `U ⊆ V(G)` *well-expanding* if `|Nbr_G(U)| ≥ θ_*|U|`. Then for every
well-expanding `U` and every `F ⊆ E(G)` with `|F| ≤ |U|`,
`P(|B^{ℓ_*}_{G−F}(U,V)| ≤ |V|/2) ≤ exp(−7|U|L)`. Since this event depends only on `V`, the same
bound holds for every `ρ`-random subset `V` of `V(G)`." (Stated in the last form.) -/
def L17sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (ε' s₁ ρ : ℝ) (Ω : Type v) (μ : FinDist Ω)
    (R : Ω → Finset V),
    G.IsExpander ε' s₁ → 2 ≤ G.card → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    8 * (Star.d G.card ρ : ℝ) * (Star.lam G.card ρ : ℝ) ≤ s₁ →
    μ.IsRSubset R G.verts ρ →
    ∀ (U : Finset V) (F : Finset (Sym2 V)), U ⊆ G.verts → F ⊆ G.edges → F.card ≤ U.card →
      G.IsWellExpanding (Star.theta G.card ε' ρ) U →
      μ.prob {ω | ((ball (G.deleteEdges F) (Star.ell G.card) U (R ω)).card : ℝ) ≤
          ((R ω).card : ℝ) / 2} ≤
        Real.exp (-(7 * (U.card : ℝ) * Real.logb 2 (G.card : ℝ)))

end EG.Spec
