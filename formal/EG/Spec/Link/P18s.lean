module

public import EG.Defs.Expander
public import EG.Defs.Link.Star
public import EG.Defs.Prob.FinDist

/-!
# Statement of Proposition 18* and Lemma 19* (manuscript s3:lemP18s)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s3a (`formal/work/p2s/s3a.md`; blueprint
`formal/work/p2/blueprint_s3a.md`, node `s3:lemP18s`). No proof here. Consumer: Theorem 16*
([s3:thmT16s], Step 2: applied to each colour class `X_i` with `s_1 = s/(2K_*)`, and in Step 4
pointwise to `U` and `F ∩ E(X_i)`); `EG.Spec.T16sStatement` quantifies `V : Type u`, `Ω : Type v`,
so the random-set part here quantifies `Ω` in its own universe `v`.

Manuscript v6.1, `s3.tex`, Lemma [s3:lemP18s] ("Proposition 18* and Lemma 19*"):
"Let `G` be an `n`-vertex `(ε',s_1)`-expander with `n ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, let
`ρ ∈ (0,1]`, take the parameters of (eqStar) with `L := log n`, and assume `s_1 ≥ θ_*+1`.
(i) (Proposition 18*.) Every `U ⊆ V(G)` with `1 ≤ |U| ≤ 2n/3` contains a set `U'` with
`|Nbr_G(U')| ≥ θ_*|U'|` and `|U'| ≥ ε'|U|/(3θ_*L^2)`.
(ii) (Lemma 19*.) Let `V` be a `ρ`-random subset of `V(G)`. With probability at least `1−n^{-6}`
the following holds: for every nonempty `U ⊆ V(G)` and every `F ⊆ E(G)` with `|F| ≤ μ_*|U|`,
  `|B^{ℓ_*}_{G−F}(U,V)| > |V|/2`.
The hypothesis is `s_1 ≥ θ_*+1` and not `s_1 ≥ θ_*`. […]"

Formal reading.
* `n = G.card`, `L = log₂ n` (`Real.logb 2`); parameters `θ_* = Star.theta n ε' ρ`,
  `μ_* = Star.mu n ε' ρ`, `ℓ_* = Star.ell n` (locked Defs `EG/Defs/Link/Star.lean`).
* (i): "contains a set `U'`" is `U' ⊆ U`; "`|Nbr_G(U')| ≥ θ_*|U'|`" is
  `G.IsWellExpanding θ_* U'`. Both bounds are real inequalities.
* (ii): the random set is `R : Ω → Finset V` on any finite probability space with
  `μ.IsRSubset R G.verts ρ`. The quantifiers over `U` and `F` are INSIDE the event (one event,
  probability at least `1 − n^{-6}`; blueprint note P18-SINGLE-EVENT). `n^{-6}` is the integer
  power `(n : ℝ) ^ (-6 : ℤ)`; `|F| ≤ μ_*|U|` and `> |V|/2` are real inequalities.
-/

@[expose] public section

namespace EG.Spec

universe u v

/-- [s3:lemP18s] Proposition 18* and Lemma 19*: "Let `G` be an `n`-vertex `(ε',s_1)`-expander with
`n ≥ 2` and `2^{-7} ≤ ε' ≤ 1`, let `ρ ∈ (0,1]`, take the parameters of (eqStar) with
`L := log n`, and assume `s_1 ≥ θ_*+1`. (i) (Proposition 18*.) Every `U ⊆ V(G)` with
`1 ≤ |U| ≤ 2n/3` contains a set `U'` with `|Nbr_G(U')| ≥ θ_*|U'|` and
`|U'| ≥ ε'|U|/(3θ_*L^2)`. (ii) (Lemma 19*.) Let `V` be a `ρ`-random subset of `V(G)`. With
probability at least `1−n^{-6}` the following holds: for every nonempty `U ⊆ V(G)` and every
`F ⊆ E(G)` with `|F| ≤ μ_*|U|`, `|B^{ℓ_*}_{G−F}(U,V)| > |V|/2`." -/
def P18sStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (ε' s₁ ρ : ℝ),
    G.IsExpander ε' s₁ → 2 ≤ G.card → (2 : ℝ) ^ (-7 : ℤ) ≤ ε' → ε' ≤ 1 → 0 < ρ → ρ ≤ 1 →
    Star.theta G.card ε' ρ + 1 ≤ s₁ →
    -- (i) Proposition 18*
    (∀ U : Finset V, U ⊆ G.verts → 1 ≤ U.card → (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 →
      ∃ U' ⊆ U, G.IsWellExpanding (Star.theta G.card ε' ρ) U' ∧
        ε' * (U.card : ℝ) / (3 * Star.theta G.card ε' ρ * Real.logb 2 (G.card : ℝ) ^ 2) ≤
          (U'.card : ℝ)) ∧
    -- (ii) Lemma 19*
    (∀ (Ω : Type v) (μ : FinDist Ω) (R : Ω → Finset V), μ.IsRSubset R G.verts ρ →
      1 - (G.card : ℝ) ^ (-6 : ℤ) ≤
        μ.prob {ω | ∀ U : Finset V, U.Nonempty → U ⊆ G.verts →
          ∀ F : Finset (Sym2 V), F ⊆ G.edges →
            (F.card : ℝ) ≤ Star.mu G.card ε' ρ * (U.card : ℝ) →
            ((R ω).card : ℝ) / 2 < ((ball (G.deleteEdges F) (Star.ell G.card) U (R ω)).card : ℝ)})

end EG.Spec
