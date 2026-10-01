module

public import EG.Defs.Graph
public import EG.Defs.Fnum
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic

/-!
# Statement of Theorem HI″, layered quotient induction (manuscript s7:thmHI)

PROTECTED FILE (`EG/Spec/**`): statement file. `EG/Proof/Quot/HI.lean` proves it, and
`EG/Proof/Quot/HIMain.lean` derives the internal main theorem `EG.Spec.MainInternal` from the
hypothesis `HIHyp`.

Manuscript, Theorem HI″ [s7:thmHI] (s7.tex):
"Let `C ≥ D_*/2` and `ϑ ∈ [0,1/2)` be constants with the following property. Every graph `G`
without isolated vertices, with `n ≥ N₀` vertices and `d₁ = 2|E(G)|/n ≥ D_*`, admits finitely many
simple graphs `Q₁,…,Q_k` (`k ≥ 0`) such that
  `f(G) ≤ C n + 2 ∑_{i=1}^k f(Q_i)` and `∑_{i=1}^k |V(Q_i)| ≤ ϑ n`.
Then `f(G) ≤ c |V(G)|` for every graph `G`, where `c := max(C/(1-2ϑ), N₀/2)`."

Formal reading.
* "graph" ([s1:convGraphs] (a): graphs are finite and simple): `G : EG.FGraph V` on a vertex type
  `V : Type` (as in `EG.Spec.MainInternal`); `n = |V(G)| = G.card`, `E(G) = G.edges`,
  `f(G) = EG.fnum G.edges` ([s1:defObject]; `G.edges` is loopless, so the loop convention of
  `fnum` plays no role).
* "without isolated vertices": every vertex of `G` is an end of an edge of `G`
  (`∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e`; equivalently `G.deg v ≠ 0`, see
  `EG.FGraph.noIsolated_iff_deg_ne_zero` in `EG/Proof/Quot/HI.lean`).
* `d₁ = 2|E(G)|/n ≥ D_*`: the real inequality `D_* ≤ 2 |E(G)| / n` (division in `ℝ`, exactly as
  written; for `n = 0` Lean's `x / 0 = 0` convention applies, a case the manuscript does not
  consider, and the proof never uses the hypothesis for `n = 0`).
* "finitely many simple graphs `Q₁,…,Q_k` (`k ≥ 0`)": a natural number `k` and, for every
  `i : Fin k`, a graph `Q i : EG.FGraph (W i)` on its own vertex type `W i : Type`. An `FGraph` is
  simple by construction; a Mathlib `SimpleGraph` on a `Fintype` becomes one by
  `EG.FGraph.ofSimpleGraph` with the same `f` and number of vertices.
* All constants are real numbers: `D_*` (`Dstar`), `N₀`, `C`, `ϑ`. They are universally quantified,
  so the statement covers the manuscript's fixed `N₀` and `D_*` (s1:defConstants); no sign
  condition on `D_*` or `N₀` is assumed. "The constants `C` and `ϑ` do not depend on `c`" holds
  because `c` is the explicit expression `max (C / (1 - 2 * ϑ)) (N₀ / 2)` in `C`, `ϑ`, `N₀`.
* The conclusion "for every graph `G`" ranges over all `V : Type` and all `G : EG.FGraph V`
  (including graphs with isolated vertices, with fewer than `N₀` vertices, or with `d₁ < D_*`).
-/

@[expose] public section


namespace EG.Spec

/-- [s7:thmHI] (the hypothesis of Theorem HI″) "Every graph `G` without isolated vertices, with
`n ≥ N₀` vertices and `d₁ = 2|E(G)|/n ≥ D_*`, admits finitely many simple graphs `Q₁,…,Q_k`
(`k ≥ 0`) such that `f(G) ≤ C n + 2 ∑_{i=1}^k f(Q_i)` and `∑_{i=1}^k |V(Q_i)| ≤ ϑ n`." -/
def HIHyp (Dstar N₀ C ϑ : ℝ) : Prop :=
  ∀ (V : Type) (G : EG.FGraph V),
    (∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e) →
    N₀ ≤ (G.card : ℝ) →
    Dstar ≤ 2 * (G.edges.card : ℝ) / (G.card : ℝ) →
    ∃ (k : ℕ) (W : Fin k → Type) (Q : (i : Fin k) → EG.FGraph (W i)),
      (EG.fnum G.edges : ℝ) ≤ C * (G.card : ℝ) + 2 * ∑ i, (EG.fnum (Q i).edges : ℝ) ∧
      ∑ i, ((Q i).card : ℝ) ≤ ϑ * (G.card : ℝ)

/-- [s7:thmHI] Theorem HI″ (layered quotient induction). "Let `C ≥ D_*/2` and `ϑ ∈ [0,1/2)` be
constants with the following property. [`HIHyp D_* N₀ C ϑ`] Then `f(G) ≤ c |V(G)|` for every graph
`G`, where `c := max(C/(1-2ϑ), N₀/2)`." -/
def HIStatement : Prop :=
  ∀ (Dstar N₀ C ϑ : ℝ), Dstar / 2 ≤ C → 0 ≤ ϑ → ϑ < 1 / 2 → HIHyp Dstar N₀ C ϑ →
    ∀ (V : Type) (G : EG.FGraph V),
      (EG.fnum G.edges : ℝ) ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) * (G.card : ℝ)

end EG.Spec
