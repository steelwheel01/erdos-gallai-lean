module

public import EG.Defs.Expander

/-!
# Statements of the remark after Bucić–Montgomery Definition 11 (manuscript s1:citDef11)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:citDef11`). No proof here. The definition itself is
the locked `EG.FGraph.IsExpander` (`EG/Defs/Expander.lean`); the blueprint records the Lib lemmas
that prove the remark (`IsExpander.lt_deg`, `IsExpander.lt_minDeg`, `isExpander_of_nonpos` in
`EG/Lib/Found/Graph.lean`). Consumers: s2 (witness, lemCap, lemHS, propStructure), s3.

Manuscript v6.1, `s1.tex`, Cited result [s1:citDef11] ([BM, Definition 11]), the remark:
"*Remark (from [BM]; hypotheses made explicit):* if `n ≥ 2` and `ε > 0` then, for every
`v ∈ V(G)`, the pair `U = {v}`, `F = {edges at v}` violates this inequality, so necessarily
`|F| > s`; hence `δ(G) > s` for every `(ε,s)`-expander `G` with `ε > 0` on at least two
vertices. (For `ε = 0` every graph satisfies the inequality; wherever this remark is used below,
`ε ≥ 2^{-7}`.)"

Formal reading.
* `G : EG.FGraph V`, `n = G.card`, `G.IsExpander ε s` with `ε s : ℝ`.
* "`|F| > s`" for `F = {edges at v}`: `s < deg_{E(G)}(v)` (`EG.degE G.edges v`, the number of
  edges of `G` at `v`); "`δ(G) > s`": `s < G.minDeg` (real comparison; `V(G)` is nonempty here,
  so `minDeg` is the true minimum degree).
* "For `ε = 0` every graph satisfies the inequality": every graph is a `(0,s)`-expander.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:citDef11] (remark) "if `n ≥ 2` and `ε > 0` then, for every `v ∈ V(G)`, the pair
`U = {v}`, `F = {edges at v}` violates this inequality, so necessarily `|F| > s`; hence
`δ(G) > s` for every `(ε,s)`-expander `G` with `ε > 0` on at least two vertices." -/
def ExpanderMinDegStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (ε s : ℝ),
    G.IsExpander ε s → 0 < ε → 2 ≤ G.card →
      (∀ v ∈ G.verts, s < (degE G.edges v : ℝ)) ∧ s < (G.minDeg : ℝ)

/-- [s1:citDef11] (remark) "(For `ε = 0` every graph satisfies the inequality …)": every graph
is a `(0,s)`-expander. -/
def ExpanderEpsZeroStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (s : ℝ), G.IsExpander 0 s

end EG.Spec
