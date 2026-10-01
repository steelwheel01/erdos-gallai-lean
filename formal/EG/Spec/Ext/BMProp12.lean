module

public import EG.Defs.Expander

/-!
# Statement of Bucić–Montgomery Proposition 12 (manuscript s1:citProp12)

Statement file (`EG/Spec/**`), P2 Spec unit of chunk s1 (`formal/work/p2s/s1.md`; blueprint
`formal/work/p2/blueprint_s1.md`, node `s1:citProp12`). No proof here. PLAN §3 (Ext row) lists
`BMProp12` as a cited result to be proved (the manuscript quotes the proof of [BM] in full); its
consumer is the proof of Proposition 13* ([s3:propP13s], with `d := d_*` an integer,
`U := W \ Bl` and `|F| ≤ s_1|W|/4 ≤ s_1|U|/2`).

Manuscript v6.1, `s1.tex`, Cited result [s1:citProp12] ([BM, Proposition 12]):
"For `U ⊆ V(G)` and `d > 0` let `N_{G,d}(U)` be the set of vertices of `V(G) \ U` with at least
`d` neighbours in `U`. Let `G` be an `n`-vertex `(ε,s)`-expander, `U ⊆ V(G)` with
`1 ≤ |U| ≤ 2n/3`, and `F` a set of at most `s|U|/2` edges. Then for every `0 < d ≤ s`, either
(a) `|Nbr_{G-F}(U)| ≥ s|U|/(2d)`, or (b) `|N_{G-F,d}(U)| ≥ ε|U|/log²n`."

Formal reading.
* `G : EG.FGraph V`, `n = G.card`; `G.IsExpander ε s` (Definition 11, [s1:citDef11]) with
  `ε s : ℝ`; `N_{G-F,d}(U)` is the locked `(G.deleteEdges F).nbrSetDeg U d` (defined for this
  statement and shared with s3:propP13s), `Nbr_{G-F}(U)` is `(G.deleteEdges F).nbrSet U`.
* "`F` a set of at most `s|U|/2` edges": `F ⊆ E(G)` (the inclusion that [BM] leave implicit;
  blueprint note P12-INCL) with `|F| ≤ s|U|/2` (real inequality). Nothing is lost: only
  `F ∩ E(G)` matters for `G - F`, and it is no larger than `F`.
* `d : ℝ` (a real threshold in [BM]; s3 applies it with `(d_* : ℝ)`); `log² n = (log₂ n)^2`.
  "either (a) or (b)" is an inclusive disjunction.
-/

@[expose] public section

namespace EG.Spec

universe u

/-- [s1:citProp12] ([BM, Proposition 12]) "Let `G` be an `n`-vertex `(ε,s)`-expander,
`U ⊆ V(G)` with `1 ≤ |U| ≤ 2n/3`, and `F` a set of at most `s|U|/2` edges. Then for every
`0 < d ≤ s`, either (a) `|Nbr_{G-F}(U)| ≥ s|U|/(2d)`, or (b) `|N_{G-F,d}(U)| ≥ ε|U|/log²n`." -/
def BMProp12Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (ε s d : ℝ) (U : Finset V)
    (F : Finset (Sym2 V)),
    G.IsExpander ε s → U ⊆ G.verts → 1 ≤ U.card → (U.card : ℝ) ≤ 2 * (G.card : ℝ) / 3 →
    F ⊆ G.edges → (F.card : ℝ) ≤ s * (U.card : ℝ) / 2 → 0 < d → d ≤ s →
    s * (U.card : ℝ) / (2 * d) ≤ (((G.deleteEdges F).nbrSet U).card : ℝ) ∨
      ε * (U.card : ℝ) / Real.logb 2 (G.card : ℝ) ^ 2 ≤
        (((G.deleteEdges F).nbrSetDeg U d).card : ℝ)

end EG.Spec
