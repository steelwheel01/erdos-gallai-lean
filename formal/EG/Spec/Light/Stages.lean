module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages

/-!
# Statements of the claims embedded in Definition s5:defStages and of equation (s5:eqPl)

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:defStages ("Spec … for the embedded claims (StagesHBStatement …; EqPlStatement …)").

Manuscript v6.1, `s5.tex`, Definition [s5:defStages]: "Let `Y` be a light part of round `r`. Then
`H_Y = X_Y` is a `(2^{-6}, s_r/2)`-expander on `Y` (Definition s2:defAncestors and Proposition
s2:propStructure(i)). Put `vm_Y := ⌈L_Y^6⌉` and `vb_Y := ⌈2^7 L_Y^2 vm_Y⌉`. Since `s_r ≥ λ_r^{100}`
and `L_Y ≤ 2λ_r` (Lemma s2:lemTower(b)), we have `2vm_Y ≤ 2^8λ_r^6 + 2 ≤ s_r/2`. So Lemma s3:lemHB,
applied to `X_Y` with `ε' = 2^{-6}` and `m = vm_Y` (then `b = ⌈2^7L_Y^2vm_Y⌉ = vb_Y`), provides
sets `A_Y(w) ⊆ N_{X_Y}(w)`, `w ∈ Y`, with `|A_Y(w)| = vm_Y` such that every vertex lies in at most
`vb_Y` of them. We fix one such family by a fixed rule …" and, at its end, "A pair `(v, Z)` with
`Z` a light part of round `l` and `v ∈ Pl(Z)` is exactly a pair that is parentless with respect to
the set `Bad` in the sense of Proposition s2:propParentless(iii) …. Hence, by Proposition
s2:propParentless(iii), (s5:eqPl) `∑_Z |Pl(Z)| ≤ 2n + lp`, the sum over all non-demoted light
parts `Z` of all rounds."

Formal reading (Defs `EG/Defs/Light/Stages.lean`, design note `work/p2d/light.md`).
* Setting: `EG.RunHyp N0 Dstar G run`.
* "`X_Y` is a `(2^{-6}, s_r/2)`-expander on `Y`": `(run.X G Y.1 Y.2).verts = V(Y)` and
  `IsExpander (2^{-6}) (s_r/2)` (CONVENTIONS: "spanning … expander on `Z`").
* The fixed family is `EG.Light.AY G run Y` (`Classical.epsilon` of `EG.IsHBFamily`); the claim is
  that it is a Lemma-HB family with `m = vm_Y`, `b = vb_Y` (so the `epsilon` choice is not junk).
  Of the chain `2vm_Y ≤ 2^8λ_r^6 + 2 ≤ s_r/2` only the conclusion `2vm_Y ≤ s_r/2` is stated
  (the middle term is loose, blueprint STAGES-EMBEDDED-CLAIMS; nothing else uses it).
* eqPl: for every stage-1 outcome of positive weight (`ω ∈ (Stage1.law G run).supp`, TRIAGE §2.7),
  the sum over `Z ∈ run.lightParts G` with `¬ demoted ω Z`; `n = G.card`; stated in `ℕ`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:defStages] the claims embedded in the definition: "`H_Y = X_Y` is a
`(2^{-6}, s_r/2)`-expander on `Y`", "`2vm_Y ≤ … ≤ s_r/2`", and the fixed family `A_Y` is a
Lemma-HB family of `X_Y` with `m = vm_Y`, `b = vb_Y` ("sets `A_Y(w) ⊆ N_{X_Y}(w)`, `w ∈ Y`, with
`|A_Y(w)| = vm_Y` such that every vertex lies in at most `vb_Y` of them"), for every light part `Y`,
in the setting of Section s5 (`RunHyp`). -/
def StagesHBStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ Y ∈ run.lightParts G,
      (run.X G Y.1 Y.2).verts = run.ancVerts G Y ∧
      (run.X G Y.1 Y.2).IsExpander (2 ^ (-6 : ℤ)) ((run.s G Y.1 : ℝ) / 2) ∧
      2 * (vm G run Y : ℝ) ≤ (run.s G Y.1 : ℝ) / 2 ∧
      IsHBFamily (run.X G Y.1 Y.2) (vm G run Y) (vb G run Y) (AY G run Y)

open Classical in
/-- [s5:eqPl] "`∑_Z |Pl(Z)| ≤ 2n + lp`, the sum over all non-demoted light parts `Z` of all
rounds", for every stage-1 outcome (of positive weight), in the setting of Section s5
(`RunHyp`). -/
def EqPlStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ ω ∈ (Stage1.law G run).supp,
      ∑ Z ∈ (run.lightParts G).filter (fun Z => ¬ demoted ω Z), (Pl ω Z).card ≤
        2 * G.card + lp ω

end EG.Spec
