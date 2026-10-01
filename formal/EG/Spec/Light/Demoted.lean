module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages

/-!
# Statement of Lemma fallback for demoted light parts (manuscript s5:lemDemoted), deterministic
(Tier-1) form

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:lemDemoted.

Manuscript v6.1, `s5.tex`, Lemma [s5:lemDemoted]: "Fix a stage-1 outcome and let `Y` be a demoted
light part of round `r`. Then `Y` is not a good parent; in particular no class `LU_{Y,·}` of `Y`
is used in Lemma s5:lemParent. Let `𝒢^VX_Y` be the good event of Theorem s4:thmVXp for
`O := X_Y`, an event over the VX⁺ labels of `Y` (stage 3) that depends only on `X_Y` and these
labels and has probability at least `1 − η_VX(|Y|) ≥ 1/2`. On `𝒢^VX_Y`, for every edge set `E`
with `E(X_Y) ⊆ E ⊆ E_r(Y)`, the set `E` decomposes into at most `c_VX|Y|` objects."

Formal reading.
* Setting: `EG.RunHyp N0 Dstar G run`; "a stage-1 outcome": `ω ∈ (Stage1.law G run).supp`;
  `Y ∈ run.lightParts G` with `demoted ω Y`; `r = Y.1`, `E_r(Y) = run.E G Y.1 Y.2`,
  `X_Y = run.X G Y.1 Y.2`, `|Y| = (run.ancVerts G Y).card`, `c_VX = 80`.
* "no class `LU_{Y,·}` of `Y` is used in Lemma s5:lemParent": Lemma s5:lemParent (i) uses only
  classes of the good parents of rounds `≤ l − 2` (`EG.Light.goodParents ω l`, the index set of
  `EG.Light.lentUAvail`); stated as `Y ∉ goodParents ω l` for every `l`.
* **Stage 3 (T0, TRIAGE §2.8 / §2.12).** The good event `𝒢^VX_Y` and its probability are not
  stated (the VX⁺ Spec is deterministic); the conclusion is "for every admissible `E` there is a
  decomposition" (implied by the lemma since `𝒢^VX_Y` has positive probability; consumers use
  only this). "Decomposes into objects": `IsDecomp ↑E D` (`E ⊆ E(G)` is loopless).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemDemoted] Lemma fallback for demoted light parts, deterministic form: a demoted light
part `Y` is not a good parent (so none of its classes is available to Lemma s5:lemParent), and
every edge set `E` with `E(X_Y) ⊆ E ⊆ E_r(Y)` decomposes into at most `80|Y|` objects, in the
setting of Section s5 (`RunHyp`). -/
def LemDemotedStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ ω ∈ (Stage1.law G run).supp, ∀ Y ∈ run.lightParts G, demoted ω Y →
      ¬ goodParent ω Y ∧ (∀ l : ℕ, Y ∉ goodParents ω l) ∧
      ∀ E : Finset (Sym2 V), (run.X G Y.1 Y.2).edges ⊆ E → E ⊆ run.E G Y.1 Y.2 →
        ∃ D : List (Obj V), IsDecomp (E : Set (Sym2 V)) D ∧
          D.length ≤ 80 * (run.ancVerts G Y).card

end EG.Spec
