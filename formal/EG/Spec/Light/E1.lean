module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages

/-!
# Statement of Lemma bad probabilities (manuscript s5:lemE1)

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:lemE1.

Manuscript v6.1, `s5.tex`, Lemma [s5:lemE1]: "Let `Y` be a light part of round `r`. Over the
stage-1 randomness:
(a) `P((E1) fails for Y) ≤ 3L_Y|Y| exp(−L_Y^5/32)`;
(b) `P(Y is demoted) ≤ |Y|^{-2}/2`;
(c) `P(Y ∈ Bad) ≤ |Y|^{-2}`."

Formal reading.
* Setting: `EG.RunHyp N0 Dstar G run` (the section's standing hypotheses; the proof uses Γ1 and
  the run through s3:lemCOL, s3:lemCOLJV, (s5:eqLY)).
* "Over the stage-1 randomness": the joint stage-1 law `EG.Stage1.law G run` (TRIAGE §2.7); this
  is the space on which the consumers s5:lemExpect and s6:lemLost take probabilities.
* The events are the Defs `EG.Light.E1`, `EG.Light.demoted`, `EG.Light.Bad` of the outcome `ω`.
* `|Y| = (run.ancVerts G Y).card` (as a real), `L_Y = run.LY G Y`, `exp = Real.exp`,
  `|Y|^{-2}` an integer power.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemE1] Lemma bad probabilities, (a)–(c), for every light part `Y`, over the stage-1 law,
in the setting of Section s5 (`RunHyp`). -/
def LemE1Statement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ Y ∈ run.lightParts G,
      -- (a)
      (Stage1.law G run).prob {ω | ¬ E1 ω Y} ≤
        3 * run.LY G Y * ((run.ancVerts G Y).card : ℝ) * Real.exp (-(run.LY G Y ^ 5) / 32) ∧
      -- (b)
      (Stage1.law G run).prob {ω | demoted ω Y} ≤ ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ) / 2 ∧
      -- (c)
      (Stage1.law G run).prob {ω | Y ∈ Bad ω} ≤ ((run.ancVerts G Y).card : ℝ) ^ (-2 : ℤ)

end EG.Spec
