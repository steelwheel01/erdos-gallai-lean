module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages
public import EG.Defs.Light.Constants

/-!
# Statement of Lemma expected demotion and lost-parent mass (manuscript s5:lemExpect)

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:lemExpect.

Manuscript v6.1, `s5.tex`, Lemma [s5:lemExpect]: "Over the stage-1 randomness,
`E[c_VX dem + c_PV lp] ≤ ε_U(D_*) n`, where `ε_U(D_*) := 2462 (log₂D_*)^{-205}`.
Moreover `ε_U(D_*) → 0` as `D_* → ∞`."

Formal reading.
* Setting: `EG.RunHyp N0 Dstar G run`; `n = G.card`.
* "Over the stage-1 randomness": the joint stage-1 law `EG.Stage1.law G run` (TRIAGE §2.7; the
  consumers s6:lemLost and s7:lemEXprime take expectations on it).
* `c_VX = 80` (Theorem s4:thmVXp) and `c_PV = 369` (Lemma s4:lemPV) are numerals (blueprint:
  "Constants 80, 369, 745 are numerals in Specs"); `dem`, `lp` are `EG.Light.dem ω`,
  `EG.Light.lp ω` (natural numbers, cast to `ℝ`); `ε_U` is `EG.Light.epsU` (the locked copy of
  the formula).
* The limit "`ε_U(D_*) → 0` as `D_* → ∞`" is the separate statement `LemExpectLimitStatement`
  (`Filter.atTop`); it is proved in `EG.Lib.Light.Constants` (`EG.Light.tendsto_epsU`).
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Stage1 EG.Light

universe u

/-- [s5:lemExpect] "Over the stage-1 randomness, `E[c_VX dem + c_PV lp] ≤ ε_U(D_*) n`"
(`c_VX = 80`, `c_PV = 369`), in the setting of Section s5 (`RunHyp`). -/
def LemExpectStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    (Stage1.law G run).expect (fun ω => 80 * (dem ω : ℝ) + 369 * (lp ω : ℝ)) ≤
      epsU Dstar * (G.card : ℝ)

/-- [s5:lemExpect] "Moreover `ε_U(D_*) → 0` as `D_* → ∞`." -/
def LemExpectLimitStatement : Prop :=
  Filter.Tendsto epsU Filter.atTop (nhds 0)

end EG.Spec
