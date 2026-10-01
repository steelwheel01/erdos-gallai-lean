module

public import EG.Defs.Gamma.Full
public import EG.Defs.Light.Stages
public import EG.Defs.Log

/-!
# Statements of the setting equations of Section s5 (manuscript s5:eqLY, s5:eqZp)

Statement file (`EG/Spec/**`) of the P2 s5 Spec unit (`formal/work/p2s/s5.md`); blueprint s5,
node s5:defZones (setting equations; blueprint ZONE-SETTING-FACTS).

RECONSTRUCTED FILE: the s5 unit's original of this file was overwritten by accident by probe unit
P4B (2026-09-30, the file was untracked); P4B rewrote it from the back-translation in
`formal/work/p2s/s5.md` ("s5:eqLY — `EqLYStatement`", "s5:eqZp — `EqZpStatement`"): the same two
names, the same seven inequalities of `EqLYStatement` (with `R − r` a real difference) and the same
sum of `EqZpStatement`. The s5 unit (or its reviewer) must re-check it against its original. See
`formal/work/p2b/P4B.md`, "Problems".

Manuscript v6.1, `s5.tex`, setting paragraph: "for a light part `Y` of round `r`,
(s5:eqLY) `|Y| ≥ P_r/2 ≥ λ_r^{103}/2`, `L_Y ≥ 103 log₂λ_r − 1 ≥ 102 log₂λ_r`,
`R − r ≤ 2 log* d_r + 2 ≤ log₂λ_r`, by Proposition s2:propStructure(iv), `P_r = ⌈λ_r^{C'}⌉` with
`C' = 103`, and Lemma s2:lemTower(a),(d). In particular `R − r ≤ L_Y/102`. Moreover, for every
vertex `v`, (s5:eqZp) `Σ_{Y∋v} L_Y^{-2} < 1/2`, the sum over all light parts `Y` containing `v`."

Formal reading: setting `EG.RunHyp N0 Dstar G run`; a light part `Y ∈ run.lightParts G` of round
`r = Y.1`, `|Y| = (run.ancVerts G Y).card`, `L_Y = run.LY G Y`, `λ_r = run.lam G r`,
`P_r = run.P G r`, `d_r = run.d G r`, `log* = EG.logStar` (base 2), `log₂ = Real.logb 2`; `R − r`
is a real difference; `L_Y^{-2}` is an integer power.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s5:eqLY] "for a light part `Y` of round `r`, `|Y| ≥ P_r/2 ≥ λ_r^{103}/2`,
`L_Y ≥ 103 log₂λ_r − 1 ≥ 102 log₂λ_r`, `R − r ≤ 2 log* d_r + 2 ≤ log₂λ_r` … In particular
`R − r ≤ L_Y/102`" (s5 setting, `RunHyp`). -/
def EqLYStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ Y ∈ run.lightParts G,
      (run.P G Y.1 : ℝ) / 2 ≤ ((run.ancVerts G Y).card : ℝ) ∧
      run.lam G Y.1 ^ 103 / 2 ≤ (run.P G Y.1 : ℝ) / 2 ∧
      103 * Real.logb 2 (run.lam G Y.1) - 1 ≤ run.LY G Y ∧
      102 * Real.logb 2 (run.lam G Y.1) ≤ 103 * Real.logb 2 (run.lam G Y.1) - 1 ∧
      (run.R : ℝ) - (Y.1 : ℝ) ≤ 2 * (logStar (run.d G Y.1) : ℝ) + 2 ∧
      2 * (logStar (run.d G Y.1) : ℝ) + 2 ≤ Real.logb 2 (run.lam G Y.1) ∧
      (run.R : ℝ) - (Y.1 : ℝ) ≤ run.LY G Y / 102

open Classical in
/-- [s5:eqZp] "for every vertex `v`, `Σ_{Y∋v} L_Y^{-2} < 1/2`, the sum over all light parts `Y`
containing `v`" (s5 setting, `RunHyp`). -/
def EqZpStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : Run V),
    RunHyp N0 Dstar G run →
    ∀ v : V,
      ∑ Y ∈ (run.lightParts G).filter (fun Y => v ∈ run.ancVerts G Y), run.LY G Y ^ (-2 : ℤ) <
        1 / 2

end EG.Spec
