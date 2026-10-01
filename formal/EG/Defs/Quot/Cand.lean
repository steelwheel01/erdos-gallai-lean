module

public import EG.Defs.Chain.Lending
public import EG.Defs.Stage1.Pool
public import EG.Defs.Stage1.COL

/-!
# Candidates and JV-bad ports (manuscript s7:defCand)

PROTECTED FILE (`EG/Defs/**`): changes need the approval procedure in `APPROVALS/README.md`.

Manuscript v6.1, `s7.tex`, Definition [s7:defCand] ("Candidates and JV-bad ports"), quoted in the
docstrings below. Design note: `formal/work/p2d/quot.md`. Namespace `EG.Quot`; TRIAGE §3 item 29.

Encoding decisions (TRIAGE §2.7 CAND-MEAN-DEF, §2.10; blueprint s7a CAND-*):
* the threshold `½ E|Cand_l(u)|` is written with the closed form
  `candMean = q_l π_{l,r} p_Y deg_{H_Y}(u)` (Lemma [s7:lemCand] (ii), first equality, which is a
  Spec obligation); so JV-badness does not depend on the definition of the stage-1 law;
* the stage-1 outcome is read, as in s6 (design note `work/p2d/design.md`, D-DES-1), through the
  stage-data record `S : EG.Chain.StageData V` (the classes `LJV_{Y,l} = S.ljv Y l`) and the pool
  labels `π : ↥G.verts → Option (ℕ × ℕ)` of component (1d) (`EG.Stage1.poolSet`); for an outcome
  `ω` these are `StageData.ofOutcome ω …` and `ω.pool`;
* the class `Y(u)` of a classed port `u` of round `l` is `δ l u` (`EG.Chain.Designation`), its round
  `r(u) = (δ l u).1`;
* `Cand`, `candMean` and `JVBad` are total in `(l, u)`; `JVBad` contains "`u` is a classed port of
  round `l`" (`EG.Chain.classedPorts`), so that only classed ports can be JV-bad;
* `Hcd_l := λ_{l-2}^{95}/(8M_l^2)` is defined through `HcdOf M λ`, which the abstract round input of
  `EG.Defs.Quot.Round` uses as well (`RoundInput.Hcd`), so that the two agree by `rfl` on
  `RoundInput.ofPast`.
-/

@[expose] public section

namespace EG.Quot

open EG.HB EG.Chain

/-- The formula `Hcd = λ^{95}/(8M^2)` of [s7:defCand] as a function of `M` (a natural number,
v6.1 (R2)) and `λ` (a real number). -/
noncomputable def HcdOf (M : ℕ) (lam : ℝ) : ℝ := lam ^ 95 / (8 * (M : ℝ) ^ 2)

/-- The formula `θ^ult = ⌊M Hcd/7⌋` of [s7:consRound] (c) as a function of `M` and `Hcd`. -/
noncomputable def thultOf (M : ℕ) (Hcd : ℝ) : ℕ := ⌊(M : ℝ) * Hcd / 7⌋₊

variable {V : Type*} [DecidableEq V] (run : Run V) (G : FGraph V) (δ : Designation V)
  (S : StageData V)

/-- [s7:defCand] "Put `Hcd_l := λ_{l-2}^{95}/(8M_l^2)`" (`λ_{l-2} = run.lam G (l - 2)`, read for
`l ≥ 3`). -/
noncomputable def Hcd (l : ℕ) : ℝ := HcdOf (run.M G l) (run.lam G (l - 2))

/-- [s7:consRound] (c) "`θ^ult_l := ⌊M_l Hcd_l/7⌋`" (run form; `RoundInput.thult` is the same
formula on the abstract round input). -/
noncomputable def thult (l : ℕ) : ℕ := thultOf (run.M G l) (Hcd run G l)

/-- [s7:defCand] "Let `u` be a classed port of round `l ≥ 3`, with class `Y := Y(u)` of round
`r := r(u) ≤ l-2`. Its *candidate set* is `Cand_l(u) := {w ∈ Pool_{l,r(u)} : uw ∈ LJV_{Y,l}}`."
Here `Y(u) = δ l u`, `r(u) = (δ l u).1`, `Pool_{l,r} = Stage1.poolSet G π l r` and
`LJV_{Y,l} = S.ljv Y l`. Total in `(l, u)`; read at classed ports of round `l`. -/
noncomputable def cand (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (u : V) : Finset V :=
  (Stage1.poolSet G π l (δ l u).1).filter (fun w => s(u, w) ∈ S.ljv (δ l u) l)

/-- [s7:defCand], [s7:lemCand] (ii) the mean `E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u)` in
closed form (TRIAGE §2.7 CAND-MEAN-DEF: "Here `E` is the unconditional expectation over stage 1,
which is a number determined by the run and `δ`"; the equality with the expectation is Lemma
[s7:lemCand] (ii), first equality). `Y = δ l u`, `r = r(Y)`, `q_l = Stage1.qPool`,
`π_{l,r} = Stage1.piPool`, `p_Y = Stage1.pY`, `H_Y = run.ancGraph G Y`. -/
noncomputable def candMean (l : ℕ) (u : V) : ℝ :=
  Stage1.qPool G run l * Stage1.piPool l (δ l u).1 * Stage1.pY G run (δ l u) *
    ((run.ancGraph G (δ l u)).deg u : ℝ)

/-- [s7:defCand] "The port `u` is *JV-bad* if `|Cand_l(u)| < ½ E|Cand_l(u)|`, and *JV-good*
otherwise. … The definition applies to every classed port, whether or not it lies in `Lost_l`."
(`u` a classed port of round `l`, i.e. `u ∈ Q_Z` for some `Z ∈ Std_l`; the mean in closed form,
`candMean`.) -/
def JVBad (π : ↥G.verts → Option (ℕ × ℕ)) (l : ℕ) (u : V) : Prop :=
  u ∈ classedPorts run G l ∧ ((cand G δ S π l u).card : ℝ) < candMean run G δ l u / 2

end EG.Quot
