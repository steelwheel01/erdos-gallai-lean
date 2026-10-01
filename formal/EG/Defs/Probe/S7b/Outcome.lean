module

public import EG.Defs.Quot.Round
public import EG.Defs.Quot.Xprime
public import EG.Defs.Light.Stages
public import EG.Defs.Chain.StageInst

/-!
# The stage data, the past and the functional `X'` of a stage-1 outcome (probe Defs, unit S7b)

New Defs file of the P2 Spec unit s7b (`formal/work/p2s/s7b.md`). It adds three abbreviations
that the s7b Specs (`EG/Spec/Quot/{Vstar,Pay,EXprime,UHsplit,OneOutcome,Cost,JVps}.lean`) need and
that no locked Defs file provides; each is a composition of locked Defs, nothing else.

* `stageOf ω`: the stage data (`EG.Chain.StageData`) of the stage-1 outcome
  `ω : EG.Stage1.Outcome G run`, with the s5 statuses of [s5:defStages] (`EG.Light.demoted ω`,
  `EG.Light.dem ω`, `EG.Light.lp ω`) as its status fields. This is the instantiation contract of
  work/p2d/design.md (D-DES-1) and TRIAGE §3 item 20 (G-S5-1: "the s6 record is
  `StageData.ofOutcome ω (demoted …) (dem …) (lp …)`").
* `pastOf run G δ ω l J`: the past of round `l` as read by the s7 round step
  ([s7:consRound] "Fix `3 ≤ l ≤ R` and the past `Past_l`. The input is the set `J_l` …"), i.e.
  `EG.Quot.RoundInput.ofPast` at the stage data `stageOf ω` and the pool labels `ω.pool` of
  component (1d).
* `XprimeOf run G δ ω`: the functional `X'` of [s7:defXprime] at the outcome `ω`
  (`EG.Quot.Xprime` at `stageOf ω` and `ω.pool`); similarly `XUOf`, `XpoolOf`, `XVOf` for its three
  terms. As functions of `ω` their expectations under `EG.Stage1.law G run` are the manuscript's
  `E X'`, `E X_U`, `E X_pool`, `E X_V` ("`E` is over the stage-1 law").
-/

@[expose] public section

namespace EG.Quot

open EG.HB EG.Chain

variable {V : Type*} [DecidableEq V]

/-- [s6:defLending], [s5:defStages] "Fix a valid run, a designation `δ` and a stage-1 outcome …
with its stage-2 data": the stage data of the stage-1 outcome `ω`, whose status fields are the
s5 statuses `demoted`, `dem`, `lp` of `ω`. -/
noncomputable def stageOf {G : FGraph V} {run : Run V} (ω : Stage1.Outcome G run) :
    StageData V :=
  StageData.ofOutcome ω (Light.demoted ω) (Light.dem ω) (Light.lp ω)

/-- [s7:consRound] the past of round `l` of the stage-1 outcome `ω` with the J-set `J`, as read by
the round step: `RoundInput.ofPast` at `stageOf ω` and the pool labels `ω.pool`. -/
noncomputable def pastOf (run : Run V) (G : FGraph V) (δ : Designation V)
    (ω : Stage1.Outcome G run) (l : ℕ) (J : Finset (Sym2 V)) : RoundInput V :=
  RoundInput.ofPast run G δ (stageOf ω) ω.pool l J

/-- [s6:defLending] `X_U` at the stage-1 outcome `ω`. -/
noncomputable def XUOf (run : Run V) (G : FGraph V) (δ : Designation V)
    (ω : Stage1.Outcome G run) : ℕ :=
  XU run G δ (stageOf ω)

/-- [s7:defXprime] `X_pool` at the stage-1 outcome `ω`. -/
noncomputable def XpoolOf (run : Run V) (G : FGraph V) (δ : Designation V)
    (ω : Stage1.Outcome G run) : ℕ :=
  Xpool run G δ (stageOf ω) ω.pool

/-- [s7:lemVstar] `X_V` at the stage-1 outcome `ω` (a function of the pool labels only). -/
noncomputable def XVOf (run : Run V) (G : FGraph V) (ω : Stage1.Outcome G run) : ℕ :=
  XV run G ω.pool

/-- [s7:defXprime] "`X' := X_U + X_pool + X_V`" at the stage-1 outcome `ω`. -/
noncomputable def XprimeOf (run : Run V) (G : FGraph V) (δ : Designation V)
    (ω : Stage1.Outcome G run) : ℕ :=
  Xprime run G δ (stageOf ω) ω.pool

end EG.Quot
