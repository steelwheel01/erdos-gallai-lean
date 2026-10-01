module

public import EG.Defs.HB.Run
public import EG.Defs.Gamma.Core

/-!
# Statement of Lemma-25 size cap, part (ii), in full (manuscript s2:lemCap (ii))

Statement file (`EG/Spec/**`), unit P2 specs chunk s2a. Status note `formal/work/p2s/s2a.md`.
Blueprint `formal/work/p2/blueprint_s2a.md` (node `s2:lemCap`, CAP-GAMMA-EXPLICIT, CAP-RUN-API,
CAP-M-CEIL), blueprint s2b DR-ROUND-LOCAL, TRIAGE §2.2 ("Round-level Specs: lemCap(ii), propOV and
propDegRec are stated at round level (hypotheses `Round.Valid`, `Dstar ≤ Round.d n H`), with
run-level corollaries").

Existing related Specs (not edited): part (i) is `EG.Spec.CapStatement`, the remark is
`EG.Spec.CapUniformStatement`, the graph step of the proof is `EG.Spec.CapGraphStatement`
(`EG/Spec/HB/Cap.lean`); the run-level form of the first three clauses of (ii) is
`EG.Spec.CapPrePartStatement` (`EG/Spec/HB/CapPrePart.lean`, unit P2J), which omits the last
clause (on `τ_l`). This file adds
* `CapRoundStatement`: all of (ii) at round level (for one valid round with `d_l ≥ D_*`, also of
  an unfinished execution, as in `RunTerminatesStatement`). It assumes the full
  `Round.Valid`, whose fourth field presupposes the `τ`-runs, so the `τ`-run termination step of
  s2:propExists (`RoundTauTermStatement`, `EG/Spec/HB/Exists.lean`, hypotheses `CyclesValid`,
  `IsS0Rec`, `StopsAt` only) cannot use it; there the piece cap comes from a Lib lemma under
  those partial hypotheses (from `CapGraphStatement`, (R1) and the `s = 0` stopping rule), which
  also gives clause (1) here;
* `CapRunTauStatement`: the last clause of (ii) at run level (the form in which s2:propOV,
  s2:propStructure (ii) and s2:propDegRec apply Lemma 14^τ to the `τ`-runs of a valid run).
`CapRoundStatement` and `CapPrePartStatement` together imply `CapRunTauStatement` only through the
Run API (`run.d G l = Round.d (run.graph G l)`, validity of each round); the run-level statement is
therefore written out.

Manuscript v6.1, `s2.tex`, Lemma [s2:lemCap] (ii):
"In every round `l ≤ R` of a valid `HB^tp` run, every `s = 0` piece `𝒫` satisfies `|𝒫| ≤ M_l`.
Hence every round-`l` pre-part has `|Z^0| ≤ M_l`; for every round-`l` part `Z` (light or
standalone) every vertex is incident with at most `M_l − 1` edges of `E_l(Z)`; and
`τ_l ≥ 128 s_l log²|𝒫|`, so Lemma s2:lem14tau applies to the `τ`-run of every piece with
`|𝒫| ≥ P_l`."

Formal reading.
* Hypothesis `Gamma2a Dstar` (`D_* ≥ 2^{117}`): the proof uses "By Γ2(a) (Condition s1:condG2),
  `d_l ≥ D_* ≥ 2^{117}`" (blueprint CAP-GAMMA-EXPLICIT); "round `l ≤ R` of a valid run" is, at
  round level, `Round.Valid H c` with `D_* ≤ Round.d H` (`H = G_l`, `c` the choices of round `l`),
  and at run level `run.Valid G Dstar` with `l ∈ [1, R]`.
* `M_l = MOf d_l ∈ ℕ` (v6.1 (R2) with the ceiling); `s_l = sOf d_l`, `τ_l = tauOf d_l`,
  `P_l = POf d_l` (natural numbers). "incident with at most `M_l − 1` edges of `E_l(Z)`" is
  `degE (E_l(Z)) v ≤ M_l − 1` in `ℕ` for every vertex `v` (as in `CapPrePartStatement`;
  `M_l ≥ 2^{40}`, so the subtraction is exact). The part of the pre-part `a` is indexed by `a`
  (its light part if light, itself if standalone), `E_l(Z) = Round.E H c a`.
* "`τ_l ≥ 128 s_l log²|𝒫|`" is the real inequality in the form of the hypothesis of the
  Lemma 14^τ Specs (`128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ`, `EG/Spec/HB/Lemma14Tau.lean`).
* "so Lemma s2:lem14tau applies to the `τ`-run of every piece with `|𝒫| ≥ P_l`" is written as the
  remaining hypotheses of those Specs: `1 ≤ s_l`, and, for every big piece `q`
  (`q ∈ bigPieceAddrs`, i.e. `|𝒫| ≥ P_l`), the tree `c.tauRun q` is a `τ`-run of the piece graph
  with parameters `(s_l, τ_l)` (`IsTauRun epsC s_l τ_l`). The last one is a field of `Round.Valid`;
  it is restated so that consumers get all hypotheses of Lemma 14^τ from one statement.
-/

@[expose] public section

namespace EG.Spec

open EG.HB

universe u

/-- [s2:lemCap] (ii), round level: "In every round `l ≤ R` of a valid `HB^tp` run, every `s = 0`
piece `𝒫` satisfies `|𝒫| ≤ M_l`. Hence every round-`l` pre-part has `|Z^0| ≤ M_l`; for every
round-`l` part `Z` (light or standalone) every vertex is incident with at most `M_l − 1` edges of
`E_l(Z)`; and `τ_l ≥ 128 s_l log²|𝒫|`, so Lemma s2:lem14tau applies to the `τ`-run of every piece
with `|𝒫| ≥ P_l`." (One round with input graph `H = G_l` and choices `c`, valid, with
`D_* ≤ d_l` and `Γ2(a)`; module docstring.) -/
def CapRoundStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (c : RoundChoice V) (Dstar : ℝ),
    Gamma2a Dstar → Dstar ≤ Round.d H → Round.Valid H c →
      (∀ q ∈ Round.pieceAddrs c, (Round.piece H c q).card ≤ MOf (Round.d H)) ∧
      (∀ a ∈ Round.prePartAddrs H c,
        (Round.Z0 H c a).card ≤ MOf (Round.d H) ∧
        ∀ v : V, degE (Round.E H c a) v ≤ MOf (Round.d H) - 1) ∧
      (∀ q ∈ Round.pieceAddrs c,
        128 * (sOf (Round.d H) : ℝ) * Real.logb 2 (Round.piece H c q).card ^ 2 ≤
          (tauOf (Round.d H) : ℝ)) ∧
      1 ≤ sOf (Round.d H) ∧
      ∀ q ∈ Round.bigPieceAddrs H c,
        (c.tauRun q).IsTauRun epsC (sOf (Round.d H)) (tauOf (Round.d H) : ℝ) (Round.piece H c q)

/-- [s2:lemCap] (ii), last clause, run level: "In every round `l ≤ R` of a valid `HB^tp` run, …
`τ_l ≥ 128 s_l log²|𝒫|`, so Lemma s2:lem14tau applies to the `τ`-run of every piece with
`|𝒫| ≥ P_l`" (under `Γ2(a)`; the first clauses at run level are `CapPrePartStatement`). -/
def CapRunTauStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    ∀ l ∈ Finset.Icc 1 run.R,
      (∀ q ∈ run.pieceAddrs l,
        128 * (run.s G l : ℝ) * Real.logb 2 (run.piece G l q).card ^ 2 ≤ (run.tau G l : ℝ)) ∧
      1 ≤ run.s G l ∧
      ∀ q ∈ run.bigPieceAddrs G l,
        (run.tauRun l q).IsTauRun epsC (run.s G l) (run.tau G l : ℝ) (run.piece G l q)

end EG.Spec
