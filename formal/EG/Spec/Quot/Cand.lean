module

public import EG.Defs.Quot.Cand
public import EG.Defs.Chain.StageInst
public import EG.Defs.Gamma.Full

/-!
# Statement of Lemma "Candidate counts" (manuscript s7:lemCand)

Statement file (`EG/Spec/**`), chunk s7a (P2 Specs). Status note: `formal/work/p2s/s7a.md`.
Definitions: `EG.Quot.cand`, `EG.Quot.candMean`, `EG.Quot.JVBad`, `EG.Quot.Hcd`
(`EG/Defs/Quot/Cand.lean`), the stage-1 law `EG.Stage1.law` and the record
`EG.Chain.StageData` (`EG/Defs/Chain/Lending.lean`, `StageData.ofOutcome` in
`EG/Defs/Chain/StageInst.lean`).

Manuscript v6.1, `s7.tex`, Lemma [s7:lemCand]:
"Let `u` be a classed port of round `l ≥ 3` with class `Y` of round `r`. Then:
(i) `|Cand_l(u)|` is a sum of independent Bernoulli variables, one for each `w ∈ N_{H_Y}(u)`, each
with success probability `q_l π_{l,r} p_Y`;
(ii) its mean satisfies `E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u) ≥ λ_r^{96} 2^{-(l-r)}/M_l^2 ≥ 2Hcd_l`;
(iii) `P(u is JV-bad) ≤ exp(−Hcd_l/4)`;
(iv) if `u` is JV-good then `|Cand_l(u)| ≥ Hcd_l ≥ 2^{10} M_l^{10}`."
Proof of (i): "By definition,
`|Cand_l(u)| = Σ_{w ∈ N_{H_Y}(u)} 1[plab(w) = (l,r)] · 1[uw ∈ LJV_{Y,l}]`."

Formal reading.
* Setting (section setting of s7, CAND-GAMMA-IMPLICIT): `EG.RunHyp N0 Dstar G run` (Γ1, Γ3,
  `N0Cond`, `n ≥ N_0`, `d_1 ≥ D_*`, a valid run; TRIAGE §2.6: s7 Specs take `RunHyp`; Γ4 is not
  used) and a designation `δ` with `IsDesignation run G δ` ("a designation `δ` is fixed").
  "A classed port of round `l ≥ 3`" is `3 ≤ l` and `u ∈ Chain.classedPorts run G l`; its class is
  `Y = δ l u`, of round `r = (δ l u).1`. (`l ≤ R` is not assumed: there are no classed ports of
  rounds `l > R`, `Std_l = ∅`.)
* Probabilities and expectations are over the stage-1 law `Stage1.law G run` ("`E` is the
  unconditional expectation over stage 1"). The candidate set of an outcome `ω` is
  `cand G δ (Sω ω) ω.pool l u`, where `Sω ω` is the stage-data record of `ω` as s6/s7 read it: its
  JV-lent classes are those of `ω` (hypothesis `hS`, `(Sω ω).ljv Y l = E(LJV_{Y,l}(ω))`, the field
  `ljv` of `StageData.ofOutcome ω …`). The other fields of the record (the s5 status data, which
  `cand` and `JVBad` do not read) are left free, so consumers may pass
  `Sω ω := StageData.ofOutcome ω (demoted ω) (dem ω) (lp ω)` with any s5 data.
* (i): `N_{H_Y}(u) = (run.ancGraph G Y).nbrs u`; the summand of `w` is the product of the two
  indicators, as a real random variable; "independent" is `FinDist.iIndepFun` of the family
  indexed by `↥N_{H_Y}(u)`; "Bernoulli … with success probability `p`" is `P(summand = 1) = p`
  (the summands are `{0,1}`-valued by construction). `q_l = Stage1.qPool`, `π_{l,r} = Stage1.piPool`,
  `p_Y = Stage1.pY`.
* (ii): `E|Cand_l(u)|` is the expectation of the cardinality; the closed form
  `q_l π_{l,r} p_Y deg_{H_Y}(u)` is the Defs constant `candMean` (TRIAGE §2.7 CAND-MEAN-DEF: JV-badness
  is defined with it, and this first equality is what ties it to the TeX's `½ E|Cand_l(u)|`).
  `λ_r = run.lam G r`, `M_l = run.M G l` (a natural number, cast), `2^{-(l-r)}` the integer power
  `(2:ℝ) ^ (-((l:ℤ) - r))`. The two inequalities are deterministic.
* (iii): the event `{ω | JVBad run G δ (Sω ω) ω.pool l u}`.
* (iv): deterministic, stated for every stage-data record `S` and every pool-label family `π`
  (the TeX's "if `u` is JV-good then …" for a stage-1 outcome is the case `S = Sω ω`, `π = ω.pool`;
  the claim only uses `candMean ≥ 2Hcd_l`, a fact about the run, so the general form is the
  same statement in the form `RoundInput.ofPast_valid` (field `good_cand`) consumes). The second
  inequality `Hcd_l ≥ 2^{10} M_l^{10}` is stated on its own (it does not depend on the outcome; it is
  the field `Hcd_ge` of `RoundInput.Valid`).

Consumers: s7:lemEXprime (chunk s7b) uses (iii) and (iv) in exactly this form (the event is
`JVBad run G δ S π l u` with `S` the record of the outcome, as in `EG.Quot.jvBadPorts`);
`RoundInput.ofPast_valid` (joint s6/s7 unit) uses (iv) for the fields `good_cand` and `Hcd_ge`.
-/

@[expose] public section

namespace EG.Spec

open EG.HB EG.Chain EG.Quot

/-- [s7:lemCand] "Let `u` be a classed port of round `l ≥ 3` with class `Y` of round `r`. Then:
(i) `|Cand_l(u)|` is a sum of independent Bernoulli variables, one for each `w ∈ N_{H_Y}(u)`, each
with success probability `q_l π_{l,r} p_Y`; (ii) its mean satisfies
`E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u) ≥ λ_r^{96} 2^{-(l-r)}/M_l^2 ≥ 2Hcd_l`;
(iii) `P(u is JV-bad) ≤ exp(−Hcd_l/4)`; (iv) if `u` is JV-good then
`|Cand_l(u)| ≥ Hcd_l ≥ 2^{10} M_l^{10}`." (Proof of (i): "`|Cand_l(u)| =
Σ_{w ∈ N_{H_Y}(u)} 1[plab(w) = (l,r)] · 1[uw ∈ LJV_{Y,l}]`".) -/
def CandCountStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : Run V) (δ : Designation V),
    RunHyp N0 Dstar G run → IsDesignation run G δ →
    ∀ (Sω : Stage1.Outcome G run → StageData V),
      (∀ ω Y l, (Sω ω).ljv Y l = (Stage1.LJV G run Y (ω.colAt Y) l).edges) →
    ∀ (l : ℕ) (u : V), 3 ≤ l → u ∈ classedPorts run G l →
      -- (i) the sum of the indicators over `N_{H_Y}(u)`
      (∀ ω : Stage1.Outcome G run,
          ((cand G δ (Sω ω) ω.pool l u).card : ℝ) =
            ∑ w ∈ (run.ancGraph G (δ l u)).nbrs u,
              (if Stage1.plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
                (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0)) ∧
      -- (i) the summands are mutually independent
      (Stage1.law G run).iIndepFun
        (fun (w : ↥((run.ancGraph G (δ l u)).nbrs u)) (ω : Stage1.Outcome G run) =>
          (if Stage1.plabOf ω.pool (w : V) = some (l, (δ l u).1) then (1 : ℝ) else 0) *
            (if s(u, (w : V)) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0)) ∧
      -- (i) each is Bernoulli with success probability `q_l π_{l,r} p_Y`
      (∀ w ∈ (run.ancGraph G (δ l u)).nbrs u,
          (Stage1.law G run).prob {ω |
            (if Stage1.plabOf ω.pool w = some (l, (δ l u).1) then (1 : ℝ) else 0) *
              (if s(u, w) ∈ (Sω ω).ljv (δ l u) l then (1 : ℝ) else 0) = 1} =
            Stage1.qPool G run l * Stage1.piPool l (δ l u).1 * Stage1.pY G run (δ l u)) ∧
      -- (ii) `E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u) ≥ λ_r^{96} 2^{-(l-r)}/M_l^2 ≥ 2Hcd_l`
      (Stage1.law G run).expect (fun ω => ((cand G δ (Sω ω) ω.pool l u).card : ℝ)) =
        candMean run G δ l u ∧
      run.lam G (δ l u).1 ^ 96 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) / (run.M G l : ℝ) ^ 2 ≤
        candMean run G δ l u ∧
      2 * Hcd run G l ≤
        run.lam G (δ l u).1 ^ 96 * (2 : ℝ) ^ (-((l : ℤ) - (δ l u).1)) / (run.M G l : ℝ) ^ 2 ∧
      -- (iii) `P(u is JV-bad) ≤ exp(−Hcd_l/4)`
      (Stage1.law G run).prob {ω | JVBad run G δ (Sω ω) ω.pool l u} ≤
        Real.exp (-(Hcd run G l) / 4) ∧
      -- (iv) JV-good ⇒ `|Cand_l(u)| ≥ Hcd_l`, and `Hcd_l ≥ 2^{10} M_l^{10}`
      (∀ (S : StageData V) (π : ↥G.verts → Option (ℕ × ℕ)),
          ¬ JVBad run G δ S π l u → Hcd run G l ≤ ((cand G δ S π l u).card : ℝ)) ∧
      (2 : ℝ) ^ 10 * (run.M G l : ℝ) ^ 10 ≤ Hcd run G l

end EG.Spec
