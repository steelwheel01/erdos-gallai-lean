# P2 Specs, chunk s7b (X_V, payments, X', E X', UH*-split, one outcome, cost, JV⁺*, HI″, GammaSat, main proof): status

Manuscript v6.1 `proofs/manuscript/s7.tex` lines 881–1519 (CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s7b.md`, `nodes_s7b.json`; data model TRIAGE §2 (2.4 constants/Γ,
2.6 RunHyp, 2.7 stage-1 law, 2.9 MIX-C B′, 2.10 s7 interfaces, patch set R); Defs design notes
`work/p2d/quot.md`, `work/p2d/design.md`.

Result. All 12 nodes are covered. The Spec files of this unit were written in an earlier (interrupted)
run of the unit and committed in `51a83b1`; this run re-checked every one of them against the TeX,
rebuilt them, and wrote the missing report and test file. No Spec was changed in this run.
* 8 Spec modules of this unit (14 `…Statement` defs), 1 probe Defs module, 1 test file.
* Reused: `EG/Spec/Quot/HI.lean` (locked, s7:thmHI), `EG/Spec/Gamma/Sat.lean` (unit GAMMA,
  s7:lemGammaSat), `EG/Spec/Main.lean` (locked `MainInternal`, the Tier-1 form of s7:thmMainProof).
* Build: `lake build EG.Spec.Quot.{Vstar,Pay,EXprime,UHsplit,OneOutcome,Cost,JVps,HI}
  EG.Spec.Main.CorJVpsEG EG.Spec.Gamma.Sat` succeeds;
  `scripts/check.sh EGTest/Spec_s7b.lean`: rc 0, 0 errors, 0 sorry warnings.
  `python3 -I scripts/lint.py`: 0 findings. No proofs, no stubs.
* Root imports for the orchestrator (I did not edit the root files): to `EG`,
  `EG.Defs.Probe.S7b.Outcome`, `EG.Spec.Quot.{Vstar,Pay,EXprime,UHsplit,OneOutcome,Cost,JVps}`,
  `EG.Spec.Main.CorJVpsEG` (`EG.Spec.Gamma.Sat` if it is not already imported); to `EGTest`,
  `EGTest.Spec_s7b`.

## Files

| File | Contents |
|---|---|
| `EG/Defs/Probe/S7b/Outcome.lean` (NEW Defs, probe unit S7b) | `EG.Quot.stageOf ω` (= `StageData.ofOutcome ω (Light.demoted ω) (Light.dem ω) (Light.lp ω)`), `EG.Quot.pastOf run G δ ω l J` (= `RoundInput.ofPast run G δ (stageOf ω) ω.pool l J`), `XUOf`, `XpoolOf`, `XVOf`, `XprimeOf` (the locked `XU`, `Xpool`, `XV`, `Xprime` at `stageOf ω`, `ω.pool`). Compositions of locked Defs only. |
| `EG/Spec/Quot/Vstar.lean` | `VstarStatement` |
| `EG/Spec/Quot/Pay.lean` | `PayStatement`, `PayGlobalStatement` |
| `EG/Spec/Quot/EXprime.lean` | `EXprimeStatement` |
| `EG/Spec/Quot/UHsplit.lean` | `UHsplitRoundStatement`, `UHsplitSumStatement`, `UHsplitDetStatement`, `UHsplitThetaStatement` |
| `EG/Spec/Quot/OneOutcome.lean` | `OneOutcomeStage1Statement`, `OneOutcomeRoundStatement` |
| `EG/Spec/Quot/Cost.lean` | `CostStatement`, `CostC0Statement` |
| `EG/Spec/Quot/JVps.lean` | `JVpsStatement` |
| `EG/Spec/Main/CorJVpsEG.lean` | `CorJVpsEGStatement` |
| `EGTest/Spec_s7b.lean` | non-vacuity checks (below) |

## Table: label → Lean name → file → status

Lean names are in namespace `EG.Spec` unless stated.

| label (kind) | Lean name | file | status |
|---|---|---|---|
| s7:lemVstar (lemma) | `VstarStatement`; the definitions `EG.Quot.XVl`, `EG.Quot.XV`, `EG.Quot.tCC` | `EG/Spec/Quot/Vstar.lean`; Defs `EG/Defs/Quot/Xprime.lean` | new (this unit); Defs existing (locked) |
| s7:lemPay (lemma) | `PayStatement` (per round, (a1)–(e)), `PayGlobalStatement` ((b), (d) summed over rounds); `EG.Quot.poolWeight` (Defs) | `EG/Spec/Quot/Pay.lean` | new |
| s7:defXprime (definition) | Defs `EG.Quot.{poolWeight, jvBadPorts, Xpool, Xprime}`; `XprimeOf` etc. (probe Defs) | `EG/Defs/Quot/Xprime.lean`; `EG/Defs/Probe/S7b/Outcome.lean` | existing Defs (locked) + new probe Defs; no Spec (non-negativity is by the type ℕ; determinism by the argument list) |
| s7:lemEXprime (lemma) | `EXprimeStatement`; `EG.Quot.epsX` (Defs) | `EG/Spec/Quot/EXprime.lean` | new |
| s7:lemUHsplit (lemma) | `UHsplitRoundStatement` (ii), `UHsplitSumStatement` (iii), `UHsplitDetStatement` (iv) first sentence, `UHsplitThetaStatement` (iv) "Hence…"; `EG.Quot.{detl, FQ, eps2, thetaQ}` (Defs) | `EG/Spec/Quot/UHsplit.lean` | new |
| s7:lemOneOutcome (lemma) | `OneOutcomeStage1Statement` ((1), step (i)), `OneOutcomeRoundStatement` ((3), step (iii)) | `EG/Spec/Quot/OneOutcome.lean` | new |
| s7:propCost (proposition) | `CostStatement`, `CostC0Statement`; `EG.Quot.{eps1, C0}` (Defs) | `EG/Spec/Quot/Cost.lean` | new |
| s7:thmJVps (theorem) | `JVpsStatement` | `EG/Spec/Quot/JVps.lean` | new |
| s7:thmHI (theorem) | `HIHyp`, `HIStatement` (proved: `EG.hi`) | `EG/Spec/Quot/HI.lean` | existing (locked) |
| s7:lemGammaSat (lemma) | `GammaSatItemsStatement` (i), `GammaSatEpsStatement` (ii), `GammaSatStatement` (iii), `GammaCondExistsStatement` ("In particular"); also `Col3EventuallyStatement` (s3:lemCOLJVev (iii)) | `EG/Spec/Gamma/Sat.lean` | existing (unit GAMMA; all proved in `EG/Proof/Gamma/Sat.lean`) |
| s7:thmMainProof (corollary) | `EG.Spec.MainInternal` (Tier-1, locked); `CorJVpsEGStatement` (explicit `c_EG`, Tier-2) | `EG/Spec/Main.lean`; `EG/Spec/Main/CorJVpsEG.lean` | existing (locked); new |
| s7:remNonCirc (remark) | none | — | no Spec (remark; its content is enforced by the types: `EG.Quot.eps1/eps2/C0 : ℝ → ℝ`, `JConsumer.out` reads `(l, J)` only, no Spec but HI mentions a free `c`) |

Consumers in other chunks: s7:thmJVps is consumed by s7:thmMainProof through `HIHyp`
(`JVpsStatement` gives a family indexed by `ℕ` read on `[3, R]`; the adapter to `Fin k` is
`EG.hiHyp_of_fintype_index`, existing). s1:condG4 / s1:defConstants read `eps1`, `eps2`
(locked Defs). No other chunk consumes these nodes in a Spec (MIX-C, s6b, has no Spec yet; its
B′ interface is what `CostStatement` assumes, TRIAGE §2.9).

## New Specs: TeX statement ↔ back-translation of the Lean

Common setting (all but JVps/CorJVpsEG/CostC0): `V : Type u` with decidable equality, a graph
`G : FGraph V`, reals `N0, Dstar`, a run `run`, and `RunHyp N0 Dstar G run` = Γ1(D_*) ∧ Γ3(N_0,D_*)
∧ N0Cond(N_0) ∧ n ≥ N_0 ∧ d_1 ≥ D_* ∧ the run is valid (TRIAGE §2.6). Where δ occurs:
`IsDesignation run G δ`. `E` = expectation under the joint stage-1 law `Stage1.law G run`;
`n = G.card`, `M_l = run.M G l ∈ ℕ` (cast to ℝ), `log₂ = Real.logb 2`.

### s7:lemVstar — `VstarStatement`
TeX: "For `3 ≤ l ≤ R` put `X_{V,l} := 3M_l(t^CC_l+1)|Pool_l| + 4M_l Σ_{w∈Pool_l} mult_{r(w)}(w)`,
`X_V := Σ_{l=3}^R X_{V,l}`. Each `X_{V,l}` is a deterministic function of the run and the pool
labels, and `E X_{V,l} ≤ (6 log₂M_l + 12) n/M_l`, `E X_V ≤ 2.1 (6 log₂D_* + 12) n/D_*`."
Lean: under RunHyp, (1) for every `l` with `3 ≤ l ≤ R`,
`E[XVl run G ω.pool l] ≤ (6 log₂ M_l + 12)·n/M_l`; (2) `E[XV run G ω.pool] ≤ 2.1·((6 log₂ D_* + 12)·n/D_*)`.
"Deterministic function of the run and the pool labels" is the type of `XVl` (its only random
argument is the pool-label map `π`), T0.

### s7:lemPay — `PayStatement`, `PayGlobalStatement`
TeX: (a1)–(e) as quoted in the file (s7.tex 976–1000).
Lean `PayStatement`: under RunHyp and IsDesignation, for every ω of positive stage-1 weight, every
`3 ≤ l ≤ R`, every `J` with `JPlusProps run G δ (stageOf ω) l J` ("every past"), the past
`I = pastOf … l J`, and every valid rule `R : Rules I`:
(a1) `|I.Jlost| ≤ (M_l − 1)·|Lost_l|`;
(a2) `#(items with an end in Pool_l) ≤ Σ_{v∈Pool_l} ω_l(v)`;
(a3) `#(items with a JV-bad port end) ≤ (M_l − 1)·#(JV-bad classed ports of round l)`;
(b) every fresh centre `x` lies on at most one unpaired leg, and `#unpaired legs ≤ Σ_{Z∈Std_l}|F_Z|`;
(c) `E_ξ[#SDR-paid edges] ≤ n(M_l−1)/(4M_l)^4 ≤ n/(256 M_l^3)` and
`E_ξ[#loop-paid edges] ≤ 2(2/Hcd_l)·#PAR objects ≤ 5.5 n M_l/Hcd_l` (`E_ξ` over `roundLaw`);
(d) for every ξ in the Markov event of (f), `pay^rd_l ≤ 4(n/(256M_l^3) + 5.5nM_l/Hcd_l)`, and that
number is `≤ 2n/M_l`;
(e) the paid edge set equals `Jlost ∪ paidPool ∪ paidJVBad ∪ unpairedLegs ∪ sdrPaid ∪ loopPaid`.
`PayGlobalStatement`: for families `J_l` (JPlusProps at every `3 ≤ l ≤ R`) and valid rules `R_l`:
`Σ_{l=3}^R #unpaired legs ≤ Σ_{l=1}^R Σ_{Z∈Std_l}|F_Z| ≤ 2n`; and for draws `ξ_l` in the Markov
events at every round, `Σ_{l=3}^R pay^rd_l ≤ 9n/D_*`.

### s7:lemEXprime — `EXprimeStatement`
TeX: "`E X' ≤ ε_X(D_*) n`, where `ε_X(D_*) := ε_U(D_*) + 10.3/D_* + 2.1(6 log₂D_* + 12)/D_*` … More
precisely, `E X_U ≤ ε_U(D_*) n + 5.5 n/D_*`, `E X_pool ≤ 4.8 n/D_*` and
`E X_V ≤ 2.1(6 log₂D_* + 12) n/D_*`."
Lean: under RunHyp and IsDesignation, `E X' ≤ epsX D_*·n`, `E X_U ≤ epsU D_*·n + 5.5n/D_*`,
`E X_pool ≤ 4.8n/D_*`, `E X_V ≤ 2.1(6 log₂D_* + 12)n/D_*` (the functionals at `stageOf ω`, `ω.pool`).

### s7:lemUHsplit — four statements
TeX: quoted in full in the file (s7.tex 1101–1130).
* `UHsplitRoundStatement` (ii): for every ω of positive weight, `3 ≤ l ≤ R`, `J` with JPlusProps,
  and valid rule `R` of the past: `E_ξ[|V(Q_l)|] ≤ X_{V,l}(ω.pool) + det_l`.
* `UHsplitSumStatement` (iii): if `X'(ω) ≤ 3 E X'` (ω of positive weight), then for all admissible
  `J_l`, valid rules `R_l` and draws `ξ_l` in the Markov events at every `3 ≤ l ≤ R`:
  `Σ_{l=3}^R |V(Q_l)| ≤ 12 E X' + 4 Σ_{l=3}^R det_l`.
* `UHsplitDetStatement` (iv), first sentence: under RunHyp,
  `Σ_{l=3}^R det_l ≤ 3ε_A n + 60n/D_* + 2F(log₂D_*) n` and `2F(log₂D_*) < 2^{-1000}`.
* `UHsplitThetaStatement` (iv), "Hence": in the situation of (iii), `Σ_{l=3}^R |V(Q_l)| ≤ ε_2(D_*)·n`.
  "`θ_Q ≤ 1/4` by condition Γ4" is the hypothesis Γ4, not a claim; not restated (TRIAGE §2.6 m1).

### s7:lemOneOutcome — two statements
TeX: quoted in full in the file (s7.tex 1152–1182).
* `OneOutcomeStage1Statement`: under RunHyp and IsDesignation there is a stage-1 outcome of
  positive weight with `X'(ω) ≤ 3 E X'` ((1), step (i)).
* `OneOutcomeRoundStatement`: for every such past and valid rule, the Markov event of (f) has an
  outcome of positive round-law weight, and every ξ in it satisfies
  `|V(Q_l)| ≤ 4(X_{V,l} + det_l)` and `pay^rd_l ≤ 4(n/(256M_l^3) + 5.5nM_l/Hcd_l)` ((3), step (iii)).
* (2)/(ii) and (iv): no Lean statement (deterministic stage-3 Specs; rounds 2, 1 belong to MIX-C).

### s7:propCost — `CostStatement`, `CostC0Statement`
TeX: "On an outcome as in Lemma s7:lemOneOutcome, with the round step … as the J-consumer, the
decomposition of `E(G)` given by Theorem s6:thmMIXC has at most
`(D_*/2 + 1085 + ε_1(D_*)) n + 2 Σ_{l=3}^R f(Q_l)` objects … Consequently
`C_0 = D_*/2 + 1085 + ε_1(D_*) ≤ D_*/2 + 1091` under Γ4."
Lean `CostStatement`: under RunHyp and IsDesignation, for every ω of positive weight with
`X'(ω) ≤ 3 E X'`, there are J-sets `J_l` with JPlusProps at every `3 ≤ l ≤ R` and a decomposition
`D` of `E(G)` with `|D| ≤ (D_*/2 + 1085 + ε_1(D_*))·n + 2 Σ_{l=3}^R f(Q_l)`, where
`Q_l = roundQuotient … l J_l` is the quotient of the chosen round step on `J_l` (same rules and same
`ξ_l` as the J-consumer `roundOut`).
`CostC0Statement`: for every real `D`, Γ4(D) ⇒ `C_0(D) ≤ D/2 + 1091` (checked true in EGTest).

### s7:thmJVps — `JVpsStatement`
TeX: "Assume that `D_*` satisfies Γ1–Γ4. Let `G` be a graph with `n ≥ N_0` vertices and
`d_1 ≥ D_*`. Take any valid `HB^{τ+}` run on `G`, any designation δ, and no VX-parts. Then there
are simple graphs `Q_3, …, Q_R` without isolated vertices such that (1) `f(G) ≤ C_0 n + 2Σ f(Q_l)`,
`C_0 := D_*/2 + 1085 + ε_1(D_*)`; (2) `Σ |V(Q_l)| ≤ θ_Q n`, `θ_Q = ε_2(D_*) ≤ 1/4`."
Lean: for `N0Cond N0`, `GammaCond N0 D_*` (Γ1 ∧ Γ2(a) ∧ Γ3 ∧ Γ4), `n ≥ N_0`, `d_1 ≥ D_*`, a
valid run and a designation, there are vertex types `W l` and graphs `Q l : FGraph (W l)` such
that for `3 ≤ l ≤ R` every vertex of `Q l` lies on an edge, `f(G) ≤ C_0 n + 2Σ_{l=3}^R f(Q l)`, and
`Σ_{l=3}^R |V(Q l)| ≤ θ_Q n`. "`θ_Q ≤ 1/4`" is Γ4 (a hypothesis). "No VX-parts" has no content.

### s7:thmMainProof — `CorJVpsEGStatement`
TeX (s1:thmMain, which the corollary asserts): "Let `ε, σ, C', A, N_0, D_*` be as in Definition
s1:defConstants, with `D_*` satisfying Γ1–Γ4 … `c_EG := max{C_0/(1 − 2θ_Q), N_0/2}` … Then every
graph `G` on `n` vertices satisfies `f(G) ≤ c_EG n`."
Lean: for all reals `N_0`, `D_*` with `N0Cond N0` and `GammaCond N0 D_*`, every graph `G` on any
vertex type satisfies `f(G) ≤ cEG N0 D_* · |V(G)|`, `cEG N0 D = max(C_0(D)/(1 − 2θ_Q(D)), N0/2)`.

## Hazards and choices (T0 decisions)

1. **"For every past" = every `J` with `JPlusProps` and every valid rule** (Pay, UHsplit (ii),
   OneOutcome (3)). The past enters the round step only through `J_l` (TRIAGE §2.9/2.10), and the
   fixed rules of patch set R are quantified universally (`∀ R : Rules I, R.Valid → …`), which is
   stronger than the one chosen rule. Non-vacuity for pasts read from a run needs
   `RoundInput.ofPast_valid` (s6/s7 joint obligation, TRIAGE §3 item 31): valid rules exist for
   every valid input (`Rules.exists_valid`, checked in EGTest).
2. **OO-PROCEDURAL**: lemOneOutcome is split into a stage-1 part and a round part; property (2)
   has no Lean content (TRIAGE §2.8: TPV/PV/VX⁺ are deterministic); step (iv) is inside MIX-C.
3. **OO-SUPP**: stage-1 outcomes are quantified over the support (`ω ∈ supp`), and the selections
   return positive weight.
4. **Cost is existential in the J-sets** (MIX-C B′, TRIAGE §2.9): `∃ J_l, JPlusProps ∧ ∃ D, IsDecomp
   E(G) D ∧ |D| ≤ …` with `Q_l := roundQuotient … J_l` (JV-SAME-Q). The decomposition is not named
   "the one given by MIX-C"; its only consumer (JVps) needs `f(G) ≤ |D|` with the same `Q_l`.
5. **θ_Q ≤ 1/4 is not restated** in UHsplit (iv) and JVps (2): it is the hypothesis Γ4 (TRIAGE §2.6,
   GAMMA fix round 1, m1). JVps takes `GammaCond` (so Γ4 is available to the consumer), UHsplit
   takes `RunHyp` (no Γ4).
6. **UHsplit (iv) split** into the run-only bound (`UHsplitDetStatement`) and the quotient bound
   (`UHsplitThetaStatement`).
7. **lemPay (b), (d) per round and summed** (blueprint PAY-PER-ROUND); "Σ_{l,Z}|F_Z|" runs over all
   rounds `1 ≤ l ≤ R`. (b) per centre is stated as "at most one unpaired leg contains `x`", which
   is at least as strong as the TeX (fresh centres and ports are disjoint by (J3)).
8. **lemPay (e)** is the defining equation of `Rules.paidEdges` (the Defs define the paid set as the
   union of the six categories, PAY-E-INSPECTION); the "in particular" sentence is commentary.
9. **lemVstar "deterministic function"** and **defXprime "non-negative and deterministic"** are
   carried by the types (ℕ-valued Defs whose random argument is the pool-label map), not by
   conjuncts.
10. **JVps universe**: `W : ℕ → Type u` with `V : Type u`, so that the universe-0 consumer `HIHyp`
    can use it; `CorJVpsEGStatement` is universe-polymorphic in `V` (its proof must transport the
    universe-0 `EG.hi` result, e.g. through `Fin n`).
11. **CorJVpsEG name**: named after the corollary to avoid a clash with a possible s1
    `MainExplicit`; the Tier-1 target stays the locked `MainInternal`.
12. **GammaSat (iii) for every real `N_0`** (no `N0Cond`), a strengthening recorded by unit GAMMA.

Cosmetic (not in this unit's files): in `EG/Lib/Quot/Xprime.lean` the docstring
"[s7:lemVstar] Each `X_{V,l}` is a deterministic function …" is attached to `XV_le_Xprime`
(the comment belongs to no theorem). No action needed for the Specs.

## Math findings

None. Every statement of the chunk was re-read against the TeX, including the arithmetic of
lemPay (c)/(d) (`n(M−1)(4M)^{-4} ≤ n/(256M^3)`; `176M^3/λ^{95} ≤ λ^{-1.6} ≤ 1/M` from
`M ≤ λ^{1.6}`), the UH*-split constants (`44.7 + 32.9 ≤ 78`, `29.8 ≤ 30`, already a proved Spec
`EG/Spec/Num/CC.lean`) and the propCost ledger (`745 + 338 + 2 = 1085`; bracketed terms
`80 dem + 369 lp + Σ(169 + M_l − 1)|Lost_l| + X_pool ≤ X_U + X_pool ≤ X'`).

## EGTest/Spec_s7b.lean (non-vacuity)

* `∀ ω ∈ (Stage1.law G run).supp` and the round law range over nonempty sets (`supp_nonempty`).
* `OneOutcomeStage1Statement` is proved in one line (Markov), so the hypothesis
  `X'(ω) ≤ 3 E X'` of UHsplit (iii)/(iv) and Cost is satisfiable at a positive-weight outcome.
* Valid rules exist for every valid past (`Rules.exists_valid`).
* `XVl` vanishes on the empty pool.
* `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` (`EG.exists_gammaCond`): the hypotheses of JVps and
  CorJVpsEG are satisfiable; under them `θ_Q < 1/2`; `CostC0Statement` holds;
  `cEG N0 D = max(C0 D/(1 − 2 thetaQ D), N0/2)` (the constant of HI″ at `C = C_0`, `ϑ = θ_Q`).

Not checked: satisfiability of `RunHyp` and of `JPlusProps` for a past read from a run (beyond a
cheap check; see `EGTest/Spec_s5.lean` and s6b).

## Fix round (reviews `s7b.review-fidelity-first.md`, `s7b.review-vacuity-and-consumer-form.md`)

No statement was changed. Build: `lake build EG.Spec.Quot.{Vstar,Pay,EXprime,UHsplit,OneOutcome,
Cost,JVps} EG.Spec.Main.CorJVpsEG` succeeds; `scripts/check.sh EGTest/Spec_s7b.lean`: rc 0,
0 errors, 0 sorry warnings; `python3 -I scripts/lint.py`: 0 findings.

1. **Pay (e) is definitional** (minor): confirmed, `R.paidEdges ξ = … ∪ R.loopPaid ξ` is `rfl`.
   **Fixed**: the module docstring of `EG/Spec/Quot/Pay.lean` now says "(`rfl` in the locked Defs;
   checked)" (comment only), and `EGTest/Spec_s7b.lean` proves the conjunct by `rfl`. The real
   accounting ("every J-item is paid or lifted") is lemLift/MIX-C, as hazard 8 says.
2. **EGTest docstring overclaimed `C_0 ≥ D_*/2`, `θ_Q ≥ 0`** (minor): confirmed (only `θ_Q < 1/2`
   was checked). **Fixed**: the docstring is corrected, and the test now proves, under
   `GammaCond N0 D`, `0 ≤ thetaQ D` and `D / 2 ≤ C0 D` (every summand of `ε_1`, `ε_2` is
   non-negative for `D ≥ 4`, which follows from Γ2(a); helper `epsX_nonneg` in the test file,
   using `EG.Chain.{epsA_nonneg, epsCONC_nonneg}`, `EG.Light.epsU_nonneg`). So Theorem HI″ applies
   with `C = C_0`, `ϑ = θ_Q`.
3. **"For every past" provable only via `RoundInput.ofPast_valid`** (minor): confirmed as a
   dependency, not a defect: `ofPast_valid` is not yet a theorem (grep: mentioned only in comments
   of `EG/Spec/Quot/{Cand,Lift}.lean`); TRIAGE §3 item 31 joint s6/s7 obligation. **Not a Spec
   issue**; scheduling note for the orchestrator: prove `ofPast_valid` before the s7b proofs of
   Pay, PayGlobal, UHsplit (ii)/(iii)/Theta, OneOutcomeRound.
4. **Different parenthesization of `E X_V ≤ 2.1(6 log₂D_*+12)n/D_*` in Vstar and EXprime** (minor):
   confirmed; equal by `ring`. **Not an issue** (reviewer: no action required); I did not touch the
   EXprime statement, to avoid re-review of an unchanged meaning. The EXprime proof closes that
   conjunct by `Vstar` plus `ring_nf`/`le_of_eq`.
5. **OneOutcome existence conjuncts are hypothesis-free Markov facts** (minor): confirmed; this is
   the TeX ("needs nothing beyond Markov"). **Not an issue** (no duplicated statement: the sharper
   `1/2 ≤ P` is the s7a Spec `EG/Spec/Quot/RoundStep.lean`).
6. **Non-vacuity of `∀ J, JPlusProps …` exhibited only at `J = ∅`** (minor): confirmed as a
   limitation of the evidence; the Specs do not assume `I.Valid`, so nothing is hidden.
   **Not a Spec issue**; the missing witness is again `RoundInput.ofPast_valid` (item 3).
