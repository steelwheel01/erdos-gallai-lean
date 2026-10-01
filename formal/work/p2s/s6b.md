# P2 Specs, chunk s6b (CONC-L, lending, Lost, JS-LC, J⁺, J-consumer, order, Lent, MIX-C): status

Manuscript v6.1 `proofs/manuscript/s6.tex` lines 335–867 (CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s6b.md`, `nodes_s6b.json`; data model TRIAGE §2 (2.6 RunHyp, 2.7
stage-1 law, 2.8 stage 3, 2.9 s6 interfaces / MIX-C Option B′, 2.12 T0 record); Defs design note
`work/p2d/design.md`.

Result: 3 new Spec modules (5 `…Statement` defs), 1 test file. No new Defs file. All compile
(`lake build EG.Spec.Chain.Lost EG.Spec.Chain.MixC EG.Spec.Chain.JPlusV`;
`scripts/check.sh EGTest/Spec_s6b.lean`: 0 errors, 0 warnings, 0 sorry).
`python3 -I scripts/lint.py`: 0 findings. No proofs of Specs, no stubs. No existing file edited.

For the orchestrator, the root imports to add: to `EG`, `EG.Spec.Chain.Lost`, `EG.Spec.Chain.MixC`,
`EG.Spec.Chain.JPlusV`; to `EGTest`, `EGTest.Spec_s6b`. I did not edit the root files.

## Files

| File | Contents |
|---|---|
| `EG/Spec/Chain/Lost.lean` | `LostStatement` ((i), (K6), (iii)) |
| `EG/Spec/Chain/MixC.lean` | `MixCStatement` ((b)+(c), Option B′), `MixCConcStatement` ((c), last sentence), `MixCTPVApplicableStatement` ((a), TPV bullet) |
| `EG/Spec/Chain/JPlusV.lean` | `JplusVStatement` (s6:lemJplus (v)) |
| `EGTest/Spec_s6b.lean` | non-vacuity checks; proves `JplusVStatement`; derives `MixCConcStatement` from `ConcLSumStatement` |

## Table: label → Lean name → file → status

All Lean names are in namespace `EG.Spec` unless stated otherwise.

| label (kind) | Lean name | file | status |
|---|---|---|---|
| s6:thmCONCL (theorem) | `ConcLIStatement`, `ConcLIIStatement`, `ConcLIIIStatement`, `ConcLAlphaStatement`, `ConcLSumStatement`, `EpsCONCTendstoStatement` (+ proof-level `ConcLPerAncestorStatement`, `ConcLGCSumStatement`) | `EG/Spec/Chain/CONCL.lean` | existing (probe P3B); checked, no problem found |
| s6:defLending (definition) | Defs `EG.Chain.{lendBad, lost, ret, qs, OZ, lostRound, XU, …}`; embedded claims ("`Z^0 = Ret_Z ⊔ Q*_Z`", "`A_Z, F_Z, Lost_Z` pairwise disjoint", "for `u ∈ Q*_Z`, `Y(u)` lend-good and `u ∉ ⋃_j T_j`") are proved Lib lemmas `ret_union_qs`, `disjoint_ret_qs`, `disjoint_hubs_fresh`, `disjoint_hubs_lost`, `disjoint_fresh_lost`, `not_lendBad_of_mem_qs`, `notMem_Tj_of_mem_qs` | `EG/Defs/Chain/Lending.lean`, `EG/Lib/Chain/Lending.lean` | existing Defs (locked) + proved Lib; no Spec needed |
| s6:lemLost (lemma) | `LostStatement` | `EG/Spec/Chain/Lost.lean` | **new** |
| s6:lemJSLC (lemma) | `JSLCStatement` (with `JPlusProps`); proof steps `JslcTypesStatement`, `JslcStep2Statement`, `JslcStep7DisjStatement`, `JslcRouting*` | `EG/Spec/Chain/JSLC.lean`, `JSLCSteps.lean`, `JSLCRouting.lean` | existing (probe P2J); checked, no problem found |
| s6:remStar (remark) | none | — | no content; the JS-LC Spec has no star-split option (noted in `JSLC.lean`) |
| s6:lemJplus (lemma) | (i) exhaustive, (J1), (J2), (ii): `EG.Chain.JPlusProps` inside `JSLCStatement`; (J3), (i) exclusive, (iii), (iv): `JplusFactsStatement`; **(v): `JplusVStatement`** | `EG/Defs/Chain/JSet.lean`, `EG/Spec/Chain/JSLC.lean`, `EG/Spec/Chain/JPlus.lean`, **`EG/Spec/Chain/JPlusV.lean`** | existing (P2J) + **new** for (v) |
| s6:defJconsumer (definition) | Defs `EG.Chain.JConsumer`; "the trivial rule is a J-consumer" is `EG.Chain.trivialConsumer` (Lib, proved) | `EG/Defs/Chain/JConsumer.lean`, `EG/Lib/Chain/JConsumer.lean` | existing Defs (locked); no Spec |
| s6:consOrder (construction) | none | — | proof-internal (TRIAGE §2.9: "The chain (consOrder) and the Lent sets stay proof-internal") |
| s6:lemLent (lemma) | none | — | proof-internal (TRIAGE §2.9, blueprint Option B); its parts are proof obligations of MIX-C. No Spec is possible without exposing the chain as a Def (Option A, rejected by TRIAGE) |
| s6:thmMIXC (theorem) | `MixCStatement`, `MixCConcStatement`, `MixCTPVApplicableStatement` | `EG/Spec/Chain/MixC.lean` | **new** |

## Common reading (new Specs)

- **Setting.** `EG.RunHyp N0 Dstar G run` (TRIAGE §2.6: "s5, s6b (Lost, JS-LC, MIX-C) and s7 take
  `RunHyp`": Γ1, Γ3, `N0Cond`, `N0 ≤ n`, `D_* ≤ d_1`, valid run). No Γ4, no Γ2(b),(c). A designation
  `δ` with `IsDesignation run G δ`, quantified before the law. `V : Type u`, `[DecidableEq V]`.
- **Stage 1.** Law `EG.Stage1.law G run`; "a stage-1 outcome" is `ω ∈ (Stage1.law G run).supp`; its
  stage-2 data are `EG.Quot.stageOf ω = StageData.ofOutcome ω (Light.demoted ω) (Light.dem ω)
  (Light.lp ω)` (D-DES-1, TRIAGE §3 item 20; the record the s7b Specs read).
- **Notation.** `M_l = run.M G l` (ℕ), `s_l = run.s G l` (ℕ), `K^JS_l = Stage1.KJS G run l`,
  `ρ_l = Stage1.rhoJS G run l = M_l^{-4}`, `|V(Y)| = (run.ancVerts G Y).card`, `n = G.card`,
  `m_{Y,l} = EG.Chain.mY`, `Lost_Z = EG.Chain.lost`, `Lost_l = EG.Chain.lostRound`,
  `X_U(ω) = EG.Quot.XUOf run G δ ω`, `ε_U = Light.epsU`, `ε_M = EG.Chain.epsM`,
  `ε_CONC = EG.Chain.epsCONC`.

## New Specs: TeX statement and back-translation

### s6:lemLost — `LostStatement`
TeX: "Fix a valid run and a designation `δ`. Probabilities and expectations are over the stage-1
outcome. (i) for every classed port `u` of round `l ≥ 3`,
`P(u ∈ Lost) ≤ K^JS_l ρ_l + P(Y(u) lend-bad) ≤ M_l^{-2} + 2|V(Y(u))|^{-2} ≤ 2M_l^{-2}`;
(K6) `E|Lost_l| ≤ 2n/M_l^2` for every round `l`;
(iii) `E X_U ≤ ε_U(D_*) n + Σ_l 2n(169+M_l)/M_l^2 ≤ ε_U(D_*) n + 5.5 n/D_*`."

Lean, in plain mathematics: under RunHyp and for every designation `δ`:
- (i) for every `l ≥ 3`, every standalone pre-part `Z ∈ Std_l` and every `u ∈ Q_Z`, with `Y := δ(l,u)`:
  - `P(u ∈ Lost_Z) ≤ K^JS_l ρ_l + P(Y lend-bad)`;
  - `K^JS_l ρ_l + P(Y lend-bad) ≤ M_l^{-2} + 2|V(Y)|^{-2}`;
  - `M_l^{-2} + 2|V(Y)|^{-2} ≤ 2M_l^{-2}`;
  (probabilities under the stage-1 law; `Lost_Z` and lend-badness are those of `stageOf ω`).
- (K6) for every natural `l`: `E|Lost_l| ≤ 2n/M_l^2`.
- (iii) `E X_U ≤ ε_U(D_*) n + Σ_{l=1}^{R} 2n(169+M_l)/M_l^2`, and
  `ε_U(D_*) n + Σ_{l=1}^{R} 2n(169+M_l)/M_l^2 ≤ ε_U(D_*) n + 5.5 n/D_*`.

### s6:thmMIXC — `MixCStatement`
TeX: "Fix the following data: a valid `HB*^{τ+}` run on `G` with `n ≥ N_0` and `d_1 ≥ D_*`, and a
designation `δ`; *any* stage-1 outcome; stage-3 outcomes in the good events of Lemma s4:lemTPV …,
of Lemma s4:lemPV through Lemma s5:lemChild …, and of Theorem s4:thmVXp through Lemma
s5:lemDemoted …; *any* J-consumer. Run Construction s6:consOrder. Then: … (b) (Coverage.) The output
is a decomposition of `E(G)` … (c) (Cost.) The number of output objects is at most
`(D_*/2 + c_KRED + c_Fresh) n + ε_M(D_*) n + [80 dem + 369 lp + 169 Σ_l |Lost_l|]
+ 1.5 Σ_{(Y,l)} m_{Y,l} + Σ_l |Obj_l|`, where `ε_M(D_*) := ε_K(D_*) + 169 ε_A + 252/D_*` …"
(`c_KRED = 745`, `c_Fresh = 338`, preamble macros.)

Lean, in plain mathematics: under RunHyp, for every designation `δ`, every stage-1 outcome `ω` of
positive weight, every J-consumer `C` (for the stage data of `ω`) and every function
`b : ℕ × (edge sets) → ℝ` such that `|Obj(C, l, J)| ≤ b(l, J)` for all `3 ≤ l ≤ R` and all `J` with
the J⁺ properties at round `l`: there are edge sets `J_l` (`l ∈ [3, R]`), each with the J⁺
properties at round `l`, and a decomposition `D` of `E(G)` (into cycles and single edges) with
`|D| ≤ (D_*/2 + 745 + 338) n + ε_M(D_*) n + (80 dem(ω) + 369 lp(ω) + 169 Σ_{l=1}^{R} |Lost_l|)
+ 1.5 Σ_{l=1}^{R} Σ_{Y ancestor} m_{Y,l} + Σ_{l=3}^{R} b(l, J_l)`.

### s6:thmMIXC (c), last sentence — `MixCConcStatement`
TeX: "Moreover `1.5 Σ_{(Y,l)} m_{Y,l} ≤ 1.5 ε_CONC(D_*) n` by Theorem s6:thmCONCL(iv)."
Lean: under RunHyp, for every designation, `1.5 Σ_{l=1}^{R} Σ_{Y ancestor} m_{Y,l} ≤ 1.5 ε_CONC(D_*) n`.
(`EGTest/Spec_s6b.lean` derives it from `ConcLSumStatement`.)

### s6:thmMIXC (a), bullet "Lemma TPV at step (1)" — `MixCTPVApplicableStatement`
TeX: "`|Z^0| ≥ P_l ≥ N_0` by (s1:condG3). If `Z` is lend-good, then `O_Z = Own_Z`. By Lemma
s3:lemCOL(a) it is a spanning `(2^{-5}, s_l/4)`-expander on `Z^0`, and by Lemma s3:lemCOL(e) we have
`s_l/4 ≥ 2^{150}L_Z^{42}`. If `Z` is lend-bad, `O_Z = X^0_Z` is a spanning `(2^{-5}, s_l)`-expander on
`Z^0` (Proposition s2:propStructure(i)), and `s_l ≥ s_l/4 ≥ 2^{150}L_Z^{42}` … `E = Erem(Z) ⊇ E(O_Z)`
(Lemma s6:lemLent(iii)), and all its edges lie inside `Z^0`."
Lean: under RunHyp, for every designation, every `ω` of positive weight, every `l` and every
`Z ∈ Std_l`: if `Z` is lend-good, the data `(Z^0, O_Z, Ret_Z)` satisfy the hypotheses of Lemma TPV
(`TPVHyp`: `TPVSize |Z^0|`, `V(O_Z) = Z^0`, `O_Z` a `(2^{-5}, s_l/4)`-expander,
`2^{-7} ≤ 2^{-5} ≤ 2^{-5}`, `2^{150}(log₂|Z^0|)^{42} ≤ s_l/4`, `Ret_Z ⊆ Z^0`); if `Z` is lend-bad, the
same with `s = s_l`.

### s6:lemJplus (v) — `JplusVStatement`
TeX: "(v) In the colourings of Definition s3:defCOL, colours of distinct edges are independent."
Lean: for every run, under the stage-1 law the edge labels `ω.col Y e`, indexed by all pairs
(ancestor `Y`, edge `e` of `H_Y`), are mutually independent. Proved in `EGTest/Spec_s6b.lean` from
`EG.Stage1.iIndepFun_of_dependsOn` (so the Spec is true; a proof module can reuse that proof).

## Hazards and choices (T0 decisions)

| ID | Where | Decision |
|---|---|---|
| T0-lost-hyps | Lost | "Fix a valid run" is read as `RunHyp` (blueprint LOST-HYPS; the proof needs Γ1, `n ≥ N_0`, `d_1 ≥ D_*`). |
| T0-lost-chain | Lost (i), (iii) | The displayed chains are stated literally, link by link (3 resp. 2 inequalities). The proof-internal "`P(Y lend-bad) ≤ 2|V(Y)|^{-2}`" and "`K^JS_l ρ_l = M_l^{-2}`" are not separate conjuncts. |
| T0-lost-rounds | Lost (i), (K6), (iii) | (i): "classed port of round `l`" is `u ∈ Q_Z`, `Z ∈ Std_l` (so `l ≤ R` automatically). (K6) holds for all `l : ℕ` (trivial outside `[3, R]`). `Σ_l` in (iii) is over `[1, R]`, the range of `X_U` in the locked Def. |
| T0-lost-consumer | Lost (iii) | `E X_U` is written with `XUOf`, the consumer form of s7:lemEXprime. `EXprimeStatement` repeats this bound. |
| T0-mixc-Bprime | MIX-C (c) | Option B′ (TRIAGE §2.9, binding): the consumer term is `Σ_{l=3}^{R} b(l, J_l)` for an arbitrary bound `b` on the consumer over `JPlusProps` sets, and the chain's `J_l` are exposed existentially with `JPlusProps`. The TeX theorem implies the Lean form (take the chain's `J_l`). The converse fails, so the Lean form is strictly weaker: the `Js` are existential and constrained only by `JPlusProps` (`∅` qualifies, `jPlusProps_empty`), so they need not be the chain's sets and a prover may pick them to make `Σ b(l, Js l)` large, even with `b := |C.out|`. Design obligation: every downstream bound on `Σ_l b(l, J_l)` (and on anything read at the returned `Js`) must hold uniformly over all `JPlusProps` sets. s7:propCost (`CostStatement`) has the same existential shape, so the chain of Specs stays consistent. |
| T0-mixc-internal | MIX-C (a), (b) | Two kinds of content are proof obligations, not conjuncts. (a) and the itemized (b) concern construction-internal objects (`Lent`, `Erem`, `H_0`, `E^V`, `E^Q`, `J_l`), except the TPV bullet, which is `MixCTPVApplicableStatement`. The itemization of (c) is also internal. Blueprint MIXC-DETAILS-INTERNAL; no consumer reads any of these. |
| T0-mixc-supp | MIX-C, TPV bullet | "*any* stage-1 outcome" is `ω ∈ supp` (TRIAGE §2.7, OO-SUPP). This is weaker than a literal "every outcome". It is justified because records off the support can violate `StageData.Coherent`, and it matches `CostStatement`. |
| T0-mixc-stage3 | MIX-C | Stage-3 outcomes are not data. TPV, PV/lemChild and VX⁺/lemDemoted are deterministic existence Specs (TRIAGE §2.8), used inside the proof; K-RED is "for any admissible family". |
| T0-mixc-consumer | MIX-C | "*any* J-consumer" ranges over `EG.Chain.JConsumer`: functions of `(l, J)` in the context `(run, δ, stageOf ω)`, with obligations only on `JPlusProps` inputs (JCONS-TYPE, JCONS-CONDITIONAL). This is the locked Def. It is a subclass of the TeX's rules, which may also depend on everything constructed at rounds `> l` and on fresh randomness. So the Spec, quantified over all consumers, is weaker than the TeX. This is harmless: the only consumer used, s7's `EG.Quot.roundOut`, is a function of `(l, J)` given `ω` (through `EG.Quot.pastOf ω l J`). |
| T0-mixc-sums | MIX-C (c) | `Σ_l |Lost_l|` is over `[1, R]`. `Σ_{(Y,l)} m_{Y,l}` is over `l ∈ [1, R]` and all ancestors, the index convention of `ConcLSumStatement` (CONCL-SUM-RANGE). `c_KRED = 745` and `c_Fresh = 338` are numerals; `dem`/`lp` are `Light.dem ω`/`Light.lp ω`, the form of the K-RED Spec. |
| T0-mixc-tpv | TPV bullet | Stated with the concrete parameters `(ε_O, s) = (2^{-5}, s_l/4)` for lend-good and `(2^{-5}, s_l)` for lend-bad, which is stronger than `∃ ε_O s`. "`E = Erem(Z) ⊇ E(O_Z)`, all edges inside `Z^0`" concerns the internal `Erem` and is omitted (it is s6:lemLent(iii)). `Ret_Z ⊆ Z^0` (inside `TPVHyp`) is the partition of s6:defLending. Consumer-form weakening: the bullet's "`|Z^0| ≥ P_l ≥ N_0`" is stated as `TPVSize |Z^0|`, the form `TPVStatement` consumes. `N0Cond N0 → N0 ≤ N → TPVSize N`, so the TeX implies it, but the literal `N_0 ≤ |Z^0|` cannot be recovered from it. No consumer needs the literal inequality. |
| T0-jplusv | J⁺ (v) | This is the joint form over all pairs `(Y, e)`, which is stronger than the per-ancestor Lib lemma `iIndepFun_col_edges`. It takes no hypothesis on the run. |
| lent-internal | s6:lemLent, s6:consOrder | No Spec (TRIAGE §2.9); see the table. |

Checks on the existing Specs I reused (no edits): `JSLCStatement` has the v6.1 bound
`126 n/M_l + 1.5 Σ_{giant} m`, its sum ranges over `run.ancestors`, and it carries `JPlusProps`. The
`CONCL` sums use the same index convention as `MixCStatement`. `JPlus.lean` leaves (v) to the
stage-1 law, which the new `JplusVStatement` now covers. The s7b consumer `CostStatement`
(`EG/Spec/Quot/Cost.lean`) is shaped exactly as B′, with `ω ∈ supp`, `stageOf ω` and
`∃ Js, JPlusProps ∧ ∃ D, IsDecomp`. The s7b `EXprimeStatement` reads `E X_U` through `XUOf`.

No mathematical defect was found. I re-derived the MIX-C cost itemization, the Lost chain and the
TPV bullet against the TeX, and they are consistent. The stated `2|V(Y)|^{-2}` is loose: the proof
gives `|V(Y)|^{-2}` (blueprint LOST-UNION-SLACK). This is harmless.

## Non-vacuity (`EGTest/Spec_s6b.lean`)
- `JplusVStatement` is proved.
- `MixCConcStatement` is derived from `ConcLSumStatement`.
- The following are all shown nonempty or satisfiable: the stage-1 support; J-consumers (`nonempty_jConsumer`); the MIX-C bound hypothesis (via `b := |C.out|`); the `JPlusProps` part of the MIX-C conclusion (`Js := ∅`); `IsDecomp ∅ []`.
- `Lost_l = ∅` for `l ≤ 2`.
- Not checked: satisfiability of `RunHyp` (as in `Spec_s5.lean`).

## Fix round (reviews `s6b.review-fidelity-first.md`, `s6b.review-vacuity-and-consumer-form.md`)

Only docstrings changed: the module docstring of `EG/Spec/Chain/MixC.lean` and the T0 table above.
No statement changed. All five findings are valid, and none is a mathematical defect.

| # | Finding | Verdict | Action |
|---|---|---|---|
| 1 | Option B′ is implied by the TeX but not equivalent to it (the `Js` are existential and may be chosen to make `b` large) | **fixed** | Valid: the `Js` are constrained only by `JPlusProps`. The MixC docstring and T0-mixc-Bprime now say "implied by the TeX (take the chain's `J_l`); strictly weaker". They also state the design obligation that downstream bounds on `Σ b(l, J_l)` be uniform over `JPlusProps` sets. |
| 2 | `JConsumer` is a function of `(l, J)` only, a subclass of the TeX's rules, so the Spec is weaker | **fixed** | Valid. The restriction is now recorded in T0-mixc-consumer and in the MixC docstring bullet "*any* J-consumer". It is harmless because `roundOut` goes through `pastOf ω l J`. The Def is locked and not edited. |
| 3 | "*any* stage-1 outcome" is restricted to `ω ∈ supp` | **not an issue** | Already recorded as T0-mixc-supp. The row now also gives the reason: off-support records can violate `StageData.Coherent`, and `CostStatement` uses the same restriction. |
| 4 | Same as 1 (the second reviewer's wording) | **fixed** | Fixed together with 1. |
| 5 | TPV bullet: `TPVSize |Z^0|` in place of the literal `N_0 ≤ |Z^0|` | **fixed** | Valid. I checked `N0Cond` in `EG/Defs/Gamma/Full.lean`: `∀ N : ℕ, N0 ≤ N → TPVSize N ∧ …`. The consumer-form weakening is now recorded in T0-mixc-tpv and in the MixC docstring (TPV bullet). |

Checks after the fix: `lake build EG.Spec.Chain.MixC` and `scripts/check.sh EGTest/Spec_s6b.lean`
both pass, and `python3 -I scripts/lint.py` reports 0 findings.
