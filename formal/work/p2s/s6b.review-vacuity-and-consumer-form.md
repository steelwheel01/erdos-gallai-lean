# Clean-room review of the s6b Specs (lens: vacuity-and-consumer-form, model B)

Reviewer: clean-room statement reviewer (no Lean file of the repo edited). Date 2026-09-30.
Scope: `work/p2s/s6b.md` and the new Spec files it lists, `EG/Spec/Chain/Lost.lean`
(`LostStatement`), `EG/Spec/Chain/MixC.lean` (`MixCStatement`, `MixCConcStatement`,
`MixCTPVApplicableStatement`), `EG/Spec/Chain/JPlusV.lean` (`JplusVStatement`), and the test file
`EGTest/Spec_s6b.lean`. TeX: `proofs/manuscript/s6.tex` 390–442 (defLending, lemLost), 620–680
(lemJplus, defJconsumer), 680–867 (consOrder, lemLent, thmMIXC), `s3.tex` 1041–1500 (defCOL, lemCOL).
Locked Defs read: `EG/Defs/Chain/{Lending,StageInst,JSet,JConsumer,Design,Constants}.lean`,
`EG/Defs/Probe/S7b/Outcome.lean` (`stageOf`, `XUOf`), `EG/Defs/Probe/S4/TPV.lean` (`TPVHyp`),
`EG/Defs/Gamma/Full.lean` (`RunHyp`), `EG/Defs/Stage1/{Law,COL}.lean` (`law`, `KJS`, `rhoJS`),
`EG/Defs/Light/{Stages,Constants}.lean`, `EG/Defs/HB/Run.lean`, `EG/Defs/Prob/FinDist.lean`,
`EG/Defs/Vortex.lean`, `EG/Defs/Expander.lean`, `EG/Defs/Graph.lean` (`ofEdges`). Consumers and
providers read: `EG/Spec/Quot/{Cost,EXprime,OneOutcome,Cand}.lean`, `EG/Spec/Chain/{CONCL,JSLC}.lean`,
`EG/Spec/Light/{Expect,KRED}.lean`, `EG/Spec/Vortex/TPV.lean`, and the Lib files
`EG/Lib/Chain/{Lending,JConsumer,JSet}.lean`, `EG/Lib/Stage1/Law.lean`, `EG/Lib/Prob/Basic.lean`.
I also read the model-A review `s6b.review-fidelity-first.md` (after forming my own reading) to avoid
repeating its findings; where we overlap I say so.

## Verdict: APPROVE (no statement change required; minor and cosmetic notes only)

* No new Spec has contradictory hypotheses. Every universally quantified object of the new Specs is
  shown nonempty or satisfiable, with one shared exception (`RunHyp`, as in every s5–s7 Spec): the
  designation quantifier (V3, new here: every run admits a designation), the stage-1 support
  (`supp_nonempty`), J-consumers (`nonempty_jConsumer`), the `b`-hypothesis of MIX-C (`b := |Obj|`).
* No conclusion is trivially true. The only conjuncts that are pure bookkeeping are the ones the TeX
  itself states as such: `K^JS_l ρ_l = M_l^{-2}` inside the middle link of Lost (i) (V6), the second
  link of Lost (iii) given s2:lemTower(b) (V10), and `MixCConcStatement` (= 1.5 × `ConcLSumStatement`,
  as the TeX says "by Theorem s6:thmCONCL(iv)"; derived in `EGTest/Spec_s6b.lean`).
* Consumer form: the s7b consumers read the new Specs verbatim. `EXprimeStatement`'s `E X_U` clause is
  the composition of the two links of Lost (iii) (V8, `le_trans`); the first link of Lost (iii) is
  linearity of expectation from `LemExpectStatement` and (K6) on the same law with the same `dem`/`lp`
  (V9, proved in the scratch file); `CostStatement`'s `∃ Js, (∀ l ∈ Icc 3 R, JPlusProps run G δ
  (stageOf ω) l (Js l)) ∧ ∃ D, IsDecomp …` is syntactically the conclusion shape of `MixCStatement`
  (V12), and MIX-C's `Light.dem ω`, `Light.lp ω` are `(stageOf ω).dem`, `.lp` by `rfl` (V1), the form
  of `LemKREDStatement`.
* No hidden hypothesis: the only parameter bundle is `RunHyp` (Γ1, Γ3, N0Cond, `n ≥ N_0`, `d_1 ≥ D_*`,
  valid run). No Γ2(b),(c), no Γ4, no `Gamma2a` outside `RunHyp`'s Γ1 (grep over the three files).
* Hygiene: `python3 -I scripts/lint.py` → `lint (development): 0 findings`. Oleans of the three modules
  exist (2026-09-30 02:18–02:19). Scratch file compiled with `lake env lean` (rc 0, one unused-variable
  warning of my own): `s6b_vacuity.lean` in the session scratchpad (outside the repo).

## Scratch checks (compiled, rc 0)

| # | Check | Result | Meaning |
|---|---|---|---|
| V1 | `(stageOf ω).dem = Light.dem ω`, `(stageOf ω).lp = Light.lp ω` | `rfl` | MIX-C (c) and Lost (iii) read the same `dem`, `lp` as K-RED / lemExpect; no bridge lemma is needed. |
| V2 | `XUOf run G δ ω = 80·dem + 369·lp + Σ_{l∈[1,R]} (169+M_l)·|Lost_l(stageOf ω)|` | `simp` | Lost (iii) is stated on the literal `X_U` of s6:defLending at the record `stageOf ω`. |
| V3 | `∃ δ, IsDesignation run G δ` for every `run`, `G` (no hypothesis) | proved (`anc_l(u) ≠ ∅` for a classed port, by definition of `classed`) | the quantifier "for every designation" of all five Specs is never empty. |
| V4 | `ret run G δ S l a ⊆ run.Z0 G l a` for every record, `l`, `a` | proved | the last conjunct of `TPVHyp` in `MixCTPVApplicableStatement` is run-generic bookkeeping; the content of that Spec is `TPVSize`, the expander property and `2^{150}L^{42} ≤ s`. |
| V5 | `(OZ run G S l a).verts = run.Z0 G l a` for every record | `split_ifs <;> rfl` | the "spanning" conjunct `O.verts = Z` of `TPVHyp` holds by construction in both branches of `O_Z`. |
| V6 | `(KJS : ℝ) · rhoJS = M^{-2}` with no hypothesis (both sides `0` at `M = 0`) | proved | the middle link of Lost (i) carries only `P(Y lend-bad) ≤ 2|V(Y)|^{-2}` as content, as the TeX proof says. |
| V7 | `(0:ℕ)^{-2} = 0`; `M^{-2} + 2·0^{-2} ≤ 2M^{-2}` for `M ≥ 0` | proved | the third link of Lost (i) does not hide a false edge case at `|V(Y)| = 0` (excluded anyway by `IsDesignation.mem_ancVerts`). |
| V8 | `LostStatement → EXprime`'s second conjunct (`E X_U ≤ ε_U n + 5.5n/D_*`) | `le_trans` | consumer form: EXprime's `E X_U` clause is the composed chain of Lost (iii); a proof of EXprime should call Lost, not restate it. |
| V9 | `LemExpectStatement ∧ (K6) → ` first link of Lost (iii) | proved (`expect_add`, `expect_sum`, `expect_const_mul`) | the first link is exactly linearity of expectation over the shared law; the three Specs use one vocabulary. |
| V10 | `Σ_{l∈[1,R]} 2n(169+M_l)/M_l² ≤ 5.5n/D` from `Σ 1/M_l ≤ 2/D`, `M_l ≥ 2^40`, `n ≥ 0`, `D > 0` | proved | the second link of Lost (iii) is pure arithmetic given s2:lemTower(b); its content is the tower fact, not probability. |
| V11 | with `b l J := |(C.out l J).1|`, `Σ_{l∈[3,R]} b l (Js l)` is the literal `Σ_l |Obj_l|` at the exhibited `J_l` | `rfl` | Option B′ contains the TeX's consumer term as the special case `b = |Obj|`. |
| V12 | `JPlusProps run G δ (stageOf ω) l J` in MIX-C is the same term as in `CostStatement` | `Iff.rfl` | the s7b consumer reads MIX-C's `Js` with no transport. |

`EGTest/Spec_s6b.lean` (re-read, reported rc 0 by the unit) adds: `JplusVStatement` proved from
`iIndepFun_of_dependsOn`; `MixCConcStatement` from `ConcLSumStatement`; `supp.Nonempty`;
`nonempty_jConsumer`; the `b`-hypothesis at `b := |Obj|`; `Js := ∅` satisfies the `JPlusProps` conjunct;
`Lost_l = ∅` for `l ≤ 2`.

## Per-Spec: vacuity and consumer form

| Spec | Hypotheses satisfiable? | Conclusion trivial? | Consumer (form matches?) |
|---|---|---|---|
| `LostStatement` | `RunHyp` (shared, unexhibited: needs s2:propExists + a Γ-satisfying `D_*`, as for s5), `IsDesignation` (V3) | no. (i): three links; link 2 = `P(lend-bad) ≤ 2|V(Y)|^{-2}` plus the identity V6; link 3 needs `|V(Y)|² ≥ 2M_l²` (propStructure(iv) + lemTower(b)). (K6): content at `3 ≤ l ≤ R`, `0 ≤ 2n/M_l²` elsewhere (as the TeX's "for every round"). (iii): link 1 = lemExpect + (K6) (V9); link 2 = lemTower(b) arithmetic (V10). | `EXprimeStatement` second conjunct (V8). Note the (i) events use `stageOf ω`, the record `Cost`/`Pay`/`EXprime` read. |
| `MixCStatement` | `RunHyp`, δ (V3), `ω ∈ supp` (nonempty), `C : JConsumer` (`nonempty_jConsumer`), `b` bounding `C` on J⁺ sets at `3 ≤ l ≤ R` (satisfiable by `b := |Obj|`, or by any larger function) | no: `∃ Js` is satisfiable in its first conjunct (`Js := ∅`), and then the second conjunct demands a decomposition of `E(G)` into at most `(D_*/2 + 1083 + ε_M)n + [80dem+369lp+169Σ|Lost_l|] + 1.5Σm + Σ b(l, ∅)` objects, which is the whole content (the single-edge decomposition has `n d_1/2` objects). See N1 on the freedom in `Js`. | `CostStatement` (V12); `b` is instantiated there by s7's per-round bounds, which are uniform over J⁺ sets (blueprint MIXC-SUMOBJ, checked by the s7 blueprint). |
| `MixCConcStatement` | `RunHyp`, δ | true given `ConcLSumStatement` (derived in EGTest; the TeX says "by Theorem s6:thmCONCL(iv)") | `CostStatement`'s `1.5 ε_CONC` inside `eps1`. Redundant with `ConcLSumStatement` (N2). |
| `MixCTPVApplicableStatement` | `RunHyp`, δ, `ω ∈ supp`, `a ∈ Std_l` (nonempty for `1 ≤ l ≤ R` on a valid run; `∅` elsewhere so the `∀ l : ℕ` is harmless) | no: `TPVSize |Z^0|` (`L ≥ 2^{10}` etc.) needs `|Z^0| ≥ P_l ≥ N_0` (Γ3), the expander conjunct needs COL(a) on the support (lend-good) or propStructure(i) (lend-bad), `2^{150}L^{42} ≤ s_l/4` needs COL(e) under Γ1. The two run-generic conjuncts are V4, V5. Exactly one of the two implications is live for each `Z`. | none in the Spec layer: `EG/Spec/Quot/OneOutcome.lean` says "(2) + step (ii): no Lean statement" (TRIAGE §2.8's "used by s7:lemOneOutcome" is superseded). It is consumed inside the MIX-C proof only (N3). Its `TPVHyp` is exactly the hypothesis of `TPVStatement` (`EG/Spec/Vortex/TPV.lean`), so the proof applies TPV with no transport. |
| `JplusVStatement` | none (every run) | true but not vacuous: proved in EGTest as a structural fact of the product law, as the TeX ("holds because every colouring … is uniform and independent over edges") | none in this exact form: `EG/Spec/Quot/Cand.lean` (s7:lemCand (i)) states `iIndepFun` of a family mixing pool labels (1d) and JV-class membership (1a), which JplusV alone does not give; its proof will use `EG.Stage1.iIndepFun_of_dependsOn` directly, as the EGTest proof of JplusV does (N4). |

## Fidelity, briefly, from this lens (back-translations agree with the model-A review)

* **Lost.** "Fix a valid run and a designation" → `RunHyp`, `IsDesignation`; "over the stage-1
  outcome" → `Stage1.law G run`, events and expectations at `stageOf ω`. (i) "classed port `u` of
  round `l ≥ 3`" → `3 ≤ l`, `a ∈ Std_l`, `u ∈ Q_Z`; `Y(u) = δ l u`; the three links are stated
  literally (`≤`, non-strict, as in the TeX). (K6) "every round `l`" → `∀ l : ℕ`. (iii) `Σ_l` over
  `[1, R]`, the range of the locked `X_U` (LEND-XU-RANGE); `5.5 n/D_*` as `5.5 * n / Dstar`; `ε_U` the
  locked `Light.epsU`; `n = G.card`. Integer powers `^(-2:ℤ)` on reals; `M_l`, `K^JS_l` are `ℕ` cast.
* **MIX-C.** (b) "decomposition of `E(G)`" → `IsDecomp (G.edges : Set _) D` (loopless set, per
  CONVENTIONS). (c) constants `745`, `338`, `ε_M = epsM` (locked `ε_K + 169 ε_A + 252/D_*`), the
  bracket `80 dem + 369 lp + 169 Σ_{l∈[1,R]} |Lost_l|`, `1.5 Σ_{l∈[1,R]} Σ_{Y∈anc} m_{Y,l}` (the
  `ConcLSumStatement` convention; `m = 0` off `r(Y)+2 ≤ l`), consumer term `Σ_{l∈[3,R]} b l (Js l)`.
  "*any* stage-1 outcome" → `ω ∈ supp` (T0-mixc-supp; off-support records can violate `Coherent`).
  "*any* J-consumer" → the locked `JConsumer` (a function of `(l, J)` in context; the TeX allows a
  dependence on "everything constructed at rounds `> l`" — model-A's M3, not repeated here).
* **TPV bullet.** "`|Z^0| ≥ P_l ≥ N_0`" is stated as `TPVSize |Z^0|`, the consumer form of
  `TPVStatement` (weaker than `|Z^0| ≥ N_0` in general, implied by it under `N0Cond`; N5). Parameters
  `(2^{-5}, s_l/4)` lend-good and `(2^{-5}, s_l)` lend-bad, literal. `2^{150} L^{42} ≤ s` with
  `L = log₂|Z^0| = L_Z` (standalone: `V(Z) = Z^0`). "`E = Erem(Z) ⊇ E(O_Z)`" omitted (internal;
  s6:lemLent (iii)).
* **J⁺ (v).** Mutual independence over all pairs `(Y, e)`, stronger than per ancestor; no hypothesis.
  On a valid run the pairs are the edges of `⊔_Y E(H_Y)` (propStructure(iii)); off it a shared edge is
  two coordinates, which is the law's truth, not a fidelity issue.

## Notes and minor issues

| ID | Severity | Where | Issue | Suggested fix |
|---|---|---|---|---|
| N1 | minor (T0, already recorded by model A as M1) | `MixCStatement`, docstring "so the two forms are equivalent"; `s6b.md` T0-mixc-Bprime | The `Js` are existential and constrained only by `JPlusProps`; the TeX implies the Lean form (take the chain's `J_l`) but not conversely. From the consumer side this is safe only because every s7 bound fed into `b` is uniform over J⁺ sets (which is how `CostStatement` is written). | Change "equivalent" to "implied by the TeX (take the chain's `J_l`); the consumer's bounds must be uniform over `JPlusProps` sets". No statement change. |
| N2 | cosmetic | `MixCConcStatement` | Restates `ConcLSumStatement` × 1.5 under the stronger `RunHyp`. Harmless (the TeX has the sentence), but a proof module must derive it (as EGTest does) and never stub it as a declared input next to `ConcLSumStatement`. | Note in the proof plan. |
| N3 | cosmetic (bookkeeping) | `MixCTPVApplicableStatement` | Has no consumer in the Spec layer (s7b's `OneOutcome` gives stage 3 "no Lean statement"). It is a proof step of MIX-C stated as a Spec for fidelity of bullet "Lemma TPV at step (1)". Fine; but `s6b.md`/TRIAGE §2.8 still say it is "used by s7:lemOneOutcome". | Update the sentence in `s6b.md` (and TRIAGE §2.8 when next edited): "consumed by the MIX-C proof". |
| N4 | cosmetic (bookkeeping) | `JplusVStatement` | No consumer reads it in this form (`Cand.lean` needs a mixed (1a)/(1d) family). It is a true fidelity Spec, already proved in EGTest. | Move that proof into a proof module (`EG/Proof/Chain/JPlusV.lean`) when P3 starts, so the Spec is never a stub. |
| N5 | minor (T0, consumer form) | `MixCTPVApplicableStatement`, "`|Z^0| ≥ P_l ≥ N_0`" | Stated as `TPVSize |Z^0|` (what `TPVStatement` consumes) rather than `N0 ≤ |Z^0|`. `N0Cond N0 ∧ N0 ≤ N → TPVSize N`, so the TeX implies the Lean form; the Lean form does not give `|Z^0| ≥ N_0` back. No consumer needs the literal inequality. | Record in the T0 table of `s6b.md` (T0-mixc-tpv mentions the concrete parameters but not this weakening). |
| N6 | cosmetic | `Lost.lean` module docstring, (K6) bullet | "true as `M_l ≥ 2^{40}`" for `l ∉ [3, R]`: the reason is `Lost_l = ∅` and `0 ≤ 2n/M_l²` for every real (with `x/0 = 0`), not the size of `M_l` off-range (model A's M2). | Reword. |

## Math findings

No manuscript defect found from this lens. Re-derived and/or machine-checked:
* the identity `K^JS_l ρ_l = M_l^{-2}` (V6) and the arithmetic of Lost (iii) link 2 (V10: constant
  `(2 + 338/2^40)·2 ≈ 4.0000000006 ≤ 5.5`, given `Σ_{l≤R} 1/M_l ≤ 2/D_*`, s2:lemTower(b));
* the linearity step of Lost (iii) link 1 (V9), which needs only `LemExpectStatement` and (K6) on the
  shared law;
* the run-generic conjuncts of the TPV bullet (V4, V5);
* the existence of a designation for every run (V3), so s6:defDesign's object is never empty.

Two T0 encodings are recorded in the structured output: the B′ weakening of MIX-C (c) (N1, same as
model A's) and the `TPVSize` form of "`|Z^0| ≥ N_0`" in the TPV bullet (N5).
