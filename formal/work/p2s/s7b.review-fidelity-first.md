# Clean-room review of the s7b Specs (lens: fidelity-first, model A)

Reviewer: clean-room statement reviewer (no Lean files edited). Date 2026-09-30.
Scope: `work/p2s/s7b.md` and the files it lists:
`EG/Defs/Probe/S7b/Outcome.lean` (new probe Defs), `EG/Spec/Quot/{Vstar,Pay,EXprime,UHsplit,OneOutcome,Cost,JVps}.lean`,
`EG/Spec/Main/CorJVpsEG.lean` (new), and the reused `EG/Spec/Quot/HI.lean`, `EG/Spec/Chain/Lost.lean`,
`EG/Spec/HB/Parentless.lean`. TeX: `proofs/manuscript/s7.tex` lines 881–1560, `s1.tex` (thmMain, condG4),
`s6.tex` (defDesign `c^agg`, defLending `X_U`). Locked Defs read: `EG/Defs/Quot/{Round,Schedule,Xprime,Constants,Cand}.lean`,
`EG/Defs/Gamma/Full.lean` (`RunHyp`, `N0Cond`, `Gamma3`), `EG/Defs/Main/{Gamma,GammaCond}.lean`,
`EG/Defs/Chain/{Lending,Design}.lean`.

## Verdict: APPROVE (no major issue; minor/cosmetic notes below)

Every new Spec back-translates to the TeX statement, or to a stronger form that the TeX proof supports
(universal quantification over every admissible `J_l` and every valid rule). No Γ2(b),(c) hypothesis anywhere.
Lint: `python3 -I scripts/lint.py` → 0 findings. `scripts/check.sh EGTest/Spec_s7b.lean` → rc 0, 0 errors, 0 sorry.

## Scratch checks (outside the repo, `/tmp/s7brev/`)

* `R.paidEdges ξ = I.Jlost ∪ I.paidPool ∪ I.paidJVBad ∪ R.unpairedLegs ∪ R.sdrPaid ξ.1 ∪ R.loopPaid ξ` is `rfl`
  (so lemPay (e) is definitional; see note N1).
* `(pastOf run G δ ω l J).Hcd = Hcd run G l`, `.M = run.M G l`, `.G = G`, `.pool = Stage1.poolL G ω.pool l`,
  `.thult = thult run G l`: all `rfl`. The run-level quantities used in the Specs agree with those the round
  step reads (no silent mismatch between `Hcd run G l` in the Spec and `I.Hcd` in the Defs).
* `JPlusProps run G δ S l ∅` holds (proved in 1 line). So "for every past" (∀ J with `JPlusProps`) is not an empty
  quantifier in `J`. Together with the EGTest checks (nonempty supports, `Rules.exists_valid`,
  `exists_gammaCond`, Markov stage-1 selection) the hypotheses of every new Spec are satisfiable as far as can
  be checked cheaply (the satisfiability of `RunHyp` and `ofPast_valid` stays with s5/s6, as the report says).

## Per-Spec back-translation

| Spec | Back-translation | vs. TeX |
|---|---|---|
| `VstarStatement` | RunHyp ⇒ ∀ l∈[3,R], E_ω[X_{V,l}(ω.pool)] ≤ (6log₂M_l+12)n/M_l, and E[X_V] ≤ 2.1·((6log₂D_*+12)n/D_*) | faithful; "deterministic function" is the type of `XVl` (T0, fine) |
| `PayStatement` | RunHyp, δ designation, ω∈supp, l∈[3,R], ∀ J with J⁺, I = past, ∀ valid rules R: (a1) \|J^lost\| ≤ (M−1)\|Lost_l\| (ℝ); (a2) #items with an end in Pool_l ≤ Σ_{v∈Pool_l} ω_l(v); (a3) #items with JV-bad port end ≤ (M−1)·#JV-bad classed ports; (b) each fresh centre on ≤1 unpaired leg, #legs ≤ Σ_{Z∈Std_l}\|F_Z\|; (c) E_ξ\|sdrPaid\| ≤ n(M−1)/(4M)^4 ≤ n/(256M³), E_ξ\|loopPaid\| ≤ 2(2/Hcd)#PAR ≤ 5.5nM/Hcd; (d) on the Markov event pay^rd ≤ 4(…) and 4(…) ≤ 2n/M; (e) paid set = union of six classes | faithful; stronger in R (all valid rules) and J (all J⁺ sets); (b) per centre stated as "legs containing x", at least as strong |
| `PayGlobalStatement` | families J_l (J⁺), valid R_l: Σ_{l=3}^R #legs ≤ Σ_{l=1}^R Σ_Z\|F_Z\| ≤ 2n; draws ξ_l in the events at every round ⇒ Σ pay^rd_l ≤ 9n/D_* | faithful |
| `EXprimeStatement` | RunHyp, δ ⇒ E X' ≤ ε_X n, E X_U ≤ ε_U n + 5.5n/D_*, E X_pool ≤ 4.8n/D_*, E X_V ≤ 2.1(6log₂D_*+12)n/D_* | faithful; X_U bound matches the provider `LostStatement` (s6) verbatim |
| `UHsplitRoundStatement` | every past, valid rule: E_ξ[copies] ≤ X_{V,l}(ω.pool) + det_l | faithful ((ii)) |
| `UHsplitSumStatement` | X'(ω) ≤ 3E X', all J_l, R_l valid, ξ_l in events ⇒ Σ\|V(Q_l)\| ≤ 12E X' + 4Σdet_l | faithful ((iii)); stronger (any valid rules/J⁺ sets) |
| `UHsplitDetStatement` | RunHyp ⇒ Σ_{l=3}^R det_l ≤ 3ε_A n + 60n/D_* + 2F(log₂D_*)n ∧ 2F(log₂D_*) < 2^{-1000} | faithful (strict `<` kept) |
| `UHsplitThetaStatement` | situation of (iii) ⇒ Σ\|V(Q_l)\| ≤ ε_2(D_*)·n | faithful; "θ_Q ≤ 1/4 by Γ4" correctly not restated |
| `OneOutcomeStage1Statement` | ∃ ω ∈ supp with X'(ω) ≤ 3E X' | faithful (step (i)) |
| `OneOutcomeRoundStatement` | every past, valid rule: ∃ξ of positive weight in the event of (f); on the event copies ≤ 4(X_{V,l}+det_l), pay^rd ≤ 4(n/(256M³)+5.5nM/Hcd) | faithful (step (iii) and (3)); "probability ≥ 1/2" is proof-internal (N5) |
| `CostStatement` | ω∈supp with X' ≤ 3E X' ⇒ ∃ J_l (J⁺ at every round) ∃ decomposition D of E(G) with \|D\| ≤ (D_*/2+1085+ε_1)n + 2Σ f(roundQuotient … J_l) | T0-weaker naming (does not say "the MIX-C decomposition"), consumer-sufficient (N4) |
| `CostC0Statement` | Γ4(D) ⇒ C_0(D) ≤ D/2 + 1091 | faithful (Γ4 = ε_1 ≤ 6 ∧ ε_2 ≤ 1/4) |
| `JVpsStatement` | N0Cond, GammaCond (Γ1, Γ2(a), Γ3, Γ4), n ≥ N_0, d_1 ≥ D_*, valid run, designation ⇒ ∃ graphs Q_l (l∈[3,R]) without isolated vertices, f(G) ≤ C_0 n + 2Σf(Q_l), Σ\|V(Q_l)\| ≤ θ_Q n | faithful; FGraph is simple; same family in (1),(2) |
| `CorJVpsEGStatement` | N0Cond, GammaCond ⇒ every FGraph G (any universe) has f(G) ≤ c_EG·\|V(G)\|, c_EG = max(C_0/(1−2θ_Q), N_0/2) | faithful to s1:thmMain |

Constants checked against the TeX: `epsX`, `detl` (78, 30, 320, `log₂ θ^ult + 8`, `λ_{l-2}^{95}`), `FQ`
(3184, 30400, −90.2), `eps2` (12, 3, 60, 2), `eps1` (169, 252, 1.5, 3, 9), `C0` (1085), `cEG`, `Gamma4`
(ε_1 ≤ 6, ε_2 ≤ 1/4); strictness of `2F < 2^{-1000}`; log base 2 everywhere (`Real.logb 2`); (c)
`n(M−1)(4M)^{-4}` written `n(M−1)/(4M)^4` (same); `M_l − 1` in ℝ in Pay (no truncation issue), in ℕ in
`Xpool` (fine since `M_l ≥ 2^40`).

Arithmetic of the TeX proofs re-checked independently (not required by the Specs, but supports truth):
lemVstar (`t^CC+1 ≤ 2log₂M+2`, `3M·(2log₂M+2)/M² + 4M·1.37/M² = (6log₂M+11.48)/M`); lemPay (d)
(`4·5.5·8 = 176`, `176 M³λ^{-95} ≤ 176λ^{-90.2} ≤ λ^{-1.6} ≤ 1/M`); lemEXprime (`2.37 + 0.03 = 2.4`,
`2·2.4 = 4.8`); lemUHsplit (iv) (`78·8 = 624`, `624 + 320·8 = 3184`, `320·95 = 30400`,
`F(2^25) = 763184·2^{-2255} ≤ 2^{20}·2^{-2255}`, `F(2x) ≤ F(x)/2`); lemPay (a2) against
`c^agg_{h,l} = #{Y : d_{Y,l}(h) ≥ 1}` (s6.tex l. 255, `EG.Chain.cAgg`); propCost ledger (`X_U` uses
`169 + M_l ≥ 169 + M_l − 1`, s6.tex l. 403). No discrepancy found.

## Consistency

* Reuse: HI (locked), GammaSat (unit GAMMA), MainInternal (locked), Lost (s6) — the E X_U conjunct of
  `EXprimeStatement` is literally the conclusion of `LostStatement` (iii) (provider/consumer match).
* No Γ2(b),(c) assumed; `GammaCond` used for JVps/CorJVpsEG, `RunHyp` (Γ1, Γ3, N0Cond, n ≥ N_0, d_1 ≥ D_*,
  valid run) for the rest. JVps's hypotheses imply `RunHyp`.
* Probe Defs `Outcome.lean` are pure compositions of locked Defs (`StageData.ofOutcome` with the s5 statuses,
  `RoundInput.ofPast`, `XU/Xpool/XV/Xprime`); no new mathematics.
* Composition JVps ⇐ OneOutcomeStage1 + Cost + UHsplitTheta + OneOutcomeRound(∃ξ) + `Rules.exists_valid`
  typechecks at the level of statements: Cost's `J_l` feed `roundQuotient` = `(chosenRules).Q xiChosen`,
  which is an instance of UHsplitTheta's `(Rs l).Q (ξs l)` once `chosenRules` is valid and `xiChosen` lies in
  the event. The only open glue is `RoundInput.ofPast_valid` (N3).

## Notes (no statement change required unless stated)

* N1 (minor, vacuity of a conjunct): lemPay (e) is `rfl` in the locked Defs. The TeX content "no other item is
  paid" is thereby definitional; the substantive accounting (every J-item is paid or lifted, used by propCost)
  is carried by lemLift / MIX-C, not by this conjunct. The report says so (hazard 8). Suggest adding "(`rfl`)"
  to the file comment so no prover spends effort on it.
* N2 (minor, test hygiene): the `EGTest/Spec_s7b.lean` module docstring says the test checks
  "`θ_Q ≤ 1/4 < 1/2` and `C_0 ≥ D_*/2`", but only `θ_Q < 1/2` is checked. Theorem HI″ additionally needs
  `0 ≤ θ_Q` and `D_*/2 ≤ C_0`, i.e. `eps2 D ≥ 0` and `eps1 D ≥ 0` under Γ1 (all summands are non-negative
  once `log₂log₂D_* > 0`). These are proof obligations of s7:thmMainProof, not Spec problems; the test
  docstring should be corrected or the two checks added.
* N3 (minor, known risk): Pay, PayGlobal, UHsplit (ii)/(iii)/(iv-Theta), OneOutcomeRound quantify over every
  `J` with `JPlusProps` and every valid rule, without assuming `RoundInput.Valid`. They are provable only via
  `RoundInput.ofPast_valid` (TRIAGE §3 item 31, deferred). I checked the fields of `RoundInput.Valid` against
  `JPlusProps` + run-level facts: J1 (aggregated) follows from `J1hub` and role disjointness, J2/J2tot from
  `J2out`/`J2card`, typing from `types`; `roles`, `Hcd_ge`, `good_cand`, `ljv_*`, `lendGood_ports`,
  `cls_*` are run/designation/stage-1 facts. No field looked unobtainable, but this is the single point where
  the whole s7b chain could become unprovable; it should be scheduled.
* N4 (T0, accepted): `CostStatement` is existential in the J-sets (witness `J_l = ∅` is admissible since
  `JPlusProps ∅` holds). This makes the statement not weaker in strength of the bound, only in naming: it
  does not assert that `D` is the MIX-C decomposition. Its only consumer (JVps) needs exactly this form.
* N5 (cosmetic): OneOutcomeRound states positive weight of the Markov event, not "probability ≥ 1/2"; the 1/2 is
  in the TeX proof, not the statement; positive weight is what `xiChosen` needs.
* N6 (cosmetic, duplication): PayGlobal (b) second conjunct `Σ_{l≤R}Σ_Z|F_Z| ≤ 2n` restates the last conjunct
  of `FreshStatement` (s2:propParentless (i), K4) with an ℝ cast; Vstar (2) and EXprime (4th conjunct) state
  the same bound with different parenthesization (`2.1 * ((6L+12)*n/D)` vs `2.1*(6L+12)*n/D`). Both
  duplications are in the TeX itself; the proofs should reuse the other Spec (one `ring_nf` bridge).
* N7 (cosmetic, locked Defs docstring): `EG.RunHyp`'s docstring says "there are no VX-parts" is "an explicit
  hypothesis on the run", while JVps/Cost say it has no Lean content (VX-parts are not defined). The Specs are
  right; the RunHyp docstring is stale (locked; integrator action only).
* N8 (consumer note): JVps reads `d_1` as `run.d G 1 = 2|E(run.graph G 1)|/|…|`, while HIHyp reads
  `2|E(G)|/n`; the main-proof glue needs `run.graph G 1 = G` from the run-existence Spec (s2:propExists).

## Math findings

None against the manuscript. All inequalities of lemVstar, lemPay (a2)(c)(d), lemEXprime, lemUHsplit (ii)/(iv),
propCost and the constants were re-derived and hold.
