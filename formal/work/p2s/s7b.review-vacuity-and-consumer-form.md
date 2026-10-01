# Clean-room review of the s7b Specs (lens: vacuity-and-consumer-form, model B)

Reviewer: clean-room statement reviewer (no Lean file of the repo edited). Date 2026-09-30.
Scope: `work/p2s/s7b.md` and the files it lists: `EG/Defs/Probe/S7b/Outcome.lean` (new probe Defs),
`EG/Spec/Quot/{Vstar,Pay,EXprime,UHsplit,OneOutcome,Cost,JVps}.lean`, `EG/Spec/Main/CorJVpsEG.lean`
(new), the reused `EG/Spec/Quot/HI.lean`, `EG/Spec/Gamma/Sat.lean`, `EG/Spec/Main.lean`, and
`EGTest/Spec_s7b.lean`. TeX: `proofs/manuscript/s7.tex` 158–430 (defSchedule, consRound), 881–1560
(lemVstar … thmMainProof, remNonCirc), `s1.tex` (condGamma, defConstants, thmMain), `s6.tex`
(defLending, thmMIXC), `s2.tex` (propParentless, lemTower). Locked Defs read:
`EG/Defs/Quot/{Round,Schedule,Cand,Xprime,Constants}.lean`, `EG/Defs/Gamma/{Core,Full}.lean`,
`EG/Defs/Main/{Gamma,GammaCond}.lean`, `EG/Defs/Chain/{Lending,JSet,Design,JConsumer}.lean`,
`EG/Defs/Stage1/{Pool,Law}.lean`, `EG/Defs/Light/Stages.lean`, `EG/Defs/Prob/FinDist.lean`; Lib/Proof
consumers: `EG/Proof/Quot/HI.lean` (`hiHyp_of_fintype_index`), `EG/Lib/Quot/Round.lean`
(`Rules.exists_valid`, `chosenRules_valid`), `EG/Lib/Prob/Basic.lean`, `EG/Spec/Chain/Lost.lean`,
`EG/Spec/Quot/RoundStep.lean`.

## Verdict: APPROVE (no major issue; minor and cosmetic notes only, no statement change required)

* No new Spec has contradictory hypotheses, and no conclusion is trivially true except where the TeX
  itself is trivial (lemPay (e) "no other item is paid", propCost's "Consequently `C_0 ≤ D_*/2 + 1091`",
  and the two Markov existence claims of lemOneOutcome); see the table.
* Every Spec is in the form its consumer reads: the chain Cost → OneOutcomeRound → UHsplitTheta →
  JVps → (HI″) → CorJVpsEG → MainInternal closes with `rfl`-level plumbing (checks V4, V8, V8′, V9,
  V10 below, and `EG.hiHyp_of_fintype_index`, `EG.HB.Run.graph_one`).
* Reuse is correct: `HI.lean`, `Gamma/Sat.lean`, `Main.lean` are used, not restated; the s6 provider
  `EG/Spec/Chain/Lost.lean` already writes the stage data as `EG.Quot.stageOf ω` and `X_U` as
  `XUOf`, so the new probe Defs are the shared vocabulary, not a second copy. No hypothesis mentions
  Γ2(b),(c); the only Γ2 item is `Gamma2a`, inside the sanctioned `GammaCond`.
* Hygiene: `python3 -I scripts/lint.py` → `lint (development): 0 findings`. Scratch file compiled
  with `lake env lean` (rc 0), outside the repo (`scratchpad/s7b_vacuity.lean`).

## Scratch checks (compiled, rc 0; file `s7b_vacuity.lean` in the session scratchpad)

| # | Check | Result | Meaning |
|---|---|---|---|
| V1 | `JPlusProps run G δ S l ∅` | proved (`constructor <;> simp [degE, edgesAt]`) | the quantifier "for every past" (`∀ J, JPlusProps … → …`) of Pay, UHsplit (ii), OneOutcome (3) is never empty; the first conjunct of Cost's `∃ Js` is satisfiable. Limitation: the only instance exhibited is the degenerate empty past (see N6). |
| V2 | `R.paidEdges ξ = Jlost ∪ paidPool ∪ paidJVBad ∪ unpairedLegs ∪ sdrPaid ∪ loopPaid` | `rfl` | lemPay (e) is definitional (T0 PAY-E-INSPECTION, as recorded). |
| V3 | `∀ v ∈ (R.Q ξ).verts, ∃ e ∈ (R.Q ξ).edges, v ∈ e` | proved from `Rules.Q` | the JVps clause "without isolated vertices" is by construction for every round-step quotient. |
| V4 | `thetaQ D = eps2 D` | `rfl` | UHsplitTheta (`eps2`) feeds JVps (`thetaQ`) with no rewriting. |
| V5 | `n(M−1)/(4M)^4 ≤ n/(256M^3)` for all real `M ≥ 1`, `n ≥ 0` | proved | the chaining conjunct of Pay (c) is pure arithmetic (harmless). |
| V6 | `2.1 * ((6 log₂D + 12) n / D) = 2.1 * (6 log₂D + 12) * n / D` | `ring` | the `E X_V` bound of Vstar and of EXprime are the same number in two spellings (N2). |
| V7 | `∃ ξ, 0 < w ξ ∧ R.MarkovEvent ξ` for every `I`, every `R` | proved with no hypothesis (`half_le_prob_le_four_mul_expect_and` + `exists_of_prob_pos`) | the existence conjunct of OneOutcomeRound is pure Markov; its hypotheses (RunHyp, δ, ω ∈ supp, J⁺, R.Valid) are inert for that conjunct (N5). |
| V8 | `(pastOf …).chosenRules.Q (pastOf …).chosenRules.xiChosen = roundQuotient run G δ (stageOf ω) ω.pool l J` | `rfl` | the `Q_l` of Cost is the `(Rs l).Q (ξs l)` of UHsplitTheta at `Rs l := chosenRules`, `ξs l := xiChosen` (JV-SAME-Q closes). |
| V8′ | `Xi (pastOf …).G (pastOf …).M = Xi G (run.M G l)` | `rfl` | the draw types of Pay/UHsplit/OneOutcome (`Xi I.G I.M`) and of the global forms (`Xi G (run.M G l)`) agree. |
| V9 | JVps hypotheses ⇒ `RunHyp N0 D G run` | proved | JVps's proof can call every `RunHyp` Spec of this chunk (no hypothesis gap). |
| V10 | `(∃ ξ, 0 < w ξ ∧ MarkovEvent ξ) → MarkovEvent xiChosen` | proved | OneOutcomeRound's existence clause is exactly what puts the J-consumer's `xiChosen` in the event; so Cost's quotients satisfy the hypothesis of UHsplitTheta. |
| V11 | `4(1/(256·2^3) + 5.5·1·2/1) ≤ 2·1/2` is false | `norm_num` | the second Pay (d) conjunct (`… ≤ 2n/M_l`) is not pure arithmetic: it needs `Hcd_l` large (tower facts). Content, not vacuity. |
| V12 | `CostC0Statement` | one line from Γ4 | trivially true, as in the TeX ("Consequently"). |
| V13 | with all `Q l` empty, the JVps conclusion is `f(G) ≤ C_0 n` | proved | the JVps conclusion is not satisfiable by junk quotients: its content is the nontrivial bound. |

EGTest/Spec_s7b.lean (re-read, not re-run beyond the unit's rc 0 report) adds: nonempty supports of
the stage-1 and round laws, `OneOutcomeStage1Statement` proved (so `X'(ω) ≤ 3E X'` at positive
weight is satisfiable), `Rules.exists_valid` for valid pasts, `exists_gammaCond`, `θ_Q < 1/2` under Γ4,
`cEG = max(C0/(1−2θ_Q), N0/2)` by `rfl`.

## Per-Spec: vacuity and consumer form

| Spec | Hypotheses satisfiable? | Conclusion trivial? | Consumer (form matches?) |
|---|---|---|---|
| `VstarStatement` | `RunHyp` (needs s2:propExists + GammaSat, not exhibitable in a test; N7) | no: bounds an expectation of a ℕ-valued functional by an explicit function; RHS ≥ 0 since `M_l ≥ 1` | EXprime (4th conjunct is the same fact, N2); UHsplit reads `XVl run G ω.pool l` verbatim |
| `PayStatement` | RunHyp, δ, ω ∈ supp (nonempty), J with J⁺ (V1), `R.Valid` (`Rules.exists_valid` given `I.Valid`, N6) | (e) is `rfl` (V2); the (c)-chaining conjunct is pure arithmetic (V5); all other conjuncts carry content (V11) | OneOutcomeRound (payrd bound), Cost (through the MIX-C B′ bound), PayGlobal |
| `PayGlobalStatement` | as Pay, for families `Js`, `Rs`, `ξs` (dependent types line up, V8′) | no | Cost's `9n/D_*` and `2n` rows |
| `EXprimeStatement` | RunHyp, δ | no | UHsplitTheta (`12 E X' ≤ 12 ε_X n`), Cost (`3E X' ≤ 3ε_X n`); provider Lost (iii) is stated at `XUOf` (same term) |
| `UHsplitRoundStatement` | as Pay | no | OneOutcomeRound (copies bound) |
| `UHsplitSumStatement` | as Pay + `X'(ω) ≤ 3E X'` (satisfiable: OneOutcomeStage1 proved) + `MarkovEvent` at every round (V7) | no | UHsplitTheta |
| `UHsplitDetStatement` | RunHyp | no (first conjunct); second conjunct is a numeric fact about `D_*` only (N3) | UHsplitTheta |
| `UHsplitThetaStatement` | as UHsplitSum | no | JVps (2), at `Rs l := chosenRules`, `ξs l := xiChosen` (V8, V10); `eps2 = thetaQ` (V4) |
| `OneOutcomeStage1Statement` | RunHyp, δ (inert: pure Markov, proved in EGTest) | true but not vacuous (a real, easy lemma, as in the TeX) | Cost, UHsplitSum/Theta (their `X' ≤ 3E X'` hypothesis) |
| `OneOutcomeRoundStatement` | as Pay | existence conjunct is pure Markov (V7); the two bounds are consequences of UHsplitRound + Pay (c), as the TeX's "Consequently" | Cost/JVps: puts `xiChosen` in the event (V10) |
| `CostStatement` | RunHyp, δ, ω ∈ supp, `X'(ω) ≤ 3E X'` | no: `∃ Js` is satisfiable in its first conjunct by `Js = ∅` (V1), but the second conjunct then reads `f(G) ≤ C_0 n` (V13 shape), so the existential carries the full content whichever `Js` the prover exhibits | JVps (1) with `f(G) ≤ D.length` (`EG.fnum_le_of_isDecomp`), same `Q_l` as UHsplitTheta (V8) |
| `CostC0Statement` | `Gamma4 D` (satisfiable) | trivially true (V12), as the TeX | JVps/CorJVpsEG do not need it (the TeX sentence is informational) |
| `JVpsStatement` | `N0Cond ∧ GammaCond` (satisfiable, `exists_gammaCond`), `n ≥ N_0`, `d_1 ≥ D_*`, valid run, δ (existence of run and δ is s2:propExists and anc ≠ ∅; N7) | no (V13) | CorJVpsEG via `HIHyp`: `hiHyp_of_fintype_index` takes a family over any `Fintype ι` (here `Icc 3 R`), `run.d G 1 = 2|E(G)|/|V(G)|` by `run.graph_one`, isolated-vertex hypothesis of HIHyp is unused by the producer; universe: `JVpsStatement.{0}` gives `W : ℕ → Type` as HIHyp wants |
| `CorJVpsEGStatement` | `N0Cond ∧ GammaCond` | no | `MainInternal` with `c := ⌈cEG N0 D⌉₊` at `V : Type`; polymorphic `V : Type u` is a strengthening the proof must transport (recorded, hazard 10) |

## Fidelity (back-translation vs. TeX), briefly, from this lens

Every new Spec back-translates to the quoted TeX or to a form stronger in a way the TeX proof
supports (every admissible `J_l`, every valid fixed rule, per-round forms of Pay (b),(d)). Checked in
particular: quantifier order (RunHyp → δ → ω → l → J → I → R → ξ), `3 ≤ l ≤ R` everywhere, sums over
`Icc 3 R` (and `Icc 1 R` for `Σ_{l,Z}|F_Z|`, `X_U`), strict `<` in `2F(log₂D_*) < 2^{-1000}`,
`M_l − 1` in ℝ in Pay (no truncation), `log₂ = Real.logb 2`, constants 6/12/2.1, 5.5/4.8/10.3,
78/30/320/95, 3184/30400/−90.2, 12/3/60/2, 169/252/1.5/3/9, 1085/1091, `c_EG = max(C_0/(1−2θ_Q),
N_0/2)`, `Gamma4 = (ε_1 ≤ 6 ∧ ε_2 ≤ 1/4)`, and that "θ_Q ≤ 1/4" is Γ4 (hypothesis of JVps through
`GammaCond`), not restated.

## Notes (none requires a statement change)

* **N1 (cosmetic, `Pay.lean` ll. 112–114).** Conjunct (e) is `rfl` (V2). It is the faithful rendering
  of "no other item is paid" once the paid set is *defined* as the union (T0 PAY-E-INSPECTION); its
  value is documentary. The actual inspection content ("the single edges of `Obj_l` are exactly the
  paid ones") is likewise definitional in `Rules.objs`. Keep; the docstring already says so.
* **N2 (minor, `Vstar.lean` ll. 52–53 vs `EXprime.lean` ll. 56–57).** The bound `E X_V ≤
  2.1(6log₂D_*+12)n/D_*` is stated twice (as in the TeX: lemVstar and lemEXprime "More precisely"),
  with different parenthesization (`2.1 * ((…) * n / D)` vs `2.1 * (…) * n / D`, equal by `ring`,
  V6). Harmless; if ever touched, spell EXprime's 4th conjunct exactly as Vstar's 2nd so the proof is
  literal reuse.
* **N3 (cosmetic, `UHsplit.lean` l. 98).** `2F(log₂D_*) < 2^{-1000}` is a fact about `D_*` alone
  (it needs only `log₂D_* ≥ 2^25`, i.e. Γ1(a)), but it is only available under `RunHyp N0 Dstar G run`,
  i.e. after exhibiting a graph and a valid run. No consumer uses it (blueprint UH-GAMMA4: "never
  used"), so nothing is lost; a consumer wanting the pure fact would need a `∀ D, Gamma1 D → …`
  form. Faithful to the TeX sentence, which is inside the lemma's setting.
* **N4 (cosmetic, `UHsplit.lean` l. 117 vs `JVps.lean` l. 65).** `eps2 Dstar` vs `thetaQ Dstar`,
  `rfl` (V4). Fine.
* **N5 (minor, `OneOutcome.lean` ll. 65–71, 84).** Both existence claims are hypothesis-free Markov
  facts (EGTest for stage 1; V7 for the round: `P(event) ≥ 1/2 > 0` for every past and every rule).
  The Specs keep the TeX's standing hypotheses, which the proofs will discard. Not vacuous, not
  trivial in the bad sense; simply cheap. The s7a Spec `EG/Spec/Quot/RoundStep.lean` (l. 134) states
  the sharper `1/2 ≤ P(MarkovEvent)`, of which OneOutcomeRound's clause is a corollary; no
  duplication of a statement, just a weaker consumer-level form (what `xiChosen` needs, V10).
* **N6 (minor; limitation of the non-vacuity evidence, `Pay.lean` l. 82, `UHsplit.lean` l. 64,
  `OneOutcome.lean` l. 82, `Cost.lean` l. 65).** "For every past" is instantiated in the tests only at
  `J = ∅` (V1), where all items are empty and the claims are trivial. The informative instances are
  the J-sets produced by JS-LC, and for those the quantifier `∀ R, R.Valid → …` is populated through
  `Rules.exists_valid (hI : I.Valid)`, whose premise for `I = pastOf …` is `RoundInput.ofPast_valid`
  (not in Lib yet; grep finds no such theorem; TRIAGE §3 item 31 joint obligation). The Specs do not
  assume `I.Valid` (correct: it must be *derived* from RunHyp ∧ δ ∧ ω ∈ supp ∧ JPlusProps in the
  proofs), so nothing is hidden; but until `ofPast_valid` exists, the only exhibited non-degenerate
  witness of the round-step hypotheses is none. Recorded as the status note already says.
* **N7 (cosmetic; inherent).** Every RunHyp-conditioned Spec of the chunk (Vstar, Pay, EXprime,
  UHsplit, OneOutcome, Cost) is non-vacuous only through s2:propExists (a valid run on any graph with
  `d_1 ≥ D_*`) and s7:lemGammaSat (a `D_*` with `N0Cond ∧ GammaCond`, proved). A graph with
  `n ≥ N_0 ≥ 2^{40}` vertices and `d_1 ≥ D_* ≥ 2^{2^{256}}` cannot be exhibited in a test; this is a
  property of the manuscript's constants, not of the encoding. `RunHyp` forces `R ≥ 1`
  (`Run.Valid` has `d_{R+1} < D_* ≤ d_1`), consistent with the TeX.
* **N8 (cosmetic, `Pay.lean` ll. 98–99).** The chaining conjunct `n(M−1)/(4M)^4 ≤ n/(256M^3)` holds
  for every real `M ≥ 1` (V5); it is the TeX's own "≤ n/(256M_l^3)". Keep (faithful).
* **N9 (cosmetic, `JVps.lean` l. 59).** `Dstar ≤ run.d G 1` is implied by `run.Valid G Dstar` once
  `R ≥ 1`, and conversely forces `R ≥ 1`; the TeX lists "d_1 ≥ D_*" explicitly, so keep.
* **N10 (cosmetic, `Cost.lean` ll. 65–70).** The `∃ Js` is not tied to "the J-sets of the MIX-C
  chain" (T0, recorded). From the consumer's side this is right: JVps needs only *some* admissible
  `Js` with the bound, and UHsplitTheta holds for *all* admissible `Js`. From the vacuity side: the
  admissibility conjunct is satisfiable by `Js = ∅` (V1), so the whole weight of the Spec is in the
  decomposition bound; there is no way to satisfy it with junk quotients (V13). Fine.
* **N11 (consistency, positive).** `Hcd run G l = I.Hcd`, `I.M = run.M G l`, `I.G = G`,
  `I.pool = Stage1.poolL G ω.pool l`, `I.lost = lostRound …`, `I.fresh = freshCentres …` for
  `I = pastOf …` are all definitional (V8′ and the `ofPast` record), so the Spec-level names
  (`Hcd run G l`, `lostRound …`, `run.M G l`) and the Defs-level fields the round step reads never
  diverge. `stageOf ω` is `StageData.ofOutcome ω (Light.demoted ω) (Light.dem ω) (Light.lp ω)`, the
  G-S5-1 instantiation, and `EG/Spec/Chain/Lost.lean` uses the same `stageOf`/`XUOf` (no second copy).
* **N12 (cosmetic, outside this unit's files).** `EG/Lib/Quot/Xprime.lean` l. 31: the `[s7:lemVstar]`
  "deterministic function" docstring is attached to `XV_le_Xprime`, which states something else.
  Already noted by the unit.

## Math findings

No T2/T3 finding. The TeX arithmetic behind the statements was re-derived from this lens as a
consistency check (each chained inequality in a Spec must be *true*, else the Spec is unprovable):
lemVstar `6log₂M+11.48 ≤ 6log₂M+12`; lemPay (c) `4·1.37 = 5.48 ≤ 5.5`, (d) `4·5.5·8 = 176`,
`176λ^{-90.2} ≤ λ^{-1.6} ≤ 1/M_l` for `λ ≥ 2^{25}`, `4n/(256M^3) ≤ n/M`, `Σ 2n/M_l ≤ 4n/D_* ≤ 9n/D_*`;
lemEXprime `2.37 + 0.03 = 2.4`, `n/M^2 ≤ 0.03n/M` iff `M ≥ 34`, `2·2.4 = 4.8`, `5.5 + 4.8 = 10.3`;
lemUHsplit (iv) `78·8 = 624`, `624 + 320·8 = 3184`, `320·95 = 30400`, `4.8 − 95 = −90.2`,
`F(2x) ≤ F(x)/2` on `[2,∞)`, `F(2^{25}) = 763184·2^{-2255} < 2^{20−2255}`, `2·2^{-2235} < 2^{-1000}`;
propCost `745 + 338 + 2 = 1085`, `(169 + M_l − 1) ≤ 169 + M_l`, bracket `≤ X_U + X_pool ≤ X'`.
T0 encoding decisions with a manuscript-wording consequence, both already recorded by the unit:
(i) lemPay (e) is the defining equation of the paid set (PAY-E-INSPECTION); (ii) lemOneOutcome (2)
and step (iv) have no Lean content (deterministic stage-3 Specs; rounds 1, 2 inside MIX-C).
