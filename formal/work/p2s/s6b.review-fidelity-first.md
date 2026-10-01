# Clean-room review of the s6b Specs (lens: fidelity-first, model A)

Reviewed: `work/p2s/s6b.md`; new Spec files `EG/Spec/Chain/Lost.lean`, `EG/Spec/Chain/MixC.lean`,
`EG/Spec/Chain/JPlusV.lean`; TeX `proofs/manuscript/s6.tex` lines 335-867 (v6.1). I also read the Defs
they use: `EG/Defs/Chain/{Lending,StageInst,JConsumer,Design,Constants}.lean`,
`EG/Defs/Probe/S7b/Outcome.lean`, `EG/Defs/Probe/S4/TPV.lean`, `EG/Defs/Stage1/{Law,COL}.lean`,
`EG/Defs/Light/Stages.lean`, `EG/Defs/Gamma/Full.lean` (`RunHyp`), and `EG/Defs/HB/Run.lean`
(`anc`, `ancEps`, `ancS`, `ancVerts`). I also read the consumer Specs `EG/Spec/Quot/Cost.lean`
(`CostStatement`), `EG/Spec/Quot/EXprime.lean` and `EG/Spec/Chain/CONCL.lean` (`ConcLSumStatement`),
and the TeX of s2:lemTower(b), s3:lemCOL(a),(e) and s5:lemExpect, plus the preamble macros
(`\cKRED` = 745, `\cFresh` = 338). I edited no Lean file.

**Verdict: approve.** I found no fidelity defect that changes the meaning of a statement. I have two
minor wording corrections for the docstring/status (M1, M2), two T0 observations (M3, M4) and one
redundancy note (C1). Lint: `python3 -I scripts/lint.py` gives 0 findings. The oleans of the three modules exist
(built 2026-09-30 02:18-02:19).

## 1. Fidelity (back-translation vs TeX)

### `LostStatement` [s6:lemLost]
Back-translation. Let G be a graph, N0 and D* reals, and run an HB run with RunHyp (Γ1, Γ3, N0Cond,
n ≥ N0, d_1 ≥ D*, valid run). Let δ be a designation with IsDesignation. Then:
- (i) For every l ≥ 3, every Z ∈ Std_l and every u ∈ Q_Z, with Y = δ(l,u), under the stage-1 law:
  - P(u ∈ Lost_Z) ≤ K^JS_l·ρ_l + P(Y lend-bad);
  - K^JS_l·ρ_l + P(Y lend-bad) ≤ M_l^{-2} + 2|V(Y)|^{-2};
  - M_l^{-2} + 2|V(Y)|^{-2} ≤ 2M_l^{-2}.
- (K6) For every l ∈ ℕ: E|Lost_l| ≤ 2n/M_l².
- (iii) E X_U ≤ ε_U(D*)n + Σ_{l=1}^{R} 2n(169+M_l)/M_l², and that right-hand side is
  ≤ ε_U(D*)n + 5.5n/D*.

Comparison with the TeX ("Fix a valid run and a designation δ. … (i) for every classed port u of round
l ≥ 3, P(u∈Lost) ≤ K^JS_l ρ_l + P(Y(u) lend-bad) ≤ M_l^{-2} + 2|V(Y(u))|^{-2} ≤ 2M_l^{-2}; (K6)
E|Lost_l| ≤ 2n/M_l^2 for every round l; (iii) E X_U ≤ ε_U(D_*) n + Σ_l 2n(169+M_l)/M_l^2 ≤ ε_U(D_*) n
+ 5.5 n/D_*"):
- **Quantifiers.** δ is fixed before the law (it is deterministic), which is correct. "classed port u
  of round l" is `u ∈ run.classed G l a` with `a ∈ Std_l`. `Lost` is `Lost_Z` for that Z; the Z is
  unique on a valid run.
- **Constants and powers.** `KJS = M^2` is a natural number and `rhoJS = M^{-4}`. `^(-2:ℤ)` is an
  integer power of a real. `n = G.card = |G.verts|`. The chains are stated link by link, which is the
  literal content. The bound 2|V(Y)|^{-2} is looser than the proof's |V(Y)|^{-2}; the TeX states the
  looser value, so this is faithful.
- **Edge cases, checked in a scratch file.** Lean gives `(0:ℝ)^(-2:ℤ) = 0` and `2n/0^2 = 0`. So at
  l ∉ [3,R], where Lost_l = ∅, (K6) reads 0 ≤ 2n/M_l², which holds for every value of M_l. At M_l ≠ 0,
  `KJS·rhoJS = M^{-2}` is exact.
- **Range of Σ_l in (iii).** It is [1,R], the range of `X_U` in the locked Def. s2:lemTower(b)
  states "Σ_{l≤R} 1/M_l ≤ 2/D_*" over the same range, and M_l ≥ 2^40 for l ≤ R. So the second link
  holds as stated: (2 + 338/2^40)·2 ≤ 5.5.
- **Consumer form.** `XUOf` is the form that `EXprimeStatement` reads. The second conjunct of
  `EXprimeStatement` is exactly the composition of the two links of (iii), so the two Specs agree.

### `MixCStatement` [s6:thmMIXC] (b)+(c), Option B′
Back-translation. Assume RunHyp and a designation δ, and take any stage-1 outcome ω of positive
weight. Take any J-consumer C (in the context of ω's stage data) and any b : ℕ × EdgeSet → ℝ that
bounds |Obj_l(C, J)| for all 3 ≤ l ≤ R and all J with the J⁺ properties at round l. Then there are
sets J_l (3 ≤ l ≤ R), each with the J⁺ properties, and a decomposition D of E(G) into cycles and single
edges such that

|D| ≤ (D*/2 + 745 + 338)n + ε_M(D*)n + 80·dem + 369·lp + 169·Σ_{l=1}^{R}|Lost_l|
      + 1.5·Σ_{l=1}^{R} Σ_{Y ancestor} m_{Y,l} + Σ_{l=3}^{R} b(l, J_l).

Comparison with the TeX (c) display, `(D_*/2+c_KRED+c_Fresh)n + ε_M(D_*)n + [80 dem + 369 lp + 169
Σ_l|Lost_l|] + 1.5 Σ_{(Y,l)} m_{Y,l} + Σ_l|Obj_l|`:
- **Constants.** They match: c_KRED = 745 and c_Fresh = 338 (preamble), and `epsM` is the locked
  formula ε_K + 169ε_A + 252/D*.
- **Cost itemization.** I re-derived it and it matches the TeX:
  - K-RED: (D*/2 + 745 + ε_K)n + 80·dem + 369·lp;
  - TPV: 169(2 + ε_A)n + 169Σ|Lost_l|;
  - JS-LC: 126·Σ_{l≥3} n/M_l ≤ 252n/D*, plus 1.5Σ_giant m ≤ 1.5Σ_all m;
  - J-consumer: Σ|Obj_l|.
- **Coverage.** "The output is a decomposition of E(G)" is `IsDecomp (G.edges : Set _) D` on a
  loopless set, which follows CONVENTIONS.
- **Index ranges.** They match the convention of `ConcLSumStatement`. m_{Y,l} = 0 off
  r(Y)+2 ≤ l, and Lost_l = ∅ for l ≤ 2.
- **Hypotheses.** RunHyp matches "valid run with n ≥ N_0, d_1 ≥ D_*" plus the standing parameter
  hypotheses. It carries no Γ2(b),(c) and no Γ4. The K-RED Spec also takes only RunHyp, so the
  declared inputs are consistent.
- **Stage-3 outcomes.** They are not data (TRIAGE §2.8). This is acceptable because the TPV, PV and
  VX⁺ Specs are deterministic existence statements, and the Lean conclusion is an existence
  statement.
- **Where the Lean form is weaker.** See M1, M3 and M4 below. In each case the TeX implies the
  Lean form (take J_l to be the chain's sets, which have `JPlusProps` by JS-LC/J⁺), and the
  consumer `CostStatement` has exactly this shape: ω ∈ supp, `stageOf ω`, ∃ Js with `JPlusProps` on
  Icc 3 R, ∃ D with `IsDecomp`.

### `MixCConcStatement` [s6:thmMIXC] (c), last sentence
"Moreover 1.5Σ_{(Y,l)} m_{Y,l} ≤ 1.5 ε_CONC(D_*) n". This is `ConcLSumStatement` scaled by 1.5
under RunHyp (Γ1 gives Gamma1core). `EGTest/Spec_s6b.lean` derives it. It is faithful and redundant
by design, because the TeX states it separately (see C1).

### `MixCTPVApplicableStatement` [s6:thmMIXC] (a), bullet "Lemma TPV at step (1)"
Back-translation. Take any ω ∈ supp, any l and any Z = a ∈ Std_l.
- **Z lend-good.** `TPVHyp(Z^0, O_Z, Ret_Z, 2^{-5}, s_l/4)` holds. That is: TPVSize|Z^0|;
  V(O_Z) = Z^0; O_Z is a (2^{-5}, s_l/4)-expander; 2^{-7} ≤ 2^{-5} ≤ 2^{-5};
  2^150(log₂|Z^0|)^42 ≤ s_l/4; and Ret_Z ⊆ Z^0.
- **Z lend-bad.** The same with s = s_l.

Checked against the TeX bullet and the Defs:
- **Lend-good case.** `OZ` is `FGraph.ofEdges (Z0) (Own_Z)`. `Coherent.colA_own` gives that
  `(H_Z).restrictEdges Own_Z` is an `(ancEps, ancS/4)`-expander. For a standalone Z,
  `ancEps = 2^{-5}` and `ancS = s_l` (`HB/Run.lean`), so the parameters are (2^{-5}, s_l/4), as in
  the TeX.
- **Size condition.** L_Z = log₂|V(Z)| = log₂|Z^0| for a standalone Z. s3:lemCOL(e) states
  "s_Y/4 ≥ 2^150 L_Y^42" for standalone Y, with no stage-1 event.
- **Lend-bad case.** O_Z = X^0_Z, and s2:propStructure(i) makes it a spanning (2^{-5}, s_l)-expander.
- **Size of Z^0.** "|Z^0| ≥ P_l ≥ N_0" becomes `TPVSize |Z^0|` through N0Cond, the form of the TPV
  Spec.
- **Omitted clause.** "E = Erem(Z) ⊇ E(O_Z)" concerns an internal set and is correctly left to the
  proof (s6:lemLent(iii)).
- **Concrete parameters.** The Spec uses the concrete (ε_O, s) rather than ∃ε_O s. This is stronger
  and literal.

### `JplusVStatement` [s6:lemJplus] (v)
"In the colourings of Definition s3:defCOL, colours of distinct edges are independent." The Lean
statement is mutual independence, under `Stage1.law G run`, of the label triples `ω.col Y e` over all
pairs (Y ∈ ancestors, e ∈ E(H_Y)). This is faithful: the triple (bit, lent index, own label) is
"the colour" of the edge, and independence of the triples implies independence of each component.
It is stronger than the per-ancestor form and is proved in `EGTest/Spec_s6b.lean`, so it is true for
every run with no hypothesis.

## 2. Vacuity
- **RunHyp.** Its satisfiability is not checked, as for the s5 Specs. It is shared with every
  s5/s6/s7 Spec and is not a new risk.
- **MixC.** The universally quantified objects are nonempty or satisfiable:
  - J-consumers: `nonempty_jConsumer`;
  - the b-hypothesis: take b := |C.out|;
  - the stage-1 support: `supp_nonempty`.

  The conclusion is not trivially true: D must decompose E(G) within a bound whose main term is
  (D*/2 + O(1))n. See M1 for the freedom in choosing Js.
- **Lost.** Every conjunct is a non-trivial inequality. The edge cases (M_l = 0 off-range,
  |V(Y)| = 0) only make links trivially true where the TeX statement is empty or trivial anyway.
- **TPVApplicable.** No hypotheses beyond RunHyp, IsDesignation and ω ∈ supp, and the conclusion has
  content.
- **JplusV.** It is proved, so it is not vacuous. It is a structural fact of the product law, as in
  the TeX ("holds because every colouring … is uniform and independent over edges").

Scratch probe: `/tmp/s6b_rev/Probe.lean`. The two edge-case evaluations (0^{-2} = 0 and x/0 = 0)
compile. The two arithmetic helper examples did not compile with the minimal imports I used, and I did
not retry them to avoid loading all of Mathlib on the shared machine. I checked them by hand:
K·ρ = M^{-2}, and (2 + 338/2^40)·2 ≈ 4.0000000006 ≤ 5.5.

## 3. Consistency
- **Reuse.** The Specs reuse the locked Defs and the existing probe Defs (S7b `stageOf`/`XUOf`,
  S4 `TPVHyp`). No new Defs file. No Γ2(b),(c) anywhere, and none of the three files assumes Γ4.
- **Duplication.**
  - `MixCConcStatement` duplicates `ConcLSumStatement` scaled by 1.5 (C1). It is acceptable because
    the TeX has the sentence, but a proof module should derive it and not declare it as an input.
  - The composed form of Lost (iii) is repeated in `EXprimeStatement` (s7). The two are consistent.
- **Labels.** No other Spec carries [s6:lemLost], [s6:thmMIXC] or [s6:lemJplus] (v).
- **TRIAGE §2.9.** The existing `JPlus.lean` leaves (v) to the stage-1 law, and `JPlusV.lean` fills
  that gap as TRIAGE §2.9 intends.

## 4. Hygiene
`python3 -I scripts/lint.py`: 0 findings. Each file has the module header and `@[expose] public
section`, and each docstring starts with its label and quotes the TeX. The Specs contain no `sorry`
and no stubs.

## Issues

| ID | Severity | Where | Issue | Suggested fix |
|---|---|---|---|---|
| M1 | minor | `MixC.lean` module docstring ("so the two forms are equivalent"); s6b.md T0-mixc-Bprime | The B′ form is implied by the TeX but does not imply it. The `Js` are existential and constrained only by `JPlusProps`, so a prover may choose them to *maximize* `b l ·`, not only take `∅`. The statement is therefore strictly weaker than the TeX. Its strength rests on downstream bounds of `b` being uniform over `JPlusProps` sets. `CostStatement` has the same existential shape, so the chain is consistent. | Replace "equivalent" with "implied by the TeX statement (take the chain's `J_l`)". State the design obligation explicitly: every downstream bound on `Σ b(l, J_l)` must hold uniformly for all `JPlusProps` sets. |
| M2 | cosmetic | `Lost.lean` module docstring, (K6) bullet | "true as `M_l ≥ 2^{40}`" for `l ∉ [3,R]` is not the reason: `M_l` need not be ≥ 2^40 off `[1,R]`. The bound holds because `Lost_l = ∅` and `2n/M_l^2 ≥ 0` for every real `M_l`, with x/0 = 0 in Lean. | Reword the justification. |
| M3 | minor (T0 record) | `MixCStatement`, "*any* J-consumer" | The locked `JConsumer` is a function of `(l, J)` in the context `(run, δ, stageOf ω)` only. The TeX allows the rule to depend on "everything constructed at rounds > l … (and possibly fresh randomness)". The Spec therefore quantifies over a subclass and is weaker. This is harmless for the s7 consumer, whose past (`pastOf run G δ ω l J`) is a function of `(l, J, ω)`. | Record it in the T0 table of s6b.md (T0-mixc-consumer mentions JCONS-TYPE but not this restriction). |
| M4 | minor (T0 record) | `MixCStatement`, `MixCTPVApplicableStatement` | "*any* stage-1 outcome" is restricted to `ω ∈ supp`, which is weaker than the TeX. It is justified: records off the support can violate `StageData.Coherent`, for example labels ≥ K^JS_l. It matches `CostStatement`. | None; already recorded as T0-mixc-supp. |
| C1 | cosmetic | `MixCConcStatement` | Redundant with `ConcLSumStatement` (scaled by 1.5). | A proof module should derive it from `ConcLSumStatement`, as the test does, and not stub it as a declared input. |

## Math findings
No manuscript defect found. I re-derived:
- the Lost (i) chain: 2|V(Y)|^{-2} ≤ 8M_l^{-26} ≤ M_l^{-2} via P_r ≥ P_{l-2} ≥ M_l^{13};
- (K6): at most n classed ports per round;
- (iii): Σ_{l≤R} 1/M_l ≤ 2/D* and M_l ≥ 2^40 give ≤ 4.0000000007n/D* ≤ 5.5n/D*;
- the MIX-C cost itemization;
- the TPV bullet parameters: standalone ε_Y = 2^{-5}, s_Y = s_l, COL(a) gives (ε_Y, s_Y/4), COL(e)
  needs no event.

One T0 is recorded in the structured output (it corresponds to M1 above): the B′ encoding weakens
the literal conclusion.
