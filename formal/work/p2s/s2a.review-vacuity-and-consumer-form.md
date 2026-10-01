# Clean-room review of the s2a Specs (lens: vacuity-and-consumer-form, model B)

Reviewed: `work/p2s/s2a.md`; the new Spec modules `EG/Spec/HB/HS.lean`, `EG/Spec/HB/CapRound.lean`,
`EG/Spec/HB/HBtpFacts.lean`; the test `EGTest/Spec_s2a.lean`; against `proofs/manuscript/s2.tex`
503–720 (s2:defHBtp, s2:defAncestors, s2:lemCap, s2:lemHS) and the consumers 722–790
(s2:propStructure) and 1001–1035 (s2:propExists). Defs read: `EG/Defs/HB/Round.lean`, `Run.lean`,
`SplitTree.lean` (`graft`, `leafAddrs`, `graphAtD`, `IsTauRun`, `WF`), `EG/Defs/Expander.lean`,
`EG/Defs/Graph.lean`, `EG/Defs/Gamma/Core.lean`. Consumer Specs read: `EG/Spec/HB/CapPrePart.lean`,
`Lemma14Tau.lean`, `SEP.lean` (i), `Cap.lean` (`CapGraphStatement`), `Structure.lean`
(`StructureExpStatement`), `Exists.lean` (`RoundTauTermStatement`, `RoundExistsStatement`).
The sibling review `s2a.review-fidelity-first.md` (model A) was read after my own back-translation;
I do not repeat its fidelity table except where my lens adds something. No Lean file edited;
scratch file `<scratchpad>/Vac.lean` (outside the repo).

**Verdict: approve.** All nine statements are faithful to the TeX and non-vacuous (or
intentionally definitional, and documented as such); their conclusions are in the syntactic form
their consumers need; the only Γ hypothesis is `Gamma2a`. Two remarks are worth recording
(R1: a consumer-form inaccuracy in the status note; R2: a vacuity range of the pre-part clauses
under `Gamma2a` alone), neither requires a change to a Spec.

## 1. Fidelity (back-translation, checked independently)

| Spec | Back-translation (plain mathematics) | TeX match |
|---|---|---|
| `HSStatement` | ∀ graph X, W, reals ε', s, s_W: ε' > 0, s ≥ 0, \|V(X)\| ≥ 11, X an (ε',s)-expander (Def 11, log₂ of its own vertex count), W ⊆ V(X), \|W\| ≤ \|V(X)\|/2 (real), s_W ≤ s, and \|N_X(u) ∩ W\| ≤ s_W for every u ∈ V(X)∖W ⇒ (1) \|V(X−W)\| = \|V(X)\| − \|W\| (ℕ), (2) X−W is an (ε'(log₂ z'/log₂ z)², s − s_W)-expander with z' = z − \|W\| real, (3) ε'/2 ≤ ε'(log₂ z'/log₂ z)². | exact; "on z' vertices" is (1); Def 11 of X−W uses log₂\|V(X−W)\| = log₂ z' by (1), so the constant in (2) is the TeX's. |
| `HSCorStatement` | same standing hypotheses with ε' = 2^{-5}, s_W = s/2 ⇒ V(X−W) = V(X)∖W ∧ X−W is a (2^{-6}, s/2)-expander. | exact ("spanning … of V(X)∖W" per CONVENTIONS). |
| `CapRoundStatement` | ∀ H, c, D_*: D_* ≥ 2^{117}, D_* ≤ d(H), Round.Valid H c ⇒ (1) \|𝒫_q\| ≤ M for every piece; (2) \|Z⁰_a\| ≤ M and deg_{E(a)}(v) ≤ M − 1 (ℕ) for every pre-part a and vertex v; (3) 128·s·log₂²\|𝒫_q\| ≤ τ (ℝ) for every piece; (4) 1 ≤ s; (5) for every big piece the chosen tree is a τ-run with (ε, s, τ). | (1)–(3) literal; (4)+(5)+(3) = "Lemma 14^τ applies" read as the hypotheses of `L14*Statement` (checked syntactically: `1 ≤ s`, `128 * (s : ℝ) * Real.logb 2 H.card ^ 2 ≤ τ`, `t.IsTauRun epsC s τ H`). |
| `CapRunTauStatement` | ∀ G, D_* ≥ 2^{117}, valid run, l ∈ [1,R]: (3), (4), (5) above with the run's objects. | as above; complements `CapPrePartStatement` exactly (that one omits this clause, its docstring says so). |
| `HBMCeilStatement` | ∀ d ∈ ℝ: max(2^{40}, 2^{16}·T·log₂⁴T) ≤ M(d) ≤ max(…) + 1, T = d·log₂²d. | exact (R2); stronger than per-round. |
| `HBTwoLevelStatement` | ∀ H, c: (1) leaves of the two-level tree = small pieces ∪ {q ++ b : q big piece, b leaf of τ-run(q)}; (2) leaf graph at a small piece = piece graph; (3) leaf graph at q ++ b = τ-run(q)'s graph at b rooted at 𝒫_q; (4) pre-parts = {q ++ b : … with ≥ P vertices}. | exact (R3), both sentences ("Its leaves are …", "equivalently"). |
| `HBStdStatement` | ∀ H, c, pre-part a: GC-part ∨ ¬(L1) ∨ ¬(L2) ⇒ a ∈ Std. | exact (R4). |
| `HBStep1Statement` | ∀ valid (H, c): X⁰ of distinct pre-parts edge-disjoint; E(X_a) ⊆ E(X⁰_a) for all a; an edge in the part graphs of two pre-parts forces equality. | exact (R5)(1) parenthesis. |
| `AncestorFactsStatement` | ∀ valid run: (0) ancestors = {(r,a) : r round, a round-r pre-part}; (1) V(Y) ⊆ Y⁰; (2) anc_l = ∅ for l ≤ 2; (3) fresh = ports for l ≤ 2; (4) w ∈ D_r ⟺ μ_r(w) ≥ 2. | exact (the "so"-claims and "Y⁰ ⊇ V(Y)"). |

Quantifier order, strictness (`0 < ε'` strict; all others non-strict as in the TeX), constants
(11, 2^{-5}, 2^{-6}, 128, 2^{40}, 2^{16}, 2^{117}), log base (log₂ throughout, `Real.logb 2`),
integer vs real (`M_l − 1` in ℕ with `M_l ≥ 2^{40}`; `τ_l` compared as a real; `s_l/2` real;
`|W| ≤ z/2` real) all match. No extra hypothesis beyond `Gamma2a` (which the TeX proof of
lemCap (ii) cites explicitly); no missing hypothesis.

## 2. Vacuity

Checked in the scratch file (compiles, 0 errors) and by hand.

* **Contradictory hypotheses: none.**
  - HS / HSCor: satisfiable with W = ∅ (test file, K₁₁). Also with W ≠ ∅ by hand: X = K₁₂,
    W = one vertex, s = s_W = 1, ε' = 2^{-5} (every u ∉ W has exactly one neighbour in W; K₁₂ is a
    (2^{-5},1)-expander since deleting ≤ |U| edges isolates at most one vertex from U). The
    hypotheses do not force W = ∅ or s_W = 0. A negative `sW` makes the neighbour hypothesis
    unsatisfiable (V(X)∖W ≠ ∅ as z' ≥ z/2 > 0): the statement is then vacuous, harmless (the
    TeX's "s_W ≥ 0 is forced" remark).
  - CapRound: `Gamma2a Dstar ∧ Dstar ≤ Round.d H ∧ Round.Valid H c` is not witnessed concretely
    (needs d(H) ≥ 2^{117}), but it is exactly hypotheses + conclusion of the s2b Spec
    `RoundExistsStatement` (`Gamma2a Dstar → Dstar ≤ Round.d H → ∃ c, Round.Valid H c`), and
    graphs with d(H) ≥ 2^{117} exist (K_N, N ≥ 2^{117}+1). So non-vacuity reduces to a Spec of
    the project, as the status note says. `Round.Valid` does not contain the Lemma 14^τ
    hypotheses (HB-VALID-NO-TERMINATION), so CapRound does not assume its own conclusion.
  - CapRunTau: `Run.Valid` with R = 1 satisfiable (`EGTest.HB.run1_valid`); with `Gamma2a` and
    R ≥ 1 it reduces to `ExistsRunStatement` (which needs `Gamma1core`, s2b T0-exists-gamma).
* **Trivially true conclusions (proved in scratch; all are intentional restatements).**
  - CapRound (4) `1 ≤ sOf (Round.d H)` and CapRunTau `1 ≤ run.s G l` hold for **every real d**
    with no hypothesis: `MOf d ≥ 2^{40}` always, so `LamOf d ≥ 40` and `sOf d ≥ 1`
    (`sOf_pos_all`). The conjunct is a convenience for consumers of Lemma 14^τ, not content.
  - CapRound (5) is definitionally the fourth field of `Round.Valid` (`capRound5_of_valid`,
    3 lines; `bigPieceAddrs` unfolds to the same filter). The file's docstring says so.
  - HSCor conjunct 1 `(X.deleteVerts W).verts = X.verts \ W` holds for every X, W (`hscor1`).
  - HBStep1 conjunct 2 `(Round.X H c a).edges ⊆ (Round.X0 H c a).edges` holds for every address
    without validity (`step1_2`); the validity hypothesis is needed only for conjuncts 1 and 3.
  - `HBMCeil`, `HBStd`, `AncestorFacts` are definitional (the sibling review proved them). They
    are proof obligations the blueprint (HB-EMBEDDED-CLAIMS) asked for; not vacuous, just cheap.
* **R2 — vacuity range of the pre-part clauses under `Gamma2a` alone (not a defect).**
  For d_l close to D_* = 2^{117}: P_l = ⌈λ_l^{103}⌉ = ⌈117^{103}⌉ ≈ 2^{707.6}, while
  M_l ≈ 2^{16}·T·log₂⁴T with T = 2^{117}·117² ≈ 2^{130.7}, log₂⁴T ≈ 2^{28.1}, so M_l ≈ 2^{175}.
  Hence M_l < P_l for 2^{117} ≤ d_l ≲ 2^{940} (M_l < P_l ⟺ roughly λ + 16 < 97 log₂ λ). In such a
  round every piece has |𝒫| ≤ M_l < P_l (CapRound (1)): there are no big pieces, no τ-runs and
  no pre-parts, so CapRound (2), (5), CapRunTau's big-piece clause, HBStep1, HBTwoLevel (4) and
  `HSCor`'s application are all vacuous there. The statements stay true and faithful; under the
  manuscript's standing Γ1(a) (λ_l ≥ log D_* ≥ 2^{256}, s2:propStructure proof) the range is
  never entered. Consequence for the tests: a witness of the pre-part conjuncts would need
  d_l ≳ 2^{940}, so "not checked" in `s2a.md` §Non-vacuity is the right status; suggest adding
  this reason there. (It also corroborates s2b's T0-exists-gamma: with only Γ2(a), a disjoint
  union of K_{2^{118}} has d ≥ D_*, no long cycle, all pieces small, and passes every edge
  down, so R is infinite — hence propExists/propDegRec need Γ1, which s2b already records.)

## 3. Consistency and consumer form

* Reuse: `IsExpander`, `deleteVerts`, `nbrs`, `Round.*`, `Run.*`, `STree.*`, `IsTauRun`,
  `Gamma2a`, `epsC`; the literals `(2:ℝ)^(-5:ℤ)`, `(2:ℝ)^(-6:ℤ)` are those of `Run.ancEps`
  (and `epsC` unfolds to the former). No new Defs; no duplicate of an existing [s2:lemHS] or
  (R2)–(R5) Spec (`grep -rn "\[s2:lemHS\]" EG/Spec` gives only `HS.lean`).
* Hidden hypotheses: none. Only `Gamma2a` (Γ2(a)); Γ2(b), Γ2(c), Γ1 never assumed. The
  consumer `StructureExpStatement` also assumes only `Gamma2a`; the TeX proof of
  propStructure (i) uses Γ1(a) only for "P_l ≥ 11", which already follows from Γ2(a)
  (λ_l ≥ 117 ⇒ P_l ≥ 117^{103}), so HSCor's `11 ≤ X.card` is available there. OK.
* **HSCor → `StructureExpStatement` (propStructure (i), light clause).** Instantiating
  `X = run.X0 G l a`, `W = run.guests G l a`, `s = (run.s G l : ℝ)`, HSCor's conclusion is
  `(X0.deleteVerts guests).verts = X0.verts \ guests ∧ (X0.deleteVerts guests).IsExpander 2^{-6}
  (s/2)`, which is `StructureExp`'s `(run.X G l a).verts = run.Z0 G l a \ run.guests G l a ∧
  (run.X G l a).IsExpander 2^{-6} ((run.s G l : ℝ)/2)` after unfolding `Run.X`, `Round.X`,
  `Round.Z0` — a syntactic match. Hypotheses: `(L1)` is `2·|S| ≤ |Z⁰|` in ℕ, cast to
  `(W.card:ℝ) ≤ X.card/2`; `(L2)` counts neighbours in `G'_l[Z⁰]` and transfers to `X⁰_Z` by
  `X⁰_Z ≤ G'_l[Z⁰]` (HB-L2-GRAPH / HS-APPLICATION-GRAPH); `X0.IsExpander 2^{-5} s` is the
  stopping rule of the τ-run (StructureExp's first clause). Form is right.
* **CapRunTau → Lemma 14^τ Specs (propOV, propDegRec, propStructure (ii)).** For every big
  piece q the three conjuncts are, verbatim, the three hypotheses of `L14SplitStatement`,
  `L14GlobalStatement`, `L14OVStatement`, `L14ThinStatement` with `H := run.piece G l q`,
  `s := run.s G l`, `τ := (run.tau G l : ℝ)`, `t := run.tauRun l q`; the τ inside `IsTauRun` is
  the same cast `((tauOf _ : ℕ) : ℝ)` as in `Round.Valid`, and `run.tau G l = tauOf (run.d G l)`
  = `tauOf (Round.d (run.graph G l))` definitionally. `tauRun` is read only at big pieces
  (CONVENTIONS). Form is right.
* **R1 — CapRound and propExists (status-note inaccuracy, no Spec change).** `s2a.md` says
  `CapRoundStatement` "is the form s2:propExists needs". The s2b Spec that formalizes the
  relevant sentence ("By Lemma lemCap(ii), τ_l ≥ 128 s_l log²|𝒫| for every piece, so Lemma
  14^τ(a) applies to every τ-run with every choice of witnesses"), `RoundTauTermStatement`,
  assumes only `CyclesValid ∧ IsS0Rec ∧ StopsAt` — deliberately, because the τ-runs are what
  is being constructed there — and restates `1 ≤ s_l` and the τ inequality under those partial
  hypotheses. `CapRoundStatement` assumes the full `Round.Valid`, whose fourth field presupposes
  the τ-runs; so a proof of `RoundTauTermStatement` cannot invoke `CapRoundStatement` (that
  would be circular in usage, though not in truth) and must re-derive the piece cap from
  `CapGraphStatement` + (R1) + the s = 0 stopping rule. This is fine — the piece cap
  `|𝒫| ≤ M_l` depends only on those three fields, and one Lib lemma under the partial
  hypotheses will discharge both Specs — but the status note should say that propExists
  consumes the piece cap through such a lemma (or through a future round-level "piece cap"
  Spec with the partial hypotheses), not through `CapRoundStatement`. The other consumers
  (`RoundExistsStatement`, and propOV/propDegRec at run level) do have full validity.
* Duplication across chunks: CapRound (3),(4) restricted to big pieces = the first two conjuncts
  of s2b's `RoundTauTermStatement` under weaker hypotheses; CapRound (1),(2) = `CapPrePartStatement`
  at round level. Both duplications are the intended TRIAGE §2.2 pattern (round-level statement,
  run-level corollary); no contradiction between the copies (same casts and constants).
* `AncestorFactsStatement` (0) includes `run.IsRound r ∧ …` although `run.prePartAddrs G r = ∅`
  outside rounds; redundant but harmless and closer to the TeX wording.
* `CapRoundStatement` could equivalently take `2^{117} ≤ Round.d H` (∃ D_* eliminated); the
  chosen form (`Gamma2a Dstar → Dstar ≤ Round.d H`) matches CONVENTIONS and the consumers.

## 4. Hygiene

`python3 -I scripts/lint.py`: 0 findings. Module headers (`module`, `public import`,
`@[expose] public section`), docstrings starting with the label and quoting the TeX, `.olean`s of
the three modules present and newer than the sources. No forbidden tokens, no `sorry`.

## Issues

| # | severity | location | description | suggested fix |
|---|---|---|---|---|
| I1 | minor | `work/p2s/s2a.md` §Consumers ("`CapRoundStatement` is the form s2:propExists needs") | The propExists consumer `RoundTauTermStatement` (s2b) assumes only `CyclesValid ∧ IsS0Rec ∧ StopsAt`; `CapRoundStatement` assumes `Round.Valid`, which contains the τ-run field, so it cannot be applied in the termination proof of the τ-runs (R1 above). | Reword the note: propExists uses the piece cap through a Lib lemma under the partial validity hypotheses (from `CapGraphStatement`), which then also proves `CapRoundStatement` (1); optionally record a round-level "piece cap under partial validity" Spec for P3. No change to the Specs. |
| I2 | cosmetic | `work/p2s/s2a.md` §Non-vacuity | The joint satisfiability of the pre-part conjuncts is not only "not checked": under `Gamma2a` alone with d_l ≲ 2^{940} we have M_l < P_l, so no pre-part exists (R2). | Add the reason (M_l < P_l for λ_l ≲ 940; Γ1(a) gives λ_l ≥ 2^{256}) so nobody tries to build a small witness. |
| I3 | cosmetic | `EG/Spec/HB/CapRound.lean` docstring of `CapRoundStatement` | Conjunct (4) `1 ≤ s_l` holds for every real d unconditionally (`sOf_pos_all`); the docstring presents it as one of "the remaining hypotheses of the Lemma 14^τ Specs" without saying it is free. | Documentation only (P3 can discharge it by a one-line Lib lemma `EG.HB.one_le_sOf`). |
| I4 | cosmetic | `EGTest/Spec_s2a.lean` | HS witnesses use W = ∅ only; the (s − s_W) and z' parts are not exercised. | Optional: add K₁₂ with W a singleton, s = s_W = 1 (hand-checked above). |

## Math findings

* **T1 (edge range, statements true in all uses) — s2:defHBtp (R2)/(R3) with s2:lemCap (ii).**
  For D_* ≤ d_l ≲ 2^{940} one has M_l < P_l (numbers in R2), so by lemCap (ii) every piece is
  small and the round has no τ-run, no pre-part and Std_l = ∅. Nothing in s2a is false: lemCap
  (ii), HS and the embedded claims hold (vacuously for pre-parts). It matters only for
  statements that assume Γ2(a) alone and need pre-parts or termination (propDegRec, propExists:
  the disjoint union of copies of K_{2^{118}} passes all edges down at D_* = 2^{117}); s2b already
  records this as T0-exists-gamma and gives those Specs `Gamma1core`. Optional manuscript
  action: none beyond s2b's suggested standing-assumption sentence.
* No other doubt. The HS numerics ((log z'/log z)² ≥ 1/2 ⇐ z' ≥ z/2, z ≥ 10.67; checked at
  z = 11, |W| = 5 (0.558) and z = 14, |W| = 7 (0.544)) and the cap argument (Lemma 25 needs
  m ≥ 2^{40} = 2^{30}/ε², the long-cycle bound T_l, then (i)) check out.
