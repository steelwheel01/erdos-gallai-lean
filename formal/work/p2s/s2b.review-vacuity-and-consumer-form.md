# Clean-room review of the s2b Specs (lens: vacuity-and-consumer-form, model B)

Reviewed: `work/p2s/s2b.md`; the seven new Spec modules `EG/Spec/HB/{Structure, OVRun, DegRec,
Exists, Lacunary, Tower, Parentless}.lean` (22 `…Statement` defs); the test `EGTest/Spec_s2b.lean`;
against `proofs/manuscript/s2.tex` 20–29 (standing assumption), 503–720 (s2:defHBtp,
s2:defAncestors, s2:lemCap, s2:lemHS), 722–1533 (s2:propStructure … s2:remTauConstants) and
376–400 (s2:lem14tau (a)). Defs read: `EG/Defs/HB/{Witness, SplitTree, Round, Run}.lean`,
`EG/Defs/Gamma/{Core, Full}.lean`, `EG/Defs/Main/GammaCond.lean`, `EG/Defs/Log.lean`,
`EG/Defs/Constants.lean`, `EG/Defs/Graph.lean`, `EG/Defs/Expander.lean`, `EG/Defs/Light/Stages.lean`
(`Bad`, `goodParents`, `Rt`, `Pl`, `lp`). Reused Specs read: `StructureHY`, `StructureLight`,
`OVRunK`, `LacunaryGeom`, `TowerA`, `TowerB`, `TowerBM`, `TowerBLate`, `TowerC`, `Lemma14Tau`
(`L14SplitStatement`, `L14TermStatement`), `Num/OV`. Consumer Specs read: `Light/Stages.lean`
(`EqPlStatement`), `Light/ParentRun.lean` (`MlTyStatement`, `EtaHalvingStatement`),
`Light/Setting.lean` (s5:eqLY), `Light/Expect.lean` (header), `Quot/UHsplit.lean`
(`UHsplitDetStatement`), `Quot/Cost.lean`, `Chain/MixC.lean` (headers), `Quot/JVps.lean`,
`Main/CorJVpsEG.lean`, `Quot/Pay.lean` (header). The sibling review
`s2b.review-fidelity-first.md` (model A) was read after my own back-translation; its fidelity
table is not repeated except where my lens adds something. No Lean file edited. Scratch file
`<scratchpad>/Vac2b.lean` (outside the repo; compiled with `lake env lean`, 0 errors).

**Verdict: approve.** All 22 statements are faithful to the TeX and non-vacuous (every conjunct
that is "cheap" is an intentional transcription of a TeX clause and documented); the conclusions are
in the syntactic form their consumers (s5, s6, s7, and the s2 proofs themselves) need; the only Γ
hypotheses are `Gamma2a` and `Gamma1core`, never Γ2(b),(c), never `N0Cond`. Remarks R1–R6 below
require no change to any Spec.

## 1. Fidelity (independent back-translation; only what my lens adds)

I back-translated every statement and compared with the TeX clause it quotes; the sibling review's
clause-by-clause table is correct and I agree with it. Points a fidelity table does not show:

* **Quantifier scope of the Γ hypothesis.** Every Γ-dependent Spec puts `Gamma2a Dstar` /
  `Gamma1core Dstar` *before* `run.Valid G Dstar`, with the same `Dstar` in both: the constant of
  the stopping rule is the constant assumed to satisfy Γ. That is the TeX's "`D_*` denotes the
  constant of Definition s1:defConstants(iii)" (s2.tex 24–29). No Spec quantifies a second real.
* **Round ranges.** All run-level clauses range over `Finset.Icc 1 run.R` (or `1 ≤ l ∧ l ≤ run.R`);
  "`r < R`" is `Finset.Ico 1 run.R` or `1 ≤ r ∧ r + 1 ≤ run.R`; offsets `l − 2`, `R − r`, `l − r`
  are ℕ-subtractions exactly where they are exact (`3 ≤ l`, `r ≤ l ≤ R`). No clause reads a
  guarded object (`cycles`, `prePartAddrs`, `D`, `E`, `Std`, `DupStar`, `mu`) outside `[1,R]`.
  `E_0 = run.E0 G = E(G_{R+1})` is read once, at the stopping round, as in (R0).
* **Strictness.** The three strict inequalities of the chunk are exactly the TeX's: `< d_l`
  (propDegRec), `2|E| < qP_l` (propDegRec (b)), `|E_0| < D_* n/2` (propStructure (iii)),
  `s_Y < deg` (propStructure (i)), `d_{l+1} < d_l` (propExists), `0 < |U'|` and `< |K|`
  (propExists, "`U' ≠ ∅`, `n_1, n_2 < m`"), `τ_r < …` is in `TowerC` (not new). Everything else
  is non-strict as in the TeX (`Σ ≤ 2X_R`, `≤ 1.37 n`, `≤ ε_A n`, …).
* **Integer vs real.** ℕ where the TeX compares integers (`M_{l−1} ≥ 2M_l`, `P_r ≥ 2P_{r+1}`,
  `s_l ≤ P_l`, `|D| ≤ dup`, (K4), the parentless count, `Σ|Cyc_l| ≤ n`, `|cs| ≤ |E(G)|`); ℝ where
  the TeX has a real right-hand side (`/2`, `/log P`, `ε n`, `d^2`, `x^{103}`). Casts are placed
  so that no ℕ-subtraction or ℕ-division appears in a real bound.
* **Log base.** `Real.logb 2` everywhere (`lamOf`, `LamOf`, `L_Y`, `log M`, `log P`, `log* `
  through `logIter`), `2^{x/A}` and `x^{-a}` are `Real.rpow`; the natural exponents (`^100`,
  `^103`, `^Aexp`, `^(2*Aexp)`, `^13`, `^4`, `2^(R−r)`) are `Monoid.npow`, as the TeX's integers.

## 2. Vacuity

### 2.1 Hypotheses are satisfiable (no contradiction)
* `Gamma1core`, `Gamma2a`: `EGTest/Spec_s2b.lean` (`exists_gamma1core`, `2^117`).
* `run.Valid G Dstar`: satisfiable with `R = 1` and a light part (`EGTest.HB.run1_valid`, K₃,
  `D_* = 1`), so `prePartAddrs`, `lightParts`, `Std` are not forced empty. Also with `R = 0`:
  every `G` with `d(G) < D_*` (e.g. `G` edgeless) has the empty run valid.
* Joint satisfiability of `Gamma1core Dstar ∧ run.Valid G Dstar ∧ 1 ≤ run.R` needs a graph with
  `d ≥ D_* ≥ 2^{2^{256}}` and a valid round on it: mathematically clear (K_N, N ≥ D_* + 1, plus the
  construction of s2:propExists), not checkable in Lean cheaply; it is exactly
  `ExistsRunStatement` applied to such a `G` (and `RoundExistsStatement` for the round-level
  Specs). Same status as in `Spec_s2b.lean`; correct.
* **Real content at `R = 0`.** Several run-level Specs are *not* vacuous even at `R = 0`:
  `StructurePartitionStatement` then says `E(G) = E_0` and `|E(G)| < D_* n/2`, i.e. `d_1 < D_*`
  (true, the stopping rule); `StructureVertexStatement`, `FreshStatement`,
  `ParentlessCountStatement` become `0 ≤ 2n + …`; the Tower/Lacunary/AdmissibleParent Specs have
  `1 ≤ R` or `d_1 ≥ D_*` (⇒ `R ≥ 1`) or `Y.1 + 2 ≤ Z.1` (⇒ `R ≥ 3`) and are vacuous at `R = 0` as
  the TeX intends ("so `R ≥ 1`").
* The Lacunary hypotheses on `F` are satisfiable by `F = 0` (test file) and, non-trivially, by the
  six functions of `LacunaryExamplesStatement` (under Γ1); the sequence hypotheses by any run under
  Γ1 (`LacunaryIIStatement`, first conjunct). The `η`-disjunction has three witnesses.
* `RunTerminatesStatement`: the choice-list hypothesis is satisfied by `[]` (conclusion
  `0 ≤ |E(G)|`, trivial) and by `[c1]` of the K₃ run (test file); with `Gamma1core` and a non-empty
  list it needs `d_1 ≥ D_*`, again the `ExistsRun` situation.
* **Γ2(a)-only range (not a defect; cross-reference).** Under `Gamma2a` alone, rounds with
  `2^{117} ≤ d_l ≲ 2^{940}` have `M_l < P_l` (s2a review R2), hence no big pieces and no
  pre-parts: the pre-part clauses of `StructureExpStatement`, `StructurePartitionStatement`
  (`X^0` disjointness), `OVRoundStatement` (K1)–(F11), `DegRecKindsRoundStatement` (a), (c), the
  standalone clause, and `RoundTauTermStatement` are vacuous there and the statements stay true
  (e.g. `Σ_a |Z^0_a| = 0 ≤ 1.37 n`, `|D_r| = 0`). Under the standing Γ1 (`λ_l ≥ 2^{256}`) the range
  is never entered. The kinds clause (b) is *not* vacuous there: every edge of `G_{l+1}` is then an
  edge of a small piece, and `2|E| < qP_l` for `q ≥ 1` is real content.

### 2.2 Trivially true or definitional conjuncts (proved in the scratch file; all intentional)
| Spec, conjunct | Status | Why kept |
|---|---|---|
| `StructureExp` (1) `(run.X0 G l a).verts = run.Z0 G l a` | `rfl` for every `l`, `a` | TeX "expander **on** `Z^0`" (CONVENTIONS "spanning … on Z") |
| `StructureExp` (2) `(run.X G l a).verts = Z^0 \ S` | true for every `l`, `a` (`deleteVerts_verts`) | TeX "on the light part `Z`" |
| `StructureVertex` (3) `v ∉ D_l ⇒ ≤ 1` pre-part | true for every `H`, `c`, no validity (`D = {μ ≥ 2}`) | TeX clause; the TeX proof also calls it "by definition of `D_l`" |
| `StructureVertex` (4) ports of distinct `Std` parts disjoint | true for every run, round, no validity (`ports = Z^0 \ D`) | TeX clause |
| `StructureVertex` (2b) `P_l/2 ≤ |Z^0|/2` | definitional for `a ∈ prePartAddrs` | TeX "`|Y^0| ≥ P_r`" |
| `OVRound` (K2) `Σ_{Std} ≤ Σ_{pre-parts}` | `Std ⊆ prePartAddrs` | first link of the TeX chain |
| `DegRecRound`/`DegRec` middle link `1.21P + 9s log M ≤ 6P + 9s log M + 1.2s` | true for every real `d` (casts ≥ 0) | the TeX writes this link |
| `RoundTauTerm` `1 ≤ s_l` | true for every real `d` (`M ≥ 2^{40}` ⇒ `Λ ≥ 40`) | hypothesis "`s ≥ 1`" of Lemma 14^τ, in consumer form |
| `TowerD` (3) `2^{l−r} ≤ 2^{R−r}` | trivial from `l ≤ R` | last link of the TeX chain |
| `TowerBRound` per-ancestor `Λ_r ≤ 2λ_r` (not new) | repeats the round conjunct | P4A's literal transcription |

None of these makes a Spec vacuous: each sits in a conjunction whose other conjuncts carry the
content, and all of them are literally in the TeX statement. The remaining conjuncts are
non-trivial: I checked in particular that `StructureVertex` (5) (`home_l(v) = a` for `v` in the
light part of `a`) needs `homeOrder.toFinset = prePartAddrs` from `Round.Valid` (for `v ∉ D_l` the
`find?` must hit `a`), that `OVRound` (F11)'s equality is a genuine double count (not `rfl`), and
that `ParentlessCount`'s "more precisely" clause forces `j_1(v) < ⊤` (none of the three disjuncts
holds at `⊤`, checked), which is true as `v ∈ V(Z)` with `Z` light.

### 2.3 Nothing is a false-by-junk statement
* `POf d = 0` junk (`d ≤ 1`) and `thetaGC` junk are unreachable in the Γ-Specs (`d ≥ D_* ≥ 2^{117}`)
  and harmless in the Γ-free ones (`StructureVertex`, `Fresh`, `ParentlessCount` are purely
  combinatorial in `P`).
* `logb 2 M` for `M ≥ 2`, `logb 2 P_r` with `P_r ≥ 117^{103}`, `logb 2 (M_l : ℝ)` with `M_l ≥ 2^{40}`:
  all positive where divided by.
* DegRec (b) at `q = 0` would read `0 < 0`: unreachable for valid rounds with `d ≥ D_*` under
  Γ2(a) (τ-children have `|U'| ≥ 127|U|/128 > 0` by Lemma 14^τ (a), whose hypothesis
  `τ ≥ 128 s log²|𝒫|` is lemCap (ii) under Γ2(a); `s = 0` children have `|U| ≥ 1` and
  `m − |U| ≥ m/3`; the root has `n ≥ 1` since `d ≥ D_* > 0`). This is the one place where the
  "kinds" Spec really needs `Gamma2a` besides the counts; the Spec has it. Without Γ2(a) an empty
  first child is possible (`H_out = U` when `τ` is tiny), so the hypothesis is not spurious.
* `j_0(x)`, `j_1(v)` in `WithTop ℕ`: `l ≤ j_0(x) + 1` at `j_0 = ⊤` is true (harmless; `j_0` is
  finite in the clause since `x ∈ Z^0`), checked.

## 3. Consistency and consumer form

### 3.1 Reuse, duplication, hidden hypotheses
* Reused, not restated: `CapPrePart`/`CapRunTau`/`CapRound` (propStructure (ii)), `StructureHY`,
  `StructureLight` (implied by `StructureVertex` (1): `RunHyp ⊇ run.Valid`), `OVK1`/`OVK3`,
  `LacunaryGeom`, `TowerA`/`TowerB`/`TowerBM`/`TowerBLate`/`TowerC`, `GC*`, `Origin*`.
  `grep -rn "\[s2:propExists\]\|\[s2:lemLacunary\]\|\[s2:propParentless\]\|\[s2:propDegRec\]"
  EG/Spec` gives only the s2b files (plus `LacunaryGeom`, `TowerA` for their own parts): no second
  Spec of any node. `EG/Spec/Num/OV.lean` (`NumPropOVConstStatement`) states only the numeric
  constant inequalities of the propOV proof, not (eqDupComposite); no overlap with `OVRun`.
* The one deliberate overlap: `StructurePartitionStatement` restates the pairwise disjointness of
  the part sets `E_{r(Y)}(Y)` that `StructureHYStatement` has (needed to state the displayed `⊔`
  in one place). Harmless; documented in the module docstring.
* Hypotheses: `Gamma2a` in Structure (i), (iii), OVRun/OVRound, DegRecKinds*, RoundTauTerm,
  RoundExists; `Gamma1core` in DegRec*, RunTerminates, ExistsRun, Lacunary{Mono, II, Run,
  Examples}, Tower*, AdmissibleParent; nothing in StructureVertex, RoundSteps, LacunarySeq, Fresh,
  ParentlessCount. `grep -n "Gamma2b\|Gamma2c\|Gamma1f\|N0Cond\|RunHyp" EG/Spec/HB/{the seven}`:
  empty. Γ2(b),(c) are never assumed. Each choice is the weakest the TeX proof supports (Γ1 exactly
  where propDegRec or Γ1 (a)–(d) are used), so each Spec is at least as strong as the TeX claim
  under its standing assumption.
* Universe: all run-level Specs are `Prop`-valued over `V : Type u`; `TowerStatement.{u}`,
  `LacunaryStatement.{u}` fix the universe of their `Type u` members and leave the sequence
  forms universe-free. Consumers in universe 0 or `u` can instantiate.

### 3.2 Consumer forms (syntactic match checked against the consumer Specs)
* **s5:eqPl → `ParentlessCountStatement`.** `EG.Light.Pl ω Z = V(Z) \ Rt ω Z` with
  `Rt ω Z = V(Z).filter (∃ Y ∈ goodParents ω Z.1, v ∈ V(Y))`,
  `goodParents ω l = lightParts.filter (goodParent ω Y ∧ Y.1 + 2 ≤ l)`,
  `goodParent ω Y ↔ Y ∈ lightParts ∧ ¬ demoted ∧ ¬ parentBad`, and
  `Bad ω = lightParts.filter (demoted ∨ parentBad)`. So `v ∈ Pl ω Z ↔ v ∈ V(Z) ∧ ¬ ∃ Y ∈ lightParts,
  Y ∉ Bad ω ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ V(Y)`: the Spec's filter with `Bad := Bad ω`, up to the
  propositional identity `Y ∈ lightParts ∧ Y ∉ Bad ω ↔ goodParent ω Y`. The right-hand side
  `lp ω = Σ_{Y ∈ Bad ω} |V(Y)| (R − Y.1)` is *verbatim* the Spec's `∑ Y ∈ Bad, (run.ancVerts G Y).card
  * (run.R - Y.1)` (ℕ, truncated subtraction, same as the Defs). `EqPlStatement` sums over the
  non-demoted `Z` only (a subset of `lightParts`): `Finset.sum_le_sum_of_subset`. `Bad ω` is a
  `Finset PartId` of light parts, within the Spec's "any `Finset PartId`". Form is right, and
  the RT2-I9 obligation (demoted **or** parent-bad in `Bad`) is met by the s5 Defs.
* **s5:lemParent Step 9 → `LacunaryIIStatement`.** `EtaHalvingStatement` concludes exactly
  `AntitoneOn etaCh (Set.Ici (Real.logb 2 Dstar))` and `∀ x, logb 2 Dstar ≤ x → etaCh (2^(x/Aexp))
  ≤ etaCh x / 2`: the two `F`-hypotheses of `LacunaryIIStatement`, with the same `x_0`, the same
  `(2 : ℝ) ^ (x / (Aexp : ℝ))` and the same `/ 2`. The third hypothesis (`0 ≤ F x` on the domain)
  is the consumer's to supply (`etaCh ≥ 0` there). `Gamma1 Dstar` gives `Gamma1core Dstar` by
  `And.left`. Form is right.
* **s5:lemExpect (`ε_U = 2462 (log D_*)^{-205}`) → Lacunary (ii)/(iv) with `F = x^{-205}`.**
  `LacunaryExamplesStatement` gives `HypH x_0 (x ↦ x^{-a})`, antitonicity and nonnegativity for
  `a = 205 ≥ 1/100`. `LacunaryIIStatement` wants the *halving* form `F(2^{x/A}) ≤ F(x)/2`, not
  (H); the passage is `HypH x_0 F x (2^{x/A}) (h1) (h2) le_rfl` with `h2 : x_0 ≤ 2^{x/A}` from
  `x_0 ≤ x ≤ 2^{x/A}`, the first conjunct of `LacunaryMonoStatement`. Alternatively
  `LacunaryRunStatement` takes (H) directly and gives `Σ ≤ 2F(λ_R)`, and antitonicity plus
  `x_0 ≤ λ_R` (from `Valid`) gives `≤ 2F(x_0)`. Both routes are two lines; see R1.
* **s5:eqLY (`Light/Setting.lean`) → `TowerAStatement`, `TowerDStatement`.** The consumer's
  `R − r ≤ 2 log* d_r + 2 ≤ log₂ λ_r` (real difference) is `TowerA` (ℤ, cast) and `TowerD` (1)
  `(2:ℝ)^(2 log* d_r + 2) ≤ λ_r`, converted by `Real.le_logb_iff_rpow_le` + `Real.rpow_natCast`
  (`λ_r > 0` from `d_r ≥ D_* > 1`). One-line glue; the natural-exponent form is the right primitive
  (it is what the TeX proves: `λ_r = 2^μ ≥ 2^{2 log* d_r + 2}`).
* **s5:lemParent Steps 5, 9 → `TowerBMStatement`, `TowerAStatement`** (`MlTyStatement`): not new,
  unchanged.
* **s7:thmMainProof (`CorJVpsEGStatement`) → `ExistsRunStatement`.** The consumer is
  `∀ N0 Dstar, N0Cond N0 → GammaCond N0 Dstar → ∀ (V : Type u) (G : FGraph V), fnum G.edges ≤ …`;
  `GammaCond N0 Dstar = Gamma1 Dstar ∧ Gamma2a Dstar ∧ Gamma3 N0 Dstar ∧ Gamma4 Dstar` and
  `Gamma1 = Gamma1core ∧ Gamma1f`, so `ExistsRunStatement.{u} V G Dstar h.1.1 : ∃ run, run.Valid G
  Dstar` (with `Classical.decEq V`, since the consumer has no `DecidableEq` instance; `Run.Valid`
  only needs one). The TeX (s7.tex 1526: "By Proposition s2:propExists, `G` has a valid `HB^tp`
  run") is used exactly so, and `Dstar ≤ run.d G 1` (hypothesis of `JVpsStatement`) is the
  consumer's case split `d_1 ≥ D_*` (`run.d G 1 = Round.d G` is independent of the run). Form is
  right.
* **s6/s7 (`ε_A`) → `TowerEStatement`.** `UHsplitDetStatement` has `3 * epsA Dstar * (G.card : ℝ)`;
  `Cost`, `MixC` use `EG.HB.epsA` inside `ε_1`, `ε_M`. `TowerE` gives
  `((∑ l ∈ Icc 1 R, (run.D G l).card : ℕ) : ℝ) ≤ epsA Dstar * (G.card : ℝ)` and the same for
  `∑ l, ∑ a ∈ run.Std G l, (run.hubs G l a).card`: the sums s7:lemUHsplit (iv) needs
  (`Σ_l |D_l|`, `Σ_l Σ_Z |A_Z|` over all rounds; a sum over `Icc 3 R` is bounded by the `Icc 1 R`
  sum termwise). `A_Z = run.hubs G l a = Z^0 ∩ D_l` is the Defs' name (used by `Chain/*`). Form is
  right, `epsA` is the shared Def (TOW-EPSA-DEF).
* **Inside s2: `RoundTauTermStatement` ↔ Lemma 14^τ Specs.** Its per-split clause is, symbol for
  symbol, the first conjunct of `L14TermStatement` with `H := Round.piece H c q`,
  `s := sOf (Round.d H)`, `τ := (tauOf (Round.d H) : ℝ)` (same `2 ≤ K.card → K.card ≤ H.card →
  IsWitness K epsC s U F → N = witN K U F →` prefix; `L14Term` states `1 ≤ card ∧ card < card` for
  both children, `RoundTauTerm` states `0 < |U'|` and both `< |K|` — the TeX's "`U' ≠ ∅`,
  `n_1, n_2 < m`"; `0 < |U'|` is also a conjunct of `L14SplitStatement`). Its last clause (the
  τ-run for every witness rule `W`) is *verbatim* the second conjunct of `L14TermStatement`. So a
  proof of `RoundTauTermStatement` is: the piece cap `|𝒫| ≤ M_l` from `CapGraphStatement` + (R1) +
  the `s = 0` stopping rule (not from `CapRoundStatement`, whose hypothesis `Round.Valid`
  presupposes the τ-runs; s2a review R1), then `L14TermStatement`. Consistent with the s2a design
  (TRIAGE §2.2 DR-ROUND-LOCAL, HB-VALID-NO-TERMINATION).
* **Inside s2: run level from round level.** `DegRecStatement`, `DegRecKindsStatement`,
  `OVRunStatement` are the round-level statements at `(H, c) := (run.graph G l, run.choice l)` with
  `run.Valid` supplying `Dstar ≤ run.d G l ∧ Round.Valid …` for `l ∈ Icc 1 R`; every run-level
  object unfolds to the round-level one (`run.M G l = MOf (Round.d (run.graph G l))`,
  `run.graph G (l+1) = Round.next … ` for `IsRound l`, `run.dup = Σ (run.mu − 1)` with
  `run.mu = Round.mu` on rounds, `run.mult` = the round-level filter count). Checked term by term;
  the only non-definitional step is the (F11) reindexing `(run.ancestors G).filter (Y.1 = r)` ↔
  `(run.prePartAddrs G r).image (r, ·)` (`mem_parts`).
* **`RunTerminatesStatement` / `ExistsRunStatement`.** The termination bound is on `cs.length` for
  lists that are *not* required to be valid runs (no stop clause), which is what an existence
  proof by well-founded recursion on `|E(G_l)|` needs, and `Run.mk cs` reuses the run API
  (`(Run.mk cs).graph`, `.d`, `.choice`) so no second "execution" notion exists. `ExistsRun` is in
  the exact form `∃ run : Run V, run.Valid G Dstar` that `Spec_s2a`'s and `Spec_s2b`'s non-vacuity
  notes and s7 need.

## 4. Hygiene
* `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
* `lake build EG.Spec.HB.{Structure,OVRun,DegRec,Exists,Lacunary,Tower,Parentless}`: up to date,
  success. No `sorry` in the seven files or the test file (grep). Module headers: `module`,
  `public import`, `@[expose] public section`, namespace `EG.Spec`, docstrings start with the
  manuscript label and quote the TeX.
* Scratch file compiled with `lake env lean` (LEAN_NUM_THREADS=2): 0 errors.

## 5. Remarks (no Spec change needed)

* **R1 (consumer convenience, cosmetic).** `LacunaryIIStatement` takes the TeX's halving
  hypothesis `F(2^{x/A}) ≤ F(x)/2` (faithful), while (iv) delivers (H). The bridge is the first
  conjunct of `LacunaryMonoStatement` (`x ≤ 2^{x/A}`), which the unit added for exactly this
  reason. Consumers wanting `Σ F(λ_r) ≤ 2F(x_0)` from (H) alone can also use `LacunaryRunStatement`
  + antitonicity. Fine as is.
* **R2 (status-file fix, cosmetic; agrees with sibling 4.1).** `s2b.md` "Manuscript action
  (optional): add a standing-assumption sentence to s2" — already present in v6.1 (`s2.tex`
  24–29, which even names propExists/propDegRec/Γ1). T0-exists-gamma is purely the encoding of
  that sentence; no manuscript action.
* **R3 (docstring hygiene in other units' files, cosmetic).** `TowerA.lean`, `TowerC.lean`,
  `OVRunK.lean` docstrings still say the full s2b Specs are "not written yet".
* **R4 (a proof-planning note, not a Spec issue).** Of the Γ-free Specs, `StructureVertex` (5),(6)
  and `Fresh` (1),(2),(K4) need only the home-order clause of `Round.Valid`; `ParentlessCount`
  needs (5),(6) of `StructureVertex`; `Fresh` (2) needs `Fresh` (1) at round `j_0(x)`. So these can
  be proved in the order Vertex → Fresh → ParentlessCount with no Γ and no Lemma 14^τ, as
  `EG.structureHY` was.
* **R5 (T0, agreed with the unit and the sibling).** propDegRec (b) "a leaf with `q` vertices has
  fewer than `qP_l/2` edges" is stated for the leaves with `q < P_l` (the kind-(b) leaves); for
  pre-parts (`q ≥ P_l`) the literal reading is false. Optional wording fix in the TeX.
* **R6 (status-note precision).** `s2b.md` §Non-vacuity says the Γ-Specs are non-vacuous "exactly
  when `ExistsRunStatement`/`RoundExistsStatement` hold"; more precisely their *round quantifiers*
  are non-empty exactly then, while several of them (`StructurePartition`, `StructureVertex`,
  `Fresh`, `ParentlessCount`, `RunTerminates` at `cs = []`) already have true, non-trivial
  instances at `R = 0` (§2.1). Cosmetic.

## 6. Math findings
No T1–T3 finding. Two T0 confirmations (encoding decisions already recorded by the unit):
T0-exists-gamma (`Gamma1core` on propExists; the literal statement without Γ is false, K_{2^{117}+1}
at `D_* = 2^{117}`), and propDegRec (b) restricted to `q < P_l`. Both agree with the sibling review.
