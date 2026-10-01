# P2 Specs, chunk s7a (s7: pools, candidates, schedule, round step, WellDef, MULT, Simple, Lift, CC, Ultra): status

Manuscript v6.1 `proofs/manuscript/s7.tex` lines 1–879 (a CANDIDATE proof, AI-reviewed only).
Blueprint `work/p2/blueprint_s7a.md`, `nodes_s7a.json`; data model TRIAGE §2.5–2.7, §2.10, §2.12;
Defs `EG/Defs/Stage1/{Pool,Law,COL}.lean`, `EG/Defs/Quot/{Cand,Schedule,Round,Xprime}.lean`
(locked, not edited); design note `work/p2d/quot.md`.

This unit ran twice. The first run (committed as WIP in `51a83b1`) wrote
`EG/Spec/Stage1/Pool.lean`, `EG/Spec/Quot/Cand.lean`, `EG/Spec/Quot/CC.lean` and
`EG/Spec/Quot/Ultra.lean` but no status note and no test file. This second run re-reviewed those four
files against the TeX and left them unchanged. It added two Spec modules for the claims inside
s7:defCand and s7:consRound, `EGTest/Spec_s7a.lean`, and this note.

Result:
* 6 Spec modules of this unit, with 14 `…Statement` defs; 2 of the modules are new in this run.
* No new Defs, no proofs, no stubs.
* No existing file of another unit was edited.
* The P1 and NUM Specs for s7a nodes are recorded below, unchanged.

Build and checks:
* `lake build EG.Spec.Quot.RoundStep EG.Spec.Quot.CandDef`: success.
* `lake build EG.Spec.Stage1.Pool EG.Spec.Quot.Cand EG.Spec.Quot.CC EG.Spec.Quot.Ultra`: success.
* `scripts/check.sh EGTest/Spec_s7a.lean`: 0 errors, 0 warnings, 0 sorry (re-checked in the fix round, with the new `ParLive` section).
* `python3 -I scripts/lint.py`: 0 findings.
* `scripts/lock.py check` was not run. It needs all of `EG` built, and the task rule forbids building `EG` as a whole.

Root imports for the orchestrator to add (I did not edit the root files):
* to `EG`: `EG.Spec.Stage1.Pool`, `EG.Spec.Quot.Cand`, `EG.Spec.Quot.CandDef`, `EG.Spec.Quot.RoundStep`, `EG.Spec.Quot.CC`, `EG.Spec.Quot.Ultra`;
* to `EGTest`: `EGTest.Spec_s7a`.

`EG.lean` currently imports none of the s7a Spec modules. The P1 modules
`EG.Spec.Quot.{Simple,MULT,WellDef,Lift}` and the NUM modules `EG.Spec.Num.{WellDef,CC}` are not
imported either. That is for their owners to settle.

## Table: label → Lean name → file → status

All Lean names are in namespace `EG.Spec`.

| label (node) | Lean name(s) | file | status |
|---|---|---|---|
| s7:defPool (definition) | Defs `EG.Stage1.{poolIdx, qPool, piPool, poolMass, poolLabelLaw, poolLaw, plabOf, poolSet, poolL, poolRound}` | `EG/Defs/Stage1/Pool.lean` | existing Defs (locked) |
| s7:defPool (embedded claims: the law is a probability distribution, the marginals, `P(v ∈ Pool_l) ≤ q_l`, disjointness, `r(w)`, independence) | `PoolLawStatement` | `EG/Spec/Stage1/Pool.lean` | **new** (this unit, run 1) |
| s7:defCand (definition) | Defs `EG.Quot.{HcdOf, Hcd, cand, candMean, JVBad}` | `EG/Defs/Quot/Cand.lean` | existing Defs (locked) |
| s7:defCand (embedded claims: `Cand_l(u) ⊆ N_{H_Y}(u) ⊆ V(Y)`; with the section setting, `Y(u) ∈ anc`, `r(u) ≤ l−2`, `u ∈ V(Y(u))`) | `CandSubsetStatement` | `EG/Spec/Quot/CandDef.lean` | **new** (this run) |
| s7:lemCand ((i)–(iv)) | `CandCountStatement` | `EG/Spec/Quot/Cand.lean` | **new** (this unit, run 1) |
| s7:defSchedule (definition, Table s7:tabSchedule) | Defs `EG.Stage1.{Outcome, law}`, `EG.Quot.{Lists, Orders, Xi, subset3Law, listsLaw, ordersLaw, roundLaw}` | `EG/Defs/Stage1/Law.lean`, `EG/Defs/Quot/Schedule.lean` | existing Defs (locked); no Spec of its own (see "defSchedule" below) |
| s7:consRound (construction) | Defs `EG.Quot.{RoundInput, RoundInput.Valid, Rules, Rules.Valid, …, Rules.MarkovEvent, Rules.xiChosen}` | `EG/Defs/Quot/Round.lean` | existing Defs (locked) |
| s7:consRound (claims in the text: rules exist and `k_h⌈Hcd/8⌉ ≥ c_h`; (c) the law of the lists; (e2) uniform independent injections; (f) the event has probability ≥ 1/2) | `RoundRulesExistStatement`, `RoundListsLawStatement`, `RoundInjectionStatement`, `RoundMarkovStatement` | `EG/Spec/Quot/RoundStep.lean` | **new** (this run) |
| s7:lemWellDef ((i)–(v)) | `WellDefParStatement`, `WellDefListsStatement`, `CuckooSDRStatement`, `WellDefE1Statement`, `WellDefE2Statement` | `EG/Spec/Quot/WellDef.lean` | existing (probe P1) |
| s7:lemWellDef (iii), numerics of the proof | `NumWellDefSDRSeriesStatement`, `NumWellDefSDRUseStatement`, `NumWellDefSDRRatioStatement`, `NumWellDefSDRConstStatement` | `EG/Spec/Num/WellDef.lean` | existing (NUM) |
| s7:lemMULT (both inequalities; the sub-layer counts; the PAR analogue of the CC preamble) | `MultStatement`, `MultSublayerStatement`, `ParMultSublayerStatement`, `MultRunStatement` | `EG/Spec/Quot/MULT.lean` | existing (probe P1) |
| s7:lemSimple | `QuotSimpleStatement` | `EG/Spec/Quot/Simple.lean` | existing (probe P1) |
| s7:lemLift ((i)–(iv), round and run level) | `LiftRolesStatement`, `LiftDecompStatement`, `LiftAccountingStatement`, `LiftJConsumerStatement`, `LiftJConsumerRunStatement` | `EG/Spec/Quot/Lift.lean` | existing (probe P1) |
| s7:lemCC ((i), (ii), (iii)) | `CCPartnerStatement`, `CCMaxStatement`, `CCCopiesStatement` | `EG/Spec/Quot/CC.lean` | **new** (this unit, run 1) |
| s7:lemCC (iii), numerics of the proof | `NumCCConstStatement`, `NumCCTwoPowStatement`, `NumCCCombineStatement` | `EG/Spec/Num/CC.lean` | existing (NUM) |
| s7:lemUltra ((i)–(iv)) | `UltraIndepStatement`, `UltraMaxStatement`, `UltraCopiesStatement`, `UltraSumStatement` | `EG/Spec/Quot/Ultra.lean` | **new** (this unit, run 1) |

`grep -rn "\[s7:<label>\]" EG/Spec` was run for all 11 labels before any file was written.

I re-read the existing P1 Specs (WellDef, MULT, Simple, Lift) against the TeX and found no
unfaithful statement. Two of them are conditional on an unstated obligation: `MultRunStatement` and
`LiftJConsumerRunStatement` take `(RoundInput.ofPast …).Valid` as a hypothesis. Hazard H1 below
covers this.

### defSchedule: why there is no Spec

The blueprint says "No Spec of its own: the schedule is an architecture decision". Each claim of the
definition and its table is covered elsewhere:
* "Four mutually independent families" is the product law `Stage1.law` (Defs). The pool family's
  independence from the other three is stated in `PoolLawStatement`.
* "ξ_l consists of mutually independent uniform variables" and "ξ_l is fresh" are definitional:
  `roundLaw` is a product of `pi`s of uniform laws, and the past is a parameter.
* Table row 1e (probability ≥ 2/3) is used only in its existence form, `OneOutcomeStage1Statement`
  (chunk s7b).
* Table row "stage 3" (≥ 1/2 − o(1)) is internal to the s4 Specs, which are label-free (TRIAGE §2.8).
* Table row "rounds" (≥ 1/2) is the new `RoundMarkovStatement`. Its existence form is
  `OneOutcomeRoundStatement` (s7b).

## Common reading (all Specs of this unit)

* **Run-level Specs** (`PoolLawStatement`, `CandCountStatement`, `CandSubsetStatement`):
  - setting: `EG.RunHyp N0 Dstar G run`, which is Γ1, Γ3, `N0Cond`, `n ≥ N_0`, `d_1 ≥ D_*` and a valid run (TRIAGE §2.6);
  - no Γ4, and no Γ2(b),(c);
  - a designation `δ` with `IsDesignation run G δ` where one is needed.
* **Stage-1 randomness.** The law is `EG.Stage1.law G run`. An outcome `ω` is read through
  `ω.pool` and through a stage-data record `Sω ω`. The hypothesis `hS` pins the record's JV-lent
  classes to those of `ω`; all other fields are free (TRIAGE §2.7; D-DES-1).
* **Round-level Specs** (`RoundStep`, `CC`, `Ultra`):
  - "for every past" is `∀ I : RoundInput V, I.Valid`, and `∀ R : Rules I, R.Valid` where rules are involved;
  - "the lists are fixed" is a parameter `L : Lists I.G I.M`;
  - `E[·|Past_l]` is taken under `roundLaw I.G I.M`;
  - `E[·|Past_l, lists]` is taken under `ordersLaw I.G` with `L` fixed (TRIAGE §2.10, SCHED-PAST-PARAMETER).
* **Notation.**
  - Colours are naturals: `κ < 3M` (PAR) and `κ < 4M` (HUB).
  - `n = |V(G)|` is `I.G.card` or `G.card`.
  - `Hcd_l` is `I.Hcd` (or `EG.Quot.Hcd run G l`), `θ^ult_l = I.thult`, `λ_{l−2} = I.lam`.
  - `log₂ = Real.logb 2`, `e = Real.exp 1`.

## New Specs: TeX statement and back-translation

### s7:defPool — `PoolLawStatement` (`EG/Spec/Stage1/Pool.lean`)

TeX (s7:defPool, the claims): "This is a probability distribution: for each `l` we have
`Σ_{r=1}^{l−2} π_{l,r} = 1−2^{−(l−2)} < 1`, and `Σ_l q_l ≤ Σ_l M_l^{−1} ≤ 2/D_* < 1` by Lemma
s2:lemTower(b). … so that `P(v ∈ Pool_l) = q_l(1−2^{−(l−2)}) ≤ q_l` for every `v`. The sets `Pool_l`
(`3 ≤ l ≤ R`) are pairwise disjoint, because every vertex has one label. For `w ∈ Pool_l` let `r(w)`
denote the unique `r` with `w ∈ Pool_{l,r}`. … They are independent of all other stage-1 data".

Back-translation. Let `D_*`, `N_0`, `G` and a run satisfy `RunHyp`. Then:
1. For every `l ≥ 3`: `Σ_{1≤r, r+2≤l} 2^{−(l−1−r)} = 1 − 2^{−(l−2)}`, and this is `< 1`.
2. `Σ_{l=3}^{R} M_l^{−2} ≤ Σ_{l=3}^{R} M_l^{−1} ≤ 2/D_* < 1`.
3. The total non-`⊥` mass `Σ_{(l,r)} q_l π_{l,r}` is `< 1`.
4. The pool-label marginal of the stage-1 law is the product law `poolLaw`.
5. For `v ∈ V(G)` and every admissible `(l,r)`: `P(plab(v) = (l,r)) = q_l π_{l,r}`, and
   `P(plab(v) = ⊥) = 1 − Σ q_l π_{l,r}`.
6. For `v ∈ V(G)` and `3 ≤ l ≤ R`: `P(v ∈ Pool_l) = q_l(1 − 2^{−(l−2)}) ≤ q_l`.
7. For every label family, `Pool_l ∩ Pool_{l'} = ∅` when `l ≠ l'`.
8. Every `w ∈ Pool_l` lies in `Pool_{l, r(w)}` with `r(w) = poolRound w`, and in no other `Pool_{l,r}`.
9. Under the stage-1 law, the pool labels are independent of the triple (colourings, zones, JS labels).

### s7:defCand — `CandSubsetStatement` (`EG/Spec/Quot/CandDef.lean`, new in this run)

TeX: "Let `u` be a classed port of round `l ≥ 3`, with class `Y := Y(u)` of round
`r := r(u) ≤ l−2`. … Since `LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y)` and `H_Y` is a graph on `V(Y)`,
automatically `Cand_l(u) ⊆ N_{H_Y}(u)` and `N_{H_Y}(u) ⊆ V(Y)`."

Section setting: "since `Y(u) ∈ anc_l(u)` we have `r(u) ≤ l−2` and `u ∈ V(Y(u))`".

Back-translation. Assume `RunHyp` and a valid designation `δ`. Let every outcome `ω` carry a stage
record whose JV-lent classes are those of `ω`. Let `l ≥ 3` and let `u` be a classed port of round
`l`. Then:
* `Y = δ(l,u)` is an ancestor;
* `1 ≤ r(Y)` and `r(Y) + 2 ≤ l`;
* `u ∈ V(Y)`;
* for every outcome `ω`: `Cand_l(u) ⊆ N_{H_Y}(u)` and `N_{H_Y}(u) ⊆ V(Y)`.

### s7:lemCand — `CandCountStatement` (`EG/Spec/Quot/Cand.lean`)

TeX: "Let `u` be a classed port of round `l ≥ 3` with class `Y` of round `r`. Then:
(i) `|Cand_l(u)|` is a sum of independent Bernoulli variables, one for each `w ∈ N_{H_Y}(u)`, each
with success probability `q_l π_{l,r} p_Y`;
(ii) its mean satisfies
`E|Cand_l(u)| = q_l π_{l,r} p_Y deg_{H_Y}(u) ≥ λ_r^{96}2^{−(l−r)}/M_l^2 ≥ 2Hcd_l`;
(iii) `P(u is JV-bad) ≤ exp(−Hcd_l/4)`;
(iv) if `u` is JV-good then `|Cand_l(u)| ≥ Hcd_l ≥ 2^{10}M_l^{10}`."

Back-translation. Same setting as `CandSubsetStatement` (`RunHyp`, valid `δ`, `hS`, `l ≥ 3`, `u` a
classed port of round `l`, `Y = δ(l,u)`, `r = r(Y)`).
* (i)
  - For every `ω`, `|Cand_l(u)| = Σ_{w ∈ N_{H_Y}(u)} 1[plab(w) = (l,r)]·1[uw ∈ LJV_{Y,l}]`.
  - These summands, as random variables indexed by `N_{H_Y}(u)`, are mutually independent under the stage-1 law.
  - Each summand equals 1 with probability `q_l π_{l,r} p_Y`.
* (ii)
  - `E|Cand_l(u)| = candMean`, where `candMean = q_l π_{l,r} p_Y deg_{H_Y}(u)` is the Defs closed form.
  - `λ_r^{96}·2^{−(l−r)}/M_l^2 ≤ candMean`.
  - `2Hcd_l ≤ λ_r^{96}·2^{−(l−r)}/M_l^2`.
* (iii) `P(JVBad) ≤ exp(−Hcd_l/4)`.
* (iv) For every stage record and every pool-label family: if `u` is not JV-bad, then
  `Hcd_l ≤ |Cand_l(u)|`. Separately, `2^{10} M_l^{10} ≤ Hcd_l`.
  The second conjunct is `EG.Spec.COLJVRow11Statement` at `l`: `Hcd_def` is `rfl`, and `l ≤ R`
  holds because a classed port exists (`classedPorts_eq_empty_of_not_isRound`). The TeX makes this
  cross-reference itself ("the line `Hcd_l ≥ 2^{10}M_l^{10}` of the table of Lemma s3:lemCOLJV").
  **For the proof unit:** derive this conjunct from `COLJVRow11Statement` (reuse its declared
  input). Do not create a second stub for it.

### s7:consRound — `RoundStep.lean` (new in this run)

**`RoundRulesExistStatement`.** TeX (*Fixed rules*): "Rules with these arguments exist, for
instance lexicographically first choices … (the greedy colouring of (b) succeeds for every order, by
part (i) of the next lemma, and a split into groups as in (c) always exists)". From (c): "This is
possible because `k_h⌈Hcd_l/8⌉ ≥ c^live_h`".

Back-translation: for every valid past,
* every non-ultra hub with `c^live_h ≥ 1` satisfies `c^live_h ≤ k_h·⌈Hcd_l/8⌉`;
* there is a choice of fixed rules satisfying `Rules.Valid`.

The argument restrictions of the TeX are the field types of `Rules`. **Proved** in
`EGTest/Spec_s7a.lean` (`roundRulesExist`) from the Lib lemmas `Rules.exists_valid` and
`RoundInput.clive_le_kh_mul_groupCap`.

**`RoundListsLawStatement`.** TeX (c): "The lists of the groups of `h` are pairwise disjoint, and,
since the groups and their numbering are functions of `Past_l` while `η_h` is independent of
`Past_l`, they form a uniformly random sequence of `k_h` pairwise disjoint `3`-subsets of `[4M_l]`.
Lists of distinct hubs are independent. For an ultra `h`, every live item `(h,u)` is its own group,
with list `ζ_{h,u}`."

Back-translation. For every valid past and every non-ultra hub `h` with `c^live_h ≥ 1`:
* for every value of the lists, the group lists `{η_h(3i), η_h(3i+1), η_h(3i+2)}` (`i < k_h`) are
  3-subsets of `{0,…,4M−1}`, pairwise disjoint;
* for every sequence `(A_i)_{i<k_h}` of pairwise disjoint 3-subsets of `{0,…,4M−1}`, the probability
  under `listsLaw` that the group lists equal `(A_i)` is `6^{k_h}/(4M)_{3k_h}`.

Moreover, for every valid rule, the maps `u ↦ list of the item (h,u)` for distinct hubs `h ∈ D_l`
are mutually independent under `listsLaw`.

**`RoundInjectionStatement`.** TeX (e2): "With `Past_l` and the lists fixed, the map `e_i ↦ w_i` is a
uniformly random injection of `E'(u)` into `Cand_l(u) \ Used(u)`, and these injections are
independent over ports".

Back-translation. For every valid past, valid rules and value `L` of the lists:
* for every port `u` and every injective `f : E'(u) → C(u) := Cand_l(u) \ Used(u)`, the probability
  under `ordersLaw` that every end `e ∈ E'(u)` receives the (e2) junction `f(e)` is
  `1/(|C(u)|)_{|E'(u)|}`;
* the junction maps `e ↦ e2Junc(e)` on `E'(u)`, indexed by the ports `u`, are mutually independent
  under `ordersLaw`.

**`RoundMarkovStatement`.** TeX (f): "this event has probability at least `1/2` given `Past_l` (each of
the two events fails with probability at most `1/4`)".

Back-translation. For every valid past and valid rules, under `roundLaw`:
* `P(copies_l > 4E copies_l) ≤ 1/4`;
* `P(pay^rd_l > 4E pay^rd_l) ≤ 1/4`;
* `P(MarkovEvent) ≥ 1/2`.

### s7:lemCC — `CC.lean`

TeX: "Let the past and the lists be fixed. Fix a PAR colour `κ` and `w ∈ Pool_l`. Condition further
on the indicators `I_x := 1[the end at x of the κ-object at x receives the junction w]` for every
port `x` carrying a PAR object of colour `κ`. Let `S_w` be the set of PAR objects of colour `κ` with
exactly one end whose junction is `w`.
(i) The partner ports `v_o` of the objects `o ∈ S_w` … are pairwise distinct. Under the
conditioning, the junctions of the partner ends are independent, and the junction of the partner end
of `o` is uniform on `(Cand_l(v_o) \ Used(v_o)) \ {w}`. In particular it equals a given `w'` with
probability at most `3/Hcd_l`.
(ii) For every integer `t ≥ 1`,
`E[max_{w'} m_κ(w,w') | Past_l, lists, (I_x)_x] ≤ t·1[S_w ≠ ∅] + 6e|S_w|/Hcd_l + 4e2^{−t}|S_w|`.
(iii) With `t := t^CC_l := ⌈2log₂M_l⌉`, …
`E[#{PAR copies} | Past_l, lists] ≤ 3M_l(t^CC_l+1)|Pool_l| + 44.7nM_l/Hcd_l + 29.8n/M_l`."

Back-translation. Fix a valid past, valid rules, lists `L`, a colour `κ < 3M` and `w ∈ Pool_l`.
Take a pattern `b` saying, for every end `(o,c)` of a `κ`-object, whether it receives the junction
`w`, and let its atom have positive probability under `ordersLaw`. Let `S_w` be the set of
`κ`-objects with exactly one end marked, and let the partner end of each be its unmarked end.
* (i) Under `ordersLaw` conditioned on the atom:
  - the partner ports are pairwise distinct;
  - the partner junctions are mutually independent;
  - for every `w'`, `P(partner junction = w') = 1/|C'|` if `w' ∈ C' := (Cand(v_o) \ Used(v_o)) \ {w}`, and `0` otherwise;
  - this probability is `≤ 3/Hcd_l`.
* (ii) Under the same conditioned law, for every `t ≥ 1`:
  `E[max_{w' ∈ Pool_l∖{w}} m_κ(w,w')] ≤ t·1[S_w ≠ ∅] + 6e|S_w|/Hcd_l + 4e·2^{−t}|S_w|`.
* (iii) For every `L`:
  `E_{ordersLaw}[#vertices of Q_l with PAR tag] ≤ 3M(t^CC+1)|Pool_l| + 44.7nM/Hcd + 29.8n/M`.

### s7:lemUltra — `Ultra.lean`

TeX: "Let the past and the lists be fixed.
(i) Let `h` be an ultra hub, `κ ∈ [4M_l]`, and let `ω_1,…,ω_N` be the junctions of the coloured hub
items of `h` of colour `κ`. These items lie at `N` distinct ports … The `ω_i` are independent, and
each is uniform on a set of size at least `Hcd_l/2`.
(ii) If `N ≥ 1` then, with `μ* := 2N/Hcd_l`, `E[max_w m_κ(h,w) | Past_l, lists] ≤ log₂N + 2eμ* + 8`.
(iii) The number of vertices of HUB sub-layers that are copies of `h` satisfies
`E[·|Past_l, lists] ≤ 4M_l(log₂c^live_h + 8) + 4e c^live_h/Hcd_l`.
(iv) Summed over all ultra hubs, the expected number of hub copies of ultra hubs, given `Past_l` and
the lists, is at most `320 nM_l^3(log₂θ^ult_l + 8)/λ_{l−2}^{95}`."

Back-translation. Fix a valid past, valid rules and lists `L`.
* (i) Let `h ∈ D_l` be ultra and `κ < 4M`. Then:
  - the coloured items of `h` of colour `κ` have pairwise distinct ports;
  - their junctions are mutually independent under `ordersLaw`;
  - for each such item `(h,u)`, `|Cand(u) \ Used(u)| ≥ Hcd/2` and its junction is uniform on that set.
* (ii) If `N ≥ 1`: `E[max_{w ∈ Pool} m_κ(h,w)] ≤ log₂N + 2e(2N/Hcd) + 8`.
* (iii) For an ultra `h`: `E[#{vertices of Q_l with HUB tag, hub side, vertex h}] ≤ 4M(log₂c_h + 8) + 4e·c_h/Hcd`.
* (iv) `E[Σ_{h ∈ D_l, c_h > θ^ult} (hub copies of h)] ≤ 320·n·M^3·(log₂θ^ult + 8)/λ^{95}`.

## Hazards and choices (T0 decisions)

1. **H1 `ofPast_valid` is not stated as a Spec** (joint s6/s7 obligation, TRIAGE §3 item 31;
   OBL-P1-1 of `work/p2b/P1.md`). The run-level Specs `MultRunStatement` and
   `LiftJConsumerRunStatement` (P1) assume `(RoundInput.ofPast …).Valid`. The following Specs of
   this unit provide some of its fields:
   * `CandSubsetStatement`: `cls_anc`, `cls_round`, `cls_mem`, and the `V(Y)` half of `ljv_in`;
   * `CandCountStatement` (iv): `good_cand`, `Hcd_ge`.

   The remaining fields come from s6:lemJplus, s2:propStructure and s2:defHBtp:
   * J1–J3, typing, `J2tot`;
   * `M_ge`;
   * `ljv_disj`, `ljv_J`, `lendGood_ports`;
   * `pool_sub`, `ports_sub`;
   * the `e ∈ E(G)` half of `ljv_in`.

   I did not write this instantiation Spec. It is not a manuscript label, and it belongs to the
   owner of s6:lemJplus / s7:thmJVps. Until it is stated and proved, the round-level Specs of this unit
   (`RoundStep`, `CC`, `Ultra`) cannot be discharged at the run level. **For the integrator:**
   keep the `ofPast_valid` instantiation Spec on the obligation list (TRIAGE §3 item 31), owned by
   the s6:lemJplus / s7:thmJVps unit.
2. **H2 (T0, CC-ATOMS; run 1).** The indicators `I_x` of Lemma CC are indexed by the ends `(o,c)`
   of the `κ`-objects, not by the ports `x`. Each such port carries exactly one `κ`-end
   (s7:lemWellDef (i), and the two ends of an object are at distinct ports), so the two families
   generate the same atoms. "Condition on `(I_x)`" is `FinDist.cond` on the atom of a value pattern
   `b` of positive probability, quantified `∀ b, ∀ hb`.
3. **H3 (T0, CAND-MEAN-DEF, inherited from the Defs).** JV-badness uses the closed form `candMean`.
   The first equality of s7:lemCand (ii), `E|Cand_l(u)| = candMean`, is the conjunct that ties
   this to the TeX's `½E|Cand_l(u)|`.
4. **H4 (T0).** s7:lemCand (iv) is stated for every stage record `S` and every pool-label family `π`.
   This is the form `good_cand` consumes, and it is stronger than the TeX's "for the outcome"
   (the claim only uses `candMean ≥ 2Hcd_l`). `Hcd_l ≥ 2^{10}M_l^{10}` is a separate conjunct,
   since it does not depend on the outcome.
5. **H5 (T0).** `PoolLawStatement` states the strict `Σ q_l π_{l,r} < 1` given by the TeX's argument,
   which is stronger than the Defs guard `≤ 1`. The sums `Σ_l` range over `3 ≤ l ≤ R`, the label
   range. s2:lemTower(b) bounds `Σ_{l ≤ R} M_l^{−1}`, which is ≥ this sum, so the chain is as in the
   TeX.
6. **H6 (T0).** `RoundListsLawStatement` numbers groups from 0: group `i` gets `{η(3i),η(3i+1),η(3i+2)}`
   (TeX 1-based `{η(3i−2),η(3i−1),η(3i)}`, Defs `listOf`). "Uniformly random sequence of disjoint
   3-subsets" is written as "each admissible sequence has probability `6^k/(4M)_{3k}`", which is the
   reciprocal of their number. The independence clause is stated for all hubs, ultra or not, and
   reads each hub's lists through `R.hubList`. That also covers "for an ultra `h` … list `ζ_{h,u}`".
7. **H7 (T0).** `RoundInjectionStatement` is stated at every port `u ∈ I.ports`. At ports without a
   live item `E'(u) = ∅`, and the claim is trivial (`(c)_0 = 1`). Independence is over the ports.
   The ends of `E'(u)` all lie at `u`, so the junction map of `u` reads only `≺_u`.
   Two degenerate cases (fix round):
   * If `|E'(u)| > |C(u)|` with `C(u) = Cand_l(u) \ Used(u)`, no injective `f : E'(u) → C(u)`
     exists, so the uniform-injection clause is vacuous at `u`, and the (e2) junctions of `u` may
     be `none`.
   * In `CCPartnerStatement` (i), the uniform clause forces `C' := C(v_o) \ {w} ≠ ∅`. `C' = ∅`
     is excluded only through `hb`, and only when `WellDefE2` holds.

   Neither Spec states that the junctions exist. That is `WellDefE2Statement` (s7:lemWellDef (v),
   `EG/Spec/Quot/WellDef.lean`, probe P1; its consequences are the Lib lemmas
   `Rules.e2Junc_some`, `Rules.junction_par_some`). So the proofs of CC (i), Ultra (i) and
   lemPay (c) must combine `RoundInjectionStatement` / `CCPartnerStatement` with
   `WellDefE2Statement`, which gives `|E'(u)| ≤ |C(u)|` and `|C(u)| ≥ Hcd_l/2`. There is no
   statement change: the TeX's (e2) sentence and Lemma CC (i) presuppose Lemma WellDef (v) in the
   same way.
8. **H8 (T0).** `RoundMarkovStatement` carries `I.Valid`, `R.Valid` although Markov needs neither.
   This keeps the TeX's scope ("given `Past_l`" for the actual past). It is the probability form of
   the existence that `Rules.xiChosen` relies on. The Defs docstring of `xiChosen` calls this "a
   Spec obligation", and the obligation is now stated.
9. **H9 (T0).** `CandCountStatement` and `CandSubsetStatement` do not assume `l ≤ R`: for `l > R`
   there are no classed ports (`Std_l = ∅`).
10. **H10 (not checked for non-vacuity).** Two sets of hypotheses are not shown satisfiable:
    * the run-level Specs (`RunHyp` plus a classed port of a round `l ≥ 3`) need a valid run with
      `R ≥ 3` and `d_1 ≥ D_*`, and there is no such concrete run in the tests;
    * an ultra hub under `I.Valid` needs more than `⌊M Hcd/7⌋ ≥ 2^{447}` live items at one hub.

    `UltraSumStatement` and `CCCopiesStatement` have only `I.Valid`, `R.Valid`, which hold on
    `EGTest.Quot.Live.I`.

    Fix round: the non-trivial CC case is now exercised. `EGTest/Spec_s7a.lean`, section
    `ParLive`, builds a valid input with one live `J^par` item `01` between two JV-good ports
    (`Pool_l = [2, 2^500)`, `Cand = Pool_l` at both ports). For every valid rule and every value
    of the lists, the PAR object has a colour `κ < 3M`, and the atom "end `false` receives
    junction `2`, end `true` does not" has positive probability, with `S_2 = {o}` and a nonempty
    partner set (`ccAtom_nontrivial`). There, `|E'(u)| = 1 ≤ |C(u)|` at both ports.
11. **H11 (scope, P1 Specs).** `LiftAccountingStatement` checks "exactly one lent class" only among
    the round-`l` JV classes of the past. This is a recorded T0 of probe P1, and I left it unchanged.

## Mathematics (re-derived, no error found)

I re-derived the following:
* **Lemma CC.** `6e·2.74 = 44.69 < 44.7` and `4e·2.74 = 29.79 < 29.8`. `2^{−t} ≤ M^{−2}` for
  `t = ⌈2log₂M⌉`. `|C(v)∖{w}| ≥ Hcd/2 − 1 ≥ Hcd/3`, which needs `Hcd ≥ 6`.
* **Ultra (ii).** `T − 1 + 2e/T ≤ log₂N + 2eμ* + 1 + 2e < log₂N + 2eμ* + 8`.
* **Ultra (iv).**
  - `g(x) = (log₂x+8)/x` is decreasing on `[1,∞)`.
  - `θ ≥ λ^{95}/(56M) − 1 ≥ λ^{95}/(57M)`, which needs `λ^{95}/M ≥ 3192`; in fact `λ^{95}/M ≥ 2^{453}`.
  - First term: `4·1.37·57 = 312.36`.
  - Second term: `4e·1.37·8 = 119.17 ≤ 119.2`.
  - `119.2/16 = 7.45 ≤ 7.5`, and `312.36 + 7.5 < 320`.
* **Uniform-sequence count.** The count `(4M)_{3k}/6^k` is correct.
* **Lemma Cand.** `(eqCandExp)` and the chain `λ_r ≥ 2^{l−r−2}` hold.

The blueprint had already checked these. There are no math findings.

## Fix round (reviews `s7a.review-fidelity-first.md`, `s7a.review-vacuity-and-consumer-form.md`)

I verified each item against the Specs, the Defs and the Lib. No statement was changed. No locked
file and no file of another unit was edited. Files edited: `EGTest/Spec_s7a.lean` (new section
`ParLive`, three more imports) and this note.

1. **H7: `|E'(u)| > |C(u)|` not recorded; existence carried only by `WellDefE2Statement`**
   (`RoundInjectionStatement`, `CCPartnerStatement`). **Fixed** (H7 extended). I checked the
   claim. If `|E'(u)| > |C(u)|` there is no injective `MapsTo` map (`card_le_card_of_injOn`), so
   the clause is vacuous, and `e2Junc` returns `none` past the end of the sorted list. Existence
   comes only from `WellDefE2Statement`.
2. **Round-level Specs conditional on `I.Valid`; `ofPast_valid` not a Spec** (TRIAGE §3 item 31).
   **Not an issue for this unit** (already recorded as H1). This is an integrator obligation, and
   H1 now asks for it explicitly. The instantiation is not a manuscript label, and its fields come
   mostly from s6:lemJplus and s2:propStructure. Writing it belongs to the s6:lemJplus / s7:thmJVps
   owner, not to this Spec chunk.
3. **Test: CC exercised only trivially** (`Live.I` has no PAR objects). **Fixed.** The new
   section `ParLive` of `EGTest/Spec_s7a.lean` does the following:
   * builds a valid input with one live `J^par` item `01` between JV-good ports `0`, `1`
     (`ParLive.I_valid`);
   * proves `ccAtom_nontrivial`: for every valid rule and every value of the lists there are a
     colour `κ < 3M` and `2 ∈ Pool_l` whose atom (end `false` gets `2`, end `true` does not) has
     positive probability, with `ccS = {o}` and a nonempty partner set. The witness order ranks
     `2` first at `o(false)` and `3` first elsewhere;
   * proves an example that `RoundInjectionStatement` has content at these ports:
     `|E'(u)| = 1 ≤ |C(u)|`.

   Still unchecked, as in H10: `RunHyp` with `R ≥ 3`, and ultra hubs, which need about `2^{447}`
   live items at one hub.
4. **`CandCountStatement` (iv), second conjunct, duplicates `COLJVRow11Statement`.** **Fixed**
   (recorded under s7:lemCand (iv) above; no Spec change). I checked it: `Hcd run G l` unfolds to
   `λ_{l−2}^{95}/(8M_l^2)`, which is `HcdOf`, and this is the right-hand side of
   `COLJVRow11Statement` at `3 ≤ l ≤ R`. `l ≤ R` follows from the classed port. The TeX makes
   the same cross-reference. Keeping the conjunct is right, because `RoundInput.Valid.Hcd_ge`
   consumes it at the Cand Spec. The proof unit must reuse the COLJV declared input and must not
   create a second stub.
5. **Uniform clauses vacuous or degenerate; consumers must combine them with
   `WellDefE2Statement`.** This duplicates item 1, together with the `C' = ∅` case of CC (i).
   **Fixed** in the same H7 extension, which names the consumers: the proofs of CC (i),
   Ultra (i) and lemPay (c).

Checks after the fix round:
* `scripts/check.sh EGTest/Spec_s7a.lean`: rc 0, 0 errors, 0 sorry;
* `python3 -I scripts/lint.py`: 0 findings.
