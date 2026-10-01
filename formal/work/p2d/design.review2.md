# Clean-room definition review, round 2: P2-D [design] (s6 interfaces)

Reviewer: clean-room definition reviewer (round 2), 2026-09-26.
Scope: `EG/Defs/Chain/{Design,Lending,JSet,JConsumer,Constants,StageInst}.lean`, their Lib API
(`EG/Lib/Chain/{Design,Lending,JSet,JConsumer,Constants,StageInst}.lean`), the tests `EGTest/Design.lean`,
`EGTest/StageInst.lean`, the design note `work/p2d/design.md` (including its "Fix round 1" section) and the
round-1 review `work/p2d/design.review1.md`. Compared against manuscript v6.1: `s6.tex` 236–262 (defDesign),
297–356 (CONC, CONC-L), 388–422 (defLending, lemLost), 441–458 (JS-LC), 618–677 (J⁺, defJconsumer), 757–812
(MIX-C); `s3.tex` 1041–1110 (defCOL), 1453–1510 (lemCOL); `s5.tex` 79–100 (defStages), 225–229 (ε_ch),
358–362 (ε_K := ε_ch); `s1.tex` 1679–1686 (ε_CONC); `s7.tex` 60–80 (JV-bad, "applies to every classed port"),
226–245 (consRound input, "Fixed rules"). Blueprints s6a (defDesign, CONC), s6b (all nodes), s7a
(RoundInput.Valid, `ofPast_valid`, ROUND-RULE-DEPENDENCE), s7b (lemPay, defXprime, propCost, thmJVps),
s5 (defStages types, epsChain); TRIAGE §1b MULT-J1, §2.7, §2.9, §2.10, §3 items 15–20, 24–28, 31 and the gate
"items 26, 27 and 31 are reviewed together". No Lean file was edited.

## Verdict: APPROVE (the five round-1 files and `StageInst` are lockable; four minor items, four cosmetic)

The round-1 MAJOR-1 (no coherence predicate, no instantiation from a stage-1 outcome) is fixed additively
and correctly: `StageData.ofOutcome` is the D-DES-1 contract as a definition, `StageData.Coherent` is a named,
reviewed bundle of exactly the stage-1 facts the s6/s7 statements read, `coherent_ofOutcome` proves it on
the support of `Stage1.law`, and `exists_coherent` shows it is not vacuous. The five original Defs files are
byte-identical to round 1 (checked: their oleans postdate the sources, and design.md says so). I re-did the
back-translation of every definition, added six Lean scratch checks (all compile), and found **no unfaithful
definition, no wrong index type, no missing field for any downstream use that can be stated today**. The one
thing that cannot be closed in this round is the TRIAGE gate itself: item 31 (`EG/Defs/Quot/Round.lean`)
does not exist yet, so the s7 side of the joint review (26 ↔ 27 ↔ 31) must be done when it lands
(MINOR-A lists exactly what to check then).

Mechanical status (re-run): `python3 -I scripts/lint.py`: 0 findings. `python3 scripts/lock.py check`:
419 locked constants, 0 violations, 216 pending (the s6 files are PENDING, as expected). Every olean of the
eleven modules and two test files is newer than its source (timestamps 13:26–14:09 UTC vs. sources
13:25–14:08). `EG.lean`/`EGTest.lean` still lack the root imports (integrator, as design.md says).

## 0. Scratch checks (this round)

File: `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/Rev2Check.lean`,
compiled with `lake env lean` against the built oleans: 0 errors, 0 warnings.

| check | content | result |
|---|---|---|
| A | **Non-vacuity beyond `∅`:** for any `J^hub`-edge `e` (`IsJhubEdge run G δ S l h Y e`) and `M_l ≥ 2`, `JPlusProps run G δ S l {e}` holds. Proved from the Defs alone (uses `eq_of_mem_E`, `E_subset_edges`). So the nine fields are mutually consistent on a nonempty `J` without a concrete run. | proved |
| B | **TPV-applicability bridge:** on a `Coherent` record, for a standalone lend-good `Z = (l,a)`, `OZ run G S l a = (run.ancGraph G (l,a)).restrictEdges (S.own (l,a))`, i.e. `O_Z` is literally the graph that `Coherent.colA_own` calls an `(ε_Z, s_Z/4)`-expander. Needs only `own_sub` and `H_Z = X^0_Z`. | proved |
| C | **MIX-C Option B′ shape** with `S := StageData.ofOutcome ω dmt dem lp`: `∀ C : JConsumer run G δ S, ∀ b : ℕ → Finset (Sym2 V) → ℝ, (∀ l J, 3 ≤ l → l ≤ R → JPlusProps … l J → ((C.out l J).1.length : ℝ) ≤ b l J) → ∃ Js, (∀ l ∈ [3,R], JPlusProps … l (Js l)) ∧ ∃ D, IsDecomp E(G) D ∧ D.length ≤ (D*/2+745+338)n + epsM D* n + (80 S.dem + 369 S.lp + 169 Σ_{l∈[1,R]} |lostRound l|) + 1.5 Σ_{l∈[1,R]} Σ_{Y∈ancestors} mY Y l + Σ_{l∈[3,R]} b l (Js l)` | type-checks |
| D | **JS-LC conclusion shape** with `S.Coherent run G → IsDesignation run G δ → 3 ≤ l → l ≤ R → (∀ a ∈ Std_l, B a ⊆ E_l(a) ∧ ∀ e ∈ B a, ∃ u ∈ qs l a, u ∈ e) → ∃ J LentJS D, J ⊆ ⋃B ∧ LentJS ⊆ ⋃_{Y∈lendGoodAnc l} ⋃_{j<KJS l} S.ljs Y l j ∧ IsDecomp ((⋃B \ J) ∪ LentJS) D ∧ (cycles only) ∧ (single ancestor per cycle) ∧ D.length ≤ 126 n/M_l + Σ_{Y giant} 1.5 mY ∧ J.card ≤ jBound l ∧ JPlusProps … l J` (the `IsGiant` filter needs `open Classical`) | type-checks |
| E | **s6:lemLost (i) event shape** over `Stage1.law`: `μ.prob {ω ∣ u ∈ lost run G δ (ofOutcome ω (dmt ω) (dem ω) (lp ω)) l a} ≤ KJS l · rhoJS l + μ.prob {ω ∣ lendBad … (δ l u)}` | type-checks |
| F | `T_j(Y,l)` and `T_{j'}(Y,l)` are disjoint for `j ≠ j'` on **every** record (the label is a function), which JS-LC Step 7 needs and which is not a `Coherent` field. | proved |

## 1. Back-translation (re-done; differences from round 1 only)

The round-1 table (design.review1.md §1) was re-checked line by line against the quoted manuscript text; I
agree with every row. Additional rows for the fix-round-1 file:

| Lean | back-translation | manuscript (quoted) | verdict |
|---|---|---|---|
| `StageData.ofOutcome ω demoted dem lp` | `colA Y := COLa (ω.cOutAt Y)`, `colB Y := COLb (ω.cOutAt Y)`, `lab := ω.labAt`, `own Y := (Own (ω.colAt Y)).edges`, `ljs Y l j := (LJS … l j).edges`, `ljv Y l := (LJV … l).edges`; `demoted`, `dem`, `lp` parameters | s6:defLending "Fix a valid run, a designation δ and a stage-1 outcome: the colourings and JS labels of Definition s3:defCOL, and the zones of Definition s5:defZones" (zones enter only through the s5 statuses, hence through the parameters) | faithful; the parameter types (`PartId → Prop`, `ℕ`, `ℕ`) match the s5 blueprint's `demoted ω run G Y : Prop`, `dem ω run G : ℕ`, `lp ω run G : ℕ` (blueprint_s5 lines 283, 293–294), so the s5 instantiation is `ofOutcome ω (S5.demoted ω run G) (S5.dem ω run G) (S5.lp ω run G)` with no cast |
| `Coherent.colB_conn` | `colB Y → ∀ l ∈ [r+2,R], ∀ j < K^JS_l, (H_Y.restrictEdges (ljs Y l j)).IsPathConnected (2^12 L_Y^4) (t^JS_l) (Tj Y l j)` | s3:lemCOL(b) "For all r+2 ≤ l ≤ R and 0 ≤ j < K^JS_l, the class LJS_{Y,l,j} is (2^12 L_Y^4, t^JS_l)-path connected through T_j(Y,l)" | faithful; identical to `Stage1.COLb` after `LJS_restrict`, `Tj_ofOutcome` |
| `Coherent.colA_own / colA_ljs / colA_ljv` | the `Own_Y`, JS-lent and JV-lent conjuncts of COL(a) | s3:lemCOL(a) "Own_Y … (ε_Y, s_Y/4)-expander on V(Y). Every lent class … (ε_Y, s_Y/(8k_lend(Y)))-expander" | faithful (a sub-bundle of `Stage1.COLa`; the `Lend_Y` and own-class conjuncts are not read by s6/s7 and are correctly omitted) |
| `own_sub`, `ljs_sub`, `ljv_sub` | every class `⊆ E(H_Y)` | s3:defCOL (i) "Every edge of H_Y … lies in Own_Y or in Lend_Y", (ii) classes are subsets of `Lend_Y` | faithful |
| `ljs_disj`, `ljv_disj`, `ljs_ljv_disj`, `own_ljs_disj`, `own_ljv_disj` | classes of one ancestor pairwise disjoint | s3:lemCOL(g) "the lent classes are pairwise edge-disjoint"; (i) Own/Lend split | faithful (holds for every outcome, not only on the support: a colouring is a function) |
| `ljs_eq_empty`, `ljv_eq_empty` | no class outside `I^JS(Y)`, `I^JV(Y)` | s3:defCOL (ii) index families; "If r ≥ R−1, all three families are empty" | faithful; support fact |
| `lab_dom`, `lab_lt` | a label `≠ ∗` sits at a site `(l,y)` with `r+2 ≤ l ≤ R`, `y ∈ V(Y)` and has value `< K^JS_l` | s3:defCOL (iv) "For every r+2 ≤ l ≤ R and every y ∈ V(Y) … lab ∈ {∗} ∪ {0,…,K^JS_l − 1}" | faithful; `lab_lt` is a support fact |

`coherent_ofOutcome` discharges all sixteen fields from `Stage1` Lib facts (`disjoint_lentClass`,
`lentClass_edges_subset_Lend`, `disjoint_Own_Lend`, `mem_lentIdx`, `idx_mem_of_mem_supp`, the JS-label support);
I read the proof and it uses `hω ∈ supp` only for `ljs_eq_empty`, `ljv_eq_empty`, `lab_lt`, as the docstring says.

## 2. JPlusProps, JConsumer, MIX-C B′ together (the TRIAGE gate, s6 side)

Re-verified against every s7 citation listed in blueprint s6b JPLUS-EXISTENTIAL and s7a/s7b:

| s7 consumer | needs | source in the s6 interface | status |
|---|---|---|---|
| consRound input, lemLift (J3) | roles `D_l`, `⋃F_Z`, `⋃Q*_Z`, `Lost_l` pairwise disjoint | six `disjoint_*` lemmas (every run) | ok |
| lemLift, lemPay (typed ends) | Jlost/Jhub/Jfr/Jpar endpoints; `J ⊆ E(G)` | the four `IsJ*Edge` + `types` + `union_types`, `subset_edges` | ok |
| lemMULT (MULT-J1), lemPay (a2) | (J1) at hubs **aggregated over all parts** | `J1hub` (filter over all of `J`); s7 shape `J1hub_ports`; `one_le_classDeg`, `mem_cAggClasses` | ok; `¬ J1hub` is the P-2 refutation target |
| lemWellDef, CC, Ultra, Pay (a1),(a3) | ≤ M−1 J-edges at every vertex outside `D_l`; `|J| ≤ n(M−1)`; (ii) | `J2out`, `J2card`, `freshCap`; lost centres are outside `D_l` (`lost_subset_classed`, `not_mem_D_of_mem_ports`) | ok |
| lemLift (iii), lemCand | port ends in `Q*_Z`, class lend-good of round `≤ l−2`, `u ∈ V(Y(u))`, `lab = ∗` | `not_lendBad_of_mem_qs`, `mem_lendGoodAnc_of_mem_qs`, `IsDesignation.{mem_ancVerts, round_add_two_le, one_le_round}`, `lab_eq_none_of_mem_qs`, `notMem_Tj_of_mem_qs` | ok |
| lemLift (iv) = JC1–JC3 | exactly the consumer predicate | `JC1`, `JC2 = IsDecomp (J ∪ L)`, `JC3_of_JC2` | ok (LIFT-JC-INTERFACE satisfied) |
| RoundInput.Valid `ljv_in`, `ljv_disj`, `ljv_J` | `LJV ⊆ E(H_Y)` inside `V(Y)`; disjoint over `Y`; disjoint from `J` | `Coherent.ljv_sub` + `FGraph.edge_verts`; s2:propStructure(iii) (run Spec) for distinct ancestors and for `E(H_Y) ∩ E_l(Z) = ∅`; `Coherent.ljv_eq_empty_of_lt` for `r(Y)+2 > l`; `E(H_Y) ⊆ E(G)` from `partGraph_le_X0`, `X0_le_graph`, `graph_le_of_le` (glue, COSMETIC-B) | ok |
| propCost COST-BRACKET | MIX-C's bracket and `XU` read the same `dem`, `lp`, `lostRound` | both read `S.dem`, `S.lp`, `lostRound run G δ S` of the same `S` (Check C) | ok by construction |
| thmJVps / MIX-C B′ | `Js`, `JPlusProps … l (Js l)`, `Σ b l (Js l)` | Check C | ok |
| lemGammaSat | `epsCONC`, `epsM` tendsto | Defs exist; tendsto lemmas are s6/s7 proof work | ok |

Nothing in `JPlusProps` is stronger than s6:lemJplus (every field is a sentence of the lemma, quoted in the
docstring), and nothing s7 reads about `J_l` is outside `JPlusProps ∪ Lib ∪ run Specs`. Check A confirms
the fields are jointly satisfiable on a nonempty `J`. `JConsumer` is exactly the TRIAGE §2.9 type
(`out : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V)`, obligations only for `3 ≤ l ≤ R` and
`JPlusProps` inputs), and the s7 "Fixed rules" paragraph (s7.tex:236–248: rules are functions of `Past_l`
and, from (d) on, of the lists) is compatible with it: the rules are internal to the s7 instance of `out`,
whose only s6-visible arguments are `(l, J_l)` in the context `(run, δ, S)`.

## 3. Edge cases (round 2)

- **Non-ancestor `Y` in `Coherent`.** `own_sub Y`, `ljs_sub`, `ljv_sub` bound the classes of a junk `Y` by
  `E(H_Y)` of a junk part graph, which may be nonempty. Harmless: every consumer ranges `Y` over
  `run.ancestors G` (`lendGoodAnc`, `anc`, `RoundInput.A`), and on the instantiation the junk colouring is
  all-`false`, so the classes are empty (`mem_lentIdx_of_mem_lentClass` handles it). Nothing to change.
- **`OZ` for a lend-good standalone `Z`** is `Own_Z` as a graph on `Z^0` and equals `H_Z.restrictEdges own`
  (Check B), so the MIX-C TPV bullet ("spanning `(2^{-5}, s_l/4)`-expander on `Z^0`") is available from
  `Coherent.colA_own` with `ancEps = 2^{-5}`, `ancS = s_l` for standalone `Z`.
- **`lost` reads `S.lab (δ l u) l u`** at `Y = δ l u ∈ anc_l(u)`, hence at a site (`l ∈ [r+2, R]`, `u ∈ V(Y)`)
  whenever `3 ≤ l ≤ R` and `IsDesignation`; on the instantiation `labAt` is `none` off sites, so no port can
  become lost through a wrong index (LEND-LAB-DOMAIN). The stage-1 review's M3 ("guard off-ancestor reads")
  is respected: `(δ l u) ∈ run.ancestors G` (`IsDesignation.mem_ancestors`), and `OZ` reads `own (l,a)` at
  `a ∈ Std_l ⊆ prePartAddrs`, an ancestor.
- **`T_j` disjointness** (Check F) holds on every record; `Coherent.Tj_eq_empty` for `j ≥ K^JS_l`.
- **`l ≤ 2`, `l > R`, `M_l = 0`, `V(G) = ∅`**: as in round 1; additionally `JPlusProps … l J → J = ∅` for
  `l > R` (from `types`, `Std_l = ∅`), and Check A needs `1 ≤ G.card`, which every `J^hub`-edge supplies.
- **`epsK` parse** re-checked against `s5.tex:225–229`: `614/D + log₂(2A·log₂(A·log₂log₂D)) / (371 (log₂log₂D)²)`;
  the Lean term is exactly this (`^ 2` binds tighter than `*`, `/` left-assoc). `epsCONC` re-checked against
  `s1.tex:1682–1684` and `s6.tex:347`: identical.

## 4. Probability laws and independence

These files still define no law. `δ` is bound before any `FinDist` (DES-DETERMINISTIC). The instantiation
`ofOutcome` reads `ω` only through `cOutAt`, `colAt`, `labAt`, whose marginals are `colLaw`/`jsLabelLaw`
(stage-1 Lib). `lemLost(i)` (Check E) will use: `labAt (δ l u) l u` is the coordinate `(Y, (l,u))` of
component (1c) with law `jsLabelLaw G run l`, so `P(≠ ∗) = M_l² · M_l^{-4}` exactly (`M_l ∈ ℕ`, v6.1 (R2)).
`lendBad` mixes (1a),(1c) of `Y` and, through `demoted`, the zones (1b): the union bound is formed on the one
joint law `Stage1.law`, as TRIAGE §2.7 requires. No weights are introduced here; nothing to check.

## 5. Findings

### MINOR-A (gate not closable yet): the s7 third of the joint review

`EG/Defs/Quot/Round.lean` (TRIAGE item 31) does not exist. The s6 side of the gate is complete (§2). When
`RoundInput`/`RoundInput.Valid`/`ofPast` are written, the reviewer of item 31 must check, against this note:
1. `RoundInput.ofPast` sets `hubs := run.D G l`, `fresh := freshCentres run G l`, `ports := qsRound run G δ S l`,
   `lost := lostRound run G δ S l`, `cls := δ l` (with `A` a nonempty type, e.g. `Option PartId` or
   `↥(run.ancestors G)` with a default — round-1 MINOR-4), `ljv Y := S.ljv Y l`, `lendGood Y := ¬ lendBad run G S Y`,
   `Jhub := Jhub run G δ S l J`, etc.;
2. every `Valid` field is discharged by the lemma named in design.md's "Interface map" (I re-derived J1 and J2
   in round 1's Check1/Check3 and they are now Lib lemmas `J1hub_ports`, `degE_types_le`);
3. `ljv_J` uses `Coherent.ljv_eq_empty_of_lt` for `r(Y)+2 > l` and propStructure(iii) otherwise, so `ofPast`
   needs no range guard on `ljv` **provided** the s7 Spec carries `S.Coherent run G` (or quantifies `ω ∈ supp`).
No change to the s6 files is expected from this; if item 31 needs a fact about `J_l` that is not in
`JPlusProps ∪ Lib`, that is a MAJOR finding against item 31's blueprint, not a reason to touch the locked s6 Defs.

### MINOR-B (gating item G-S5-1, reinforced): `epsChain` and the s5 status data

blueprint_s5 (lines 31, 547) still proposes `EG.epsChain` **as a literal copy** of the formula ("(= epsK)").
Two locked copies of one formula are a lock hazard (round-1 MINOR-3). Binding recommendation for item 20:
`noncomputable def epsChain (D : ℝ) : ℝ := EG.Chain.epsK D` (importing `EG.Defs.Chain.Constants`), or lock
both in the same batch with the `rfl` test `example : epsChain = EG.Chain.epsK := rfl` in `EGTest`.
For item 19: `demoted ω run G : PartId → Prop` (total on `PartId`; the light guard is inside `lendBad`),
`dem lp : ℕ` — these are the types `StageData.ofOutcome` takes, and blueprint_s5's `lean_shape` already has
them; keep them (a real-valued `dem`/`lp` would force a change to the locked `ofOutcome`).

### MINOR-C (lock ordering): `StageInst` is byte-tied to the unlocked Stage1 Defs

`EG/Defs/Chain/StageInst.lean` imports `EG.Defs.Stage1.Law` and states `Coherent.colB_conn` in exactly the
`Stage1.COLb` shape (`lateRounds`, `KJS`, `tJS`, `LY`). Items 15–18 are PENDING (`lock.py` lists
`Stage1/Pool.lean`, `Stage1/Zones.lean` as unlocked). Lock order: Stage1 (15–18) before `StageInst`; any change
to `Outcome.labAt`, `COLa`/`COLb`, `Own`/`LJS`/`LJV` or `jsSites` forces a re-review of `ofOutcome`/`Coherent`
(the stage-1 review approved these with minor items only, none touching these names).

### MINOR-D (residual of round-1 MINOR-1): no concrete round with `E_l(Z) ≠ ∅`

Unchanged: `run3` has `E_3 = ∅`, so the class data and J-types are tested at `0/∅/false` on the concrete
run. The fix added the abstract positive lemmas (`one_le_classDeg`, `mem_cAggClasses`, `one_le_cFresh`,
`J1hub_ports`, `degE_types_le`) and my Check A adds "a one-edge `J^hub` set satisfies `JPlusProps`". Together
these rule out a constantly-`0`/`∅`/`False` definition of `classDeg`, `cAgg`, `cFresh`, `IsJhubEdge`,
`IsJfrEdge` and a `JPlusProps` that only `∅` satisfies. A concrete three-graph run is still the only way to
test `Bead`/`IsGiant`/`alphaY` positively; I agree with deferring it (the integrator may request it as part of
P-2's test suite, where a nonempty `J` will be produced anyway).

### COSMETIC-A: TRIAGE §2.9 wording vs. D-DES-3

TRIAGE §2.9 (binding) says "Class degrees count ports, with an equivalence lemma to edge counting"; the Defs
count **edges** (literal manuscript text) and the port form is the lemma `classDeg_eq_card_ports`. Semantically
equivalent, recorded as D-DES-3; the integrator should update the TRIAGE sentence so the binding text and the
locked Def agree.

### COSMETIC-B: glue lemma `E(H_Y) ⊆ E(G)`

`Coherent.ljv_subset_edges`/`ljs_subset_edges` take `(run.ancGraph G Y).edges ⊆ G.edges` as a hypothesis. It
follows from `EG.HB.Run.partGraph_le_X0`, `X0_le_graph`, `graph_le_of_le` (all in `EG.Lib.HB.Run`); a two-line
`ancGraph_edges_subset_edges` in `EG.Lib.HB.Run` or `EG.Lib.Chain.StageInst` would let `ofPast_valid.ljv_in` and
the JC2 "of G" remark be stated without the hypothesis. Not a defect.

### COSMETIC-C: add Check B as a Lib lemma

`OZ_eq_restrictEdges` (Check B) is what MIX-C's TPV bullet needs twice (lend-good `Z`: `Own_Z` expander from
`colA_own`; lend-bad `Z`: `X^0_Z` expander from propStructure(i)). Suggest adding it to `EG/Lib/Chain/StageInst.lean`
(Lib only; no Defs change).

### COSMETIC-D: root imports

`EG.lean` and `EGTest.lean` do not yet import the eleven s6 modules and two test files (design.md lists them).

## 6. T0 readings (unchanged, confirmed)

`X_U` sums over `l ∈ [1,R]`; JC2's "of G" follows from `J ∪ LentJV ⊆ E(G)`; (J1) at fresh/lost centres stated
aggregated; the vestigial `1.37` in (J2); the "every choice / Steps 3–8 delete nothing" clause of J⁺ is not
encoded (used by nothing downstream: re-checked against s7 lines 233–245, 272–304, 459, 580–581, 961–994);
`Lost_Z` guard `3 ≤ l` literal; `O_Z` a graph on `Z^0`; ε-functions total with Real junk below `D_* ≤ 4`.
No manuscript change is needed.

## 7. Summary for the integrator

- **Lock now:** `EG/Defs/Chain/{Design,Lending,JSet,JConsumer,Constants}.lean` (unchanged since round 1, all
  round-1 items resolved or additive). **Lock after items 15–18:** `EG/Defs/Chain/StageInst.lean`.
- The s6 side of the gate "26 ↔ 27 ↔ 31" is complete; finish it when `Quot/Round.lean` exists (MINOR-A).
- Before locking item 20 (`Light/Constants.lean`): `epsChain := EG.Chain.epsK` or a locked `rfl` test (MINOR-B).
- Update TRIAGE §2.9's "count ports" sentence to match D-DES-3 (COSMETIC-A); add the two glue lemmas
  (COSMETIC-B/C) whenever `ofPast_valid` or MIX-C is written; add the root imports (COSMETIC-D).
