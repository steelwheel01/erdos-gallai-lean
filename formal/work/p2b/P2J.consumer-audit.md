# P2J consumer audit: is `EG.Spec.JSLCStatement` strong enough for every use?

Adversarial audit (2026-09-30) of the formal statement of Lemma JS-LC + Lemma J⁺
(`EG/Spec/Chain/JSLC.lean`, `EG/Defs/Chain/JSet.lean`) against every consumer in the manuscript
(v6.1, `proofs/manuscript/s6.tex`, `s7.tex`, `s1.tex`) and in Lean (`EG/Defs/Quot/Round.lean`,
`EG/Spec/Quot/Lift.lean`, `EG/Defs/Chain/JConsumer.lean`). Trigger: the proof `EG.jslc` uses a
simpler construction than the manuscript (cherries everywhere, first-fit groups, no `𝒮_0`/MED/EQ-LPT/
padding), which could hide a weakened statement. No Lean file of the project was edited; one scratch
file was compiled under the session scratchpad (see §5). The proof being audited is a CANDIDATE proof
(AI-reviewed only); nothing here says the conjecture is solved.

**VERDICT: sufficient**

Every conclusion of Lemma JS-LC and Lemma J⁺ that a consumer (MIX-C: s6:consOrder, s6:lemLent,
s6:thmMIXC; the s7 J-consumer: s7:consRound, lemWellDef, lemMULT, lemLift, lemCC, lemUltra, lemPay,
lemEXprime, propCost; s1 overview) actually reads is delivered by `JSLCStatement` (+ the J-independent
`JplusFactsStatement`, proved, and `StageData.Coherent`) verbatim or in a stronger form. No consumer
needs a property of the manuscript's `𝒮_0`/MED/EQ-LPT machinery; the simplified construction is
mathematically correct and gives a *better* cycle count (≤ 11.96 n/M_l + Σ_giant m_{Y,l}) than the
statement asserts. The two declared inputs are faithful to s2:lemCap (ii) and s2:lemTower (b) (with
one extra, weakening hypothesis each: Γ2(a), Γ1core, both supplied by `RunHyp`). Findings: T0 only
(encoding notes for the future MIX-C author); no T1 defects; no T2/T3.

---

## 1. Back-translation of `JSLCStatement` (plain mathematics)

For every vertex type `V`, graph `G` (n = |V(G)|), reals `N_0, D_*`, run `run`, designation `δ`,
stage-data record `S`, round `l` and edge-set family `B : Addr → Finset (Sym2 V)`:

**Hypotheses.** `RunHyp N0 D* G run` (Γ1, Γ3, N0Cond, n ≥ N_0, D_* ≤ d_1, valid run);
`IsDesignation run G δ` (δ l u ∈ anc_l(u) for every classed port u of a standalone pre-part, l ≥ 3);
`S.Coherent run G` (the s3:defCOL/s3:lemCOL(a),(b),(g) facts on the record: classes ⊆ E(H_Y),
pairwise disjoint, empty outside r(Y)+2 ≤ l ≤ R and j < K^JS_l, COL(b) path connectivity for Y with
`colB Y`, label domain); `3 ≤ l ≤ R`; for every Z ∈ Std_l: `B_Z ⊆ E_l(Z)` and every edge of B_Z has
an end in Q*_Z = Q_Z \ Lost_Z.

**Conclusion.** There exist edge sets `J`, `LentJS` and a list `D` of objects with
1. `J ⊆ ⋃_{Z∈Std_l} B_Z`;
2. `LentJS ⊆ ⋃ { LJS_{Y,l,j} : Y ∈ lendGoodAnc l (an ancestor, r(Y)+2 ≤ l, not lend-bad), j < K^JS_l }`;
3. `IsDecomp ((⋃B ∪ LentJS) \ J) D`: the objects of D are well formed (cycles: nodup vertex list of
   length ≥ 3), their edge lists are pairwise disjoint and duplicate-free, and their union is exactly
   `(⋃B ∪ LentJS) \ J`. With (1) this is literally "⋃B ∪ LentJS is partitioned into the single edges
   of J and the cycles of D";
4. every object of D is an `Obj.cycle`;
5. `|D| ≤ 126 n/M_l + 1.5 Σ_{Y ∈ ancestors, (Y,l) giant} m_{Y,l}` (in ℝ; M_l = run.M G l ∈ ℕ);
6. for every cycle of D there is one ancestor Y such that each of its edges lies in ⋃B or in some
   LJS_{Y,l,j}, j < K^JS_l;
7. `|J| ≤ jBound` = the right side of (s6:eqJbound), computed from the E_l(Z);
8. `JPlusProps run G δ S l J`: (i) exhaustive typing of J-edges (J^par / J^hub / J^fr / J^lost, each
   type including "e ∈ E_l(Z), Z ∈ Std_l"); (J1) at most one J^hub-edge of each class at each hub
   h ∈ D_l **counted over all of J** (all parts of round l), same at fresh and lost centres; (J2)
   every J-edge in E_l(Z) has an end in Q*_Z, ≤ M_l−1 J-edges of E_l(Z) at any vertex per Z, ≤ M_l−1
   J-edges at any vertex ∉ D_l, |J| ≤ n(M_l−1); (ii) ≤ M_l−1 J^fr-edges at a fresh centre.

Not in this statement, by design (TRIAGE §2.9, checked below): the hypothesis "no edge of any
LJS_{Y,l,j} has been used" (encoded as: nothing assumed, JS-LC may use the whole classes), the
J-independent J⁺ items (J3), (i)-exclusive, (iii), (iv) (`JplusFactsStatement`, proved), (v)
(stage-1 law), the sentence "J_l consists exactly of the Step-2 deletions / Steps 3–8 delete
nothing" (about the proof), and remStar.

## 2. Per-consumer table

Legend: **=** delivered verbatim; **+** delivered in a stronger/more explicit form; **−** weaker or
missing (none found). "Derivable" = follows from the Spec's conclusion plus proved Lib/Proof lemmas
(names given); the scratch file of §5 compiles the non-trivial ones.

| # | Consumer (label, s6/s7/s1 line) | What it uses from JS-LC / J⁺ | Lean source | Status |
|---|---|---|---|---|
| 1 | s6:consOrder step (3), s6.tex 702 | Applies JS-LC with B_Z := E^Q(Z); needs the input condition "B_Z ⊆ E_l(Z), each edge with an end in Q*_Z" to be the only hypothesis on B | hypothesis `∀ a ∈ Std l, B a ⊆ E l a ∧ ∀ e ∈ B a, ∃ u ∈ qs …` | = (consumer must supply it from TPV (T1) + (R5); no extra hypothesis) |
| 2 | s6:consOrder step (3), 702; Lent sets 692 | "Its cycles are output, LentJS_l is recorded, this yields J_l"; LentJS(Y) := ⋃_l (LentJS_l ∩ ⋃_j LJS_{Y,l,j}) | conclusions (1)–(4), (2) gives LentJS ⊆ ⋃ classes | = |
| 3 | s6:consOrder, hypothesis "no class edge used", 702 / MIX-C (a) 800 | The JS-LC hypothesis is discharged by COL(g) + lemLent(i) | not a hypothesis (JSLC-USED): JS-LC assumes nothing about prior use | + (JS-LC is applicable unconditionally; MIX-C must instead prove disjointness of LentJS_l from everything used before, see T0-1) |
| 4 | s6:lemLent (i), 729–740 | LentJS(Y) ⊆ Lend_Y; Lent(Y) determined by rounds ≥ r(Y)+2 | (2): LentJS ⊆ ⋃ LJS_{Y,l,j} with r(Y)+2 ≤ l; `Coherent.ljs_sub` (⊆ E(H_Y)), `own_ljs_disj` | = |
| 5 | s6:lemLent (ii), 744 | lend-bad Y ⇒ LentJS(Y) = ∅ (TeX argues via R_Y = ∅) | (2): range is `lendGoodAnc` | + (given directly) |
| 6 | s6:thmMIXC (a) "Classes used", 799 | JS-LC routes only in LJS_{Y,l,·} of ancestors of rounds ≤ l−2 | (2) | = |
| 7 | s6:thmMIXC (a) "Hypotheses of JS-LC", 800 | as row 1 and 3 | | = |
| 8 | s6:thmMIXC (b) coverage, 831 | "the cycles of step (3) decompose (⨆_Z E^Q(Z) \ J_l) ⊔ LentJS_l"; J_l ∩ E_l(Z) ⊆ E^Q(Z) | (3) with (1); `IsDecomp` = edge-disjoint, exact union | = (the Spec's `(⋃B ∪ LentJS) \ J` equals `(⋃B \ J) ∪ LentJS` once `Disjoint ⋃B LentJS`, derivable: scratch thm `disjoint_Bu_LentJS` via `EG.jslcStep7Disj`) |
| 9 | s6:thmMIXC (b), 834 | "Every edge of LentJS_l lies in exactly one class LJS_{Y,l,j}; distinct l use distinct classes" | (2) + `Coherent.ljs_disj` + `EG.structureHY` (classes of distinct ancestors disjoint, via `jslcStep7Disj`) | derivable |
| 10 | s6:thmMIXC (b), 852–854 | "every lent edge lies in at most one object"; returned/unused class edges are junk covered by the owner's device | (3) (edge-disjointness); no property of unused edges is needed from JS-LC (owner's device tolerates junk: TPV/K-RED obligation) | = |
| 11 | s6:thmMIXC (b) last item, 856 | (s6:eqJbound) "computed on the sets E_l(Z)" | (7) `jBound` reads only E_l, δ, Lost | = (kept although unused) |
| 12 | s6:thmMIXC (c) "JS-LC cycles", 788, 860 | Σ_{l≥3}(126 n/M_l + 1.5 Σ_{(Y,l) giant} m_{Y,l}) ≤ 252n/D* + 1.5 Σ_{(Y,l)} m_{Y,l}, then CONCL(iv) | (5); sum over `(run.ancestors G).filter IsGiant` ⊆ `run.ancestors G`, which is CONCL(iv)'s index set (`ConcLSumStatement`, Σ_{l∈[1,R]} Σ_{Y∈ancestors}); m ≥ 0 | = (constants 126, 1.5 verbatim; index sets compatible) |
| 13 | s6:thmMIXC (a) "Step (4)", 810; s6:defJconsumer 670–676 | "The J-consumer receives J_l, which has the properties of Lemma J⁺"; JC1/JC2 required only for such J | (8) `JPlusProps`; `JConsumer.jc1/jc2` take `JPlusProps` as hypothesis | = |
| 14 | s6:thmMIXC (b), 832 | J_l ⊔ LentJV_l disjoint: J_l ⊆ ⋃_Z E_l(Z), LentJV_l ⊆ ⋃ E(H_Y), r(Y) ≤ l−2 | `JPlusProps.subset_E` (Lib) + `structureHY` + `Coherent.ljv_eq_empty` | derivable |
| 15 | s7:consRound input, 232–234 | J_l = J^lost ∪ J^hub ∪ J^fr ∪ J^par with (J1)–(J3), (i)–(v) | (8) types + `JPlusProps.union_types` (Lib); (J3),(i)-excl,(iii),(iv) = `EG.jplusFacts` (proved); (v) = stage-1 law (not JS-LC) | = for everything JS-LC owns; (v) out of scope (T0-3) |
| 16 | s7:lemWellDef proof, 457–460 | (J2) every port ≤ M_l−1 J-edges; (ii) every fresh centre ≤ M_l−1 J^fr-edges | `J2out` (ports and fresh centres are ∉ D_l: jplusFacts (J3)); `freshCap` | = |
| 17 | s7:lemMULT proof, 580–583 | (J1) at hub h: ≤ 1 J^hub-edge per class, **aggregated over all MIX-parts** ⇒ classes of items at h with a common junction are distinct | `J1hub` (filter over the whole J; `∃ a ∈ Std l` inside `IsJhubEdge`); `JPlusProps.J1hub_ports` = the `RoundInput.Valid.J1` shape | = |
| 18 | s7:lemLift proof, 655, 707 | (J3) roles disjoint; (iii) E(H_Y) ∩ E_l(Z) = ∅ so junction edges are not items | `jplusFacts`, `structureHY`; item ∈ E_l(Z) from (8) types | = |
| 19 | s7:lemCC proof, 749–752 | (J2) |J_l| ≤ n(M_l−1) ≤ 1.37 n(M_l−1) | `J2card` (sharper form) | + |
| 20 | s7:lemUltra proof, 908–909 | (J2) Σ_h clive_h ≤ |J_l| | `J2card` | + |
| 21 | s7:lemPay proof, 984–1000 | (a1) J^lost edges join Lost_l to a port, every vertex ≤ M_l−1 J-edges; (a2) at a pooled hub v ∈ D_l: items are J^hub (J3), ≤ 1 per class (J1), each class has d_{Y,l}(v) ≥ 1 ⇒ ≤ c^agg_{v,l}; v ∉ D_l: ≤ M_l−1 (J2); (a3) ports ≤ M_l−1; (b) fresh-centre pairing | `types`/`IsJlostEdge`, `J2out`, `J1hub`, `IsJhubEdge.one_le_classDeg`, `IsJhubEdge.mem_cAggClasses` (Lib), `freshCap` | = |
| 22 | s7:lemEXprime proof, 1076–1080 | the count "≤ n classed ports" used in the proof of (J2) | run fact (`classed_disjoint`), not a J⁺ conclusion | n/a |
| 23 | s7:propCost, 1274–1345; table 1304 | MIX-C (c) with the JS-LC row 252 n/D* + 1.5 ε_CONC n; the round step is a J-consumer (lemLift (iv)) | rows 12, 13; `LiftJConsumerRunStatement` is stated for every J with `JPlusProps` (modulo `ofPast_valid`, an s7 obligation) | = |
| 24 | s7 Lean `RoundInput.Valid` (Defs/Quot/Round.lean 150–199), instantiated by `ofPast` | J-fields: hub/fr/par/lost_typed, J_sub, J1, J2, J2tot, ljv_J, lendGood_ports | all derivable from `JPlusProps` + `jplusFacts` + `Coherent` + `jslcTypes`: `union_types`, `subset_edges`, `J1hub_ports`, `degE_types_le`/`J2out`, `J2card`, `subset_E` + `structureHY` + `ljv_eq_empty`, `mem_lendGoodAnc_of_mem_qs`. Non-J fields (Hcd_ge, good_cand) are s7:lemCand's | + (the Spec provides everything `ofPast_valid` will need on the J side) |
| 25 | s1 overview 528–540, 2515 | "chaining cost ≤ 1.5 Σ m_{Y,l} plus a decaying term"; statement "restated in v6.1 as 126 n/M_l + 1.5 Σ" | (5) | = |
| 26 | s6:remStar 614–618 | no consumer; says J_l does not depend on the split | J is existential; no star split in the Spec | n/a |

Quantifier order: `δ`, `S`, `l`, `B` are universally quantified before the existential; `J`,
`LentJS`, `D` are chosen after `B`. This matches MIX-C, which fixes the past (hence B_Z = E^Q(Z))
and then applies the lemma once per round. The statement is per round; the chain over rounds is
MIX-C's (Option B′, proof-internal recursion, TRIAGE §2.9). No conjunct is vacuous under the
hypotheses: for B_Z = ∅ the conclusion holds with J = LentJS = ∅, D = [] (test
`EGTest/ProbeP2J.lean`); for non-empty B it is now a theorem (`EG.jslc`), so consistency of the
conclusion is no longer in question. Satisfiability of `RunHyp ∧ 3 ≤ l ≤ R` with E_l(Z) ≠ ∅ is
s2:propExists, outside this unit (T0-6).

## 3. The simplified construction (Steps 4–5 replaced by "cherries everywhere")

**Claim checked: "every centre is even by the aggregated parity of Step 2, so every component of
R_Y splits into cherries".** Correct. `JslcStep2Statement` (proved, `EG.jslcStep2`) gives, for every
class Y, `∀ h ∉ V(Y), Even (degE (R Y) h)` where `degE (R Y) h` counts all R_Y-edges at h over all
parts of round l (aggregated), and every edge of R_Y is hu with u ∈ Q*_Z ∩ V(Y), h ∉ V(Y). So every
vertex of R_Y outside V(Y) — hubs in several parts, fresh centres, lost centres and pseudo-hubs
(ports of another class; they are outside V(Y) by Lemma EL, `JslcCtx.el`) — has even R_Y-degree, and
its edges pair into cherries u–h–u' with u ≠ u' (distinct edges of a set). Every edge of R_Y lies in
exactly one cherry (`Cherry.exists_cherry`, `disjoint_cEdges`). Giant-ness is irrelevant to the
pairing; the manuscript restricted the cherry split to giant components only to control the count.

**Systems.** Each first-fit group is ≤ K^JS_l pairwise vertex-disjoint cherries, one per layer, all
loads 1, no padding. This is an instance of the HCC-P data (`cherrySys_valid` discharges
`HccpData.Valid`: (D) clusters disjoint and disjoint from ⋃T_j, T_j pairwise disjoint (`Coherent`
labels), (P) centres of degree 2, (JC-P) one edge-disjoint path per junction in LJS_{Y,l,j} through
T_j(Y,l), obtained from COL(b) by `EG.jslcRouting` with the multiplicity bound "a vertex lies in at
most deg_{R_Y}(v) ≤ M_l − 1 < t^JS_l pairs at each junction" (`card_pairs_le`); paths and beads are
disjoint (`jslcStep7Disj`)). HCC-P (`EG.hccp`, audited in P2E) then returns genuine edge-disjoint
cycles of G covering the group's beads ∪ used path edges. The union over all systems
(`exists_union`) reproduces the Step-7 disjointness list of the TeX verbatim. So the output cycles
are genuine cycles of G in the project's representation (`Obj.cycle`, `IsDecomp`; all edges in
`E_l(Z) ⊆ E(G)` or `LJS ⊆ E(H_Y) ⊆ E(G)`).

**Count.** Per class: #groups ≤ (Δ+1) + #cherries/K with conflict degree
Δ ≤ deg(h)+deg(u)+deg(u') ≤ m_{Y,l} + 2(M_l−1), so ≤ m_{Y,l} + 2M_l + |R_Y|/M_l². Summing over the
≤ ν_l classes, with m_{Y,l} ≤ 2γ_l for non-giant (Y,l) (`mY_le_of_not_isGiant`: all class-Y edges at
h lie in Bead_{Y,l} and in one component), ν_l ≤ 2.74n/P_{l−2}, γ_l ≤ P_{l−2}/M_l, P_{l−2} ≥ M_l^13,
Σ|R_Y| ≤ n(M_l−1): total ≤ Σ_giant m + 5.48 n/M_l + 5.48 n/M_l + n/M_l = 11.96 n/M_l + Σ_giant m
≤ 126 n/M_l + 1.5 Σ_giant m. Re-derived by hand; `step8_arith` is the Lean form. The construction
therefore proves a *stronger* bound than stated; the statement was not weakened to fit it.

**Does anything downstream need `𝒮_0`, MED, EQ-LPT or padding?** No. Lemma J⁺ is about J_l, which
is fixed by Step 2 and untouched by Steps 3–8 in both constructions ("Steps 3–8 delete nothing";
in Lean `J` is produced by `jslcStep2` and passed through unchanged, `JSLC.lean`). MED/EQ-LPT are
cited only inside the JS-LC proof (grep of s1/s4/s5/s7: only s1's audit narrative and notation
table). MIX-C and s7 read only the statement. The `𝒮_0` hypothesis checks remain proved as separate
Specs (`JslcPairsBalance/Distinct/JointMult`); they are proof-internal and now unused by `EG.jslc`
(recorded in P2J.md C3; harmless).

**Why the simpler proof is not a red flag.** The manuscript's `𝒮_0` machinery exists to charge a
non-giant class at most 5γ_l cycles; cherries charge it m_{Y,l} + 2M_l ≤ 2γ_l + 2M_l, which is
smaller. The manuscript did not use the observation m_{Y,l} ≤ 2γ_l for non-giant pairs (it is immediate
from the definition of "giant"). This is a genuine simplification of the *proof*, with the same
statement.

## 4. The two declared inputs

**`EG.Spec.CapPrePartStatement` ↔ s2:lemCap (ii) (s2.tex 635–646).** TeX: "In every round l ≤ R of a
valid HB^tp run, every s=0 piece satisfies |𝒫| ≤ M_l. Hence every round-l pre-part has |Z^0| ≤ M_l;
for every round-l part Z (light or standalone) every vertex is incident with at most M_l−1 edges of
E_l(Z); and τ_l ≥ …". Lean: `Gamma2a D* → run.Valid G D* → ∀ l ∈ [1,R], (∀ q ∈ pieceAddrs l,
|piece l q| ≤ M_l) ∧ ∀ a ∈ prePartAddrs l, |Z0 l a| ≤ M_l ∧ ∀ v, degE (E l a) v ≤ M_l − 1`. Faithful:
pieces, pre-parts (light and standalone are both pre-part addresses; E_l is indexed by pre-part) and
the degree clause are verbatim; the τ_l clause is omitted (unused by JS-LC; omitting a conclusion
weakens the input, which is safe); the added hypothesis Γ2(a) is the standing assumption the TeX proof
uses (blueprint s2b CAP-GAMMA-EXPLICIT) and is supplied by `RunHyp` (`hrh.gamma2a`). A stub with an
extra hypothesis and fewer conclusions is a weaker unproved claim than the TeX — the safe direction.
JS-LC uses only the degree clause (`JslcCtx.cap`), for standalone pre-parts.

**`EG.Spec.TowerBLateStatement` ↔ s2:lemTower (b) (s2.tex 1144–1180).** TeX: "For every valid
HB run with d_1 ≥ D_*: … For 3 ≤ l ≤ R: … P_{l−2} ≥ M_l^13 … Finally, completing (K1) of
propOV, the number ν_l of ancestors of rounds at most l−2 satisfies ν_l ≤ 2.74 n/P_{l−2} for
3 ≤ l ≤ R." Lean: `Gamma1core D* → run.Valid G D* → D* ≤ d_1 → ∀ l, 3 ≤ l → l ≤ R →
M_l^13 ≤ P_{l−2} ∧ (nuAnc l : ℝ) ≤ 2.74 n / P_{l−2}` with `nuAnc l = #{Y ∈ ancestors : r(Y)+2 ≤ l}`
(`Run.nuAnc`, all ancestors = `run.parts`, light and standalone). Faithful; only the two clauses JS-LC
uses are stated (the others omitted: safe); Γ1core is the s2 standing assumption and is `hrh.1.1`.
Plausibility check of the clause itself (not required): |V(Y)| ≥ P_{r(Y)}/2 ≥ P_{l−2}/2 and
Σ_Y |V(Y)| ≤ 1.37 n give exactly 2.74 n/P_{l−2}.

Axiom scan re-run (2026-09-30, `scripts/Axioms.lean --prefix EG EG.Proof.Chain.JSLC`): 3779
constants, 0 violations, 0 meta-scan hits; `sorryAx` reaches `EG.jslc` only through `EG.capPrePart`
and `EG.towerBLate` (plus the intermediate `exists_jslcCtx`, `jslcStep2`, `step2Hyp_of`). Confirms
P2J.md.

## 5. Scratch check (compiled, not part of the project)

`<scratchpad>/JslcConsumer.lean` (imports `EG.Spec.Chain.JSLC`, `EG.Proof.Chain.JSLCStep7`,
`EG.Lib.Chain.JSet`; `lake env lean`, exit 0, one unused-variable linter warning):
- `disjoint_Bu_LentJS`: from conjunct (2), `B_Z ⊆ E_l(Z)`, `run.Valid`, `S.Coherent` and
  `EG.jslcStep7Disj`: `Disjoint (⋃_Z B_Z) LentJS` (the blueprint's conjunct (1), P2J.md C1);
- `blueprint_form`: `IsDecomp ((E ∪ L) \ J) D`, `J ⊆ E`, `Disjoint E L` ⊢ `IsDecomp ((E \ J) ∪ L) D`
  (so the Spec's partition implies the form MIX-C (b) 831 reads);
- `JPlusProps → J ⊆ E(G) ∧ ∀ e ∈ J, ¬ e.IsDiag` (what `JConsumer.jc2`'s `IsDecomp (J ∪ L)` needs
  for the single-edge objects).

## 6. Findings

### T0 (encoding; no action on JS-LC)
- **T0-1 (JSLC-USED, hand-off to MIX-C).** The hypothesis "no edge of any class LJS_{Y,l,j} has been
  used" is dropped; JS-LC may use every edge of every lend-good round-l class. This is faithful (the
  TeX uses the hypothesis only in claim (d), "the whole class is available") and makes JS-LC
  *easier* to apply. The obligation moves to the future MIX-C Spec/proof: LentJS_l must be shown
  disjoint from everything output at rounds > l and at steps (1),(2) of round l. Available now:
  LentJS_l ⊆ E(H_Y) with r(Y) ≤ l−2 is disjoint from all E_{l'}(Z') (`structureHY`), from
  LJS_{·,l',·} for l' ≠ l and from all LJV (`Coherent.ljs_disj`, `ljs_ljv_disj`), from Own_Y
  (`own_ljs_disj`). **Not available in `StageData`/`Coherent`: the U-classes LU_{Y,l',c,·} of
  s5:lemParent** (the record has no `lu` field). The MIX-C author must obtain LU ∩ LJS = ∅ from the
  stage-1 colouring layer (`EG/Defs/Stage1/**`) or extend `Coherent`. Not a JS-LC defect; recorded so
  it is not lost.
- **T0-2.** The J⁺ clause "J_l consists exactly of the deletions of Step 2, for every choice; Steps
  3–8 delete nothing" is not encoded (about the proof). Checked: no consumer reads it (rows 15–24);
  J is existential and `JPlusProps` carries every consumed property.
- **T0-3.** J⁺ (v) (independence of edge colours) is a stage-1 law property and is neither in
  `JSLCStatement` nor in `JplusFactsStatement`. Its only consumer is s7:lemCand (via s7:consRound's
  preamble); it must come from `EG/Defs/Stage1/Law.lean`. Out of JS-LC's scope.
- **T0-4.** `RunHyp` is stronger than what the proof needs (Γ1core, valid, D_* ≤ d_1, Γ2(a));
  MIX-C has `RunHyp`, so no consumer is blocked. The Spec is correspondingly slightly weaker than a
  minimal-hypothesis form, but never weaker than the TeX (TRIAGE §2.6: JS-LC takes the s5 setting).
- **T0-5.** The single-ancestor clause (6) quantifies `Y ∈ run.ancestors G`, as the TeX ("a single
  ancestor Y"); the proof yields a lend-good one. No consumer uses (6) at all (MIX-C's coverage uses
  conjuncts (2), (3) and class disjointness instead).
- **T0-6.** Non-vacuity of the *hypotheses* with a non-trivial round (R ≥ 3, E_3(Z) ≠ ∅) is not
  exercised by any test; it is s2:propExists (deferred project-wide, P2-D MINOR-D). Since the
  statement is now proved, the only residual question about it is this satisfiability, which is not a
  JS-LC question.
- **T0-7.** The proof-internal Specs `JslcPairsBalance/Distinct/JointMult` (the `𝒮_0` hypothesis
  checks) are proved but no longer used by `EG.jslc`; `JslcJointMultStatement` also carries the
  tautological conjunct `2M−2 < 2M+2`. Harmless; the integrator may drop or keep them (they are not
  consumed outside JS-LC and are not locked statements read by anyone).

### T1 (minor; statement true in all uses)
None. (Checked candidates: the constant 126 vs the proof's 15/11.96 — the Spec states 126 as the TeX
does; `J2card` drops the vestigial 1.37 — stronger; `LentJS` index range restricted to the classes
named in the hypothesis — stronger and exactly what MIX-C (a) and lemLent (ii) read; the partition
stated as `(⋃B ∪ LentJS) \ J` rather than the blueprint's `(⋃B \ J) ∪ LentJS` — stronger, see §5.)

### T2 (major, repairable)
None found. Every consumer use has a concrete Lean source (table §2); no use requires a hypothesis
the consumer cannot supply, no quantifier is in the wrong order, no conclusion is vacuous, no edge set
is missing from the coverage, and no constant is looser than the TeX.

### T3 (fatal)
None.

## 7. Files read
`proofs/manuscript/s6.tex` 380–865 (defLending, lemLost, lemJSLC + proof, remStar, lemJplus + proof,
defJconsumer, consOrder, lemLent, thmMIXC + proof), `s7.tex` 225–262, 428–470, 558–600, 700–755,
900–915, 980–1000, 1075–1085, 1262–1345 (consRound, lemWellDef, lemMULT, lemLift, lemCC, lemUltra,
lemPay, lemEXprime, lemOneOutcome, propCost), `s2.tex` 635–660, 1144–1182 (lemCap, lemTower),
`s1.tex` 528–542, 2515–2520; `formal/work/p2/TRIAGE.md` §2.9–2.10, `blueprint_s6b.md` (JS-LC/J⁺/
J-consumer/MIX-C rows and notes), `formal/work/p2b/P2J.md`; `EG/Spec/Chain/{JSLC,JPlus,JSLCSteps,
CONCL}.lean`, `EG/Spec/HB/{CapPrePart,TowerBLate}.lean`, `EG/Defs/Chain/{JSet,JConsumer,Lending,
StageInst,Design}.lean`, `EG/Defs/Objects.lean`, `EG/Defs/Gamma/Full.lean`, `EG/Defs/HB/Run.lean`
(ancestors, nuAnc), `EG/Defs/Quot/Round.lean` 140–230, `EG/Lib/Quot/Round.lean` (ofPast_*),
`EG/Lib/Chain/JSet.lean` (lemma list), `EG/Spec/Quot/Lift.lean`, `EG/Proof/Chain/{JSLC,JSLCCtx,
JSLCGroups,JSLCSystems,JSLCAssembly,JSLCBound}.lean`, `EG/Lib/Chain/Cherry.lean`,
`EGTest/ProbeP2J.lean`.
