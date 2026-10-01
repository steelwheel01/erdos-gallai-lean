# P2J: probe P-2, part 2 (JS-LC Steps 6/7 hypothesis checks, JS-LC, J⁺). Stage 1: the statements

Unit P2J, stage 1: the Specs, the declared-input stubs, one new probe Defs file and the non-vacuity tests. The proofs
come in stage 2. This stage proves three statements that are pure assemblies of existing Lib lemmas and declared
inputs. The proof being formalized is a CANDIDATE proof of the Erdős–Gallai cycle decomposition conjecture, reviewed
only by AI; nothing here says the conjecture is solved.

Sources:
- the manuscript v6.1 `proofs/manuscript/s6.tex` 443–666 (JS-LC, remStar, J⁺), 680–865 (consOrder, lemLent, MIX-C:
  the consumer), `s2.tex` 600–760 (defAncestors, lemCap, propStructure), 821 (lemEL), 1144–1170 (lemTower);
- `work/p2/TRIAGE.md` §2.6, §2.7, §2.9, §4 (row P-2), §1a (JSLC-G-UNDEFINED);
- `work/p2/blueprint_s6b.md` / `nodes_s6b.json` (s6:lemJSLC, s6:lemJplus, s6:remStar);
- `work/p2d/design.md` (Interface map, D-DES-1…9, fix rounds 1–2);
- `work/p2b/P2E.md` (part 1: the engine, and its hand-off of the aggregated claim (c)).

## 1. Status

| file | content | state |
|---|---|---|
| `EG/Spec/Chain/JSLC.lean` | `JSLCStatement` (s6:lemJSLC + s6:lemJplus J-interface) | compiles |
| `EG/Spec/Chain/JSLCSteps.lean` | `JslcTypesStatement` (Step 1, T-avoidance), `JslcStep2Statement` (Step 2, J1 aggregated), `JslcStep7DisjStatement` (Step 7) | compiles |
| `EG/Spec/Chain/JSLCRouting.lean` | `JslcPairsBalanceStatement`, `JslcPairsDistinctStatement` (claim (a)), `JslcJointMultStatement` (claim (c)), `JslcRoutingStatement` (claim (d)) | compiles |
| `EG/Spec/Chain/JPlus.lean` | `JplusFactsStatement` (s6:lemJplus (J3), (i) exclusive, (iii), (iv)) | compiles |
| `EG/Spec/HB/CapPrePart.lean` | `CapPrePartStatement` (s2:lemCap (ii)) — declared input | compiles |
| `EG/Spec/HB/StructureHY.lean` | `StructureHYStatement` (s2:propStructure (iii), clauses used) — declared input until fix round 1, now proved | compiles |
| `EG/Spec/HB/TowerBLate.lean` | `TowerBLateStatement` (s2:lemTower (b), late clauses) — declared input | compiles |
| `EG/Proof/HB/{CapPrePart,TowerBLate}.lean` | `EG.capPrePart`, `EG.towerBLate`: DECLARED INPUT stubs (the only two declared inputs since fix round 1) | 1 `sorry` each (allowed) |
| `EG/Proof/HB/StructureHY.lean` | `EG.structureHY : StructureHYStatement` (fix round 1; was a stub) | **proved**, 0 sorry, from `run.Valid` alone |
| `EG/Proof/Chain/JPlus.lean` | `EG.jplusFacts : JplusFactsStatement` | **proved**, 0 sorry (uses `EG.structureHY`, proved in fix round 1) |
| `EG/Proof/Chain/JSLCTypes.lean` | `EG.jslcTypes : JslcTypesStatement` | **proved**, 0 sorry (uses `EG.edgeLaminarity`, Lemma EL, proved by P3A in its fix round 1) |
| `EG/Proof/Chain/JSLCStep7.lean` | `EG.jslcStep7Disj : JslcStep7DisjStatement` | **proved**, 0 sorry (uses `EG.structureHY`, proved in fix round 1) |
| `EG/Defs/Probe/P2J/PreSystem.lean` | NEW Defs: `HccpData.IsPort`, `HccpData.junctionOcc`, `HccpData.PreValid` | compiles |
| `EGTest/ProbeP2J.lean` | non-vacuity and sanity tests | compiles, 0 sorry |

Checks run:
- `lake build` of every module above (one build at a time, `LEAN_NUM_THREADS=2`);
- `scripts/check.sh` on every new file: 0 errors; the only `sorry` warnings are the three stubs;
- `python3 -I scripts/lint.py`: 0 findings;
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Chain.{JPlus,JSLCTypes,JSLCStep7}
  EG.Proof.HB.{CapPrePart,TowerBLate}` (re-run 2026-09-29 22:55, after P3A proved Lemma EL): 2394 constants,
  0 violations, 0 meta-scan hits; `sorryAx` only in the three declared-input stubs (`capPrePart`, `structureHY`,
  `towerBLate`) and in the two proved theorems that use `structureHY` (`jplusFacts`, `jslcStep7Disj`).
  `jslcTypes` is now sorry-free (Lemma EL, `EG.edgeLaminarity`, is proved in `EG/Proof/HB/EL.lean`).
- **Fix round 1 update:** `structureHY` is now proved (see "Fix round 1" at the end), so `sorryAx` occurs only in the
  two remaining stubs `capPrePart`, `towerBLate`; `jplusFacts`, `jslcStep7Disj`, `jslcTypes` are sorry-free.

Size: 1257 lines (Specs 702, stubs 78, proofs 141, probe Defs 96, tests 240).

Root imports for the orchestrator (I did not edit `EG.lean` / `EGTest.lean`):
- to `EG`: `EG.Defs.Probe.P2J.PreSystem`, `EG.Spec.HB.{CapPrePart,StructureHY,TowerBLate}`,
  `EG.Proof.HB.{CapPrePart,StructureHY,TowerBLate}`, `EG.Spec.Chain.{JSLC,JSLCSteps,JSLCRouting,JPlus}`,
  `EG.Proof.Chain.{JPlus,JSLCTypes,JSLCStep7}`;
- to `EGTest`: `EGTest.ProbeP2J`.

## 2. Nodes: manuscript label → Lean

| label | Lean statement | proof | notes |
|---|---|---|---|
| `s6:lemJSLC` | `EG.Spec.JSLCStatement` | stage 2 | v6.1 form (`1.5 Σ m`), with `JPlusProps` |
| `s6:lemJplus` (i) exhaustive, (J1), (J2), (ii) | conjunct `JPlusProps run G δ S l J` of `JSLCStatement` | stage 2 | TRIAGE §2.9: J⁺ lives inside JS-LC |
| `s6:lemJplus` (J3), (i) exclusive, (iii), (iv) | `EG.Spec.JplusFactsStatement` | **done** (`EG.jplusFacts`) | `J`-independent |
| `s6:lemJplus` (v) | — | — | stage-1 law fact (Stage1 API; TRIAGE §2.9) |
| `s6:remStar` | — | — | no content; the Spec has no star split |
| JS-LC proof, Step 1 + claim (e) (**T-avoidance**) | `EG.Spec.JslcTypesStatement` | **done** (`EG.jslcTypes`) | uses Lemma EL |
| JS-LC proof, Step 2 (+ Step 3 ¶1) (**J1 aggregated**) | `EG.Spec.JslcStep2Statement` | stage 2 | refutation target |
| JS-LC proof, claim (a), "the bijections exist" | `EG.Spec.JslcPairsBalanceStatement` | stage 2 | |
| JS-LC proof, claim (a), **distinct pair ends** | `EG.Spec.JslcPairsDistinctStatement` | stage 2 | |
| JS-LC proof, claim (c) (**joint multiplicity** `≤ 2M_l−2 < t^JS`) | `EG.Spec.JslcJointMultStatement` | stage 2 | the P2E hand-off |
| JS-LC proof, claim (d) (routing) | `EG.Spec.JslcRoutingStatement` | stage 2 | from `Coherent.colB_conn` |
| JS-LC proof, Step 7 (disjointness for HCC-P / HCCglob) | `EG.Spec.JslcStep7DisjStatement` | **done** (`EG.jslcStep7Disj`) | |

Engine nodes used from part 1 (already proved, `work/p2b/P2E.md`): `EG.med`, `EG.medExc` (MED), `EG.eqLpt`,
`EG.eqLptExists` (EQ-LPT), `EG.par`, `EG.parExists` (PAR), `EG.hccp` (HCC-P), `EG.hccGlob`, `EG.hccUnion` (HCCglob),
`EG.hccpEndMult`, `EG.jsMultNum`, `EG.jsMult_lt_tJS`.

## 3. Declared inputs

| label | Spec | stub | why |
|---|---|---|---|
| `s2:lemCap` (ii) | `EG.Spec.CapPrePartStatement` (`EG/Spec/HB/CapPrePart.lean`) | `EG.capPrePart` | JS-LC's "two facts" ("Every vertex has degree at most `M_l − 1` in every `E_l(Z)` (Lemma s2:lemCap(ii))"), Steps 2, 3, 8, and J⁺ (J2). Its proof needs Cited result s1:citLem25 (`EG.bmLemma25`, itself open) and the (R2) algebra: upstream s2, not a P-2 node. No Spec of (ii) existed (`Cap.lean` has (i), the remark and the graph-level step). |
| `s2:propStructure` (iii), clauses used (**no longer an input since fix round 1**) | `EG.Spec.StructureHYStatement` (`EG/Spec/HB/StructureHY.lean`) | none since fix round 1: `EG.structureHY` is **proved** (0 sorry) | JS-LC Step 7 ("`Lend_Y ⊆ E(H_Y) ⊆ E_r(Y)`, while beads lie in `⋃_Z E_l(Z)`. These sets are disjoint by the partition of Proposition s2:propStructure(iii)"; "`E(H_Y) ∩ E(H_{Y'}) = ∅`") and J⁺ (iii). Upstream s2 structure (needs SEP(i) through the graft); no Spec existed. |
| `s2:lemTower` (b), late clauses | `EG.Spec.TowerBLateStatement` (`EG/Spec/HB/TowerBLate.lean`) | `EG.towerBLate` | JS-LC Step 8 ("`ν_l ≤ 2.74n/P_{l−2}` (Lemma s2:lemTower(b)…). Moreover … `P_{l−2} ≥ M_l^{13}`"). Upstream (R2) algebra + (K1) of propOV. `TowerBRoundStatement` (P4A) has only the first sentence of (b). |
| `s2:lemEL` | existing `EG.Spec.ELStatement` | none: `EG.edgeLaminarity` (unit P3A) is now **proved**, 0 sorry | Step 1 (types, centres outside `V(Y)`, classes of port–port edges differ). Reused, not re-declared; no longer an input. |

Kept out of the list, on purpose:
- **s2:propStructure (iv)** (one pre-part per vertex outside `D_l`; port sets disjoint): already proved in Lib
  (`EG.Chain.eq_of_mem_Z0_of_notMem_D`, `ports_disjoint`, `classed_disjoint`).
- **s3:lemCOL (b)** (path connectivity of the JS classes) and **s3:defCOL** (classes in `E(H_Y)`, pairwise disjoint;
  `T_j` disjoint): these are fields of `StageData.Coherent` (design note fix round 1), a hypothesis of the Specs,
  discharged for every stage-1 outcome of positive weight by `EG.Chain.coherent_ofOutcome` (proved). No stub needed.
- **s1:citDef7 / s3:remMultiset / s3:lemMonotone (iii)**: built into `EG.FGraph.IsPathConnected` (indexed families
  = multisets; all families quantified). No stub.
- **Lovász path connectivity**: not cited by JS-LC or J⁺ (only through COL(b), which is a `Coherent` field).
- **s1:factAdd**: Lib (`EG.isDecomp_finset_biUnion`).
- **Greedy `(Δ+1)`-colouring (Step 5)**: not a cited result; stage 2 proves it in Lib.
- **s2:propOV**: only indirect (through lemTower(b)).

## 4. Defs used, and the new Defs file

Locked Defs used (no change): `EG.Defs.HB.Run` (`Run`, `Std`, `E`, `D`, `Z0`, `classed`, `hubs`, `fresh`,
`ancestors`, `ancVerts`, `ancGraph`, `LY`, `M`, `P`, `nuAnc`, `prePartAddrs`, `pieceAddrs`, `piece`, `Valid`);
`EG.Defs.Chain.{Design,Lending,JSet,StageInst,HCCP,Cluster}` (`Designation`, `IsDesignation`, `mY`, `IsGiant`,
`Bead`, `StageData`, `lendGoodAnc`, `Tj`, `qs`, `ret`, `freshCentres`, `qsRound`, `IsJ*Edge`, `jBound`,
`JPlusProps`, `StageData.Coherent`, `HccpData`, `layP`, `pexc`, `demMinus`, `demPlus`, `Phi`, `succ`);
`EG.Defs.Stage1.COL` (`KJS`, `tJS`, `lateRounds`); `EG.Defs.Gamma.{Core,Full}` (`Gamma2a`, `Gamma1core`, `RunHyp`);
`EG.Defs.Objects` (`Obj`, `IsDecomp`); `EG.Defs.Graph` (`degE`); `EG.Defs.Walk` (`IsPathBetween`, `IsThrough`,
`pathLength`, `walkEdges`).

**New Defs file** `EG/Defs/Probe/P2J/PreSystem.lean` (module, `@[expose] public section`, namespace
`EG.Chain.HccpData`; it does not change the locked `HccpData`):
- `HccpData.IsPort S u := ∃ i, u ∈ (S.K i).ports` ("a port of the system");
- `HccpData.junctionOcc S j u := if h : j < S.k then [u ∈ LayP_j]·dem⁻(u) + [u ∈ LayP_{j+1}]·dem⁺(u) else 0`: the
  number of junction-`j` pairs of the system containing `u` (Step 6's definition, quoted in the file; for `k = 1`
  it equals `exc⁻ + exc⁺` since `pad ≡ 0`, which is the `X^out`/`X^in` clause);
- `HccpData.PreValid S G`: the fields of the locked `HccpData.Valid` other than those of (JC-P), with the same names
  and quoted text (`k_pos`, `adm`, `beads_G`, `T_disj`, `pad_k1`, `D_KK`, `D_KT`, `parityClean`).

Why it is needed: in JS-LC the systems exist (Steps 4–5) **before** their path families (routing, Step 6), and the
Step-6 checks ("the bijections exist", distinct ends, joint multiplicity) are about that state. `HccpData.Valid`
includes (JC-P), which mentions the paths, so it cannot express the pre-routing state. `PreValid` is the literal
subset; `Valid G → PreValid G` field by field (checked in the tests for `S1`, `S2`).

## 5. Back-translation: each Spec next to its TeX

### `JSLCStatement` [s6:lemJSLC] + [s6:lemJplus]
TeX (s6.tex 443–458): "Fix a valid run, a designation `δ`, a stage-1 outcome with its stage-2 data (Definition
s6:defLending), and a round `3 ≤ l ≤ R`. For every `Z ∈ Std_l` let `B_Z ⊆ E_l(Z)` be a set of edges, each of which
has an end in `Q*_Z`. … Hypothesis: no edge of any class `LJS_{Y,l,j}` (`0 ≤ j < K^JS_l`, `Y` a lend-good ancestor of
a round `≤ l−2`) has been used. Then there are a set `J_l ⊆ ⋃_Z B_Z` and a set `LentJS_l ⊆ ⋃_{Y,j} LJS_{Y,l,j}`
such that `⋃_Z B_Z ∪ LentJS_l` is partitioned into the single edges of `J_l` and at most
`126 n/M_l + 1.5 Σ_{(Y,l) giant} m_{Y,l}` cycles. … Each cycle consists of edges of `⋃_Z B_Z` and edges of
`⋃_j LJS_{Y,l,j}` for a single ancestor `Y`. Moreover (eqJbound) `|J_l| ≤ Σ_{h∈D_l} c^agg_{h,l} + Σ_{Z∈Std_l}[…]`."
J⁺: "`J_l = J^lost ⊔ J^hub ⊔ J^fr ⊔ J^par` … (J1) … (J2) … (i) … (ii) …".

Lean, in plain words: for every vertex type `V`, graph `G`, reals `N_0, D_*`, run, designation `δ`, stage data `S`,
round `l` and input family `B` (indexed by pre-part addresses): if the standing hypotheses of s5–s7 hold
(`RunHyp`: Γ1, Γ3, `N0Cond`, `n ≥ N_0`, `d_1 ≥ D_*`, run valid), `δ` is a designation, `S` is coherent, `3 ≤ l ≤ R`,
and for each `Z ∈ Std_l`, `B_Z ⊆ E_l(Z)` with every edge having an end in `Q*_Z`, then there are edge sets `J`,
`LentJS` and a list `D` of objects with:
- `J ⊆ ⋃_Z B_Z`;
- `LentJS ⊆ ⋃ {LJS_{Y,l,j} : Y a lend-good ancestor of round ≤ l−2, j < K^JS_l}`;
- `D` decomposes `(⋃_Z B_Z ∪ LentJS) \ J` (so `⋃B ∪ LentJS` = `J` ⊔ the edges of `D`, each edge in exactly one
  object); every object of `D` is a cycle;
- `|D| ≤ 126 n/M_l + 1.5 Σ_{Y ancestor, (Y,l) giant} m_{Y,l}` (reals);
- for each cycle some ancestor `Y` such that each of its edges is in `⋃_Z B_Z` or in some `LJS_{Y,l,j}`, `j < K^JS_l`;
- `|J| ≤ jBound` (eqJbound);
- `JPlusProps run G δ S l J`.

Faithfulness / T0 encodings (all recorded in the Spec docstring):
- **JSLC-USED**: "no edge … has been used" is a statement about the assembly, not a predicate. Encoded by
  assuming nothing: JS-LC may use every edge of every class; the consumer (MIX-C (a), lemLent (i)) discharges
  disjointness. The manuscript uses the hypothesis only in claim (d) ("so the whole class is available").
- **Index range of `LentJS`**: "`⋃_{Y,j}`" is read as the classes named in the hypothesis (lend-good, round
  `≤ l−2`, `j < K^JS_l`). This is what the proof produces and what MIX-C (a) and lemLent (ii) read.
- **Partition**: stated as `IsDecomp ((⋃B ∪ LentJS) \ J) D` with `J ⊆ ⋃B`. The blueprint's
  `IsDecomp ((⋃B \ J) ∪ LentJS) D` would allow an edge in `J ∩ LentJS` to also lie on a cycle, which the TeX
  ("partitioned") forbids. My form is the literal partition.
- **Setting**: `RunHyp` (TRIAGE §2.6) plus `IsDesignation` and `S.Coherent` (design note MAJOR-1 fix); the
  statement then transfers to every stage-1 outcome of positive weight via `coherent_ofOutcome`.
- **The v6.1 count** (T1 patch JSLC-G-UNDEFINED already applied in the TeX): `1.5 Σ m`, sum over
  `Y ∈ run.ancestors G` with `IsGiant`.
- **eqJbound** stays (not used later, but part of the statement: no weakening).
- **J⁺ "for every choice / Steps 3–8 delete nothing"**: not encoded (about the proof; unused downstream; D-DES-7).

### `JplusFactsStatement` [s6:lemJplus] (J3), (i) excl., (iii), (iv)
TeX: "(J3) The sets `D_l`, `⋃_Z F_Z`, `⋃_Z Q*_Z` are pairwise disjoint. Each vertex outside `D_l` that lies in a
round-`l` pre-part lies in exactly one such pre-part … (i) The types above are exhaustive and exclusive. … (iii)
`E(H_Y) ⊆ E_r(Y)` for every ancestor `Y` of round `r`, and the sets `E_r(Y)` (`Y` light) and `E_l(Z)`
(`Z ∈ Std_l`) are pairwise disjoint. (iv) `u ∈ V(Y(u))` for every classed port `u`."

Lean, in plain words: for a valid run and a designation, for every round `l`: the hubs, the fresh centres and the
classed non-lost ports are pairwise disjoint, and a vertex outside `D_l` lies in at most one round-`l` pre-part; no
edge is of two of the four J-types; `E(H_Y) ⊆ E_{r(Y)}(Y)` for every ancestor and the assigned sets of distinct
ancestors are disjoint; every classed port of a standalone pre-part of a round `≥ 3` lies in `V(Y(u))`. The
exhaustive half of (i) is `JPlusProps.types`; (v) is not stated (stage-1 law).

### `JslcTypesStatement` [s6:lemJSLC:proof-step-1] (T-avoidance)
TeX: "For `u ∈ Q*_Z`, the class `Y(u)` is lend-good and `lab_{Y(u),l}(u) = *`. … Both ends lie in `Z^0` … Since
`Z^0 = Ret_Z ⊔ Q*_Z` … `Y(v) ≠ Y(u)` … contrary to Lemma s2:lemEL. By the same lemma, for every edge `hu ∈ E_l(Z)`
with `u ∈ Q_Z` and `Y(u) = Y`, the vertex `h` lies outside `V(Y)`. In particular `h ∉ T_j(Y,l)`." Claim (a)/(e):
ports lie in `V(Y)` and outside every `T_{j'}(Y,l)`.

Lean: for a valid run, a designation, any stage data, `l ≥ 3`, `Z ∈ Std_l`: every `u ∈ Q*_Z` has `Y(u)` lend-good of
round `≤ l−2`, label `*`, `u ∈ V(Y(u))`, `u ∉ T_j(Y(u),l)` for all `j`; both ends of every edge of `E_l(Z)` lie in
`Ret_Z ∪ Q*_Z`; for every `u ∈ Q_Z` and every edge `hu ∈ E_l(Z)`: `h ∉ V(Y(u))` and `h ∉ T_j(Y(u),l)` for all `j`;
the two ends of a port–port edge of `E_l(Z)` have different classes.

### `JslcStep2Statement` [s6:lemJSLC:proof-step-2] (the set `J_l`; J1 aggregated)
TeX: Step 2 (2a), (2b), the move rule, "Only centres in `Ret_Z` are ever odd … So after the moves every centre has
even degree in every `R_Y`", "Counting `J_l` … This proves (s6:eqJbound)"; Step 3: "Every edge `hu ∈ R_Y` lies in
`Bead_{Y,l}`"; J⁺ (J1): "at most one `J^hub`-edge of class `Y` at `h`, aggregated over all parts of round `l`".

Lean, in plain words: under `Γ2(a)`, a valid run, a designation, any stage data, `3 ≤ l ≤ R` and the JS-LC input
`B`, there are `J` and a family `R_Y` (indexed by `PartId`) such that:
- `J ⊆ ⋃B`, each `R_Y ⊆ ⋃B`, `⋃B = J ∪ ⋃_Y R_Y`, `J` disjoint from each `R_Y`, the `R_Y` pairwise disjoint;
- every edge of `R_Y` lies in some `E_l(Z)`, `Z ∈ Std_l`, and is `hu` with `u ∈ Q*_Z` of class `Y` and `h ∉ V(Y)`;
- every vertex outside `V(Y)` (in particular every centre) has even degree in `R_Y`, with the degree counted over
  all parts of round `l` (aggregated parity);
- `R_Y ⊆ Bead_{Y,l}`;
- for every hub `h ∈ D_l` and class `Y`: at most one edge of `J` is a `J^hub`-edge of class `Y` at `h` (the
  refutation target, stated explicitly; the same as `JPlusProps.J1hub`);
- `|J| ≤ jBound` and `JPlusProps J`.

Faithfulness: the `R_Y` are proof objects (the realized beads); they are existentially quantified, which is what
Steps 3–7 consume (clusters from the components of `R_Y`, parity-clean by the even-degree clause). The explicit
`J1hub` conjunct duplicates a field of `JPlusProps` on purpose (visibility of the target).

### `JslcStep7DisjStatement` [s6:lemJSLC:proof-step-7]
TeX: "(D) … The sets `T_j(Y,l)` are pairwise disjoint … (JC-P) … The path families for distinct `j` lie in distinct
classes `LJS_{Y,l,j}`, which are disjoint. All of them lie in `Lend_Y ⊆ E(H_Y) ⊆ E_r(Y)`, while beads lie in
`⋃_Z E_l(Z)`. These sets are disjoint … for different `Y ≠ Y'`, because `E(H_Y) ∩ E(H_{Y'}) = ∅`."

Lean: for a valid run, coherent stage data and every round `l`: for every ancestor `Y`, every `j`, every
`Z ∈ Std_l`, `LJS_{Y,l,j} ∩ E_l(Z) = ∅`; classes of distinct ancestors are disjoint; classes of distinct `j` of one
ancestor are disjoint; the `T_j(Y,l)` are pairwise disjoint and lie in `V(Y)`. (No range on `l`/`Y.1` is needed:
the classes are empty outside `r(Y)+2 ≤ l ≤ R`, `j < K^JS_l`, by coherence. This makes the statement stronger.)

### `JslcPairsBalanceStatement` [s6:lemJSLC:proof-claim-a]
TeX: "(a) The bijections exist. … the padded loads of all layers are equal … By Lemma MED(b),
`Σ_{LayP_j} exc^- = Σ_{LayP_j} exc^+`. So the number of out-units of layer `j` equals its padded load, which equals
the padded load of layer `j+1`, which is the number of its in-units. For depth `1`, `Σ exc^- = Σ exc^+`."

Lean: for a system with the HCC-P hypotheses other than (JC-P) (`PreValid`) and all padded loads `Φ_j` equal, for
every junction `j`: `Σ_{u ∈ LayP_j} dem⁻(u) = Σ_{v ∈ LayP_{j+1}} dem⁺(v)`. Uniform in `k` (for `k = 1`, `pad ≡ 0`
gives the `X^out`/`X^in` sums).

### `JslcPairsDistinctStatement` [s6:lemJSLC:proof-claim-a] (distinct pair ends)
TeX: "The two vertices of a pair are distinct: for `k ≥ 2`, the layers `j` and `j+1` consist of different, pairwise
vertex-disjoint clusters …; for `k = 1`, `X^out ∩ X^in = ∅`."

Lean: for a `PreValid` system, every `u ∈ LayP_j` with `dem⁻(u) > 0` differs from every `v ∈ LayP_{j+1}` with
`dem⁺(v) > 0`. (Membership of the ends in `V(Y) \ ⋃T` is `JslcTypesStatement`.)

### `JslcJointMultStatement` [s6:lemJSLC:proof-claim-c] (joint multiplicity; P2E hand-off)
TeX: "(c) Every vertex lies in at most `max(2M_l−2, (M_l−1)+⌈M_l/2⌉) = 2M_l−2 ≤ t` pairs of `𝔓_j(Y,l)`. … at a
fixed junction a port occurs in at most `max(dem⁻, dem⁺)` pairs of each system containing it. Centres occur in no
pair. By Steps 4 and 5 and part (b), a port occurs in at most `(M_l−1)+⌈M_l/2⌉` pairs (if it belongs to `𝒮_0`) or
at most `2(M_l−1)` pairs (if it belongs to cherry systems). For `M_l ≥ 2` … both are at most `2M_l−2 < t = 2M_l+2`."

Lean, in plain words: let `M ≥ 2` and let `Sys_0, …, Sys_{q−1}` be `PreValid` systems, each marked cherry or not,
such that: at most one is not a cherry system (`𝒮_0`); at the ports of `𝒮_0`, `|exc| ≤ M−1` and `pad ≤ ⌈M/2⌉`; at
the ports of cherry systems, `|exc| ≤ 1` and `pad ≤ 1`; a port of `𝒮_0` is a port of no cherry system; every
vertex is a port of at most `M−1` cherry systems. Then for every junction `j` and vertex `v`,
`Σ_s junctionOcc(Sys_s, j, v) ≤ 2M−2`, and `2M−2 < 2M+2`.

The hypotheses are exactly the facts the proof takes from Steps 4, 5 and claim (b); stage 2 must establish them for
its construction. The pad hypothesis is `⌈M/2⌉` (the TeX's bound in (c)); Step 4's sharper `⌈(M−1)/2⌉` implies it
(`EG.Spec.JsMultNumStatement`, proved). The link to `t^JS_l = Stage1.tJS G run l` is `EG.tJS_eq_two_mul_add_two`.
The pair count `#{i : (P i).1 = v ∨ (P i).2 = v}` of `IsPathConnected` equals `Σ_s junctionOcc` once the pairs are
the bijections of claim (a) (distinct ends).

### `JslcRoutingStatement` [s6:lemJSLC:proof-claim-d]
TeX: "(d) There are pairwise edge-disjoint paths in `LJS_{Y,l,j}`, one for each pair of `𝔓_j(Y,l)` and joining its
two vertices. Each has length at most `2^{12}L_Y^4` and all its interior vertices in `T_j(Y,l)`. … `Y` is
lend-good. By … Lemma s3:lemCOL(b), `LJS_{Y,l,j}` is `(2^{12}L_Y^4, t)`-path connected through `T_j(Y,l)`, as a
graph on `V(Y)` … every multiset of pairs of distinct vertices of `V(Y)` in which every vertex lies in at most `t`
pairs …"

Lean: for coherent stage data, `Y ∈ lendGoodAnc l`, `l ≤ R`, `j < K^JS_l`, and every finite indexed family of pairs
of distinct vertices of `V(Y)` in which every vertex lies in at most `t^JS_l` pairs, there are paths `Q_i` in the
edge set `LJS_{Y,l,j}` joining the pairs, through `T_j(Y,l)`, of length `≤ 2^{12}L_Y^4`, pairwise edge-disjoint.

### `CapPrePartStatement` [s2:lemCap] (ii) (declared input)
TeX: "In every round `l ≤ R` of a valid `HB^tp` run, every `s = 0` piece `𝒫` satisfies `|𝒫| ≤ M_l`. Hence every
round-`l` pre-part has `|Z^0| ≤ M_l`; for every round-`l` part `Z` (light or standalone) every vertex is incident
with at most `M_l − 1` edges of `E_l(Z)`; and `τ_l ≥ …`."

Lean: under `Γ2(a)` and a valid run, for every round `l ∈ [1,R]`: every `s = 0` piece has at most `M_l` vertices;
every pre-part has `|Z^0| ≤ M_l` and every vertex has at most `M_l − 1` edges of `E_l(Z)`. The `τ_l` clause is
omitted (unused). `Γ2(a)` is the hidden standing assumption the proof uses (CAP-GAMMA-EXPLICIT).

### `StructureHYStatement` [s2:propStructure] (iii) (declared input, clauses used)
TeX: "`E(G) = ⨆ E(Cyc_l) ⊔ E_0 ⊔ ⨆_{Y light} E_{r(Y)}(Y) ⊔ ⨆_l ⨆_{Z∈Std_l} E_l(Z)` (disjoint unions);
`E(H_Y) ⊆ E_{r(Y)}(Y)` for every ancestor `Y`; every edge of `E_{r(Y)}(Y)` has both ends in `V(Y)`; the graphs
`H_Y` of all ancestors `Y` of all rounds are pairwise edge-disjoint".

Lean: for a valid run: `E(H_Y) ⊆ E_{r(Y)}(Y)` and `E_{r(Y)}(Y) ⊆ V(Y)^{(2)}` for every ancestor; the assigned sets of
distinct ancestors are disjoint; the `E(H_Y)` of distinct ancestors are disjoint. Only `run.Valid` is assumed (the
clauses stated need no condition on `D_*` or `n`; strengthening, blueprint STR-N0).

### `TowerBLateStatement` [s2:lemTower] (b), late clauses (declared input)
TeX: "For `3 ≤ l ≤ R`: … `P_{l−2} ≥ M_l^{13}` … Finally, completing (K1) of Proposition s2:propOV, the number `ν_l`
of ancestors of rounds at most `l−2` satisfies `ν_l ≤ 2.74 n/P_{l−2}` for `3 ≤ l ≤ R`."

Lean: under `Gamma1core D_*`, a valid run and `D_* ≤ d_1`, for every `3 ≤ l ≤ R`: `M_l^{13} ≤ P_{l−2}` (in ℕ) and
`ν_l ≤ 2.74 n / P_{l−2}` (in ℝ). Same hypothesis shape as `TowerBRoundStatement`.

## 6. The refutation target, and how the probe hits it

TRIAGE §4: "P-2: two `J^hub` edges of one class at one hub in one round (J1 aggregated)".

- **Where it is stated.** `JslcStep2Statement` has the explicit conjunct
  `∀ h ∈ D_l, ∀ Y, #{e ∈ J : IsJhubEdge l h Y e} ≤ 1`, where the filter runs over the whole `J_l` (all parts `Z`
  containing `h`), jointly with the **aggregated** even-degree clause for the `R_Y` (`degE (R_Y) h` counts
  class-`Y` beads at `h` in all parts). The same conjunct is `JPlusProps.J1hub` inside `JSLCStatement`.
- **Why this is the hazard.** A per-part parity rule makes each part even separately and moves one edge per
  (part, hub, class), so a hub in two parts with odd class-`Y` degree in each could lose two `J^hub` edges of class
  `Y`. That violates (J1), which s7:lemMULT and lemUltra use. Aggregated parity moves at most one. The Step-2
  Spec forces both: evenness of the `R_Y` over all parts (so every odd `(h,Y)` gets a move), and at most one
  class-`Y` `J^hub` edge at `h`.
- **Test.** `EGTest.ProbeP2J.two_jhub_violates_J1`: two distinct class-`Y` `J^hub` edges at one hub in `J` (from the
  same part or from different parts) violate the conjunct, and hence `JPlusProps`.
- **Manuscript check (by hand, stage 1).** I re-derived Step 2: pseudo-hubs are even by PAR (a class-`b` port lies
  in one part, being outside `D_l`); moves change the centre degree only; a PAR deletion is port–port, so never a
  `J^hub` edge; hubs are never ports (`A_Z ⊆ D_l`, `U_Z ∩ D_l = ∅`). No gap found. Stage 2 must prove it.

The other P-2 targets: **joint multiplicity** (`JslcJointMultStatement`, the aggregated claim (c) handed off by
P2E), **distinct pair ends** (`JslcPairsDistinctStatement`), **T-avoidance** (`JslcTypesStatement`, proved from
Lemma EL; `JslcStep7DisjStatement`, proved from s2:propStructure(iii)).

## 7. Non-vacuity (`EGTest/ProbeP2J.lean`)

- JS-LC / Step 2: a designation and coherent stage data exist for every run; `B_Z = ∅` meets the input condition;
  the conclusions of `JSLCStatement` and `JslcStep2Statement` hold for `B_Z = ∅` with `J = LentJS = ∅`, `D = []`,
  `R_Y = ∅` (consistency: the conclusion is not contradictory). Helpers `one_le_M`, `jBound_nonneg`.
- Refutation target: `two_jhub_violates_J1`, and its consequence `¬ JPlusProps`.
- Pre-routing systems: `S1` (`k = 1`) and `S2` (`k = 2`) of `EGTest.Chain` are `PreValid`; their junction
  occurrences are computed (`S2`: junction 0 pairs `1`–`2`, junction 1 pairs `3`–`0`; `S1`: pair `1`–`0`); the
  hypotheses and conclusions of `JslcPairsBalanceStatement` (equal loads; equal unit counts at both junctions),
  `JslcPairsDistinctStatement` (an out-unit and an in-unit exist) and `JslcJointMultStatement` (`S2` as a cherry
  system and `S1` as `𝒮_0`, `M = 2`) hold on the instances. **Sharpness**: three cherry systems through one port
  (dropping the hypothesis "at most `M − 1` cherry systems") give `3 > 2M − 2` pairs.
- Declared inputs: `Γ2(a)` plus a valid run (the run without rounds, `D_* = 2^{117}`) satisfy the hypotheses of
  `CapPrePartStatement`, `StructureHYStatement`, `JslcTypesStatement`, `JslcStep7DisjStatement` and
  `JplusFactsStatement` (with a designation).
- **Not checked**: hypotheses that need a valid run with `R ≥ 3` rounds under Γ1 and `n ≥ N_0` (`RunHyp` with
  `3 ≤ l ≤ R`; `TowerBLateStatement`, whose `D_* ≤ d_1` contradicts the run without rounds; `JslcRoutingStatement`,
  which needs a lend-good ancestor with `r(Y)+2 ≤ l ≤ R`). Such runs need `d_1 ≥ D_* ≥ 2^{2^{256}}` and are
  s2:propExists; the design note of P2-D [design] (MINOR-D) already deferred a concrete round with
  `E_3(Z) ≠ ∅`. For the round-level Specs the tests show only that the non-run hypotheses are satisfiable and that
  the conclusions are consistent.

## 8. Hazards and open questions

- **H1 (T0): JSLC-USED encoding.** The hypothesis "no edge … has been used" is dropped (the whole class is available
  to JS-LC). Reviewer: confirm that MIX-C discharges the disjointness (lemLent (i), MIX-C (a)).
- **H2 (T0): partition form** `IsDecomp ((⋃B ∪ LentJS) \ J) D` instead of the blueprint's `(⋃B \ J) ∪ LentJS`
  (§5). The blueprint form is weaker than "partitioned" when `J ∩ LentJS ≠ ∅`.
- **H3 (T0): `LentJS` index range** = lend-good ancestors of rounds `≤ l−2`, `j < K^JS_l` (the classes named in the
  hypothesis; stronger than an unrestricted `⋃_{Y,j}`; what MIX-C/lemLent read).
- **H4: the single-ancestor clause** uses `Y ∈ run.ancestors G` (the literal "a single ancestor `Y`"), not
  `lendGoodAnc`. The proof gives lend-good; the consumer does not need it (it has the `LentJS` range).
- **H5: Step-2 and routing Specs are proof-internal** (tags `[s6:lemJSLC:proof-…]`, as in P2E's EngineMult). Their
  hypotheses (e.g. Step 4's `|exc| ≤ M−1`, `pad ≤ ⌈M/2⌉`, claim (b)) are obligations of the stage-2 JS-LC proof.
  If stage 2 builds the systems differently, these Specs may need adjusting **before** they are locked; they are
  not consumed outside JS-LC.
- **H6: new Defs file** `EG/Defs/Probe/P2J/PreSystem.lean` (`PreValid`, `junctionOcc`, `IsPort`) needs integrator
  review. `PreValid` copies the `Valid` fields verbatim; a reviewer should diff the two.
- **H7: `RunHyp` for JS-LC** includes `N0Cond`/`Γ3`/`n ≥ N_0`, which the proof does not use (it uses Γ1 through
  lemTower(b), and `M_l ≥ 2^{40}` by definition). Kept for uniformity with TRIAGE §2.6 (s6b takes `RunHyp`); a
  reviewer may prefer the minimal hypotheses (Γ1core, valid, `d_1 ≥ D_*`). Either is faithful; `RunHyp` is weaker.
- **H8: the count of JS-LC needs `ν_l`, the number of all ancestors of rounds `≤ l−2`**, while the S_0 systems exist
  only for classes `Y` with `R_Y ≠ ∅`. The inequality "number of systems `≤ ν_l`" is immediate; noted for stage 2.
- **H9 (stage 2, size)**: the greedy `(Δ+1)`-colouring (Step 5) is not in Mathlib; the blueprint estimates ~100
  lines. EQ-USE-EMPTY-S0 (P2E H7): when `𝒮_0 = ∅` EQ-LPT does not apply; the proof must case-split.
- **H10: hypothesis set of the declared input `StructureHYStatement`** is `run.Valid G Dstar` only (the TeX has
  `n ≥ N_0`, `d_1 ≥ D_*`; blueprint s2b's full propStructure carries `2^{117} ≤ D_*`, `0 < n`). A stub with fewer
  hypotheses is a stronger unproved claim, so I re-checked why the four clauses are structural: `E_{r(Y)}(Y) ⊆ V(Y)^{(2)}`
  and the pairwise disjointness of the `E` sets follow from the definition of `Round.assign` (a function; steps
  (1)–(3) only assign edges inside `partVerts`/`Z^0`; assigned edges do not pass down); `E(H_Y) ⊆ E_{r(Y)}(Y)` needs
  the leaf graphs `X^0_Z` of one round to be edge-disjoint, which is SEP(i) (`EG.sepI`, proved, needs only
  `STree.WF`) through the graft, plus `X_Z ≤ X^0_Z`; the last clause follows from the first and third. None uses
  `D_*`, `n` or Γ. The integrator should still confirm when the full s2 Spec is written (it must imply this one).
- **Open question: stage-2 order.** Proposed: `JslcPairsDistinct` → `JslcPairsBalance` (MED(b)) → `JslcJointMult`
  (`hccpEndMult`-style per-system bound + counting) → `JslcRouting` (`colB_conn`, `exists_paths`) → `JslcStep2`
  (PAR + moves; the J1 target) → `JSLCStatement` (Steps 3–8, using all of the above and the engine).

## 9. Re-verification (second session, 2026-09-29 22:55)

The first session wrote all files but did not return its status. This session re-read every file against the TeX
(s6.tex 443–666, s2.tex 635–645, 722–740, 821–826, 1144–1160), rebuilt all modules, re-ran `scripts/check.sh` on
`EGTest/ProbeP2J.lean` (0 errors, 0 sorry), lint (0 findings) and the axiom scan (§1). Changes: Lemma EL has been
proved by P3A meanwhile, so `jslcTypes` no longer depends on a stub; the note, the docstrings of the three stubs,
`JSLCTypes.lean` and the test were updated accordingly (docstrings only; no statement changed). Hazard H10 added.

## 10. Math findings

None. I re-derived, by hand, Step 2 (the J1 target), claims (a), (c), (d), eqSzeroCost (the three cases of `k_0`),
the pad bound of Step 4 (`Π_j ≤ Φ_max ≤ Φ^raw_j ≤ ½(M−1)|LayP_j|`), eqCherryCost and the Step-8 arithmetic
(`0.75 + 13.7 + 0.5 + 16.44 M^{-11} ≤ 15`): no error. The only items are the T0 encodings H1–H3 and H7.

## Fix round 1 (2026-09-29; review `work/p2b/P2J.review1.md`)

- **R1 (minor; `StructureHYStatement` stub has fewer hypotheses than the TeX, `n ≥ N_0` dropped): fixed.**
  Verified: the review is right that an unproved stub with fewer hypotheses is a stronger unproved claim. Instead of
  adding `n ≥ N_0`, I proved the statement exactly as stated, from `run.Valid G Dstar` alone, so the stub (and its
  `sorry`) is gone: `EG.structureHY` in `EG/Proof/HB/StructureHY.lean` (0 sorry; axiom scan: 0 `sorryAx`; also
  `jplusFacts` and `jslcStep7Disj` are now sorry-free). The proof uses only the home-order clause of `Round.Valid`
  (`homeOrder.toFinset = prePartAddrs`), no condition on `n`, `D_*` or `Γ`:
  - `E(H_Y) ⊆ E_{r(Y)}(Y)` (new `EG.HB.Round.partGraph_edges_subset_E`): an edge of the part graph of pre-part `a`
    lies in the leaf graph `X^0_a` of the two-level recursion; by SEP (i) in count form (`EG.HB.STree.sep_count`,
    which needs no `WF`) at most one leaf graph contains it (`Round.eq_of_mem_partGraph_edges`), so step (1) of
    `Round.assign` (first pre-part in the home order whose part graph contains `e`) returns `a`
    (`Round.assign_of_mem_partGraph`). This is exactly the reviewer's "part graphs of one round are edge-disjoint"
    point; `X_Z ≤ X^0_Z` is `Round.partGraph_le_X0`.
  - `E_{r(Y)}(Y) ⊆ V(Y)^{(2)}`: existing `EG.HB.Run.E_subset_sym2`.
  - `E_{r(Y)}(Y)` pairwise disjoint (new `EG.HB.Run.disjoint_E_of_ne`): same round by `Round.disjoint_E`; rounds
    `l < l'` by `E_{l'} ⊆ E(G'_{l'}) ⊆ E(G_{l'}) ⊆ E(G_{l+1}) = passed_l`, disjoint from `E_l(Z)`
    (`Run.disjoint_E_graph_edges`).
  - `E(H_Y)` pairwise disjoint: from the first and third clauses.
  The Spec statement is unchanged (docstring only: now says proved). `EG.Spec.StructureHYStatement` is no longer a
  declared input of P2J; the remaining declared inputs are `capPrePart` (s2:lemCap (ii)) and `towerBLate`
  (s2:lemTower (b)). The helper lemmas live in the proof file (namespaces `EG.HB.Round`, `EG.HB.Run`); the s2
  structure unit may move them to `EG/Lib/HB/` when it writes the full propStructure Spec. Docstrings of
  `CapPrePart`/`TowerBLate` stubs, `JPlus.lean`, `JSLCStep7.lean` and `EGTest/ProbeP2J.lean` updated
  ("two `sorry`s of unit P2J"). §1 and §3 above still describe the pre-fix state where they say "three stubs"/
  "declared input" for `structureHY`; this section supersedes them.
- **C1 (cosmetic; `Disjoint (⋃B) LentJS` not stated in `JSLCStatement`): fixed (docstring only).** Verified derivable:
  `LentJS ⊆` lend-good classes `LJS_{Y,l,j}`, disjoint from every `E_l(Z)` by `JslcStep7DisjStatement` (now proved
  with 0 sorry), and `B_Z ⊆ E_l(Z)` is a hypothesis of `JSLCStatement`. Added one sentence to the module docstring
  of `EG/Spec/Chain/JSLC.lean`; the statement is unchanged.
- **C2 (cosmetic; conjunct `2M−2 < 2M+2` of `JslcJointMultStatement` is a tautology): not an issue.** Verified: it
  is true for every `M ≥ 2` in ℕ and records the TeX's "`< t^JS_l`"; the module docstring (line 70 of
  `EG/Spec/Chain/JSLCRouting.lean`) already says the link to `t^JS` is `EG.tJS_eq_two_mul_add_two`. No change.
- **C3 (note; proof-internal Specs `JslcJointMult`/`Step2` presuppose the Steps 4/5 construction): not an issue now,
  recorded.** Verified: these Specs have no consumer outside JS-LC and hypothesise exactly the Step 4/5 and claim (b)
  facts of the TeX. Stage 2 must re-review them before locking if its construction of the systems differs.
- **C4 (note; JSLC-USED hand-off to MIX-C (a)/lemLent (i) cannot be checked yet): not an issue now, recorded.**
  Verified: `EG/Spec/Chain/` has no MixC Spec. Whoever writes it must discharge "no edge of the classes has been used
  before" by disjointness (COL(g), lemLent (i)), since `JSLCStatement` gives JS-LC the whole classes.

Build check after the fix: `lake build EG.Proof.HB.StructureHY EG.Spec.Chain.JSLC EG.Spec.Chain.JSLCSteps
EG.Spec.Chain.JSLCRouting EG.Proof.Chain.JPlus EG.Proof.Chain.JSLCStep7 EG.Proof.Chain.JSLCTypes
EG.Proof.HB.CapPrePart EG.Proof.HB.TowerBLate`: success (only `sorry` warnings: the two stubs);
`scripts/check.sh EGTest/ProbeP2J.lean`: 0 errors, 0 sorry; `python3 -I scripts/lint.py`: 0 findings; axiom scan of
`EG.Proof.HB.StructureHY` and `EG.Proof.Chain.JSLCStep7` (prefix `EG`): 0 `sorryAx`, 0 violations.

## Proof round 1 (stage 3, 2026-09-30)

Work log (updated incrementally).

| node | Lean | file | state |
|---|---|---|---|
| claim (a), bijections exist | `EG.jslcPairsBalance` | `EG/Proof/Chain/JSLCRouting.lean` | **proved**, 0 sorry |
| claim (a), distinct pair ends | `EG.jslcPairsDistinct` | `EG/Proof/Chain/JSLCRouting.lean` | **proved**, 0 sorry |
| claim (c), joint multiplicity | `EG.jslcJointMult` | `EG/Proof/Chain/JSLCRouting.lean` | **proved**, 0 sorry |
| claim (d), routing | `EG.jslcRouting` | `EG/Proof/Chain/JSLCRouting.lean` | **proved**, 0 sorry (COL(b) on the record) |
| Step 2, J1 aggregated (**refutation target**) | `EG.jslcStep2` | `EG/Proof/Chain/JSLCStep2.lean` (+ `JSLCStep2{Par,Defs,Facts,JPlus,Count}.lean`) | **proved**, 0 sorry; `sorryAx` only through the declared input `EG.capPrePart` |
| JS-LC + J⁺ (`s6:lemJSLC`, `s6:lemJplus` J-interface) | `EG.jslc : EG.Spec.JSLCStatement` | `EG/Proof/Chain/JSLC.lean` (+ `JSLCCtx`, `JSLCGroups`, `JSLCSystems`, `JSLCAssembly`, `JSLCBound`) | **proved**, 0 sorry; `sorryAx` only through the declared inputs `EG.capPrePart`, `EG.towerBLate` |

Lib: `EG/Lib/Chain/JslcPairs.lean` (`PreValid.sum_demMinus_eq_Phi`, `PreValid.junctionOcc_le`,
`junctionOcc_eq_zero_of_not_isPort`), `EG/Lib/Chain/PairUp.lean` (pairing of an even set; first-fit
grouping `exists_firstFit`), `EG/Lib/Chain/Cherry.lean` (cherry split: `cherries`, exactly one cherry
per edge, conflict degree), `EG/Lib/Chain/CherrySystem.lean` (`cherrySys`: a list of pairwise
vertex-disjoint cherries as HCC-P data, one cherry per layer; `cherrySys_valid`).

**All probe nodes of the note are now proved** (round 1 finished, 2026-09-30). Remaining: nothing. No stuck goal.

How `EG.jslc` is assembled (files in `EG/Proof/Chain/`):
- `JSLCCtx.lean`: `exists_jslcCtx` runs Step 2 (`EG.jslcStep2`) and packs `J_l`, `R_Y` and the
  inputs (Lemma EL via `jslcTypes`/`step2Hyp_of`, `capPrePart`, `jslcStep7Disj`, `towerBLate`) into
  `JslcCtx`; Step-3 facts (`degE_port_le ≤ M_l−1`, `degE_centre_le ≤ m_{Y,l}`,
  `card_Bu_le ≤ n(M_l−1)`, `mY_le_of_not_isGiant`: `m_{Y,l} ≤ 2γ_l` for non-giant `(Y,l)`).
- `JSLCGroups.lean`: cherries of `R_Y` (`chs`), first-fit groups of ≤ `K^JS_l` pairwise vertex-disjoint
  cherries (`exists_grouping`, `GroupSpec`), junction pairs `(u'_j, u_{j+1 mod k})`, claims (a)
  (`pair_ends`), (c) (`card_pairs_le`: ≤ `deg_{R_Y}(v) ≤ M_l−1 < t^JS_l` pairs per vertex), (d)
  (`exists_routes`, by `EG.jslcRouting`).
- `JSLCSystems.lean`: Step 7 hypotheses of HCC-P per group (`sys_valid`), HCC-P gives ≤ 1 cycle
  (`exists_sys_decomp`).
- `JSLCAssembly.lean`: `exists_union`, the union over all systems `(Y,i)` (pairwise disjointness of
  beads/path edges exactly as in the TeX's Step 7 list), the partition
  `(⋃B ∪ LentJS) \ J = ⨆ systems`, `|D| ≤ Σ_Y |used Y|`, single ancestor per cycle.
- `JSLCBound.lean`: Step 8 (`card_used_le_real`, `sum_card_R_le`, `card_classes_le` (`≤ ν_l`),
  `sum_mY_le`, `gammaL_le_real`, `step8_arith`): the number of cycles is at most
  `Σ_{giant} m_{Y,l} + ν_l(2γ_l + 2M_l) + n/M_l ≤ 11.96 n/M_l + Σ_{giant} m_{Y,l} ≤ 126 n/M_l + 1.5 Σ_{giant} m_{Y,l}`.

**Deviation from the manuscript's construction (not a finding; the Spec is existential and
unchanged).** Steps 4–5 are simplified: the cherry split is applied to *every* component of `R_Y`
(all centres have even `R_Y`-degree by Step 2, so this is always possible), and the cherries are
grouped by first fit directly into groups of at most `K^JS_l` pairwise vertex-disjoint cherries, one
cherry per layer, load `1`, no padding. The system `𝒮_0(Y,l)` (MED, EQ-LPT, padding) is not built.
The cost is at most `m_{Y,l} + 2M_l + #cherries/K^JS_l` per class; for a non-giant `(Y,l)`,
`m_{Y,l} ≤ 2γ_l`, so the total stays within Step 8's budget (`ν_l·2γ_l ≤ 5.48 n/M_l`, versus the
manuscript's `ν_l·5γ_l`). The manuscript's 𝒮_0 hypothesis checks remain proved separately as the
Specs `JslcPairsBalance`, `JslcPairsDistinct`, `JslcJointMult`. Joint multiplicity in this
construction: a port lies in at most one pair per group and junction, and in at most
`deg_{R_Y}(u) ≤ M_l − 1` groups, so ≤ `M_l − 1 < t^JS_l` pairs.

Checks (2026-09-30): `lake build` of all unit modules succeeds (only `sorry` warnings: the stubs
`EG/Proof/HB/CapPrePart.lean`, `EG/Proof/HB/TowerBLate.lean`); `scripts/check.sh` on
`JSLCAssembly`, `JSLCBound`, `JSLC`: 0 errors, 0 sorry; `python3 -I scripts/lint.py`: 0 findings;
`lake env lean --run scripts/Axioms.lean --prefix EG` on `EG.Proof.Chain.{JPlus,JSLC,JSLCAssembly,
JSLCBound,JSLCCtx,JSLCGroups,JSLCRouting,JSLCStep2,JSLCStep2Count,JSLCStep2Defs,JSLCStep2Facts,
JSLCStep2JPlus,JSLCStep2Par,JSLCStep7,JSLCSystems,JSLCTypes} EG.Proof.HB.{CapPrePart,StructureHY,
TowerBLate}`: 3781 constants, 0 violations, 0 meta-scan hits; `sorryAx` in 6: the two stubs
`EG.capPrePart`, `EG.towerBLate` and, through them only, `EG.jslc`, `EG.exists_jslcCtx`,
`EG.jslcStep2`, `EG.step2Hyp_of`.

Small edits to earlier unit files: `@[expose]` on `GroupSpec` (`JSLCGroups.lean`) and `RouteSpec`
(`JSLCSystems.lean`), so later files can apply them.

Root imports for the orchestrator (not edited by me): add to `EG` the modules
`EG.Lib.Chain.{JslcPairs,PairUp,Cherry,CherrySystem}` and `EG.Proof.Chain.{JSLCRouting,JSLCStep2Par,
JSLCStep2Defs,JSLCStep2Facts,JSLCStep2JPlus,JSLCStep2Count,JSLCStep2,JSLCCtx,JSLCGroups,JSLCSystems,
JSLCAssembly,JSLCBound,JSLC}` (the last imports all others).

## Stage-1 re-dispatch (2026-09-30 00:25 UTC, after a restart)

The workflow re-issued the stage-1 task. All stage-1 deliverables were already present and reviewed (r1, r2); nothing
was rewritten, so the stage-3 work above is untouched. Re-verified: `lake build` of the 14 stage-1 modules (Specs,
stubs, probe Defs, `JPlus`/`JSLCTypes`/`JSLCStep7` proofs) succeeds, the only `sorry` warnings being the two stubs
`EG.capPrePart`, `EG.towerBLate`; `scripts/check.sh EGTest/ProbeP2J.lean`: 0 errors, 0 sorry; lint: 0 findings.
Review 2 items: C4 (tables in §1/§3 still listing `structureHY` as an input) fixed in the tables above; C3
(`PreValid` docstring should also name `bb_disj`, implied by `D_KK`) left for the integrator, to avoid rebuilding
the probe Defs' importers for a docstring.
