# P2J review 1 (clean-room, Specs of probe P-2 part 2: JS-LC Step 6/7 checks, JS-LC, J⁺)

Reviewer: clean-room statement reviewer, round 1, 2026-09-29. Scope: `work/p2b/P2J.md` and every file it lists:
`EG/Spec/Chain/{JSLC,JSLCSteps,JSLCRouting,JPlus}.lean`, `EG/Spec/HB/{CapPrePart,StructureHY,TowerBLate}.lean`,
the stubs `EG/Proof/HB/{CapPrePart,StructureHY,TowerBLate}.lean`, the new Defs file
`EG/Defs/Probe/P2J/PreSystem.lean`, and `EGTest/ProbeP2J.lean` (read only). The TeX is `proofs/manuscript/s6.tex`
443–666 (JS-LC, remStar, J⁺) and `s2.tex` 635–690 (lemCap), 722–760 (propStructure), 1144–1175 (lemTower). I also read
the locked Defs these Specs use: `EG/Defs/Chain/{JSet,Lending,Design,StageInst,HCCP,Cluster}.lean`,
`EG/Defs/HB/{Run,Round}.lean` (assign, E, partGraph, ancestors, nuAnc), `EG/Defs/Expander.lean` (IsPathConnected),
`EG/Defs/Objects.lean` (IsDecomp), `EG/Defs/Gamma/Full.lean` (RunHyp). I edited no Lean file.

**Verdict: approve.** Every Spec reads back to its TeX with the stated T0 encodings. I found no false statement, no
vacuous hypothesis set and no probe node hidden among the declared inputs. The declared-input stub
`StructureHYStatement` is stated with fewer hypotheses than the TeX (see R1). It is not blocking, but the integrator must
confirm it. The other items are cosmetic. I found no error in the manuscript (§6).

## 1. Hygiene

- `python3 -I scripts/lint.py`: 0 findings.
- `sorry`: 0 in every Spec, in the Defs file, in the three proved files and in the test file. The three
  `[DECLARED INPUT]` stubs each have one `sorry`, which is allowed. The file-level count is 2 because the docstring
  also contains the word.
- Docstrings start with the manuscript label. The proof-internal Specs use the tag `[s6:lemJSLC:proof-…]`, as
  `EngineMult.lean` already does.
- Scratch check `/tmp/p2jrev/Scratch.lean` (against the built modules): for `k = 1`,
  `junctionOcc 0 u = dem⁻(u) + dem⁺(u)` at a port. So the `X^out`/`X^in` reading of the Defs file depends on
  `PreValid.pad_k1`, which every consumer assumes. It compiles.

## 2. Fidelity: back-translation of each Spec

### `JSLCStatement` [s6:lemJSLC] + J⁺ interface
Plain mathematics:
- Hypotheses: RunHyp (Γ1, Γ3, N0Cond, `n ≥ N_0`, `d_1 ≥ D_*`, valid run); `δ` is a designation; `S` is coherent
  stage data; `3 ≤ l ≤ R`; for every `Z ∈ Std_l`, `B_Z ⊆ E_l(Z)` and every edge of `B_Z` has an end in `Q*_Z`.
- Conclusion: there are `J`, `LentJS` and a list `D` of objects such that:
  - `J ⊆ ⋃B`;
  - `LentJS ⊆ ⋃{LJS_{Y,l,j} : Y lend-good, r(Y)+2 ≤ l, j < M_l²}`;
  - `D` is a list of cycles that exactly partitions `(⋃B ∪ LentJS) \ J`, with `|D| ≤ 126n/M_l + 1.5 Σ_{Y ancestor, (Y,l) giant} m_{Y,l}` (in ℝ);
  - each cycle has one ancestor `Y` whose classes `LJS_{Y,l,j}` (`j < K^JS_l`) contain all its edges outside `⋃B`;
  - `|J| ≤ RHS(eqJbound)`;
  - `JPlusProps`.

Comparison with TeX 443–458:
- **Quantifier order.** `δ` comes before `S`, as in "Fix a valid run, a designation δ, a stage-1 outcome…". Correct.
- **Partition.** `IsDecomp` includes WF (Nodup, length ≥ 3). With `J ⊆ ⋃B` it gives exactly "⋃B ∪ LentJS is
  partitioned into the single edges of J and … cycles". The author's form is the literal one (H2), and I agree that the
  blueprint's `(⋃B \ J) ∪ LentJS` form is weaker when `J ∩ LentJS ≠ ∅`.
- **Cycles are cycles of G.** This is automatic: `B ⊆ E_l(Z) ⊆ E(G)`, and `LentJS ⊆ LJS ⊆ E(H_Y)` (`Coherent.ljs_sub`).
- **Constants.** 126 and 1.5 match the v6.1 statement (T1 patch JSLC-G-UNDEFINED). The sum range "ancestors `Y` for
  which `(Y,l)` is giant" is `(run.ancestors G).filter IsGiant`. `n = G.card`. `M_l ∈ ℕ` (M-INTEGER resolved), with
  real division. Correct.
- **Single ancestor.** "Each cycle consists of edges of ⋃B and edges of ⋃_j LJS_{Y,l,j} for a single ancestor Y" is
  rendered literally. H4 (`Y ∈ ancestors`, not lend-good) is fine: together with the `LentJS` range and the
  disjointness of the classes of distinct ancestors, a cycle that contains a lent edge has a lend-good `Y`.
- **T0 JSLC-USED (H1).** The hypothesis "no edge … has been used" is dropped, so the Spec gives JS-LC the whole
  classes. The manuscript uses the hypothesis only in claim (d) ("so the whole class is available"). Dropping it makes
  the Spec stronger, and I accept the encoding. The consumer MIX-C Spec does not exist yet (`EG/Spec/Chain/` has no
  MixC). Its author must still discharge "not used before" by disjointness (COL(g), lemLent (i)). I cannot check that
  hand-off now.
- **T0 LentJS range (H3).** Accepted. It is the range named in the hypothesis, and it is stronger than an unrestricted
  union.
- **Not stated: disjointness of `⋃B` and `LentJS`.** The blueprint lists it under (1). It is derivable: `LentJS` lies
  in lend-good classes, which are disjoint from every `E_l(Z)` by `JslcStep7DisjStatement` (proved), and
  `B_Z ⊆ E_l(Z)`. No change is needed. See C1.
- **RunHyp (H7).** RunHyp contains more than the proof uses. The extra hypotheses weaken the statement but match the
  consumer's setting (TRIAGE §2.6), so I accept it. Γ2(a), which Cap(ii) and hence (J2) need, follows from Γ1.
- **eqJbound.** `jBound` matches the displayed RHS term by term:
  - `c^agg` is `cAgg`, counted over `E_l(Z)` (not `B_Z`), as the TeX says;
  - `Σ_{x∈F_Z} c_x(Z)`;
  - `(M_l−1)|Lost_Z|` is computed in ℝ;
  - `½ Σ_{u∈Q_Z} c_pp(u)` runs over `classed` = `Q_Z`, as in the TeX (not `Q*_Z`).
- **JPlusProps (locked Defs, read for the interface).**
  - `types`: J⁺ (i), exhaustive.
  - `J1hub`/`J1fr`/`J1lost`: the filter runs over all of `J`, so they are aggregated.
  - `J2end`, `J2cap`, `J2out`, `J2card`: (J2), with the vestigial 1.37 dropped in favour of the sharper bound.
  - `freshCap`: (ii).
  - Everything else of J⁺ ((J3), exclusivity, (iii), (iv)) is in `JplusFactsStatement`. (v) is a stage-1-law fact.
    "For every choice / Steps 3–8 delete nothing" is not encoded (D-DES-7). I accept that: no consumer reads it.

### `JplusFactsStatement` [s6:lemJplus] (J3), (i) exclusive, (iii), (iv) — proved
Plain mathematics: for a valid run, a designation and any stage data:
- for every `l`, the sets `D_l`, `⋃F_Z` and `⋃Q*_Z` are pairwise disjoint, and a vertex outside `D_l` lies in at most
  one round-`l` pre-part;
- no edge is of two of the four J-types;
- `E(H_Y) ⊆ E_{r(Y)}(Y)`, and the `E_{r(Y)}(Y)` of distinct ancestors are disjoint;
- for `l ≥ 3`, every classed port `u` of a standalone pre-part lies in `V(δ_l(u))`.

Comparison:
- (J3) "exactly one such pre-part" is stated as "at most one". Together with "lies in a round-`l` pre-part" this is
  the same thing, so it is faithful.
- (iii): ancestors = parts = light parts or standalone pre-parts (`Run.ancestors = parts`). So "E_r(Y) (Y light) and
  E_l(Z) (Z ∈ Std_l) pairwise disjoint" is exactly pairwise disjointness over distinct ancestors. Faithful.
- (iv) is restricted to `l ≥ 3`. `anc_l = ∅` for `l ≤ 2`, so there are no classed ports there. Faithful.
- Hypotheses: `n ≥ N_0` and Γ are dropped. That strengthens the statement, and it is proved using `EG.structureHY`.
  See R1.

### `JslcTypesStatement` (Step 1 + claim (e), T-avoidance) — proved
Plain mathematics: for `l ≥ 3` and `Z ∈ Std_l`:
- every `u ∈ Q*_Z` has `Y(u)` lend-good of round `≤ l−2`, `lab = *`, `u ∈ V(Y(u))`, and `u ∉ T_j(Y(u),l)` for all `j`;
- both ends of every edge of `E_l(Z)` lie in `Ret_Z ∪ Q*_Z`;
- for `u ∈ Q_Z` and an edge `hu ∈ E_l(Z)`: `h ∉ V(Y(u))` and `h` lies in no `T_j(Y(u),l)`;
- the ends of a port–port edge have different classes.

This matches the TeX's "two facts", Step 1, (a) and (e). The class clause is stated over `Q_Z` instead of `Q*_Z`,
which is stronger, and it is proved from Lemma EL (no stub). It needs no stage-data coherence, which is also stronger.

### `JslcStep2Statement` (Step 2 + Step 3 ¶1; J1 aggregated — refutation target)
Plain mathematics: under Γ2(a), a valid run, a designation, any `S`, `3 ≤ l ≤ R` and the JS-LC input `B`, there are
`J` and `R : PartId → edge sets` such that:
- `⋃B = J ⊔ ⨆_Y R_Y`;
- every edge of `R_Y` is `hu ∈ E_l(Z)` with `u ∈ Q*_Z`, class `Y`, and `h ∉ V(Y)`;
- every vertex outside `V(Y)` has even `R_Y`-degree, counted over all parts;
- `R_Y ⊆ Bead_{Y,l}`;
- for every hub `h ∈ D_l` and class `Y`, at most one `J^hub` edge of class `Y` at `h` in all of `J`;
- `|J| ≤ jBound`, and `JPlusProps J`.

Comparison:
- "Every centre has even degree in every `R_Y`" is correct: the centres of class-`Y` edges are exactly the vertices of
  `R_Y` outside `V(Y)` (Step 1, EL).
- The target is stated in the aggregated form (TRIAGE §1b MULT-J1), and the parity is aggregated over the parts too.
- `R_Y ⊆ Bead`: `Bead` asks that `h` not be a class-`Y` classed port of `Z`. `h ∉ V(Y)` gives this, because a class-`Y`
  classed port lies in `V(Y)` by the designation.
- Nothing needed downstream is missing. Steps 3–7 read port degree ≤ `M_l − 1` (Cap), centre degree ≤ `m_{Y,l}` (via
  `Bead`) and parity-cleanness (the even-degree clause).
- I re-derived the truth of the target by hand; see §6.

### `JslcStep7DisjStatement` (Step 7 disjointness) — proved
Plain mathematics: for a valid run and coherent `S`, for every round `l`:
- `LJS_{Y,l,j} ∩ E_l(Z) = ∅` for every ancestor `Y` and every `Z ∈ Std_l`;
- classes of distinct ancestors are disjoint;
- classes of distinct `j` of one `Y` are disjoint;
- the `T_j(Y,l)` are pairwise disjoint and lie in `V(Y)`.

These are exactly the Step 7 facts ((D) and (JC-P)). They hold with no range on `l`/`Y`, which is stronger; the
classes are empty off-range by `ljs_eq_empty`.

### `JslcPairsBalanceStatement` (claim (a), bijections exist)
Plain mathematics: for `PreValid` data with all padded loads equal, for every `j`:
`Σ_{LayP_j} dem⁻ = Σ_{LayP_{j+1}} dem⁺`.
- Faithful.
- True: `IsAdmissible` orients exactly the beads, the hubs are balanced, and every bead end is a hub or a port, so
  `Σ_ports exc = 0` for each cluster. By `D_KK`, `pexc` is the excess in the unique cluster. So
  `Σ_{LayP_j} dem⁻ = Σ_{LayP_j} dem⁺ = Φ_j = Φ_{j+1}`.
- The `k = 1` case is covered, because `pad ≡ 0` and the `Φ` hypothesis is trivial.

### `JslcPairsDistinctStatement` (claim (a), distinct pair ends)
Plain mathematics: for `PreValid` data, an out-unit of layer `j` and an in-unit of layer `j+1 mod k` are different
vertices.
- Faithful.
- True: for `k ≥ 2`, the layers differ, and a vertex that is a port of two clusters contradicts `D_KK`. For `k = 1`,
  `pad = 0`, so `exc⁻ > 0` and `exc⁺ > 0` cannot both hold. That is the TeX's `X^out ∩ X^in = ∅`.

### `JslcJointMultStatement` (claim (c), joint multiplicity)
Plain mathematics: let `M ≥ 2` and let `Sys_s` (`s < q`) be `PreValid` systems with at most one non-cherry system.
Assume:
- at ports of the non-cherry system, `|exc| ≤ M−1` and `pad ≤ ⌈M/2⌉`;
- at ports of cherry systems, `|exc| ≤ 1` and `pad ≤ 1`;
- no port of the non-cherry system is a port of a cherry system;
- every vertex is a port of at most `M−1` cherry systems.

Then for all `j` and `v`: `Σ_s junctionOcc(Sys_s, j, v) ≤ 2M−2 < 2M+2`.

Comparison:
- The hypotheses are exactly those the TeX draws from Steps 4, 5 and (b). The pad bound is the weaker `⌈M/2⌉`
  (stronger statement).
- True: per system, `occ ≤ max(dem⁻, dem⁺) = |exc| + pad` for `k ≥ 2` (one layer per port by `D_KK`), and
  `occ = |exc|` for `k = 1`. So
  - `S_0`: `≤ (M−1) + ⌈M/2⌉ ≤ 2M−2` for `M ≥ 2`;
  - cherries: `≤ 2(M−1)`;
  - the two kinds never share a port.
- Direction check: `Σ junctionOcc` is at least the number of pairs containing `v`, which is the count that
  `IsPathConnected` reads. So the bound is safe to use for routing even before distinctness.
- The TeX's sharpness sentence ("If `M_l ≥ 4`, the value `2M_l−2` can occur only at …") is commentary and is not
  used; its omission is fine.

### `JslcRoutingStatement` (claim (d))
Plain mathematics: suppose `S` is coherent, `Y` is lend-good of round `≤ l−2`, `l ≤ R` and `j < K^JS_l`. Then for every
finite family of pairs of distinct vertices of `V(Y)`, in which each vertex lies in at most `t^JS_l` pairs, there are
paths in `LJS_{Y,l,j}` joining the pairs. They go through `T_j(Y,l)`, have length `≤ 2^{12}L_Y^4`, and are pairwise
edge-disjoint.
- This matches (d) together with s1:citDef7, the multiset reading and remMonotone(iii), since the statement quantifies
  over all families.
- It follows from `Coherent.colB_conn`: `lendGoodAnc` gives `¬lendBad`, hence `colB Y`, and
  `r(Y)+2 ≤ l ≤ R` gives `l ∈ lateRounds`.
- `ancGraph.verts = partVerts = ancVerts`, so the vertex hypothesis is the same as in `IsPathConnected`.
- Not requiring `R_Y ≠ ∅` makes the statement stronger.

### New Defs `EG/Defs/Probe/P2J/PreSystem.lean`
- **PreValid.** I diffed it against the locked `HccpData.Valid`. `PreValid` has exactly the fields `k_pos`, `adm`,
  `beads_G`, `T_disj`, `pad_k1`, `D_KK`, `D_KT`, `parityClean`, with the same bodies. It omits the (JC-P) fields
  `path_G`, `path_ends`, `path_T`, `starts`, `ends`, `path_edisj`, `pp_disj`, `pb_disj`, and also `bb_disj`, which
  the locked docstring itself says is "also implied by (D)". Correct subset.
- **junctionOcc.** `[u∈LayP_j]dem⁻ + [u∈LayP_{j+1 mod k}]dem⁺`, and 0 for `j ≥ k`. This is the number of copies of `u`
  in the two multisets of Step 6. For `k = 1` it is `exc⁻+exc⁺+2pad`, which equals `|exc|` under `pad_k1` (scratch
  check). Faithful.
- **IsPort.** Faithful.

### Declared inputs
- **`CapPrePartStatement` [s2:lemCap](ii).**
  - Statement: under Γ2(a) and a valid run, for every `l ∈ [1,R]`: every `s = 0` piece (`pieceAddrs` is the leaves of
    the `s = 0` recursion) has `≤ M_l` vertices; every pre-part has `|Z^0| ≤ M_l`; and every vertex has `≤ M_l−1`
    edges of `E_l(Z)`.
  - Matches TeX 646–651. The `τ_l` clause is omitted (unused).
  - Γ2(a) is the condition the TeX proof invokes ("By Γ2(a) … `d_l ≥ D_* ≥ 2^{117}`"; deps list s1:condG2).
  - Used by JS-LC ("two facts", (J2), Step 8). An upstream s2 node, not a P-2 node.
  - It does not duplicate `Cap.lean`, which has (i), the remark and the graph-level step.
- **`TowerBLateStatement` [s2:lemTower](b).** Under `Gamma1core`, a valid run and `D_* ≤ d_1`, for `3 ≤ l ≤ R`:
  `M_l^{13} ≤ P_{l−2}` (ℕ) and `ν_l ≤ 2.74n/P_{l−2}` (ℝ, `ν_l` = number of ancestors with `r+2 ≤ l`). This matches TeX
  1156–1162 with the same hypothesis shape as `TowerBRoundStatement`. It is used by Step 8 of JS-LC. Upstream.
- **`StructureHYStatement` [s2:propStructure](iii), the clauses used.** For a valid run:
  - `E(H_Y) ⊆ E_{r(Y)}(Y)`;
  - `E_{r(Y)}(Y) ⊆ V(Y)^{(2)}`;
  - the `E_{r(Y)}(Y)` of distinct ancestors are disjoint;
  - the `E(H_Y)` of distinct ancestors are disjoint.

  This matches the TeX clauses. It is used by Step 7 and by J⁺(iii). Upstream. See R1 for the hypotheses.
- **Nothing hidden.** No P-2 node is among the inputs:
  - Lemma EL is used through the proved `EG.edgeLaminarity`.
  - COL(b) and defCOL are `Coherent` fields, discharged by `coherent_ofOutcome` (proved).
  - s2:propStructure(iv) is used through proved Lib lemmas.
  - Lovász path-connectivity is not cited by JS-LC.
  - The greedy colouring is to be proved in Lib.

## 3. Vacuity

- **Round-level Specs** (`JSLCStatement`, `JslcStep2Statement`, `JslcRoutingStatement`, `TowerBLateStatement`). Their
  hypotheses need a valid run with `R ≥ 3` under Γ1 and `n ≥ N_0`, and no test exhibits one. This is a known
  project-wide gap (s2:propExists; design MINOR-D), and §7 of the note documents it. The non-run hypotheses (designation,
  coherent `S`, `B_Z = ∅`) are shown satisfiable, and the conclusions are shown consistent.
- **Non-trivial conclusions.** In `JSLCStatement` and `JslcStep2Statement`, `J := ⋃B`, `D = []` is not a witness in
  general: `JPlusProps.J1hub`/`J1fr`/`J1lost`, `J2cap` and `jBound` bind as soon as a hub carries two class-`Y` edges.
  `two_jhub_violates_J1` shows this for J1.
- **`PreValid`-level Specs.** They are satisfied by the concrete systems `S1`, `S2`, and the conclusions hold there.
  The sharpness test (three cherry systems through one port, giving `3 > 2M−2`) shows that the "`≤ M−1` cherry
  systems" hypothesis is needed.
- **Proved Specs** (Types, Step7Disj, JplusFacts). Their hypotheses are satisfied by the run without rounds, and the
  conclusions are not tautologies (they are disjointness and membership facts about the defined sets).
- **Trivial conjunct.** Only the conjunct `2M−2 < 2M+2` of `JslcJointMultStatement` is trivially true. It is
  harmless; see C2.

## 4. Findings

- **R1 (minor, T0; declared input stated with fewer hypotheses than the TeX).** The TeX of s2:propStructure assumes
  "`n ≥ N_0` and `d_1 ≥ D_*`". `StructureHYStatement` assumes only `run.Valid G Dstar`. Since `Run.Valid` contains
  `D_* ≤ d_l` for every round in `[1,R]`, `d_1 ≥ D_*` is implied whenever there is a round. The dropped part is
  `n ≥ N_0`.
  - A stub with fewer hypotheses is a stronger unproved claim.
  - The author's structural argument (H10) is plausible. I checked it against `Round.assign`:
    - `assign` is a function, so the `E` sets of one round are disjoint;
    - assigned edges do not pass down, so the `E` sets of different rounds are disjoint;
    - steps (1)–(3) assign only inside `partGraph`/`partVerts`/`Z0`, which gives the `V(Y)^{(2)}` clause;
    - `E(H_Y) ⊆ E_{r(Y)}(Y)` needs step (1)'s `find?` to return `Y` itself, i.e. the part graphs of one round are
      edge-disjoint. That follows from SEP(i) (proved) plus `X_Z ≤ X^0_Z`, provided `Round.Valid` supplies the tree
      well-formedness.
  - None of this uses `n` or Γ.
  - **Action:** the s2 structure unit proves this exact statement, or its full propStructure Spec is checked to imply
    it with only `run.Valid`. If it cannot, add the hypotheses to the stub and to the two proved statements that use
    it (`JplusFactsStatement`, `JslcStep7DisjStatement`); JS-LC itself already carries RunHyp.
- **C1 (cosmetic).** `JSLCStatement` does not state `Disjoint (⋃B) LentJS`, which the blueprint lists. It is derivable
  from `JslcStep7DisjStatement`, so a consumer lemma can supply it. No change needed. Optionally, add one sentence to
  the module docstring.
- **C2 (cosmetic).** In `JslcJointMultStatement`, the conjunct `2*M - 2 < 2*M + 2` is a tautology in ℕ for `M ≥ 2`.
  It records the TeX's "`< t`", and the link to `t^JS_l` goes through `EG.tJS_eq_two_mul_add_two`. Fine as
  documentation.
- **C3 (note for stage 2, H5).** The Step-6 Specs are proof-internal: `JslcJointMult` hypothesises Step 4/5 facts
  (`|exc| ≤ M−1`, `pad ≤ ⌈M/2⌉`, cherry `pad ≤ 1`, claim (b)). If stage 2 builds the systems differently, re-review
  before locking. They have no consumer outside JS-LC.
- **C4 (note).** The consumer check of the JSLC-USED encoding (MIX-C (a) / lemLent (i) discharging "not used before" by
  disjointness) must happen when the MIX-C Spec is written. No MixC Spec exists yet.

## 5. Refutation target (P-2): two `J^hub` edges of one class at one hub in one round

- **Stated correctly.** The target is the conjunct
  `∀ h ∈ D_l, ∀ Y, #(J.filter (IsJhubEdge l h Y)) ≤ 1` of `JslcStep2Statement`, where the filter runs over all of `J`.
  It is also `JPlusProps.J1hub` inside `JSLCStatement`.
- **The typed predicate cannot be satisfied spuriously.**
  - `IsJhubEdge` needs `h ∈ hubs(Z) ⊆ D_l`, `u ∈ Q*_Z ⊆ U_Z = Z^0 \ D_l`, `e ∈ E_l(Z)` and class `Y(u) = Y`.
  - A PAR deletion has both ends in `Q*_Z`, so it is never a `J^hub` edge.
  - The roles cannot swap, because `u ∉ D_l`.
- **Hand check of the TeX (Step 2).**
  - A hub `h ∈ D_l` is never a port, so it is a centre of class-`Y` edges only through centre–port edges `hu ∈ B_Z`
    with `Y(u) = Y`, over all parts `Z ∋ h`.
  - Its `R^0_Y`-degree is the sum over those parts. It gets one move if and only if that sum is odd.
  - A move at `(h', Y')` with `h' ≠ h` is an edge `h'u'`. It is a `J^hub` edge at `h` only if `h ∈ {h', u'}`, but
    `h ≠ h'` and `h ≠ u'` (a port). So it is not one.
  - Hence at most one `J^hub` edge of class `Y` at `h`. The target holds in the manuscript.
- **The per-part variant** (odd in `Z_1` and odd in `Z_2`, hence two moves) is exactly what the aggregated parity rules
  out. The Spec forces the aggregated reading through both the even-degree clause and the counting conjunct.

## 6. Mathematical doubts about the manuscript

None. I re-derived the following and found no gap:
- Step 1 (EL);
- Step 2: pseudo-hubs are even by PAR, since a pseudo-hub is not in `D_l` and so lies in one part; a move changes only
  the centre's degree; the eqJbound count term by term;
- Step 3: `R_Y ⊆ Bead`, and giant ⇒ `(Y,l)` giant;
- Step 4: `Φ(clu_C) ≥ 1`; `k_0 ≤ #clusters`; the raw loads are `≥ Φ_max`; the pad spread
  `pad ≤ ⌈(M−1)/2⌉`, from `Π_j ≤ Φ_max ≤ Φ^raw_j ≤ ½(M−1)|LayP_j|`; the three cases of eqSzeroCost;
- Step 5: conflict degree `≤ m/2 + 2M − 5`; `⌈η/⌊η/2⌋⌉ ≤ 3` for `η ≥ 4`; eqCherryCost; `sc ≤ (1.5m−12)^+`;
- claims (a)–(e);
- Step 7 (D)/(P)/(JC-P);
- Step 8: `0.75 + 13.7 + 0.5 + 16.44 M^{-11} ≤ 15` for `M ≥ 2^{40}`, using `γ_l ≤ P_{l−2}/M_l`,
  `ν_l ≤ 2.74n/P_{l−2}` and `P_{l−2} ≥ M_l^{13}`.

The only wording item is the one the Defs already record: the factor 1.37 in (J2) is vestigial.

---

# P2J review 1, re-dispatch (clean-room, 2026-09-30)

Reviewer: a fresh clean-room statement reviewer, round 1, re-issued by the workflow after the restart. I did not read
the review above. I appended this section so the review above (already answered by "Fix round 1" in `P2J.md`) is
kept. Scope: the current state of every Spec, stub and probe-Defs file listed in `work/p2b/P2J.md` §1, checked against
`s6.tex` 443–666 (JS-LC, remStar, J⁺), 680–865 (the MIX-C consumer), `s2.tex` 635–651 (lemCap), 839–851 (propOV K1)
and 1144–1250 (lemTower and its proof), and `s1.tex` 1644–1656 (Γ2). I edited no Lean files. Scratch checks are in
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/P2Jr1.lean` (session scratchpad) (compiled with `lake env lean`, 0 errors).

**Verdict: approve.** No major or minor fidelity defect. There are a few cosmetic or record-keeping notes (N1–N5)
below. I found no mathematical error in the manuscript passages.

## 1. Fidelity (back-translation next to the TeX)

| Spec | plain mathematics | TeX comparison |
|---|---|---|
| `JSLCStatement` | For every valid run with Γ1, Γ3, N0Cond, `n ≥ N_0` and `d_1 ≥ D_*`, every designation δ, all coherent stage data S, every `3 ≤ l ≤ R`, and every family `B_Z ⊆ E_l(Z)` (`Z ∈ Std_l`) whose edges each have an end in `Q*_Z`, there exist `J`, `LentJS` and a list `D` of objects such that: `J ⊆ ⋃B`; `LentJS ⊆ ⋃{LJS_{Y,l,j} : Y lend-good with r(Y) ≤ l−2, j < M_l²}`; `D` is an edge-partition of `(⋃B ∪ LentJS) \ J` into well-formed objects, each of them a cycle; `|D| ≤ 126n/M_l + 1.5 Σ_{Y ancestor, (Y,l) giant} m_{Y,l}` (in ℝ); each cycle uses only edges of `⋃B` and of `⋃_{j<K} LJS_{Y,l,j}` for one ancestor `Y`; `|J| ≤` RHS of eqJbound; and `JPlusProps J`. | Faithful. The quantifier order is TeX's order (run, δ, stage data, `l`, then `B`). The constants 126 and 1.5 are right, `n = |V(G)|`, and `K^JS = M_l²` (`KJS`). "Partitioned" is exactly `J ⊆ ⋃B` plus `IsDecomp` of the complement. The setting matches the consumer MIX-C (s6.tex 683: "valid run with `n ≥ N_0` and `d_1 ≥ D_*`"). The "not used" hypothesis is dropped and the whole class is given to JS-LC. That is a T0 encoding, and it is a strengthening: the MIX-C text (s6.tex ~800: "By COL(g) … no edge of these classes has been used") shows that the consumer discharges it by disjointness. |
| `JPlusProps` (locked Def) | Every edge of `J` is of type J^par, J^hub, J^fr or J^lost, each lying in some `E_l(Z)`. At each hub `h ∈ D_l` and for each class `Y`, at most one J^hub-edge of class `Y` counted over the whole of `J`, and likewise at fresh and lost centres. J-edges in `E_l(Z)` have an end in `Q*_Z`. For every `Z` and every vertex, at most `M_l−1` J-edges in `E_l(Z)` at that vertex. At most `M_l−1` J-edges at any vertex outside `D_l`. `|J| ≤ n(M_l−1)`. A fresh centre carries at most `M_l−1` J^fr-edges. | Matches J⁺ (i)-exhaustive, (J1), (J2), (ii). J2out covers lost centres and vertices in no pre-part, which is still true (they have degree 0 in `J ⊆ ⋃E_l(Z)`, or lie in one pre-part). |
| `jBound` | `Σ_{h∈D_l} c^agg + Σ_Z [Σ_{x∈F_Z} c_x(Z) + (M_l−1)|Lost_Z| + ½ Σ_{u∈Q_Z} c_pp(u)]` | Matches (s6:eqJbound), including "computed from `E_l(Z)`" (`cAgg`, `cFresh`, `cPP` read `run.E`, not `B`). |
| `JslcTypesStatement` | For `u ∈ Q*_Z`, the class `Y(u)` is lend-good of round `≤ l−2`, its label is `*`, `u ∈ V(Y(u))`, and `u` is in no `T_j`. Both ends of every `E_l(Z)` edge lie in `Ret_Z ∪ Q*_Z`. For a classed `u` and an edge `hu ∈ E_l(Z)`, `h ∉ V(Y(u))` and `h` is in no `T_j(Y(u),l)`. Classed port–port edges have different classes. | Step 1, the "two facts" and claim (e). The last two clauses are stated for `Q_Z` rather than `Q*_Z`, which is stronger; that is harmless and it is proved. |
| `JslcStep2Statement` | Under Γ2(a) and a valid run (no coherence needed), there are `J` and `R_Y` (indexed by `PartId`) such that `⋃B = J ⊔ ⨆_Y R_Y`. Every edge of `R_Y` is `hu` in some `E_l(Z)`, with `u ∈ Q*_Z`, `Y(u)=Y` and `h ∉ V(Y)`. Every vertex outside `V(Y)` has even degree in `R_Y` (counted over all parts). `R_Y ⊆ Bead_{Y,l}`. At most one J^hub-edge of class `Y` at each hub (the target). `|J| ≤ jBound`, and `JPlusProps J`. | Faithful to Step 2 and Step 3 ¶1. The parity clause reads "every centre has even degree in every `R_Y`" exactly, because the only vertices of `R_Y` outside `V(Y)` are its centres. The hypotheses are weaker than JS-LC's (a strengthening, and proved). |
| `JslcStep7DisjStatement` | `LJS_{Y,l,j} ∩ E_l(Z) = ∅`; classes of distinct ancestors are disjoint, and so are classes of distinct `j` of one ancestor; the `T_j(Y,l)` are pairwise disjoint and lie in `V(Y)`. | Step 7 (D) and (JC-P) disjointness. No range on `l` is needed, which is a strengthening. |
| `JslcPairsBalanceStatement` | For a PreValid system with all `Φ_j` equal: `Σ_{LayP_j} dem⁻ = Σ_{LayP_{j+1 mod k}} dem⁺` for every `j`. | Claim (a), "bijections exist". I re-derived it: hub balance gives `Σ_{ports} exc = 0` per cluster, and D_KK makes the ports of different clusters distinct. For `k=1` it gives the `X^out`/`X^in` sums because `pad ≡ 0`. |
| `JslcPairsDistinctStatement` | Out-units of `LayP_j` are distinct from in-units of `LayP_{j+1}`. | Claim (a), distinct ends. For `k ≥ 2` it follows from D_KK. For `k = 1` it follows from the sign of `exc` (pad = 0). True. |
| `JslcJointMultStatement` | For `M ≥ 2` and PreValid systems of which at most one is non-cherry: if the non-cherry system has `|exc| ≤ M−1` and `pad ≤ ⌈M/2⌉` at its ports, the cherry systems have `|exc| ≤ 1` and `pad ≤ 1`, the S₀ ports are disjoint from the cherry ports, and every vertex is a port of `≤ M−1` cherry systems, then `Σ_s junctionOcc ≤ 2M−2` (`< 2M+2`). | Claim (c), with the hypotheses taken from Steps 4, 5 and (b). True: at most one of the two terms of `junctionOcc` is non-zero for `k≥2` (by D_KK), and the sum is `|exc|` for `k=1`. The arithmetic was checked in scratch; `M ≥ 2` is necessary (scratch: at `M = 1`, `0+1 > 0`). |
| `JslcRoutingStatement` | For coherent S, a lend-good `Y` of round `≤ l−2`, `l ≤ R`, `j < M_l²`, and every finite indexed family of pairs of distinct vertices of `V(Y)` with multiplicity `≤ t^JS_l = 2M_l+2`: there are pairwise edge-disjoint paths in `LJS_{Y,l,j}` joining the pairs, with interiors in `T_j(Y,l)` and length `≤ 2^{12} L_Y^4` (log₂). | Claim (d), with the multiset reading (citDef7/remMultiset). The log base, the constants and the strictness are right. |
| `JplusFactsStatement` | For a valid run and a designation: (J3) `D_l`, `⋃F_Z`, `⋃Q*_Z` are pairwise disjoint, and a vertex outside `D_l` lies in at most one round-`l` pre-part; the 6 pairwise type exclusions; `E(H_Y) ⊆ E_{r(Y)}(Y)`; the `E_{r(Y)}(Y)` of distinct ancestors are disjoint; `u ∈ V(Y(u))` for classed `u` (`l ≥ 3`). | (J3), (i)-excl., (iii), (iv). In (iii), "the sets `E_r(Y)` (`Y` light) and `E_l(Z)` (`Z∈Std_l`)" are exactly the `E` sets of all ancestors. Faithful. |
| `HccpData.PreValid` (new Defs) | The fields of `HccpData.Valid` other than the (JC-P) ones. | I diffed it against `Valid`: `k_pos, adm, beads_G, T_disj, pad_k1, D_KK, D_KT, parityClean` are verbatim, and the dropped fields are `path_G, path_ends, path_T, starts, ends, path_edisj, pp_disj, pb_disj, bb_disj`. `bb_disj` is implied by D_KK plus `Cluster.ends_mem`. Scratch: `Valid → PreValid` by the anonymous constructor. |
| `HccpData.junctionOcc`, `IsPort` (new Defs) | `[u∈LayP_j]dem⁻(u) + [u∈LayP_{j+1 mod k}]dem⁺(u)` for `j<k`, else 0; `IsPort u` means `u` is a port of some cluster. | These match Step 6's multisets, and "depth > j" is the `j<k` guard. |

## 2. Declared inputs

- `CapPrePartStatement` (s2:lemCap (ii)) is **used**: by the "two facts", Steps 2, 3 and 8, and J⁺ (J2). Its hypotheses
  are `Gamma2a` and a valid run, which is what the TeX proof uses ("By Γ2(a), `d_l ≥ D_* ≥ 2^{117}`", deps citLem25,
  condG2, lem14tau). The TeX range `l ≤ R` is `l ∈ [1,R]`. "Every round-`l` part, light or standalone" is all
  `prePartAddrs`. The unused `τ_l` clause is omitted. It is stated as in the TeX.
- `TowerBLateStatement` (s2:lemTower (b), late clauses) is **used** in Step 8 (`ν_l ≤ 2.74n/P_{l−2}` and
  `P_{l−2} ≥ M_l^{13}`). Its hypotheses are `Gamma1core`, Valid and `d_1 ≥ D_*`, while the TeX's standing assumption is
  Γ1–Γ4. I read the proof (s2.tex 1184–1247): it uses Γ1(a)–(e) (directly and through propDegRec), Γ2 (implied by Γ1,
  s1.tex 1656), propStructure(i), lemCap(ii) and (K1) of propOV (whose statement is "Fix a valid run", with no `n` or Γ
  condition). The hypothesis set is sufficient and matches `TowerBRoundStatement`.
- Nothing that the probe must prove is hidden among the inputs. `structureHY` and `edgeLaminarity` are now proved,
  and the engine (PAR, MED, EQ-LPT, HCC-P, HCCglob) is proved in P2E. COL(b) enters only as a field of `Coherent`,
  discharged by the proved `coherent_ofOutcome`. Lovász path-connectivity is not cited by JS-LC or J⁺ directly.

## 3. Vacuity

- JS-LC and Step 2 have satisfiable non-run hypotheses. Their conclusions are non-trivial: `J = ⋃B`, `D = []` is
  refuted by J1hub or jBound as soon as a hub has two class-`Y` edges (`two_jhub_violates_J1`). A full instance needs a
  run with `R ≥ 3` (s2:propExists), which the test file correctly records as not checked.
- JointMult is non-vacuous (the tests give an `S₀` + cherry instance and sharpness when the `M−1` hypothesis is
  dropped). The conjunct `2M−2 < 2M+2` is a tautology on purpose; it records TeX's "`< t`".
- Types, Step7Disj and JplusFacts are proved. Their conclusions are partly definitional (`u ∉ T_j` for `u ∈ Q*_Z` is
  the label `*`), which is correct and not a vacuity problem.

## 4. The refutation target (J1 aggregated): manuscript check

I re-derived it by hand:
- `R^0_Y` is a single set over all `Z`, so "the centre of an odd number of edges of `R^0_Y`" is aggregated. There is
  one move per (centre, class).
- PAR deletions have both ends in `Q*_Z ⊆ Z^0 \ D_l`, so they are never J^hub (the hub is in `D_l`). They are never
  J^fr or J^lost either, since `F_Z`, `Lost_Z` and `Q*_Z` are disjoint.
- A moved edge `hu` with `h ∈ D_l` can be J^hub only at `h` and only of class `Y(u)`.

So at most one J^hub-edge of class `Y` at `h` survives. Pseudo-hubs are even by PAR, because a class-`b` port lies in
one part only. A move changes only the centre's degree in `R_Y`: the port `u ∈ V(Y)` carries no constraint in `R_Y`,
and in `R_{Y'}` (`Y'≠Y`) the edge was never present. No counterexample exists; the Spec states the target explicitly.

I also re-checked Steps 4, 5 and 8:
- eqSzeroCost holds in all three `k_0` cases.
- The pad spread is `Π_j ≤ Φ_max ≤ Φ^raw_j ≤ ½(M−1)|LayP_j|`.
- The cherry conflict degree is `m/2 + 2M − 5`.
- The Step-8 sum is `0.75 + 13.7 + 0.5 + 16.44M^{-11} ≤ 15`.

No error.

## 5. Hygiene

`python3 -I scripts/lint.py`: 0 findings. The only `sorry`s are the two `[DECLARED INPUT]` stubs
(`EG.capPrePart`, `EG.towerBLate`), and both have the required docstring form. The Spec docstrings start with the
manuscript label, and proof-internal Specs carry `[s6:lemJSLC:proof-…]` tags.

## 6. Notes (none blocking)

- **N1 (cosmetic, record).** `P2J.md` §1 "Checks run" still says "the only `sorry` warnings are the three stubs", and
  lists `structureHY` among the `sorryAx` holders. §9 and "Fix round 1" supersede this. Update it at integration.
- **N2 (cosmetic).** `JslcTypesStatement`'s last two clauses quantify over `Q_Z` (classed) and not only `Q*_Z`. This is
  a strengthening, and it is proved. Its docstring could say so explicitly.
- **N3 (note).** `JslcPairs*` / `JslcJointMult` are abstract in the systems. Stage 2 must still show that the
  `IsPathConnected` pair count of the family it builds equals `Σ_s junctionOcc` (this needs the distinct ends).
  `P2J.md` §5 already says this; I record it as a stage-2 obligation, not a Spec defect.
- **N4 (note).** `JslcStep2Statement` takes Γ2(a) and Valid rather than `RunHyp`, and no coherence. These are fewer
  hypotheses than JS-LC, which is a stronger statement; it is reported proved (sorryAx only via `capPrePart`).
  Acceptable.
- **N5 (note, consumer).** The MIX-C Spec, when written, must discharge the JSLC-USED hypothesis by class disjointness
  (COL(g), lemLent (i)), and must read `LentJS` as lying in lend-good classes of rounds `≤ l−2`. `JSLCStatement`
  provides both.
