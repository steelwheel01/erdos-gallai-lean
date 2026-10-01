# P2J review 2 (clean-room, Specs of probe P-2 part 2: JS-LC Step 6/7 checks, JS-LC, J⁺)

Reviewer: clean-room statement reviewer, round 2, 2026-09-29. Independent of review 1 (read afterwards for the
diff of findings only). Scope: `work/p2b/P2J.md` (including its "Fix round 1" section) and every file it lists:
`EG/Spec/Chain/{JSLC,JSLCSteps,JSLCRouting,JPlus}.lean`, `EG/Spec/HB/{CapPrePart,StructureHY,TowerBLate}.lean`,
the stubs `EG/Proof/HB/{CapPrePart,TowerBLate}.lean`, the proof `EG/Proof/HB/StructureHY.lean` (statement only),
the new Defs file `EG/Defs/Probe/P2J/PreSystem.lean`, `EGTest/ProbeP2J.lean`. TeX: `s6.tex` 443–666 (JS-LC, remStar,
J⁺), 390–419 (defLending); `s2.tex` 600–690 (defAncestors, lemCap), 722–760 (propStructure), 821–826 (EL), 839–930
(propOV, (K1)), 1144–1260 (lemTower (b) and its proof). Locked Defs read: `EG/Defs/Chain/{JSet,Lending,Design,
StageInst,HCCP,Cluster}.lean`, `EG/Defs/HB/{Run,Round}.lean` (pieceAddrs, prePartAddrs, partVerts, partGraph, assign,
E, anc, hubs/ports/fresh/classed, nuAnc), `EG/Defs/Expander.lean` (IsPathConnected), `EG/Defs/Walk.lean`,
`EG/Defs/Objects.lean`, `EG/Defs/Graph.lean` (card, degE, restrictEdges), `EG/Defs/Gamma/{Core,Full}.lean`,
`EG/Defs/Stage1/COL.lean` (KJS, tJS, lateRounds, COLb), `EG/Defs/Orient.lean` (IsOrientation). I edited no Lean file.

**Verdict: approve.** Every Spec back-translates to its TeX with the T0 encodings the author records (JSLC-USED,
the literal partition form, the `LentJS` index range). No statement is false, no hypothesis set is contradictory, no
conclusion is a tautology (apart from the documented conjunct `2M−2 < 2M+2`), and no probe node is hidden among
the two remaining declared inputs. Two cosmetic notes and one stage-2 note (below). No mathematical doubt about the
manuscript.

## 1. Hygiene

- `python3 -I scripts/lint.py`: 0 findings.
- `sorry` (token count per file): 0 in the seven Spec files, the Defs file, `EG/Proof/Chain/{JPlus,JSLCTypes,
  JSLCStep7}.lean`, `EGTest/ProbeP2J.lean`; `EG/Proof/HB/StructureHY.lean` 1 (in the module docstring only, "First a
  declared-input stub (`sorry`); proved in fix round 1"); `EG/Proof/HB/{CapPrePart,TowerBLate}.lean` 2 each (the
  `[DECLARED INPUT]` stub plus the word in its docstring). These two stubs are the only allowed sorries.
- Every Spec docstring starts with a manuscript label; proof-internal Specs use `[s6:lemJSLC:proof-…]` (the
  `EngineMult.lean` precedent). Headers: `module`, `public import`, `@[expose] public section` (Spec/Defs),
  `public section` (Proof).
- Scratch (compiled against the built modules, `lake env lean`, exit 0, no output; file in the session scratchpad,
  `Scratch2.lean`): (i) `((run.ancGraph G Y).restrictEdges (S.ljs Y l j)).verts = run.ancVerts G Y` and its edge set is
  `S.ljs Y l j` under `Coherent.ljs_sub`; (ii) `EG.Spec.JslcRoutingStatement` is provable in ~15 lines from
  `Coherent.colB_conn` alone. So the routing Spec is exactly COL(b) read on the record, as the author says (see C1).

## 2. Fidelity: back-translation of each statement

### `JSLCStatement` [s6:lemJSLC] + J⁺ interface
Plain mathematics. For every finite vertex type, graph `G`, reals `N_0, D_*`, run, designation `δ`, stage data `S`,
round `l`, input `B`: if `RunHyp` (Γ1, Γ3, `N0Cond`, `n ≥ N_0`, `d_1 ≥ D_*`, valid run), `δ` is a designation,
`S` is coherent, `3 ≤ l ≤ R`, and for every `Z ∈ Std_l` `B_Z ⊆ E_l(Z)` with each edge having an end in `Q*_Z`, then
there are `J ⊆ ⋃B`, `LentJS ⊆ ⋃{LJS_{Y,l,j} : Y lend-good, r(Y)+2 ≤ l, j < M_l²}` and a list `D` of cycles such that
`D` partitions `(⋃B ∪ LentJS) \ J` (each edge in exactly one cycle; cycles simple, length ≥ 3),
`|D| ≤ 126 n/M_l + 1.5 Σ_{Y ancestor, (Y,l) giant} m_{Y,l}` in ℝ, each cycle has an ancestor `Y` with all its edges in
`⋃B ∪ ⋃_{j<K^JS_l} LJS_{Y,l,j}`, `|J| ≤ RHS(eqJbound)` in ℝ, and `JPlusProps J`.

Against TeX 443–458:
- Setting and quantifier order ("Fix a valid run, a designation δ, a stage-1 outcome with its stage-2 data, and a
  round 3 ≤ l ≤ R"): `δ` before `S`, `S.Coherent` as the stage-1 facts (D-DES-1; transfers to every outcome of positive
  weight by `coherent_ofOutcome`). `RunHyp` is the s6b setting of TRIAGE §2.6; it contains more than the proof uses
  (H7), which only weakens the statement. Accepted.
- "Hypothesis: no edge of any class … has been used": dropped (JSLC-USED). The Spec gives JS-LC the whole classes, a
  stronger statement; the consumer must discharge "not used before" by disjointness. Accepted as T0 (see C2).
- "`LentJS_l ⊆ ⋃_{Y,j} LJS_{Y,l,j}`": read as the classes named in the hypothesis (lend-good, `r(Y)+2 ≤ l`,
  `j < K^JS_l`); `lendGoodAnc` is `ancestors.filter (Y.1+2 ≤ l ∧ ¬lendBad)`, `K^JS_l = Stage1.KJS = M_l²`. Stronger
  than an unrestricted union; matches the remark after the lemma ("the classes indexed by the current round l").
- "partitioned into the single edges of `J_l` and at most … cycles": `IsDecomp` (`EG/Defs/Objects.lean`: WF, the
  concatenated edge lists `Nodup`, and their set equals the given set) on `(⋃B ∪ LentJS) \ J`, with `J ⊆ ⋃B` and
  every object a `Obj.cycle`. This is the literal partition; the blueprint's `(⋃B \ J) ∪ LentJS` would let an edge of
  `J ∩ LentJS` also lie on a cycle (H2). Since `J ⊆ ⋃_Z E_l(Z)` and `LentJS ⊆ E(H_Y) ⊆ E_{r(Y)}(Y)` (disjoint from every
  `E_l(Z)`, `JslcStep7DisjStatement`, proved), `J ∩ LentJS = ∅` anyway. Cycles are cycles of `G`: their edges lie
  in `⋃B ∪ LentJS ⊆ E(G)`.
- Count: `126`, `1.5`, `n = G.card = |V(G)|`, `M_l = run.M G l ∈ ℕ`, real division, sum over
  `(run.ancestors G).filter (IsGiant · l)` of `(mY : ℝ)`; `IsGiant` reads `Bead_{Y,l}` and `γ_l = ⌊P_{l−2}/M_l⌋`
  (locked Defs, checked against s6:defDesign). This is the v6.1 statement (JSLC-G-UNDEFINED patched). The number of
  cycles is `D.length`; duplicates are impossible (`Nodup` of the edge lists, cycles have ≥ 3 edges).
- "Each cycle consists of edges of `⋃_Z B_Z` and edges of `⋃_j LJS_{Y,l,j}` for a single ancestor `Y`": literal,
  with `Y ∈ run.ancestors G` (H4; a cycle with a lent edge has a lend-good `Y` by the `LentJS` range and the
  disjointness of classes of distinct ancestors).
- (eqJbound): `jBound` (locked) is the displayed right side term by term: `c^agg_{h,l}` over `h ∈ D_l`, computed from
  `E_l(Z)` (`cAggClasses` filters `run.E`, not `B`); `Σ_{x∈F_Z} c_x(Z)`; `(M_l−1)|Lost_Z|` in ℝ; `½ Σ_{u∈Q_Z} c_pp(u)`
  over `classed` (= `Q_Z`, as written; not `Q*_Z`). Kept as a conjunct (no weakening).
- `JPlusProps` (locked, read for the interface): `types` = (i) exhaustive; `J1hub/J1fr/J1lost` filter all of `J`
  (aggregated; MULT-J1); `J2end/J2cap/J2out/J2card` = (J2) with the vestigial `1.37` dropped for the sharper bound
  the TeX itself proves; `freshCap` = (ii). (J3), exclusivity, (iii), (iv) are `JplusFactsStatement`; (v) is a law
  fact. "For every choice / Steps 3–8 delete nothing" is not encoded (D-DES-7; nothing downstream reads it).
- Not stated but derivable: `Disjoint (⋃B) LentJS` (blueprint (1)); docstring records it. Fine.

### `JplusFactsStatement` [s6:lemJplus] (J3), (i) exclusive, (iii), (iv) — proved
For a valid run and a designation: for every `l`, `D_l`, `⋃F_Z`, `⋃Q*_Z` pairwise disjoint and a vertex outside `D_l`
lies in at most one round-`l` pre-part ("exactly one" for one that lies in some: same content); no edge is of two of
the four J-types; `E(H_Y) ⊆ E_{r(Y)}(Y)` and the `E_{r(Y)}(Y)` of distinct ancestors are disjoint (ancestors = light
parts and standalone pre-parts, `Run.ancestors = parts`, so this is the TeX's "`E_r(Y)` (`Y` light) and `E_l(Z)`
(`Z ∈ Std_l`) pairwise disjoint"); for `l ≥ 3` every classed port `u ∈ Q_Z`, `Z ∈ Std_l`, lies in `V(δ_l(u))`
(`anc_l = ∅` for `l ≤ 2`, so the range is exact). Hypotheses `n ≥ N_0`, `d_1 ≥ D_*`, Γ dropped: strengthening, and
the statement is proved. Faithful.

### `JslcTypesStatement` (Step 1, "two facts", claim (e); T-avoidance) — proved
For a valid run, a designation, any `S`, `l ≥ 3`, `Z ∈ Std_l`: every `u ∈ Q*_Z` has `Y(u)` lend-good of round
`≤ l−2` (`lendGoodAnc`), `lab_{Y(u),l}(u) = *` (`none`), `u ∈ V(Y(u))`, `u ∉ T_j(Y(u),l)` for all `j` (`Tj` filters
`lab = some j`); every edge of `E_l(Z)` has both ends in `Ret_Z ∪ Q*_Z` (`Z^0 = Ret_Z ⊔ Q*_Z` with (R5)); for
`u ∈ Q_Z` and `hu ∈ E_l(Z)`, `h ∉ V(Y(u))` and `h ∉ T_j(Y(u),l)` (EL); the ends of a port–port edge have different
classes (over `Q_Z`, stronger than `Q*_Z`). Faithful; no coherence needed, which is also stronger.

### `JslcStep2Statement` (Step 2 + Step 3 ¶1; (J1) aggregated — the refutation target)
Under Γ2(a), a valid run, a designation, any `S`, `3 ≤ l ≤ R`, the JS-LC input: there are `J` and `R : PartId →
edge sets` with `⋃B = J ⊔ ⨆_Y R_Y` (five clauses), every edge of `R_Y` is `hu ∈ E_l(Z)` with `u ∈ Q*_Z`, `Y(u) = Y`,
`h ∉ V(Y)`; every `h ∉ V(Y)` has even `R_Y`-degree (aggregated over all parts, since `degE (R Y) h` counts all
class-`Y` beads at `h`); `R_Y ⊆ Bead_{Y,l}`; for every `h ∈ D_l` and `Y`, at most one `J^hub`-edge of class `Y` at `h`
in all of `J`; `|J| ≤ jBound`; `JPlusProps J`.
- The TeX's "every centre has even degree in every `R_Y`" is exactly the clause: by Step 1 (EL) every edge of `R_Y`
  has exactly one end in `V(Y)` (its port), so the vertices outside `V(Y)` with `R_Y`-edges are the centres.
- `R_Y ⊆ Bead`: `Bead` asks `h ∉ Q_Z ∨ Y(h) ≠ Y`; `h ∉ V(Y)` gives it via `IsDesignation` (`δ l h ∈ anc l h ⇒ h ∈ V(δ l h)`).
- For a junk `Y ∉ ancestors`, the structure clause forces `R_Y = ∅` (`δ l u ∈ anc ⊆ ancestors`), so the universal
  quantification over `PartId` is harmless.
- The (J1) conjunct duplicates `JPlusProps.J1hub` on purpose; its filter runs over the whole `J` (all parts containing
  `h`), and the even-degree clause is aggregated, so a per-part parity rule cannot satisfy the Spec. The target is
  stated in the form TRIAGE §4 asks for.
- Hypotheses are those Steps 1–2 use (Γ2(a) for Cap(ii) in (J2); no coherence). Faithful.

### `JslcStep7DisjStatement` (Step 7 (D), (JC-P) disjointness) — proved
For a valid run and coherent `S`, every `l`, every ancestor `Y`: `LJS_{Y,l,j} ∩ E_l(Z) = ∅` for `Z ∈ Std_l`; classes
of distinct ancestors disjoint; classes of distinct `j` of one `Y` disjoint; `T_j(Y,l)` pairwise disjoint and
`⊆ V(Y)`. No range on `l`/`Y`, stronger (classes are `∅` off-range by `ljs_eq_empty`; in particular the case
`Y = (l, Z)` of the first clause is covered). Faithful.

### `JslcPairsBalanceStatement` (claim (a), "the bijections exist")
For `PreValid` data with all padded loads equal, `Σ_{LayP_j} dem⁻ = Σ_{LayP_{j+1 mod k}} dem⁺` for every `j`.
- Faithful (uniform in `k`; for `k = 1`, `pad ≡ 0` makes the sums `Σ_{X^out} exc⁻`, `Σ_{X^in} exc⁺`).
- True (checked by hand, not only "by MED(b)"): an admissible orientation is an orientation of the beads
  (`IsOrientation`: arcs are directed beads, ends in `V(𝒦)`) balanced at every hub, so `Σ_{u ∈ U_𝒦} exc(u) = Σ_{V(𝒦)}
  (d⁺ − d⁻) = 0` for each cluster; under `D_KK` each `u ∈ LayP_j` is a port of exactly one cluster and `pexc u` is
  its excess there; hence `Σ_{LayP_j} exc⁻ = Σ_{LayP_j} exc⁺`, and `Σ dem⁻ = Σ dem⁺ = Φ_j = Φ_{j+1}`.

### `JslcPairsDistinctStatement` (claim (a), distinct pair ends)
For `PreValid` data: an out-unit `u ∈ LayP_j` (`dem⁻(u) > 0`) and an in-unit `v ∈ LayP_{j+1 mod k}` (`dem⁺(v) > 0`)
are different. Faithful; true: for `k ≥ 2` the layers differ, and `D_KK` forbids a port of two clusters; for `k = 1`,
`pad = 0` gives `exc(u) < 0 < exc(v)`. Membership in `V(Y) \ ⋃T` is in `JslcTypesStatement`.

### `JslcJointMultStatement` (claim (c), joint multiplicity — P2E hand-off)
For `M ≥ 2` and `PreValid` systems `Sys_s` marked cherry or not, with: at most one non-cherry system; at its ports
`|exc| ≤ M−1`, `pad ≤ ⌈M/2⌉`; at cherry ports `|exc| ≤ 1`, `pad ≤ 1`; no port of the non-cherry system is a cherry
port; every vertex is a port of at most `M−1` cherry systems: `Σ_s junctionOcc(Sys_s, j, v) ≤ 2M−2 (< 2M+2)` for all
`j`, `v`.
- The hypotheses are exactly the Step 4/5 and claim (b) facts the TeX invokes ("`|exc(u)| ≤ M_l−1`",
  "`pad(u) ≤ ⌈(M_l−1)/2⌉ ≤ ⌈M_l/2⌉`", "`pad ≤ 1`" and `exc = ±1` at cherry ports, "never of both", "at most `M_l−1`
  cherry systems"). The pad bound is the weaker `⌈M/2⌉` (the one used in (c)), fine.
- True: per system, `junctionOcc ≤ max(dem⁻, dem⁺) ≤ |exc| + pad` (for `k ≥ 2` a port is in one layer, `D_KK`; for
  `k = 1` it is `|exc|`), so `≤ (M−1) + ⌈M/2⌉ ≤ 2M−2` for `𝒮_0` (`⌈M/2⌉ ≤ M−1` iff `M ≥ 2`) and `≤ 2(M−1)` summed
  over cherry systems; the two kinds share no port. `Σ_s junctionOcc` is the multiplicity of `v` in `𝔓_j(Y,l)` once
  the pairs have distinct ends (`JslcPairsDistinctStatement`); systems of depth `≤ j` contribute `0`.
- `2M−2 < 2M+2` is a tautology recording "`< t = 2M_l+2`" (`t^JS_l = 2M_l+2` is `EG.tJS_eq_two_mul_add_two`).
- The sharpness test (three cherry systems through one port, `M = 2`) shows the cherry-count hypothesis is needed.

### `JslcRoutingStatement` (claim (d))
For coherent `S`, `Y ∈ lendGoodAnc l`, `l ≤ R`, `j < K^JS_l`, every finite indexed family of pairs of distinct
vertices of `V(Y)` with each vertex in `≤ t^JS_l` pairs: pairwise edge-disjoint paths in `LJS_{Y,l,j}`, one per pair,
through `T_j(Y,l)`, of length `≤ 2^{12} L_Y^4`. This is Definition 7 (with the multiset clause, s3:remMultiset) for
the class as a graph on `V(Y)`, and lemMonotone(iii) is automatic (all families quantified). It is COL(b) on the
record (`Coherent.colB_conn`; `¬lendBad ⇒ colB`, `Y.1+2 ≤ l ≤ R ⇒ l ∈ lateRounds`); scratch check §1 (ii).
Faithful.

### New Defs `EG/Defs/Probe/P2J/PreSystem.lean`
- `IsPort S u := ∃ i, u ∈ (S.K i).ports` — "a port of the system". Faithful.
- `junctionOcc S j u := if j < k then [u ∈ LayP_j]·dem⁻(u) + [u ∈ LayP_{succ j}]·dem⁺(u) else 0`: the number of
  copies of `u` in the two multisets of Step 6 (junction-`j` pairs exist only for depth `> j`). For `k = 1`,
  `succ 0 = 0` and `pad = 0` (`PreValid.pad_k1`) give `exc⁻ + exc⁺ = |exc|`, the `X^out`/`X^in` clause. Faithful.
- `PreValid`: I diffed it against the locked `HccpData.Valid`: same fields `k_pos, adm, beads_G, T_disj, pad_k1,
  D_KK, D_KT, parityClean` with identical bodies and quoted text; omitted are the (JC-P) fields `path_G, path_ends,
  path_T, starts, ends, path_edisj, pp_disj, pb_disj` and `bb_disj`. `bb_disj` is implied by `D_KK` (a bead of two
  clusters would have an end in both vertex sets). The docstring says "the fields other than those of (JC-P)";
  strictly it also drops `bb_disj`, which is harmless (cosmetic, see C3). `Valid → PreValid` is checked field by
  field in the tests.

### Declared inputs (each really used; stated as in the TeX; nothing hidden)
- **`CapPrePartStatement` [s2:lemCap](ii).** Under `Gamma2a` and a valid run, for `l ∈ [1,R]`: every `s = 0` piece
  has `≤ M_l` vertices (`pieceAddrs = tree0.leafAddrs`, the leaves of the `s = 0` recursion, `piece.card` = vertex
  count — the TeX's "`s = 0` piece" is a stopped piece, an expander, i.e. a leaf; internal nodes are not claimed,
  which matters since the root has `n` vertices); every pre-part has `|Z^0| ≤ M_l` (`prePartAddrs` = leaves of the
  two-level recursion with `≥ P_l` vertices); every vertex has `degE (E_l(Z)) v ≤ M_l − 1` for every pre-part `Z`
  (the TeX's "part (light or standalone)"; `E_l(Z)` is per pre-part address). The `τ_l` clause is omitted (unused).
  `Gamma2a` is the standing assumption the proof names ("By Γ2(a) … `d_l ≥ D_* ≥ 2^{117}`"). Cited by JS-LC ("two
  facts", Steps 2, 3, 8) and (J2). Upstream s2 (needs `EG.bmLemma25`), not a P-2 node; `Cap.lean` has only (i), the
  remark and the graph-level step. Correct declared input.
- **`TowerBLateStatement` [s2:lemTower](b), late clauses.** Under `Gamma1core`, a valid run, `D_* ≤ d_1`, for
  `3 ≤ l ≤ R`: `M_l^{13} ≤ P_{l−2}` (ℕ) and `ν_l ≤ 2.74 n/P_{l−2}` (ℝ; `nuAnc l = #{Y ancestor : r(Y)+2 ≤ l}`). Matches
  TeX 1156–1162; same hypothesis shape as `TowerBRoundStatement` (P4A). I checked the proof's needs: the
  `P_{l−2} ≥ M_l^{13}` chain uses propDegRec and Γ1(c); the `ν_l` bound uses (K1) of propOV (lemOVgeneric on the
  two-level recursion, `|Z^0| ≥ P_r`, and Cap(ii) for `τ_r ≥ 128 s_r log²|𝒫|`, which needs Γ2(a)) and
  `P_r ≥ 2P_{r+1}` (Γ1). `Gamma1core ⇒ Gamma2a` is `EG.Gamma1core.gamma2a`, so the stub's hypotheses cover the
  proof; nothing uses `n ≥ N_0`. Cited by Step 8. Upstream. Correct declared input.
- **`StructureHYStatement` [s2:propStructure](iii), clauses used.** No longer an input: proved from `run.Valid` alone
  (fix round 1, R1 of review 1). Statement: `E(H_Y) ⊆ E_{r(Y)}(Y)`, `E_{r(Y)}(Y) ⊆ V(Y)^{(2)}`, the `E_{r(Y)}(Y)`
  and the `E(H_Y)` of distinct ancestors pairwise disjoint. Faithful to the quoted clauses.
- **Nothing hidden.** Lemma EL is `EG.edgeLaminarity` (proved, P3A); COL(b), defCOL(i)–(iv) are `Coherent` fields
  discharged by `coherent_ofOutcome` (proved); propStructure(iv) is in Lib (proved); Lovász path-connectivity is not
  cited by JS-LC/J⁺ (only inside COL(b)); the greedy colouring and PAR/MED/EQ-LPT/HCC-P/HCCglob are proved engine
  nodes or stage-2 Lib. The Step 2/6 checks that the probe must prove (`JslcStep2`, `PairsBalance`, `PairsDistinct`,
  `JointMult`, `Routing`) are Specs without stubs, so they cannot be silently assumed.

## 3. Vacuity

- Round-level Specs (`JSLCStatement`, `JslcStep2Statement`, `JslcRoutingStatement`, `TowerBLateStatement`) need a valid
  run with `R ≥ 3` under Γ1, which no test exhibits (project-wide gap, s2:propExists; documented in §7 of the note).
  The non-run hypotheses are shown satisfiable (`exists_isDesignation`, `exists_coherent`, `B_Z = ∅`), and the
  conclusions are shown consistent (`J = LentJS = ∅`, `D = []`, `R_Y = ∅`).
- Non-trivial conclusions: `J := ⋃B, D := []` is not a witness in general (`J1hub`, `J1fr`, `jBound` bind as soon as a
  centre carries two class-`Y` edges; `two_jhub_violates_J1`).
- `PreValid`-level Specs are instantiated on `S1`, `S2` (hypotheses and conclusions hold); the sharpness example shows
  the cherry-count hypothesis is not idle.
- Proved Specs: hypotheses met by the run without rounds; conclusions are disjointness/membership facts, not
  tautologies.
- The only trivially true conjunct is `2M−2 < 2M+2` (documentation of "`< t`").

## 4. Findings

- **C1 (cosmetic, note).** `JslcRoutingStatement` follows from `Coherent.colB_conn` in a few lines (scratch, §1). This
  is expected — claim (d) *is* COL(b) applied to the record — and it is the right shape for stage 2 (it packages
  the `restrictEdges` unfolding once). No change.
- **C2 (note; carried from review 1 C4).** The JSLC-USED encoding hands "no edge … has been used" to the consumer.
  `EG/Spec/Chain/` still has no MIX-C/lemLent Spec; its author must discharge it by disjointness (COL(g), lemLent (i)).
  Cannot be checked now.
- **C3 (cosmetic).** `PreValid`'s docstring says "the fields of `HccpData.Valid` other than those of (JC-P)"; it also
  omits `bb_disj`, which is implied by `D_KK`. One clause in the docstring would make the diff exact. No statement
  change.
- **C4 (cosmetic, documentation).** `P2J.md` §1 and §3 still describe `structureHY` as a stub/declared input; the
  "Fix round 1" section supersedes them and says so. Fine as is; the integrator may want the tables updated.
- **N1 (stage-2 note, H5/C3 of review 1).** The proof-internal Specs `JslcJointMult`, `JslcPairsBalance`,
  `JslcPairsDistinct`, `JslcStep2` hypothesise the Step 4/5 construction (`|exc| ≤ M−1`, `pad ≤ ⌈M/2⌉`, cherry
  `pad ≤ 1`, claim (b), equal padded loads). If stage 2 builds the systems differently they must be re-reviewed before
  locking; they have no consumer outside JS-LC.

## 5. Refutation target (P-2): two `J^hub` edges of one class at one hub in one round

- Stated correctly and visibly: conjunct `∀ h ∈ D_l, ∀ Y, #(J.filter (IsJhubEdge l h Y)) ≤ 1` of `JslcStep2Statement`
  (filter over the whole `J`), also `JPlusProps.J1hub` in `JSLCStatement`, jointly with the aggregated even-degree
  clause of the `R_Y`.
- The typed predicate cannot be met spuriously: `IsJhubEdge` needs `h ∈ A_Z ⊆ D_l`, `u ∈ Q*_Z ⊆ Z^0 \ D_l`, `e ∈ E_l(Z)`,
  `Y(u) = Y`; a PAR deletion is port–port and never qualifies; roles cannot swap.
- Hand check of the TeX: a hub is never a port; its class-`Y` centre degree is aggregated over all parts containing it;
  one move iff odd; a move at `(h', Y')` is a `J^hub` edge of class `Y` at `h` only if `h' = h` and `Y' = Y`. So at most
  one. The per-part variant (odd in `Z_1` and in `Z_2`) is exactly what the aggregated clauses exclude. The test
  `two_jhub_violates_J1` shows the conjunct rejects two such edges from the same or different parts.
- Joint multiplicity, distinct pair ends and T-avoidance are stated in `JslcJointMult`, `JslcPairsDistinct`,
  `JslcTypes` (proved) and `JslcStep7Disj` (proved).

## 6. Mathematical doubts about the manuscript

None. Independently re-derived: Step 1 (EL); Step 2 (pseudo-hubs even by PAR and in one part; moves change only the
centre's class degree; each eqJbound term, using `|J'| ≤ |V(E_ab)|/2` from lemPAR and the `c_pp` count); Step 3
(`R_Y ⊆ Bead`, centre degree `≤ d_{Y,l}(h) ≤ m_{Y,l}`, port degree `≤ M_l−1`); Step 4 (`Φ ≥ 1`; `k_0 ≤ #clusters`;
`Φ^raw_j ≥ Φ_max ≥ Π_j` from EQ-LPT and `k_0 ≤ ΣΦ/(2Φ_max)`; `pad ≤ ⌈(M−1)/2⌉` from `Π_j ≤ ½(M−1)|LayP_j|`; the three
cases of eqSzeroCost); Step 5 (conflict degree `m/2 + 2M − 5`; `⌈η/⌊η/2⌋⌉ ≤ 3` for `η ≥ 4`; eqCherryCost;
`sc ≤ (1.5m − 12)^+`); claims (a)–(e), including `Σ_{U_𝒦} exc = 0` for every admissible orientation; Step 7 (D), (P),
(JC-P); Step 8 (`0.75 + 13.7 + 0.5 + 16.44 M^{-11} ≤ 15` for `M ≥ 2^{40}`, with `γ_l ≤ P_{l−2}/M_l`,
`ν_l ≤ 2.74n/P_{l−2}`, `P_{l−2} ≥ M_l^{13}`). The only wording items are the ones already on record: the vestigial
`1.37` in (J2), and "`𝒮_0(Y,l)` (if non-empty)" for the case without non-giant components (P2E H7, EQ-USE-EMPTY-S0).
