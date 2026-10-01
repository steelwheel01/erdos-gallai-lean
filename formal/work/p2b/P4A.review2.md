# P4A: clean-room review, round 2 (re-dispatch, 2026-09-29) — Specs of probe P-4, part 1: PV(c) core and COL-JV rows 4, 7, 8

Reviewer: clean-room Spec reviewer, round 2. I worked from the TeX (v6.1), the locked Defs, the P4A
Defs/Spec/Proof/EGTest files and `work/p2b/P4A.md`; the two earlier review files were opened only
after my own back-translation was finished, to keep the issue numbering comparable. No Lean file of
the repo was edited. My scratch checks are in
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/P4AScratchR2.lean`
(outside the repo; `lake env lean` rc=0, 0 errors). The proof being formalized is a CANDIDATE
proof, reviewed by AI only; nothing here calls the conjecture solved.

Files reviewed in full:
- NEW DEFS `EG/Defs/Probe/P4A/PVHyp.lean` (`EG.Vortex.PVE1'`, `PVHyp`, `PVAdm`);
- Specs `EG/Spec/Vortex/{Observations, PVCore, PV}.lean`, `EG/Spec/Lend/{COLJVRows, COLJVCount}.lean`,
  `EG/Spec/Ext/Cor22.lean`, `EG/Spec/HB/TowerB.lean`;
- Proofs/stubs `EG/Proof/Vortex/PVCore.lean`, `EG/Proof/Lend/COLJVRows.lean`,
  `EG/Proof/{Ext/Cor22, HB/TowerB, Lend/COLJVCount}.lean`;
- `EGTest/ProbeP4A.lean`.

Locked Defs read for the back-translation: `EG/Defs/{Objects, Walk, PathDecomp, Graph, Vortex}.lean`,
`EG/Defs/Vortex/PVData.lean`, `EG/Defs/Link/HBFamily.lean`, `EG/Defs/Stage1/COL.lean`
(`lateRounds`, `IU/IJS/IJV`, `klend`, `JY`, `kown`, `pY`, `tY`), `EG/Defs/Stage1/Zones.lean`
(`rhoY`), `EG/Defs/HB/{Round, Run}.lean` (`lamOf`, `MOf`, `LamOf`, `sOf`, `POf`, `prePartAddrs`,
`isL1`, `isLight`, `partVerts`, `Valid`, `parts`/`ancestors`, `ancS`, `LY`), `EG/Defs/Gamma/{Core,
Full}.lean`, `EG/Defs/Lend/COLTable.lean`, `EG/Spec/Found/EG0.lean` (`FactEG0bStatement`).

TeX compared: `s4.tex` 20–160 (convVortex, (S), (E), (C)), 395–642 (Lemma PV and proof, CR1-PV
remarks), 320–345 (TPV (P3), cited by the PV proof); `s3.tex` 1041–1160 (defCOL, Table tabCOLJV),
1185–1352 (Lemma COL-JV and proof), thmT16s statement; `s2.tex` 600–630 (defAncestors), 1144–1175
(lemTower); `s1.tex` 635–650 (factEG0), 1015–1035 (citThm21, citCor22), 1644–1660 (condG2).

## Verdict: APPROVE

- Every Spec and every new Defs item back-translates to the quoted TeX (section 1). The only
  deviations are the four recorded T0 encodings (deterministic PV, loopless edge sets, `PVSize`
  for `N ≥ N_0`, row 7 with `(12L_Y^5)^3` for `ρ^{-3}`) and true, harmless strengthenings
  (rows 4/7 for standalone `Y`; free `N` in the finish; `∀ x : V` in PV (c); `8|Pl_J|` instead of
  `16|Pl|`). No statement is weakened.
- No hypothesis set is contradictory, and no conclusion is trivially true where the TeX has
  content (section 2). Non-vacuity witnesses in `EGTest/ProbeP4A.lean` re-checked by reading; two
  small facts re-proved in my scratch file.
- The three declared inputs are exactly what the manuscript proof cites, stated as in the TeX; no
  probe node hides among them (section 3).
- `python3 -I scripts/lint.py`: 0 findings; `sorry` only in the three `[DECLARED INPUT]` stubs
  (section 4).
- The docstring-only fixes of the round-1 re-dispatch (m1, c2, c3) are in place (section 0).
- Remaining issues are cosmetic (section 6). Math findings: no T1–T3; the T0 encodings are
  listed in section 7.

## 0. Fixes of the round-1 re-dispatch (docstrings only)

| Issue | Claimed | Verified |
|---|---|---|
| m1 (`PVArcEndsDegStatement` is a general fact; refutation role overstated) | docstring of the statement names the P4B comparisons; TRIAGE note for the orchestrator | Yes: the docstring of `PVArcEndsDegStatement` in `EG/Spec/Vortex/PVCore.lean` now ends with the paragraph "Scope as refutation target …" naming the per-bundle multiplicity and `|Z| − 1 ≤ M_l − 1 < t_Y` (s5:lemParent Step 5) as P4B nodes. The statement body is unchanged. |
| c2 (redundant `Λ_r ≤ 2λ_r` in the per-ancestor conjunct of `TowerBRoundStatement`) | recorded in the module docstring | Yes (last bullet of the "Formal reading"). Body unchanged; the redundancy is harmless. |
| c3 (`PVStatement` placement) | module docstring says the s4 owner adopts the file | Yes ("Ownership (review P4A.review1 re-dispatch, c3) …"). |
| c1, c4 (arc `≥ 1` edge; rows for standalone `Y`) | no change | Agreed (see 1.3 and 1.5). |

I confirmed by reading that no `def …Statement` body and no Defs file differs from what the two
earlier rounds approved (the diff to the round-1 files is in docstrings only, as P4A.md states).

## 1. Fidelity (independent back-translation)

### 1.1 New Defs (`EG/Defs/Probe/P4A/PVHyp.lean`)

- **`PVE1' D`**: for every `w ∈ Pl`, `L^5/8 ≤ #{u ∈ A(w) : s(w,u) ∈ E(M) ∧ ext u = none}` (real).
  TeX: "`C_w := {wu : u ∈ A(w), wu ∈ E(M), ext(u) = *}` … (E1′) `|C_w| ≥ L^5/8` for every
  `w ∈ Pl`". For fixed `w`, `u ↦ s(w,u)` is injective, so counting far ends is counting `C_w`.
  `none` = `*` (PV-EXT-ENCODING). Faithful.
- **`PVHyp D`** = `PVSize |Z|` ("`N ≥ N_0`", locked TPV-SIZE-PRED: `N0Cond N0 → N0 ≤ N → PVSize N`)
  ∧ `V(O) = Z` ∧ `O` a `(2^{-6}, s_O)`-expander ∧ `2m ≤ s_O` ∧ `IsHBFamily O m b A`
  ("`A(w) ⊆ N_O(w)` (`w ∈ Z`) with `|A(w)| = m` such that every vertex lies in at most `b` of
  them": the `IsHBFamily` count is over `w ∈ V(O) = Z`, and `∀ u : V` is equivalent to
  `∀ u ∈ Z` since `A w ⊆ N_O(w) ⊆ Z`) ∧ every `R_{j,c}` and `M` spanning `Z` and
  `(2^{-6}, s')`-expanders ∧ `2^{145}L^{41} ≤ s'` ∧ `R`'s pairwise edge-disjoint ∧ each `R`
  edge-disjoint from `M` ∧ `Rt ∩ Pl = ∅` ∧ `Rt ∪ Pl = Z` ∧ (E1′). This is the data list of
  s4:lemPV item by item, with `m = pvM N = ⌈L^6⌉`, `b = pvB N = ⌈2^7L^2m⌉`, `J = pvJ N` (index type
  `Fin (pvJ Z.card) × Fin 4`, PV-OWNCLASS-INDEX). One `s'` for all own classes, as the TeX writes
  one `s'`. `ext` unconstrained, as in the TeX. Faithful.
- **`PVAdm D H_0`**: loopless ∧ both ends in `Z` ∧ `E(M) ⊆ H_0` ∧ `∀ i, E(R_i) ⊆ H_0`. TeX: "every
  edge set `H_0` all of whose edges have both ends in `Z` and which contains `E(M)` and every
  `E(R_{j,c})`". Looplessness is the recorded T0 convention (CONVENTIONS "Objects and f"; T0-eg0-loop
  analogue). Faithful.

### 1.2 Observations (`EG/Spec/Vortex/Observations.lean`)

- **`TrailSplitStatement`**: `T ≠ []` (`q ≥ 0`), `(walkEdges T).Nodup` ("pairwise distinct
  edges"), no loop among the edges ("in a simple graph"; the only use of simplicity in the TeX
  proof is "`i' − i = 1` would be a loop"). Conclusion: cycles `C` with `(Obj.cycle c).WF`
  (distinct vertices, `≥ 3`: "each of length at least 3"); `|C| ≤ T.length − |T.toFinset|`
  (= `rep(T)`; the right side never exceeds the left, so `ℕ`-subtraction is exact); the
  concatenated edge lists of the pieces are a `List.Perm` of `walkEdges T` ("`E(T)` is the disjoint
  union of the edge sets", exact since `walkEdges T` is duplicate-free); `p.isSome ↔ head ≠ last`
  ("the path is present iff `x_0 ≠ x_q`"); the path is nodup with `≥ 2` vertices and the same
  first/last vertex as `T` ("its ends are `x_0` and `x_q`"; fixing the orientation is a harmless
  strengthening that the TeX proof gives); all piece vertices in `T`. Faithful.
- **`TrailRepInnerStatement`**: `(interior T).Nodup → T.length − |T.toFinset| ≤ 2`. TeX: "if the
  inner vertices `x_1,…,x_{q−1}` are pairwise distinct, then `rep(T) ≤ 2`". No trail hypothesis
  is needed (the TeX proof uses only `|{x_0,…,x_q}| ≥ q − 1`). I re-proved it in the scratch file
  (`|T.toFinset| ≥ |(interior T).toFinset| = T.length − 2`). Faithful; true.
- **`PathEndsParityStatement`**: `IsPathDecomp ↑F P → ∀ v, pec(P,v) % 2 = deg_F(v) % 2`. Literal
  first sentence of (E) ("(non-trivial) paths" = `2 ≤ p.length` in `IsPathDecomp`). Faithful.
- **`PathEndsCountStatement`**: + `∀ v, pec ≤ 2` + all edge ends in `W` ⇒ `|P| ≤ |W|`. Literal
  second sentence. Faithful.
- **`ClosingStatement`**: `Q` nodup, `pathLength Q ≥ 2`, from `x` to `y`; `Q'` nodup from `x` to
  `y`; `interior Q'` avoids `Q`; edge lists disjoint. Conclusion: `Q ++ (interior Q').reverse` is a
  well-formed cycle whose `cycleEdges` are a `Perm` of `walkEdges Q ++ walkEdges Q'`. "`x ≠ y`"
  follows from `Q` nodup with `≥ 3` vertices; "length at least 3" is the `WF` clause `3 ≤ length`.
  The edge-disjointness hypothesis is redundant for the list-level conclusion (it is implied by the
  other hypotheses) but faithful to the TeX. Faithful.

### 1.3 PV(c) core (`EG/Spec/Vortex/PVCore.lean`)

- **`PVStepPhaseStatement`** (steps (iv)–(vi) of one phase `c` of step `j`, and "Cost of step `j`").
  Hypotheses: `Rt`, `W = W_j`, `Up = Pl ∩ U_{j+1}` pairwise disjoint (so `U_j = Rt ⊔ W ⊔ Up`,
  `U_{j+1} = Rt ⊔ Up`); `F = F_{j,c}` loopless, inside `U_j` ((Inv1)), every edge meets `W`
  (definition of `F_j`); `P = Paths_{j,c}` a Corollary-22 decomposition; far ends `u₁ w ≠ u₂ w` in
  `U_{j+1}` ("eight distinct edges … `u ∈ Z_j ⊆ U_{j+1}`") with `s(w,u_i w) ∉ F` (`F_{j,c}` is
  non-reserved). Conclusion: objects `D` well formed; `D`, `A`, `Q` edge lists duplicate-free and
  together exactly `F ∪ {reserved edges}` ("The edges used at step `j` are exactly the edges of
  `F_j` …" restricted to phase `c`; connector edges are outside this statement); arcs nodup with
  `≥ 1` edge, both ends in `Rt`, every vertex in `V(F)` or a far end, `|A| ≤ |P|` ("each arc of
  phase `c` comes from a distinct path of `Paths_{j,c}`"); `Q`-paths satisfy (P2), (P3), have
  vertices in `V(F) ∪ W ∪ {far ends}` (the input of (P1)), and (P4) in the form
  `pec(Q,v) ≤ 2 + #{w ∈ W : v ∈ {u₁ w, u₂ w}}` (the far-end count that `b` bounds once
  `u_i w ∈ A(w)` is known, which is the composition's business); cost
  `|D| + |Q| ≤ |W| + 3(2|W| + 2|Up|)` (single edges `≤ |W|` per phase; type-(1) trails `≤ 2|W|`,
  type-(2) trails `≤ 2|Up|`, each `≤ 3` objects; the remaining trails become arcs and cost
  nothing). I re-derived every clause from the TeX procedure, including:
  - trails have pairwise distinct inner vertices and edges (reserved edges of distinct `w` are
    distinct since `u_i w ∉ W`; `s(w,u₁ w) ≠ s(w,u₂ w)`; reserved edges are not in `F`);
  - (P3) `pathLength ≥ 2` for the `Q`-paths: a remainder of length `1` after splitting would be an
    `F`-edge between two far ends or between a far end and a non-`W` end, but every `F`-edge meets
    `W` and far ends and non-`W` ends lie in `Rt ∪ Up`. This is the TPV argument the PV proof cites
    ("each of its edges meets `W_j`", s4.tex 328);
  - (P4): a trail end at `v` is a `P`-end outside `W` (`≤ 2`) or the far end of one reserved edge
    per `w` with `v ∈ {u₁ w, u₂ w}` (`u₁ w ≠ u₂ w`, each reserved edge in at most one trail).
  The arc clause `2 ≤ a.length` (`≥ 1` edge) is the PV (b) form ("paths of length at least 1"),
  not (P3); this was c1 of the earlier round 2 and is deliberate (finish arcs can have one edge and
  the composition only uses (b)). The cherry note m2 of round 1 stands: the vertex clause admits a
  cherry centre `w` only when `w ∈ V(F_{j,c})`, where (s4:eqPVclass) gives `ext(w) ≠ c`; `|A| ≤ |P|`
  binds either way. Faithful (as an existence statement carrying exactly the properties the PV
  proof uses).
- **`PVStepCostStatement`**: `4|W| + 12(2|Up| + 2|W|) ≤ 28|W ∪ Up|` for disjoint `W`, `Up`. Literal
  (s4:eqPVstep) with `W_j ⊔ (Pl ∩ U_{j+1}) = Pl ∩ U_j`. Proved (`EG.pvStepCost`).
- **`PVtStatement`**: under `2^{10} ≤ L`: `2 + b ≤ 2^7L^8 + 2^7L^2 + 3 ≤ 2^9L^8` with
  `b = pvB N`. Literal (s4:eqPVt) (the display has exactly these two inequalities; the fixes note's
  "second inequality deleted" refers to the former conjunct `8J + 8 + b ≤ …`, round-1 c3). Proved
  (`EG.pvT`).
- **`PVStripStatement`**: `Rt ∩ Pl_J = ∅`; `T` a path (`nodup`, `≥ 2` vertices) with vertices in
  `Rt ∪ Pl_J` and every edge meeting `Rt` (an `E_2`-path); conclusion: stripped edges `S` and an
  infix `T'` with `S ++ E(T') ~ E(T)`, `|S| ≤ #(ends of T in Pl_J)`, and `T'` has `≤ 1` vertex or
  `≥ 2` vertices with both ends in `Rt`. This is the TeX sentence "After stripping at the ends of
  `T` lying in `Pl_J`, what remains of `T` has no edges or is a path of length at least 1 with two
  distinct ends in `Rt`". I re-derived the three cases (`p x`, `p x q`, longer paths: the
  neighbour of an end in `Pl_J` is in `Rt` because the edge meets `Rt` and `Pl_J ∩ Rt = ∅`; both
  ends in `Pl_J` with `|T| = 2` is impossible). Faithful.
- **`PVFinishStatement`**: `2^{10} ≤ L(N)` (size condition (i), giving `N > 1` and `4·64 ≤ L`, the
  hypotheses of Fact EG0(b)); `|Pl| ≤ N` (`α := |Pl| ≤ N`); `Pl_J ⊆ Pl`; `Rt ∩ Pl = ∅`;
  (G5) `|Pl_J| ≤ 64|Pl|/L`; `H_J` loopless inside `Rt ∪ Pl_J` ((Inv1) at `J`). Conclusion:
  `Hobj ⊆ H_J` decomposed into `≤ 64|Pl| + 8|Pl_J|` objects (EG0(b) gives `≤ βα = 64|Pl|`, stripping
  `≤ 2|Pl_J|` per phase, `8|Pl_J|` total, the TeX's own tighter figure), the rest path-decomposed
  into phased arcs with ends in `Rt` and `ext ≠` phase on every vertex, `≤ 4|U_J|` arcs ((c):
  "at most `|U_J| ≤ N` arcs per phase by (E)"), and `Pl_J = ∅ → Hobj = ∅` ((d)). I checked the
  shape against `EG.Spec.FactEG0bStatement` (real `N`, `α`, `β`; the free natural `N` here is cast):
  it applies with `N := N`, `α := |Pl|`, `β := 64`, `W := Pl_J`, `F := E_1`. Faithful; the free
  `N` (H6) is a harmless generalization.
- **`PVArcEndsDegStatement`**: `H_0` loopless inside `Z`, `H^arc ⊆ H_0`, arcs a path decomposition
  of `H^arc` ⇒ `∀ x, pec(arcs,x) ≤ deg_{H_0}(x) ∧ deg_{H_0}(x) ≤ |Z| − 1`. Literal (c) with its
  proof ("An arc with end `x` contains exactly one edge at `x` … distinct arcs are edge-disjoint …
  distinct edges at `x` have distinct other ends"). `∀ x : V` is a harmless strengthening
  (`deg = 0` off `Z`); `ℕ`-subtraction is exact (scratch check: `Z = ∅` forces `H_0 = ∅`).
  Faithful. Its role as refutation target is correctly qualified in the docstring (round-1 m1).

### 1.4 Anchor `PVStatement` (`EG/Spec/Vortex/PV.lean`; not a P4A node)

`∀ D, PVHyp D → ∀ H_0, PVAdm D H_0 → ∃ Hobj Dobj arcs, Hobj ⊆ H_0 ∧ (a) IsDecomp Hobj Dobj ∧
|Dobj| ≤ 369|Pl| ∧ (b) IsPathDecomp (H_0 \ Hobj) arcs ∧ ends in Rt ∧ ext ≠ phase on every vertex
∧ (c) |arcs| ≤ 4(J+1)N ∧ pec ≤ deg_{H_0} ∧ deg_{H_0} ≤ N − 1 ∧ (d) Rt = ∅ → arcs = [] ∧ Pl = ∅ →
Hobj = ∅`. (a)–(d) are literal (`IsPathDecomp` = "pairwise edge-disjoint paths of length at least
1, each with two distinct ends"; `H^arc = H_0 \ Hobj` is the partition). The deterministic form is
the recorded T0 decision PV-DET-SPEC (TRIAGE §2.8): the TeX conclusion is label-free and
`P(𝒢_PV) ≥ 1/2 − η_PV > 0`, so the TeX implies this form, and the consumers use only
non-emptiness. Faithful under that decision.

### 1.5 COL-JV rows (`EG/Spec/Lend/COLJVRows.lean`)

Context of all three: `Gamma1 D → run.Valid G D → ∀ Y ∈ run.ancestors G` (TRIAGE §2.6:
"s3 COL/COLJV take `Gamma1 D ∧ run.Valid G D`"; lemma: "Assume condition Γ1. Let `Y` be an
ancestor of round `r ≤ R`").
- **Row 4** (`Y.1 + 2 ≤ R`): `2^{135}·t_Y·L_Y^{28}·(12L_Y^5)^5 ≤ s_Y/(8k_lend)` with
  `t_Y = Stage1.tY = ⌈λ_r^{1.6}⌉₊`, `s_Y = run.ancS` (`s_r/2` light, `s_r` standalone,
  s2:defAncestors), `k_lend = Stage1.klend`. Literal column 2. Under the guard `k_lend ≥ 1`
  (`|I^JV| = R − r − 1 ≥ 1`; scratch check), so the real division is never junk. Scope "for
  `r ≤ R − 2`" is the lemma's ("Rows 4–7 … asserted for `r ≤ R − 2`"); no light guard, as the lemma
  has none; for standalone `Y` the inequality is true (`s_Y = s_r ≥ s_r/2`) by the same derivation
  (H4). Faithful (a harmless strengthening for standalone `Y`).
- **Row 7** (`Y.1 + 2 ≤ R`): `Σ_{i ∈ I^U(Y)} 2^{86}·t_Y·L_Y^{19}·(12L_Y^5)^3·N^{-3} ≤ N^{-2}/4`,
  `N = |V(Y)|`, integer powers. Column 2 says "T16* failures over `I^U(Y)` sum to at most
  `|V(Y)|^{-2}/4`"; the per-class failure of Theorem 16* is `2^{86} t L^{19} ρ^{-3} N^{-3}`
  (s3:thmT16s, checked), and the row's own derivation substitutes `t = t_Y` and
  `ρ^{-3} ≤ 1728L_Y^{15} = (12L_Y^5)^3`. So the Spec is the manuscript's sufficient form (T0 record
  H3); the consumer combines it with `ρ_Y ≥ 1/(12L_Y^5)` through the proved bridge
  `EG.colJVRow7_rhoY`. For standalone `Y` the sum is empty (`I^U = ∅`) and the statement is trivially
  true, as in the TeX. Faithful.
- **Row 8** (every ancestor): (a) `2^{150}L_Y^{42} ≤ s_r/4`; (b) `2^{146}L_Y^{38}log₂L_Y ≤ s_r/4`;
  (c) `2^{151}L_Y^{38}log₂L_Y ≤ s_r/2`; (d) `2^{145}L_Y^{41} ≤ s_r/(16k_own)` and
  `2⌈L_Y^6⌉₊ ≤ s_r/(16k_own)`, with `s_r = run.s G Y.1` (as the row writes `s_r`, not `s_Y`) and
  `k_own = Stage1.kown = 4J_Y + 1`. Literal column 2, five inequalities; `log = log₂` (manuscript
  convention). Scope "rows 3 and 8 for every ancestor `Y` of round `r`", every `r ≤ R`. (b) is
  asserted by the lemma although the table marks it "not used"; keeping it is faithful. Faithful.

I re-derived the three rows from the inputs at the statement level (all needed: (B1)
`L_Y ≤ log M_r ≤ 2λ` and (B3) `s_r ≥ λ^{100}` from `TowerBRoundStatement`; `|I^U| ≤ 12L_Y^3`,
`k_lend ≤ k̄ ≤ λ^{3.3}` from `COLJVCountStatement`; column 3 of rows 4, 7, 8 from `Gamma1f` at
`μ = log₂λ_r ≥ log₂log₂D_*`, which needs only `d_r ≥ D_*` from `Valid`; (B4) `|V(Y)| ≥ P_r/2 ≥
λ^{103}/2` definitional in the locked model: `prePartAddrs` filters `P_l ≤ |Z^0|`, `partVerts` of a
light part is `Z^0 \ S_Z` with `isL1 : 2|S_Z| ≤ |Z^0|` part of `isLight`, `P_r = ⌈λ_r^{103}⌉₊`).
Row 4: `2^{135}·2λ^{1.6}·(2λ)^{28}·12^5(2λ)^{25} = 2^{189}12^5λ^{54.6} ≤ λ^{100}/(16λ^{3.3})` iff
`λ^{42.1} ≥ 2^{193}12^5`. Row 7: `12L^3·2^{86}·2λ^{1.6}L^{19}·12^3L^{15} ≤ 12^4 2^{124}λ^{38.6}`,
and `N ≥ λ^{103}/2 ≥ 12^4 2^{126}λ^{38.6}` iff `λ^{64.4} ≥ 2^{127}12^4`. Row 8 (a)–(d) with
`k_own ≤ max(1, L_Y) ≤ 2λ` (indeed `4⌊log₂(L/8)⌋ + 1 ≤ L` for `L ≥ 8`) and `log₂L_Y ≤ μ + 1`;
the cases `L_Y < 1` are harmless (`L_Y^{38}log₂L_Y ≤ 0`). The `1.6` vs `8/5` literal bridge is a
`norm_num` fact (scratch check).

### 1.6 Declared inputs

- **`Cor22Statement`**: every loopless `F : Finset (Sym2 V)` has a path decomposition with
  `pec ≤ 2` everywhere. TeX: "Every graph can be decomposed into paths such that each vertex is an
  end of at most two of the paths". Faithful (finite simple graph = loopless edge finset, T0).
- **`TowerBRoundStatement`**: under `Gamma1core D`, `run.Valid G D`, `D ≤ d_1`, for every
  `r ∈ [1, R]`: `M_r ≤ d_r^2`; `λ_r ≤ Λ_r ≤ 2λ_r`; `λ_r^{100} ≤ s_r ≤ 2Λ_r^σ`; `s_r ≤ P_r`; and for
  every ancestor `Y` of round `r`, `L_Y ≤ Λ_r ≤ 2λ_r`. This is the first sentence of lemTower (b)
  verbatim (`Λ_r = log₂M_r = LamOf(d_r)`, `σ = sigmaC = 100`). Hypotheses: the TeX's "valid run
  with `d_1 ≥ D_*`" under the s2 standing assumption; the Spec carries `Gamma1core` (Γ1 (a)–(e))
  only, which is a documented strengthening (round-1 m3): lemTower's `\deps` list Γ1 and Γ2 only,
  and s1:condG2 says (a) `D_* ≥ 2^{117}` follows from Γ1 (locked `Gamma1core.gamma2a`) and "none
  of these proofs … uses (b) or (c)". `D ≤ d_1` is implied by `Valid` when `R ≥ 1` but is the TeX
  hypothesis. Faithful (stronger than the TeX; to be confirmed by the s2 tower unit).
- **`COLJVCountStatement`**: under `Gamma1 D`, `Valid`, for every ancestor `Y`:
  `R ≤ r + 1 → k_lend = 0`; `r + 2 ≤ R →` `|I^U| ≤ 12L_Y^3`, `|I^JS| ≤ (4/3)M_{r+2}^2`,
  `|I^JV| = R − r − 1`, `R − r − 1 ≤ 2log*d_r + 1`, and the four-link chain
  `k_lend ≤ 12L_Y^3 + (4/3)M^2 + 2log*d_r + 2 ≤ 24L_Y^3 + (4/3)M^2 ≤ k̄(log₂λ_r) ≤ λ_r^{3.3}`, and
  `λ_r^{-4} ≤ p_Y`. This is every clause of (i) (the last two sentences of (i) are remarks). Guards
  `R ≤ r + 1` / `r + 2 ≤ R` avoid `ℕ`-subtraction; `R − r − 1` is exact under the guard. Faithful.

## 2. Vacuity

- Contradictory hypotheses: none found. `PVStepPhaseStatement`, `PVStripStatement`,
  `PVArcEndsDegStatement`, `Cor22Statement`, `PathEndsCountStatement`, `ClosingStatement`,
  `TrailSplitStatement` have explicit small witnesses in `EGTest/ProbeP4A.lean` (re-read; the
  `StripScenario` section instantiates the manuscript's CR1-PV scenario with `pec(arcs,0) = 3`,
  `pec(paths,0) = 0`, `deg = 6 = |Z| − 1`). `PVFinishStatement`'s size hypothesis holds at
  `N = 2^{1024}`. `PVHyp` and `Gamma1 D ∧ Valid` with an ancestor are not cheaply instantiable
  (astronomically large graphs), but `Gamma1` alone is satisfiable (GAMMA unit) and the HB model
  admits valid runs (s2:propExists); there is no sign of contradiction.
- Trivial conclusions: none where the TeX has content. `PVStepPhaseStatement` cannot be satisfied
  by dumping everything into `D` (cost bound) or into `A` (`|A| ≤ |P|`, ends in `Rt`, vertex
  clause); `PVStripStatement` cannot take `T' = T` when an end lies in `Pl_J` (last clause);
  `PVFinishStatement` cannot take `Hobj = H_J` (object count `64|Pl| + 8|Pl_J|` is far below `|H_J|`
  in general) nor `Hobj = ∅` (arcs need ends in `Rt`). Row 7 for standalone `Y` and
  `TrailRepInnerStatement` are "trivially" true in the sense that the TeX's own content is small
  there (empty sum; a counting fact); both are faithful.
- Junk values checked: `ℕ`-subtraction in `|Z| − 1`, `rep(T)`, `R − r − 1` (exact under guards);
  real division by `8k_lend`, `16k_own` (`k_lend ≥ 1` under the guard, `k_own ≥ 1` always);
  `logb 2 0 = 0` for an empty `V(Y)` (harmless in row 8).

## 3. Declared inputs: use and completeness

| Input | Used by | In the TeX proof | Stated as in TeX | Hidden probe content? |
|---|---|---|---|---|
| `Cor22Statement` (`EG.cor22`) | `PVFinishStatement` ("Take a Corollary-22 decomposition of each `E_{2,c}`") | yes (s4:lemPV `\deps` lists s1:citCor22) | yes | no: a cited result; Lovász → Cor 22 is the Ext unit's node (PLAN §3) |
| `TowerBRoundStatement` (`EG.towerBRound`) | rows 4, 7, 8 via (B1), (B3) | yes ("(Lemma s2:lemTower(b))" at (B1), (B3)) | first sentence of (b) verbatim, with `Gamma1core` (documented strengthening) | no: (R2) algebra and propStructure, s2 tower unit |
| `COLJVCountStatement` (`EG.colJVCount`) | rows 4, 7 via `|I^U| ≤ 12L_Y^3`, `k_lend ≤ k̄` | yes (proof of (ii): "the bound `k_lend(Y) ≤ k̄` of (i)") | all of (i) | no: (i) needs lemTower (a), (b), (d), the geometric sum, `log*`; s3 lending unit |

Not declared, correctly: Fact EG0(b) (proved, `EG.factEG0b`); Euler/T-join, Lovász, T16*, HB,
Monotone, (MC), (B), Chernoff, Markov (enter only through `𝒢_PV`, which the deterministic core
does not use); propStructure (iv) for (B4) (definitional, see 1.5). The step-phase node takes the
Corollary-22 decomposition as a hypothesis, so it needs no input.

## 4. Hygiene

- `python3 -I scripts/lint.py`: "lint (development): 0 findings" (run by me).
- `sorry` appears only in `EG.cor22`, `EG.towerBRound`, `EG.colJVCount`, each with the
  `[DECLARED INPUT] [label]` docstring form.
- Headers: `module`, `public import`, `@[expose] public section` in Defs/Spec, `public section` in
  Proof; namespaces `EG.Spec` (statements) / `EG` (proofs); every statement quantifies
  `∀ (V : Type u) [DecidableEq V]`; docstrings start with the manuscript label and quote the TeX.
  No Spec opens more than one of `EG.Star`/`EG.Vortex`/`EG.COLTable` (`open EG.HB` only).
- Universe: `EG.colJVRow7_rhoY.{u}` takes the Spec at universe `u` explicitly; fine.
- Scratch (`P4AScratchR2.lean`, `lake env lean`, rc=0): all seven Spec modules import; `(1.6:ℝ) =
  8/5`; `TrailRepInnerStatement` re-proved; `1 ≤ klend` under `Y.1 + 2 ≤ R`; empty-`Z` consistency
  of `PVArcEndsDegStatement`.

## 5. Refutation target (PV(c) per-vertex bound → `t`)

- `PVArcEndsDegStatement` is a true general fact (section 1.3); `PVtStatement` (`2 + b ≤ t`) is
  proved; rows 4 and 7 carry `t_Y = ⌈λ_r^{1.6}⌉` and are derivable from the inputs (section 1.5).
  None of these can be refuted, and none of them is where a per-vertex multiplicity meets `t_Y`:
  that comparison is `|Z| − 1 ≤ M_l − 1 < t_Y` (s5:lemParent Step 5), a P4B node. I agree with the
  round-1 re-dispatch (m1) that TRIAGE §4 row P-4 should count the target as hit only once P4B's
  Step-5 statement is written and reviewed. Note for P4B: `t_Y ≥ M_l` for `r + 2 ≤ l ≤ R` is
  asserted in s3:defCOL ("`M_l ≤ λ_{l−2}^{1.6} ≤ λ_r^{1.6}`, Lemma s2:lemTower (a),(b)"); the Step-5
  comparison uses the per-bundle degree `≤ M_l − 1` (s2:lemCap (ii)), not `|Z| − 1` directly.
- The switch from the Corollary-22 end count (`8J + 8 + b`) to `deg_{H_0}` is correctly motivated by
  the stripping scenario, which `EGTest` instantiates.

## 6. Issues

None blocking. All cosmetic; no statement change requested.

- **c1 (cosmetic, docs).** `PVStepPhaseStatement`'s (P4) clause bounds the far-end count by
  `#{w ∈ W : v ∈ {u₁ w, u₂ w}}` without a hypothesis `u_i w ∈ A(w)`, so the step `… ≤ b` of the TeX
  is left to the composition (which has `PVData`). Correct as designed; a one-line note in the
  docstring ("`b` bounds this count once `u_i w ∈ A(w)`, `IsHBFamily`") would save the stage-2
  author a search. Optional.
- **c2 (cosmetic).** `TowerBRoundStatement` repeats `Λ_r ≤ 2λ_r` in the per-ancestor conjunct
  (already recorded; the s2 unit may drop it in the full lemTower (b) Spec).
- **c3 (cosmetic, tracking).** Two items remain for other owners: the s2 tower unit must confirm
  the `Gamma1core`-only form of `TowerBRoundStatement` (round-1 m3); TRIAGE §4 row P-4 should record
  that the P-4 refutation target is hit only with P4B's Step-5 statement (round-1 re-dispatch m1).
  Both are noted in P4A.md; nothing to change in this unit.
- **c4 (cosmetic, manuscript, outside this unit).** The `\fixes` note of s4:lemPV ("second
  inequality of (s4:eqPVt) deleted") reads ambiguously next to the current two-inequality display
  (round-1 c3); suggested wording "the former bound `8J + 8 + b ≤ t` removed".

## 7. Math findings

No finding of class T1–T3. I re-derived: (S) (minimal repetition gives a cycle of length `≥ 3`,
`rep` drops by `≥ 1`), (E), (C); the reserved-edge distinctness and trail properties of (iv); (P2),
(P3) (via "every edge of `F_{j,c}` meets `W_j`"), (P4), (P5); the type (1)/(2) cost analysis and
(s4:eqPVstep); the finish (EG0(b) hypotheses, stripping, `8|Pl_J|`, arcs `≤ |U_J|` per phase);
(c) and (d); rows 4, 7, 8 from (B1), (B3), (B4), (i) and column 3.

T0 encoding decisions (recorded, all consistent with CONVENTIONS/TRIAGE):
- PV-DET-SPEC: `PVStatement` is deterministic (∀ admissible `H_0` ∃ …); `𝒢_PV` is not stated.
- Loopless edge sets for `H_0`, `F`, `H_J`, Cor 22 ("edge set of a simple graph").
- `PVSize N` for "`N ≥ N_0`" (TPV-SIZE-PRED).
- Row 7 stated with `(12L_Y^5)^3` for `ρ^{-3}` (the manuscript's derivation), bridged to `ρ_Y` by
  `EG.colJVRow7_rhoY`.
- (Wording, not a gap) row 8's derivation says "`k_own ≤ L_Y`", which needs `L_Y ≥ 8`; true for
  every ancestor by (B4) (`L_Y ≥ 103μ − 1`), and the Spec does not depend on it.
