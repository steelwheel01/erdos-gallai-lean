# P4A — clean-room statement review, round 1 (re-dispatch, 2026-09-29)

Reviewer: independent clean-room reviewer (round 1), working only from the TeX (v6.1), the locked Defs, the P4A Spec/Defs/Proof/EGTest files and the design note `work/p2b/P4A.md`. The earlier review files were not consulted. I edited no Lean file.

**Verdict: APPROVE.** Every issue below is cosmetic or minor, and none needs a statement change. I found no T1–T3 math finding in the scope (s4 (S), (E), (C), the proof of Lemma PV; s3 Table COL-JV rows 4, 7, 8; the inputs s1:citCor22, s2:lemTower (b), s3:lemCOLJV (i)).

## Scope checked

| File | Checked |
|---|---|
| `EG/Defs/Probe/P4A/PVHyp.lean` (NEW DEFS) | `PVE1'`, `PVHyp`, `PVAdm` against s4.tex 400–447 |
| `EG/Spec/Vortex/Observations.lean` | (S), (E), (C) against s4.tex 49–138 |
| `EG/Spec/Vortex/PVCore.lean` | step phase, step cost, (s4:eqPVt), strip, finish, per-vertex bound against s4.tex 449–641 |
| `EG/Spec/Vortex/PV.lean` | anchor; conclusion (a)–(d) and the deterministic form, against s4.tex 400–447, s5.tex 171/197–204 and s7.tex 1195–1252 |
| `EG/Spec/Lend/COLJVRows.lean` | rows 4, 7, 8 against s3.tex 1150–1340 (table, lemma, proof) |
| `EG/Spec/Ext/Cor22.lean`, `EG/Spec/HB/TowerB.lean`, `EG/Spec/Lend/COLJVCount.lean` | declared inputs, against s1 citCor22, s2 lemTower, s3 lemCOLJV (i) |
| `EG/Proof/**` stubs and proofs | `EG/Proof/Vortex/PVCore.lean`, `EG/Proof/Lend/COLJVRows.lean` |
| `EGTest/ProbeP4A.lean` | non-vacuity witnesses |

Locked Defs read for the back-translation:
- `Objects` (`Obj.WF`, `cycleEdges`, `IsDecomp`);
- `Walk` (`walkEdges`, `pathLength`, `interior`);
- `PathDecomp` (`IsPathDecomp`, `pathEndCount`);
- `Graph` (`degE`);
- `Expander` (`IsExpander`);
- `Link/HBFamily`;
- `Vortex`, `Vortex/PVData`;
- `HB/Run` (`Valid`, `parts`/`ancestors`, `ancS`, `LY`, `lam`, `Lam`, `s`, `M`, `P`);
- `Stage1/COL` (`IU`, `IJS`, `IJV`, `klend`, `JY`, `kown`, `pY`, `tY`);
- `Gamma/Core`, `Gamma/Full`, `Lend/COLTable` (`row`, `col3`).

## 1. Fidelity (back-translation, compared with the TeX)

### New Defs (`PVHyp.lean`)
- **`PVE1' D`:** for every `w ∈ Pl`, `L^5/8 ≤ #{u ∈ A(w) : wu ∈ E(M), ext(u) = *}`.
  - TeX (E1′) counts `C_w = {wu : u ∈ A(w), wu ∈ E(M), ext(u) = *}`.
  - `u ↦ wu` is injective, and `u = w` would give a loop, which is not in `E(M)` because FGraphs are loopless. So the two counts agree. OK.
- **`PVHyp D`** is the conjunction of:
  - `PVSize N` (in place of `N ≥ N_0`, TRIAGE decision TPV-SIZE-PRED);
  - `O` spanning `Z`, a `(2^{-6}, s_O)`-expander, with `2m ≤ s_O`;
  - `IsHBFamily O m b A` (`A(w) ⊆ N_O(w)`, `|A(w)| = m` for `w ∈ V(O) = Z`, every vertex in `≤ b` of the sets);
  - every `R_{j,c}` and `M` spanning `Z` and a `(2^{-6}, s')`-expander;
  - `2^{145}L^{41} ≤ s'`;
  - the `4J + 1` classes pairwise edge-disjoint (the `R` among themselves and each `R` against `M`);
  - `Rt ⊔ Pl = Z`;
  - (E1′).
  - Every clause matches the bullets of s4:lemPV. `ext` is unconstrained, as in the TeX.
- **`PVAdm D H0`:** loopless, all ends in `Z`, `E(M) ⊆ H0`, and `E(R_{j,c}) ⊆ H0` for all `j, c`.
  - This matches "every edge set `H_0` all of whose edges have both ends in `Z` and which contains `E(M)` and every `E(R_{j,c})`", plus the T0 looplessness convention. OK.

### Observations
- **`TrailSplitStatement`:**
  - Hypotheses: a nonempty vertex list, pairwise distinct consecutive edges, no loops.
  - Conclusion:
    - well-formed cycles (distinct vertices, `≥ 3`), at most `(q+1) - |{x_i}|` of them;
    - an optional path with no repeated vertex and `≥ 2` vertices, present iff `x_0 ≠ x_q`, with the same first and last vertex as `T`;
    - the edges of the pieces are a permutation of `E(T)`;
    - all piece vertices lie in `T`.
  - This matches the TeX. The orientation-specific form of "its ends are `x_0` and `x_q`" is a harmless strengthening: cycle excision keeps the first and last entries.
  - Edge case `q = 0`: `C = []`, no path. True.
- **`TrailRepInnerStatement`:** "inner vertices pairwise distinct ⇒ `rep ≤ 2`". It is true for all lists (`|set T| ≥ q - 1`), including `T = [a, a]` (`rep = 1`). OK.
- **`PathEndsParityStatement` / `PathEndsCountStatement`:** literal forms of (E).
  - Count: every path has two distinct ends, both ends of edges of `F`, hence in `W`, so `2|P| = Σ_{v ∈ W} pec ≤ 2|W|`. True.
  - An `F` containing a loop makes `IsPathDecomp` false (walk edges of a nodup list are never loops). Harmless.
- **`ClosingStatement`:** `Q` nodup with `≥ 2` edges forces `x ≠ y`, as the TeX assumes, and makes `Q'` have `≥ 1` edge. The closed list `Q ++ reverse(interior Q')` is a correct encoding of `Q ∪ Q'`. OK.

### PV core
- **`PVStepPhaseStatement`** (steps (iv)–(vi) of one phase `c` of step `j`, and the cost analysis).
  - Hypotheses:
    - `Rt`, `W = W_j` and `Up = Pl ∩ U_{j+1}` are pairwise disjoint;
    - `F = F_{j,c}` is loopless, inside `U_j`, with every edge meeting `W`;
    - `P` is a Corollary-22 decomposition of `F`;
    - reserved far ends `u₁ w ≠ u₂ w` lie in `U_{j+1} = Rt ∪ Up`, with `wu_i ∉ F`.
  - I re-derived that the conclusion follows from the TeX procedure:
    - Reserved edges are pairwise distinct and are not loops (far ends lie outside `W`).
    - The trails have distinct inner vertices (the vertices of one `P`-path), so `rep ≤ 2` by (S).
    - Every `Q`-path and every step arc has `≥ 2` edges. An edge between two far ends / `Rt ∪ Up` vertices would miss `W`. `u = y` for a one-edge path `wy` would give `wu ∈ F`.
    - (P2): trail ends are `P`-ends outside `W` or far ends, all in `Rt ∪ Up`.
    - (P4): a vertex is an end of `≤ 2` `P`-paths, and a far end of `≤ 1` reserved edge per `w` (`u₁ ≠ u₂`).
    - Cost `≤ |W| + 3(2|W| + 2|Up|)`: single edges `≤ |W|`, type-(1) trails `≤ 2|W|`, type-(2) trails `≤ 2|Up|`, each giving `≤ 3` objects.
    - `|A| ≤ |P|`: an arc never comes from a cherry.
  - The statement is not trivially satisfiable. Putting everything into `D` breaks the cost bound. Arcs may use only `F`/reserved edges, need ends in `Rt`, and number `≤ |P|`.
  - It feeds the composition correctly:
    - (P1): `Q` vertices lie in `V(F)`, in `W` (outside `U_{j+1} ⊇ V_{j,c}`) or are far ends (`κ = 0`);
    - PV (b) for step arcs: vertices in `V(F_{j,c})` (s4:eqPVclass) or far ends (`ext = *`).
  - OK. See c1 for the arc-length form.
- **`PVStepCostStatement`:** `4w + 12(2u + 2w) = 28w + 24u ≤ 28(w + u)`. This is the literal (s4:eqPVstep). OK (proved).
- **`PVtStatement`:** `2 + b ≤ 2^7L^8 + 2^7L^2 + 3 ≤ 2^9L^8` under `L ≥ 2^{10}`, with `b = pvB N = ⌈2^7L^2⌈L^6⌉⌉`. This is the literal (s4:eqPVt). OK (proved).
- **`PVStripStatement`:** I re-derived the three cases (`p x`, `p x q`, longer). The conclusion `T' ⊑ T` (infix) gives both the distinctness of the ends and "every vertex of `T'` is a vertex of `T`", which the finish needs for `ext ≠ c`.
  - The bound `|S| ≤ #(ends of T in Pl_J)` forces a genuine strip: for `T` with both ends in `Rt` it forces `T' = T`.
  - OK.
- **`PVFinishStatement`:**
  - Hypotheses: `L ≥ 2^{10}`, `|Pl| ≤ N`, `Pl_J ⊆ Pl`, `Rt ∩ Pl = ∅`, (G5) `|Pl_J| ≤ 64|Pl|/L`, and `H_J` loopless inside `Rt ∪ Pl_J`.
  - Conclusion: `Hobj ⊆ H_J` decomposes into `≤ 64|Pl| + 8|Pl_J|` objects, and the rest into phased arcs with:
    - ends in `Rt`;
    - `ext ≠` phase on every vertex;
    - `≤ 4|U_J|` arcs;
    - `Pl_J = ∅ ⇒ Hobj = ∅`.
  - It is provable from `EG.factEG0b` (`N := N`, `α := |Pl|`, `β := 64`, `W := Pl_J`), `Cor22Statement`, (E) and `PVStripStatement`.
  - `8|Pl_J|` is the TeX's own tighter bound. The free `N` (H6) is harmless. OK.
- **`PVArcEndsDegStatement`:** `pec(arcs, x) ≤ deg_{H_0}(x) ≤ |Z| - 1` for every `x : V`, for any path decomposition of any `H^arc ⊆ H_0` with `H_0` loopless inside `Z`.
  - This is exactly the argument of (c).
  - Natural subtraction is harmless: `deg = 0` off `Z`, and `Z = ∅` forces `H_0 = ∅`.
  - OK. See m1 for its role as refutation target.

### Anchor `PVStatement` (not a P4A node)
- (a)–(d) are literal: `IsPathDecomp` gives pairwise edge-disjoint paths of length `≥ 1` with two distinct ends, and the arc count is `4(J+1)N`.
- The deterministic form "∀ admissible `H_0` ∃ …" is implied by the TeX ("∃ label outcome in `𝒢_PV`, ∀ `H_0`, ∃ …", with `P(𝒢_PV) ≥ 1/2 - η > 0`), since the conclusion does not mention the labels.
- I checked the consumers:
  - s5:lemChild uses only (a)–(d) on `𝒢_PV`;
  - s7:lemOneOutcome step (ii) says "only this non-emptiness is used", and the PV labels are read by nothing outside the run.
- So the deterministic form is sufficient. OK. See c3 for placement.

### COL-JV rows
- **Row 4:** `2^{135}·t_Y·L_Y^{28}·(12L_Y^5)^5 ≤ s_Y/(8k_lend)` for `Y ∈ ancestors`, `r + 2 ≤ R`.
  - This is literal column 2.
  - `k_lend ≥ 1` under the guard (`|I^JV| = R - r - 1 ≥ 1`), so there is no division-by-zero junk.
  - Derivation re-checked: `2^{135}·2λ^{1.6}·(2λ)^{28}·12^5(2λ)^{25} = 2^{189}12^5λ^{54.6} ≤ λ^{100}/(16λ^{3.3})` iff `λ^{42.1} ≥ 2^{193}12^5` (col3 row 4, with row 9 from the input). OK.
- **Row 7:** the sum over `I^U(Y)` of `2^{86}t_Y L_Y^{19}(12L_Y^5)^3N^{-3}` is `≤ N^{-2}/4`, with `N = |V(Y)|`.
  - This is the manuscript's own sufficient form (proof of row 7: "`ρ^{-3} ≤ 1728L_Y^{15}`").
  - It implies the literal column-2 requirement through the proved bridge `EG.colJVRow7_rhoY`, since the T16* per-class failure is `2^{86}tL^{19}ρ^{-3}N^{-3}` (s3:thmT16s).
  - Derivation re-checked: `12^4 2^{124}λ^{38.6}N^{-3} ≤ N^{-2}/4` iff `N ≥ 12^4 2^{126}λ^{38.6}`, which follows from `N ≥ λ^{103}/2` and `λ^{64.4} ≥ 2^{127}12^4`. OK.
- **Row 8:** (a)–(d) are literal, with `log = log₂` and `k_own = 4J_Y + 1`. The scope is every ancestor (every `r ≤ R`), as the lemma says.
  - Re-checked from `s_r ≥ λ^{100}`, `L_Y ≤ 2λ`, `log L_Y ≤ μ + 1` and `k_own ≤ max(1, L_Y)`.
  - For `L_Y < 1` the (b)/(c) left sides are `≤ 0`.
  - OK.
- **Hypotheses:** `Gamma1 Dstar ∧ run.Valid G Dstar`, the TeX's "Assume Γ1".
  - The hypothesis `d_1 ≥ D_*` of the input `TowerBRoundStatement` is recovered: `run.Valid` gives `D_* ≤ d_l` for `l ∈ [1, R]`, and an ancestor exists only if `R ≥ 1`.
  - (B4) `|V(Y)| ≥ P_r/2` is definitional, as the note says: `Round.prePartAddrs` filters on `P_l ≤ |X^0|`, and light parts are `Z^0 \ S_Z`. The stage-2 proof must extract (L1) `2|S_Z| ≤ |Z^0|` from `isLight`.

## 2. Vacuity
- All the probe-node hypotheses are satisfiable on small instances. I re-ran `scripts/check.sh EGTest/ProbeP4A.lean`: rc=0, 0 errors, 0 sorry.
- The non-trivial conclusions are witnessed:
  - step phase on `Fin 4`;
  - strip;
  - the star attaining `pec = deg = |Z| - 1`;
  - the finish-stripping scenario `StripScenario`.
- No conclusion is trivially true:
  - the cost bound, the `|S|` bound and `Pl_J = ∅ ⇒ Hobj = ∅` rule out the "everything is a single edge" witness;
  - the arc edge-set clause rules out free arcs.
- `PVHyp` and `Gamma1 ∧ Valid` with an ancestor of round `≤ R-2` are not cheaply instantiable (astronomical sizes). No contradiction is visible among their clauses:
  - `PVHyp` needs `N ≥ 2^{1024}`, and every constraint there is a lower bound on degrees / expansion, attainable by dense graphs;
  - Γ1 is non-vacuous (GAMMA unit).
- This matches the note's "not cheap" list.

## 3. Declared inputs
| Input | Used by the manuscript proof? | Stated as in TeX? | Hides a probe node? |
|---|---|---|---|
| `Cor22Statement` [s1:citCor22] | yes: PV finish "Take a Corollary-22 decomposition of each `E_{2,c}`" (and step (iii), taken there as a hypothesis) | yes (loopless edge set, T0) | no. Lovász → Cor 22 is an Ext node, and the task allowed Lovász as the input |
| `TowerBRoundStatement` [s2:lemTower] (b), first sentence | yes: (B1), (B3) in rows 4, 7, 8 | yes, clause by clause (`σ = 100`, rounds `Icc 1 R`); the last conjunct `Λ_r ≤ 2λ_r` is repeated (c2) | no. The hypothesis `Gamma1core` instead of the full standing assumptions (Γ1–Γ4, `n ≥ N_0`) is plausible: every clause except `L_Y ≤ log M_r` is pure arithmetic in `d_r ≥ D_*`; that clause is structural (lemCap) and independent of `N_0`. The s2 unit must confirm it |
| `COLJVCountStatement` [s3:lemCOLJV] (i) | yes: `|I^U| ≤ 12L^3` (row 7), `k_lend ≤ k̄ ≤ λ^{3.3}` (row 4) | yes, every clause of (i), with `μ = log₂λ_r` and `k̄ = COLTable.kbar μ` | no. Rows 9/10 of column 2 sit inside (i) but are not P4A nodes |

- Stub docstrings start with `[DECLARED INPUT] [label]`. The only `sorry`s are the three stubs.
- Nothing from the PV(c) core or from rows 4/7/8 is among the inputs.

## 4. Hygiene
- `python3 -I scripts/lint.py`: `lint (development): 0 findings`.
- Every Spec statement is a `def …Statement : Prop` with a docstring starting with the manuscript label and quoting the TeX.
- The Spec files are `module` + `@[expose] public section`, and the Proof files `public section`.
- Qualified names are used for `Vortex.*` / `Stage1.*` / `COLTable.*`: no double `open`.
- Row indices are used only through `col3`/concrete rows.

## Issues

- **m1 (minor, scope; no change requested).** The refutation target is only partly exercised in P4A.
  - `PVArcEndsDegStatement` is a general combinatorial fact about path decompositions. It does not involve the PV procedure, so proving it cannot refute anything.
  - The refutation-relevant question is whether `deg_{H_0}(x) ≤ |Z| - 1` fits under the path-connectivity multiplicity. That is `|Z| - 1 ≤ M_l - 1 < t_Y` in s5:lemParent Step 5, together with the claim that the pair multiset fed to T16* per bundle `(l, c, σ)` has per-vertex multiplicity bounded by the arc-end count of a single light part per round. Both live in P4B.
  - The note says this (line 12). The orchestrator should record that the P-4 target is "hit" only when P4B's Step-5 statement is written and reviewed.
- **c1 (cosmetic).** The step arc clause of `PVStepPhaseStatement` (`2 ≤ a.length`, `≥ 1` edge) is weaker than TeX (P3) (length `≥ 2`) for step arcs. This is deliberate and sufficient for PV (b). Already recorded in the note.
- **c2 (cosmetic).** `TowerBRoundStatement` repeats `Λ_r ≤ 2λ_r` in the per-ancestor conjunct. This is harmless, and it mirrors the TeX's "`L_Y ≤ log M_r ≤ 2λ_r`".
- **c3 (cosmetic, placement).** `EG/Spec/Vortex/PV.lean` holds `PVStatement`, the anchor, which is not a P4A node. The s4 statement owner should adopt this file, not write a second Lemma-PV Spec. This is the note's open question 1.
- **c4 (cosmetic).** Rows 4 and 7 are asserted for standalone `Y` too (H4). The TeX defines `t_Y` only for light `Y`, but the Lean `Stage1.tY` is total, so this is a true, harmless strengthening. Row 7 is trivial there (`I^U = ∅`).

## Math findings
None of class T0–T3 beyond the T0 decisions already recorded in the note (H1–H7). I re-derived all of the following and found each correct:
- (S) with the minimal-repetition excision;
- (E);
- (C);
- the step analysis, including (P3) for trails with appended edges and the arcs from type-(1) trails;
- (s4:eqPVstep), (s4:eqPVt);
- (G2) arithmetic: `s' ≥ 2^{144}L^{41}` needed; failure `2^{95}L^{30}N^{-3}`, times `4J ≤ L`;
- (G4): `L^4/2 ≥ 16`;
- (G5) via Markov (each `< 1/4`);
- the finish stripping and the `8|Pl_J|` count;
- (c) both parts;
- rows 4, 7, 8 from col3 + (B1)–(B4) + (i).

One manuscript wording point, cosmetic and outside this unit: the `\fixes` line of s4:lemPV ("second inequality of (s4:eqPVt) deleted") reads ambiguously next to the current two-inequality display. It refers to a removed conjunct `8J+8+b ≤ …`.
