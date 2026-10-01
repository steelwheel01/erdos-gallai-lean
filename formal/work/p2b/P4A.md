# P2b probe unit P4A (probe P-4, part 1), stage 1: statements

Chain: the PV(c) core (the type (1)/(2)/arc analysis of a PV step, stripping in the finish, the per-vertex arc bound of the CR1-PV repair) and rows 4, 7, 8 of the COL-JV table (the rows that carry `t_Y = ⌈λ_r^{1.6}⌉` and the own-device thresholds). This is TRIAGE §4 row P-4, first part.
Manuscript: `proofs/manuscript/s4.tex` v6.1 (observations (S), (E), (C); Lemma PV and its proof) and `s3.tex` (Table s3:tabCOLJV, Lemma s3:lemCOLJV). The manuscript is a CANDIDATE proof, reviewed by AI only.
Blueprints used: `work/p2/blueprint_s4.md` (convVortex, lemPV), `work/p2/blueprint_s3b.md` (tabCOLJV, lemCOLJV). Data model: TRIAGE §2.4, §2.6, §2.8; `work/p2d/params.md`, `work/p2d/light.md`.

Refutation target (TRIAGE §4): "a per-vertex multiplicity feeding a path-connectivity parameter `t`". In this part that means the PV(c) degree bound and the rows that use `t_Y`. The target is hit by three statements:
- `PVArcEndsDegStatement`: the per-vertex bound `#arcs ending at x ≤ deg_{H_0}(x) ≤ |Z| - 1`. EGTest shows that the inequality `pec ≤ deg_{H_0}` is attained (abstract star), and, separately, the finish-stripping scenario in which a rooted vertex ends several arcs while being an end of no Corollary-22 path (fix round 1, m1).
- `PVtStatement`: `2 + b ≤ t` in the run.
- `COLJVRow4Statement` / `COLJVRow7Statement`: the Theorem-16* requirements at multiplicity `t_Y`.

The link `|Z| - 1 ≤ M_l - 1 ≤ t_Y` (s5:lemParent Step 5, row 12) belongs to part 2 (P4B). No statement was found false.

## Status (stage 1)

- Every file below compiles:
  - `scripts/check.sh` on each file;
  - `lake build` of the Defs, Spec and Proof modules;
  - `EGTest/ProbeP4A.lean` with 0 errors and 0 warnings.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan: `scripts/Axioms.lean --prefix EG` on `EG.Proof.Vortex.PVCore`, `EG.Proof.Ext.Cor22`, `EG.Proof.HB.TowerB` and `EG.Proof.Lend.COLJVCount`.
  - 760 constants, 0 violations.
  - `sorryAx` appears only in the three declared-input stubs `EG.cor22`, `EG.towerBRound` and `EG.colJVCount`.
- Proved already (trivial):
  - `EG.pvStepCost : PVStepCostStatement` ((s4:eqPVstep), the arithmetic);
  - `EG.pvT : PVtStatement` ((s4:eqPVt)).
- Everything else is stage 2. No proof file of a probe node contains `sorry`.
- No math finding of class T1–T3 (see "Math findings"). There are four T0 encoding decisions, listed under "Hazards".

## Files

| File | Module | Contents |
|---|---|---|
| `EG/Defs/Probe/P4A/PVHyp.lean` | `EG.Defs.Probe.P4A.PVHyp` | **NEW DEFS**: `EG.Vortex.PVE1'`, `EG.Vortex.PVHyp`, `EG.Vortex.PVAdm` |
| `EG/Spec/Vortex/Observations.lean` | `EG.Spec.Vortex.Observations` | `TrailSplitStatement`, `TrailRepInnerStatement` ((S)); `PathEndsParityStatement`, `PathEndsCountStatement` ((E)); `ClosingStatement` ((C)) |
| `EG/Spec/Vortex/PVCore.lean` | `EG.Spec.Vortex.PVCore` | `PVStepPhaseStatement`, `PVStepCostStatement`, `PVtStatement`, `PVStripStatement`, `PVFinishStatement`, `PVArcEndsDegStatement` |
| `EG/Spec/Vortex/PV.lean` | `EG.Spec.Vortex.PV` | `PVStatement` (Lemma PV, deterministic form). It is an anchor only: not a P4A node and not proved here |
| `EG/Spec/Lend/COLJVRows.lean` | `EG.Spec.Lend.COLJVRows` | `COLJVRow4Statement`, `COLJVRow7Statement`, `COLJVRow8Statement` |
| `EG/Spec/Ext/Cor22.lean` | `EG.Spec.Ext.Cor22` | `Cor22Statement` (declared input) |
| `EG/Spec/HB/TowerB.lean` | `EG.Spec.HB.TowerB` | `TowerBRoundStatement` (declared input) |
| `EG/Spec/Lend/COLJVCount.lean` | `EG.Spec.Lend.COLJVCount` | `COLJVCountStatement` (declared input) |
| `EG/Proof/Ext/Cor22.lean` | `EG.Proof.Ext.Cor22` | stub `EG.cor22` (`sorry`, DECLARED INPUT) |
| `EG/Proof/HB/TowerB.lean` | `EG.Proof.HB.TowerB` | stub `EG.towerBRound` (`sorry`, DECLARED INPUT) |
| `EG/Proof/Lend/COLJVCount.lean` | `EG.Proof.Lend.COLJVCount` | stub `EG.colJVCount` (`sorry`, DECLARED INPUT) |
| `EG/Proof/Vortex/PVCore.lean` | `EG.Proof.Vortex.PVCore` | `EG.pvStepCost`, `EG.pvT` (proved) |
| `EG/Proof/Lend/COLJVRows.lean` | `EG.Proof.Lend.COLJVRows` | fix round 1 (c1): the row-7 bridge `EG.colJVRow7_rhoY` and `EG.zpow_neg_three_le_of_ge_inv` (proved, 0 sorry); the proofs of rows 4, 7, 8 are stage 2 |
| `EGTest/ProbeP4A.lean` | `EGTest.ProbeP4A` | non-vacuity checks |

Conventions:
- Statements are in namespace `EG.Spec`, proofs in namespace `EG`. Every statement quantifies `∀ (V : Type u) [DecidableEq V]`.
- The s3 statements are placed in area `Lend`, where blueprint s3b puts `COLJV`, rather than `Vortex`. They use new file names (`COLJVRows`, `COLJVCount`), so they cannot collide with the future full `COLJV.lean`.
- The Specs and the design note total about 1020 lines of Lean.

Root imports for the orchestrator to add (I did not edit `EG.lean`, `EGTest.lean` or `EGCheck.lean`):
- to `EG`: `EG.Defs.Probe.P4A.PVHyp`, `EG.Spec.Vortex.Observations`, `EG.Spec.Vortex.PVCore`, `EG.Spec.Vortex.PV`, `EG.Spec.Lend.COLJVRows`, `EG.Spec.Ext.Cor22`, `EG.Spec.HB.TowerB`, `EG.Spec.Lend.COLJVCount`, `EG.Proof.Ext.Cor22`, `EG.Proof.HB.TowerB`, `EG.Proof.Lend.COLJVCount`, `EG.Proof.Vortex.PVCore`, `EG.Proof.Lend.COLJVRows` (new in fix round 1);
- to `EGTest`: `EGTest.ProbeP4A`.

## Nodes: label → Lean names

| Label | Role | Statement(s) | Planned proof name(s) (stage 2) |
|---|---|---|---|
| s4:eqSplit (S) | probe (Lib engine) | `TrailSplitStatement`, `TrailRepInnerStatement` | `EG.trailSplit`, `EG.trailRepInner` |
| s4:eqEnds (E) | probe (Lib engine) | `PathEndsParityStatement`, `PathEndsCountStatement` | `EG.pathEndsParity`, `EG.pathEndsCount` |
| s4:eqClose (C) | probe (Lib engine) | `ClosingStatement` | `EG.closing` |
| s4:lemPV proof, steps (iv)–(vi) + "Cost of step j" (type (1)/(2)/arc analysis; CR1-PV) | probe | `PVStepPhaseStatement` | `EG.pvStepPhase` (uses (S), (E)) |
| s4:eqPVstep | probe | `PVStepCostStatement` | `EG.pvStepCost` (**done**) |
| s4:eqPVt | probe | `PVtStatement` | `EG.pvT` (**done**) |
| s4:lemPV proof, "Finish", stripping (CR1-PV) | probe | `PVStripStatement` | `EG.pvStrip` |
| s4:lemPV proof, "Finish" (EG0(b), phases, Cor 22, stripping; (c) finish count; (d)) | probe | `PVFinishStatement` | `EG.pvFinish` (uses `EG.factEG0b`, `EG.cor22`, (E), strip) |
| s4:lemPV (c), per-vertex bound (CR1-PV) | probe (**refutation target**) | `PVArcEndsDegStatement` | `EG.pvArcEndsDeg` |
| s3:lemCOLJV (ii), row 4 (CR1-PV, `t_Y`) | probe (**refutation target**) | `COLJVRow4Statement` | `EG.colJVRow4` |
| s3:lemCOLJV (ii), row 7 (CR1-PV, `t_Y`) | probe (**refutation target**) | `COLJVRow7Statement` | `EG.colJVRow7` |
| s3:lemCOLJV (ii), row 8 | probe | `COLJVRow8Statement` | `EG.colJVRow8` |
| s4:lemPV (the lemma) | anchor, **not** a P4A node | `PVStatement` | P4B declares it as an input (lemChild) |
| s1:citCor22 | **declared input** | `Cor22Statement` | stub `EG.cor22` |
| s2:lemTower (b), first sentence | **declared input** | `TowerBRoundStatement` | stub `EG.towerBRound` |
| s3:lemCOLJV (i) | **declared input** | `COLJVCountStatement` | stub `EG.colJVCount` |

Planned stage-2 files:
- `EG/Lib/Vortex/Trail.lean`: list surgery for (S) and (C), with cycle removal at a minimal repetition.
- `EG/Lib/Vortex/Ends.lean`: (E), by double counting; parity per path.
- `EG/Proof/Vortex/Observations.lean`.
- `EG/Proof/Vortex/PVCore.lean`: the step-phase engine, then strip, finish and arc-ends.
- `EG/Lib/Lend/Standing.lean`: (B1), (B3), (B4); `λ_r > 1`, `μ_r ≥ log₂log₂D_*`, `COLTable.lam μ_r = λ_r`, `t_Y ≤ 2λ^{1.6}`, `k_own ≤ max(1, L_Y) ≤ 2λ`, `k_lend ≥ 1` for `r ≤ R-2`.
- `EG/Proof/Lend/COLJVRows.lean` (created in fix round 1 with the row-7 bridge `EG.colJVRow7_rhoY`; the row proofs go there).

Notes for the stage-2 composition (fix round 1):
- **m2 (PV (b) for step arcs).** `PVStepPhaseStatement` describes arcs only by their properties (H2), so a witness may declare a cherry `u₁ w u₂` an arc when `w ∈ V(F)` (an interior vertex of a `Paths_{j,c}` path) and `u₁, u₂ ∈ Rt`, whereas TeX (vi) always closes cherries. The composition (PV (b), here and in P4B) must therefore derive `ext ≠ c` on the vertices of step arcs from the arc vertex clause ("in `V(F_{j,c})` or a far end") together with (s4:eqPVclass) (`ext(y) ≠ c` for `y ∈ V(F_{j,c})`) and `ext = *` at far ends (TeX (P5): "far ends (where `ext = *`)"; reserved edges are chosen in `C_w`, whose far ends have `ext = *`), and **not** from "arcs never come from cherries" (the TeX's (P5) route). A cherry whose centre `w` is not in `V(F)` cannot be declared an arc: `w ∈ W` is neither in `V(F)` nor a far end (far ends lie in `Rt ∪ Up`, disjoint from `W`). The count `|A| ≤ |P|` binds either way.
- **c1 (row 7 consumer).** Use `EG.colJVRow7_rhoY` with `ρ_Y ≥ 1/(12L_Y^5)` from s5:lemZones (ii) and `L_Y > 0`.
- **m3 (TowerB).** When the s2 tower unit proves lemTower (b), it must confirm that the `Gamma1core`-only form (no Γ2–Γ4, no `n ≥ N_0`) holds, and record this next to STR-N0 in TRIAGE (orchestrator-owned; not edited by P4A).

## Declared inputs, with justification

1. **[s1:citCor22] `Cor22Statement`**, stub `EG.cor22`.
   - Used in the PV finish ("Take a Corollary-22 decomposition of each `E_{2,c}`"). `PVFinishStatement` needs it.
   - It is a cited result. PLAN §3 (Ext: "`Lovasz` + `Cor22`") derives it from the stage-α Lovász hypothesis [s1:citThm21] by adding a vertex joined to the even-degree vertices. That is the Ext unit's job; it needs a vertex-type extension and is not part of the PV(c) core.
   - The task allowed "Lovasz" as the declared input. I declare Cor 22 instead, because Cor 22 is the statement the probe uses (a single input, no bridge). Lovász → Cor 22 remains an Ext node.
   - The step-phase node takes a Corollary-22 decomposition as a *hypothesis*, so it does not use `EG.cor22`.
2. **[s2:lemTower] (b), first sentence: `TowerBRoundStatement`**, stub `EG.towerBRound`.
   - The row derivations use (B1) "`L_Y ≤ log M_r ≤ 2λ`" and (B3) "`s_r ≥ λ^{100}`". The proof of s3:lemCOLJV quotes both from [s2:lemTower] (b).
   - Their proofs need the (R2) algebra and propStructure (s2 tower unit, blueprint s2b).
   - Stated like P3A's `TowerCStatement`: `Gamma1core`, `Valid`, `d_1 ≥ D_*`. The full (b) Spec must import it.
3. **[s3:lemCOLJV] (i): `COLJVCountStatement`**, stub `EG.colJVCount`.
   - Rows 4 and 7 use "`|I^U(Y)| ≤ 12L_Y^3`" and "`k_lend ≤ k̄ (≤ λ^{3.3})`" from part (i).
   - Part (i) needs [s2:lemTower] (a), (b), (d), a geometric sum over `M_l` and `log*`. It is the s3 lending unit's job.
   - Stated in full: every clause of (i).

Not declared, because unused:
- Euler / T-joins (lemParent, part 2).
- Lovász (see item 1).
- Theorem 16*, Lemma HB, Monotone, (MC), (B), Chernoff and Markov. They enter Lemma PV only through the good event `𝒢_PV`, which the PV(c) core does not use.
- Fact EG0(b) is used by `PVFinishStatement`, but it is already proved (`EG.factEG0b`), so it is not an input.

(B4) "`|V(Y)| ≥ P_r/2 ≥ λ^{103}/2`" is not an input: it is **definitional** in the locked HB model.
- `Round.prePartAddrs` keeps only leaves with `P_l ≤ |Z^0|`.
- A light part is `Z^0 \ S_Z` with (L1) `2|S_Z| ≤ |Z^0|` and `S_Z ⊆ Z^0`.
- `P_r = ⌈λ_r^{103}⌉₊`.
So propStructure (iv) is not needed for it.

## Definitions used

- Locked:
  - `EG.Vortex.{PVData, L, PVSize, pvJ, pvM, pvB}`;
  - `EG.IsHBFamily`;
  - `EG.FGraph.IsExpander`;
  - `EG.{IsPathDecomp, pathEndCount, walkEdges, pathLength, interior, cycleEdges, Obj, IsDecomp, degE}`;
  - `EG.HB.Run.{Valid, R, ancestors, ancVerts, ancS, LY, s, lam, Lam, M, P, d}`;
  - `EG.Stage1.{tY, klend, kown, IU, IJS, IJV, pY}`;
  - `EG.COLTable.{kbar, col3}` (through `Gamma1`);
  - `EG.{Gamma1, Gamma1core}`;
  - `EG.logStar`;
  - `EG.sigmaC`.
- **New Defs file**, `EG/Defs/Probe/P4A/PVHyp.lean` (namespace `EG.Vortex`). TRIAGE §2.8 says "The PV hypotheses as named Defs remain the s4 Spec author's job". The file defines:
  - `PVE1' D` ((E1′));
  - `PVHyp D` (all hypotheses on the fixed data);
  - `PVAdm D H0` (admissible `H_0`).
  (E1′) is written in exactly the form of `EG.Light.E1_childData`, so s5 passes `childData ω Z` with no bridge.
- No existing definition looks wrong for this chain. Checked specifically:
  - `Stage1.tY = ⌈λ_r^{1.6}⌉₊` (literal `1.6`; equal to `8/5`);
  - `kown = 4·pvJ|V(Y)| + 1`;
  - `ancS` (`s_r/2` light, `s_r` standalone);
  - `IU = ∅` for standalone `Y`.

## Back-translation of every statement (plain mathematics next to the TeX)

Notation: `V` is a type with decidable equality. A *path* is a vertex list without repeated vertex. `P` is a list of paths. `pec(P, v)` is `pathEndCount`, the number of paths of `P` with `v` as first or last vertex. `deg_F(v)` is `degE`.

### (S) `TrailSplitStatement`, `TrailRepInnerStatement`
- TeX: "Let `T = x_0⋯x_q` (`q ≥ 0`) be a trail … in a simple graph and put `rep(T) := (q+1) - |{x_0,…,x_q}|`. Then `E(T)` is the disjoint union of the edge sets of at most `rep(T)` cycles, each of length at least 3, and of at most one path; the path is present iff `x_0 ≠ x_q`, and then its ends are `x_0` and `x_q`. Every vertex of every piece is a vertex of `T`. In particular, if the inner vertices are pairwise distinct, then `rep(T) ≤ 2` …"
- Lean (`TrailSplitStatement`): let `T` be a non-empty list whose consecutive-pair edges are pairwise distinct and are not loops. Then there are cycles `C` and possibly one path `p` such that:
  - every `c ∈ C` is a well-formed cycle (distinct vertices, `≥ 3` of them);
  - `|C| ≤ |T| - |set(T)|`;
  - the cycle edges plus the path edges are a permutation of the edges of `T`;
  - `p` exists iff first vertex ≠ last vertex, and then `p` has distinct vertices, `≥ 2` of them, with the same first and last vertex as `T`;
  - all vertices of all pieces lie in `T`.
- Lean (`TrailRepInnerStatement`): if the interior of `T` (all but the two ends) has no repetition, then `|T| - |set(T)| ≤ 2`. No trail hypothesis is needed, since the count alone gives it.

### (E) `PathEndsParityStatement`, `PathEndsCountStatement`
- TeX: "Let `𝒫` be a decomposition of an edge set `F` into (non-trivial) paths. For every vertex `v` the number of paths of `𝒫` having `v` as an end is congruent to `deg_F(v)` modulo 2. If every vertex is an end of at most two paths of `𝒫` and all edges of `F` have both ends in a set `W`, then `|𝒫| ≤ |W|`."
- Lean (parity): if `P` is a path decomposition of the finset `F`, then `pec(P, v) ≡ deg_F(v) (mod 2)` for all `v`.
- Lean (count): if in addition `pec(P, v) ≤ 2` for all `v`, and all ends of edges of `F` lie in `W`, then `|P| ≤ |W|`.

### (C) `ClosingStatement`
- TeX: "Let `Q` be a path of length at least 2 with ends `x ≠ y`, and let `Q'` be an `x–y` path whose inner vertices avoid `V(Q)` and which shares no edge with `Q`. Then `Q ∪ Q'` is a cycle of length at least 3."
- Lean: assume
  - `Q` has distinct vertices, `≥ 2` edges, and runs from `x` to `y`;
  - `Q'` has distinct vertices and runs from `x` to `y`;
  - the interior of `Q'` avoids `Q`;
  - the edge lists are disjoint.
- Lean, conclusion: the list `Q ++ reverse(interior Q')` is a well-formed cycle, and its edges are a permutation of `E(Q) ++ E(Q')`.

### `PVStepPhaseStatement` (steps (iv)–(vi) for one phase, and the cost analysis)
- TeX: steps (iv)–(vi) and "Cost of step `j`", quoted in the docstring. In particular:
  - "a trail produces objects only if (1) it is a cherry or has an appended edge, or (2) it is a path of `Paths_{j,c}` without appended edges having an end in `Pl` … at most `2|W_j|` … at most `2|Pl ∩ U_{j+1}|` … Every remaining trail … becomes an arc. Each trail of type (1) or (2) gives at most three objects";
  - (c): "each arc of phase `c` comes from a distinct path of `Paths_{j,c}`".
- Lean, hypotheses:
  - `Rt`, `W`, `Up` are pairwise disjoint;
  - `F` is loopless, every edge has both ends in `Rt ∪ W ∪ Up`, and every edge meets `W`;
  - `P` is a path decomposition of `F` with `pec ≤ 2`;
  - for each `w ∈ W` there are far ends `u₁ w ≠ u₂ w`, both in `Rt ∪ Up`, with `w u_i w ∉ F`.
- Lean, conclusion: there exist objects `D`, arcs `A` and to-be-closed paths `Q` such that:
  - the objects are well formed;
  - the edges of `D`, `A`, `Q` together are, without repetition, exactly `F` plus the reserved edges `w u₁ w`, `w u₂ w` (`w ∈ W`);
  - each arc has distinct vertices, at least 2 of them (so at least 1 edge), both ends in `Rt`, and every vertex on an edge of `F` or equal to a far end;
  - `|A| ≤ |P|`;
  - each `q ∈ Q` has distinct vertices, `≥ 2` edges, both ends in `Rt ∪ Up`, and every vertex on an edge of `F`, in `W`, or a far end;
  - `pec(Q, v) ≤ 2 + #{w ∈ W : v is a far end of w}`;
  - `|D| + |Q| ≤ |W| + 3(2|W| + 2|Up|)`.
- Reading in the manuscript's terms:
  - `W = W_j`, `Up = Pl ∩ U_{j+1}`, `F = F_{j,c}`, `P = Paths_{j,c}`;
  - `D` is the single edges and split cycles;
  - `Q` are the paths closed in (vi), each giving one more cycle;
  - `A` are the arcs of phase `c`;
  - the vertex clauses are the inputs of (P1) and of (P5)/(b);
  - the `pec(Q, ·)` clause is (P4) before HB is applied.

### `PVStepCostStatement` (s4:eqPVstep)
- TeX: "using `W_j ⊔ (Pl ∩ U_{j+1}) = Pl ∩ U_j`, step `j` outputs at most `4|W_j| + 4·3(2|Pl ∩ U_{j+1}| + 2|W_j|) ≤ 28|Pl ∩ U_j|` objects."
- Lean: for disjoint `W`, `Up`: `4|W| + 12(2|Up| + 2|W|) ≤ 28|W ∪ Up|`.

### `PVtStatement` (s4:eqPVt)
- TeX: "Since `b ≤ 2^7L^2(L^6+1)+1`, `2+b ≤ 2^7L^8+2^7L^2+3 ≤ 2^9L^8 = t`."
- Lean: if `L = log₂N ≥ 2^{10}`, then `2 + pvB N ≤ 2^7L^8 + 2^7L^2 + 3 ≤ 2^9L^8`.

### `PVStripStatement`
- TeX: "If an end `p` of `T` lies in `Pl_J`, the edge of `T` at `p` lies in `E_2`, so its other end lies in `Rt`; output this edge as a single edge (stripping). After stripping at the ends of `T` lying in `Pl_J`, what remains of `T` has no edges or is a path of length at least 1 with two distinct ends in `Rt`."
- Lean, hypotheses:
  - `Rt ∩ PlJ = ∅`;
  - `T` has distinct vertices, at least 2 of them, all in `Rt ∪ PlJ`;
  - every edge of `T` has an end in `Rt`.
- Lean, conclusion: there are edges `S` and a contiguous piece `T'` of `T` such that:
  - `S ++ E(T')` is a permutation of `E(T)`;
  - `|S|` is at most the number of ends of `T` in `PlJ`;
  - `T'` has at most one vertex, or has `≥ 2` vertices with both ends in `Rt`.

### `PVFinishStatement`
- TeX: the "Finish" paragraph, the finish count of (c) ("at most `|U_J| ≤ N` arcs per phase by (E)") and (d) ("If `Pl = ∅` … `H^obj = ∅`"). All are quoted in the docstring.
- Lean, hypotheses:
  - `log₂N ≥ 2^{10}`;
  - `|Pl| ≤ N`, `PlJ ⊆ Pl`, `Rt ∩ Pl = ∅`;
  - `|PlJ| ≤ 64|Pl|/log₂N`;
  - `HJ` is loopless with all edge ends in `Rt ∪ PlJ`;
  - `ext` is any map to `[4] ∪ {*}`.
- Lean, conclusion: there are `Hobj ⊆ HJ`, a decomposition of `Hobj` into at most `64|Pl| + 8|PlJ|` objects, and arcs with phases such that:
  - the arcs are a path decomposition of `HJ \ Hobj`;
  - every arc has both ends in `Rt`, and every vertex of a phase-`c` arc has `ext ≠ c`;
  - there are at most `4|Rt ∪ PlJ|` arcs;
  - `PlJ = ∅` implies `Hobj = ∅`.
- Note: the TeX states the tighter `8|Pl_J|` explicitly, and keeps `16|Pl|` only in the final sum.

### `PVArcEndsDegStatement` (Lemma PV (c), per-vertex bound)
- TeX: "every vertex `x` is an end of at most `deg_{H_0}(x) ≤ |Z|-1` arcs", with the proof quoted in the docstring.
- Lean: assume
  - `H_0` is loopless with all edge ends in `Z`;
  - `H^arc ⊆ H_0`;
  - the arcs are a path decomposition of `H^arc`.
- Lean, conclusion: for every vertex `x`, `pec(arcs, x) ≤ deg_{H_0}(x)` and `deg_{H_0}(x) ≤ |Z| - 1`.

### `PVStatement` (Lemma PV, deterministic; anchor)
- TeX: quoted in the module docstring.
- Lean: for PV data `D` with `PVHyp D` (listed below) and every admissible `H_0` (listed below), there are `Hobj ⊆ H_0`, objects and phased arcs with:
  - (a) `Hobj` decomposes into `≤ 369|Pl|` objects;
  - (b) the arcs are a path decomposition of `H_0 \ Hobj`, with ends in `Rt` and `ext ≠` phase on every vertex;
  - (c) `|arcs| ≤ 4(J+1)N`, `pec ≤ deg_{H_0}`, and `deg_{H_0} ≤ N - 1`;
  - (d) `Rt = ∅ →` no arcs, and `Pl = ∅ → Hobj = ∅`.
- `PVHyp D` consists of:
  - `PVSize N`;
  - `O` spanning `Z`, a `(2^{-6}, s_O)`-expander, with `2m ≤ s_O`;
  - `A` an HB family of `O` with parameters `(m, b)`;
  - own classes spanning `Z`, `(2^{-6}, s')`-expanders, with `s' ≥ 2^{145}L^{41}`, pairwise edge-disjoint including `M`;
  - `Rt ⊔ Pl = Z`;
  - (E1′).
- `PVAdm D H_0` means:
  - `H_0` is loopless with all edge ends in `Z`;
  - `H_0 ⊇ E(M)` and `H_0 ⊇ E(R_{j,c})`.

### `COLJVRow4Statement`
- TeX: row 4, "T16* for U-lent classes: `s_Y/(8k_lend) ≥ 2^{135} t_Y L_Y^{28}(12L_Y^5)^5`, `t_Y = ⌈λ^{1.6}⌉`"; "Rows 4–7 … asserted for `r ≤ R-2`".
- Lean: under Γ1 and a valid run, for every ancestor `Y` of round `r` with `r + 2 ≤ R`:
  `2^{135}·t_Y·L_Y^{28}·(12L_Y^5)^5 ≤ s_Y/(8k_lend(Y))`.

### `COLJVRow7Statement`
- TeX: row 7, "T16* failures over `I^U(Y)` sum to at most `|V(Y)|^{-2}/4`"; the proof: "`t = t_Y ≤ 2λ^{1.6}` and `ρ^{-3} ≤ 1728L_Y^{15}`. The sum is at most `12L_Y^3·2^{86}·2λ^{1.6}L_Y^{19}·12^3L_Y^{15}N^{-3}`".
- Lean: same context (`r + 2 ≤ R`):
  `Σ_{i ∈ I^U(Y)} 2^{86}·t_Y·L_Y^{19}·(12L_Y^5)^3·N^{-3} ≤ N^{-2}/4`, where `N = |V(Y)|`.

### `COLJVRow8Statement`
- TeX: row 8, "own devices: (a) `s_r/4 ≥ 2^{150}L_Y^{42}`; (b) `s_r/4 ≥ 2^{146}L_Y^{38} log L_Y`; (c) `s_r/2 ≥ 2^{151}L_Y^{38} log L_Y`; (d) `s' := s_r/(16k_own) ≥ 2^{145}L_Y^{41}` and `s' ≥ 2⌈L_Y^6⌉`"; "rows 3 and 8 for every ancestor `Y` of round `r`" (every `r ≤ R`).
- Lean: under Γ1 and a valid run, for every ancestor `Y`, the five inequalities with `s_r = run.s G Y.1`, `log = log₂` and `k_own = 4J_Y + 1`.

### `Cor22Statement` (declared input)
- TeX: "Every graph can be decomposed into paths such that each vertex is an end of at most two of the paths."
- Lean: every loopless finset `F` of edges has a path decomposition `P` with `pec(P, v) ≤ 2` for all `v`.

### `TowerBRoundStatement` (declared input)
- TeX: "(b) For `r ≤ R`: `M_r ≤ d_r^2`; `λ_r ≤ Λ_r ≤ 2λ_r`; `λ_r^{100} ≤ s_r ≤ 2Λ_r^σ`; `s_r ≤ P_r`; and `L_Y ≤ log M_r ≤ 2λ_r` for every ancestor `Y` of round `r`."
- Lean: under Γ1(a)–(e), for a valid run with `d_1 ≥ D_*` and every round `1 ≤ r ≤ R`: exactly these six facts, with `Λ_r = log₂M_r`.

### `COLJVCountStatement` (declared input)
- TeX: s3:lemCOLJV (i), quoted in the file.
- Lean: under Γ1 and a valid run, for every ancestor `Y` of round `r`:
  - if `R ≤ r + 1` then `k_lend = 0`;
  - if `r + 2 ≤ R`, then all of the following hold, with `M = M_{r+2}` and `μ = log₂λ_r`:
    - `|I^U| ≤ 12L^3`;
    - `|I^JS| ≤ (4/3)M^2`;
    - `|I^JV| = R - r - 1 ≤ 2log* d_r + 1`;
    - `k_lend ≤ 12L^3 + (4/3)M^2 + 2log* d_r + 2 ≤ 24L^3 + (4/3)M^2 ≤ k̄(μ) ≤ λ^{3.3}`;
    - `p_Y ≥ λ^{-4}`.

## Hazards (T0 encoding decisions and statement-shape choices)

- **H1, PV-DET-SPEC (TRIAGE §2.8).** `PVStatement` is deterministic: ∀ admissible `H_0` ∃ the decomposition. The good event `𝒢_PV` and Claim 1 are not stated; the consumers use only non-emptiness.
- **H2, step-phase output shape.** Two points:
  - Arcs are **not** only the unsplit Corollary-22 paths. A trail with appended edges whose far ends both lie in `Rt` (far ends lie in `Z_j ⊆ U_{j+1} = Rt ⊔ (Pl ∩ U_{j+1})`) gives, after splitting, a non-cherry path with both ends in `Rt`, which rule (vi) declares an arc.
  - An earlier draft of this Spec wrongly characterized the arcs as the paths of `P` with both ends in `Rt`. The final Spec states only the properties that PV (b), (c) need:
    - ends in `Rt`;
    - vertices in `V(F_{j,c})` or far ends (this gives `ext ≠ c` via (s4:eqPVclass), and excludes cherry centres);
    - `|A| ≤ |P|`.
  - This is not a manuscript error. The cost paragraph's "remaining trail … becomes an arc" describes only the trails that produce no objects.
- **H3, row 7 precise form.** The per-class failure is `2^{86}t_Y L^{19}(12L^5)^3N^{-3}`: `ρ_Y^{-3}` is replaced by its bound `(12L_Y^5)^3`, as in the manuscript's derivation, and as row 4's column 2 writes `(12L_Y^5)^5`.
  - The consumer (s3:lemCOL (c), part 2) must combine this with `ρ_Y ≥ 1/(12L_Y^5)` (s5:lemZones (ii)).
  - Alternative: state row 7 with `EG.Stage1.rhoY`. Rejected, because rows 4 and 7 should use one form.
- **H4, scope of rows 4 and 7.** Stated for every ancestor with `r ≤ R-2`, with no light guard, as the lemma asserts them. For a standalone `Y`, `I^U = ∅`, and row 4 holds since `s_Y = s_r ≥ s_r/2`. This is stronger than the blueprint's light-only C4/C7 and still provable by the same derivation.
- **H5, no `N_0`** in the rows and in the two s2/s3 inputs (TRIAGE §2.6, COLJV-N0-IMPLICIT: "s3 COL/COLJV take `Gamma1 D ∧ run.Valid G D`"). `TowerBRoundStatement` follows P3A's `TowerCStatement` (`Gamma1core`, no `N_0`).
- **H6, `PVFinishStatement` takes a free `N`** with `|Pl| ≤ N`, rather than `N = |Z|`. This is a harmless generalization: Fact EG0(b) needs only `N > 1`, `α = |Pl| ≤ N` and `4β ≤ L`.
- **H7, `(1.6 : ℝ)` in `Stage1.tY`** versus `8/5` in `COLTable`. They are equal (`norm_num`). The stage-2 proof of rows 4 and 7 must convert once (CONVENTIONS "`1.6` vs `8/5`").

## Math findings

None of class T1–T3. I re-derived every step of the four rows' paths at the statement level:
- Row 4 needs `λ^{45.4} ≥ 2^{193}12^5k̄`, which follows from row 4 column 3 and row 9.
- Row 7 needs `λ^{103}/2 ≥ 12^4 2^{126}λ^{38.6}`, which follows from row 7 column 3.
- Row 8 (a)–(d), with `k_own ≤ max(1, L_Y) ≤ 2λ`, `log L_Y ≤ μ + 1`, and `L_Y^{38} log L_Y ≤ 0` when `L_Y < 1`.
- The PV (c) per-vertex argument.
- The stripping case analysis (`T = p x`, `p x q`, and longer paths).
- The type (1)/(2) counting, including the arcs from type-(1) trails (H2).
- The PV(c) arc count `4J N + 4N`.

The inequality `pec ≤ deg_{H_0}` of the CR1-PV per-vertex bound can be an equality: EGTest has an (abstract) path decomposition, a star, in which a vertex is an end of `deg_{H_0}(x) = |Z| - 1` arcs. This star is not an output of the PV procedure, so it does not by itself show that no bound in terms of Corollary-22 end counts can hold (fix round 1, m1). The manuscript's actual reason for the switch from the Corollary-22 end count (`8J + 8 + b`) to `deg_{H_0}` is the finish-stripping scenario: a rooted `x` that is an interior vertex of many Corollary-22 paths `p_i x y_i …` with `p_i ∈ Pl_J` ends one arc per such path, and Corollary 22 does not limit their number. EGTest now instantiates this scenario (`StripScenario`: `x = 0` ends three arcs and no Corollary-22 path). The downstream parameter must absorb the degree bound `|Z| - 1`; part 2 (`M_l - 1 ≤ t_Y`) has to check that.

## Non-vacuity (`EGTest/ProbeP4A.lean`)

- `PVStepPhaseStatement`, on `Fin 4` (`Rt = {1,2,3}`, `W = {0}`, `F = {01}`, `P = [01]`, far ends 2, 3): all hypotheses hold, and the conclusion holds with `D = [03]` (single edge), `A = [2 0 1]` (the appended trail, which is an arc), `Q = []`.
- `PVStripStatement`, on `T = 0 1 2` (`Rt = {1}`, `PlJ = {0,2}`): the hypotheses hold, and the witness strips both edges and leaves `[1]`.
- `PVArcEndsDegStatement`: the star at 0 on `Fin 5` split into four one-edge arcs satisfies the hypotheses, and the inequality `pec ≤ deg_{H_0}` is attained (`pec = deg = |Z| - 1 = 4`). This is an abstract path decomposition, not a PV output.
- Finish-stripping scenario (fix round 1, m1), `StripScenario` on `Fin 7`: `Rt = {0,4,5,6}`, `Pl_J = {1,2,3}`, `E_2 = {10,04,20,05,30,06}`, Corollary-22 paths `[1 0 4], [2 0 5], [3 0 6]` (a path decomposition, `pec ≤ 2`, `pec(·, 0) = 0`). The hypotheses of `PVStripStatement` hold for each path, and the witness `strip_witness` strips `p0` and keeps the arc `0 y`. The arcs `[0 4], [0 5], [0 6]` path-decompose `H^arc = {04,05,06} ⊆ E_2`, and `pec(arcs, 0) = 3` while `pec(paths, 0) = 0`; the degree bound covers it (`3 ≤ deg_{E_2}(0) = 6 = |Z| - 1`). With `k` paths `p_i 0 y_i` the same gives `k` arcs at `0`.
- Inputs of `PathEndsCount`/`Cor22`, `Closing` and `TrailSplit` hold on small lists.
- The size hypothesis of the finish holds at `N = 2^{1024}`.
- **Not cheap:**
  - `PVHyp`: expanders with `s' ≥ 2^{145}L^{41}` on `N ≥ 2^{1024}` vertices.
  - `Gamma1 D ∧ run.Valid G D` with an ancestor (rows): this needs astronomically large graphs. Γ1 alone is non-vacuous (GAMMA unit). Column 3 holds at `μ = 8192` (`EGTest.Params`).

## Open questions

1. Should `PVStatement` live here (the Vortex area) and be locked from this draft, or be re-authored by the s4 statement owner? P4B needs it as its declared input for lemChild.
2. Lovász → Cor 22: confirm that the Ext unit owns `Cor22Statement` (file `EG/Spec/Ext/Cor22.lean`), rather than a P4 unit.
3. H3: confirm the `(12L_Y^5)` form for row 7 (the alternative is `rhoY`).

## Fix round 1 (review `work/p2b/P4A.review1.md`, verdict APPROVE)

Every issue was re-checked against the TeX (s4.tex 455–642, s1.tex 1644–1740, s2.tex lemTower/lemCap `\deps`) and the locked Defs.

| Issue | Verdict | Action |
|---|---|---|
| **m1** (minor): the star example is said to show "no bound in terms of the Corollary-22 end counts alone can hold" | valid (overstatement) | **fixed.** Reworded in this note (refutation target, math findings, non-vacuity) and in the `EGTest/ProbeP4A.lean` module docstring and the star example: the star only shows that `pec ≤ deg_{H_0}` is attained. Added the optional test: section `StripScenario` of `EGTest/ProbeP4A.lean` instantiates the manuscript's finish-stripping scenario (s4.tex 633–636): three Corollary-22 paths `p_i 0 y_i` with `p_i ∈ Pl_J`, the hypotheses and a witness (`strip_witness`) of `PVStripStatement` for each, and the resulting arcs, which path-decompose `H^arc ⊆ E_2` with `pec(arcs, 0) = 3`, `pec(paths, 0) = 0`, `deg_{E_2}(0) = 6 = |Z| - 1`. |
| **m2** (minor): `PVStepPhaseStatement` allows a cherry `u₁ w u₂` with `w ∈ V(F)` to be declared an arc | valid (as a note; no Spec defect) | Re-derived: the arc vertex clause admits `w` when `w ∈ V(F_{j,c})` (interior of a path of `Paths_{j,c}`), and (s4:eqPVclass) then gives `ext(w) ≠ c`; far ends have `ext = *`; `|A| ≤ |P|` still binds. A cherry with `w ∉ V(F)` is excluded (`w ∈ W` is not a far end). No Spec change. **Recorded** in "Planned stage-2 files → Notes for the stage-2 composition": PV (b) for step arcs is derived from the vertex clause and (s4:eqPVclass), not from "arcs never come from cherries". |
| **m3** (minor): `TowerBRoundStatement` carries only `Gamma1core` (drops Γ2–Γ4 and `n ≥ N_0`) | valid observation; kept | Verified: lemTower's `\deps` (s2.tex) list only `s1:condG1`, `s1:condG2` among the Γ's (no Γ3, Γ4); lemCap's `\deps` list `s1:condG2`, whose item (a) `D_* ≥ 2^{117}` is `EG.Gamma1core.gamma2a`; Γ2(b), (c) follow from Γ1 and, by s1:condG2, none of their proofs uses them (Γ2(b) is proved in lemTower (b) itself); `n ≥ N_0` is STR-N0. Statement unchanged (same form as `TowerCStatement`). The analysis is now in the module docstring of `EG/Spec/HB/TowerB.lean` (docstring only), and the stage-2 note asks the s2 tower unit to confirm it and record it next to STR-N0 in TRIAGE (orchestrator-owned; not edited here). |
| **c1** (cosmetic): row 7 uses `(12L_Y^5)^3` for `ρ_Y^{-3}` (H3); the consumer needs a bridge | valid | **fixed.** New file `EG/Proof/Lend/COLJVRows.lean` (the planned stage-2 file): `EG.zpow_neg_three_le_of_ge_inv` (`L > 0`, `ρ ≥ 1/(12L^5)` ⇒ `ρ^{-3} ≤ (12L^5)^3`) and `EG.colJVRow7_rhoY` (from `COLJVRow7Statement`, `L_Y > 0` and `ρ_Y ≥ 1/(12L_Y^5)` of s5:lemZones (ii) as hypotheses: the row-7 sum with `EG.Stage1.rhoY ^ (-3)`). Both proved, 0 sorry. The docstring of `EG/Spec/Lend/COLJVRows.lean` names the bridge (docstring only). |
| **c2** (cosmetic): rows 4/7/8 for standalone `Y`, `PVStatement` (c) for all `x : V`, `PVFinishStatement` with a free `N` | not an issue | True, harmless strengthenings (H4, H6); the reviewer re-derived each. No change. |
| **c3** (cosmetic, manuscript): the fixes note of s4:lemPV says "second inequality of (s4:eqPVt) deleted", but the display still has two inequalities | valid (ambiguous wording) | Checked against git: before commit `743d255` (manuscript v2, CR1-PV) the display was `2+b ≤ t and 8J+8+b ≤ 2^7L^8+2^7L^2+8log₂L+9 ≤ 2^9L^8 = t`; the deleted "second inequality" is the conjunct `8J+8+b ≤ …`. The note is accurate but reads ambiguously next to the current chain. Nothing depends on it. The manuscript is outside this unit's scope, so it is **not edited**; suggested wording for the manuscript owner: "the former bound `8J+8+b ≤ t` removed". |

Files changed:
- `EGTest/ProbeP4A.lean` (m1: docstrings, new section `StripScenario`);
- `EG/Spec/HB/TowerB.lean` (m3, module docstring only);
- `EG/Spec/Lend/COLJVRows.lean` (c1, module docstring only);
- `EG/Proof/Lend/COLJVRows.lean` (c1, **new**; root import `EG.Proof.Lend.COLJVRows` to be added to `EG` by the orchestrator);
- this note.

No statement (`def …Statement` body) and no Defs file changed.

Checks:
- `lake build` of `EG.Spec.HB.TowerB`, `EG.Proof.HB.TowerB`, `EG.Spec.Lend.COLJVRows`, `EG.Proof.Lend.COLJVRows`, `EG.Proof.Lend.COLJVCount`, `EG.Proof.Vortex.PVCore`, `EG.Proof.Ext.Cor22` and of the imports of `EGTest/ProbeP4A.lean`: success.
- `scripts/check.sh EG/Proof/Lend/COLJVRows.lean`: rc=0, 0 errors, 0 sorry.
- `scripts/check.sh EGTest/ProbeP4A.lean`: rc=0, 0 errors, 0 warnings, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan on `EG.Proof.Lend.COLJVRows`, `EG.Proof.Vortex.PVCore`: 808 constants, 0 sorryAx, 0 violations.
- `sorry` still appears only in the three declared-input stubs `EG.cor22`, `EG.towerBRound`, `EG.colJVCount`.

## Re-dispatch check of stage 1 (2026-09-29, after review round 2, verdict APPROVE)

The stage-1 task was dispatched again after the workflow resumed. Nothing was re-authored: every stage-1 file above was already approved by both review rounds, so this pass only re-verified them.
- No Defs/Lib file imported by the P4A modules changed after `EG/Defs/Probe/P4A/PVHyp.lean` was written.
- `lake build` of the 13 P4A modules (Defs, Spec, Proof): success. The only warnings are the three `sorry`s of the declared-input stubs (`EG.cor22`, `EG.towerBRound`, `EG.colJVCount`).
- `scripts/check.sh EGTest/ProbeP4A.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.

Review 2's remaining issues are all cosmetic:
- **c1:** in `PVStepPhaseStatement`, the arc clause (`≥ 1` edge) is deliberately the PV (b) form. The manuscript's (P3) "length ≥ 2" is kept only for the to-be-closed paths `Q`, because finish arcs can have one edge. Recorded here; no Spec change.
- **c2:** redundant conjunct in `TowerBRoundStatement`. No change.
- **c3:** tracking of m3 (s2 tower unit). No change.

## Fix round 1 (re-dispatch, 2026-09-29; review `work/p2b/P4A.review1.md` re-dispatch, verdict APPROVE)

The review file `P4A.review1.md` was rewritten by a new clean-room round-1 reviewer. Its five issues were each re-checked against the TeX and the Lean files. The issues of the earlier round 1 (the section "Fix round 1" above) keep their verdicts. **No statement body (`def …Statement`) and no Defs file changed.** Only docstrings changed.

| Issue | Verdict | Action |
|---|---|---|
| **m1** (minor): `PVArcEndsDegStatement` is a general fact about path decompositions, so proving it cannot refute anything. The refutation-relevant comparisons are P4B's (per-bundle `(l, c, slot)` per-vertex pair multiplicity, and `\|Z\| - 1 ≤ M_l - 1 < t_Y`, s5:lemParent Step 5). | valid (scope observation). The statement is correct and faithful to (c); only its role as refutation target is overstated. This note already said the link `\|Z\| - 1 ≤ M_l - 1 ≤ t_Y` belongs to P4B. | **fixed (docs).** The docstring of `PVArcEndsDegStatement` (`EG/Spec/Vortex/PVCore.lean`) now says that it does not involve the PV procedure and names the P4B comparisons. **For the orchestrator (TRIAGE is orchestrator-owned; not edited here):** record in TRIAGE §4 row P-4 that the P-4 refutation target counts as **hit only once P4B's Step-5 multiplicity statement (per-bundle per-vertex pair multiplicity and `\|Z\| - 1 ≤ M_l - 1 < t_Y`) is written and reviewed**. P4A exercises only the PV(c) side (the degree bound, `2 + b ≤ t`) and rows 4 and 7 at multiplicity `t_Y`. |
| **c1** (cosmetic): step arcs need only `≥ 1` edge (`2 ≤ a.length`), while TeX (P3) gives length `≥ 2` | not an issue. Deliberate: it is the PV (b) form ("paths of length at least 1"), which is all the composition uses; `Q`-paths keep `≥ 2` edges. Already recorded (review 2, c1). | none |
| **c2** (cosmetic): `TowerBRoundStatement` repeats `Λ_r ≤ 2λ_r` in the per-ancestor conjunct | valid but harmless. It transcribes the TeX chain "`L_Y ≤ log M_r ≤ 2λ_r`" literally, and it is logically redundant. The statement is kept, because it is faithful and was approved by two review rounds, and the reviewer marks the fix optional and deferred to the s2 unit. | **docs only.** A bullet in the module docstring of `EG/Spec/HB/TowerB.lean` records the redundancy and says the full lemTower (b) Spec of the s2 unit may drop it. |
| **c3** (cosmetic): `PVStatement` sits at the natural path of the future s4 Lemma-PV Spec, so a second Spec could be written in parallel | valid (placement risk) | **docs.** The module docstring of `EG/Spec/Vortex/PV.lean` now says that the s4 statement owner adopts this file rather than writing a second Lemma-PV Spec. Open question 1 still stands for the orchestrator. |
| **c4** (cosmetic): rows 4 and 7 are asserted for standalone `Y` too | not an issue. It is a true strengthening (H4): `Stage1.tY` is total; row 7 is trivial because `I^U = ∅`; row 4 holds since `s_Y = s_r`. | none |

Files changed (docstrings only):
- `EG/Spec/Vortex/PVCore.lean` (m1);
- `EG/Spec/HB/TowerB.lean` (c2);
- `EG/Spec/Vortex/PV.lean` (c3);
- this note.

Checks:
- `lake build` of the following: success.
  - `EG.Spec.Vortex.{PV, PVCore, Observations}`, `EG.Spec.HB.TowerB`, `EG.Spec.Lend.COLJVRows`;
  - `EG.Proof.Vortex.PVCore`, `EG.Proof.HB.TowerB`, `EG.Proof.Lend.{COLJVRows, COLJVCount}`, `EG.Proof.Ext.Cor22`.
  - The only warnings are the three declared-input `sorry`s.
- `scripts/check.sh EGTest/ProbeP4A.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.

## Proof round 1 (stage 3) — done (2026-09-30)

**All 14 probe nodes are proved with 0 `sorry`.** The only `sorryAx` in their axiom closure comes from the three declared-input stubs `EG.cor22`, `EG.towerBRound`, `EG.colJVCount`. No Spec, Defs, stub or test file was edited.

| Node | Lean name | File |
|---|---|---|
| (S) | `EG.trailSplit`, `EG.trailRepInner` | `EG/Proof/Vortex/Observations.lean` (Lib `EG/Lib/Vortex/Trail.lean`) |
| (E) | `EG.pathEndsParity`, `EG.pathEndsCount` | same (Lib `EG/Lib/Vortex/Ends.lean`) |
| (C) | `EG.closing` | same (Lib `Trail.lean`) |
| steps (iv)–(vi), cost | `EG.pvStepPhase` | `EG/Proof/Vortex/PVCore.lean` (Lib `EG/Lib/Vortex/{StepPhase,StepCount,StepAssemble,StepOutput,StepCost}.lean`) |
| (s4:eqPVstep), (s4:eqPVt) | `EG.pvStepCost`, `EG.pvT` | `PVCore.lean` |
| finish stripping | `EG.pvStrip` | `PVCore.lean` (Lib `EG/Lib/Vortex/Strip.lean`) |
| finish | `EG.pvFinish` | **new** `EG/Proof/Vortex/PVFinish.lean` (Lib `EG/Lib/Vortex/{Finish,FinishCore}.lean`); uses `EG.factEG0b` (proved) and `EG.cor22` (declared input) |
| PV (c) per-vertex bound | `EG.pvArcEndsDeg` | `PVCore.lean` |
| rows 4, 7, 8 | `EG.colJVRow4`, `EG.colJVRow7`, `EG.colJVRow8` | `EG/Proof/Lend/COLJVRows.lean` (Lib **new** `EG/Lib/Lend/Standing.lean`); use `EG.towerBRound`, `EG.colJVCount` |

How the last pieces go:
- `EG.PVFin.finish_core` (`FinishCore.lean`, the `sorry` noted in the re-dispatch check is gone): objects `D_1 ++` stripped single edges; arcs = the stripped remainders with `≥ 2` vertices, tagged with their phase; `H^obj = E_1 ∪ {stripped edges}`. The per-class permutation `S ++ E(T') ~ E(T)` is lifted twice with `flatMap2_perm`. Counts: stripped edges `≤ Σ_c Σ_{p ∈ Pl_J} pec(𝒫_c, p) ≤ 8|Pl_J|`; arcs `≤ Σ_c |𝒫_c| ≤ 4|Rt ∪ Pl_J|` by (E) (`IsPathDecomp.length_le_card`). `Pl_J = ∅` gives `E_1 = ∅` and no stripped edge.
- `EG.pvFinish`: phases by `EG.exists_phase`, Corollary 22 per phase class, Fact EG0(b) with `β = 64`, `α = |Pl|` (`N > 1` from `L ≥ 2^{10}`).
- Rows. Setup (`EG.colJV_rows_setup`): `λ = λ_r ≥ 2^{256}`, `2^{log λ} = λ`, column 3 at `μ = log λ` (Γ1(f), `μ ≥ loglog D_*` since `d_r ≥ D_*`), (B1) `0 ≤ L_Y ≤ 2λ` and (B3) `λ^{100} ≤ s_r` from `towerBRound` (with `D_* ≤ d_1` from `Valid`). (B4) `|V(Y)| ≥ λ^{103}/2` is proved from the HB definitions (`Standing.card_ancVerts_ge`: pre-parts have `P_r ≤ |Z^0|`, (L1) for light parts). `t_Y ≤ 2λ^{1.6}` (`1.6 = 8/5` converted once). Row 4 uses `k_lend ≤ λ^{3.3}` and `|I^U| ≤ 12L_Y^3` from `colJVCount` and the exponent identity `42.1 + 1.6 + 3.3 + 53 = 100`. Row 7 uses `64.4 + 1.6 + 37 = 103`. Row 8 uses `k_own ≤ L_Y/2 + 1 ≤ 2λ` (`Standing.kown_le`; the TeX writes `k_own ≤ L_Y`), `log L_Y ≤ μ + 1` and `L^m log L ≤ (2λ)^m (μ + 1)` also when `log L_Y < 0`.
- Small cleanups in files of this unit: two unused simp arguments (`FinishCore.lean`), a deprecated `List.Sublist.cons₂` (`Trail.lean`), `push_neg` → `push Not`.

Remaining: nothing for P4A. Stuck goals: none.

Math findings: none (T1–T3). One remark only: the TeX's "`k_own ≤ L_Y`" (rows 3 and 8) needs `L_Y ≥ 1`, which holds by (B4); the Lean proof uses `k_own ≤ L_Y/2 + 1 ≤ 2λ` instead, valid for every `L_Y ≥ 0`.

Checks:
- `lake build EG.Proof.Lend.COLJVRows EG.Proof.Vortex.PVFinish EG.Proof.Vortex.PVCore EG.Proof.Vortex.Observations`: success. The only `sorry` warnings are the three stubs.
- `scripts/check.sh` on `FinishCore.lean`, `Standing.lean`, `PVFinish.lean`, `COLJVRows.lean`, `Trail.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EG` on those four modules: 2724 constants, 0 violations. `sorryAx` appears only in `EG.cor22`, `EG.towerBRound`, `EG.colJVCount` and, transitively, in `EG.pvFinish` (via `cor22`) and `EG.colJVRow{4,7,8}`, `EG.colJV_rows_setup`, `EG.colJV_klend_facts` (via `towerBRound` / `colJVCount`). All other nodes are axiom-clean apart from the standard axioms.

Root imports for the orchestrator to add to `EG` (I did not edit `EG.lean`): `EG.Lib.Lend.Standing`, `EG.Proof.Vortex.PVFinish`. The earlier Lib files (`EG.Lib.Vortex.{Trail,Ends,Strip,StepPhase,StepCount,StepAssemble,StepOutput,StepCost,Finish,FinishCore}`) and `EG.Proof.Vortex.Observations` too, if they are not yet listed.

## Re-dispatch check of stage 1 (2026-09-30, second re-dispatch)

The stage-1 task was dispatched again. Nothing was re-authored, and no Spec, Defs, stub or test file was edited. The stage-1 files above were approved by both review rounds and by the re-dispatch fix round, so this pass only re-verified them.
- **Dependency change since stage 1:** `EG/Defs/Gamma/Full.lean` (GAMMA unit, uncommitted, 2026-09-30 00:13). The diff is **docstring only**: a junk-range remark on `Gamma3`, saying that a Spec taking `Gamma3` alone must add `2 < D` or `Gamma1 D`. No P4A Spec uses `Gamma3`: the rows and `COLJVCountStatement` take `Gamma1 D`, and `TowerBRoundStatement` takes `Gamma1core`. So no P4A statement is affected. No other Defs file imported by P4A changed.
- `lake build` of the 13 P4A stage-1 modules plus the EGTest imports `EG.Lib.Vortex.Params` and `EG.Lib.Found.PathDecomp`: success. The only warnings are the three declared-input `sorry`s (`EG.cor22`, `EG.towerBRound`, `EG.colJVCount`).
- `lake build EG.Proof.Vortex.PVCore EG.Proof.Vortex.Observations`: success, with no `sorry` warning.
- `scripts/check.sh EGTest/ProbeP4A.lean`: rc=0, 0 errors, 0 sorry.
- `python3 -I scripts/lint.py`: 0 findings.
- Stage-3 note: `EG/Lib/Vortex/FinishCore.lean` (proof round 1, `pvFinish` in progress) contains one `sorry` (line 121). It is not imported by any stage-1 module or by `EG.Proof.Vortex.PVCore`. It is proof-round work in progress, not a stage-1 artifact, and it was left untouched.

## Proof round 1 — resume check (2026-09-30, after usage-limit interruption)

This pass continued the proof round, which had been interrupted. The "Proof round 1 (stage 3) — done" section above describes the current state. Nothing was left to prove, so no Lean file was edited in this pass.
- The note in "Re-dispatch check of stage 1 (second re-dispatch)" about a `sorry` in `EG/Lib/Vortex/FinishCore.lean` (line 121) is **stale**. That file now has no `sorry`, and neither does any other `EG/Lib/Vortex/*`, `EG/Lib/Lend/Standing.lean`, `EG/Proof/Vortex/{Observations,PVCore,PVFinish}.lean` or `EG/Proof/Lend/COLJVRows.lean` file.
- `EG/Proof/Vortex/PV.lean` (stub `EG.pvLemma`) belongs to **P4B**: it is P4B's declared input [s4:lemPV]. It is not a P4A file and P4A did not touch it.
- `lake build EG.Proof.Lend.COLJVRows EG.Proof.Vortex.PVFinish EG.Proof.Vortex.PVCore EG.Proof.Vortex.Observations`: success (2260 jobs).
  - The only `sorry` warnings come from the three declared-input stubs.
  - There are two cosmetic linter warnings, in `StepCount.lean:52` (`<;>`) and `StepAssemble.lean:84` (unused `hp`). I left them alone to avoid rebuilds.
- `python3 -I scripts/lint.py`: 0 findings.
- Axiom scan: `scripts/Axioms.lean --prefix EG` on the same four modules.
  - 2724 constants, 0 violations.
  - `sorryAx` appears directly only in the stubs `EG.cor22`, `EG.towerBRound` and `EG.colJVCount`.
  - It appears transitively in `EG.pvFinish` and `EG.colJVRow{4,7,8}` / `EG.colJV_rows_setup` / `EG.colJV_klend_facts`.
- `git status` shows no change under `EG/Spec` or `EG/Defs`.

Proved: all 14 probe nodes (table above). Remaining: none. Stuck goals: none.
