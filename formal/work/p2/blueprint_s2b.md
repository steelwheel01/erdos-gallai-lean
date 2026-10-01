# P2-U formalization blueprint: chunk s2b (s2: structure of a valid run, EL, overlap constants, degree recursion, existence, lacunary sums, tower facts, rule GC, ORIGIN^tau, parentless mass, tau+ constants remark)

Manuscript: `proofs/manuscript/s2.tex` lines 709-1515 (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s2b.json` (same content, one object per label, same field names as `nodes_s1.json` / `nodes_s2a.json`). Line numbers refer to `s2.tex`. This chunk builds on the data model proposed in `blueprint_s2a.md` (split trees `EG.HB.STree`, `Run`, `Run.Valid`, round objects indexed by (round, address)); Lean names in `code` that already exist were checked against `formal/EG/**` (EG.FGraph, IsExpander, eBetween, deg, deleteVerts, EG.Obj, EG.cycleEdges, EG.Spec.CapStatement); all `EG.HB.*` names are proposals (from s2a or new here). No node of this chunk involves randomness.

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s2:propStructure` | proposition | Spec EG/Spec/HB/Structure.lean | 650 | 3 | risk (STR-PARTITION-ENCODING) |
| `s2:lemEL` | lemma | Spec EG/Spec/HB/Structure.lean | 80 | 1 | note (EL-STATIONARY) |
| `s2:propOV` | proposition | Spec EG/Spec/HB/Overlap.lean | 550 | 4 | risk (OV-IMPLICIT-DSTAR) |
| `s2:propDegRec` | proposition | Spec EG/Spec/HB/DegRec.lean | 500 | 3 | risk (DR-ROUND-LOCAL) |
| `s2:propExists` | proposition | Spec EG/Spec/HB/Exists.lean | 450 | 4 | risk (EX-GAMMA-NEEDED) |
| `s2:lemLacunary` | lemma | Spec EG/Spec/HB/Lacunary.lean | 500 | 3 | risk (LAC-LOGSTAR) |
| `s2:lemTower` | lemma | Spec EG/Spec/HB/Tower.lean | 750 | 3 | risk (TOW-LOGSTAR) |
| `s2:lemGC` | lemma | Spec EG/Spec/HB/GC.lean | 100 | 1 | note (GC-I-DEFINITIONAL) |
| `s2:propOrigin` | proposition | Spec EG/Spec/HB/Origin.lean | 400 | 3 | risk (OR-GRAFT-DUP) |
| `s2:propParentless` | proposition | Spec EG/Spec/HB/Parentless.lean | 350 | 2 | note (PL-BAD-SCOPE) |
| `s2:remTauConstants` | remark (with Table s2:tabTauConstants) | none | 0 | 1 | note (REM-NO-FORMAL) |

Estimated new Lean for this chunk: **~4330 lines** (not counting the split-tree, graft and Run foundations, which are counted in s2a). **No blocker originates in this chunk.** It inherits the pending blocker HB-M-INTEGER of s2:defHBtp (M_l real vs integer); every M_l inequality of this chunk (propDegRec, lemTower(b),(c)) was re-checked under both readings and needs no change. The mathematics of all ten results was re-derived line by line and found correct as stated, modulo implicit hypotheses. The main problems are of formalization shape: (1) three results (lemCap(ii), propOV, propDegRec) must hold for rounds of UNFINISHED executions (propExists), which the run-level data model of s2a cannot express (DR-ROUND-LOCAL); (2) several statements hide Gamma hypotheses, and propExists is FALSE with Gamma2(a) alone (explicit counterexample, EX-GAMMA-NEEDED); (3) propOV and propOrigin need a graft API that does not exist yet (OV-GRAFT, OR-GRAFT-DUP); (4) lemLacunary(iv) and lemTower(a),(d) need a real-valued log* library (LAC-LOGSTAR, TOW-LOGSTAR).

## 2. Cross-cutting decisions proposed for the integrator

- **Round-local API (DR-ROUND-LOCAL; decide in P2-D before `EG/Defs/HB/Run.lean` is locked).** Define every round object as a function of (n, input graph H = G_l, round choice c): `Round.graph'`, `Round.twoLevel`, `Round.prePartAddrs`, `Round.D`, `Round.home`, `Round.guests`, `Round.isL1/isL2/isGC/isLight`, `Round.assign`, `Round.E`, `Round.next` (= G_{l+1}), and a predicate `Round.Valid n H Dstar c` (cycles, s=0 tree stopping exactly at (eps,0)-expanders, tau-runs at big pieces stopping exactly at (eps,s)-expanders, complete home order). Then `Run.graph G (l+1) := Round.next n (Run.graph G l) c_l`, `run.X G l a := Round.X n (run.graph G l) c_l a`, and `Run.Valid G Dstar run := (∀ l ∈ [1,R], Dstar ≤ d l ∧ Round.Valid n (graph l) Dstar c_l) ∧ d (R+1) < Dstar`. State s2:lemCap(ii), s2:propOV and s2:propDegRec at round level (hypotheses `Round.Valid`, `Dstar ≤ Round.d n H`) with run-level corollaries; propExists then quantifies over lists of round choices that are not valid runs.
- **Gamma hypotheses per Spec (s1 blueprint: s2 statements take only the items they use).** None: lemEL, lemGC(i)-(iii), propOrigin(a),(b),(d), propParentless(i),(iii), propStructure(iv), lemLacunary(i) and its sequence form. `Gamma2a Dstar` (2^117 <= D_*): propStructure(i),(iii), propOV (implicit in the manuscript!), propDegRec classification, propOrigin(c). `Gamma1core Dstar`: propDegRec bounds, propExists (essential: counterexample with Gamma2a only), lemLacunary(ii)-(iv), lemTower, lemGC(iv), propParentless(ii). Gamma1core implies Gamma2a (log2 D_* >= 2^256); provide the transfer lemmas `Gamma1core D → D ≤ d → Gamma1Items (logb 2 (logb 2 d))` and `Gamma1core D → Gamma2a D` once in Lib. (Provided in `EG.Lib.Found.Gamma`: `Gamma1core.items_loglog`, `Gamma1core.gamma2a`, and for lemLacunary(iv) `Gamma1core.items_logb_of_le : Gamma1core D → logb 2 D ≤ x → Gamma1Items (logb 2 x)`.)
- **Unused manuscript hypotheses are dropped (strengthening).** propStructure's 'n >= N_0' (N0Cond is not even definable in the s2 layer: CONST-LAYERING) is replaced by 0 < n (needed for |E_0| < D_* n/2); 'd_1 >= D_*' is kept only in lemTower (where it gives R >= 1) and is irrelevant elsewhere.
- **Stationary G_l.** `Run.graph G l` must be defined for every l and be stationary for l > R+1; the Run API proves antitonicity `j ≤ l → (graph l).edges ⊆ (graph j).edges` for all j, l. Used by lemEL and propOrigin ('every round l > r'), and by s5/s6.
- **Graft API (extends HB-GRAFT of s2a).** Needed lemmas: graft of a WF tree is WF; internal/leaf addresses of the graft; graphAtD (a ++ b) of the graft = graphAtD b of the grafted tree rooted at the piece graph; labels and sizes transported; OVHyp transported (propOV); deleted(graft) = ⋃ deleted(tau-run at big pieces) when the base tree deletes nothing; Dup(tau-run) ⊆ Dup*(graft); u ∉ Dup*(graft) ⇒ u lies in exactly one base leaf (propOrigin); node graphs are subgraphs of the root (propStructure(i), propDegRec).
- **Split `isLight` into named components** `isL1`, `isL2`, `isGC` (and `isGCPart := isL1 ∧ isL2 ∧ ¬isGC`): propOV(K3) sums over 'pre-parts failing (L1)', lemGC(iii) speaks about GC-parts.
- **New Defs introduced by this chunk** (all in `EG/Defs/HB/`): `epsA D` and `psiPool x` (they enter the explicit eps_1, eps_2 of s7 and Gamma4, so they must be Defs, not Lib), `Run.nuAnc` (nu_l, with r + 2 <= l), `HypH x0 F` (condition (H)). Spec-local/Run API: `EdgeSrc`/`srcs`/`srcEdges` (partition of E(G)), `pieceOf`, `TypeBeta`/`TypeAlpha`, `lightIncidences`, `Parentless`. From s1: `EG.logStar`, `EG.logIter` (needed here in lemLacunary(iv), lemTower(a),(d)).
- **Lacunary sums in sequence form.** State lemLacunary(i) and (iii) for abstract real sequences; the run version is a corollary. s5-s7 apply the lemma to 1/M_l, psi(M_l), 1/P_r, F(lambda_{l-2}) and should not need a run.
- **Design constraints that are not Specs** (checked by the Defs reviewer): D_l, home_l, S_Z, pre-parts must not depend on (GC)/lightness (lemGC(i), propExists 'GC feeds back into nothing'); homeOrder must list all pre-parts (lemEL); Run.Valid must contain both directions of the stopping rules (HB-STOPRULE), edge-disjointness of the long cycles and 'length >= T_l' (propStructure(iii)).
- **Undeclared dependencies found in proofs** (for msreport): propStructure uses s1:condG2(a) (via lemCap) and s1:defObject; propOV uses s2:lemCap and s1:condG2(a); propDegRec uses s1:condG2(a); propExists uses s1:condG1, s1:condG2, s1:citDef11; lemLacunary and lemTower use s1:convGraphs (log*); propOrigin uses s2:defTauRules (through thin cut). Declared but not logically used: s1:citLem14 (propStructure), s1:condG2 as a hypothesis in lemTower (it PROVES Gamma2(b)), s2:lemCap and s2:lemEL in propOrigin (parenthetical / redundant), all refs of s2:remTauConstants.

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| risk | `s2:propStructure` | STR-PARTITION-ENCODING | The displayed partition of E(G) mixes three kinds of index (long cycles of each round, E_0, the assigned sets E_l(Z) of light parts and standalone pre-parts). A faithful Lean statement needs an explicit index type (EdgeSrc) with 'pairwise disjoint' AND 'union = E(G)'; 'E(Cyc_l)' as a disjoint union needs the cycles of one round to be pairwise edge-disjoint, which Run.Valid must require (Nodup of the flattened cycle edges, HB-R1-ENCODING), and each cycle's edges must lie in E(G_l). 'Iterating from l = 1 to l = R' is an induction over rounds that needs E_l(Z) ∪ E(Cyc_l) ⊆ E(G_l) \ E(G_{l+1}) and E(G_{l+1}) ⊆ E(G_l) for every l; about 150 Lean lines of real work hidden in one sentence. If the Run definition makes E l a and the passed-down set two filters of ONE assignment function (assign l e : Option address, blueprint_s2a), the per-round partition is definitional and the risk drops to routine. |
| risk | `s2:propOV` | OV-IMPLICIT-DSTAR | Implicit hypothesis. The statement fixes 'a valid run and a round r <= R' with no condition on D_*, but the proof needs Lemma 14^tau(b) for every tau-run, i.e. tau_r >= 128 s_r log^2 \|Q\|, which is s2:lemCap(ii) and needs D_* >= 2^117 (Gamma2(a)). Without it the c = 1.6 bound \|N''\| <= 1.6 eps \|U'\|/log^2 m can fail (\|H_out\| + \|H_in\| <= s\|U\|/tau is only small if tau >> s log^2 m), and S_r <= 1.21 n is unproved. Also log2 P_r > 0 needs P_r >= 2. The Spec must carry Gamma2a Dstar. Every downstream citation of (K1)-(K3) (s5-s7) is under Gamma anyway. |
| risk | `s2:propOV` | OV-GRAFT | Applying Lemma OV to the composite tree needs the graft API (HB-GRAFT): the graft of t0_r with the tau-runs is a split recursion on G'_r (WF), its internal nodes are the internal nodes of t0_r and (a ++ b) for internal b of the tau-run at piece a, with the same graphs (graphAtD (a ++ b) = graphAtD_{tauRun a} b rooted at Q_a), labels, sizes and first-child sizes; its leaves are the small pieces and the tau-run leaves. OVHyp at c = 1.6 then follows from OVInstance (c = 1, monotone in c) and lem14tau(b). Without this API the manuscript's one-paragraph 'composite tree' argument has no Lean proof path. |
| risk | `s2:propOV` | OV-CONST-TIGHT | Inherits OV-CONST-546 (blueprint_s2a): 5.46 = 1.6(1 + 1/c_OV) needs log2(4/3) >= 0.414508 (use 17/41: 2^65 >= 3^41; 12/29 is NOT enough). The intermediate (eqDupComposite) 5.46 * 1.21 = 6.6066 <= 6.61 has 0.05% slack; with exact values 1.6(1+1/c_OV)/(1 - 5.472 eps) = 5.4552/0.829 = 6.5805. The stated final constants (7.6, 15.2, 16, 30.4, 1.37) have >= 13% slack. Recommend: prove the Delta bound from the sharp OV(a) form with exact c_OV and derive 6.61; do not route through rounded 3.42 or 5.5. |
| risk | `s2:propDegRec` | DR-ROUND-LOCAL | s2:propExists applies s2:lemCap(ii), s2:propOV and s2:propDegRec 'to every round l with d_l >= D_* of any (possibly unfinished) execution'. In the blueprint_s2a data model Run.Valid includes the stopping clause d_{R+1} < D_*, so an unfinished execution is NOT a valid run and the run-level Specs do not apply to it. Unless the round objects are defined as functions of (input graph H = G_l, n, round choice c) with a predicate Round.Valid n H Dstar c, and Run.Valid := (∀ l ≤ R, Round.Valid (graph l) (choice l) ∧ Dstar ≤ d l) ∧ d (R+1) < Dstar, the existence proof has to re-prove these three results. P2-D must fix this BEFORE EG/Defs/HB/Run.lean is locked; the three Specs should then be stated at round level with run-level corollaries. |
| risk | `s2:propExists` | EX-GAMMA-NEEDED | 'For every graph G a valid HB run exists' is FALSE without Gamma1 (the manuscript assumes Gamma globally but the statement does not say so). Counterexample with Gamma2(a) only: D_* = 2^117, G = K_m with m = 2^117 + 1. Then d_1 = m - 1 = 2^117 >= D_*; T_1 = 2^117 * 117^2 > m, so there is no long cycle and G'_1 = G; K_m is an (eps,0)-expander, so the s=0 recursion must stop at the root and the only piece is K_m with m < P_1 = ceil(117^103); there are no pre-parts, every edge passes down, G_2 = G_1, and the procedure repeats forever: no finite valid run exists. (For D_* <= 0 it never stops either.) The Spec must assume Gamma1core D_* (items (a),(b) suffice, via propDegRec). |
| risk | `s2:propExists` | EX-TERMINATION-SHAPE | 'Every sequence of admissible choices terminates' is a statement about a nondeterministic procedure. With finite trees and finite lists in the data model, its Lean content is: (T1) every tau-rule split under tau >= 128 s log^2 \|H\| strictly shrinks both children (s2:lem14tau termination Spec) and the s=0 splits shrink; (E1) existence of each choice; (E2) a bound on the number of valid rounds. A statement 'Run.Valid G D run' alone does not express termination. The formulation needs the round-local API (DR-ROUND-LOCAL): RunTerminatesStatement quantifies over lists of round choices that are NOT valid runs (no stop condition). |
| risk | `s2:propExists` | EX-CONSTRUCT | Existence requires constructing, by well-founded recursion on \|H\|: an s=0 tree that stops EXACTLY at (eps,0)-expanders (both directions of the leaf iff expander clause of Run.Valid, HB-STOPRULE), a tau-run for every big piece (needs lemCap(ii) at round level, i.e. pieces are (eps,0)-expanders of G'_l and G'_l has no long cycle), a maximal family of edge-disjoint long cycles (greedy: Finset induction on the edge set), and a home order (any list of the pre-part addresses). Choice of witnesses via Classical.choose from ¬IsExpander. About 300 Lean lines; nothing deep, but every piece of the Valid predicate must be satisfiable, which is also the non-vacuity check of Run.Valid (a Valid that is never satisfiable would make every s2-s7 Spec vacuous). |
| risk | `s2:lemLacunary` | LAC-LOGSTAR | (iv) for the three log*-functions needs a real-valued log* with a verified API that does not exist yet (CONV-LOGSTAR): log*(2^x) = 1 + log* x for x > 0 (rpow), log* z <= z (z >= 1) and log* z <= 1 + log2 z (z >= 4) by induction, the tower characterization 'log* z = j iff tw(j-1) < z <= tw(j)', tw(j+1) >= 4 tw(j) once tw(j) >= 4, and several 'holds at y_0 and the right side grows faster' inequalities (2 log2 y + 6 <= y^{1/2} for y >= 2^12, 2 log2 y + 6 <= y^{1/4} for y >= 2^32, 2 log2 u + 8 <= u^{1/2} for u >= 2^12, 95 log2 y + 8 <= y^{1/2} for y >= 2^30) whose Lean proofs need monotonicity arguments (derivatives or log bounds). Correct as stated (re-derived), but the largest real-analysis block of s2 (~250 lines). |
| risk | `s2:lemTower` | TOW-LOGSTAR | (a) and (d) need the real log* API (CONV-LOGSTAR): the induction d_{r+2i} <= log^[i] d_r for i <= k = log* d_r uses log^[i] d_r > 1 for i < log* d_r (Nat.find minimality) and log^[k] d_r <= 1; (d) needs log* d_r = 2 + log* mu for d_r = 2^{2^mu} (two applications of log*(2^y) = 1 + log* y, y > 0) and log* mu <= 1 + log2 mu (mu >= 4). Correct (re-derived) but depends on foundations that do not exist yet; 'log^[i]' beyond log* is junk in Lean (CONV-LOGJUNK). |
| risk | `s2:propOrigin` | OR-GRAFT-DUP | (a),(b) need correspondences between the grafted tree T_r and its components that the manuscript takes for granted: (1) u ∉ Dup*_r ⇒ u lies in exactly one piece (a vertex in two pieces lies in two leaves of T_r, via SEP(0) on the subtrees below the pieces); (2) Dup(tau-run of Q) ⊆ Dup*_r (leaves of the tau-run are leaves of T_r at a ++ b); (3) deleted(T_r) = ⋃_{big pieces q} deleted(tauRun q) (first level deletes nothing: OV instance); (4) the leaf address of Y in the tau-run is Y with the piece prefix removed, so thin cut applies to (tauRun q, Q, leaf Y'). All four are graft lemmas (HB-GRAFT). Without them the proof of (b), which s6:thmCONC/thmCONCL use for every ancestor, has no path. |
| note | `s2:propStructure` | STR-N0 | The hypothesis 'n >= N_0' is unused in the proof and cannot even be stated in the s2 layer (N0Cond needs the s4 size predicates; s1 blueprint CONST-LAYERING). Drop it (this strengthens the statement). The hypothesis 'd_1 >= D_*' is also unused except for n > 0: with n = 0 Lean gives d_1 = 0 < D_*, R = 0, E_0 = ∅ and the claim \|E_0\| < D_* n/2 reads 0 < 0, false. The Spec therefore carries 0 < G.card (implied by n >= N_0 or by d_1 >= D_* > 0). |
| note | `s2:propStructure` | STR-GAMMA-MIN | The proof cites Gamma1(a) but uses only P_l >= 11 (Lemma HS needs z >= 11), D_* >= 8 (k_0 = floor(log2 D_*) >= 3 in the long-cycle count), log2 d_l >= 1 (T_l >= d_l) and s2:lemCap(ii) (needs D_* >= 2^117). All follow from Gamma2(a): D_* >= 2^117. The Spec takes Gamma2a only (s1 blueprint decision: s2 statements take only the Gamma items they use); (iv) needs no hypothesis on D_* at all. |
| note | `s2:propStructure` | STR-MINDEG | 'delta(H_Y) > s_Y' via the Def-11 remark needs eps_Y > 0 and \|V(Y)\| >= 2 (T0-def11-eps) and uses (iv) for \|V(Y)\| >= P_r/2 >= 2. State it pointwise (every v ∈ V(H_Y) has deg > s_Y), never via EG.FGraph.minDeg (0 on the empty graph). |
| note | `s2:propStructure` | STR-HS-SUBGRAPH | (i)(b) applies Lemma HS with W = S_Z, s_W = s_l/2 and needs 'every u has at most s_l/2 neighbours in S_Z IN X^0_Z'; (L2) gives this in G'_l[Z^0]. The transfer needs E(X^0_Z) ⊆ E(G'_l) (node graphs of the grafted two-level tree are subgraphs of the root: SEP(0') through the graft, HB-GRAFT). Keep (L2) on G'_l[Z^0] in the Defs (HB-L2-GRAPH). |
| note | `s2:propStructure` | STR-LAMBDA-LE-LAMBDA | s2:lemTower(b) cites 'Lambda_r >= lambda_r' from 'the proof of' (i); a Lean proof cannot cite a proof. The Spec of (i) includes lamOf d_r <= logb 2 M_r as an explicit conjunct (done in the sketch), or lemTower proves it directly (M_r >= T_r >= d_r). |
| note | `s2:propStructure` | STR-CYCLE-COUNT | Σ\|Cyc_l\| <= n: grouping rounds by k = floor(log2 y_l) with y_l = d_l (y_{R+1} = d_{R+1} is used for l = R) and Σ_{k >= k_0} k^-2 <= 1/(k_0 - 1). Correct; needs 'length >= T_l' for every cycle of Cyc_l (a Valid field), cycle length = number of edges (EG.cycleEdges length), and \|E(G_l)\| - \|E(G'_l)\| = total cycle length (edge-disjointness). \|Cyc_l\| is the NUMBER of cycles (list length). |
| note | `s2:propStructure` | STR-II-DUPLICATE | (ii) restates s2:lemCap(ii); do not create a second Spec (it would need the same D_* >= 2^117 hypothesis, which the manuscript's 'valid run' hides: CAP-GAMMA-EXPLICIT). |
| note | `s2:propStructure` | STR-X0-CROSS-ROUND | The parenthetical warning is load-bearing for Spec review: only the H_Y (X_Y for light Y) are pairwise edge-disjoint across rounds; X^0_Y of light pre-parts of different rounds may share guest-core edges (passed down). A reviewer must reject a Spec claiming disjointness of all X^0 across rounds. |
| note | `s2:lemEL` | EL-STATIONARY | 'every round l > r' includes l = R+1 (G_{R+1} carries E_0; used by s6) and, in Lean, all l > R+1 unless the statement bounds l. The Run definition must make graph G l stationary for l > R+1 (no round choice left), and the Run API must provide antitonicity of graph edges in l for ALL l; otherwise state l ≤ run.R + 1 and check that s6:thmCONCL and s5:lemKRED only use such l. |
| note | `s2:lemEL` | EL-HOMEORDER-COMPLETE | The proof needs steps (2) and (3) to assign an edge WHENEVER some light part (resp. standalone pre-part) contains both ends, whatever the order. With the blueprint_s2a encoding (find? over homeOrder) this holds only if homeOrder lists ALL pre-parts; Run.Valid must require homeOrder.toFinset = prePartAddrs (it does in blueprint_s2a). Independent of the HB-R5-ORDER decision. |
| note | `s2:propOV` | OV-LCA | (K3) second bound: for u ∈ Y^0 ∩ Dup*_r, the lowest common ancestor nu of Y and another leaf containing u has u in both children, hence u ∈ N''_nu (SEP(0)), and \|nu\| >= \|Y^0\| >= P_r, so dup_{>=P_r}(u) >= 1. In Lean: longest common prefix of the two addresses; needs 'vertex in both children ⇒ ∈ N''' and 'sizes shrink along prefixes' (SEP API). u in Dup*_r but in no pre-part contributes mu = 0 (harmless). |
| note | `s2:propOV` | OV-NU-DEF | nu_l ('ancestors of rounds at most l-2') needs its own Def with r + 2 <= l and 1 <= r (ANC-ROUND-OFFSET); for l <= 2 it is 0. The manuscript's sum Σ_{r <= l-2} ranges over r <= min(l-2, R). |
| note | `s2:propOV` | OV-L1-PRED | 'pre-parts failing (L1)' requires (L1) as a separately named predicate (isLight is a conjunction L1 ∧ L2 ∧ GC). Split the Def so that K3 and GC-parts (s2:lemGC) can refer to the components. |
| note | `s2:propOV` | OV-DUP-NAMES | Four different objects: Dup (a vertex set of one split recursion, SEP), Dup*_r (vertex set, all leaves of T_r), dup_r (a number, pre-parts only, s2:defAncestors), dup_{>=M}(v)/Delta_{>=M} (counts of duplication events, OV). (K3) uses Dup*_r, (K2) dup_r. Lean names must keep them apart (ANC-DUP-POSPART). |
| note | `s2:propDegRec` | DR-GAMMA | Uses Gamma1(a),(b) at mu = log2 x = log2 lambda_l >= log2 log2 D_*: x >= 2^256, x >= 2^14 * 105 * log2^3 x, hence x >= 20 + 6 log2 x, x > 105 log2 x, x^2 >= 2^107. Transfer lemma needed: Gamma1core D → D <= d → Gamma1Items (logb 2 (logb 2 d)). The classification part needs only Gamma2(a) (through lemCap(ii) for (a)); the Spec split above reflects this. |
| note | `s2:propDegRec` | DR-M-INTEGER | Depends on the pending blocker HB-M-INTEGER (s2:defHBtp). Checked: with M_l := ceil(max(2^40, 2^16 T log^4 T)) every claim survives (M_l <= 2^20 x^6 2^x + 1 <= 2^{2x} = d_l^2; Lambda_l <= 2x; s_l <= Lambda^100 + 1). Write the statement with (MOf d : ℝ) so it is type-agnostic. |
| note | `s2:propDegRec` | DR-COUNTERFACTUAL | 'declaring a pre-part a GC-part (instead of light) can only decrease the set of passed-down edges' compares the defined procedure with a modified one; it is not a proposition about a valid run. Formalize only the factual part (standalone pre-parts pass none of their leaf-graph edges down: last conjunct of DegRecKindsStatement). If a later proof needs the comparison, it must be stated for an assignment function parametrized by the set of light pre-parts (monotonicity lemma). |
| note | `s2:propDegRec` | DR-LEAF-NONEMPTY | 'a leaf with q vertices has fewer than qP_l/2 edges' is false for q = 0 (0 < 0). Leaves of valid trees are nonempty (tau-split children have n_1 >= \|U'\| >= 1, n_2 = m - \|U'\| >= 1; s=0 children likewise), but that is a lemma; state the bound as 2\|E\| <= q(q-1) <= q P_l or require q >= 1. |
| note | `s2:propDegRec` | DR-KINDS-SUPERSET | The counts in (a)-(c) bound the full kind sets (all deleted edges, all small-leaf edges, all guest edges), not only the passed-down ones; some deleted edges are re-assigned by (R5)(2),(3). The d_{l+1} bound uses Σ(small leaf sizes) + Σ(light \|Z^0\|) <= S_l <= 1.21 n (distinct leaves of T_l) and s_l <= P_l. Guest edges between two guests are double-counted in Σ_u \|N(u) ∩ S_Z\| (upper bound, harmless). Constant chain: 4 * 1.12 = 4.48 <= 4.5; 2 * 4.48 = 8.96 <= 9; 2 * 0.605 = 1.21. |
| note | `s2:propDegRec` | DR-REAL-NUMERICS | Final bounds: 6x^103 + 6 + 9 * 2^102 x^101 + 1.2 * 2^101 x^100 <= 6x^103 + 2^107 x^101 <= 7x^103 (x^2 >= 2^107); 7x^103 <= x^104 (x >= 7); x^105 < 2^x (105 log2 x < x). Needs d_l = 2^{lambda_l} (rpow, d_l > 0) and P_l <= x^103 + 1, s_l <= 2^101 x^100. Routine but long in Lean (~120 lines). |
| note | `s2:propExists` | EX-GC-DEFINITIONAL | '(GC) is a deterministic relabelling that feeds back into neither D_l nor home nor the guest sets' is a property of the DEFINITIONS, not a theorem. In Lean it holds iff Round.D, Round.home, Round.guests, Round.prePartAddrs are defined without isLight/isGC (true in the blueprint_s2a sketch). No Spec; the Defs reviewer must check it (a definition of home through light parts would be circular: S_Z depends on home, lightness on S_Z). |
| note | `s2:propExists` | EX-LEXI | (R1)'s 'lexicographically first cycle' is encoded as any maximal family of edge-disjoint long cycles (HB-R1-ENCODING); existence of a maximal family replaces termination of the greedy loop. |
| note | `s2:lemLacunary` | LAC-NONMONO-LOGSTAR | The three log*-functions are not claimed non-increasing (they are not: F jumps up where log* increases). (ii) does not apply to them; only (iii)+(iv): Σ F(lambda_r) <= 2 F(lambda_R) <= 4 F(x_0). A downstream use of the bound 2F(x_0) for them would be an error; the s6 proof (s6.tex:271-330) uses its own tower-halving (eqTowerHalf) and Lacunary(i) instead, consistent with this. |
| note | `s2:lemLacunary` | LAC-SEQ-FORM | State (i) and (iii) for abstract real sequences (hypotheses lam_r >= x_0 and lam_r >= 2^{lam_{r+1}/A}) and derive the run version: s5-s7 apply the lemma to other round sequences (1/M_l, psi(M_l), F(lambda_{l-2}), 1/P_r) and must not need a run to do so. |
| note | `s2:lemLacunary` | LAC-DOMAIN | F : [x_0,∞) → [0,∞) becomes F : ℝ → ℝ with hypotheses on Set.Ici x0 only; nonnegativity is needed for (i) (X_r >= 0). Real exponents: x^{-a}, 2^{x/A} are Real.rpow; lambda_r > 0 needed for rpow identities. |
| note | `s2:lemLacunary` | LAC-SHIFT-NAT | Shifted sums use lambda_{l-2} with ℕ subtraction; they are only claimed for 3 <= l <= R (R >= 3). (R - l + 1) and (R - r + 1) are ℕ casts. Statement (iii)'s 'likewise for F(lambda_{l-2})' is spelled out explicitly in the Spec (the manuscript gives it in (ii) only). |
| note | `s2:lemLacunary` | LAC-GAMMA | Only Gamma1(a),(b) are used (x >= 2^256; x/A >= 101 log2 x; x >= 2A log2 x; x >= A log2^2 x / 4; x/A >= 2^12; x_0 >= 4 log2 x_0; 2^{x_0-2} >= x_0). Transfer lemma: Gamma1core D → x >= log2 D → Gamma1Items (log2 x) (since log2 x >= log2 log2 D). |
| note | `s2:lemLacunary` | LAC-COMMENTARY | The closing paragraph (how round-l quantities are summed; the M_l^3(...)/lambda^95 example using M_l <= lambda_{l-2}^{1.6} from lemTower(b)) is commentary with a forward pointer; no Spec. Its arithmetic (95 - 3*1.6 = 90.2) is trivially correct. |
| note | `s2:lemTower` | TOW-NAT-SUB | 'R - r <= 2 log* d_r - 1' and 'R - r <= 2 log* d_r + 2' are ℕ statements with subtraction; state the first as R - r + 1 <= 2 log* d_r (valid because log* d_r >= 1) or in ℤ. s6.tex:377 uses 'R - r - 1 <= 2 log* d_r + 1'; all consistent. lambda_{l-2}, P_{l-2}, M_{l-1} need l >= 3 (resp. 2) in the Spec (ℕ subtraction). |
| note | `s2:lemTower` | TOW-GAMMA-ITEMS | Uses Gamma1(a)-(d) at three different points of the ray: mu = log2 lambda_r ((a),(c),(d) items), u = log2 lambda_{l-2} (Gamma1(c) for M_l <= lambda^1.6: 210 log2(105u) <= 1.6u), v = log2 log2 d_{l-1} ((a),(b) for 2^y >= 2 y^{2A}). All >= log2 log2 D_* because d >= D_*. The Spec takes Gamma1core (items (a)-(e)); (e) unused here. |
| note | `s2:lemTower` | TOW-PSI-RATIO | Σ psi(M_l) <= 2.1 psi(D_*) is NOT an instance of Lacunary(i) (the ratio 0.512 > 1/2): it needs the geometric bound Σ_{k>=0} 0.512^k = 1/0.488 = 2.049 <= 2.05 and psi decreasing on [1,∞) (psi'(x) = (6/ln 2 - 6 log2 x - 12)/x^2 < 0) and psi(2M) = psi(M)(1/2 + 3/(6 log2 M + 12)) <= 0.512 psi(M) for log2 M >= 40 (3/252 = 0.0119). psi(M_R) <= psi(D_*) needs M_R >= d_R >= D_*. Correct. |
| note | `s2:lemTower` | TOW-M-INTEGER | Depends on the pending HB-M-INTEGER decision (s2:defHBtp). Checked every M_l claim under the ceiling definition: M_l <= d_l^2 (slack 2^{2x} vs 2^20 x^6 2^x), M_l <= (A log lambda)^{2A} (via d_l^2), M_{l-1} >= d_{l-1} >= 2 d_l^2 >= 2M_l, Σ 1/M_l <= 2/M_R <= 2/D_*, psi monotone, log2 M_l >= 40. No change needed. |
| note | `s2:lemTower` | TOW-EPSA-DEF | eps_A is used in the explicit formulas of eps_1, eps_2 (s7) and hence in Gamma4; it must be a Def (EG.HB.epsA) available to the s7 layer with exactly this formula (31 eps / (C' log2 log2 D_*)); similarly psi (pool term of eps_X). Only 30.4 <= 31 is needed in (e). |
| note | `s2:lemTower` | TOW-B-FROM-PROOF | (b) takes 'Lambda_r >= lambda_r' and 's_r >= lambda_r^100' from 'the proof of' propStructure(i). Include them in StructureExpStatement (done in its sketch) or prove them directly here (M_r >= 2^16 T_r log^4 T_r >= T_r >= d_r); a Lean proof cannot cite a proof. |
| note | `s2:lemTower` | TOW-C-EXPONENTS | (c) with sigma = 100: 2^{sigma+11} = 2^111, sigma+2 = 102, C' = sigma + 3 = 103 (P_r >= lambda^103). theta^GC >= lambda^{102.5} > 2^111 lambda^102 > tau_r needs lambda^{1/2} > 2^111, i.e. log2 lambda_r > 222 (Gamma1(a): >= 256). Real exponent -1/2 (rpow) in theta^GC; theta^GC = ceil(\|Z^0\| lambda^{-1/2}) >= \|Z^0\| lambda^{-1/2}. |
| note | `s2:lemTower` | TOW-E-USES-K2 | (e)'s consequences use (K2) of s2:propOV (\|D_l\| <= 7.6 eps n/log P_l, Σ\|A_Z\| <= 15.2 eps n / log P_l) and therefore inherit OV-IMPLICIT-DSTAR (Gamma2(a), implied by Gamma1core) and OV-CONST-TIGHT. |
| note | `s2:lemGC` | GC-I-DEFINITIONAL | (i) is a statement about the order of definitions, not a proposition about a run. Lean: enforced by the Defs (D, home, guests, prePartAddrs, X0, DupStar must not reference isLight/isGC); record as a Defs-review checklist item (shared with EX-GC-DEFINITIONAL). No Spec. |
| note | `s2:lemGC` | GC-III-WHICH-PART | 'every edge of G'_r with both ends in Y^0 is assigned at round r' does not say to which part; edges not in X^0_Y may go by (R5)(2) to a light part or by (R5)(3) to another standalone pre-part earlier in the order. A Spec claiming 'assigned to Y' (E_r(Y) ⊇ E(G'_r[Y^0])) would be FALSE in general; only E(X^0_Y) ⊆ E_r(Y) holds. |
| note | `s2:lemGC` | GC-EBETWEEN | e_{X^0_Y}(x, Y) counts X^0_Y-edges between x and the light part Y = Y^0 \ S_Y; with EG.FGraph.eBetween use {x} and Y^0 \ S_Y (disjoint because x ∈ S_Y), as CONVENTIONS require. theta^GC is a natural number (ceiling); the comparison is in ℕ. |
| note | `s2:lemGC` | GC-IV-GAMMA | (i)-(iii) hold for every valid run without any hypothesis on D_*; (iv) needs Gamma1core (lambda_r^{1/2} > 2^111 and tau_r <= 2^111 lambda^102). Split the Spec accordingly (the manuscript's statement has no hypothesis at all; Gamma is implicit). |
| note | `s2:propOrigin` | OR-TYPE-DEF | 'ux was deleted by the tau-run of Q' must be a definition: membership in the deleted set of the tau-run of the piece above Y (TypeBeta above), equivalently deletion at an address of T_r extending the piece address. It must NOT be 'ux ∈ F'' of some node of T_r' (a first-level node deletes nothing, so equivalent, but the equivalence is a lemma). |
| note | `s2:propOrigin` | OR-THINCUT-NO-GAMMA | (b) uses thin cut, which needs every split of the tau-run to be a tau-rule split with s_nu < tau: here s_nu = s_r and tau_r = ceil(128 s_r log2^2 M_r) >= 128 * 1600 * s_r > s_r for every d (M_r >= 2^40 by the max in (R2), s_r >= 1). So (a),(b),(d) need NO hypothesis on D_*; only (c) needs Gamma2(a). The manuscript's parenthetical appeal to lemCap(ii) is not needed. |
| note | `s2:propOrigin` | OR-L-BEYOND | 'for every round l > r' uses E(G_l) ⊆ E(G_{r+1}) for all l > r, including l = R+1 and (in Lean) l > R+1: needs the stationary G_l and antitonicity lemma of EL-STATIONARY. |
| note | `s2:propOrigin` | OR-TAU-NAT | '<= tau_r - 1' with tau_r ∈ ℕ, tau_r >= 1: state as count < tau_r (as in the thin-cut Spec) to avoid ℕ subtraction; ceil(tau_r) = tau_r since tau_r is an integer by (R2). |
| note | `s2:propOrigin` | OR-C-POINTER | (c) is literally (K3) of s2:propOV; do not restate (it would need Gamma2a, which (a),(b) do not). |
| note | `s2:propOrigin` | OR-EXACTLY-ONE | Exclusivity is by x ∉ Y^0 in (β) versus x ∈ S_Y ⊆ Y^0 in (α). 'Exactly one' must be stated as an exclusive disjunction (as in the sketch), since s6 uses both 'every edge is (α) or (β)' and 'standalone ⇒ all edges are (β), so h ∉ Y^0'. |
| note | `s2:propParentless` | PL-BAD-SCOPE | 'Bad any set of light parts' becomes an arbitrary Finset of (round, address) pairs; non-light or out-of-range members only add nonnegative terms to the bound (strengthening). The sum's \|Y\| must be partVerts (the LIGHT part's vertex set Y^0 \ S_Y), not Z0; R - r(Y) is ℕ subtraction (0 for r > R, harmless). The s5 consumer (s5:defStages, eqPl) must instantiate Bad with demoted OR parent-bad parts (RT2-I9): that is an obligation of the s5 blueprint, not of this Spec. |
| note | `s2:propParentless` | PL-J0-OFFSET | 'x ∈ F_Z iff j_0(x) >= l - 1' mixes a WithTop ℕ (j_0 is ∞ for vertices in no pre-part; here x ∈ Z^0 so j_0(x) <= l is finite) with ℕ subtraction; write l <= j_0(x) + 1. It relies on the 1-indexed rounds and on anc_l(x) := ∅ for l <= 2 (ANC-ROUND-OFFSET): with 0-indexed rounds the equivalence and (K4) change. |
| note | `s2:propParentless` | PL-COUNT-ENCODING | 'The number of such pairs' is the card of a Finset of (v, (l, a)); the per-vertex argument needs: at most one light part per round containing v (propStructure(iv)(e)), so pairs of v are indexed by distinct rounds l >= j_1(v); rounds j_1 + 2 .. R number R - j_1 - 1 <= R - j_1. The double counting Σ_v [Y_1(v) ∈ Bad](R - j_1) <= Σ_{Y ∈ Bad} \|Y\|(R - r(Y)) needs v ∈ Y_1(v) and that Y_1(v) is determined by v. |
| note | `s2:propParentless` | PL-II-GAMMA | (ii) needs Gamma1core (via lemTower(a),(b): items (a)-(c)) and lemCap(ii) (\|Z\| <= M_l, Gamma2(a)); (i),(iii) need no hypothesis on D_*. The manuscript's 'd_1 >= D_*' is irrelevant for (i),(iii); in Lean (ii) is vacuous unless R >= 3. |
| note | `s2:propParentless` | PL-II-LOG | \|Z\| L_Z^4 <= M_l log^4 M_l needs log2 monotone and \|Z\| >= 1 (L_Z >= 0) for the fourth power to be monotone; true since light parts have >= P_l/2 vertices. |
| note | `s2:remTauConstants` | REM-NO-FORMAL | Nothing to formalize. The left-hand column (plain HB*: 1.28n, 3.5 eps S/log P, 2.6n/P, 4.5, 9, 18) is 'neither used nor proved'; the P2 statement reviewers must reject any Spec in s3-s7 that uses a left-hand constant (notation.txt migration list maps them to the tau+ values). |
| note | `s2:remTauConstants` | REM-ROUNDING | The table's '5.5 eps S/log P' is a rounding of lem14tau(b)'s proved 5.46 eps S/log M (1.6(1 + 1/c_OV) = 5.4552); the 1.21n composite-tree value is what propOV proves (1.37n is the stated, looser (K1) constant). Consistent; no Spec should use 5.5 where 5.46 is proved without checking OV-CONST-546. |

## 4. Nodes

### `s2:propStructure` — proposition: structure of a valid run (s2.tex:709)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/Structure.lean: StructureExpStatement (i), StructurePartitionStatement (iii), StructureVertexStatement (iv); (ii) is NOT restated (it is CapRunStatement of s2:lemCap(ii)). Needs a small Run API def EdgeSrc/srcEdges (EG/Defs/HB/Run.lean or Lib).

**Statement (precise restatement).** HYPOTHESES (Lean): 2^117 <= D_* (Gamma2(a); the manuscript cites Gamma1(a) but only uses consequences P_l >= 11, D_* >= 8, lambda_l >= 1 and, through s2:lemCap(ii), D_* >= 2^117), a valid HB*^{tau+} run on the finite simple graph G, and 0 < n := |V(G)| (the manuscript's n >= N_0 and d_1 >= D_* are replaced by this: see STR-N0). Rounds are 1-indexed, 1 <= l <= R. Constants: d_l = 2|E(G_l)|/n, lambda_l = log2 d_l, T_l = d_l log2^2 d_l, M_l, Lambda_l = log2 M_l, s_l = ceil(Lambda_l^100), P_l = ceil(lambda_l^103) as in (R0)-(R2).
(i) (a) For every l in [1,R] and every round-l pre-part Z: the leaf graph X^0_Z has vertex set Z^0 and is a (2^-5, s_l)-expander. (b) For every light pre-part Z of round l: X_Z = X^0_Z - S_Z has vertex set Z^0 \ S_Z and is a (2^-6, s_l/2)-expander (s_l/2 real). (c) For every ancestor Y of round r (s2:defAncestors: light part with H_Y = X_Y, s_Y = s_r/2, or standalone pre-part with H_Y = X^0_Y, s_Y = s_r) and every vertex v of H_Y: deg_{H_Y}(v) > s_Y (so delta(H_Y) > s_Y; V(H_Y) = V(Y) is nonempty, |V(Y)| >= P_r/2 >= 2). (d) For every r in [1,R]: s_r >= lambda_r^100 (and, from the proof, Lambda_r >= lambda_r, M_r >= T_r >= d_r).
(ii) The conclusions of s2:lemCap(ii) hold (every s=0 piece Q of round l has |Q| <= M_l; |Z^0| <= M_l; deg_{E_l(Z)}(v) <= M_l - 1; tau_l >= 128 s_l log2^2 |Q|).
(iii) (a) For every l in [1,R]: E(G_{l+1}) ⊆ E(G'_l) ⊆ E(G_l), hence d_{l+1} <= d_l. (b) PARTITION: the edge sets E(C) (C a long cycle of Cyc_l, l in [1,R]; one set per cycle occurrence), E_0 = E(G_{R+1}), E_{r(Y)}(Y) (Y a light part, i.e. a light round-r pre-part, r in [1,R]) and E_l(Z) (Z in Std_l, l in [1,R]) are pairwise disjoint and their union is E(G). [Light parts and standalone pre-parts together are all pre-parts, so equivalently: {E(C)} ∪ {E_0} ∪ {E_l(a) : l in [1,R], a a round-l pre-part} is a partition of E(G) (empty members allowed).] (c) For every ancestor Y of round r: E(H_Y) ⊆ E_r(Y), and every edge of E_r(Y) has both ends in V(Y). (d) For distinct ancestors Y ≠ Y' (any rounds, distinct (round, address) pairs): E(H_Y) ∩ E(H_{Y'}) = ∅. For distinct pre-parts Z ≠ Z' of the same round: E(X^0_Z) ∩ E(X^0_{Z'}) = ∅. (NOT claimed: X^0 of light pre-parts of different rounds are edge-disjoint.) (e) Σ_{l=1}^{R} |Cyc_l| <= n (number of long cycles). (f) |E_0| < D_* n/2.
(iv) (a) Light parts of one round are pairwise vertex-disjoint. (b) For every light part Y of round r: 2|Y| >= |Y^0| >= P_r (|Y| = |Y^0 \ S_Y|). (c) Every vertex outside D_l lies in at most one round-l pre-part. (d) The port sets U_Z = Z^0 \ D_l of distinct Z in Std_l are pairwise disjoint. (e) If v lies in the light part of a light round-l pre-part Z then home_l(v) = Z; hence each vertex lies in at most one light part per round.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| valid run, rounds, G_l, G'_l, d_l, Cyc_l, pieces, pre-parts, X^0_Z, S_Z, D_l, home_l, light/standalone, Std_l, X_Z, E_l(Z), E_0, R | (R0)-(R5) of s2:defHBtp; addresses of the two-level tree index pre-parts | s2:defHBtp | no: EG.HB.Run.* proposed in blueprint_s2a (Run.Valid, graph, graph', d, cycles, twoLevel, prePartAddrs, Z0, X0, guests, D, home, isLight, Std, partVerts, X, E, E0, R) |
| round constants lamOf, TOf, MOf, LamOf, sOf, POf, tauOf | functions of d_l, (R0)-(R2) | s2:defHBtp | no: EG.HB.lamOf ... (blueprint_s2a); MOf subject to HB-M-INTEGER |
| ancestor data ancVerts, ancGraph, ancEps, ancS | V(Y), H_Y, eps_Y, s_Y of s2:defAncestors, indexed by (round, pre-part address) | s2:defAncestors | no: EG.HB.Run.ancVerts etc. (blueprint_s2a) |
| (eps,s)-expander | Def 11 | s1:citDef11 | yes: EG.FGraph.IsExpander |
| deg, deleteVerts, sym2 (both ends in a set) | s1:convGraphs(c) | s1:convGraphs | yes: EG.FGraph.deg, EG.FGraph.deleteVerts; Finset.sym2 (Mathlib) |
| EdgeSrc / srcEdges (the index set of the partition in (iii)(b)) | inductive EdgeSrc := cyc (l i : ℕ) \| part (l : ℕ) (a : List Bool) \| zero; srcEdges (cyc l i) = (cycleEdges (cycles l)[i]).toFinset, srcEdges (part l a) = E l a, srcEdges zero = E0; srcs = valid indices | s2:propStructure(iii) | no: new (Run API) |
| long cycle, cycle edges, cycle length | well-formed cycle object; length = number of vertices = number of edges | s1:defObject, (R1) | yes: EG.Obj.cycle, EG.cycleEdges, EG.Obj.WF |
| Lemma HS (deleting a thin set keeps expansion) | s2:lemHS | s2:lemHS | no (Spec proposed in blueprint_s2a: HSStatement) |

**deps_declared** (manuscript \deps): s2:defHBtp, s2:defAncestors, s2:lem14tau, s2:lemCap, s2:lemHS, s1:citDef11, s1:citLem14, s2:lemSEP, s1:condG1

**deps_from_proof:** s2:defHBtp, s2:defAncestors, s2:lem14tau, s2:lemCap, s2:lemHS, s1:citDef11, s2:lemSEP, s1:condG1, s1:condG2, s1:defObject

**deps_notes:** s1:citLem14 is declared but not used (attribution). s1:condG1 is cited for P_l >= 11, D_* >= 8, k_0 >= 3; all follow from D_* >= 2^117, and s2:lemCap(ii) needs exactly Gamma2(a) (s1:condG2(a), undeclared). s2:lem14tau is used only for the stopping rule (leaves of tau-runs are (eps,s_l)-expanders), which in Lean is a field of Run.Valid (HB-STOPRULE), not the lemma. s2:lemSEP: (i) (edge-disjointness of leaves; every G'_l edge deleted once or in one leaf) and the monotonicity 'node graphs are subgraphs of the root' (SEP(0'), through the graft). s1:defObject: cycles of Cyc_l.

**used_by:** s2:propOV; s2:lemTower; s2:propOrigin; s2:propParentless; s3:defCOL; s3:lemCOLJV; s3:lemCOL; s5:defZones; s5:lemZones; s5:defStages; s5:lemE1; s5:lemExpect; s5:lemChild; s5:lemParent; s5:lemDemoted; s5:lemKRED; s5:remConstants; s6:lemLost; s6:lemJSLC; s6:lemJplus; s6:thmMIXC; s7:lemCand; s7:lemLift; s7:lemEXprime; s1:condGamma (pointer)

**randomness:** none: a valid run is a deterministic object built from arbitrary choices; every clause is universally quantified over Run.Valid.

**lean_shape:**

```lean
namespace EG.Spec.HB
open EG EG.HB
universe u
-- notation in sketches: d l := run.d G l, s l := sOf (d l), P l := POf (d l), lam l := lamOf (d l)
/-- [s2:propStructure] (i) -/
def StructureExpStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar →
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l,
        (run.X0 G l a).IsExpander EG.epsC (sOf (run.d G l))) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l, run.isLight G l a →
        (run.X G l a).verts = run.Z0 G l a \ run.guests G l a ∧
        (run.X G l a).IsExpander (2 ^ (-6 : ℤ)) ((sOf (run.d G l) : ℝ) / 2)) ∧
    (∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r, ∀ v ∈ (run.ancGraph G r a).verts,
        run.ancS G r a < ((run.ancGraph G r a).deg v : ℝ)) ∧
    (∀ r ∈ Finset.Icc 1 run.R, lamOf (run.d G r) ≤ Real.logb 2 (MOf (run.d G r)) ∧
        lamOf (run.d G r) ^ 100 ≤ (sOf (run.d G r) : ℝ))
/-- [s2:propStructure] (iii) -/
def StructurePartitionStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → 0 < G.card → run.Valid G Dstar →
    (∀ l ∈ Finset.Icc 1 run.R, (run.graph G (l + 1)).edges ⊆ (run.graph' G l).edges ∧
        (run.graph' G l).edges ⊆ (run.graph G l).edges ∧ run.d G (l + 1) ≤ run.d G l) ∧
    (↑(run.srcs G) : Set EdgeSrc).PairwiseDisjoint (run.srcEdges G) ∧
    (run.srcs G).biUnion (run.srcEdges G) = G.edges ∧
    (∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r,
        (run.ancGraph G r a).edges ⊆ run.E G r a ∧ run.E G r a ⊆ (run.ancVerts G r a).sym2) ∧
    (∀ r₁ ∈ Finset.Icc 1 run.R, ∀ a₁ ∈ run.prePartAddrs G r₁, ∀ r₂ ∈ Finset.Icc 1 run.R,
        ∀ a₂ ∈ run.prePartAddrs G r₂, (r₁, a₁) ≠ (r₂, a₂) →
        Disjoint (run.ancGraph G r₁ a₁).edges (run.ancGraph G r₂ a₂).edges) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G l, ∀ b ∈ run.prePartAddrs G l, a ≠ b →
        Disjoint (run.X0 G l a).edges (run.X0 G l b).edges) ∧
    (∑ l ∈ Finset.Icc 1 run.R, (run.cycles l).length) ≤ G.card ∧
    ((run.E0 G).card : ℝ) < Dstar * G.card / 2
/-- [s2:propStructure] (iv) (no hypothesis on Dstar needed) -/
def StructureVertexStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ l ∈ Finset.Icc 1 run.R,
    (∀ a ∈ run.prePartAddrs G l, ∀ b ∈ run.prePartAddrs G l, a ≠ b → run.isLight G l a →
        run.isLight G l b → Disjoint (run.partVerts G l a) (run.partVerts G l b)) ∧
    (∀ a ∈ run.prePartAddrs G l, run.isLight G l a →
        (run.Z0 G l a).card ≤ 2 * (run.partVerts G l a).card ∧ POf (run.d G l) ≤ (run.Z0 G l a).card) ∧
    (∀ v ∉ run.D G l, ((run.prePartAddrs G l).filter (v ∈ run.Z0 G l ·)).card ≤ 1) ∧
    (∀ a ∈ run.Std G l, ∀ b ∈ run.Std G l, a ≠ b → Disjoint (run.ports G l a) (run.ports G l b)) ∧
    (∀ a ∈ run.prePartAddrs G l, run.isLight G l a → ∀ v ∈ run.partVerts G l a,
        run.home G l v = some a)
-- (ii): no new statement; cite EG.Spec.HB.CapRunStatement (s2:lemCap(ii)).
```

**hazards:**

- **[risk] STR-PARTITION-ENCODING.** The displayed partition of E(G) mixes three kinds of index (long cycles of each round, E_0, the assigned sets E_l(Z) of light parts and standalone pre-parts). A faithful Lean statement needs an explicit index type (EdgeSrc) with 'pairwise disjoint' AND 'union = E(G)'; 'E(Cyc_l)' as a disjoint union needs the cycles of one round to be pairwise edge-disjoint, which Run.Valid must require (Nodup of the flattened cycle edges, HB-R1-ENCODING), and each cycle's edges must lie in E(G_l). 'Iterating from l = 1 to l = R' is an induction over rounds that needs E_l(Z) ∪ E(Cyc_l) ⊆ E(G_l) \ E(G_{l+1}) and E(G_{l+1}) ⊆ E(G_l) for every l; about 150 Lean lines of real work hidden in one sentence. If the Run definition makes E l a and the passed-down set two filters of ONE assignment function (assign l e : Option address, blueprint_s2a), the per-round partition is definitional and the risk drops to routine.
- **[note] STR-N0.** The hypothesis 'n >= N_0' is unused in the proof and cannot even be stated in the s2 layer (N0Cond needs the s4 size predicates; s1 blueprint CONST-LAYERING). Drop it (this strengthens the statement). The hypothesis 'd_1 >= D_*' is also unused except for n > 0: with n = 0 Lean gives d_1 = 0 < D_*, R = 0, E_0 = ∅ and the claim |E_0| < D_* n/2 reads 0 < 0, false. The Spec therefore carries 0 < G.card (implied by n >= N_0 or by d_1 >= D_* > 0).
- **[note] STR-GAMMA-MIN.** The proof cites Gamma1(a) but uses only P_l >= 11 (Lemma HS needs z >= 11), D_* >= 8 (k_0 = floor(log2 D_*) >= 3 in the long-cycle count), log2 d_l >= 1 (T_l >= d_l) and s2:lemCap(ii) (needs D_* >= 2^117). All follow from Gamma2(a): D_* >= 2^117. The Spec takes Gamma2a only (s1 blueprint decision: s2 statements take only the Gamma items they use); (iv) needs no hypothesis on D_* at all.
- **[note] STR-MINDEG.** 'delta(H_Y) > s_Y' via the Def-11 remark needs eps_Y > 0 and |V(Y)| >= 2 (T0-def11-eps) and uses (iv) for |V(Y)| >= P_r/2 >= 2. State it pointwise (every v ∈ V(H_Y) has deg > s_Y), never via EG.FGraph.minDeg (0 on the empty graph).
- **[note] STR-HS-SUBGRAPH.** (i)(b) applies Lemma HS with W = S_Z, s_W = s_l/2 and needs 'every u has at most s_l/2 neighbours in S_Z IN X^0_Z'; (L2) gives this in G'_l[Z^0]. The transfer needs E(X^0_Z) ⊆ E(G'_l) (node graphs of the grafted two-level tree are subgraphs of the root: SEP(0') through the graft, HB-GRAFT). Keep (L2) on G'_l[Z^0] in the Defs (HB-L2-GRAPH).
- **[note] STR-LAMBDA-LE-LAMBDA.** s2:lemTower(b) cites 'Lambda_r >= lambda_r' from 'the proof of' (i); a Lean proof cannot cite a proof. The Spec of (i) includes lamOf d_r <= logb 2 M_r as an explicit conjunct (done in the sketch), or lemTower proves it directly (M_r >= T_r >= d_r).
- **[note] STR-CYCLE-COUNT.** Σ|Cyc_l| <= n: grouping rounds by k = floor(log2 y_l) with y_l = d_l (y_{R+1} = d_{R+1} is used for l = R) and Σ_{k >= k_0} k^-2 <= 1/(k_0 - 1). Correct; needs 'length >= T_l' for every cycle of Cyc_l (a Valid field), cycle length = number of edges (EG.cycleEdges length), and |E(G_l)| - |E(G'_l)| = total cycle length (edge-disjointness). |Cyc_l| is the NUMBER of cycles (list length).
- **[note] STR-II-DUPLICATE.** (ii) restates s2:lemCap(ii); do not create a second Spec (it would need the same D_* >= 2^117 hypothesis, which the manuscript's 'valid run' hides: CAP-GAMMA-EXPLICIT).
- **[note] STR-X0-CROSS-ROUND.** The parenthetical warning is load-bearing for Spec review: only the H_Y (X_Y for light Y) are pairwise edge-disjoint across rounds; X^0_Y of light pre-parts of different rounds may share guest-core edges (passed down). A reviewer must reject a Spec claiming disjointness of all X^0 across rounds.

**effort:** ~650 Lean lines, difficulty 3/5 ((i) ~120 (stopping rule field, HS application via (L1),(L2), min-degree remark, s_r >= lambda_r^100 real inequality); (iii) ~380 (partition by induction over rounds, disjointness of H_Y via assignment, long-cycle count with floor-log grouping and Σ 1/k^2); (iv) ~100; EdgeSrc API ~50.)

### `s2:lemEL` — lemma: edge laminarity, EL (s2.tex:808)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/Structure.lean: ELStatement

**Statement (precise restatement).** For every valid HB*^{tau+} run (no hypothesis on D_*), every round r in [1,R], every ancestor Y of round r (a round-r pre-part a; V(Y) = Y^0 \ S_Y if light, V(Y) = Y^0 if standalone, GC-parts included) and every round l > r (l = R+1, i.e. the leftover E_0 = E(G_{R+1}), included; for l > R+1 the Lean G_l must be stationary, see EL-STATIONARY): no edge of G_l has both ends in V(Y), i.e. E(G_l) ∩ V(Y)^(2) = ∅. Proof: E(G_l) ⊆ E(G_{r+1}) ⊆ E(G'_r) ((R1), (R5)(4)); an edge of G_{r+1} is an unassigned edge of G'_r; if both ends lie in a light part, step (1) or step (2) of (R5) assigns it; if both ends lie in Y^0 of a standalone pre-part, step (1), (2) or (3) assigns it.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| G_l (all l >= 1), G'_r, assignment steps (1)-(4) of (R5) | s2:defHBtp | s2:defHBtp | no: EG.HB.Run.graph, graph', assign (blueprint_s2a) |
| ancestor vertex set V(Y) | partVerts r a | s2:defAncestors | no: EG.HB.Run.ancVerts |

**deps_declared** (manuscript \deps): s2:defHBtp, s2:defAncestors

**deps_from_proof:** s2:defHBtp, s2:defAncestors

**deps_notes:** The monotonicity E(G_{j+1}) ⊆ E(G'_j) ⊆ E(G_j) is re-derived from (R1),(R5) (it is also propStructure(iii)(a)); no labelled result is needed. ms_deps flags both declared deps as unreferenced because they are used by name ((R1),(R5)), not by \ref.

**used_by:** s2:lemGC; s2:propOrigin; s5:lemKRED; s6:thmCONCL; s6:lemJSLC; s6:lemJplus

**randomness:** none

**lean_shape:**

```lean
/-- [s2:lemEL] -/
def ELStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r, ∀ l : ℕ, r < l →
      ∀ e ∈ (run.graph G l).edges, e ∉ (run.ancVerts G r a).sym2
-- Run API lemma needed (also for propOrigin, s6): ∀ j l, j ≤ l → (run.graph G l).edges ⊆ (run.graph G j).edges
-- (with graph stationary for l > R + 1).
```

**hazards:**

- **[note] EL-STATIONARY.** 'every round l > r' includes l = R+1 (G_{R+1} carries E_0; used by s6) and, in Lean, all l > R+1 unless the statement bounds l. The Run definition must make graph G l stationary for l > R+1 (no round choice left), and the Run API must provide antitonicity of graph edges in l for ALL l; otherwise state l ≤ run.R + 1 and check that s6:thmCONCL and s5:lemKRED only use such l.
- **[note] EL-HOMEORDER-COMPLETE.** The proof needs steps (2) and (3) to assign an edge WHENEVER some light part (resp. standalone pre-part) contains both ends, whatever the order. With the blueprint_s2a encoding (find? over homeOrder) this holds only if homeOrder lists ALL pre-parts; Run.Valid must require homeOrder.toFinset = prePartAddrs (it does in blueprint_s2a). Independent of the HB-R5-ORDER decision.

**effort:** ~80 Lean lines, difficulty 1/5 (Unfold assign; case split light/standalone; antitonicity lemma from the Run API.)

### `s2:propOV` — proposition: overlap constants on HB*^{tau+}; (K1)-(K3), (F11) (s2.tex:826)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/Overlap.lean: OVRunStatement (leaf masses, K1, K2, K3, F11); plus the nu_l bound (K1, last clause). Needs Defs nuAnc and the (L1) predicate as a separate def.

**Statement (precise restatement).** HYPOTHESES (Lean): 2^117 <= D_* (implicit in the manuscript; see OV-IMPLICIT-DSTAR), a valid run, a round r in [1,R]. eps = 2^-5, n = |V(G)|, P_r = ceil(lambda_r^103) (>= 2). S_r := Σ over the leaves of the two-level recursion T_r (on G'_r) of their vertex counts; S^Q_r := Σ over the s=0 pieces (leaves of the first-level tree t0_r) of |Q|. CLAIMS: S^Q_r <= 1.12 n and S_r <= 1.21 n. Intermediate (eqDupComposite): for every real M >= 2, Delta_{>=M}(T_r) <= 5.46 eps S_r / log2 M <= 6.61 eps n / log2 M.
(K1) Σ_{round-r pre-parts Z} |Z^0| <= 1.37 n; |Std_r| <= 1.37 n / P_r; #ancestors of round r (= #round-r pre-parts, one ancestor per pre-part, V(Y) ⊆ Y^0) <= 1.37 n / P_r; hence for every l: nu_l := #{ancestors of rounds r with 1 <= r <= min(l-2, R)} <= 1.37 n Σ_{1 <= r <= min(l-2,R)} 1/P_r.
(K2) |D_r| <= dup_r <= 7.6 eps n / log2 P_r, where dup_r = Σ_{w ∈ V(G)} (mu_r(w) - 1)^+ and mu_r(w) = #round-r pre-parts containing w; and Σ_{Z ∈ Std_r} |A_Z| <= Σ_{all round-r pre-parts Z} |Z^0 ∩ D_r| <= 2 dup_r <= 15.2 eps n / log2 P_r (A_Z = Z^0 ∩ D_r).
(K3) Σ_{round-r pre-parts Z failing (L1), i.e. 2|S_Z| > |Z^0|} |Z^0| <= 30.4 eps n / log2 P_r; and Σ_{round-r pre-parts Y} |Y^0 ∩ Dup*_r| <= 16 eps n / log2 P_r (Dup*_r = vertices in >= 2 leaves of T_r, any size).
(F11) Σ_{w ∈ V(G)} mult_r(w) = Σ_{ancestors Y of round r} |V(Y)| <= 1.37 n, and mult_r(w) <= mu_r(w) for every w.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| two-level recursion T_r = graft of t0_r with the tau-runs at big pieces; leafMass; DeltaGe; dupGe; dup (Dup*_r) | s2:lemSEP, s2:lemOVgeneric, (R3) | s2:lemSEP, s2:lemOVgeneric, s2:defHBtp | no: EG.HB.STree.graft/leafMass/DeltaGe/dupGe/dup, EG.HB.Run.twoLevel/DupStar (blueprint_s2a) |
| pre-parts, Std_r, D_r, S_Z, A_Z (hubs), mu_r, dup_r, mult_r, ancestors | s2:defHBtp (R3),(R4); s2:defAncestors | s2:defHBtp, s2:defAncestors | no: EG.HB.Run.prePartAddrs/Std/D/guests/hubs/mu/dup/mult (blueprint_s2a) |
| (L1) predicate | L1 r a :⇔ 2 \|S_a\| <= \|Z^0_a\| (ℕ) | s2:defHBtp (R4) | no: split EG.HB.Run.isLight into isL1 ∧ isL2 ∧ isGC (needed here and for GC-parts) |
| nu_l | nuAnc l := #{(r,a) : 1 <= r <= R, r + 2 <= l, a ∈ prePartAddrs r} | s2:propOV (K1), s2:lemTower(b) | no: new EG.HB.Run.nuAnc (write r + 2 <= l, ANC-ROUND-OFFSET) |
| c_OV, OVHyp, OV statement, instance c = 1, lem14tau(b) | s2:lemOVgeneric, s2:lem14tau | s2 | no (blueprint_s2a: OVStatement, OVInstanceStatement, Lemma14Tau (b)) |

**deps_declared** (manuscript \deps): s2:lemOVgeneric, s2:lem14tau, s2:propStructure, s2:defAncestors, s2:defHBtp, s2:lemSEP

**deps_from_proof:** s2:lemOVgeneric, s2:lem14tau, s2:lemCap, s2:propStructure, s2:lemSEP, s2:defHBtp, s2:defAncestors, s1:condG2

**deps_notes:** propStructure is used only through (ii) = s2:lemCap(ii) (tau_r >= 128 s_r log^2|Q|, so lem14tau applies to every tau-run); this needs D_* >= 2^117 = Gamma2(a) (s1:condG2(a), undeclared). s2:lemOVgeneric: (a) at M = P_r (via eqDupComposite), (b) for mu_r <= 1 + dup_{>=P_r}, (c) for S_r, instance c = 1 for the first level and for S^Q_r. s2:lem14tau(b): tau-splits satisfy OVHyp with c = 1.6. s2:lemSEP(0): 'a vertex in both children lies in N''' (K3 second bound) and node sizes shrink downwards.

**used_by:** s2:propDegRec; s2:propExists; s2:lemTower; s2:propOrigin; s2:remTauConstants; s5:lemExpect; s5:lemParent; s5:remConstants; s6:thmCONC; s6:thmCONCL; s6:lemJSLC; s6:thmMIXC; s7:lemMULT; s7:lemVstar; s7:lemEXprime; s7:lemUHsplit; s7:propCost

**randomness:** none

**lean_shape:**

```lean
/-- [s2:propOV] -/
def OVRunStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar → ∀ r ∈ Finset.Icc 1 run.R,
    let ε : ℝ := EG.epsC; let n : ℝ := G.card; let P : ℝ := POf (run.d G r)
    ((run.tree0 r).leafMass (run.graph' G r) : ℝ) ≤ 1.12 * n ∧
    ((run.twoLevel G r).leafMass (run.graph' G r) : ℝ) ≤ 1.21 * n ∧
    (∀ M : ℝ, 2 ≤ M → ((run.twoLevel G r).DeltaGe (run.graph' G r) M : ℝ) ≤ 6.61 * ε * n / Real.logb 2 M) ∧
    -- (K1)
    ((∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a).card : ℕ) : ℝ) ≤ 1.37 * n ∧
    ((run.Std G r).card : ℝ) ≤ 1.37 * n / P ∧ ((run.prePartAddrs G r).card : ℝ) ≤ 1.37 * n / P ∧
    -- (K2)
    (run.D G r).card ≤ run.dup G r ∧ (run.dup G r : ℝ) ≤ 7.6 * ε * n / Real.logb 2 P ∧
    (∑ a ∈ run.Std G r, (run.hubs G r a).card) ≤ ∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a ∩ run.D G r).card ∧
    (∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a ∩ run.D G r).card) ≤ 2 * run.dup G r ∧
    -- (K3)
    ((∑ a ∈ (run.prePartAddrs G r).filter (fun a => ¬ run.isL1 G r a), (run.Z0 G r a).card : ℕ) : ℝ)
        ≤ 30.4 * ε * n / Real.logb 2 P ∧
    ((∑ a ∈ run.prePartAddrs G r, (run.Z0 G r a ∩ run.DupStar G r).card : ℕ) : ℝ) ≤ 16 * ε * n / Real.logb 2 P ∧
    -- (F11)
    (∑ w ∈ G.verts, run.mult G r w) = ∑ a ∈ run.prePartAddrs G r, (run.ancVerts G r a).card ∧
    ((∑ a ∈ run.prePartAddrs G r, (run.ancVerts G r a).card : ℕ) : ℝ) ≤ 1.37 * n ∧
    ∀ w, run.mult G r w ≤ run.mu G r w
/-- [s2:propOV] (K1), last clause -/
def NuAncStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar → ∀ l : ℕ,
    (run.nuAnc G l : ℝ) ≤ 1.37 * G.card *
      ∑ r ∈ (Finset.Icc 1 run.R).filter (· + 2 ≤ l), 1 / (POf (run.d G r) : ℝ)
-- Proof route: OVHyp (2^-5) 1.6 (twoLevel r) (graph' r) from OVInstance (first level; c monotone)
-- + Lemma14Tau(b) transported along the graft (needs CapRun: tau_r ≥ 128 s_r log²|Q|).
```

**hazards:**

- **[risk] OV-IMPLICIT-DSTAR.** Implicit hypothesis. The statement fixes 'a valid run and a round r <= R' with no condition on D_*, but the proof needs Lemma 14^tau(b) for every tau-run, i.e. tau_r >= 128 s_r log^2 |Q|, which is s2:lemCap(ii) and needs D_* >= 2^117 (Gamma2(a)). Without it the c = 1.6 bound |N''| <= 1.6 eps |U'|/log^2 m can fail (|H_out| + |H_in| <= s|U|/tau is only small if tau >> s log^2 m), and S_r <= 1.21 n is unproved. Also log2 P_r > 0 needs P_r >= 2. The Spec must carry Gamma2a Dstar. Every downstream citation of (K1)-(K3) (s5-s7) is under Gamma anyway.
- **[risk] OV-GRAFT.** Applying Lemma OV to the composite tree needs the graft API (HB-GRAFT): the graft of t0_r with the tau-runs is a split recursion on G'_r (WF), its internal nodes are the internal nodes of t0_r and (a ++ b) for internal b of the tau-run at piece a, with the same graphs (graphAtD (a ++ b) = graphAtD_{tauRun a} b rooted at Q_a), labels, sizes and first-child sizes; its leaves are the small pieces and the tau-run leaves. OVHyp at c = 1.6 then follows from OVInstance (c = 1, monotone in c) and lem14tau(b). Without this API the manuscript's one-paragraph 'composite tree' argument has no Lean proof path.
- **[risk] OV-CONST-TIGHT.** Inherits OV-CONST-546 (blueprint_s2a): 5.46 = 1.6(1 + 1/c_OV) needs log2(4/3) >= 0.414508 (use 17/41: 2^65 >= 3^41; 12/29 is NOT enough). The intermediate (eqDupComposite) 5.46 * 1.21 = 6.6066 <= 6.61 has 0.05% slack; with exact values 1.6(1+1/c_OV)/(1 - 5.472 eps) = 5.4552/0.829 = 6.5805. The stated final constants (7.6, 15.2, 16, 30.4, 1.37) have >= 13% slack. Recommend: prove the Delta bound from the sharp OV(a) form with exact c_OV and derive 6.61; do not route through rounded 3.42 or 5.5.
- **[note] OV-LCA.** (K3) second bound: for u ∈ Y^0 ∩ Dup*_r, the lowest common ancestor nu of Y and another leaf containing u has u in both children, hence u ∈ N''_nu (SEP(0)), and |nu| >= |Y^0| >= P_r, so dup_{>=P_r}(u) >= 1. In Lean: longest common prefix of the two addresses; needs 'vertex in both children ⇒ ∈ N''' and 'sizes shrink along prefixes' (SEP API). u in Dup*_r but in no pre-part contributes mu = 0 (harmless).
- **[note] OV-NU-DEF.** nu_l ('ancestors of rounds at most l-2') needs its own Def with r + 2 <= l and 1 <= r (ANC-ROUND-OFFSET); for l <= 2 it is 0. The manuscript's sum Σ_{r <= l-2} ranges over r <= min(l-2, R).
- **[note] OV-L1-PRED.** 'pre-parts failing (L1)' requires (L1) as a separately named predicate (isLight is a conjunction L1 ∧ L2 ∧ GC). Split the Def so that K3 and GC-parts (s2:lemGC) can refer to the components.
- **[note] OV-DUP-NAMES.** Four different objects: Dup (a vertex set of one split recursion, SEP), Dup*_r (vertex set, all leaves of T_r), dup_r (a number, pre-parts only, s2:defAncestors), dup_{>=M}(v)/Delta_{>=M} (counts of duplication events, OV). (K3) uses Dup*_r, (K2) dup_r. Lean names must keep them apart (ANC-DUP-POSPART).

**effort:** ~550 Lean lines, difficulty 4/5 (Graft transport of OVHyp ~150 (on top of the graft API counted in s2:defHBtp); S^Q, S_r, Delta ~60; K1 ~60; K2 ~80 (OV(b) at M = P_r, mu <= 2(mu-1)); K3 ~120 (LCA argument); F11 ~40; real constants ~40.)

### `s2:propDegRec` — proposition: degree recursion (s2.tex:909)

- **Manuscript referee status:** x2+RT; R6: no referee yet
- **Formalization:** Spec EG/Spec/HB/DegRec.lean: DegRecBoundsStatement (parameters and the chain of inequalities), DegRecKindsStatement (classification (a)-(c) and counts, standalone pre-parts pass nothing). RECOMMENDED: both stated at ROUND level (Round.Valid on an input graph H with d(H) >= D_*), with run-level corollaries (DR-ROUND-LOCAL).

**Statement (precise restatement).** HYPOTHESES (Lean): Gamma1core D_* (items (a),(b) are used, at mu = log2 lambda_l; Gamma2(a) follows), a valid run (or a valid round, DR-ROUND-LOCAL), a round l with d_l >= D_* (i.e. l in [1,R]). x := lambda_l = log2 d_l (so d_l = 2^x, x >= 2^256). CLAIMS: M_l <= d_l^2; Lambda_l = log2 M_l <= 2x; s_l <= P_l; and
d_{l+1} <= 1.21 P_l + 9 s_l log2 M_l <= 6 P_l + 9 s_l log2 M_l + 1.2 s_l <= 7 x^103 <= x^105 < d_l (A = 105; x^104 would suffice).
CLASSIFICATION: every edge e of G_{l+1} is of (at least) one kind: (a) e is deleted by the tau-run of a piece Q with |Q| >= P_l; for each such piece the tau-run deletes at most 4 s_l |Q| log2 |Q| edges, and all tau-runs of round l together delete at most 4.5 n s_l log2 M_l edges; (b) e is an edge of a leaf of the two-level recursion T_l with fewer than P_l vertices (a small tau-run leaf, or a piece with |Q| < P_l); a leaf with q vertices has at most q(q-1)/2 < q P_l/2 edges (q >= 1); (c) e is a GUEST EDGE: an edge of X^0_Z with at least one end in S_Z, for a light pre-part Z; for each light Z there are at most |Z^0| s_l / 2 guest edges. MOREOVER: for every standalone pre-part Z (GC-parts included), E(X^0_Z) ∩ E(G_{l+1}) = ∅. (The sentence 'declaring a pre-part a GC-part instead of light can only decrease the set of passed-down edges' is a comparison between two different procedures; see DR-COUNTERFACTUAL.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| round objects: G_l, G'_l, d_l, t0_l, pieces, tau-runs, T_l, pre-parts, X^0_Z, S_Z, light/standalone, assign, G_{l+1} | (R0)-(R5) | s2:defHBtp | no: EG.HB.Run.* (blueprint_s2a); round-local versions EG.HB.Round.* proposed here (DR-ROUND-LOCAL) |
| constants lamOf, TOf, MOf, LamOf, sOf, POf | (R0)-(R2) | s2:defHBtp | no (blueprint_s2a) |
| deleted edges of a tau-run, leaves of T_l, guest edges | STree.deleted, STree.leafAddrs, (X0 l a).edges.filter (∃ v ∈ e, v ∈ guests l a) | s2:lemSEP, s2:defHBtp | no (blueprint_s2a STree API) |
| Gamma1core | D > 2 ∧ ∀ mu >= log2 log2 D, Gamma1Items mu (items (a)-(e)) | s1:condGamma | no: EG.Gamma1core (blueprint_s1) |

**deps_declared** (manuscript \deps): s2:lem14tau, s2:lemCap, s2:propOV, s2:defHBtp, s2:lemSEP, s1:condG1, s2:lemOVgeneric

**deps_from_proof:** s1:condG1, s2:lemCap, s2:lemSEP, s2:lemOVgeneric, s2:lem14tau, s2:propOV, s2:defHBtp, s1:condG2

**deps_notes:** Gamma1(a),(b) at mu = log2 lambda_l. s2:lemCap(ii) (|Q| <= M_l; tau_l >= 128 s_l log^2|Q| so lem14tau(a) applies) needs Gamma2(a) (implied by Gamma1(a)). s2:lemSEP(i) on T_l (deleted once or in exactly one leaf). s2:lemOVgeneric instance c = 1: first-level splits delete nothing. s2:lem14tau(a): deletion bound 4 s n_0 log n_0. s2:propOV: S^Q_l <= 1.12 n and S_l <= 1.21 n.

**used_by:** s2:propExists; s2:lemLacunary; s2:lemTower; s1:condGamma (pointer)

**randomness:** none

**lean_shape:**

```lean
/-- [s2:propDegRec] parameter bounds and the chain -/
def DegRecBoundsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → ∀ l ∈ Finset.Icc 1 run.R,
    let d := run.d G l; let x := lamOf d; let M : ℝ := MOf d; let s : ℝ := sOf d; let P : ℝ := POf d
    M ≤ d ^ 2 ∧ Real.logb 2 M ≤ 2 * x ∧ s ≤ P ∧
    run.d G (l + 1) ≤ 1.21 * P + 9 * s * Real.logb 2 M ∧
    1.21 * P + 9 * s * Real.logb 2 M ≤ 6 * P + 9 * s * Real.logb 2 M + 1.2 * s ∧
    6 * P + 9 * s * Real.logb 2 M + 1.2 * s ≤ 7 * x ^ 103 ∧ 7 * x ^ 103 ≤ x ^ 105 ∧ x ^ 105 < d
/-- [s2:propDegRec] classification of passed-down edges -/
def DegRecKindsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma2a Dstar → run.Valid G Dstar → ∀ l ∈ Finset.Icc 1 run.R,
    let d := run.d G l; let T := run.twoLevel G l; let H := run.graph' G l
    (∀ e ∈ (run.graph G (l + 1)).edges,
        (∃ q ∈ run.bigPieceAddrs G l, e ∈ (run.tauRun l q).deleted (run.piece G l q)) ∨
        (∃ b ∈ T.leafAddrs, (T.graphAtD H b).card < POf d ∧ e ∈ (T.graphAtD H b).edges) ∨
        (∃ a ∈ run.prePartAddrs G l, run.isLight G l a ∧ e ∈ (run.X0 G l a).edges ∧
            ∃ v ∈ e, v ∈ run.guests G l a)) ∧
    (∀ q ∈ run.bigPieceAddrs G l, (((run.tauRun l q).deleted (run.piece G l q)).card : ℝ) ≤
        4 * sOf d * (run.piece G l q).card * Real.logb 2 (run.piece G l q).card) ∧
    (((run.bigPieceAddrs G l).biUnion (fun q => (run.tauRun l q).deleted (run.piece G l q))).card : ℝ)
        ≤ 4.5 * G.card * sOf d * Real.logb 2 (MOf d) ∧
    (∀ a ∈ run.prePartAddrs G l, run.isLight G l a →
        ((((run.X0 G l a).edges.filter (fun e => ∃ v ∈ e, v ∈ run.guests G l a)).card : ℕ) : ℝ)
          ≤ (run.Z0 G l a).card * (sOf d : ℝ) / 2) ∧
    (∀ a ∈ run.Std G l, Disjoint (run.X0 G l a).edges (run.graph G (l + 1)).edges)
-- DR-ROUND-LOCAL: the same two statements with (H : FGraph V) (c : RoundChoice V) (n : ℕ)
--   (hc : Round.Valid n H Dstar c) (hd : Dstar ≤ Round.d n H) in place of (run, l); run versions are corollaries.
```

**hazards:**

- **[risk] DR-ROUND-LOCAL.** s2:propExists applies s2:lemCap(ii), s2:propOV and s2:propDegRec 'to every round l with d_l >= D_* of any (possibly unfinished) execution'. In the blueprint_s2a data model Run.Valid includes the stopping clause d_{R+1} < D_*, so an unfinished execution is NOT a valid run and the run-level Specs do not apply to it. Unless the round objects are defined as functions of (input graph H = G_l, n, round choice c) with a predicate Round.Valid n H Dstar c, and Run.Valid := (∀ l ≤ R, Round.Valid (graph l) (choice l) ∧ Dstar ≤ d l) ∧ d (R+1) < Dstar, the existence proof has to re-prove these three results. P2-D must fix this BEFORE EG/Defs/HB/Run.lean is locked; the three Specs should then be stated at round level with run-level corollaries.
- **[note] DR-GAMMA.** Uses Gamma1(a),(b) at mu = log2 x = log2 lambda_l >= log2 log2 D_*: x >= 2^256, x >= 2^14 * 105 * log2^3 x, hence x >= 20 + 6 log2 x, x > 105 log2 x, x^2 >= 2^107. Transfer lemma needed: Gamma1core D → D <= d → Gamma1Items (logb 2 (logb 2 d)). The classification part needs only Gamma2(a) (through lemCap(ii) for (a)); the Spec split above reflects this.
- **[note] DR-M-INTEGER.** Depends on the pending blocker HB-M-INTEGER (s2:defHBtp). Checked: with M_l := ceil(max(2^40, 2^16 T log^4 T)) every claim survives (M_l <= 2^20 x^6 2^x + 1 <= 2^{2x} = d_l^2; Lambda_l <= 2x; s_l <= Lambda^100 + 1). Write the statement with (MOf d : ℝ) so it is type-agnostic.
- **[note] DR-COUNTERFACTUAL.** 'declaring a pre-part a GC-part (instead of light) can only decrease the set of passed-down edges' compares the defined procedure with a modified one; it is not a proposition about a valid run. Formalize only the factual part (standalone pre-parts pass none of their leaf-graph edges down: last conjunct of DegRecKindsStatement). If a later proof needs the comparison, it must be stated for an assignment function parametrized by the set of light pre-parts (monotonicity lemma).
- **[note] DR-LEAF-NONEMPTY.** 'a leaf with q vertices has fewer than qP_l/2 edges' is false for q = 0 (0 < 0). Leaves of valid trees are nonempty (tau-split children have n_1 >= |U'| >= 1, n_2 = m - |U'| >= 1; s=0 children likewise), but that is a lemma; state the bound as 2|E| <= q(q-1) <= q P_l or require q >= 1.
- **[note] DR-KINDS-SUPERSET.** The counts in (a)-(c) bound the full kind sets (all deleted edges, all small-leaf edges, all guest edges), not only the passed-down ones; some deleted edges are re-assigned by (R5)(2),(3). The d_{l+1} bound uses Σ(small leaf sizes) + Σ(light |Z^0|) <= S_l <= 1.21 n (distinct leaves of T_l) and s_l <= P_l. Guest edges between two guests are double-counted in Σ_u |N(u) ∩ S_Z| (upper bound, harmless). Constant chain: 4 * 1.12 = 4.48 <= 4.5; 2 * 4.48 = 8.96 <= 9; 2 * 0.605 = 1.21.
- **[note] DR-REAL-NUMERICS.** Final bounds: 6x^103 + 6 + 9 * 2^102 x^101 + 1.2 * 2^101 x^100 <= 6x^103 + 2^107 x^101 <= 7x^103 (x^2 >= 2^107); 7x^103 <= x^104 (x >= 7); x^105 < 2^x (105 log2 x < x). Needs d_l = 2^{lambda_l} (rpow, d_l > 0) and P_l <= x^103 + 1, s_l <= 2^101 x^100. Routine but long in Lean (~120 lines).

**effort:** ~500 Lean lines, difficulty 3/5 (Parameter bounds + chain ~150 (real analysis with rpow/logb); classification ~150 (SEP(i) on the graft, (R5) case analysis); counting (a)-(c) ~150 (Σ over pieces, lem14tau(a), (L2)); standalone clause ~20; round-local restatement ~30.)

### `s2:propExists` — proposition: existence and termination (s2.tex:987)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/Exists.lean: RoundExistsStatement (a valid round exists on every input graph with d >= D_*), RunTerminatesStatement (any list of valid rounds with d >= D_* has length <= |E(G)|), ExistsRunStatement (a valid run exists). Tau-run termination (T1) is Lemma14Tau's termination Spec (s2:lem14tau). The (GC)-feeds-back-into-nothing clause is a Defs design constraint, not a Spec.

**Statement (precise restatement).** HYPOTHESES (Lean; implicit in the manuscript, see EX-GAMMA-NEEDED): Gamma1core D_* (items (a),(b) used through s2:propDegRec; Gamma2(a) through s2:lemCap(ii)). CLAIMS: (E3) For every finite simple graph G there EXISTS a valid HB*^{tau+} run. (E2) Every sequence of admissible choices terminates: formally, for every list of round choices c_1, ..., c_k such that for each l <= k the choice c_l is a valid round (R1)-(R5) on the graph G_l produced by c_1, ..., c_{l-1} and d_l >= D_*, we have k <= |E(G)| (because d_{l+1} < d_l and |E(G_l)| ∈ ℕ). (E1) Within a round (d_l >= D_*): a maximal family of edge-disjoint cycles of length >= T_l (R1) exists (greedy deletion terminates: each step deletes >= 1 edge); an s=0 recursion on G'_l stopping exactly at (eps,0)-expanders exists (children of a split have |U| + |N| < 3m/4 and m - |U| < m vertices, both >= 1, so every root-to-node path has <= n nodes); for every piece Q with |Q| >= P_l, tau_l >= 128 s_l log2^2 |Q| (s2:lemCap(ii)), so a tau-run of Q exists and EVERY tau-rule split in it has U' ≠ ∅ and n_1, n_2 < m (s2:lem14tau(a)); home orders exist. (E4, design constraint) D_l, home_l and the guest sets S_Z are defined from the pre-parts and the home order alone; (L1), (L2), (GC) are evaluated afterwards and their outcome is not used in D_l, home_l, S_Z; (R5) is deterministic. (E5) d_{l+1} < d_l whenever d_l >= D_* (s2:propDegRec), so R is finite. If d_1 < D_* the run is empty (R = 0).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| Round.Valid n H Dstar c; Round.next (G_{l+1} from G_l and c) | one round (R1)-(R5) on an input graph H with vertex set V(G), n = \|V(G)\| | s2:defHBtp | no: proposed here (DR-ROUND-LOCAL); Run.Valid should be defined from it |
| Run, Run.Valid | list of round choices; per-round validity with d_l >= D_*; stop d_{R+1} < D_* | s2:defHBtp | no (blueprint_s2a) |
| witness, s=0 recursion, tau-run | s2:defWitness, s2:lemOVgeneric, s2:lem14tau | s2 | no (blueprint_s2a: IsWitness, IsS0Rec, IsTauRun) |
| Gamma1core | s1:condGamma items (a)-(e) on the ray | s1:condGamma | no (blueprint_s1) |

**deps_declared** (manuscript \deps): s2:lem14tau, s2:propDegRec, s2:defHBtp, s2:lemCap, s2:lemOVgeneric, s2:defWitness, s2:propOV

**deps_from_proof:** s2:lemCap, s2:propOV, s2:propDegRec, s2:defWitness, s2:lemOVgeneric, s2:lem14tau, s2:defHBtp, s1:condG1, s1:condG2, s1:citDef11

**deps_notes:** s1:condG1 (through propDegRec) and s1:condG2(a) (through lemCap(ii)) are undeclared but essential (EX-GAMMA-NEEDED). s2:propOV enters only through propDegRec. s1:citDef11 (witness exists at a non-expander) is used via s2:defWitness. The proof's first paragraph ('the proofs of lemCap(ii), propOV, propDegRec use only the data of round l') is exactly the round-local form DR-ROUND-LOCAL.

**used_by:** s7:thmJVps; s7:thmMainProof

**randomness:** none

**lean_shape:**

```lean
/-- [s2:propExists] (E1) -/
def RoundExistsStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (H : FGraph V) (n : ℕ) (Dstar : ℝ),
    Gamma1core Dstar → Dstar ≤ Round.d n H → ∃ c : RoundChoice V, Round.Valid n H Dstar c
/-- [s2:propExists] (E2)+(E5): termination for every choice sequence -/
def RunTerminatesStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (cs : List (RoundChoice V)),
    Gamma1core Dstar →
    (∀ l ∈ Finset.Icc 1 cs.length, Dstar ≤ (Run.mk cs).d G l ∧
        Round.Valid G.card ((Run.mk cs).graph G l) Dstar (cs[l - 1]!)) →
    cs.length ≤ G.edges.card
/-- [s2:propExists] (E3) -/
def ExistsRunStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ),
    Gamma1core Dstar → ∃ run : Run V, run.Valid G Dstar
-- (E4) is not a Prop: reviewers check that EG.HB.Round.{D, home, guests, prePartAddrs} do not mention isLight/isGC.
```

**hazards:**

- **[risk] EX-GAMMA-NEEDED.** 'For every graph G a valid HB run exists' is FALSE without Gamma1 (the manuscript assumes Gamma globally but the statement does not say so). Counterexample with Gamma2(a) only: D_* = 2^117, G = K_m with m = 2^117 + 1. Then d_1 = m - 1 = 2^117 >= D_*; T_1 = 2^117 * 117^2 > m, so there is no long cycle and G'_1 = G; K_m is an (eps,0)-expander, so the s=0 recursion must stop at the root and the only piece is K_m with m < P_1 = ceil(117^103); there are no pre-parts, every edge passes down, G_2 = G_1, and the procedure repeats forever: no finite valid run exists. (For D_* <= 0 it never stops either.) The Spec must assume Gamma1core D_* (items (a),(b) suffice, via propDegRec).
- **[risk] EX-TERMINATION-SHAPE.** 'Every sequence of admissible choices terminates' is a statement about a nondeterministic procedure. With finite trees and finite lists in the data model, its Lean content is: (T1) every tau-rule split under tau >= 128 s log^2 |H| strictly shrinks both children (s2:lem14tau termination Spec) and the s=0 splits shrink; (E1) existence of each choice; (E2) a bound on the number of valid rounds. A statement 'Run.Valid G D run' alone does not express termination. The formulation needs the round-local API (DR-ROUND-LOCAL): RunTerminatesStatement quantifies over lists of round choices that are NOT valid runs (no stop condition).
- **[risk] EX-CONSTRUCT.** Existence requires constructing, by well-founded recursion on |H|: an s=0 tree that stops EXACTLY at (eps,0)-expanders (both directions of the leaf iff expander clause of Run.Valid, HB-STOPRULE), a tau-run for every big piece (needs lemCap(ii) at round level, i.e. pieces are (eps,0)-expanders of G'_l and G'_l has no long cycle), a maximal family of edge-disjoint long cycles (greedy: Finset induction on the edge set), and a home order (any list of the pre-part addresses). Choice of witnesses via Classical.choose from ¬IsExpander. About 300 Lean lines; nothing deep, but every piece of the Valid predicate must be satisfiable, which is also the non-vacuity check of Run.Valid (a Valid that is never satisfiable would make every s2-s7 Spec vacuous).
- **[note] EX-GC-DEFINITIONAL.** '(GC) is a deterministic relabelling that feeds back into neither D_l nor home nor the guest sets' is a property of the DEFINITIONS, not a theorem. In Lean it holds iff Round.D, Round.home, Round.guests, Round.prePartAddrs are defined without isLight/isGC (true in the blueprint_s2a sketch). No Spec; the Defs reviewer must check it (a definition of home through light parts would be circular: S_Z depends on home, lightness on S_Z).
- **[note] EX-LEXI.** (R1)'s 'lexicographically first cycle' is encoded as any maximal family of edge-disjoint long cycles (HB-R1-ENCODING); existence of a maximal family replaces termination of the greedy loop.

**effort:** ~450 Lean lines, difficulty 4/5 (Round existence ~300 (s=0 tree by WF recursion, tau-run existence from lem14tau (T2), cycle family, home order); termination bound ~60 (d strictly decreasing, |E| ∈ ℕ); run existence ~60 (induction on |E(G)|, prepending a round); the round-level lemCap/DegRec restatements are counted in their nodes.)

### `s2:lemLacunary` — lemma: tower-lacunary sums (s2.tex:1021)

- **Manuscript referee status:** x2; R6: no referee yet
- **Formalization:** Spec EG/Spec/HB/Lacunary.lean: LacunaryGeomStatement (i), LacunarySeqStatement ((iii) for abstract sequences), LacunaryRunStatement ((ii)/(iii) for runs, incl. shifted sums), LacunaryMonoStatement ((ii): monotone + halving ⇒ (H)), LacunaryExamplesStatement (iv). Defs: HypH, logStar (s1 blueprint), tw (tower) if used in the proof only (Lib).

**Statement (precise restatement).** Constants: A = 105, x_0 := log2 D_*. (i) [no hypotheses on D_*] For every R >= 1 and reals X_1, ..., X_R >= 0 with X_r <= X_{r+1}/2 for all 1 <= r < R: Σ_{r=1}^{R} X_r <= 2 X_R and Σ_{r=1}^{R} (R - r + 1) X_r <= 4 X_R. (H) For F : [x_0, ∞) → [0, ∞): (H) holds iff F(y) <= F(x)/2 whenever x >= x_0 and y >= 2^{x/A}. (iii) [Gamma1core, valid run, R >= 1] If F satisfies (H) (and is >= 0 on [x_0,∞)), then Σ_{r=1}^{R} F(lambda_r) <= 2 F(lambda_R) and Σ_{r=1}^{R} (R - r + 1) F(lambda_r) <= 4 F(lambda_R); if R >= 3 also Σ_{l=3}^{R} F(lambda_{l-2}) <= 2 F(lambda_{R-2}) and Σ_{l=3}^{R} (R - l + 1) F(lambda_{l-2}) <= 4 F(lambda_{R-2}). (ii) [Gamma1core, valid run, R >= 1] lambda_r >= 2^{lambda_{r+1}/A} for all 1 <= r < R (from d_{r+1} <= lambda_r^A, s2:propDegRec). If F is non-increasing on [x_0,∞), >= 0 there, and F(2^{x/A}) <= F(x)/2 for all x >= x_0, then F satisfies (H) (because 2^{x/A} >= x >= x_0 for x >= x_0), hence Σ F(lambda_r) <= 2F(lambda_R) <= 2F(x_0), Σ (R-r+1) F(lambda_r) <= 4 F(x_0), and the shifted sums are <= 2F(lambda_{R-2}) <= 2F(x_0), resp. <= 4F(lambda_{R-2}) <= 4F(x_0). (iv) [Gamma1core] (H) holds for F(x) = x^{-a} (every real a >= 1/100), F(x) = 1/log2 x, F(x) = (95 log2 x + 8) x^{-b} (every real b >= 1), and these three are non-increasing on [x_0,∞); (H) also holds for the three functions F_eta(x) = (2 log*(2^x) + 2)/eta(x), eta ∈ {x, x^{1/2}, log2 x} (2 log*(2^x) + 2 = 2 log* x + 4 for x > 0), which are NOT claimed monotone, and each satisfies F_eta(x) <= 2 F_eta(x_0) for all x >= x_0. The closing paragraph ('Round-l quantities ... are summed either by (i) ... or by F(lambda_{l-2}) ...' with the example M_l^3 (95 log lambda_{l-2} + 8)/lambda_{l-2}^95 <= (95 log lambda_{l-2} + 8) lambda_{l-2}^{-90.2}) is commentary; the example is not used in the proof.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| lambda_r = log2 d_r of a valid run; R | (R0) | s2:defHBtp | no: lamOf (run.d G r) (blueprint_s2a) |
| log*, log^[k] | log* z = least k >= 0 with log^[k] z <= 1 (so log* z = 0 iff z <= 1; log* z = 1 + log*(log2 z) for z > 1) | s1:convGraphs(b) | no: EG.logIter, EG.logStar (blueprint_s1, CONV-LOGSTAR) |
| HypH x0 F | ∀ x y, x0 <= x → 2^(x/105) <= y → F y <= F x / 2 | s2:lemLacunary(iii) | no: new EG.HB.HypH |
| tw (tower function) | tw 0 = 1, tw (j+1) = 2^(tw j); log* z = j iff tw(j-1) < z <= tw(j) | proof of (iv) | no: Lib only (not in any Spec) |
| Gamma1core | s1:condGamma (a)-(e) on the ray | s1:condGamma | no (blueprint_s1) |

**deps_declared** (manuscript \deps): s2:propDegRec, s1:condG1

**deps_from_proof:** s2:propDegRec, s1:condG1, s1:convGraphs

**deps_notes:** Gamma1(a),(b) only (at mu = log2 x for x >= x_0, and at x_0 itself). s2:propDegRec gives d_{r+1} <= lambda_r^A for r < R (so it inherits Gamma1core and the DR-ROUND-LOCAL question only for its run-level corollary). s1:convGraphs for log* (undeclared).

**used_by:** s2:lemTower; s5:lemExpect; s6:thmCONC; s6:thmCONCL; s7:lemUHsplit; s1:condGamma (pointer)

**randomness:** none

**lean_shape:**

```lean
/-- [s2:lemLacunary] (i) -/
def LacunaryGeomStatement : Prop :=
  ∀ (X : ℕ → ℝ) (R : ℕ), 1 ≤ R → (∀ r ∈ Finset.Icc 1 R, 0 ≤ X r) →
    (∀ r ∈ Finset.Ico 1 R, X r ≤ X (r + 1) / 2) →
    ∑ r ∈ Finset.Icc 1 R, X r ≤ 2 * X R ∧
    ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * X r ≤ 4 * X R
def HypH (x0 : ℝ) (F : ℝ → ℝ) : Prop := ∀ x y : ℝ, x0 ≤ x → (2 : ℝ) ^ (x / 105) ≤ y → F y ≤ F x / 2
/-- [s2:lemLacunary] (iii), sequence form (reused by s5-s7) -/
def LacunarySeqStatement : Prop :=
  ∀ (lam : ℕ → ℝ) (R : ℕ) (x0 : ℝ) (F : ℝ → ℝ), 1 ≤ R → (∀ r ∈ Finset.Icc 1 R, x0 ≤ lam r) →
    (∀ r ∈ Finset.Ico 1 R, (2 : ℝ) ^ (lam (r + 1) / 105) ≤ lam r) →
    (∀ x, x0 ≤ x → 0 ≤ F x) → HypH x0 F →
    ∑ r ∈ Finset.Icc 1 R, F (lam r) ≤ 2 * F (lam R) ∧
    ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * F (lam r) ≤ 4 * F (lam R)
/-- [s2:lemLacunary] (ii),(iii) for runs -/
def LacunaryRunStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → 1 ≤ run.R →
    (∀ r ∈ Finset.Ico 1 run.R, (2 : ℝ) ^ (lamOf (run.d G (r + 1)) / 105) ≤ lamOf (run.d G r)) ∧
    ∀ F : ℝ → ℝ, (∀ x, Real.logb 2 Dstar ≤ x → 0 ≤ F x) → HypH (Real.logb 2 Dstar) F →
      let lam := fun r => lamOf (run.d G r); let R := run.R
      ∑ r ∈ Finset.Icc 1 R, F (lam r) ≤ 2 * F (lam R) ∧
      ∑ r ∈ Finset.Icc 1 R, ((R - r + 1 : ℕ) : ℝ) * F (lam r) ≤ 4 * F (lam R) ∧
      (3 ≤ R → ∑ l ∈ Finset.Icc 3 R, F (lam (l - 2)) ≤ 2 * F (lam (R - 2)) ∧
        ∑ l ∈ Finset.Icc 3 R, ((R - l + 1 : ℕ) : ℝ) * F (lam (l - 2)) ≤ 4 * F (lam (R - 2)))
/-- [s2:lemLacunary] (ii), monotone criterion -/
def LacunaryMonoStatement : Prop :=
  ∀ (Dstar : ℝ) (F : ℝ → ℝ), Gamma1core Dstar → let x0 := Real.logb 2 Dstar
    (∀ x, x0 ≤ x → 0 ≤ F x) → AntitoneOn F (Set.Ici x0) →
    (∀ x, x0 ≤ x → F ((2 : ℝ) ^ (x / 105)) ≤ F x / 2) → HypH x0 F
/-- [s2:lemLacunary] (iv) -/
def LacunaryExamplesStatement : Prop :=
  ∀ Dstar : ℝ, Gamma1core Dstar → let x0 := Real.logb 2 Dstar
    (∀ a : ℝ, 1 / 100 ≤ a → HypH x0 (fun x => x ^ (-a)) ∧ AntitoneOn (fun x => x ^ (-a)) (Set.Ici x0)) ∧
    (HypH x0 (fun x => 1 / Real.logb 2 x) ∧ AntitoneOn (fun x => 1 / Real.logb 2 x) (Set.Ici x0)) ∧
    (∀ b : ℝ, 1 ≤ b → HypH x0 (fun x => (95 * Real.logb 2 x + 8) * x ^ (-b)) ∧
        AntitoneOn (fun x => (95 * Real.logb 2 x + 8) * x ^ (-b)) (Set.Ici x0)) ∧
    (∀ η ∈ ({fun x => x, fun x => Real.sqrt x, fun x => Real.logb 2 x} : Set (ℝ → ℝ)),
      let F := fun x => (2 * (logStar ((2 : ℝ) ^ x) : ℝ) + 2) / η x
      HypH x0 F ∧ ∀ x, x0 ≤ x → F x ≤ 2 * F x0)
```

**hazards:**

- **[risk] LAC-LOGSTAR.** (iv) for the three log*-functions needs a real-valued log* with a verified API that does not exist yet (CONV-LOGSTAR): log*(2^x) = 1 + log* x for x > 0 (rpow), log* z <= z (z >= 1) and log* z <= 1 + log2 z (z >= 4) by induction, the tower characterization 'log* z = j iff tw(j-1) < z <= tw(j)', tw(j+1) >= 4 tw(j) once tw(j) >= 4, and several 'holds at y_0 and the right side grows faster' inequalities (2 log2 y + 6 <= y^{1/2} for y >= 2^12, 2 log2 y + 6 <= y^{1/4} for y >= 2^32, 2 log2 u + 8 <= u^{1/2} for u >= 2^12, 95 log2 y + 8 <= y^{1/2} for y >= 2^30) whose Lean proofs need monotonicity arguments (derivatives or log bounds). Correct as stated (re-derived), but the largest real-analysis block of s2 (~250 lines).
- **[note] LAC-NONMONO-LOGSTAR.** The three log*-functions are not claimed non-increasing (they are not: F jumps up where log* increases). (ii) does not apply to them; only (iii)+(iv): Σ F(lambda_r) <= 2 F(lambda_R) <= 4 F(x_0). A downstream use of the bound 2F(x_0) for them would be an error; the s6 proof (s6.tex:271-330) uses its own tower-halving (eqTowerHalf) and Lacunary(i) instead, consistent with this.
- **[note] LAC-SEQ-FORM.** State (i) and (iii) for abstract real sequences (hypotheses lam_r >= x_0 and lam_r >= 2^{lam_{r+1}/A}) and derive the run version: s5-s7 apply the lemma to other round sequences (1/M_l, psi(M_l), F(lambda_{l-2}), 1/P_r) and must not need a run to do so.
- **[note] LAC-DOMAIN.** F : [x_0,∞) → [0,∞) becomes F : ℝ → ℝ with hypotheses on Set.Ici x0 only; nonnegativity is needed for (i) (X_r >= 0). Real exponents: x^{-a}, 2^{x/A} are Real.rpow; lambda_r > 0 needed for rpow identities.
- **[note] LAC-SHIFT-NAT.** Shifted sums use lambda_{l-2} with ℕ subtraction; they are only claimed for 3 <= l <= R (R >= 3). (R - l + 1) and (R - r + 1) are ℕ casts. Statement (iii)'s 'likewise for F(lambda_{l-2})' is spelled out explicitly in the Spec (the manuscript gives it in (ii) only).
- **[note] LAC-GAMMA.** Only Gamma1(a),(b) are used (x >= 2^256; x/A >= 101 log2 x; x >= 2A log2 x; x >= A log2^2 x / 4; x/A >= 2^12; x_0 >= 4 log2 x_0; 2^{x_0-2} >= x_0). Transfer lemma: Gamma1core D → x >= log2 D → Gamma1Items (log2 x) (since log2 x >= log2 log2 D).
- **[note] LAC-COMMENTARY.** The closing paragraph (how round-l quantities are summed; the M_l^3(...)/lambda^95 example using M_l <= lambda_{l-2}^{1.6} from lemTower(b)) is commentary with a forward pointer; no Spec. Its arithmetic (95 - 3*1.6 = 90.2) is trivially correct.

**effort:** ~500 Lean lines, difficulty 3/5 ((i) ~40; sequence form (iii) ~50; run form incl. shifted sums ~80 (needs DegRec); (ii) ~40; (iv) power/log examples ~90; log* examples + F <= 2F(x_0) ~250 (log*, tower, growth inequalities).)

### `s2:lemTower` — lemma: tower facts; (K5), F9 (s2.tex:1126)

- **Manuscript referee status:** x2+RT; R6: no referee yet
- **Formalization:** Spec EG/Spec/HB/Tower.lean: TowerAStatement, TowerBStatement, TowerCStatement, TowerDStatement, TowerEStatement. New Defs: EG.HB.epsA (D : ℝ) : ℝ, EG.HB.psiPool (x : ℝ) : ℝ (both used by s6/s7 formulas, so they belong in Defs, not Lib).

**Statement (precise restatement).** HYPOTHESES: Gamma1core D_* (items (a)-(d) used; Gamma2(a) follows), a valid run with d_1 >= D_* (so R >= 1). A = 105, sigma = 100, C' = 103, eps = 2^-5.
(a) For 1 <= r <= R: lambda_r >= d_{r+1}^{1/A}. For 1 <= r <= R-1: d_{r+2} <= lambda_r (via (A log2 lambda_r)^A <= lambda_r, Gamma1(c)). For 1 <= r <= R: R - r <= 2 log* d_r - 1, in particular R - r <= 2 log* d_r + 2. lambda is non-increasing: lambda_r >= lambda_{l-2} whenever 1 <= r <= l-2 <= R.
(b) For 1 <= r <= R: M_r <= d_r^2; lambda_r <= Lambda_r <= 2 lambda_r; lambda_r^100 <= s_r <= 2 Lambda_r^sigma; s_r <= P_r; for every ancestor Y of round r: L_Y = log2 |V(Y)| <= log2 M_r <= 2 lambda_r. For 3 <= l <= R: M_l <= (A log2 lambda_{l-2})^{2A} <= lambda_{l-2}^{1.6}; P_{l-2} >= M_l^13; P_{l-2}/2 >= M_l log2^4 M_l (this is Gamma2(b)). For 2 <= l <= R: M_{l-1} >= 2 M_l. For 1 <= r < R: P_r >= 2 P_{r+1}. Σ_{l=1}^{R} 1/M_l <= 2/D_*; Σ_{l=1}^{R} psi(M_l) <= 2.1 psi(D_*), psi(x) := (6 log2 x + 12)/x. For 3 <= l <= R: nu_l <= 2.74 n / P_{l-2} (nu_l = number of ancestors of rounds <= l-2; needs Gamma2(a) through (K1)).
(c) For 1 <= r <= R: tau_r <= 257 Lambda_r^{sigma+2} <= 2^{sigma+11} lambda_r^{sigma+2}; tau_r / P_r <= 2^{sigma+11}/lambda_r; and for every round-r pre-part Z: theta^GC_r(Z^0) >= P_r lambda_r^{-1/2} > tau_r.
(d) For 1 <= r <= l <= R: lambda_r >= 2^{2 log* d_r + 2} >= 2^{R-r} >= 2^{l-r}.
(e) eps_A := 31 eps / (C' log2 log2 D_*) (a function of D_* only). Then Σ_{l=1}^{R} 15.2 eps / log2 P_l <= eps_A; consequently Σ_{l=1}^{R} |D_l| <= eps_A n and Σ_{l=1}^{R} Σ_{Z ∈ Std_l} |A_Z| <= eps_A n.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| round constants d, lambda, M, Lambda, s, P, tau, theta^GC | (R0)-(R2), (GC) | s2:defHBtp | no (blueprint_s2a: lamOf, MOf, LamOf, sOf, POf, tauOf, thetaGC) |
| log* | s1:convGraphs(b) | s1:convGraphs | no: EG.logStar (blueprint_s1) |
| L_Y, ancestors, nu_l, D_l, A_Z, Std_l | s2:defAncestors; nuAnc (s2:propOV) | s2:defAncestors, s2:propOV | no (blueprint_s2a; nuAnc proposed in s2:propOV) |
| eps_A | epsA D := 31 * 2^-5 / (103 * logb 2 (logb 2 D)) | s2:lemTower(e) | no: new EG.HB.epsA (Defs: it enters eps_1, eps_2 of s7 and Gamma4) |
| psi | psiPool x := (6 * logb 2 x + 12) / x | s2:lemTower(b) | no: new EG.HB.psiPool (Defs: the pool term of eps_X, s7:lemEXprime, Gamma4) |
| Gamma1core | s1:condGamma | s1:condGamma | no (blueprint_s1) |

**deps_declared** (manuscript \deps): s2:propDegRec, s2:lemLacunary, s2:defHBtp, s1:condG1, s1:condG2, s2:propStructure, s2:lemCap, s2:propOV, s2:defAncestors

**deps_from_proof:** s2:propDegRec, s2:lemLacunary, s1:condG1, s2:propStructure, s2:lemCap, s2:propOV, s2:defHBtp, s2:defAncestors, s1:convGraphs

**deps_notes:** Gamma1(a)-(d): (a),(b) through propDegRec and directly ((b) at v = log2 log2 d_{l-1} for M_{l-1} >= 2M_l), (c) at u = log2 lambda_r ((a), (b) M_l <= lambda^1.6), (d) at mu = log2 lambda_r ((d)). s1:condG2 is declared but not used as a hypothesis: (b) PROVES Gamma2(b); Gamma2(a) enters only via lemCap(ii)/propOV. propStructure: (iii) monotonicity of d and the proof of (i) (Lambda_r >= lambda_r, M_r >= d_r) — see STR-LAMBDA-LE-LAMBDA. lemLacunary (i),(ii),(iv) (F = 1/(C' log x) in (e)). propOV (K1) for nu_l, (K2) for (e). lemCap(ii) for |V(Y)| <= M_r. s1:convGraphs for log* (undeclared).

**used_by:** s2:lemGC; s2:propParentless; s2:remTauConstants; s3:defCOL; s3:lemCOLJV; s3:lemCOL; s5:defZones; s5:lemZones; s5:defStages; s5:lemE1; s5:lemExpect; s5:lemParent; s5:lemDemoted; s5:remConstants; s6:defDesign; s6:thmCONC; s6:thmCONCL; s6:lemLost; s6:lemJSLC; s6:thmMIXC; s7:defPool; s7:lemCand; s7:lemVstar; s7:lemPay; s7:lemEXprime; s7:lemUHsplit; s7:propCost; s7:lemGammaSat; s1:condGamma (Gamma2(b) is proved here)

**randomness:** none

**lean_shape:**

```lean
-- common prefix of every Tower statement:
--   ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
--     Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 → ...
-- notation: d r := run.d G r, lam r := lamOf (d r), M r := (MOf (d r) : ℝ), P r := (POf (d r) : ℝ), R := run.R
/-- [s2:lemTower] (a) -/
def TowerAStatement : Prop := ∀ V [DecidableEq V] (G : FGraph V) Dstar (run : Run V),
  Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
  (∀ r ∈ Finset.Icc 1 run.R, run.d G (r + 1) ^ ((1 : ℝ) / 105) ≤ lamOf (run.d G r)) ∧
  (∀ r ∈ Finset.Icc 1 (run.R - 1), run.d G (r + 2) ≤ lamOf (run.d G r)) ∧
  (∀ r ∈ Finset.Icc 1 run.R, run.R - r + 1 ≤ 2 * logStar (run.d G r)) ∧     -- R - r ≤ 2 log* d_r - 1
  (∀ r l, 1 ≤ r → r + 2 ≤ l → l ≤ run.R + 2 → lamOf (run.d G (l - 2)) ≤ lamOf (run.d G r))
/-- [s2:lemTower] (b) (sketch of the conjuncts) -/
def TowerBStatement : Prop := ∀ V [DecidableEq V] (G : FGraph V) Dstar (run : Run V),
  Gamma1core Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
  (∀ r ∈ Finset.Icc 1 run.R, M r ≤ d r ^ 2 ∧ lam r ≤ Real.logb 2 (M r) ∧ Real.logb 2 (M r) ≤ 2 * lam r ∧
      lam r ^ 100 ≤ sOf (d r) ∧ (sOf (d r) : ℝ) ≤ 2 * Real.logb 2 (M r) ^ 100 ∧ sOf (d r) ≤ POf (d r) ∧
      ∀ a ∈ run.prePartAddrs G r, run.LY G r a ≤ Real.logb 2 (M r)) ∧
  (∀ l ∈ Finset.Icc 3 run.R, M l ≤ (105 * Real.logb 2 (lam (l - 2))) ^ (210 : ℕ) ∧
      (105 * Real.logb 2 (lam (l - 2))) ^ (210 : ℕ) ≤ lam (l - 2) ^ (1.6 : ℝ) ∧
      M l ^ 13 ≤ P (l - 2) ∧ M l * Real.logb 2 (M l) ^ 4 ≤ P (l - 2) / 2 ∧
      (run.nuAnc G l : ℝ) ≤ 2.74 * G.card / P (l - 2)) ∧
  (∀ l ∈ Finset.Icc 2 run.R, 2 * M l ≤ M (l - 1)) ∧
  (∀ r ∈ Finset.Ico 1 run.R, 2 * P (r + 1) ≤ P r) ∧
  ∑ l ∈ Finset.Icc 1 run.R, 1 / M l ≤ 2 / Dstar ∧
  ∑ l ∈ Finset.Icc 1 run.R, psiPool (M l) ≤ 2.1 * psiPool Dstar
/-- [s2:lemTower] (c) -/
def TowerCStatement : Prop := ... ∀ r ∈ Finset.Icc 1 run.R,
  (tauOf (d r) : ℝ) ≤ 257 * Real.logb 2 (M r) ^ (102 : ℕ) ∧
  257 * Real.logb 2 (M r) ^ (102 : ℕ) ≤ 2 ^ 111 * lam r ^ (102 : ℕ) ∧
  (tauOf (d r) : ℝ) / P r ≤ 2 ^ 111 / lam r ∧
  ∀ a ∈ run.prePartAddrs G r, P r * lam r ^ (-(1 / 2 : ℝ)) ≤ thetaGC (d r) (run.Z0 G r a).card ∧
    tauOf (d r) < thetaGC (d r) (run.Z0 G r a).card
/-- [s2:lemTower] (d) -/
def TowerDStatement : Prop := ... ∀ r ∈ Finset.Icc 1 run.R,
  (2 : ℝ) ^ (2 * logStar (d r) + 2 : ℕ) ≤ lam r ∧ run.R - r ≤ 2 * logStar (d r) + 2
/-- [s2:lemTower] (e) -/
def epsA (D : ℝ) : ℝ := 31 * (2 : ℝ) ^ (-5 : ℤ) / (103 * Real.logb 2 (Real.logb 2 D))
def TowerEStatement : Prop := ...
  ∑ l ∈ Finset.Icc 1 run.R, 15.2 * (2 : ℝ) ^ (-5 : ℤ) / Real.logb 2 (P l) ≤ epsA Dstar ∧
  (∑ l ∈ Finset.Icc 1 run.R, (run.D G l).card : ℝ) ≤ epsA Dstar * G.card ∧
  (∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.hubs G l a).card : ℝ) ≤ epsA Dstar * G.card
```

**hazards:**

- **[risk] TOW-LOGSTAR.** (a) and (d) need the real log* API (CONV-LOGSTAR): the induction d_{r+2i} <= log^[i] d_r for i <= k = log* d_r uses log^[i] d_r > 1 for i < log* d_r (Nat.find minimality) and log^[k] d_r <= 1; (d) needs log* d_r = 2 + log* mu for d_r = 2^{2^mu} (two applications of log*(2^y) = 1 + log* y, y > 0) and log* mu <= 1 + log2 mu (mu >= 4). Correct (re-derived) but depends on foundations that do not exist yet; 'log^[i]' beyond log* is junk in Lean (CONV-LOGJUNK).
- **[note] TOW-NAT-SUB.** 'R - r <= 2 log* d_r - 1' and 'R - r <= 2 log* d_r + 2' are ℕ statements with subtraction; state the first as R - r + 1 <= 2 log* d_r (valid because log* d_r >= 1) or in ℤ. s6.tex:377 uses 'R - r - 1 <= 2 log* d_r + 1'; all consistent. lambda_{l-2}, P_{l-2}, M_{l-1} need l >= 3 (resp. 2) in the Spec (ℕ subtraction).
- **[note] TOW-GAMMA-ITEMS.** Uses Gamma1(a)-(d) at three different points of the ray: mu = log2 lambda_r ((a),(c),(d) items), u = log2 lambda_{l-2} (Gamma1(c) for M_l <= lambda^1.6: 210 log2(105u) <= 1.6u), v = log2 log2 d_{l-1} ((a),(b) for 2^y >= 2 y^{2A}). All >= log2 log2 D_* because d >= D_*. The Spec takes Gamma1core (items (a)-(e)); (e) unused here.
- **[note] TOW-PSI-RATIO.** Σ psi(M_l) <= 2.1 psi(D_*) is NOT an instance of Lacunary(i) (the ratio 0.512 > 1/2): it needs the geometric bound Σ_{k>=0} 0.512^k = 1/0.488 = 2.049 <= 2.05 and psi decreasing on [1,∞) (psi'(x) = (6/ln 2 - 6 log2 x - 12)/x^2 < 0) and psi(2M) = psi(M)(1/2 + 3/(6 log2 M + 12)) <= 0.512 psi(M) for log2 M >= 40 (3/252 = 0.0119). psi(M_R) <= psi(D_*) needs M_R >= d_R >= D_*. Correct.
- **[note] TOW-M-INTEGER.** Depends on the pending HB-M-INTEGER decision (s2:defHBtp). Checked every M_l claim under the ceiling definition: M_l <= d_l^2 (slack 2^{2x} vs 2^20 x^6 2^x), M_l <= (A log lambda)^{2A} (via d_l^2), M_{l-1} >= d_{l-1} >= 2 d_l^2 >= 2M_l, Σ 1/M_l <= 2/M_R <= 2/D_*, psi monotone, log2 M_l >= 40. No change needed.
- **[note] TOW-EPSA-DEF.** eps_A is used in the explicit formulas of eps_1, eps_2 (s7) and hence in Gamma4; it must be a Def (EG.HB.epsA) available to the s7 layer with exactly this formula (31 eps / (C' log2 log2 D_*)); similarly psi (pool term of eps_X). Only 30.4 <= 31 is needed in (e).
- **[note] TOW-B-FROM-PROOF.** (b) takes 'Lambda_r >= lambda_r' and 's_r >= lambda_r^100' from 'the proof of' propStructure(i). Include them in StructureExpStatement (done in its sketch) or prove them directly here (M_r >= 2^16 T_r log^4 T_r >= T_r >= d_r); a Lean proof cannot cite a proof.
- **[note] TOW-C-EXPONENTS.** (c) with sigma = 100: 2^{sigma+11} = 2^111, sigma+2 = 102, C' = sigma + 3 = 103 (P_r >= lambda^103). theta^GC >= lambda^{102.5} > 2^111 lambda^102 > tau_r needs lambda^{1/2} > 2^111, i.e. log2 lambda_r > 222 (Gamma1(a): >= 256). Real exponent -1/2 (rpow) in theta^GC; theta^GC = ceil(|Z^0| lambda^{-1/2}) >= |Z^0| lambda^{-1/2}.
- **[note] TOW-E-USES-K2.** (e)'s consequences use (K2) of s2:propOV (|D_l| <= 7.6 eps n/log P_l, Σ|A_Z| <= 15.2 eps n / log P_l) and therefore inherit OV-IMPLICIT-DSTAR (Gamma2(a), implied by Gamma1core) and OV-CONST-TIGHT.

**effort:** ~750 Lean lines, difficulty 3/5 ((a) ~150 (log* induction); (b) ~300 (many real inequalities with rpow/logb, nu_l via Lacunary(i), psi geometric sum); (c) ~80; (d) ~60; (e) ~80 (Lacunary(ii),(iv) with F = 1/(103 log2 x)); epsA/psiPool Defs ~10; transfer lemmas from Gamma1core ~70.)

### `s2:lemGC` — lemma: rule GC (s2.tex:1264)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/GC.lean: GCStatement ((ii),(iii); no hypothesis on D_*), GCThetaStatement ((iv) = lemTower(c), Gamma1core). (i) is a Defs design constraint (no Spec).

**Statement (precise restatement).** For every valid run and every round r in [1,R]: (i) [definitional] the pre-parts, their leaf graphs X^0_Z, Dup*_r, D_r, home_r and the guest sets S_Z are defined in (R1)-(R4) before and independently of (GC); (GC) only decides whether a pre-part satisfying (L1) and (L2) is light or standalone. (ii) For every light round-r pre-part Y and every guest x ∈ S_Y: e_{X^0_Y}(x, Y^0 \ S_Y) < theta^GC_r(Y^0) = ceil(|Y^0| lambda_r^{-1/2}) (the number of X^0_Y-edges from x to the light part). (iii) Every GC-part Y (a round-r pre-part satisfying (L1), (L2) and failing (GC)) is standalone (Y ∈ Std_r); every edge of G'_r with both ends in Y^0 is assigned at round r (to SOME part, not necessarily Y; the edges of X^0_Y, guest-core edges included, are assigned to Y by (R5)(1)); no edge of G_{r+1} has both ends in V(Y) = Y^0; and S_Y ⊆ D_r ⊆ Dup*_r. (iv) [Gamma1core] theta^GC_r(Z^0) > tau_r for every round-r pre-part Z (= s2:lemTower(c)).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| (L1), (L2), (GC), isGCPart, Std_r, theta^GC | (R4) | s2:defHBtp | no: EG.HB.Run.isL1/isL2/isGC/isGCPart/Std, EG.HB.thetaGC (blueprint_s2a; split isLight into components, OV-L1-PRED) |
| assign (R5), G_{r+1}, Dup*_r, D_r | (R3)-(R5) | s2:defHBtp | no (blueprint_s2a) |
| e_H(A,B) | number of edges between disjoint A, B | s1:convGraphs(c) | yes: EG.FGraph.eBetween (use only for disjoint sets: {x} and Y^0 \ S_Y are disjoint since x ∈ S_Y) |

**deps_declared** (manuscript \deps): s2:defHBtp, s2:lemTower, s2:lemEL, s2:defAncestors

**deps_from_proof:** s2:defHBtp, s2:lemEL, s2:lemTower, s2:defAncestors

**deps_notes:** (ii) is the definition of (GC); (iii) uses (R4), (R5)(1) and s2:lemEL (applied to the standalone ancestor Y with V(Y) = Y^0); 'D_r ⊆ Dup*_r' because pre-parts are leaves of T_r; (iv) is s2:lemTower(c) and inherits its Gamma1core hypothesis.

**used_by:** s2:propOrigin; s6:thmCONCL

**randomness:** none

**lean_shape:**

```lean
/-- [s2:lemGC] (ii),(iii) -/
def GCStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R,
    (∀ a ∈ run.prePartAddrs G r, run.isLight G r a → ∀ x ∈ run.guests G r a,
        (run.X0 G r a).eBetween {x} (run.Z0 G r a \ run.guests G r a) < thetaGC (run.d G r) (run.Z0 G r a).card) ∧
    (∀ a ∈ run.prePartAddrs G r, run.isGCPart G r a →
        a ∈ run.Std G r ∧
        (∀ e ∈ (run.graph' G r).edges, e ∈ (run.Z0 G r a).sym2 → run.assign G r e ≠ none) ∧
        (∀ e ∈ (run.graph G (r + 1)).edges, e ∉ (run.Z0 G r a).sym2) ∧
        run.guests G r a ⊆ run.D G r) ∧
    run.D G r ⊆ run.DupStar G r
/-- [s2:lemGC] (iv) -/
def GCThetaStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar → ∀ r ∈ Finset.Icc 1 run.R, ∀ a ∈ run.prePartAddrs G r,
      tauOf (run.d G r) < thetaGC (run.d G r) (run.Z0 G r a).card
-- (i): design constraint on EG/Defs/HB/Run.lean (see EX-GC-DEFINITIONAL).
```

**hazards:**

- **[note] GC-I-DEFINITIONAL.** (i) is a statement about the order of definitions, not a proposition about a run. Lean: enforced by the Defs (D, home, guests, prePartAddrs, X0, DupStar must not reference isLight/isGC); record as a Defs-review checklist item (shared with EX-GC-DEFINITIONAL). No Spec.
- **[note] GC-III-WHICH-PART.** 'every edge of G'_r with both ends in Y^0 is assigned at round r' does not say to which part; edges not in X^0_Y may go by (R5)(2) to a light part or by (R5)(3) to another standalone pre-part earlier in the order. A Spec claiming 'assigned to Y' (E_r(Y) ⊇ E(G'_r[Y^0])) would be FALSE in general; only E(X^0_Y) ⊆ E_r(Y) holds.
- **[note] GC-EBETWEEN.** e_{X^0_Y}(x, Y) counts X^0_Y-edges between x and the light part Y = Y^0 \ S_Y; with EG.FGraph.eBetween use {x} and Y^0 \ S_Y (disjoint because x ∈ S_Y), as CONVENTIONS require. theta^GC is a natural number (ceiling); the comparison is in ℕ.
- **[note] GC-IV-GAMMA.** (i)-(iii) hold for every valid run without any hypothesis on D_*; (iv) needs Gamma1core (lambda_r^{1/2} > 2^111 and tau_r <= 2^111 lambda^102). Split the Spec accordingly (the manuscript's statement has no hypothesis at all; Gamma is implicit).

**effort:** ~100 Lean lines, difficulty 1/5 ((ii) unfold isLight; (iii) from assign step (1) + ELStatement + D ⊆ DupStar (pre-parts are leaves); (iv) = TowerC.)

### `s2:propOrigin` — proposition: ORIGIN^tau (s2.tex:1302)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/Origin.lean: OriginTypesStatement (a), OriginThinStatement (b), OriginGuestCapStatement (final paragraph); (c) is a pointer to OVRunStatement (K3) and gets no new Spec. Defs: pieceOfPrePart (the piece address above a pre-part), TypeBeta/TypeAlpha predicates.

**Statement (precise restatement).** Fix a valid run, a round r in [1,R], a round-r pre-part Y (address in T_r) and a vertex u ∈ Y^0 \ Dup*_r. (a) u lies in exactly one s=0 piece Q (a leaf of t0_r) and in exactly one leaf of the two-level recursion T_r, namely Y; Q has |Q| >= P_r, Y is a leaf of the tau-run of Q, and Y^0 ⊆ V(Q). For every round l > r (in particular l = r+1) and every edge ux ∈ E(G_l) (⊆ E(G_{r+1})), EXACTLY ONE of: (β) x ∉ Y^0 and ux ∈ F''(tau-run of Q) (deleted by the tau-run of Q; hence x ∈ V(Q)); (α) Y is light, x ∈ S_Y and ux ∈ E(X^0_Y) (a guest-core edge; it is neither deleted nor assigned at round r). If Y is standalone (GC-parts included) there is no edge of type (α). (b) For every vertex h and every round l > r: #{u ∈ Y^0 \ Dup*_r : hu ∈ E(G_l) and hu is of type (β)} <= tau_r - 1 (and = 0 if h ∈ Y^0). (c) Σ_{round-r pre-parts Y} |Y^0 ∩ Dup*_r| <= 16 eps n / log2 P_r (= (K3) of s2:propOV; needs D_* >= 2^117). (d, final paragraph) An (α)-edge has its core end u ∉ Dup*_r (so u ∈ Y^0 \ S_Y); for a light Y and a guest x ∈ S_Y: #{u ∈ Y^0 \ Dup*_r : ux ∈ E(G_l) of type (α)} < theta^GC_r(Y^0) (by s2:lemGC(ii)); there is no third type.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| two-level tree T_r, pieces (leaves of t0_r), tau-run of a piece, graft, Dup*_r | (R3) | s2:defHBtp | no: EG.HB.Run.twoLevel/pieceAddrs/piece/tauRun/DupStar, STree.graft (blueprint_s2a) |
| deleted edges of the tau-run of Q | (run.tauRun r q).deleted (run.piece G r q) (= deleted edges of T_r at addresses extending q) | s2:lemSEP, (R3) | no (blueprint_s2a STree.deleted) |
| pieceOfPrePart r a | the unique piece address q with q a prefix of a (pre-parts lie below big pieces) | s2:propOrigin(a) | no: new (Run API) |
| TypeBeta r Y u x, TypeAlpha r Y u x | β: x ∉ Y^0 ∧ s(u,x) ∈ deleted(tauRun of pieceOfPrePart Y); α: isLight Y ∧ x ∈ S_Y ∧ s(u,x) ∈ E(X^0_Y) | s2:propOrigin(a) | no: new (Spec-local defs) |
| Dup of the tau-run of Q (thin-cut Dup) | STree.dup of tauRun at the piece graph | s2:lemSEP | no (blueprint_s2a) |

**deps_declared** (manuscript \deps): s2:lemThinCut, s2:lemSEP, s2:lemCap, s2:propOV, s2:lemEL, s2:defHBtp, s2:lemGC, s2:lemOVgeneric, s2:propStructure

**deps_from_proof:** s2:lemSEP, s2:lemOVgeneric, s2:lemThinCut, s2:lemGC, s2:lemEL, s2:propStructure, s2:propOV, s2:defHBtp, s2:defTauRules

**deps_notes:** SEP(0) (vertex below a node lies in a leaf below it; vertex sets shrink), (i), (ii) on T_r; OV instance c = 1 (first level deletes nothing); thin cut on the tau-run of Q (needs only s_r < tau_r, true for every d since M_r >= 2^40, s_r >= 1: no lemCap needed; the manuscript mentions lemCap(ii) only parenthetically); lemEL is cited for the standalone case but not needed; propStructure(iii) for E(G_l) ⊆ E(G_{r+1}); propOV (K3) for (c); lemGC(ii) for the final paragraph. s2:defTauRules is used through thin cut (undeclared, harmless).

**used_by:** s6:thmCONC; s6:thmCONCL

**randomness:** none

**lean_shape:**

```lean
def Run.pieceOf (run : Run V) (G : FGraph V) (r : ℕ) (a : List Bool) : List Bool := -- the piece address q <+: a
def Run.TypeBeta (run) (G) (r) (Y : List Bool) (u x : V) : Prop :=
  x ∉ run.Z0 G r Y ∧ s(u, x) ∈ (run.tauRun r (run.pieceOf G r Y)).deleted (run.piece G r (run.pieceOf G r Y))
def Run.TypeAlpha (run) (G) (r) (Y : List Bool) (u x : V) : Prop :=
  run.isLight G r Y ∧ x ∈ run.guests G r Y ∧ s(u, x) ∈ (run.X0 G r Y).edges
/-- [s2:propOrigin] (a) -/
def OriginTypesStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ Y ∈ run.prePartAddrs G r, ∀ u ∈ run.Z0 G r Y \ run.DupStar G r,
    (∀ q ∈ run.pieceAddrs G r, u ∈ (run.piece G r q).verts ↔ q = run.pieceOf G r Y) ∧
    run.pieceOf G r Y ∈ run.pieceAddrs G r ∧ run.Z0 G r Y ⊆ (run.piece G r (run.pieceOf G r Y)).verts ∧
    (∀ b ∈ (run.twoLevel G r).leafAddrs, u ∈ ((run.twoLevel G r).graphAtD (run.graph' G r) b).verts ↔ b = Y) ∧
    ∀ l : ℕ, r < l → ∀ x : V, s(u, x) ∈ (run.graph G l).edges →
      (run.TypeBeta G r Y u x ∧ ¬ run.TypeAlpha G r Y u x) ∨ (run.TypeAlpha G r Y u x ∧ ¬ run.TypeBeta G r Y u x)
/-- [s2:propOrigin] (b) -/
def OriginThinStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ Y ∈ run.prePartAddrs G r, ∀ h : V, ∀ l : ℕ, r < l →
      ((run.Z0 G r Y \ run.DupStar G r).filter
          (fun u => s(h, u) ∈ (run.graph G l).edges ∧ run.TypeBeta G r Y u h)).card < tauOf (run.d G r) ∧
      (h ∈ run.Z0 G r Y → ((run.Z0 G r Y \ run.DupStar G r).filter
          (fun u => s(h, u) ∈ (run.graph G l).edges ∧ run.TypeBeta G r Y u h)) = ∅)
/-- [s2:propOrigin] final paragraph -/
def OriginGuestCapStatement : Prop :=
  ∀ V [DecidableEq V] (G : FGraph V) Dstar (run : Run V), run.Valid G Dstar →
    ∀ r ∈ Finset.Icc 1 run.R, ∀ Y ∈ run.prePartAddrs G r, run.isLight G r Y → ∀ x ∈ run.guests G r Y, ∀ l, r < l →
      ((run.Z0 G r Y \ run.DupStar G r).filter
          (fun u => s(u, x) ∈ (run.graph G l).edges ∧ run.TypeAlpha G r Y u x)).card < thetaGC (run.d G r) (run.Z0 G r Y).card
-- (c): OVRunStatement (K3).
```

**hazards:**

- **[risk] OR-GRAFT-DUP.** (a),(b) need correspondences between the grafted tree T_r and its components that the manuscript takes for granted: (1) u ∉ Dup*_r ⇒ u lies in exactly one piece (a vertex in two pieces lies in two leaves of T_r, via SEP(0) on the subtrees below the pieces); (2) Dup(tau-run of Q) ⊆ Dup*_r (leaves of the tau-run are leaves of T_r at a ++ b); (3) deleted(T_r) = ⋃_{big pieces q} deleted(tauRun q) (first level deletes nothing: OV instance); (4) the leaf address of Y in the tau-run is Y with the piece prefix removed, so thin cut applies to (tauRun q, Q, leaf Y'). All four are graft lemmas (HB-GRAFT). Without them the proof of (b), which s6:thmCONC/thmCONCL use for every ancestor, has no path.
- **[note] OR-TYPE-DEF.** 'ux was deleted by the tau-run of Q' must be a definition: membership in the deleted set of the tau-run of the piece above Y (TypeBeta above), equivalently deletion at an address of T_r extending the piece address. It must NOT be 'ux ∈ F'' of some node of T_r' (a first-level node deletes nothing, so equivalent, but the equivalence is a lemma).
- **[note] OR-THINCUT-NO-GAMMA.** (b) uses thin cut, which needs every split of the tau-run to be a tau-rule split with s_nu < tau: here s_nu = s_r and tau_r = ceil(128 s_r log2^2 M_r) >= 128 * 1600 * s_r > s_r for every d (M_r >= 2^40 by the max in (R2), s_r >= 1). So (a),(b),(d) need NO hypothesis on D_*; only (c) needs Gamma2(a). The manuscript's parenthetical appeal to lemCap(ii) is not needed.
- **[note] OR-L-BEYOND.** 'for every round l > r' uses E(G_l) ⊆ E(G_{r+1}) for all l > r, including l = R+1 and (in Lean) l > R+1: needs the stationary G_l and antitonicity lemma of EL-STATIONARY.
- **[note] OR-TAU-NAT.** '<= tau_r - 1' with tau_r ∈ ℕ, tau_r >= 1: state as count < tau_r (as in the thin-cut Spec) to avoid ℕ subtraction; ceil(tau_r) = tau_r since tau_r is an integer by (R2).
- **[note] OR-C-POINTER.** (c) is literally (K3) of s2:propOV; do not restate (it would need Gamma2a, which (a),(b) do not).
- **[note] OR-EXACTLY-ONE.** Exclusivity is by x ∉ Y^0 in (β) versus x ∈ S_Y ⊆ Y^0 in (α). 'Exactly one' must be stated as an exclusive disjunction (as in the sketch), since s6 uses both 'every edge is (α) or (β)' and 'standalone ⇒ all edges are (β), so h ∉ Y^0'.

**effort:** ~400 Lean lines, difficulty 3/5 (Graft correspondences (1)-(4) ~150 (beyond the graft API of s2:defHBtp); (a) classification ~120 ((R5) case analysis mirrors propDegRec); (b) ~60 (thin cut transport); final paragraph ~40; pieceOf/Type defs ~30.)

### `s2:propParentless` — proposition: fresh and parentless mass; (K4) (s2.tex:1396)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/HB/Parentless.lean: FreshStatement ((i) incl. (K4)), AdmissibleParentStatement ((ii), Gamma1core), ParentlessCountStatement ((iii) incl. 'more precisely'). Defs: lightIncidences, Parentless (Spec-local or Run API).

**Statement (precise restatement).** For every valid run (the hypothesis d_1 >= D_* only matters for (ii), which is vacuous when R <= 2): (i) If x lies in some round-r pre-part (r ∈ [1,R]), then H := home_r(x) is an ancestor of round r containing x: x ∈ H^0 \ S_H = V(H) if H is light, x ∈ H^0 = V(H) if H is standalone. Hence, for Z ∈ Std_l and x ∈ U_Z (ports): x ∈ F_Z (fresh) iff j_0(x) >= l - 1 (j_0(x) = first round in which x lies in a pre-part; x ∈ Z^0 gives j_0(x) <= l). A vertex is a port of at most one part per round (U_Z of distinct Z ∈ Std_l are disjoint), so it is a fresh port only at rounds j_0(x) and j_0(x)+1, and (K4): Σ_{l=1}^{R} Σ_{Z ∈ Std_l} |F_Z| <= 2n. (ii) [Gamma1core] (admissible parents) If Y is a light part of round r and Z a light part of round l with 1 <= r <= l-2, l <= R, then |Y| >= P_r/2 >= P_{l-2}/2 >= M_l log2^4 M_l >= |Z| L_Z^4 (L_Z = log2 |Z|). (iii) Let Bad be ANY set of light parts (Lean: any finite set of (round, address) pairs). A pair (v, Z), Z a light part of some round l ∈ [1,R], v ∈ Z (the light part's vertex set), is PARENTLESS w.r.t. Bad if no light part outside Bad of a round r with 1 <= r <= l-2 contains v. Then #{parentless pairs} <= 2n + Σ_{Y ∈ Bad} |Y| (R - r(Y)). More precisely, a vertex v is in parentless pairs only at its light parts of rounds j_1(v) and j_1(v)+1 (j_1(v) = first round in which v lies in a light part), and at later rounds only if the light part Y_1(v) of round j_1(v) containing v lies in Bad. (Application constraint RT2-I9: every reason for which a light part is not used as a parent must place that part in Bad.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| home_r, S_H, light parts, ancestors V(Y), Std_l, ports U_Z, fresh ports F_Z, anc_l(x), j_0, j_1 | s2:defHBtp (R4); s2:defAncestors | s2:defHBtp, s2:defAncestors | no (blueprint_s2a: home, guests, partVerts, Std, ports, fresh, anc, j0, j1 : WithTop ℕ) |
| L_Z, M_l, P_r | log2 \|Z\|; (R2) | s2:defAncestors, s2:defHBtp | no (blueprint_s2a: LY, MOf, POf) |
| lightIncidences | Finset of (v, (l, a)) with l ∈ [1,R], a ∈ prePartAddrs l, isLight l a, v ∈ partVerts l a | s2:propParentless(iii) | no: new (Run API) |
| Parentless Bad (v, (l, a)) | ¬ ∃ r ∈ [1,R], r + 2 <= l, ∃ b ∈ prePartAddrs r, isLight r b ∧ (r, b) ∉ Bad ∧ v ∈ partVerts r b | s2:propParentless(iii) | no: new (Spec-local def; s5 uses it via its Pl(Z)) |

**deps_declared** (manuscript \deps): s2:propStructure, s2:lemTower, s2:lemCap, s2:defAncestors, s2:defHBtp

**deps_from_proof:** s2:propStructure, s2:lemTower, s2:lemCap, s2:defAncestors, s2:defHBtp

**deps_notes:** propStructure(iv): disjoint port sets, at most one light part per round, |Y| >= P_r/2. lemTower(a): lambda non-increasing (P_r >= P_{l-2}); lemTower(b): P_{l-2}/2 >= M_l log^4 M_l (Gamma2(b)). lemCap(ii): |Z| <= |Z^0| <= M_l (needs Gamma2(a), implied by Gamma1core). (i) and (iii) use only the definitions and propStructure(iv) (no Gamma).

**used_by:** s5:defStages; s5:lemKRED; s5:remConstants; s6:thmMIXC; s7:lemPay; s7:propCost; s1:condGamma (pointer: Gamma2(b))

**randomness:** none

**lean_shape:**

```lean
/-- [s2:propParentless] (i) and (K4) -/
def FreshStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    (∀ r ∈ Finset.Icc 1 run.R, ∀ x : V, (∃ a ∈ run.prePartAddrs G r, x ∈ run.Z0 G r a) →
        ∃ a ∈ run.prePartAddrs G r, run.home G r x = some a ∧ x ∈ run.ancVerts G r a) ∧
    (∀ l ∈ Finset.Icc 1 run.R, ∀ a ∈ run.Std G l, ∀ x ∈ run.ports G l a,
        x ∈ run.fresh G l a ↔ ((l : ℕ) : WithTop ℕ) ≤ run.j0 G x + 1) ∧
    (∑ l ∈ Finset.Icc 1 run.R, ∑ a ∈ run.Std G l, (run.fresh G l a).card) ≤ 2 * G.card
/-- [s2:propParentless] (ii) -/
def AdmissibleParentStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V),
    Gamma1core Dstar → run.Valid G Dstar →
    ∀ r l, 1 ≤ r → r + 2 ≤ l → l ≤ run.R →
    ∀ a ∈ run.prePartAddrs G r, run.isLight G r a → ∀ b ∈ run.prePartAddrs G l, run.isLight G l b →
      (POf (run.d G r) : ℝ) / 2 ≤ (run.partVerts G r a).card ∧
      (POf (run.d G (l - 2)) : ℝ) ≤ POf (run.d G r) ∧
      (MOf (run.d G l) : ℝ) * Real.logb 2 (MOf (run.d G l)) ^ 4 ≤ (POf (run.d G (l - 2)) : ℝ) / 2 ∧
      ((run.partVerts G l b).card : ℝ) * Real.logb 2 (run.partVerts G l b).card ^ 4 ≤
        (MOf (run.d G l) : ℝ) * Real.logb 2 (MOf (run.d G l)) ^ 4
/-- [s2:propParentless] (iii) -/
def Run.Parentless (run : Run V) (G : FGraph V) (Bad : Finset (ℕ × List Bool)) (p : V × ℕ × List Bool) : Prop :=
  ¬ ∃ r ∈ Finset.Icc 1 run.R, r + 2 ≤ p.2.1 ∧ ∃ b ∈ run.prePartAddrs G r,
      run.isLight G r b ∧ (r, b) ∉ Bad ∧ p.1 ∈ run.partVerts G r b
def ParentlessCountStatement : Prop :=
  ∀ (V : Type u) [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : Run V), run.Valid G Dstar →
    ∀ Bad : Finset (ℕ × List Bool),
      ((run.lightIncidences G).filter (run.Parentless G Bad)).card ≤
        2 * G.card + ∑ Y ∈ Bad, (run.partVerts G Y.1 Y.2).card * (run.R - Y.1)
-- 'more precisely': ∀ p ∈ lightIncidences, Parentless Bad p →
--    (p.2.1 : WithTop ℕ) ≤ run.j1 G p.1 + 1 ∨ (the light part of round j1(p.1) containing p.1) ∈ Bad
```

**hazards:**

- **[note] PL-BAD-SCOPE.** 'Bad any set of light parts' becomes an arbitrary Finset of (round, address) pairs; non-light or out-of-range members only add nonnegative terms to the bound (strengthening). The sum's |Y| must be partVerts (the LIGHT part's vertex set Y^0 \ S_Y), not Z0; R - r(Y) is ℕ subtraction (0 for r > R, harmless). The s5 consumer (s5:defStages, eqPl) must instantiate Bad with demoted OR parent-bad parts (RT2-I9): that is an obligation of the s5 blueprint, not of this Spec.
- **[note] PL-J0-OFFSET.** 'x ∈ F_Z iff j_0(x) >= l - 1' mixes a WithTop ℕ (j_0 is ∞ for vertices in no pre-part; here x ∈ Z^0 so j_0(x) <= l is finite) with ℕ subtraction; write l <= j_0(x) + 1. It relies on the 1-indexed rounds and on anc_l(x) := ∅ for l <= 2 (ANC-ROUND-OFFSET): with 0-indexed rounds the equivalence and (K4) change.
- **[note] PL-COUNT-ENCODING.** 'The number of such pairs' is the card of a Finset of (v, (l, a)); the per-vertex argument needs: at most one light part per round containing v (propStructure(iv)(e)), so pairs of v are indexed by distinct rounds l >= j_1(v); rounds j_1 + 2 .. R number R - j_1 - 1 <= R - j_1. The double counting Σ_v [Y_1(v) ∈ Bad](R - j_1) <= Σ_{Y ∈ Bad} |Y|(R - r(Y)) needs v ∈ Y_1(v) and that Y_1(v) is determined by v.
- **[note] PL-II-GAMMA.** (ii) needs Gamma1core (via lemTower(a),(b): items (a)-(c)) and lemCap(ii) (|Z| <= M_l, Gamma2(a)); (i),(iii) need no hypothesis on D_*. The manuscript's 'd_1 >= D_*' is irrelevant for (i),(iii); in Lean (ii) is vacuous unless R >= 3.
- **[note] PL-II-LOG.** |Z| L_Z^4 <= M_l log^4 M_l needs log2 monotone and |Z| >= 1 (L_Z >= 0) for the fourth power to be monotone; true since light parts have >= P_l/2 vertices.

**effort:** ~350 Lean lines, difficulty 2/5 ((i) ~120 (home characterization, fresh iff j_0 via Nat.find/WithTop, K4 by double counting); (ii) ~50 (chain from Tower/Cap); (iii) ~180 (pair counting with j_1, Bad split).)

### `s2:remTauConstants` — remark (with Table s2:tabTauConstants): constants of HB*^{tau+} versus plain HB* (s2.tex:1502)

- **Manuscript referee status:** --
- **Formalization:** none (no mathematical content used downstream; the right-hand column is proved in s2:propOV, s2:lem14tau(b), s2:lemTower(b); the left-hand column is neither used nor proved)

**Statement (precise restatement).** Plain HB* := the procedure of s2:defHBtp with the second level of (R3) replaced by the recursion of B-M Lemma 14 at s = s_l (no tau-rules) and without (GC); HB*^tau := with tau-rules, without (GC). The overlap constants change because the separator N'' of a tau-split may exceed B-M's separator N by |H_out| + |H_in|, which raises the OV charge from c = 1 to c = 1.6 at the second level. Table s2:tabTauConstants (plain HB* -> HB*^{tau+}, where proved): Σ|Z^0| over round-r pre-parts 1.28n -> 1.37n (1.21n on the composite tree), propOV (K1); duplication at nodes of size >= P: 3.5 eps S/log P -> 5.5 eps S/log P, lem14tau(b) (which proves 5.46); nu_l: 2.6n/P_{l-2} -> 2.74n/P_{l-2}, lemTower(b); dup_r (and |D_r|): 4.5 eps n/log P_r -> 7.6 eps n/log P_r, propOV (K2); Σ_{Z ∈ Std_r}|A_Z|: 9 eps n/log P_r -> 15.2 eps n/log P_r, propOV (K2); mass of pre-parts failing (L1): 18 eps n/log P_r -> 30.4 eps n/log P_r, propOV (K3). Only the right-hand column is used; the left-hand column is recorded for comparison only and is neither used nor proved.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| plain HB*, HB*^tau | variants of s2:defHBtp (no tau-rules / no GC) | s2:remTauConstants | no, and none should be created (not used) |

**deps_declared** (manuscript \deps): s2:propOV, s2:lem14tau, s2:lemTower, s2:defHBtp, s2:lemOVgeneric

**deps_from_proof:** none (remark)

**deps_notes:** A remark; all references are pointers to where the right-hand column is proved. No logical dependency. The table environment has its own label s2:tabTauConstants (not a separate node in this chunk; covered here).

**used_by:** s1 (pointer only)

**randomness:** none

**lean_shape:**

```lean
-- No Lean statement. Cross-check only: every right-hand-column constant appears in a Spec of this
-- chunk or of s2a: 1.37 / 1.21 (OVRunStatement K1), 5.46 <= 5.5 (Lemma14Tau (b), OVStatement),
-- 2.74 (TowerBStatement), 7.6 and 15.2 (OVRunStatement K2), 30.4 (OVRunStatement K3).
```

**hazards:**

- **[note] REM-NO-FORMAL.** Nothing to formalize. The left-hand column (plain HB*: 1.28n, 3.5 eps S/log P, 2.6n/P, 4.5, 9, 18) is 'neither used nor proved'; the P2 statement reviewers must reject any Spec in s3-s7 that uses a left-hand constant (notation.txt migration list maps them to the tau+ values).
- **[note] REM-ROUNDING.** The table's '5.5 eps S/log P' is a rounding of lem14tau(b)'s proved 5.46 eps S/log M (1.6(1 + 1/c_OV) = 5.4552); the 1.21n composite-tree value is what propOV proves (1.37n is the stated, looser (K1) constant). Consistent; no Spec should use 5.5 where 5.46 is proved without checking OV-CONST-546.

**effort:** ~0 Lean lines, difficulty 1/5 (No Lean.)
