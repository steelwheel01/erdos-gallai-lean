# P2-U formalization blueprint: chunk s5 (light parts: zones, stage-2 statuses, bad probabilities, child side, parent-side U-chaining, demoted fallback, Lemma K-RED)

Manuscript: `proofs/manuscript/s5.tex` (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s5.json` (same content, one object per label, same field names as `nodes_s1.json`/`nodes_s2a.json`). Line numbers refer to `s5.tex`. Existing Lean names were checked against `formal/EG/**` (EG.FGraph, FGraph.ofEdges, FGraph.IsExpander, FGraph.IsPathConnected, EG.IsPathIn/walkEdges/pathLength/IsThrough, EG.Obj, EG.IsDecomp, EG.FinDist with pi/ofFinset/dirac/IsRSubset/IndepFun/iIndepFun, EG.FinDist.chernoffGen_lower_half, EG.Spec.L15pStatement); s2 run objects use the names proposed in `blueprint_s2a.md` (Run, run.Valid, run.partVerts, run.X, run.E, run.Std, lamOf, sOf, MOf, POf); everything else is a proposal. Hypothesis bundle used throughout: `S5Hyp N0 Dstar G run := Gamma1core ∧ Gamma1f ∧ Gamma3 ∧ N0Cond ∧ N0 ≤ n ∧ Dstar ≤ d_1 ∧ run.Valid` (s1 blueprint: s2-s6 statements take only the Γ items they use; Γ4 is not used by s5 statements).

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s5:defZones` | definition | Defs (zone law, Zone, zonePhase) + Spec (eqLY, eqZp) | 420 | 3 | risk (ZONE-LAW-WELLDEF) |
| `s5:lemZones` | lemma | Spec ((i)-(iii); (iv) on the stage-1 law) | 200 | 2 | risk (ZONES-RSUBSET-TRANSPORT) |
| `s5:defStages` | definition | Defs (A_Y, E1, COL(a), demoted, parent-bad, Bad, Rt, Pl, par, dem, lp) + Spec (eqPl, HB claim) | 320 | 2 | risk (STAGES-AY-CHOICE) |
| `s5:lemE1` | lemma | Spec (3 probability bounds) | 700 | 4 | risk (E1-COND-L15) |
| `s5:lemExpect` | lemma | Defs epsU + Spec | 350 | 3 | note (EXP-K1-INTERFACE) |
| `s5:lemChild` | lemma | Spec (faithful PV instance) + existence corollary | 300 | 3 | risk (CHILD-PV-INTERFACE) |
| `s5:lemParent` | lemma | Spec (deterministic chaining per round) + ChainSum numerics | 3000 | 5 | risk (PAR-MGRAPH-EULER) |
| `s5:lemDemoted` | lemma | Spec (VX+ instance) + existence corollary | 130 | 2 | risk (DEM-VX-INTERFACE) |
| `s5:lemKRED` | lemma | Defs Kstd + Spec (existence with count bound) | 900 | 4 | risk (KRED-CAUSALITY) |
| `s5:remConstants` | remark | none (norm_num sanity checks) | 20 | 1 | risk (REM-A-UNREVIEWED) |

Estimated new Lean for this chunk: **~6340 lines** (plus shared infrastructure owned by other chunks: EG.MGraph/T-join/Euler for multigraphs (s1), conditional Lemma-15+ on random subgraphs (s3), the PV/VX+ Specs with named good events (s4), the joint stage-1 law (s3/s7)). Hazards: 0 blocker, 19 risks, 45 notes. **No blocker**: I re-derived every inequality and every combinatorial step of the ten statements (eqLY, eqZp, rho_Y >= 1/(12L^5), the E1 Chernoff bound, 6N^-4/7N^-4, the lemExpect chain 449/898/1231/2462, the PV hypothesis check, transitions/capping/slots/multiplicity M_l - 1 <= t_Y, the cycle claim, exact cover, 307n/M_l and the eta halving, the K-RED partition and 739) and found them correct as stated, modulo the implicit hypotheses and interface decisions listed. The dominant risks are (1) the size of lemParent (multigraph Euler + trail surgery + cycle assembly, ~3000 lines), (2) cross-chunk statement-shape decisions that must precede the s3/s4/s6 Specs (stage-1 law model, lemCOL(c) interface, PV/VX+ named good events, K-RED causality), and (3) definitions that need theorems to be total (zone law, A_Y).

## 2. Cross-cutting decisions proposed for the integrator

- **Light-part identity.** Light parts are `LP := ℕ × List Bool` (round, pre-part address) with `run.lightParts G : Finset LP` (s2a HB-ADDRESS-IDENTITY); V(Y) = `run.partVerts G Y.1 Y.2`. Round conditions are written `Y.1 + 2 ≤ l` (never ℕ-subtraction).
- **Stage-1 model (ZONE-LAYER, STAGES-STAGE1-SUPPORT).** One record `EG.Stage1 V` (fields: split bit, lent index, own label per edge; JS labels; zone label `zlab : V → Option ZIdx`; pool label) and one law `stage1Law run G` = product of (1a)-(1d), defined in the s3 layer (the zone law needs only s2 data). All s5 statuses are Defs on `ω : Stage1 V`; statements quantify over `ω ∈ (stage1Law run G).supp`. Alternative (recommended if s3/s7 prefer): state probability Specs against law predicates (`μ.map (colouring, zlab) = colLaw.prod zoneLaw`), which lets s6:lemLost reuse lemE1/lemExpect on the full space.
- **Total definitions for objects that exist only under hypotheses.** Zone law: `dite` on `∑ zp ≤ 1` with `dirac none` fallback; A_Y: `Classical.epsilon` of `IsHBFamily`; plus characterization Specs (EqZpStatement, StagesHBStatement) under `S5Hyp`.
- **Setting-paragraph equations become Specs:** EqLYStatement (s5.tex:10), EqZpStatement (s5.tex:14), EqPlStatement (s5.tex:101), StagesHBStatement.
- **Deterministic core, probabilistic shell.** lemChild and lemDemoted get faithful Specs (PV/VX+ good event, probability ≥ 1/3, conclusion for every H_0 on the event) AND existence corollaries (∀ H_0 ∃ decomposition). lemParent is a purely deterministic lemma whose input is ANY arc systems with the child-side properties (PAR-ARCS-INPUT). K-RED is a pure existence statement (∀ ω, ∀ admissible Lentext, ∃ D with the bound); stage-3 outcomes are quantified away.
- **K-RED causality (KRED-CAUSALITY).** Recommend dropping 'depends only on' clauses from the Lean Specs of lemParent and K-RED and restructuring the Lean proof of s6:thmMIXC to apply K-RED once to the final Lentext family; the s6/s7 blueprints must confirm that no TPV/JS-LC/J-consumer step reads a K-RED output.
- **Interfaces other chunks must export.** s3: conditional L15+ infrastructure; a COL(a)-only failure bound (≤ 6N^-4 or ≤ N^-2/4); lemCOL(c) for arbitrary μ with index-dependent (disjoint) random sets independent of the lending data (E1-C-INTERFACE); the own-label bijection `ownIdx` (j,c) ↦ Fin k_own shared with s4. s4: `PV.Data/Hyp/labelLaw/good/Concl`, `VX.Hyp/labelLaw/good` and the size predicates `PVSize`, `VXSize`. s2: propStructure(iii) as a Finset partition, propOV (K1) count of ancestors of a round, lemTower(b) (nu_l, M_l bounds, Σ1/M_l), lemLacunary, propParentless(iii) for an arbitrary Bad set, EG.logStar. s1: EG.MGraph, T-join in forests, Euler for multigraphs with loops.
- **Constants.** New Defs: `epsU D := 2462 * (logb 2 D)^(-205)`, `epsChain D := 614/D + logb 2 (2·105·logb 2 (105·logb 2 (logb 2 D)))/(371·(logb 2 (logb 2 D))^2)` (= epsK; **binding, G-S5-1 / TRIAGE item 20: define it as `EG.Chain.epsK D`, do not retype the formula**), both with Tendsto-to-0 lemmas (used by s7:lemGammaSat/Γ4). Constants 80, 369, 745 are numerals in Specs.
- **Undeclared dependencies found in proofs** (for msreport): s5:defStages uses s3:lemCOL (definition of COL(a)) and s5:lemZones; s5:lemChild uses s3:lemHB (through A_Z); s5:lemParent uses s2:lemLacunary (inline); s5:remConstants uses s5:lemZones, s5:defStages, s5:lemParent. Declared but not logically used: s2:lemEL (K-RED), s3:lemCOL and s3:lemCOLJV (lemParent), s3:lemHB (lemE1, only via defStages).

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| risk | `s5:defZones` | ZONE-LAW-WELLDEF | Definition depends on a theorem: the law of choice(v) is a probability distribution only because sum_{Y in A(v)} zp_Y <= 1, which is eqZp, proved from Gamma1(a),(b), s2:lemTower(a) and s2:propStructure(iv) for VALID runs. A Lean Def of the stage-1 law cannot take that proof as an argument without making every Stage1 object depend on the hypotheses. Decision: define the per-vertex law with a dite fallback (if the sum is <= 1 then the true law else dirac none) and prove a characterization lemma under S5Hyp; OR state all stage-1 Specs against a law PREDICATE (mu.map zlab = product of per-vertex laws) plus a separate existence lemma. With the dite form, a wrong guard (e.g. < 1/2) silently changes the law on some runs; the guard must be exactly 'sum <= 1'. |
| risk | `s5:defZones` | ZONE-SETTING-FACTS | eqLY (s5.tex:10) and eqZp (s5.tex:14) are unlabelled claims of the setting paragraph, used by defZones (well-definedness), lemZones(i),(ii), lemE1(a),(b), lemParent Step 4, lemExpect. They need explicit Lean statements (EqLYStatement, EqZpStatement) and proofs: eqZp needs log2 lambda_r >= 2 log2 lambda_{r+1} for r < R (from lambda_r >= 2^{lambda_{r+1}/A} and Gamma1(b): 2^x >= 2^14 A x^3 >= 2Ax), hence log2 lambda_r >= 2^{R-r} 2^8, the geometric sum (4/3)(102*2^8)^{-2} < 1/2, and 'one light part per round' (propStructure(iv)) to turn the sum over light parts into a sum over rounds. eqLY needs EG.logStar (not yet defined) and s2:lemTower(a),(d). |
| risk | `s5:defZones` | ZONE-LAYER | The zone labels are component (1b) of ONE joint stage-1 law with the COL-JV colourings (s3), JS labels (s3) and pool labels (s7:defPool). PLAN puts EG.Stage1 in the s3 layer; the zone law depends only on s2 data (light parts, L_Y, R) so it can be defined before s5, but the pool law is s7 material. Decide one Stage1 record (fields split/lent/own/js/zlab/plab) and one stage1Law before any s3/s5/s6/s7 Spec mentions probabilities, or state every stage-1 Spec for an arbitrary FinDist mu with the required marginal laws and independence (recommended: then lemE1/lemExpect need only (1a),(1b) marginals and s6:lemLost can reuse them on the full space). |
| risk | `s5:lemZones` | ZONES-RSUBSET-TRANSPORT | (ii) needs a pushforward lemma: if ζ ~ pi_v mu_v and E_v := {ζ v = i}, then v \|-> [v ∈ Zone] has law rsubset (V(Y)) (mu_v(i)) when mu_v(i) = rho for all v in V(Y). EG.Lib.Prob has IsRSubset.indepEvents but not this converse transport (pi of per-coordinate laws -> rsubset of an indicator set). ~80 lines, shared with the s4 vortex Specs (sets V_{j,c} defined from levels/kappa labels). |
| risk | `s5:defStages` | STAGES-AY-CHOICE | 'We fix one such family by a fixed rule; it depends only on the run': A_Y exists only under hypotheses (\|Y\| >= 2, X_Y a (2^-6, s_r/2)-expander, 2vm <= s_r/2 — i.e. Gamma1 and validity), so a Lean Def must be total: use Classical.epsilon of the IsHBFamily property (or a dite on the hypotheses) plus StagesHBStatement. The SAME A_Y must be passed to s4:lemPV in s5:lemChild (it is, if lemChild's PV data record uses AY), since (E1) is about these sets and (E1') of PV is about the sets PV receives. |
| risk | `s5:defStages` | STAGES-STAGE1-SUPPORT | Every status is defined for an arbitrary ω : Stage1 V. For ω outside the support of stage1Law (e.g. own labels outside [k_own], lent indices outside I(Y)), the own classes need not partition Own_Y and COL(a)/(E1) lose meaning. Statements must quantify over ω in (stage1Law run G).supp (or a Stage1.WF predicate implied by positive weight). s6:thmMIXC says 'any stage-1 outcome' — read as 'any outcome of positive probability'. |
| risk | `s5:lemE1` | E1-COND-L15 | (b) applies Lemma 15+ to the RANDOM graphs Lend_Y and Own_Y 'conditionally on the split'. EG.Spec.L15pStatement is for a FIXED X with randColouring X.edges k over Fin k. The Lean proof needs: Fubini over the split bits (FinDist.compProd / pi splitting), a restriction lemma (the lent indices of the edges in Lend_Y, a fixed set once the split is fixed, have law randColouring (Lend_Y) k up to a bijection I^U ⊔ I^JS ⊔ I^JV ≃ Fin k_lend; own labels ≃ Fin k_own with a named bijection (j,c) ↦ R_{j,c}, last ↦ M — CONVENTIONS: named colour families need an explicit bijection), and the event 'Lend_Y not an expander' handled before conditioning. The identical infrastructure is needed by s3:lemCOL(a); build it once in s3 (~250 lines). |
| risk | `s5:lemE1` | E1-C-INTERFACE | (c) needs s3:lemCOL(c) in a form applicable to the zones: the sets V_{l,c,u} = Zone_{Y,l,c,u} are each exactly rho_Y-random, jointly DEPENDENT (disjoint) across indices, and independent of the lending data of Y. If the s3 Spec of lemCOL(c) is stated on a fixed product space (lending data × independent rsubsets per index), it cannot be applied (the zone family is not a product across indices). Required Spec shape: ∀ (Ω) (μ : FinDist Ω) (lend : Ω → LendData Y) (Vs : Ω → Sub(Y) → Finset V), μ.map lend = lendLaw Y → (∀ s, IsRSubset μ (Vs · s) (V Y) (ρ s)) → (∀ s, 1/(12L^5) ≤ ρ s) → IndepFun μ lend Vs → μ.prob {¬ all U-classes path connected} ≤ N^-2/2. Cross-chunk decision for the s3 blueprint. |
| risk | `s5:lemE1` | E1-INDEP | (a): the chi_u, u in A_Y(w), must be shown independent: chi_u depends on (split bit, own label) of the edge wu and on the zone label of u; the edges wu are distinct and the vertices u are distinct. In the product model this is 'functions of pairwise disjoint coordinate sets of a pi law are mutually independent' (iIndepFun), a general lemma not yet in EG.Lib.Prob (only IndepEvents from pi coordinates). Then EG.FinDist.chernoffGen_lower_half with mu := vm/(4L) <= E and threshold L^5/8 <= mu/2. P(wu in M_Y) = (1/2)(1/k_own) >= 1/(2L) needs k_own = 4J+1 <= L; P(u carries no round-l zone) >= 1 - sum zp >= 1/2 (lemZones(i)). |
| risk | `s5:lemChild` | CHILD-PV-INTERFACE | lemChild is an instantiation of s4:lemPV; its Lean statement can only be written once the s4 Spec exports PV's data record, hypothesis predicate (with the size condition PVSize N, s1 CONST-N0-INPROOF), label law (index set Pl for levels, Z for kappa, truncated geometric law per CONVENTIONS), good event and conclusion as NAMED Defs. The own classes are indexed (j,c) in Fin J × Fin 4 plus M in PV but come from a uniform Fin k_own labelling in s3: a fixed bijection ownIdx must be shared by s3 (COL(a) quantifies over all k_own classes), s5:defStages (M_Y) and the PV data. Any mismatch (e.g. M taken as label 0 in one place and label k_own-1 in another) breaks (E1'). |
| risk | `s5:lemParent` | PAR-MGRAPH-EULER | Steps 2-3 use a multigraph with loops and parallel edges (UQ_{l,c,i}), a T-join inside a spanning FOREST with \|T_i\| <= nu_l - 1, and closed Euler trails of every even component (count <= number of nodes). EG.MGraph, components, spanning forests and Euler for multigraphs with loops do not exist (s1 blueprint CONV-MGRAPH, EUL-MULTI-USE, EUL-STAGEALPHA); if Euler is a stage-alpha hypothesis for SIMPLE graphs, the multigraph-with-loops version needs the subdivision derivation (~800 lines). The count bound matters: a mere cycle decomposition of the even multigraph would give too many trails (the per-class count must be <= nu_l, not <= #arcs), so Euler per component is genuinely needed. Alternative that avoids a multigraph TYPE: state T-join and Euler for 'finite index set I with an endpoint map I → Sym2 N' directly. |
| risk | `s5:lemParent` | PAR-ARCS-INPUT | Definition-vs-use: lemParent's hypothesis says 'the arcs of Z are those given by lemChild for this H_0(Z)', but lemChild only ASSERTS EXISTENCE of arcs; there is no function 'the arcs'. The Lean lemma must take ANY arc systems satisfying the child-side properties (ArcHyp: lemChild(b),(c) + arc edges ⊆ E_l(Z)) as input. This also removes the stage-3 hypothesis (fixed outcomes in G_Z) from lemParent entirely; K-RED then feeds it the arcs obtained from ChildExistsStatement. With this reading the lemma is purely deterministic and strictly more general, and the manuscript proof uses only (F-a)-(F-d). |
| risk | `s5:lemParent` | PAR-TRAIL-SURGERY | Steps 3-8 are heavy list combinatorics: closed trails as cyclic sequences of oriented arcs (rotation to put a Y-transition last, cutting into segments at Y-transitions, grouping into blocks of <= Tslot_Y segments, re-closing each block), invariants (every arc end in exactly one transition; vis_{Y'} unchanged for Y' ≠ Y; arcs partitioned), slot assignment, forming the closed walk C(W) by concatenating arc vertex lists and connector interiors, and proving Obj.WF (Nodup, length >= 3) and that cycleEdges C(W) is exactly the union of the arcs' and connectors' edges (list-level, with the orientation reversal of arcs). Estimate 1500+ lines; it is the single largest s5 proof. Keeping arcs as vertex lists (EG.Defs.Walk) and orientations as Bool avoids transport. |
| risk | `s5:lemParent` | PAR-ETA-MONO | Step 9 needs eta(x) = x3/x1^2 (x1 = log2 x, x2 = log2(A x1), x3 = log2(2A x2)) NON-INCREASING on [log2 D_*, inf) (the manuscript differentiates ln eta in x1) and eta(2^{x/A}) <= eta(x)/2 (via 2A^2 x1^2 log2(2A x1) <= 4A^3 x1^3 <= (2^14 A x1^3)^2 <= 2^{2 x1}, Gamma1(b)). In Lean either Mathlib's antitoneOn_of_deriv_nonpos on nested logb (with domain side conditions x2, x3 > 0) or a manual argument (x3 grows at most like log x1 while x1^2 grows) — ~250 lines of real analysis. The geometric-sum step is then lemLacunary(i) (cite it instead of redoing it). |
| risk | `s5:lemParent` | PAR-DEPENDS-ONLY | 'The objects and LentU_{l,c} depend only on the stage-1 outcome and on B_{l,c}' has no direct Lean meaning; it supports K-RED's causality clause (KRED-CAUSALITY). Either drop it (recommended, if K-RED/MIX-C are restructured as existence statements) or state lemParent as the existence of a FUNCTION chainU : (arc systems) → (LUsed, D) satisfying the properties for every admissible input (a Skolemized form; follows from the ∀∃ form by choice). |
| risk | `s5:lemDemoted` | DEM-VX-INTERFACE | Needs the s4 Spec of thmVXp with the eps_O = 2^-6 branch, the size predicate VXSize N (from N0Cond), and the 'for every graph G with V(G) = Z and E(O) ⊆ E(G)' form exported with a named good event. In Lean 'graph with V(G) = Z' becomes an edge set E with O.edges ⊆ E and all edges inside Z (E ⊆ E_r(Y) gives this by propStructure(iii)); E must be loopless (true: subset of G.edges) for IsDecomp/fnum conventions. |
| risk | `s5:lemKRED` | KRED-CAUSALITY | The last assertion ('objects produced at round l depend only on stage-1/stage-3, on Lentext(Z) for round-l Z, and on rounds > l') and the 'for-all form' paragraph are what s6:thmMIXC(b) uses to identify step (2) of Construction s6:consOrder, run interleaved with TPV/JS-LC/J-consumer, with the output of K-RED for the FINAL Lentext family. A 'depends only on' clause has no direct Lean meaning. Options: (A) K-RED as pure existence (∀ admissible Lentext, ∃ D), and restructure the Lean MIX-C to first run the TPV/JS-LC/J-consumer recursion (which never reads K-RED's outputs: they use Erem(Z) of STANDALONE parts, LJS/LJV classes and J_l, all disjoint from U-classes and from light-part edge sets), obtain the final Lentext family, and apply K-RED once; (B) define K-RED's procedure as a function of (ω, stage 3, Lentext) by round recursion and prove a locality lemma. (A) is much cheaper and equally faithful for the Main Theorem, but it must be confirmed by the s6/s7 blueprints that no s6/s7 step at round l reads a K-RED output of rounds > l (s7:lemOneOutcome runs 'steps (1)-(3) of consOrder at round l' before drawing xi_l; the event of s7:consRound(f) must not depend on K-RED objects). Cross-chunk decision before the s6 Spec is written. |
| risk | `s5:lemKRED` | KRED-RECURSION | The proof is a downward recursion: H_0(Z) at round l depends on the U-lent edges LentU_{l',c} chosen by lemParent at rounds l' >= l+2, which depend on the arcs chosen at those rounds. In Lean: strong downward induction on l (or recursion on R - l) carrying the state (set of used U-lent edges, list of objects, invariants: used U-edges lie in U-classes of good parents of rounds <= current-2, pairwise disjoint over (l,c), objects decompose exactly the processed edges). Needs: LentU(Z) final when Z is processed (lemParent at l' uses only parents of rounds <= l'-2), Own_Z ⊆ H_0(Z) (lent sets ⊆ Lend_Z disjoint from Own_Z), arcs from ChildExistsStatement, and the per-round counts. ~500 lines. |
| risk | `s5:remConstants` | REM-A-UNREVIEWED | (a) was rewritten in v6 (R1: Fact EG0 replaces B-M Theorem 2 in the finish) and has NO referee yet. It asserts the per-step re-accounting 4\|W_j\| + 12(2\|Pl∩U_{j+1}\| + 2\|W_j\|) <= 28\|Pl∩U_j\| and the finish bound 64\|Pl\| + 16\|Pl\|; if the s4:lemPV Lean proof cannot reach 369 (e.g. the finish via EG0 needs x(log2 x + 2) <= 64\|Pl\| with x <= 64\|Pl\|/L, i.e. log2 x + 2 <= L, fine for L >= 2^10), c_PV and hence 745 would change linearly. The s4 blueprint must re-derive it; nothing to formalize in s5. |
| note | `s5:defZones` | ZONE-VERTEX-INDEX | The product over vertices needs a Fintype index: use [Fintype V] and label ALL of V (vertices outside G.verts or in no light part get none a.s.), or index by the subtype of G.verts. In the Tier-1 route G.verts = univ (FGraph.ofSimpleGraph), so [Fintype V] and labels on V is simplest. |
| note | `s5:defZones` | ZONE-TWO-STEP | The manuscript draws choice(v) and then a uniform sublabel; Lean should use the equivalent one-step label with weight rho_Y on each (Y,l,c,u). The only facts used downstream are: P(label(v) != none) <= sum zp <= 1/2 (lemE1(a)), P(v in Zone_{Y,s}) = rho_Y with independence over v (lemZones(ii)), and 'one label per vertex' (lemZones(iii)). Proving the two-step marginals is unnecessary. |
| note | `s5:defZones` | ZONE-OFFSETS | [4] and [Tslot_Y] are 1-based in the manuscript; use Fin 4 and range (Tslot Y). Write r(Y) <= R-2 as Y.1 + 2 <= run.R (never ℕ-subtract). rho_Y has the factor (R - r - 1) as a ℕ cast; for r >= R-1 Lean gives rho = x/0 = 0 (junk, harmless because Sub(Y) = ∅ there). |
| note | `s5:defZones` | ZONE-REAL-NAT | L_Y = logb 2 \|Y\| is real; Tslot_Y = ceil(L_Y^2) is ℕ (Nat.ceil of a real); zp_Y, rho_Y are real. Tslot_Y <= 2 L_Y^2 needs L_Y >= 1 (true: L_Y >= 102*2^8). |
| note | `s5:lemZones` | ZONES-II-SCOPE | (ii) is only for r <= R-2 (for r >= R-1, Sub(Y) = ∅ and rho_Y is junk 0/0 in Lean); the Spec must carry Y.1 + 2 <= R. The lower bound rho >= 1/(12L^5) is loose (true value >= 102/(8L^5)) and needs R - r - 1 <= L/102 (eqLY) and Tslot <= 2L^2. |
| note | `s5:lemZones` | ZONES-IV-FORM | (iv) is automatic if stage1Law is a product with zlab a separate factor; if Specs use the law-predicate interface (ZONE-LAYER) it is a hypothesis, not a lemma. Either way s5:lemE1(a),(c) need it in the form 'IndepFun (colouring of Y) (zone labels of vertices of Y)' and 'zones of Y independent of the lending data of Y' (the latter is what s3:lemCOL(c) consumes). |
| note | `s5:lemZones` | ZONES-III-TRIVIAL | (iii) holds for every ζ (one label per vertex) with no hypotheses; state it deterministically (no probability). Note Zone ζ Y s ⊆ V(Y) by the filter; the index pairs (Y,s) with s ∉ subl Y give empty zones a.s. but not for arbitrary ζ, which is harmless for disjointness. |
| note | `s5:defStages` | STAGES-EMBEDDED-CLAIMS | The definition contains lemmas: H_Y expander; 2vm <= 2^8 lambda^6 + 2 <= s_r/2 (the manuscript's 2^8 is loose: 2 ceil(L^6) <= 2(2lambda)^6 + 2 = 2^7 lambda^6 + 2); existence of A_Y (s3:lemHB); uniqueness of par(v); '(v,Z) with v in Pl(Z) is exactly parentless w.r.t. Bad'; eqPl; 'statuses are deterministic functions of stage 1'. Each becomes a Spec lemma or is definitional (the last one is automatic for Lean functions of ω). |
| note | `s5:defStages` | STAGES-COL-A-DEFINED-HERE | 'COL(a) fails' must be defined here as the explicit conjunction of 2 + k_lend + k_own expander conditions (as the text does), NOT by reference to s3:lemCOL (a probability statement). Parameters must match lemCOL(a) for light Y exactly: Own/Lend (eps_Y, s_Y/4) = (2^-6, s_r/8); lent (eps_Y, s_Y/(8k_lend)) = (2^-6, s_r/(16k_lend)); own (2^-6, s_r/(16k_own)). s6:defLending's 'lend-bad' reuses 'demoted' plus lemCOL(a),(b) events, so one shared Def of the COL(a) event (in the s3 layer) is preferable. |
| note | `s5:defStages` | STAGES-SLENT-ZERO | s_lent = s_r/(16 k_lend(Y)) with k_lend = 0 for r >= R-1: Lean division gives 0; harmless because there are no lent classes then (the quantifier over lent indices is empty). Keep the quantifier over lentIdx Y, not over Fin (klend Y) with a separate index map. |
| note | `s5:defStages` | STAGES-E1-ALL-ROUNDS | (E1) quantifies over all l in [r, R] although only l = r is used (lemChild); the text pays for it in lemE1(a) (factor 3L_Y). Keep the manuscript form: 'demoted' is also used by s6:defLending (lend-bad) and s6/s7 counts through dem, lp; changing (E1) to l = r would change those definitions (harmlessly, but it would be a definition change against the manuscript). |
| note | `s5:defStages` | STAGES-PAR | par(v) is 'the good parent of the smallest round <= l-2 containing v'. Because it is the minimum over good parents containing v, it does not depend on l as long as it exists with round <= l-2; define parU ω v : Option LP as the good parent of minimal round containing v and prove: v ∈ Rt(Z) ↔ ∃ Y, parU v = some Y ∧ Y.1 + 2 <= Z.1. Uniqueness needs propStructure(iv). Rounds are 1-indexed; write Y.1 + 2 <= l (s2a ANC-ROUND-OFFSET). |
| note | `s5:defStages` | STAGES-PL-PARENTLESS | eqPl is s2:propParentless(iii) applied to Bad (demoted OR parent-bad, RT-I9). The propParentless Spec counts pairs (v,Z) over ALL light parts Z; eqPl sums only over non-demoted Z (monotone). The propParentless Spec must take Bad as an arbitrary Finset LP of light parts; parentless must be 'no light part outside Bad of round <= l-2 contains v', literally the complement of Rt. |
| note | `s5:defStages` | STAGES-TY-REAL | t_Y = ceil(lambda_r^1.6) ∈ ℕ (rpow); IsPathConnected takes a real t: pass (tY : ℝ). ell = 2^12 L_Y^4 is real. The multiset clause is built into IsPathConnected (indexed families). |
| note | `s5:lemE1` | E1-COL-A-BOUND | The proof of (b) re-derives the COL(a) failure bound (6\|Y\|^-4) because the STATEMENT of s3:lemCOL only bounds (a),(b),(e) jointly by \|Y\|^-2/2, which is too weak here (\|Y\|^-2/2 + \|Y\|^-4 > \|Y\|^-2/2). Recommend the s3 Spec export P(COL(a) fails) <= 6N^-4 (or <= N^-2/4, as proved inside lemCOL) as its own conjunct; then (b) is a two-line union bound, and s6:lemLost's 'lend-bad' bound can use it too. |
| note | `s5:lemE1` | E1-ROW3-GAP | The L15+ hypotheses s >= 40kL are attributed to row 3 of the COL-JV table (s_Y/4 >= 40 k_lend L_Y). For k = 2 on X_Y (s = s_r/2) and for k = k_own on Own_Y (s = s_r/8) row 3 does not literally apply when k_lend is small, and for r >= R-1 (k_lend = 0) row 3 is vacuous. Both needed inequalities (s_r/2 >= 80L, s_r/8 >= 40 k_own L with k_own <= L <= 2 lambda) follow from s_r >= lambda^100: prove them separately (trivial). |
| note | `s5:lemE1` | E1-NUMERICS | Small-constant facts, all with L = L_Y >= 102*2^8 (eqLY + Gamma1(a)): 3L*2^L*exp(-L^5/32) <= 2^{-4L} (ln(3L) + 5L ln 2 <= L^5/32); 2(2+2N)N^-5 <= 6N^-4 (N >= 2); 7N^-4 <= N^-2/2 (N^2 >= 14); R-r+1 <= L/102 + 1 <= 3L; k_lend <= lambda^3.3 <= N (row 9, N >= lambda^103/2); k_own <= L <= N. Use zpow with N > 0; exp/log inequalities via Real.add_one_le_exp and nlinarith. |
| note | `s5:lemE1` | E1-SAMPLE-SPACE | 'Over the stage-1 randomness': state on the joint stage1Law (consumers s5:lemExpect and s6:lemLost take expectations on the joint law), or on any μ whose ((1a) of Y, (1b))-marginal is the product law (law-predicate interface, ZONE-LAYER). |
| note | `s5:lemExpect` | EXP-K1-INTERFACE | The count 'light parts of round r <= 1.37 n/P_r' is propOV (K1) (ancestors of round r); the s2 Spec of propOV must export it as a Finset.card bound on light parts (or ancestors) of round r, indexed by addresses (s2a HB-ADDRESS-IDENTITY), with P_r as the ℕ ceiling. |
| note | `s5:lemExpect` | EXP-REAL-POWERS | Mixes rpow (lambda^103, lambda^1.6 elsewhere), zpow (\|Y\|^-2, (log D)^-205) and ℕ ceilings (P_r); lambda_r > 1 and log2 lambda_r >= 2^8 (Gamma1(a)) are needed for every monotonicity step; log2 lambda <= lambda for the last step (lambda^-206 log lambda <= lambda^-205). Constants: 80 + 369(2log* + 2) <= 449 log2 lambda (uses 2log* + 2 <= log2 lambda and log2 lambda >= 1); 1.37 * 898 = 1230.26 <= 1231; 2 * 1231 = 2462. |
| note | `s5:lemExpect` | EXP-LACUNARY-DOMAIN | lemLacunary(ii) needs F non-increasing on [x0, inf), x0 = log2 D_*, and F(2^{x/A}) <= F(x)/2 there; the inline proof uses Gamma1(a),(b) at mu = log2 x: x/A >= 2^14 mu^3 >= mu + 1. All lambda_r >= log2 D_* (d_r >= D_* for r <= R). |
| note | `s5:lemExpect` | EXP-SUM-REINDEX | The sum over light parts is regrouped by rounds (sum_{r <= R} sum_{Y of round r}); with LP = ℕ × List Bool this is Finset.sum_fiberwise over Y.1. dem and lp are ℕ; the expectation of the ℝ-cast is linear (FinDist.expect_sum, expect_const_mul, prob_eq_expect). |
| note | `s5:lemChild` | CHILD-ARC-VERTS | (b) as stated does not say that arc vertices lie in Z or that arc edges lie in H_0(Z)/E_l(Z); lemParent (F-d) uses both (via propStructure(iii): edges of E_l(Z) have both ends in Z). Put 'IsPathIn H0' in the Lean conclusion (ChildConcl), from which both follow. Ends distinct is part of PV(b) and follows from IsPathIn (Nodup) and length >= 1. |
| note | `s5:lemChild` | CHILD-SIMULTANEITY | 'On G_Z the conclusion holds for EVERY admissible H_0 simultaneously' (G_Z does not depend on H_0) is what makes the round-by-round construction non-anticipating. In Lean, existence proofs downstream only need ∀ H0 ∃ partition (labels may be chosen after H0), so provide ChildExistsStatement as a corollary and let lemParent/K-RED depend only on it; keep the faithful LemChildStatement for fidelity (s7:lemOneOutcome's joint stage-3 outcome is then not needed in Lean). |
| note | `s5:lemChild` | CHILD-OWN-THRESHOLD | PV needs s' >= 2^145 L^41; lemCOL(e) (row 8(d)) supplies it. PLAN R3 (Haxell) may move PV's threshold to 2^146 L^41; then row 8(d) and Gamma1(f) change (R6 eventualities absorb it). The Lean statement should take the threshold from the s4 Spec, not hard-code 2^145. |
| note | `s5:lemChild` | CHILD-E1-INSTANCE | (E1') is the l = r(Z) instance of (E1) restricted to w in Pl(Z); C_w of PV counts EDGES wu, (E1) counts VERTICES u in A_Z(w): equal because u \|-> wu is injective. extph(u) = * iff zonePhase ω.zlab l u = none. |
| note | `s5:lemChild` | CHILD-STAGE3-SPACE | The level labels are indexed by Pl(Z), which depends on the stage-1 outcome: the stage-3 space is a function of ω. Harmless because ω is fixed (universally quantified) before the stage-3 law is formed; never form a joint stage-1 × stage-3 law. |
| note | `s5:lemChild` | CHILD-PROB-CONST | 1/2 - eta_PV(N) >= 1/2 - 1/100 >= 1/3 uses the N0 size condition eta_PV(N) <= 1/100 for N >= N0 (N >= P_l/2 >= N0 by Gamma3). The '1/2 - o(1)' of the text is this explicit bound. |
| note | `s5:lemParent` | PAR-JOINT-PHASES | (ii) bounds the object count SUMMED over c (cap_l is a joint quantity: sum over Y, c, i of tr/Tslot_Y <= total number of arcs of round l). A per-phase Lean statement would need a per-phase cap bound that the manuscript does not state; state all four phases in one conclusion (as in the sketch). |
| note | `s5:lemParent` | PAR-M-INTEGER | s2a blocker HB-M-INTEGER (M_l real vs integer) does not affect s5: every use here is an inequality (\|Z\| <= M_l, \|Z\| - 1 <= M_l - 1 <= t_Y, M_l + 1 <= 2M_l, J-bar + 1 <= log2 log2 M_l <= M_l, 1/M_l sums). Works with either decision. |
| note | `s5:lemParent` | PAR-CONSTANTS | Small constants: (nu-1)(M-1) + nu <= nu M (M >= 1); 56*2*2.74 = 306.88 <= 307 and the real exponent gap M^3/M^13 <= 1/M; 14/102^2 = 1/743.14 <= 1/743; 2/743 <= 1/371; 307*2 = 614. The cap estimate uses Tslot_Y >= L_Y^2 >= (102 log2 lambda_r)^2 >= (102 log2 lambda_{l-2})^2 (eqLY, lambda non-increasing in the round). All norm_num/nlinarith. |
| note | `s5:lemParent` | PAR-NU | nu_l counts ALL ancestors (light and standalone, all rounds <= l-2); the quotient nodes are only good parents, so #nodes <= nu_l; \|T_i\| <= \|E(F_i)\| <= #nodes - 1 needs at least one node when there are arcs (true: arc ends lie in Rt, so good parents exist). nu_l <= 2.74 n/P_{l-2} is lemTower(b). |
| note | `s5:lemParent` | PAR-MULTIPLICITY | Step 5: every vertex v lies in at most M_l - 1 <= t_Y pairs of P_{Y,u} (counted over ALL final trails of ALL classes for fixed (l,c)); the proof needs 'each arc end in exactly one transition' across block splits, and 'all arcs ending at v belong to the unique round-l light part Z(v)' ((F-c),(F-d)). The multiset P_{Y,u} is an indexed family over the finite type of (trail, position) pairs; IsPathConnected quantifies over ι : Type (use IsPathConnected.exists_paths if the index type lives elsewhere). Pair entries must be distinct vertices of V(Y) (transition claim). |
| note | `s5:lemParent` | PAR-CYCLE-SIMPLE | Cycle claim (length >= 3) uses G simple and E_l(Z) ∩ E_r(Y) = ∅ for r <= l-2 (propStructure(iii)); connector interiors avoid arcs because arcs avoid all round-l phase-c zones and interiors of distinct connectors of one trail are disjoint because zones of distinct (Y,u) are disjoint (lemZones(iii)) and slots at a node within a trail are distinct (Step 5). |
| note | `s5:lemParent` | PAR-UNDECLARED | Undeclared logical dependency: s2:lemLacunary (the halving/geometric-sum argument is re-proved inline). Declared but unused: s3:lemCOL, s3:lemCOLJV (row 12 enters via lemTower(b)), s1:condGamma is used (Gamma1(a),(b) at mu = log2 x). (F-b) is explicitly unused. |
| note | `s5:lemDemoted` | DEM-NOT-STAGE1 | Part (2)-(3) does not depend on the stage-1 outcome (VX+ runs on X_Y, a run object); state it for EVERY light part Y (demotedness is irrelevant), which is stronger and simpler. Only (1) mentions ω. |
| note | `s5:lemDemoted` | DEM-THRESHOLD | Numeric: 2^152 L^38 log2 L <= 2^190 lambda^38 * 2 lambda = 2^191 lambda^39 <= lambda^100 needs lambda^61 >= 2^191 (log2 lambda >= 2^8) and L <= 2 lambda (lemTower(b)), log2 L <= L; the manuscript cites row 8(c) instead (same fact). Probability: 1 - eta_VX >= 1/2 >= 1/3 by the N0 size condition. |
| note | `s5:lemKRED` | KRED-EDGE-PARTITION | Relies on propStructure(iii) as a Finset partition statement (pairwise disjoint pieces whose union is G.edges) with Kstd and the light-part pieces indexed by (round, address); and on Lentext(Y) ⊆ E_r(Y) (hypothesis + JS/JV classes ⊆ Lend_Y ⊆ E(X_Y) ⊆ E_r(Y)). The set to decompose is G.edges \ Kstd \ ⋃ Lentext; the proof's D-set equals ⊔ Cyc ⊔ E_0 ⊔ ⊔_Y (E_r(Y) \ Lentext(Y)). |
| note | `s5:lemKRED` | KRED-STAGE3-EXISTENTIAL | The manuscript fixes stage-3 outcomes in all good events as hypotheses; in Lean these only provide existence of the child and demoted decompositions (ChildExistsStatement, DemotedExistsStatement), so the Spec can omit them (∃ D is as strong for every use: s6:thmMIXC needs only the edge set and the count of O_K). |
| note | `s5:lemKRED` | KRED-SUPPORT | 'Fix a stage-1 outcome': quantify over ω in the support of stage1Law (STAGES-STAGE1-SUPPORT); for such ω the JS/JV/U classes of each Y partition Lend_Y and Own_Y is disjoint from them (s3 COL(g), holds for every well-formed ω). |
| note | `s5:lemKRED` | KRED-CONSTANTS | Counts: long cycles sum_l \|Cyc_l\| <= n and \|E_0\| < D_* n/2 (propStructure(iii)); child 369(2n + lp) = 738n + 369 lp (eqPl); U-chaining epsChain n (lemParent(ii), summed over l >= 3); demoted 80 dem. 1 + 738 = 739 <= 745. Mixed ℝ/ℕ: cast dem, lp, D.length. Objects are Obj.edge for single edges (not loops: G simple) and Obj.cycle (length >= 3) for long cycles, child, VX+ and chaining cycles. |
| note | `s5:lemKRED` | KRED-LEL-UNUSED | s2:lemEL is declared but only mentioned as an alternative reason why arc edges and connector edges differ; (F-c) (propStructure(iii)) already gives it. Do not add it as a Lean dependency. |
| note | `s5:lemKRED` | KRED-L-LE-2 | Rounds l <= 2: lemParent is not applied; correctness needs lemChild(d) (Rt(Z) = ∅ ⇒ no arcs), since Rt(Z) = ∅ for l <= 2 (no round <= l-2 >= 1 with 1-indexed rounds; write the condition as Y.1 + 2 <= l, s2a ANC-ROUND-OFFSET). |
| note | `s5:remConstants` | REM-B-EPS-NONNEG | 'epsK <= 6 because Gamma4's left side contains epsK as a summand' needs every other summand of eps1 to be >= 0 (true under Gamma1: all logs positive, log* >= 0). Not needed by any Spec (K-RED carries epsK separately). |
| note | `s5:remConstants` | REM-C-COMMENTARY | (c) asserts independence of the constants from colour probabilities and from the Markov multiplier: meta-mathematical commentary with no Lean content. |

## 4. Nodes

### `s5:defZones` — definition (stage 1b randomness, with the setting facts eqLY, eqZp): vertex choice, sublabels and zones (s5.tex:28)

- **Manuscript referee status:** x2 (s1:tabDAG row s5:defZones)
- **Formalization:** Defs EG/Defs/Light/Zones.lean (LP, ZIdx, LY, zp, Tslot, subl, avail, rho, zoneLabelLaw, zoneLaw, Zone, zonePhase) + Spec EG/Spec/Light/Setting.lean for the unlabelled setting facts eqLY and eqZp (s5.tex:10-24), which the definition and s5:lemZones rely on. The zone law must also be a component of the joint stage-1 law (proposed EG.Stage1 / stage1Law in the s3 layer, PLAN 'Link/Lend: Stage1').

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. (eqLY) For every light Y of round r: |Y| >= P_r/2 >= lambda_r^103/2; L_Y >= 103 log2 lambda_r - 1 >= 102 log2 lambda_r; R - r <= 2 log* d_r + 2 <= log2 lambda_r; hence R - r <= L_Y/102. (eqZp) For every vertex v: sum over ALL light parts Y with v in Y (all rounds) of L_Y^{-2} < 1/2. DEFINITION. For a light part Y put zp_Y := L_Y^{-2} (real) and Tslot_Y := ceil(L_Y^2) (natural). Let A(v) := {Y light : v in Y, r(Y) <= R-2}. Independently for every vertex v, and independently of all other stage-1 data (colourings and JS labels of s3:defCOL, pool labels), draw choice(v) in {none} u A(v) with P(choice(v) = Y) = zp_Y for Y in A(v) and P(choice(v) = none) = 1 - sum_{Y in A(v)} zp_Y (>= 1/2 by eqZp; this is what makes the law a probability distribution). If choice(v) = Y, v draws independently and uniformly a SUBLABEL (l,c,u) in Sub(Y) := {r(Y)+2,...,R} x [4] x [Tslot_Y] (exactly the index family I^U(Y) of s3:defCOL(ii)). One-step equivalent form (used in Lean): label(v) in {none} u {(Y,l,c,u) : Y in A(v), (l,c,u) in Sub(Y)} with P(label(v) = (Y,l,c,u)) = rho_Y := zp_Y / ((R - r(Y) - 1) * 4 * Tslot_Y), labels independent over v. ZONES: Zone_{Y,l,c,u} := {v in Y : choice(v) = Y and sublabel(v) = (l,c,u)}. A vertex v CARRIES A ROUND-l ZONE iff choice(v) != none and the first sublabel coordinate is l; its PHASE is the second coordinate c; equivalently v in Zone_{Y,l,c,u} for some Y, u. A round-l phase-c zone is any set Zone_{Y,l,c,u}.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| valid run, light parts, r(Y), V(Y), R, d_r, lambda_r, P_r, s_r, M_l | s2:defHBtp objects; light parts indexed by (round, address) (s2a HB-ADDRESS-IDENTITY); V(Y) = Z^0 \ S_Z | s2:defHBtp, s2:defAncestors | no: proposed EG.HB.Run, run.lightParts G (new: Finset (ℕ × List Bool) of (l,a) with 1 <= l <= R, a a light pre-part address), run.partVerts G l a, run.d, lamOf, POf, sOf, MOf (s2a blueprint) |
| log* (logStar) | iterated log2 count | s1:convGraphs / s2:lemTower | no: EG.logStar proposed by s1 blueprint |
| LY, zp, Tslot, subl (Sub(Y)), avail (A(v)), rho | as in the statement; subl Y := Icc (r+2) R ×ˢ Fin 4 ×ˢ range (Tslot Y) (0-based slot and phase) | s5:defZones | no: new EG.Light.* |
| zone label law | per-vertex FinDist on Option ZIdx with weights rho_Y on (Y,l,c,u), 1 - sum zp on none; product over V | s5:defZones | partly: EG.FinDist.ofFinset, FinDist.pi, FinDist.dirac exist; the law is new (EG.Light.zoneLabelLaw, zoneLaw) |
| Zone_{Y,l,c,u}, zonePhase (carries a round-l zone of phase c) | Zone := (partVerts Y).filter (label = some (Y,l,c,u)); zonePhase ζ l v := phase c if label v = some (_, l, c, _), else none | s5:defZones | no: new |
| joint stage-1 law (1a)-(1d) | product of: COL-JV colourings of all ancestors (s3:defCOL (i)-(iii)), zone labels (1b), JS labels (1c), pool labels (1d) | s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule | no: proposed EG.Stage1 V record + EG.stage1Law run G (s3 layer) |

**deps_declared** (manuscript \deps): s2:defAncestors, s3:defCOL, s2:propStructure, s2:lemTower, s1:condGamma

**deps_from_proof:** s2:defAncestors, s3:defCOL, s2:propStructure, s2:lemTower, s1:condGamma, s2:defHBtp

**deps_notes:** The definition itself needs only s2:defAncestors (light parts, V(Y)) and s3:defCOL (I^U(Y) = Sub(Y), T-slot). The well-definedness of the law needs eqZp, whose proof (s5.tex:17-24) uses s2:propStructure(iv) (one light part per round), s2:lemTower(a) (lambda_r >= 2^{lambda_{r+1}/A}), (d) and Gamma1(a),(b); eqLY uses s2:propStructure(iv), P_r = ceil(lambda_r^103) (s2:defHBtp (R2)), s2:lemTower(a),(d). The declared deps propStructure/lemTower/condGamma are used only through these unlabelled equations (ms_deps flags them unreferenced).

**used_by:** s5:lemZones; s5:defStages; s5:lemE1; s5:lemChild (extph); s5:lemParent (connector interiors); s6:defLending (stage-1 outcome); s7:defSchedule (stage 1b); EG.Stage1 (s3 layer)

**randomness:** Defines stage-1 component (1b): one label per vertex v of G, values in Option ZIdx, independent over v, law as in the statement; independent of (1a) colourings, (1c) JS labels, (1d) pool labels (s7:defSchedule: the four families are mutually independent). Nothing is conditioned on.

**lean_shape:**

```lean
namespace EG.Light
open EG.HB
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- a light part: (round, pre-part address) (s2a HB-ADDRESS-IDENTITY) -/
abbrev LP := ℕ × List Bool
/-- a zone index (Y, l, c, u); c : Fin 4 stands for [4], u < Tslot Y for [Tslot Y] -/
abbrev ZIdx := LP × ℕ × Fin 4 × ℕ
def LY (run : Run V) (G : FGraph V) (Y : LP) : ℝ := Real.logb 2 ((run.partVerts G Y.1 Y.2).card)
def zp run G Y : ℝ := (LY run G Y ^ 2)⁻¹
def Tslot run G Y : ℕ := ⌈LY run G Y ^ 2⌉₊
def subl run G (Y : LP) : Finset (ℕ × Fin 4 × ℕ) :=
  Finset.Icc (Y.1 + 2) run.R ×ˢ Finset.univ ×ˢ Finset.range (Tslot run G Y)
def avail run G (v : V) : Finset LP :=
  (run.lightParts G).filter (fun Y => v ∈ run.partVerts G Y.1 Y.2 ∧ Y.1 + 2 ≤ run.R)
def rho run G (Y : LP) : ℝ := zp run G Y / (((run.R - Y.1 - 1 : ℕ) : ℝ) * 4 * Tslot run G Y)
/-- total by a `dite` fallback (hazard ZONE-LAW-WELLDEF); weights: some (Y,s) ↦ rho Y
    for Y ∈ avail v, s ∈ subl Y; none ↦ 1 - ∑ zp; else 0 -/
noncomputable def zoneLabelLaw run G (v : V) : FinDist (Option ZIdx) :=
  if h : ∑ Y ∈ avail run G v, zp run G Y ≤ 1 then FinDist.ofFinset _ _ _ _ _ else FinDist.dirac none
noncomputable def zoneLaw run G : FinDist (V → Option ZIdx) := FinDist.pi (zoneLabelLaw run G)
def Zone (ζ : V → Option ZIdx) run G (Y : LP) (s : ℕ × Fin 4 × ℕ) : Finset V :=
  (run.partVerts G Y.1 Y.2).filter (fun v => ζ v = some (Y, s))
/-- `zonePhase ζ l v = some c` iff v carries a round-l zone of phase c -/
def zonePhase (ζ : V → Option ZIdx) (l : ℕ) (v : V) : Option (Fin 4) :=
  match ζ v with | some (_, l', c, _) => if l' = l then some c else none | none => none
end EG.Light
-- Spec (EG/Spec/Light/Setting.lean): the unlabelled setting equations
def S5Hyp (N0 Dstar : ℝ) (G : FGraph V) (run : Run V) : Prop :=
  Gamma1core Dstar ∧ Gamma1f Dstar ∧ Gamma3 N0 Dstar ∧ N0Cond N0 ∧ N0 ≤ G.card ∧
  Dstar ≤ run.d G 1 ∧ run.Valid G Dstar
def EqLYStatement : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ Y ∈ run.lightParts G, let lam := lamOf (run.d G Y.1)
    lam ^ 103 / 2 ≤ ((run.partVerts G Y.1 Y.2).card : ℝ) ∧ 102 * Real.logb 2 lam ≤ LY run G Y ∧
    ((run.R - Y.1 : ℕ) : ℝ) ≤ 2 * logStar (run.d G Y.1) + 2 ∧ 2 * logStar (run.d G Y.1) + 2 ≤ Real.logb 2 lam
def EqZpStatement : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ v : V, ∑ Y ∈ (run.lightParts G).filter (fun Y => v ∈ run.partVerts G Y.1 Y.2), zp run G Y < 1 / 2
```

**hazards:**

- **[risk] ZONE-LAW-WELLDEF.** Definition depends on a theorem: the law of choice(v) is a probability distribution only because sum_{Y in A(v)} zp_Y <= 1, which is eqZp, proved from Gamma1(a),(b), s2:lemTower(a) and s2:propStructure(iv) for VALID runs. A Lean Def of the stage-1 law cannot take that proof as an argument without making every Stage1 object depend on the hypotheses. Decision: define the per-vertex law with a dite fallback (if the sum is <= 1 then the true law else dirac none) and prove a characterization lemma under S5Hyp; OR state all stage-1 Specs against a law PREDICATE (mu.map zlab = product of per-vertex laws) plus a separate existence lemma. With the dite form, a wrong guard (e.g. < 1/2) silently changes the law on some runs; the guard must be exactly 'sum <= 1'.
- **[risk] ZONE-SETTING-FACTS.** eqLY (s5.tex:10) and eqZp (s5.tex:14) are unlabelled claims of the setting paragraph, used by defZones (well-definedness), lemZones(i),(ii), lemE1(a),(b), lemParent Step 4, lemExpect. They need explicit Lean statements (EqLYStatement, EqZpStatement) and proofs: eqZp needs log2 lambda_r >= 2 log2 lambda_{r+1} for r < R (from lambda_r >= 2^{lambda_{r+1}/A} and Gamma1(b): 2^x >= 2^14 A x^3 >= 2Ax), hence log2 lambda_r >= 2^{R-r} 2^8, the geometric sum (4/3)(102*2^8)^{-2} < 1/2, and 'one light part per round' (propStructure(iv)) to turn the sum over light parts into a sum over rounds. eqLY needs EG.logStar (not yet defined) and s2:lemTower(a),(d).
- **[risk] ZONE-LAYER.** The zone labels are component (1b) of ONE joint stage-1 law with the COL-JV colourings (s3), JS labels (s3) and pool labels (s7:defPool). PLAN puts EG.Stage1 in the s3 layer; the zone law depends only on s2 data (light parts, L_Y, R) so it can be defined before s5, but the pool law is s7 material. Decide one Stage1 record (fields split/lent/own/js/zlab/plab) and one stage1Law before any s3/s5/s6/s7 Spec mentions probabilities, or state every stage-1 Spec for an arbitrary FinDist mu with the required marginal laws and independence (recommended: then lemE1/lemExpect need only (1a),(1b) marginals and s6:lemLost can reuse them on the full space).
- **[note] ZONE-VERTEX-INDEX.** The product over vertices needs a Fintype index: use [Fintype V] and label ALL of V (vertices outside G.verts or in no light part get none a.s.), or index by the subtype of G.verts. In the Tier-1 route G.verts = univ (FGraph.ofSimpleGraph), so [Fintype V] and labels on V is simplest.
- **[note] ZONE-TWO-STEP.** The manuscript draws choice(v) and then a uniform sublabel; Lean should use the equivalent one-step label with weight rho_Y on each (Y,l,c,u). The only facts used downstream are: P(label(v) != none) <= sum zp <= 1/2 (lemE1(a)), P(v in Zone_{Y,s}) = rho_Y with independence over v (lemZones(ii)), and 'one label per vertex' (lemZones(iii)). Proving the two-step marginals is unnecessary.
- **[note] ZONE-OFFSETS.** [4] and [Tslot_Y] are 1-based in the manuscript; use Fin 4 and range (Tslot Y). Write r(Y) <= R-2 as Y.1 + 2 <= run.R (never ℕ-subtract). rho_Y has the factor (R - r - 1) as a ℕ cast; for r >= R-1 Lean gives rho = x/0 = 0 (junk, harmless because Sub(Y) = ∅ there).
- **[note] ZONE-REAL-NAT.** L_Y = logb 2 |Y| is real; Tslot_Y = ceil(L_Y^2) is ℕ (Nat.ceil of a real); zp_Y, rho_Y are real. Tslot_Y <= 2 L_Y^2 needs L_Y >= 1 (true: L_Y >= 102*2^8).

**effort:** ~420 Lean lines, difficulty 3/5 (Defs ~120 lines; eqLY ~100 lines (logStar/tower facts from s2 Specs); eqZp ~150 lines (per-round reduction, geometric sum, Gamma1 arithmetic); law characterization ~50.)

### `s5:lemZones` — lemma: zones (s5.tex:46)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/Light/Zones.lean (LemZonesStatement for (i)-(iii); (iv) as ZonesIndepStatement about the joint stage-1 law, or built into the law-predicate interface)

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. (i) For every vertex v: sum over all light parts Y with v in Y of zp_Y <= 1/2 (this is eqZp, which gives < 1/2). (ii) For every light part Y of round r <= R-2 and every sublabel (l,c,u) in Sub(Y): the random set Zone_{Y,l,c,u} is EXACTLY a rho_Y-random subset of V(Y) (each vertex of Y independently, product measure, probability rho_Y), where rho_Y = zp_Y/((R-r-1)*4*Tslot_Y) >= 1/(12 L_Y^5). (iii) All zones Zone_{Y,l,c,u}, over all light parts Y and all (l,c,u) in Sub(Y), are pairwise disjoint (deterministically, for every outcome). (iv) The family of all zones is independent of the colourings (s3:defCOL (i)-(iii)) and of the JS labels (s3:defCOL (iv)).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| zoneLaw, Zone, rho, subl, zp | see s5:defZones | s5:defZones | no (new in s5:defZones) |
| rho-random subset | IsRSubset mu V S rho: 0 <= rho <= 1 and mu.map V = rsubset S rho | s3 conventions | yes: EG.FinDist.IsRSubset, EG.FinDist.rsubset (EG/Defs/Prob/FinDist.lean) |
| independence | IndepFun mu X Y | s3:defCOL 'Consequently' | yes: EG.FinDist.IndepFun, iIndepFun |

**deps_declared** (manuscript \deps): s5:defZones, s2:propStructure, s2:lemTower, s1:condGamma, s3:defCOL

**deps_from_proof:** s5:defZones, s2:propStructure, s2:lemTower, s1:condGamma

**deps_notes:** (i) is eqZp (setting paragraph; uses propStructure(iv), lemTower(a),(d), Gamma1(a),(b)). (ii) uses eqLY (R-r-1 <= L_Y/102) and Tslot <= 2L^2. (iii),(iv) are by construction. s3:defCOL is used only for the identification Sub(Y) = I^U(Y) and for 'the colourings' in (iv).

**used_by:** s5:lemE1 ((i) in (a); (ii),(iv) in (c)); s5:lemChild ((iii): extph well defined); s5:lemParent ((iii): cycle claim (3)); s5:defStages (comment on r >= R-1)

**randomness:** Stage 1 only: the zone labels (1b), and, for (iv), the joint stage-1 law (1a)+(1b)+(1c)(+(1d)). (ii) is a statement about the pushforward of the zone law under v |-> [label(v) = (Y,l,c,u)]; nothing conditioned.

**lean_shape:**

```lean
def LemZonesStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V),
    S5Hyp N0 Dstar G run →
    (∀ v : V, ∑ Y ∈ (run.lightParts G).filter (fun Y => v ∈ run.partVerts G Y.1 Y.2), zp run G Y ≤ 1 / 2) ∧
    (∀ Y ∈ run.lightParts G, Y.1 + 2 ≤ run.R → ∀ s ∈ subl run G Y,
        FinDist.IsRSubset (zoneLaw run G) (fun ζ => Zone ζ run G Y s) (run.partVerts G Y.1 Y.2) (rho run G Y) ∧
        1 / (12 * LY run G Y ^ 5) ≤ rho run G Y) ∧
    (∀ ζ : V → Option ZIdx, ∀ Y Y' s s', (Y, s) ≠ (Y', s') → Disjoint (Zone ζ run G Y s) (Zone ζ run G Y' s'))
-- (iv), on the joint stage-1 law (s3 layer):
def ZonesIndepStatement : Prop := ∀ V [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  FinDist.IndepFun (stage1Law run G) (fun ω => (ω.split, ω.lent, ω.own, ω.js)) (fun ω => ω.zlab) ∧
  (stage1Law run G).map (fun ω => ω.zlab) = zoneLaw run G
```

**hazards:**

- **[risk] ZONES-RSUBSET-TRANSPORT.** (ii) needs a pushforward lemma: if ζ ~ pi_v mu_v and E_v := {ζ v = i}, then v |-> [v ∈ Zone] has law rsubset (V(Y)) (mu_v(i)) when mu_v(i) = rho for all v in V(Y). EG.Lib.Prob has IsRSubset.indepEvents but not this converse transport (pi of per-coordinate laws -> rsubset of an indicator set). ~80 lines, shared with the s4 vortex Specs (sets V_{j,c} defined from levels/kappa labels).
- **[note] ZONES-II-SCOPE.** (ii) is only for r <= R-2 (for r >= R-1, Sub(Y) = ∅ and rho_Y is junk 0/0 in Lean); the Spec must carry Y.1 + 2 <= R. The lower bound rho >= 1/(12L^5) is loose (true value >= 102/(8L^5)) and needs R - r - 1 <= L/102 (eqLY) and Tslot <= 2L^2.
- **[note] ZONES-IV-FORM.** (iv) is automatic if stage1Law is a product with zlab a separate factor; if Specs use the law-predicate interface (ZONE-LAYER) it is a hypothesis, not a lemma. Either way s5:lemE1(a),(c) need it in the form 'IndepFun (colouring of Y) (zone labels of vertices of Y)' and 'zones of Y independent of the lending data of Y' (the latter is what s3:lemCOL(c) consumes).
- **[note] ZONES-III-TRIVIAL.** (iii) holds for every ζ (one label per vertex) with no hypotheses; state it deterministically (no probability). Note Zone ζ Y s ⊆ V(Y) by the filter; the index pairs (Y,s) with s ∉ subl Y give empty zones a.s. but not for arbitrary ζ, which is harmless for disjointness.

**effort:** ~200 Lean lines, difficulty 2/5 ((i) from EqZp (~10); (ii) transport lemma ~80 + bound ~40; (iii) ~15; (iv) ~50 (product structure).)

### `s5:defStages` — definition (stage 2; with embedded claims and equation s5:eqPl): stage-2 statuses of light parts (s5.tex:79)

- **Manuscript referee status:** x2; parent-bad changed by CR1-PV: x1
- **Formalization:** Defs EG/Defs/Light/Stages.lean (vm, vb, AY, E1, COLa, demoted, parentBad, goodParent, Bad, Rt, Pl, parU, dem, lp) + Spec EG/Spec/Light/Stages.lean for the embedded claims (StagesHBStatement: 2vm <= s_r/2 and AY is a Lemma-HB family; EqPlStatement: eq s5:eqPl).

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. Fix a stage-1 outcome omega (colourings, JS labels, zone labels). Let Y be a light part of round r. Claims embedded in the definition: H_Y = X_Y is a (2^-6, s_r/2)-expander on Y (propStructure(i)); with vm_Y := ceil(L_Y^6) and vb_Y := ceil(2^7 L_Y^2 vm_Y), 2 vm_Y <= 2^8 lambda_r^6 + 2 <= s_r/2 (s_r >= lambda_r^100, L_Y <= 2 lambda_r). A_Y: a family of sets A_Y(w) subset N_{X_Y}(w), w in Y, |A_Y(w)| = vm_Y, every vertex in at most vb_Y of them (exists by s3:lemHB with eps' = 2^-6, m = vm_Y, b = ceil(2^7 L_Y^2 vm_Y)); ONE such family is fixed by a fixed rule depending only on the run. M_Y := the own reserve class M of Y (s3:defCOL(iii)). (E1) holds for Y iff for EVERY round l with r <= l <= R and every w in Y: #{u in A_Y(w) : wu in M_Y and u carries no round-l zone} >= L_Y^5/8. Y is DEMOTED iff (E1) fails or COL(a) fails for Y, i.e. one of Own_Y, Lend_Y (as graphs on V(Y)) is not a (2^-6, s_r/8)-expander, or some lent class is not a (2^-6, s_r/(16 k_lend(Y)))-expander, or some own class (R_{j,c}, M) is not a (2^-6, s_r/(16 k_own))-expander. Y is PARENT-BAD iff for some (l,c,u) in Sub(Y) (r+2 <= l <= R, c in [4], u in [Tslot_Y]) the U-lent class LU_{Y,l,c,u} (graph on V(Y)) is NOT (2^12 L_Y^4, t_Y)-path connected through Zone_{Y,l,c,u} in the multiset sense of s1:citDef7, t_Y = ceil(lambda_r^1.6). If r >= R-1, Sub(Y) = ∅ and Y is never parent-bad. GOOD PARENT: a light part neither demoted nor parent-bad. Bad := {demoted light parts} u {parent-bad light parts}. For a NON-DEMOTED light Z of round l: Rt(Z) := Z ∩ U{Y : Y good parent of round <= l-2}; Pl(Z) := Z \ Rt(Z); for v in Rt(Z), par(v) := the good parent of the smallest round <= l-2 containing v (unique by propStructure(iv); depends only on v and l). dem := sum_{Y demoted} |Y|; lp := sum_{Y in Bad} |Y| (R - r(Y)). Claim: (v,Z) with v in Pl(Z) is exactly a pair parentless w.r.t. Bad (s2:propParentless(iii)); hence (eqPl) sum over non-demoted light Z of |Pl(Z)| <= 2n + lp. Claim: all statuses, Bad, Rt, Pl, par, dem, lp are deterministic functions of the stage-1 outcome ((E1): colouring of Y and zone labels; COL(a): colouring of Y; parent-bad: colouring of Y and zones of Y).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| X_Y, s_r, lambda_r, R, E_l(Z), partVerts | light-part graph X_Z = X^0_Z - S_Z; round constants | s2:defHBtp, s2:defAncestors | no: proposed run.X, sOf, lamOf, run.partVerts (s2a) |
| (eps,s)-expander on V(Y) | Def 11; 'graph on V(Y)' = FGraph.ofEdges (V(Y)) F | s1:citDef11 | yes: EG.FGraph.IsExpander, EG.FGraph.ofEdges |
| (ell,t)-path connected through W (multiset sense) | Def 7 with indexed pair families | s1:citDef7 | yes: EG.FGraph.IsPathConnected (t real; pass (tY : ℝ)) |
| Lemma-HB family | IsHBFamily X m b A: ∀ w ∈ V(X), A w ⊆ nbrs w ∧ (A w).card = m, and ∀ x, #{w \| x ∈ A w} ≤ b | s3:lemHB | no: new predicate (shared with s4:lemPV/s4:thmVXp Specs) |
| Own_Y, Lend_Y, own classes R_{j,c}, M, lent classes LU/LJS/LJV, k_lend, k_own, t_Y | stage-1 colouring of E(H_Y) (s3:defCOL (i)-(iii)); k_own = 4J_Y+1; t_Y = ceil(lambda_r^1.6) | s3:defCOL | no: proposed s3-layer accessors ω.Own Y, ω.Lend Y, ω.ownCls Y i, ω.Mcls Y, ω.LU Y s, ω.LJS Y l j, ω.LJV Y l, klend, kown, tY |
| zones, zonePhase, Sub(Y) | see s5:defZones | s5:defZones | no (new) |
| E1, COLa, demoted, parentBad, goodParent, Bad, Rt, Pl, parU, dem, lp | as in the statement | s5:defStages | no: new EG.Light.* |

**deps_declared** (manuscript \deps): s5:defZones, s3:defCOL, s3:lemHB, s2:propParentless, s2:defAncestors, s2:propStructure, s2:lemTower, s1:citDef7

**deps_from_proof:** s5:defZones, s3:defCOL, s3:lemHB, s3:lemCOL, s2:propParentless, s2:defAncestors, s2:propStructure, s2:lemTower, s1:citDef7, s1:citDef11

**deps_notes:** Undeclared: s3:lemCOL (the definition of 'COL(a) fails' is lifted from Lemma COL(a) with eps_Y = 2^-6, s_Y = s_r/2) and s5:lemZones (vacuity remark). Forward pointer (not a dependency) to s5:lemE1(c). eqPl is s2:propParentless(iii) with the set Bad. The claim 2vm <= s_r/2 uses propStructure(i) (s_r >= lambda^100) and lemTower(b) (L_Y <= 2 lambda_r).

**used_by:** s5:lemE1; s5:lemExpect; s5:lemChild; s5:lemParent; s5:lemDemoted; s5:lemKRED; s6:defLending (lend-bad, X_U uses dem, lp); s6:consOrder; s6:lemLent; s7:defSchedule (stage 2)

**randomness:** None in the definition: every status is a deterministic function of the stage-1 outcome (1a colourings, 1b zone labels); nothing depends on stage 3 or later edge sets. Probabilities of the statuses are s5:lemE1.

**lean_shape:**

```lean
namespace EG.Light
def vm run G Y : ℕ := ⌈LY run G Y ^ 6⌉₊
def vb run G Y : ℕ := ⌈2 ^ 7 * LY run G Y ^ 2 * vm run G Y⌉₊
/-- the fixed Lemma-HB family (total via Classical.epsilon; its property is StagesHBStatement) -/
noncomputable def AY run G (Y : LP) : V → Finset V :=
  Classical.epsilon (fun A => IsHBFamily (run.X G Y.1 Y.2) (vm run G Y) (vb run G Y) A)
def onY run G (Y : LP) (F : Finset (Sym2 V)) : FGraph V := FGraph.ofEdges (run.partVerts G Y.1 Y.2) F
def E1 (ω : Stage1 V) run G (Y : LP) : Prop :=
  ∀ l ∈ Finset.Icc Y.1 run.R, ∀ w ∈ run.partVerts G Y.1 Y.2,
    LY run G Y ^ 5 / 8 ≤ (((AY run G Y w).filter (fun u => s(w, u) ∈ ω.Mcls Y ∧ zonePhase ω.zlab l u = none)).card : ℝ)
def COLa (ω : Stage1 V) run G Y : Prop := let s := (sOf (run.d G Y.1) : ℝ)
  (onY run G Y (ω.Own Y)).IsExpander (2 ^ (-6 : ℤ)) (s / 8) ∧ (onY run G Y (ω.Lend Y)).IsExpander (2 ^ (-6 : ℤ)) (s / 8) ∧
  (∀ i ∈ lentIdx run G Y, (onY run G Y (ω.lentCls Y i)).IsExpander (2 ^ (-6 : ℤ)) (s / (16 * klend run G Y))) ∧
  (∀ i : Fin (kown run G Y), (onY run G Y (ω.ownCls Y i)).IsExpander (2 ^ (-6 : ℤ)) (s / (16 * kown run G Y)))
def demoted ω run G Y : Prop := ¬ E1 ω run G Y ∨ ¬ COLa ω run G Y
def parentBad ω run G Y : Prop := ∃ s ∈ subl run G Y,
  ¬ (onY run G Y (ω.LU Y s)).IsPathConnected (2 ^ 12 * LY run G Y ^ 4) (tY run G Y : ℝ) (Zone ω.zlab run G Y s)
def goodParent ω run G Y : Prop := Y ∈ run.lightParts G ∧ ¬ demoted ω run G Y ∧ ¬ parentBad ω run G Y
noncomputable def Bad ω run G : Finset LP := (run.lightParts G).filter (fun Y => demoted ω run G Y ∨ parentBad ω run G Y)
noncomputable def Rt ω run G (Z : LP) : Finset V := (run.partVerts G Z.1 Z.2).filter
  (fun v => ∃ Y ∈ run.lightParts G, goodParent ω run G Y ∧ Y.1 + 2 ≤ Z.1 ∧ v ∈ run.partVerts G Y.1 Y.2)
noncomputable def Pl ω run G Z : Finset V := run.partVerts G Z.1 Z.2 \ Rt ω run G Z
/-- good parent of minimal round containing v (none if there is none) -/
noncomputable def parU ω run G (v : V) : Option LP := ...
noncomputable def dem ω run G : ℕ := ∑ Y ∈ (run.lightParts G).filter (demoted ω run G ·), (run.partVerts G Y.1 Y.2).card
noncomputable def lp ω run G : ℕ := ∑ Y ∈ Bad ω run G, (run.partVerts G Y.1 Y.2).card * (run.R - Y.1)
end EG.Light
-- Spec: embedded claims
def StagesHBStatement : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ Y ∈ run.lightParts G, 2 * (vm run G Y : ℝ) ≤ (sOf (run.d G Y.1) : ℝ) / 2 ∧
    IsHBFamily (run.X G Y.1 Y.2) (vm run G Y) (vb run G Y) (AY run G Y)
def EqPlStatement : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ ω : Stage1 V, (∑ Z ∈ (run.lightParts G).filter (fun Z => ¬ demoted ω run G Z), (Pl ω run G Z).card : ℝ)
    ≤ 2 * G.card + lp ω run G
```

**hazards:**

- **[risk] STAGES-AY-CHOICE.** 'We fix one such family by a fixed rule; it depends only on the run': A_Y exists only under hypotheses (|Y| >= 2, X_Y a (2^-6, s_r/2)-expander, 2vm <= s_r/2 — i.e. Gamma1 and validity), so a Lean Def must be total: use Classical.epsilon of the IsHBFamily property (or a dite on the hypotheses) plus StagesHBStatement. The SAME A_Y must be passed to s4:lemPV in s5:lemChild (it is, if lemChild's PV data record uses AY), since (E1) is about these sets and (E1') of PV is about the sets PV receives.
- **[risk] STAGES-STAGE1-SUPPORT.** Every status is defined for an arbitrary ω : Stage1 V. For ω outside the support of stage1Law (e.g. own labels outside [k_own], lent indices outside I(Y)), the own classes need not partition Own_Y and COL(a)/(E1) lose meaning. Statements must quantify over ω in (stage1Law run G).supp (or a Stage1.WF predicate implied by positive weight). s6:thmMIXC says 'any stage-1 outcome' — read as 'any outcome of positive probability'.
- **[note] STAGES-EMBEDDED-CLAIMS.** The definition contains lemmas: H_Y expander; 2vm <= 2^8 lambda^6 + 2 <= s_r/2 (the manuscript's 2^8 is loose: 2 ceil(L^6) <= 2(2lambda)^6 + 2 = 2^7 lambda^6 + 2); existence of A_Y (s3:lemHB); uniqueness of par(v); '(v,Z) with v in Pl(Z) is exactly parentless w.r.t. Bad'; eqPl; 'statuses are deterministic functions of stage 1'. Each becomes a Spec lemma or is definitional (the last one is automatic for Lean functions of ω).
- **[note] STAGES-COL-A-DEFINED-HERE.** 'COL(a) fails' must be defined here as the explicit conjunction of 2 + k_lend + k_own expander conditions (as the text does), NOT by reference to s3:lemCOL (a probability statement). Parameters must match lemCOL(a) for light Y exactly: Own/Lend (eps_Y, s_Y/4) = (2^-6, s_r/8); lent (eps_Y, s_Y/(8k_lend)) = (2^-6, s_r/(16k_lend)); own (2^-6, s_r/(16k_own)). s6:defLending's 'lend-bad' reuses 'demoted' plus lemCOL(a),(b) events, so one shared Def of the COL(a) event (in the s3 layer) is preferable.
- **[note] STAGES-SLENT-ZERO.** s_lent = s_r/(16 k_lend(Y)) with k_lend = 0 for r >= R-1: Lean division gives 0; harmless because there are no lent classes then (the quantifier over lent indices is empty). Keep the quantifier over lentIdx Y, not over Fin (klend Y) with a separate index map.
- **[note] STAGES-E1-ALL-ROUNDS.** (E1) quantifies over all l in [r, R] although only l = r is used (lemChild); the text pays for it in lemE1(a) (factor 3L_Y). Keep the manuscript form: 'demoted' is also used by s6:defLending (lend-bad) and s6/s7 counts through dem, lp; changing (E1) to l = r would change those definitions (harmlessly, but it would be a definition change against the manuscript).
- **[note] STAGES-PAR.** par(v) is 'the good parent of the smallest round <= l-2 containing v'. Because it is the minimum over good parents containing v, it does not depend on l as long as it exists with round <= l-2; define parU ω v : Option LP as the good parent of minimal round containing v and prove: v ∈ Rt(Z) ↔ ∃ Y, parU v = some Y ∧ Y.1 + 2 <= Z.1. Uniqueness needs propStructure(iv). Rounds are 1-indexed; write Y.1 + 2 <= l (s2a ANC-ROUND-OFFSET).
- **[note] STAGES-PL-PARENTLESS.** eqPl is s2:propParentless(iii) applied to Bad (demoted OR parent-bad, RT-I9). The propParentless Spec counts pairs (v,Z) over ALL light parts Z; eqPl sums only over non-demoted Z (monotone). The propParentless Spec must take Bad as an arbitrary Finset LP of light parts; parentless must be 'no light part outside Bad of round <= l-2 contains v', literally the complement of Rt.
- **[note] STAGES-TY-REAL.** t_Y = ceil(lambda_r^1.6) ∈ ℕ (rpow); IsPathConnected takes a real t: pass (tY : ℝ). ell = 2^12 L_Y^4 is real. The multiset clause is built into IsPathConnected (indexed families).

**effort:** ~320 Lean lines, difficulty 2/5 (Defs ~140; StagesHBStatement ~60 (expander -> min degree, L <= 2 lambda); EqPl from propParentless(iii) ~80; par uniqueness ~40.)

### `s5:lemE1` — lemma: bad probabilities (s5.tex:111)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/Light/E1.lean (LemE1Statement, three conjuncts)

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. Let Y be a light part of round r (any r <= R). Over the stage-1 randomness (joint law; only the colouring of Y (1a) and the zone labels (1b) matter): (a) P((E1) fails for Y) <= 3 L_Y |Y| exp(-L_Y^5/32); (b) P(Y demoted) <= |Y|^{-2}/2; (c) P(Y in Bad) <= |Y|^{-2}. (For r >= R-1, Y is never parent-bad and (c) follows from (b).) Intermediate claims of the proof: P(COL(a) fails) <= 2(2 + k_lend(Y) + k_own)|Y|^{-5} <= 6|Y|^{-4}; P((E1) fails) <= |Y|^{-4}; P(demoted) <= 7|Y|^{-4}; P(parent-bad) <= |Y|^{-2}/2 (s3:lemCOL(c)).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| E1, COLa, demoted, parentBad, Bad | see s5:defStages | s5:defStages | no (new) |
| stage1Law (joint) | product of (1a)-(1d) | s7:defSchedule, s3:defCOL, s5:defZones | no: proposed EG.stage1Law |
| Chernoff lower tail (Poisson-binomial) | P(X <= (1-delta)mu) <= exp(-delta^2 mu/2) for mu <= E X | s1:citChernoffGen(a) | yes: EG.FinDist.chernoffGen_lower / chernoffGen_lower_half (EG/Lib/Prob/Chernoff.lean) |
| Lemma 15+ | random k-colouring of an (eps',s)-expander, s >= 40kL: each class (eps', s/(2k))-expander w.p. >= 1 - 2N^-5 | s3:lemL15p | yes (statement): EG.Spec.L15pStatement (fixed X, randColouring X.edges k, colours Fin k) |
| Lemma COL(c) | U-lent classes (2^12 L^4, t_Y)-path connected through independent rho-random sets (rho >= 1/(12L^5), possibly dependent across indices) w.p. >= 1 - \|Y\|^-2/2 | s3:lemCOL(c) | no: s3 Spec not written yet (interface hazard E1-C-INTERFACE) |
| k_lend <= lambda_r^3.3 | row 9 of the COL-JV table | s3:lemCOLJV(i) | no |

**deps_declared** (manuscript \deps): s3:lemCOL, s3:lemHB, s5:lemZones, s5:defStages, s1:citChernoffGen, s3:defCOL, s3:lemL15p, s3:lemCOLJV, s2:propStructure, s2:lemTower, s1:condGamma

**deps_from_proof:** s5:defStages, s5:lemZones, s3:defCOL, s1:citChernoffGen, s3:lemL15p, s3:lemCOL, s3:lemCOLJV, s1:condGamma, s2:propStructure, s2:lemTower

**deps_notes:** (a): defStages (A_Y fixed, |A_Y(w)| = vm), defCOL(i),(iii) (uniform split and own labels, independence over edges), lemZones(i),(iv), citChernoffGen, eqLY (R-r+1 <= 3L). (b): lemL15p three times (as in the proof of lemCOL(a)), lemCOLJV row 3 (s >= 40kL) and (i) (k_lend <= lambda^3.3), eqLY (|Y| >= lambda^103/2), Gamma1(a) (L >= 102*2^8). (c): lemCOL(c) with V_{l,c,u} := Zone_{Y,l,c,u} via lemZones(ii),(iv). s3:lemHB is used only through defStages (declared, ms_deps: unreferenced). propStructure/lemTower through eqLY.

**used_by:** s5:lemExpect; s6:lemLost(i) (P(lend-bad) uses (b)); s1:condGamma Gamma2(c) (pointer: Gamma2(c) is this lemma, not a condition)

**randomness:** Sample space: the joint stage-1 law (1a)-(1d), of which only the following coordinates enter: for each edge e of H_Y = X_Y, the fair own/lend bit, the lent index (uniform on I^U u I^JS u I^JV of Y) and the own label (uniform on k_own labels); for each vertex u of Y, its zone label (1b). All independent. Nothing is conditioned on in the statement; the proof of (b) conditions on the own/lend split (Fubini over the split bits), and (c) uses lemCOL(c), which conditions on the lending data of Y.

**lean_shape:**

```lean
def LemE1Statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V),
    S5Hyp N0 Dstar G run → ∀ Y ∈ run.lightParts G,
    let N : ℝ := (run.partVerts G Y.1 Y.2).card
    (stage1Law run G).prob {ω | ¬ E1 ω run G Y} ≤ 3 * LY run G Y * N * Real.exp (-(LY run G Y ^ 5) / 32) ∧
    (stage1Law run G).prob {ω | demoted ω run G Y} ≤ N ^ (-2 : ℤ) / 2 ∧
    (stage1Law run G).prob {ω | Y ∈ Bad ω run G} ≤ N ^ (-2 : ℤ)
-- helper Specs recommended (shared with s3:lemCOL): COLaFailStatement : P(¬ COLa) ≤ 6 N^(-4)
```

**hazards:**

- **[risk] E1-COND-L15.** (b) applies Lemma 15+ to the RANDOM graphs Lend_Y and Own_Y 'conditionally on the split'. EG.Spec.L15pStatement is for a FIXED X with randColouring X.edges k over Fin k. The Lean proof needs: Fubini over the split bits (FinDist.compProd / pi splitting), a restriction lemma (the lent indices of the edges in Lend_Y, a fixed set once the split is fixed, have law randColouring (Lend_Y) k up to a bijection I^U ⊔ I^JS ⊔ I^JV ≃ Fin k_lend; own labels ≃ Fin k_own with a named bijection (j,c) ↦ R_{j,c}, last ↦ M — CONVENTIONS: named colour families need an explicit bijection), and the event 'Lend_Y not an expander' handled before conditioning. The identical infrastructure is needed by s3:lemCOL(a); build it once in s3 (~250 lines).
- **[risk] E1-C-INTERFACE.** (c) needs s3:lemCOL(c) in a form applicable to the zones: the sets V_{l,c,u} = Zone_{Y,l,c,u} are each exactly rho_Y-random, jointly DEPENDENT (disjoint) across indices, and independent of the lending data of Y. If the s3 Spec of lemCOL(c) is stated on a fixed product space (lending data × independent rsubsets per index), it cannot be applied (the zone family is not a product across indices). Required Spec shape: ∀ (Ω) (μ : FinDist Ω) (lend : Ω → LendData Y) (Vs : Ω → Sub(Y) → Finset V), μ.map lend = lendLaw Y → (∀ s, IsRSubset μ (Vs · s) (V Y) (ρ s)) → (∀ s, 1/(12L^5) ≤ ρ s) → IndepFun μ lend Vs → μ.prob {¬ all U-classes path connected} ≤ N^-2/2. Cross-chunk decision for the s3 blueprint.
- **[risk] E1-INDEP.** (a): the chi_u, u in A_Y(w), must be shown independent: chi_u depends on (split bit, own label) of the edge wu and on the zone label of u; the edges wu are distinct and the vertices u are distinct. In the product model this is 'functions of pairwise disjoint coordinate sets of a pi law are mutually independent' (iIndepFun), a general lemma not yet in EG.Lib.Prob (only IndepEvents from pi coordinates). Then EG.FinDist.chernoffGen_lower_half with mu := vm/(4L) <= E and threshold L^5/8 <= mu/2. P(wu in M_Y) = (1/2)(1/k_own) >= 1/(2L) needs k_own = 4J+1 <= L; P(u carries no round-l zone) >= 1 - sum zp >= 1/2 (lemZones(i)).
- **[note] E1-COL-A-BOUND.** The proof of (b) re-derives the COL(a) failure bound (6|Y|^-4) because the STATEMENT of s3:lemCOL only bounds (a),(b),(e) jointly by |Y|^-2/2, which is too weak here (|Y|^-2/2 + |Y|^-4 > |Y|^-2/2). Recommend the s3 Spec export P(COL(a) fails) <= 6N^-4 (or <= N^-2/4, as proved inside lemCOL) as its own conjunct; then (b) is a two-line union bound, and s6:lemLost's 'lend-bad' bound can use it too.
- **[note] E1-ROW3-GAP.** The L15+ hypotheses s >= 40kL are attributed to row 3 of the COL-JV table (s_Y/4 >= 40 k_lend L_Y). For k = 2 on X_Y (s = s_r/2) and for k = k_own on Own_Y (s = s_r/8) row 3 does not literally apply when k_lend is small, and for r >= R-1 (k_lend = 0) row 3 is vacuous. Both needed inequalities (s_r/2 >= 80L, s_r/8 >= 40 k_own L with k_own <= L <= 2 lambda) follow from s_r >= lambda^100: prove them separately (trivial).
- **[note] E1-NUMERICS.** Small-constant facts, all with L = L_Y >= 102*2^8 (eqLY + Gamma1(a)): 3L*2^L*exp(-L^5/32) <= 2^{-4L} (ln(3L) + 5L ln 2 <= L^5/32); 2(2+2N)N^-5 <= 6N^-4 (N >= 2); 7N^-4 <= N^-2/2 (N^2 >= 14); R-r+1 <= L/102 + 1 <= 3L; k_lend <= lambda^3.3 <= N (row 9, N >= lambda^103/2); k_own <= L <= N. Use zpow with N > 0; exp/log inequalities via Real.add_one_le_exp and nlinarith.
- **[note] E1-SAMPLE-SPACE.** 'Over the stage-1 randomness': state on the joint stage1Law (consumers s5:lemExpect and s6:lemLost take expectations on the joint law), or on any μ whose ((1a) of Y, (1b))-marginal is the product law (law-predicate interface, ZONE-LAYER).

**effort:** ~700 Lean lines, difficulty 4/5 ((a) independence + Chernoff + union bound ~250; (b) conditional L15+ x3 (or cite an s3 COL(a) bound) ~250 (+ shared s3 infrastructure); (c) lemCOL(c) application ~80; numerics ~120.)

### `s5:lemExpect` — lemma: expected demotion and lost-parent mass (s5.tex:137)

- **Manuscript referee status:** x2+RT
- **Formalization:** Defs epsU (EG/Defs/Light/Constants.lean or with the s1 constants layer) + Spec EG/Spec/Light/Expect.lean (LemExpectStatement, EpsUTendstoStatement)

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. Over the stage-1 randomness: E[80 dem + 369 lp] <= epsU(D_*) n, where epsU(D_*) := 2462 (log2 D_*)^{-205}. Moreover epsU(D_*) -> 0 as D_* -> infinity. Proof data: E[...] = sum_Y |Y| (80 P(Y demoted) + 369 (R - r(Y)) P(Y in Bad)) (sum over light parts); each term <= |Y|^{-1}(80 + 369(2 log* d_r + 2)) <= |Y|^{-1} 449 log2 lambda_r <= 898 lambda_r^{-103} log2 lambda_r; at most 1.37 n/P_r <= 1.37 n lambda_r^{-103} light parts of round r (propOV (K1)); round r contributes <= 1231 n lambda_r^{-205}; F(x) = x^{-205} is non-increasing with F(2^{x/A}) <= F(x)/2 on [log2 D_*, inf); lemLacunary(ii) gives sum_r F(lambda_r) <= 2F(log2 D_*).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| dem, lp | s5:defStages | s5:defStages | no (new) |
| epsU | 2462 * (logb 2 D)^(-205) | s5:lemExpect | no: new EG.epsU (also used by s7:lemEXprime, Gamma4 through eps1, eps2) |
| expectation | FinDist.expect | - | yes: EG.FinDist.expect, expect_sum, expect_const_mul |
| number of light parts (ancestors) of round r <= 1.37 n/P_r | propOV (K1) | s2:propOV | no: s2 Spec (s2b chunk) |
| lacunary sums | lemLacunary(ii)/(iv), F(x) = x^-205 | s2:lemLacunary | no: s2 Spec |

**deps_declared** (manuscript \deps): s5:lemE1, s5:defStages, s2:propOV, s2:lemTower, s2:lemLacunary, s1:condGamma, s2:propStructure

**deps_from_proof:** s5:lemE1, s5:defStages, s2:propOV, s2:lemLacunary, s1:condGamma, s2:lemTower, s2:propStructure

**deps_notes:** lemE1(b),(c); eqLY (R - r <= 2 log* d_r + 2 <= log2 lambda_r, |Y| >= lambda^103/2; via lemTower(a),(d), propStructure(iv)); propOV (K1) (count of ancestors of round r); P_r = ceil(lambda_r^103) >= lambda_r^103; lemLacunary(ii) (the halving is also derived inline, = lemLacunary(iv) at a = 205); Gamma1(a),(b).

**used_by:** s6:lemLost(iii); s7:lemEXprime (epsX contains epsU); s1:condGamma Gamma4 (epsU in eps1, eps2); s7:lemGammaSat (epsU -> 0)

**randomness:** Expectation over the joint stage-1 law; dem and lp are functions of (1a) colourings and (1b) zone labels only. Used later through ONE Markov bound (multiplier 3) on the combined functional X' (s7:defSchedule (1e)), not separately.

**lean_shape:**

```lean
def epsU (D : ℝ) : ℝ := 2462 * (Real.logb 2 D) ^ (-205 : ℤ)
def LemExpectStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V),
    S5Hyp N0 Dstar G run →
    (stage1Law run G).expect (fun ω => 80 * (dem ω run G : ℝ) + 369 * (lp ω run G : ℝ)) ≤ epsU Dstar * G.card
def EpsUTendstoStatement : Prop := Filter.Tendsto epsU Filter.atTop (nhds 0)
```

**hazards:**

- **[note] EXP-K1-INTERFACE.** The count 'light parts of round r <= 1.37 n/P_r' is propOV (K1) (ancestors of round r); the s2 Spec of propOV must export it as a Finset.card bound on light parts (or ancestors) of round r, indexed by addresses (s2a HB-ADDRESS-IDENTITY), with P_r as the ℕ ceiling.
- **[note] EXP-REAL-POWERS.** Mixes rpow (lambda^103, lambda^1.6 elsewhere), zpow (|Y|^-2, (log D)^-205) and ℕ ceilings (P_r); lambda_r > 1 and log2 lambda_r >= 2^8 (Gamma1(a)) are needed for every monotonicity step; log2 lambda <= lambda for the last step (lambda^-206 log lambda <= lambda^-205). Constants: 80 + 369(2log* + 2) <= 449 log2 lambda (uses 2log* + 2 <= log2 lambda and log2 lambda >= 1); 1.37 * 898 = 1230.26 <= 1231; 2 * 1231 = 2462.
- **[note] EXP-LACUNARY-DOMAIN.** lemLacunary(ii) needs F non-increasing on [x0, inf), x0 = log2 D_*, and F(2^{x/A}) <= F(x)/2 there; the inline proof uses Gamma1(a),(b) at mu = log2 x: x/A >= 2^14 mu^3 >= mu + 1. All lambda_r >= log2 D_* (d_r >= D_* for r <= R).
- **[note] EXP-SUM-REINDEX.** The sum over light parts is regrouped by rounds (sum_{r <= R} sum_{Y of round r}); with LP = ℕ × List Bool this is Finset.sum_fiberwise over Y.1. dem and lp are ℕ; the expectation of the ℝ-cast is linear (FinDist.expect_sum, expect_const_mul, prob_eq_expect).

**effort:** ~350 Lean lines, difficulty 3/5 (linearity ~60; per-term bound ~80; per-round count ~50; lacunary application + F halving ~100; tendsto ~30; constants ~30.)

### `s5:lemChild` — lemma: child side (s5.tex:163)

- **Manuscript referee status:** x2+RT; (c) changed by CR1-PV: x1
- **Formalization:** Spec EG/Spec/Light/Child.lean: LemChildStatement (faithful: PV hypotheses, probability >= 1/3, conclusion on the good event for every H0) + ChildExistsStatement (corollary without labels: for every H0 a partition exists), which is what s5:lemParent and s5:lemKRED consume.

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. Fix a stage-1 outcome and a NON-DEMOTED light part Z of round l; N := |Z|, L := L_Z. Apply s4:lemPV to the vertex set Z with: O := H_Z = X_Z; A(w) := A_Z(w) (defStages; m = ceil(L^6), b = ceil(2^7 L^2 m)); own classes := R_{j,c} (0 <= j < J_Z, c in [4]) and M = M_Z of the colouring of Own_Z (defCOL(iii)); Rt := Rt(Z), Pl := Pl(Z) (defStages); extph(v) := c if v carries a round-l zone of phase c, extph(v) := * if v carries no round-l zone. THEN: (H) all hypotheses of lemPV hold, including (E1'): N >= N0; O a spanning (2^-6, s_l/2)-expander on Z with 2m <= s_l/2; A Lemma-HB sets; own classes pairwise edge-disjoint spanning (2^-6, s')-expanders with s' = s_l/(16 k_own) >= 2^145 L^41 (and 2 ceil(L^6) <= s'); J_Z = floor(log2(L/8)) = PV's J; Z = Rt ⊔ Pl; extph : Z -> [4] u {*} well defined; (E1'): for every w in Pl(Z), #{u in A_Z(w) : wu in M_Z, extph(u) = *} >= L^5/8. (P) Let G_Z be PV's good event for these data: an event over the stage-3 labels of Z (levels on Pl(Z), truncated at J; labels kappa on Z), determined by the stage-1 outcome and these labels, with conditional probability given stage 1 >= 1/2 - eta_PV(N) >= 1/2 - 1/100 >= 1/3. (C) On G_Z, for EVERY edge set H_0(Z) with Own_Z ⊆ H_0(Z) ⊆ E_l(Z) there is a partition H_0(Z) = H^obj(Z) ⊔ H^arc(Z) with: (a) H^obj(Z) decomposes into at most 369 |Pl(Z)| objects; (b) H^arc(Z) is the edge set of a family of pairwise edge-disjoint paths (arcs), each with >= 1 edge and both (distinct) ends in Rt(Z), each carrying a phase c in [4], such that every vertex of a phase-c arc (ends included) lies in no round-l phase-c zone; (c) Z has at most 14(J_Z + 1)|Z| arcs, and every vertex x is an end of at most deg_{H_0(Z)}(x) <= |Z| - 1 arcs; (d) if Rt(Z) = ∅ (in particular if l <= 2) then Z has no arcs. Implicit (used by lemParent (F-d)): arc edges lie in H_0(Z) ⊆ E_l(Z), hence all arc vertices lie in Z (propStructure(iii)).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| PV data / hypotheses / label law / good event / conclusion | s4:lemPV: (Z, O, A, R_{j,c}, M, Rt, Pl, extph), (E1'), labels lev (truncated geometric on Pl) and kappa (on Z), event G_PV = (G2)∧(G4)∧(G5), eta_PV(N) = 2^95 L^31 N^-3 + N L e^{-L^4/16} | s4:lemPV | no: s4 Spec not written (must export PV.Data, PV.Hyp, PV.labelLaw, PV.good, PV.Concl as named Defs; hazard CHILD-PV-INTERFACE) |
| Rt, Pl, AY, vm, vb, demoted, E1, zonePhase | s5:defStages, s5:defZones | s5 | no (new) |
| own classes, Own_Z, M_Z, J_Z, k_own | s3:defCOL(iii) | s3:defCOL | no (s3 accessors) |
| E_l(Z), X_Z | (R5) assignment; light-part graph | s2:defHBtp | no: run.E, run.X (s2a) |
| objects, decomposition | Obj, IsDecomp | s1:defObject | yes: EG.Obj, EG.IsDecomp |
| paths | IsPathIn, walkEdges, pathLength | s1:convGraphs(d) | yes: EG.IsPathIn, EG.walkEdges, EG.pathLength |

**deps_declared** (manuscript \deps): s4:lemPV, s5:defStages, s5:lemZones, s3:lemCOL, s2:propStructure, s3:defCOL, s1:condGamma

**deps_from_proof:** s4:lemPV, s5:defStages, s5:lemZones, s3:lemCOL, s2:propStructure, s3:defCOL, s1:condGamma, s3:lemHB

**deps_notes:** Hypotheses: propStructure(i),(iii),(iv); Gamma3 (N >= P_l/2 >= N0, eta_PV <= 1/100 is an N0 size condition); defStages (non-demoted => COL(a) and (E1) at l = r(Z)); lemCOL(e) (s' >= 2^145 L^41, 2 ceil(L^6) <= s'; a pure inequality in s_l and L, row 8(d)); lemZones(iii) (extph well defined). s3:lemHB enters through A_Z (defStages). The good event and conclusion are lemPV verbatim; (c) weakens PV's 4(J+1)N to 14(J+1)N deliberately.

**used_by:** s5:lemParent (arcs, (F-d)); s5:lemKRED (child vortices); s6:consOrder step (2); s6:thmMIXC; s7:defSchedule (stage 3); s7:lemOneOutcome (non-emptiness of G_Z)

**randomness:** Stage 3 of Z only: levels lev(v) for v in Pl(Z) (P(lev >= j) = 2^-j, truncated at J_Z: P(lev = J) = 2^-J) and kappa(v) for v in Z (P(0) = 1/2, P(c) = 1/8 for c in [4]), all independent; the stage-1 outcome is FIXED (the label index set Pl(Z) depends on it). Downstream only non-emptiness of G_Z is used (s7:lemOneOutcome: 'only this non-emptiness is used').

**lean_shape:**

```lean
-- s4 must export (names proposed): PV.Data V, PV.Hyp, PV.labelLaw, PV.good, PV.Concl
noncomputable def childData (ω : Stage1 V) run G (Z : LP) : PV.Data V where
  Z := run.partVerts G Z.1 Z.2; O := run.X G Z.1 Z.2; A := AY run G Z
  R := fun j c => ω.ownCls Z (ownIdx run G Z j c); M := ω.Mcls Z
  Rt := Rt ω run G Z; Pl := Pl ω run G Z; ext := fun v => zonePhase ω.zlab Z.1 v
def ChildConcl ω run G (Z : LP) (H0 Hobj : Finset (Sym2 V)) (D : List (Obj V)) (arcs : List (List V × Fin 4)) : Prop :=
  Disjoint Hobj (arcEdges arcs) ∧ Hobj ∪ arcEdges arcs = H0 ∧
  IsDecomp (↑Hobj) D ∧ (D.length : ℝ) ≤ 369 * (Pl ω run G Z).card ∧                                   -- (a)
  (arcs.flatMap (fun a => walkEdges a.1)).Nodup ∧
  (∀ a ∈ arcs, IsPathIn H0 a.1 ∧ 1 ≤ pathLength a.1 ∧
     (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ Rt ω run G Z) ∧
     ∀ x ∈ a.1, zonePhase ω.zlab Z.1 x ≠ some a.2) ∧                                                 -- (b)
  (arcs.length : ℝ) ≤ 14 * (J run G Z + 1) * (run.partVerts G Z.1 Z.2).card ∧
  (∀ x, (arcs.filter (fun a => a.1.head? = some x ∨ a.1.getLast? = some x)).length ≤ degE H0 x) ∧    -- (c)
  (Rt ω run G Z = ∅ → arcs = [])                                                                      -- (d)
def LemChildStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ ω ∈ (stage1Law run G).supp, ∀ Z ∈ run.lightParts G, ¬ demoted ω run G Z →
    PV.Hyp (childData ω run G Z) ∧
    (1 / 3 : ℝ) ≤ (PV.labelLaw (childData ω run G Z)).prob (PV.good (childData ω run G Z)) ∧
    ∀ λ ∈ PV.good (childData ω run G Z), ∀ H0, ω.Own Z ⊆ H0 → H0 ⊆ run.E G Z.1 Z.2 →
      ∃ Hobj D arcs, ChildConcl ω run G Z H0 Hobj D arcs
def ChildExistsStatement : Prop :=   -- consumed by lemParent / K-RED
  ∀ V [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ ω ∈ (stage1Law run G).supp, ∀ Z ∈ run.lightParts G, ¬ demoted ω run G Z →
    ∀ H0, ω.Own Z ⊆ H0 → H0 ⊆ run.E G Z.1 Z.2 → ∃ Hobj D arcs, ChildConcl ω run G Z H0 Hobj D arcs
```

**hazards:**

- **[risk] CHILD-PV-INTERFACE.** lemChild is an instantiation of s4:lemPV; its Lean statement can only be written once the s4 Spec exports PV's data record, hypothesis predicate (with the size condition PVSize N, s1 CONST-N0-INPROOF), label law (index set Pl for levels, Z for kappa, truncated geometric law per CONVENTIONS), good event and conclusion as NAMED Defs. The own classes are indexed (j,c) in Fin J × Fin 4 plus M in PV but come from a uniform Fin k_own labelling in s3: a fixed bijection ownIdx must be shared by s3 (COL(a) quantifies over all k_own classes), s5:defStages (M_Y) and the PV data. Any mismatch (e.g. M taken as label 0 in one place and label k_own-1 in another) breaks (E1').
- **[note] CHILD-ARC-VERTS.** (b) as stated does not say that arc vertices lie in Z or that arc edges lie in H_0(Z)/E_l(Z); lemParent (F-d) uses both (via propStructure(iii): edges of E_l(Z) have both ends in Z). Put 'IsPathIn H0' in the Lean conclusion (ChildConcl), from which both follow. Ends distinct is part of PV(b) and follows from IsPathIn (Nodup) and length >= 1.
- **[note] CHILD-SIMULTANEITY.** 'On G_Z the conclusion holds for EVERY admissible H_0 simultaneously' (G_Z does not depend on H_0) is what makes the round-by-round construction non-anticipating. In Lean, existence proofs downstream only need ∀ H0 ∃ partition (labels may be chosen after H0), so provide ChildExistsStatement as a corollary and let lemParent/K-RED depend only on it; keep the faithful LemChildStatement for fidelity (s7:lemOneOutcome's joint stage-3 outcome is then not needed in Lean).
- **[note] CHILD-OWN-THRESHOLD.** PV needs s' >= 2^145 L^41; lemCOL(e) (row 8(d)) supplies it. PLAN R3 (Haxell) may move PV's threshold to 2^146 L^41; then row 8(d) and Gamma1(f) change (R6 eventualities absorb it). The Lean statement should take the threshold from the s4 Spec, not hard-code 2^145.
- **[note] CHILD-E1-INSTANCE.** (E1') is the l = r(Z) instance of (E1) restricted to w in Pl(Z); C_w of PV counts EDGES wu, (E1) counts VERTICES u in A_Z(w): equal because u |-> wu is injective. extph(u) = * iff zonePhase ω.zlab l u = none.
- **[note] CHILD-STAGE3-SPACE.** The level labels are indexed by Pl(Z), which depends on the stage-1 outcome: the stage-3 space is a function of ω. Harmless because ω is fixed (universally quantified) before the stage-3 law is formed; never form a joint stage-1 × stage-3 law.
- **[note] CHILD-PROB-CONST.** 1/2 - eta_PV(N) >= 1/2 - 1/100 >= 1/3 uses the N0 size condition eta_PV(N) <= 1/100 for N >= N0 (N >= P_l/2 >= N0 by Gamma3). The '1/2 - o(1)' of the text is this explicit bound.

**effort:** ~300 Lean lines, difficulty 3/5 (build PV data ~60; hypotheses check ~150 (expanders from COL(a), thresholds from lemCOL(e), (E1') from (E1), sizes); conclusion transfer ~60; corollary ~30.)

### `s5:lemParent` — lemma: parent side: multi-parent chaining over U-bundles (s5.tex:213)

- **Manuscript referee status:** x2+RT; (F-d), Steps 5-6 changed by CR1-PV: x1
- **Formalization:** Spec EG/Spec/Light/Parent.lean split into (A) ParentChainStatement: a deterministic combinatorial lemma for one round l (all four phases jointly) whose INPUT is any family of arc systems satisfying the child-side properties (not 'the arcs given by lemChild'), and (B) ChainSumStatement: the numeric bound sum_l (...) <= epsChain(D_*) n, plus EpsChainTendsto. Needs new foundations: EG.MGraph (multigraph with loops, loop degree 2), spanning forests, T-joins in forests, Euler circuits of even connected multigraphs, closed trails as cyclic lists of oriented arcs.

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. Fix a stage-1 outcome and, for every non-demoted light part Z, a stage-3 outcome in G_Z (lemChild). Fix a round l with 3 <= l <= R and, for every non-demoted light Z of round l, an edge set H_0(Z) with Own_Z ⊆ H_0(Z) ⊆ E_l(Z); the arcs of Z are those of lemChild for this H_0(Z). For c in [4], the U-bundle B_{l,c} := all phase-c arcs of all non-demoted light parts of round l; E(B_{l,c}) := union of their edge sets. J-bar_l := max{J_Z : Z light of round l} (0 if none); nu_l := number of ancestors of rounds <= l-2 (propOV). THEN for every c in [4] there is an edge set LentU_{l,c}, disjoint from E(B_{l,c}), such that E(B_{l,c}) ∪ LentU_{l,c} decomposes into cycles and single edges, where: (i) LentU_{l,c} ⊆ U_Y U_{u in [Tslot_Y]} LU_{Y,l,c,u}, Y over the good parents of rounds <= l-2; every edge of LentU_{l,c} ∩ LU_{Y,l,c,u} lies on a CONNECTOR: a path in LU_{Y,l,c,u} all of whose interior vertices lie in Zone_{Y,l,c,u}; (ii) the number of objects summed over c in [4] is at most 4*14 (J-bar_l + 1) M_l (M_l + 1) nu_l + cap_l, with cap_l (number of visit-capping pieces) <= 14 (J-bar_l + 1) n/(102 log2 lambda_{l-2})^2; and sum_{l=3}^R (4*14(J-bar_l + 1) M_l(M_l + 1) nu_l + cap_l) <= epsChain(D_*) n with epsChain(D) := 614/D + log2(2A log2(A log2 log2 D)) / (371 (log2 log2 D)^2), A = 105; (iii) every object consists of edges of E(B_{l,c}) ∪ LentU_{l,c}, and every such edge lies in exactly one object. Moreover: the sets LentU_{l,c} for distinct (l,c) are pairwise disjoint; the objects and LentU_{l,c} depend only on the stage-1 outcome and on B_{l,c}; epsChain(D_*) -> 0. Proof structure (all of it needs Lean): (F-a) |Z| <= M_l, J_Z + 1 <= log2 log2 M_l; (F-c) round-l light parts vertex-disjoint, edge sets E_l(Z), E_r(Y) pairwise disjoint; (F-d) arc facts (from lemChild), each vertex an end of <= |Z|-1 <= M_l - 1 arcs; Step 1 classes A_i (i-th arc of each Z; arcs of a class vertex-disjoint); Step 2 quotient multigraph UQ_{l,c,i} on the good parents of rounds <= l-2, edge e_a = {par(v), par(v')} (loop allowed), <= nu_l <= 2.74 n/P_{l-2} nodes; Step 3 T-join T_i in a spanning forest (|T_i| <= nu_l - 1; arcs with e_a in T_i output as single edges, <= M_l - 1 each), closed Euler trails of the even components (<= nu_l per class); transition claim (the two vertices of each transition are distinct vertices of its node); Step 4 visit capping (split a trail at Y into ceil(vis/Tslot_Y) blocks; total extra trails cap_l <= sum tr/Tslot_Y); Step 5 distinct slots per trail and node; pair multisets P_{Y,u}; every vertex in <= M_l - 1 <= t_Y pairs (M_l <= lambda_{l-2}^1.6 <= lambda_r^1.6); Step 6 routing by path connectivity of LU_{Y,l,c,u} through Zone_{Y,l,c,u} (Y not parent-bad); Step 7 cycle claim (C(W) is a cycle of length >= 3); Step 8 exact cover; Step 9 counting and the two sums (307n/M_l with sum 1/M_l <= 2/D_*; eta(x) = log2(2A log2(A log2 x))/(log2 x)^2 non-increasing with eta(2^{x/A}) <= eta(x)/2).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| U-bundle B_{l,c}, E(B_{l,c}) | phase-c arcs of the round-l non-demoted light parts and their edges | s5:lemParent | no: new (arc families as LP → List (List V × Fin 4)) |
| good parent, Rt, par, Zone, Tslot, t_Y, LU classes | s5:defStages, s5:defZones, s3:defCOL | s5, s3 | no (new) |
| J-bar_l, nu_l | max J_Z over light Z of round l; number of ancestors of rounds <= l-2 | s5.tex:211, s2:propOV | no: new (nu_l from the s2 ancestor API) |
| quotient multigraph UQ_{l,c,i} (loops allowed), degree (loop counts 2), components, spanning forest | MGraph N I := I → Sym2 N | s5:lemParent Step 2; PLAN §3 decision 2 | no: EG.MGraph not defined (s1 blueprint CONV-MGRAPH) |
| T-join in a forest; Euler circuit of an even connected multigraph | s1:citEuler (a),(b), applied to multigraphs with loops | s1:citEuler | no (s1 blueprint EUL-MULTI-USE, EUL-STAGEALPHA) |
| closed trail of arcs, transition, node, visits, blocks, slots | cyclic sequence (a_1..a_k) of distinct oriented arcs of one class with par(v_j^+) = par(v_{j+1}^-) | s5:lemParent Steps 3-5 | no: new (List (arc index × Bool) with rotation) |
| path connectivity (multiset sense) | Def 7 over indexed pair families | s1:citDef7, s3:lemMonotone(iii) | yes: EG.FGraph.IsPathConnected (+ IsPathConnected.exists_paths for other universes) |
| epsChain | 614/D + log2(2A log2(A log2 log2 D))/(371 (log2 log2 D)^2) | s5:lemParent(ii) | no: new EG.epsChain (= epsK, used in Gamma4 through eps1) |

**deps_declared** (manuscript \deps): s5:lemChild, s5:defStages, s5:lemZones, s3:defCOL, s3:lemCOL, s3:lemCOLJV, s3:lemMonotone, s1:citEuler, s2:propOV, s2:lemTower, s2:propStructure, s1:condGamma, s1:citDef7

**deps_from_proof:** s5:lemChild, s5:defStages, s5:lemZones, s3:defCOL, s3:lemMonotone, s1:citEuler, s2:propOV, s2:lemTower, s2:propStructure, s1:condGamma, s1:citDef7, s2:lemLacunary

**deps_notes:** (F-a): propStructure(ii) (= lemCap(ii), |Z^0| <= M_l). (F-c): propStructure(iii),(iv). (F-d): lemChild(b),(c) + propStructure(iii). Step 2: nu_l <= 2.74 n/P_{l-2} is lemTower(b) (completing propOV (K1)). Step 3: citEuler(a),(b) on MULTIGRAPHS with loops. Step 4: eqLY (Tslot >= (102 log2 lambda_r)^2), lemTower(a) (lambda_r >= lambda_{l-2}). Step 5: lemTower(b) (M_l <= lambda_{l-2}^1.6; = row 12 of the COL-JV table), defCOL (t_Y). Step 6: defStages (not parent-bad), lemMonotone(iii). Step 7: lemZones(iii), F-d, G simple. Step 9: lemTower(b) (P_{l-2} >= M_l^13, sum 1/M_l <= 2/D_*, M_l <= (A log lambda_{l-2})^{2A}), lemTower(a), Gamma1(a),(b); the halving argument for eta is lemLacunary(i)/(ii)-type but done inline (lemLacunary undeclared). Declared but not used: s3:lemCOL, s3:lemCOLJV (only through t_Y / row 12, cited via lemTower), (F-b) is explicitly unused.

**used_by:** s5:lemDemoted (pointer: demoted classes unused); s5:lemKRED (U-chaining); s6:consOrder step (2); s6:lemLent(i),(ii),(iv); s6:thmMIXC

**randomness:** None: deterministic given the fixed stage-1 outcome (zones, colourings, statuses) and the arc systems (which come from fixed stage-3 outcomes via lemChild). The 'fixed rules' (class order, spanning forest, Euler trails, node order for capping, slot assignment, choice of connectors) become existentials/Classical.choose (PLAN §3 decision 7).

**lean_shape:**

```lean
/-- child-side properties of arc systems of the round-l non-demoted light parts ((F-d) + lemChild (b),(c)) -/
def ArcHyp (ω : Stage1 V) run G (l : ℕ) (arcs : LP → List (List V × Fin 4)) : Prop :=
  ∀ Z ∈ run.lightParts G, Z.1 = l → ¬ demoted ω run G Z →
    ((arcs Z).flatMap (fun a => walkEdges a.1)).Nodup ∧
    (∀ a ∈ arcs Z, IsPathIn (run.E G l Z.2) a.1 ∧ 1 ≤ pathLength a.1 ∧
       (∀ x, (a.1.head? = some x ∨ a.1.getLast? = some x) → x ∈ Rt ω run G Z) ∧
       ∀ x ∈ a.1, zonePhase ω.zlab l x ≠ some a.2) ∧
    ((arcs Z).length : ℝ) ≤ 14 * (J run G Z + 1) * (run.partVerts G Z.1 Z.2).card ∧
    ∀ x, (((arcs Z).filter (fun a => a.1.head? = some x ∨ a.1.getLast? = some x)).length : ℝ)
          ≤ (run.partVerts G Z.1 Z.2).card - 1
def bundle (arcs : LP → List (List V × Fin 4)) (Zs : Finset LP) (c : Fin 4) : Finset (Sym2 V) := ...
def IsConnectorEdge ω run G (l : ℕ) (c : Fin 4) (e : Sym2 V) : Prop :=
  ∃ Y u p, goodParent ω run G Y ∧ Y.1 + 2 ≤ l ∧ u < Tslot run G Y ∧
    IsPathIn (ω.LU Y (l, c, u)) p ∧ IsThrough (Zone ω.zlab run G Y (l, c, u)) p ∧ e ∈ walkEdges p
def ParentChainStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ ω ∈ (stage1Law run G).supp, ∀ l, 3 ≤ l → l ≤ run.R → ∀ arcs, ArcHyp ω run G l arcs →
  let Zs := (run.lightParts G).filter (fun Z => Z.1 = l ∧ ¬ demoted ω run G Z)
  ∃ (LUsed : Fin 4 → Finset (Sym2 V)) (D : Fin 4 → List (Obj V)) (cap : ℕ),
    (∀ c, Disjoint (LUsed c) (bundle arcs Zs c) ∧ IsDecomp ↑(bundle arcs Zs c ∪ LUsed c) (D c) ∧
          ∀ e ∈ LUsed c, IsConnectorEdge ω run G l c e) ∧                                        -- (i),(iii)
    (cap : ℝ) ≤ 14 * (Jbar run G l + 1) * G.card / (102 * Real.logb 2 (lamOf (run.d G (l - 2)))) ^ 2 ∧
    ((∑ c, (D c).length : ℕ) : ℝ) ≤ 4 * 14 * (Jbar run G l + 1) * MOf (run.d G l) * (MOf (run.d G l) + 1)
                                       * nu run G l + cap                                          -- (ii)
-- G-S5-1 (TRIAGE item 20): one locked copy of the formula, `EG.Chain.epsK` (EG/Defs/Chain/Constants.lean,
-- = 614 / D + logb 2 (2 * 105 * logb 2 (105 * logb 2 (logb 2 D))) / (371 * logb 2 (logb 2 D) ^ 2)).
noncomputable def epsChain (D : ℝ) : ℝ := EG.Chain.epsK D
def ChainSumStatement : Prop := ∀ V [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∑ l ∈ Finset.Icc 3 run.R, (4 * 14 * (Jbar run G l + 1) * MOf (run.d G l) * (MOf (run.d G l) + 1) * nu run G l
     + 14 * (Jbar run G l + 1) * G.card / (102 * Real.logb 2 (lamOf (run.d G (l - 2)))) ^ 2) ≤ epsChain Dstar * G.card
def EpsChainTendsto : Prop := Filter.Tendsto epsChain Filter.atTop (nhds 0)
```

**hazards:**

- **[risk] PAR-MGRAPH-EULER.** Steps 2-3 use a multigraph with loops and parallel edges (UQ_{l,c,i}), a T-join inside a spanning FOREST with |T_i| <= nu_l - 1, and closed Euler trails of every even component (count <= number of nodes). EG.MGraph, components, spanning forests and Euler for multigraphs with loops do not exist (s1 blueprint CONV-MGRAPH, EUL-MULTI-USE, EUL-STAGEALPHA); if Euler is a stage-alpha hypothesis for SIMPLE graphs, the multigraph-with-loops version needs the subdivision derivation (~800 lines). The count bound matters: a mere cycle decomposition of the even multigraph would give too many trails (the per-class count must be <= nu_l, not <= #arcs), so Euler per component is genuinely needed. Alternative that avoids a multigraph TYPE: state T-join and Euler for 'finite index set I with an endpoint map I → Sym2 N' directly.
- **[risk] PAR-ARCS-INPUT.** Definition-vs-use: lemParent's hypothesis says 'the arcs of Z are those given by lemChild for this H_0(Z)', but lemChild only ASSERTS EXISTENCE of arcs; there is no function 'the arcs'. The Lean lemma must take ANY arc systems satisfying the child-side properties (ArcHyp: lemChild(b),(c) + arc edges ⊆ E_l(Z)) as input. This also removes the stage-3 hypothesis (fixed outcomes in G_Z) from lemParent entirely; K-RED then feeds it the arcs obtained from ChildExistsStatement. With this reading the lemma is purely deterministic and strictly more general, and the manuscript proof uses only (F-a)-(F-d).
- **[risk] PAR-TRAIL-SURGERY.** Steps 3-8 are heavy list combinatorics: closed trails as cyclic sequences of oriented arcs (rotation to put a Y-transition last, cutting into segments at Y-transitions, grouping into blocks of <= Tslot_Y segments, re-closing each block), invariants (every arc end in exactly one transition; vis_{Y'} unchanged for Y' ≠ Y; arcs partitioned), slot assignment, forming the closed walk C(W) by concatenating arc vertex lists and connector interiors, and proving Obj.WF (Nodup, length >= 3) and that cycleEdges C(W) is exactly the union of the arcs' and connectors' edges (list-level, with the orientation reversal of arcs). Estimate 1500+ lines; it is the single largest s5 proof. Keeping arcs as vertex lists (EG.Defs.Walk) and orientations as Bool avoids transport.
- **[risk] PAR-ETA-MONO.** Step 9 needs eta(x) = x3/x1^2 (x1 = log2 x, x2 = log2(A x1), x3 = log2(2A x2)) NON-INCREASING on [log2 D_*, inf) (the manuscript differentiates ln eta in x1) and eta(2^{x/A}) <= eta(x)/2 (via 2A^2 x1^2 log2(2A x1) <= 4A^3 x1^3 <= (2^14 A x1^3)^2 <= 2^{2 x1}, Gamma1(b)). In Lean either Mathlib's antitoneOn_of_deriv_nonpos on nested logb (with domain side conditions x2, x3 > 0) or a manual argument (x3 grows at most like log x1 while x1^2 grows) — ~250 lines of real analysis. The geometric-sum step is then lemLacunary(i) (cite it instead of redoing it).
- **[risk] PAR-DEPENDS-ONLY.** 'The objects and LentU_{l,c} depend only on the stage-1 outcome and on B_{l,c}' has no direct Lean meaning; it supports K-RED's causality clause (KRED-CAUSALITY). Either drop it (recommended, if K-RED/MIX-C are restructured as existence statements) or state lemParent as the existence of a FUNCTION chainU : (arc systems) → (LUsed, D) satisfying the properties for every admissible input (a Skolemized form; follows from the ∀∃ form by choice).
- **[note] PAR-JOINT-PHASES.** (ii) bounds the object count SUMMED over c (cap_l is a joint quantity: sum over Y, c, i of tr/Tslot_Y <= total number of arcs of round l). A per-phase Lean statement would need a per-phase cap bound that the manuscript does not state; state all four phases in one conclusion (as in the sketch).
- **[note] PAR-M-INTEGER.** s2a blocker HB-M-INTEGER (M_l real vs integer) does not affect s5: every use here is an inequality (|Z| <= M_l, |Z| - 1 <= M_l - 1 <= t_Y, M_l + 1 <= 2M_l, J-bar + 1 <= log2 log2 M_l <= M_l, 1/M_l sums). Works with either decision.
- **[note] PAR-CONSTANTS.** Small constants: (nu-1)(M-1) + nu <= nu M (M >= 1); 56*2*2.74 = 306.88 <= 307 and the real exponent gap M^3/M^13 <= 1/M; 14/102^2 = 1/743.14 <= 1/743; 2/743 <= 1/371; 307*2 = 614. The cap estimate uses Tslot_Y >= L_Y^2 >= (102 log2 lambda_r)^2 >= (102 log2 lambda_{l-2})^2 (eqLY, lambda non-increasing in the round). All norm_num/nlinarith.
- **[note] PAR-NU.** nu_l counts ALL ancestors (light and standalone, all rounds <= l-2); the quotient nodes are only good parents, so #nodes <= nu_l; |T_i| <= |E(F_i)| <= #nodes - 1 needs at least one node when there are arcs (true: arc ends lie in Rt, so good parents exist). nu_l <= 2.74 n/P_{l-2} is lemTower(b).
- **[note] PAR-MULTIPLICITY.** Step 5: every vertex v lies in at most M_l - 1 <= t_Y pairs of P_{Y,u} (counted over ALL final trails of ALL classes for fixed (l,c)); the proof needs 'each arc end in exactly one transition' across block splits, and 'all arcs ending at v belong to the unique round-l light part Z(v)' ((F-c),(F-d)). The multiset P_{Y,u} is an indexed family over the finite type of (trail, position) pairs; IsPathConnected quantifies over ι : Type (use IsPathConnected.exists_paths if the index type lives elsewhere). Pair entries must be distinct vertices of V(Y) (transition claim).
- **[note] PAR-CYCLE-SIMPLE.** Cycle claim (length >= 3) uses G simple and E_l(Z) ∩ E_r(Y) = ∅ for r <= l-2 (propStructure(iii)); connector interiors avoid arcs because arcs avoid all round-l phase-c zones and interiors of distinct connectors of one trail are disjoint because zones of distinct (Y,u) are disjoint (lemZones(iii)) and slots at a node within a trail are distinct (Step 5).
- **[note] PAR-UNDECLARED.** Undeclared logical dependency: s2:lemLacunary (the halving/geometric-sum argument is re-proved inline). Declared but unused: s3:lemCOL, s3:lemCOLJV (row 12 enters via lemTower(b)), s1:condGamma is used (Gamma1(a),(b) at mu = log2 x). (F-b) is explicitly unused.

**effort:** ~3000 Lean lines, difficulty 5/5 (MGraph + T-join + Euler for multigraphs (if not supplied by s1 work) ~800; classes/quotient ~200; trails, capping, slots ~700; routing + cycle assembly + exact cover ~800; counting (ii) ~200; ChainSum + eta analysis ~300.)

### `s5:lemDemoted` — lemma: fallback for demoted light parts (s5.tex:326)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec EG/Spec/Light/Demoted.lean: LemDemotedStatement (faithful, with the VX+ good event) + DemotedExistsStatement (corollary: ∀ E with E(X_Y) ⊆ E ⊆ E_r(Y), ∃ decomposition with <= 80|Y| objects).

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. Fix a stage-1 outcome and a demoted light part Y of round r; N := |Y|, L := L_Y. (1) Y is not a good parent; in particular no class LU_{Y,.} of Y is used in lemParent. (2) Apply s4:thmVXp to Z := Y, O := X_Y with eps_O = 2^-6, s = s_r/2: its hypotheses hold (N >= P_r/2 >= N0 by Gamma3; X_Y a spanning (2^-6, s_r/2)-expander; s_r/2 >= 2^151 L^38 log2 L, row 8(c) of the COL-JV table, valid in every round r <= R including r >= R-1). Let G^VX_Y be its good event: an event over the VX+ labels of Y (stage 3: uniform colouring of E(X_Y) with 3J+1 colours, J = floor(log2(L/6)); levels on Y truncated at J; kappa on Y), depending only on X_Y and these labels, with probability >= 1 - eta_VX(N) >= 1/2 (the text states >= 1/2 - o(1) >= 1/3). (3) On G^VX_Y, for EVERY edge set E with E(X_Y) ⊆ E ⊆ E_r(Y), E decomposes into at most 80|Y| objects (f(E) <= 80|Y|).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| VX+ data, hypotheses, label law, good event, conclusion | s4:thmVXp with eps_O in {2^-5, 2^-6} and thresholds 2^146 / 2^151 L^38 log2 L | s4:thmVXp | no: s4 Spec not written (must export VX.Hyp, VX.labelLaw, VX.good) |
| demoted, goodParent | s5:defStages | s5:defStages | no (new) |
| X_Y, E_r(Y), s_r | s2 run objects | s2:defHBtp | no (s2a proposals) |
| decomposition | IsDecomp | s1:defObject | yes |

**deps_declared** (manuscript \deps): s4:thmVXp, s2:propStructure, s3:lemCOLJV, s2:lemTower, s1:condGamma, s5:defStages, s5:lemParent

**deps_from_proof:** s4:thmVXp, s2:propStructure, s3:lemCOLJV, s2:lemTower, s1:condGamma, s5:defStages, s5:lemParent

**deps_notes:** (1): defStages (demoted => in Bad => not a good parent) and lemParent(i) (uses only classes of good parents). (2): propStructure(i),(iii),(iv); lemCOLJV row 8(c), or directly s_r >= lambda^100 and L <= 2 lambda (lemTower(b)) with log2 lambda >= 2^8 (Gamma1(a)): 2^152 L^38 log2 L <= 2^191 lambda^39 <= lambda^100; Gamma3 (N0 and eta_VX <= 1/100).

**used_by:** s5:lemKRED (demoted parts); s6:consOrder step (2); s6:lemLent(ii); s6:thmMIXC; s7:defSchedule (stage 3); s7:lemOneOutcome

**randomness:** Stage 3 of Y: the VX+ labels (uniform (3J+1)-colouring of E(X_Y), truncated levels on Y, kappa on Y with P(0) = 1/2, P(c) = 1/6); the stage-1 outcome enters only through 'Y demoted' (the VX+ event itself depends only on X_Y, a function of the run). Only non-emptiness is used downstream.

**lean_shape:**

```lean
def LemDemotedStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ Y ∈ run.lightParts G,
    (∀ ω, demoted ω run G Y → ¬ goodParent ω run G Y) ∧
    VX.Hyp (run.partVerts G Y.1 Y.2) (run.X G Y.1 Y.2) (2 ^ (-6 : ℤ)) ((sOf (run.d G Y.1) : ℝ) / 2) ∧
    (1 / 3 : ℝ) ≤ (VX.labelLaw (run.X G Y.1 Y.2)).prob (VX.good (run.X G Y.1 Y.2)) ∧
    ∀ λ ∈ VX.good (run.X G Y.1 Y.2), ∀ E : Finset (Sym2 V),
      (run.X G Y.1 Y.2).edges ⊆ E → E ⊆ run.E G Y.1 Y.2 →
      ∃ D : List (Obj V), IsDecomp ↑E D ∧ (D.length : ℝ) ≤ 80 * (run.partVerts G Y.1 Y.2).card
def DemotedExistsStatement : Prop := ∀ V [Fintype V] [DecidableEq V] N0 Dstar G run, S5Hyp N0 Dstar G run →
  ∀ Y ∈ run.lightParts G, ∀ E, (run.X G Y.1 Y.2).edges ⊆ E → E ⊆ run.E G Y.1 Y.2 →
    ∃ D : List (Obj V), IsDecomp ↑E D ∧ (D.length : ℝ) ≤ 80 * (run.partVerts G Y.1 Y.2).card
```

**hazards:**

- **[risk] DEM-VX-INTERFACE.** Needs the s4 Spec of thmVXp with the eps_O = 2^-6 branch, the size predicate VXSize N (from N0Cond), and the 'for every graph G with V(G) = Z and E(O) ⊆ E(G)' form exported with a named good event. In Lean 'graph with V(G) = Z' becomes an edge set E with O.edges ⊆ E and all edges inside Z (E ⊆ E_r(Y) gives this by propStructure(iii)); E must be loopless (true: subset of G.edges) for IsDecomp/fnum conventions.
- **[note] DEM-NOT-STAGE1.** Part (2)-(3) does not depend on the stage-1 outcome (VX+ runs on X_Y, a run object); state it for EVERY light part Y (demotedness is irrelevant), which is stronger and simpler. Only (1) mentions ω.
- **[note] DEM-THRESHOLD.** Numeric: 2^152 L^38 log2 L <= 2^190 lambda^38 * 2 lambda = 2^191 lambda^39 <= lambda^100 needs lambda^61 >= 2^191 (log2 lambda >= 2^8) and L <= 2 lambda (lemTower(b)), log2 L <= L; the manuscript cites row 8(c) instead (same fact). Probability: 1 - eta_VX >= 1/2 >= 1/3 by the N0 size condition.

**effort:** ~130 Lean lines, difficulty 2/5 (hypothesis check ~70, conclusion transfer ~30, corollary ~30 (given the s4 VX Spec).)

### `s5:lemKRED` — lemma: Lemma K-RED (s5.tex:337)

- **Manuscript referee status:** x2+RT; for-all form in Lentext: x2 (JV+* referees)
- **Formalization:** Defs Kstd, LentExtHyp (EG/Defs/Light/KRED.lean) + Spec EG/Spec/Light/KRED.lean: LemKREDStatement as a pure existence statement (∀ stage-1 outcome of positive probability, ∀ admissible Lentext family, ∃ decomposition with the bound). The causality clause ('objects of round l depend only on ...') is NOT recommended as part of the Spec (see KRED-CAUSALITY).

**Statement (precise restatement).** SETTING (s5.tex:9, applies to every s5 node): G is a finite simple graph on n >= N0 vertices with d_1 >= D_*; D_* satisfies Gamma1-Gamma4 (only Gamma1 including (f), Gamma3 and N0-admissibility are used in s5; Gamma2(a) follows from Gamma1(a); Gamma4 only in remConstants(b)); a valid HB*^{tau+} run on G with R rounds is fixed; the stage-1 data (s3:defCOL (i)-(iv), the zone labels of s5:defZones, the pool labels of s7:defPool) are drawn; every statement holds for every stage-1 outcome it does not name. For a light part Y (identified by (round, pre-part address), vertex set V(Y) = Y^0 \ S_Y, also written Y): r = r(Y), L_Y = log2|Y| (real), H_Y = X_Y, J_Y = floor(log2(L_Y/8)), k_own = 4J_Y + 1. Fix the valid run, a stage-1 outcome, and stage-3 outcomes in the good events of all light parts (G_Z of lemChild for non-demoted Z; G^VX_Z of lemDemoted for demoted Z). Let (Lentext(Y))_Y be ANY family indexed by the light parts with Lentext(Y) ⊆ (U_{l,j} LJS_{Y,l,j}) ∪ (U_l LJV_{Y,l}) and Lentext(Y) = ∅ if Y is demoted. Kstd := ⊔_l ⊔_{Z in Std_l} E_l(Z) (standalone pre-parts; a function of the run alone). PROCESS rounds l = R, R-1, ..., 1: (1) for every non-demoted light Z of round l: LentU(Z) := E(H_Z) ∩ U_{l' >= l+2, c in [4]} LentU_{l',c} (U-lent edges of Z used by lemParent at rounds already processed); H_0(Z) := E_l(Z) \ (LentU(Z) ∪ Lentext(Z)); decompose H_0(Z) by lemChild into H^obj(Z) (objects) and arcs; (2) for every demoted light Z of round l, decompose E_l(Z) by lemDemoted; (3) if l >= 3 apply lemParent to the bundles B_{l,c}, c in [4], formed from the arcs of (1). Output the long cycles U_l Cyc_l and the edges of E_0 (single edges). THEN the objects produced form a decomposition of E(G) \ Kstd \ U_Y Lentext(Y) into at most (D_*/2 + 745 + epsK(D_*)) n + 80 dem + 369 lp objects, epsK := epsChain. Itemized: long cycles and E_0 at most n + D_* n/2; child vortices at most 369 sum_Z |Pl(Z)| <= 369(2n + lp); U-chaining at most epsChain(D_*) n; demoted parts at most 80 dem; exact sum <= (D_*/2 + 739 + epsK) n + 80 dem + 369 lp. No edge of Kstd and no edge of any Lentext(Y) is used. Moreover the objects produced at round l depend only on the stage-1 and stage-3 outcomes, on the sets Lentext(Z) of the round-l light parts Z, and on what was produced at rounds > l. Every object is a cycle of length >= 3 or a single edge.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| Kstd | union over l <= R and Z in Std_l of E_l(Z) | s5.tex:335 | no: new EG.Light.Kstd (from run.Std, run.E) |
| Lentext family, LentU(Z), H_0(Z) | as in the statement; JS/JV classes from s3:defCOL(ii) | s5:lemKRED | no: new LentExtHyp; s3 accessors ω.LJS, ω.LJV |
| Cyc_l, E_0, Std_l, E_l(Z) | long cycles of round l, edges of G_{R+1}, standalone pre-parts, assigned edges | s2:defHBtp | no: s2a proposals (run.cycles, run.E0, run.Std, run.E) |
| dem, lp, demoted, Pl | s5:defStages | s5:defStages | no (new) |
| decomposition | IsDecomp over a Set (Sym2 V); objects Obj (edge \| cycle list) | s1:defObject | yes: EG.IsDecomp, EG.Obj |
| epsK = epsChain | s5:lemParent(ii) | s5:lemParent | no (new) |

**deps_declared** (manuscript \deps): s5:lemChild, s5:lemParent, s5:lemDemoted, s2:propStructure, s2:propParentless, s2:lemEL, s3:defCOL, s5:defStages

**deps_from_proof:** s5:lemChild, s5:lemParent, s5:lemDemoted, s2:propStructure, s2:propParentless, s3:defCOL, s5:defStages

**deps_notes:** Edge partition: propStructure(iii) (E(G) = ⊔ Cyc ⊔ E_0 ⊔ ⊔_light E_r(Y) ⊔ Kstd; E(H_Y) ⊆ E_r(Y); edges of E_r(Y) inside V(Y); sum |Cyc_l| <= n; |E_0| < D_* n/2). Lentext(Y) ⊆ Lend_Y ⊆ E(H_Y) and U-/JS-/JV-classes pairwise disjoint and disjoint from Own_Y: defCOL(i),(ii). eqPl (defStages; = propParentless(iii) with Bad). lemChild(a),(d); lemParent(i)-(iii) and disjointness of the LentU_{l,c}; lemDemoted. s2:lemEL is cited only as an alternative justification of arc/connector edge separation (not needed: (F-c) suffices).

**used_by:** s6:thmMIXC (O_K is the output of K-RED; cost line); s6:lemLent(iv); s7:propCost (cost table row K-RED); s7:lemGammaSat (epsK -> 0); s5:remConstants

**randomness:** None: deterministic given the stage-1 outcome and stage-3 outcomes in the good events. Stage-3 outcomes enter only through the existence of the child/demoted decompositions, so in Lean they can be quantified away (∃ D).

**lean_shape:**

```lean
noncomputable def Kstd (run : HB.Run V) (G : FGraph V) : Finset (Sym2 V) :=
  (Finset.Icc 1 run.R).biUnion (fun l => (run.Std G l).biUnion (fun a => run.E G l a))
def LentExtHyp (ω : Stage1 V) run G (Lext : LP → Finset (Sym2 V)) : Prop :=
  ∀ Y ∈ run.lightParts G,
    Lext Y ⊆ (ω.JSclasses run G Y ∪ ω.JVclasses run G Y) ∧ (demoted ω run G Y → Lext Y = ∅)
def LemKREDStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V),
    S5Hyp N0 Dstar G run →
    ∀ ω ∈ (stage1Law run G).supp, ∀ Lext : LP → Finset (Sym2 V), LentExtHyp ω run G Lext →
      ∃ D : List (Obj V),
        IsDecomp ↑(G.edges \ Kstd run G \ (run.lightParts G).biUnion Lext) D ∧
        (D.length : ℝ) ≤ (Dstar / 2 + 745 + epsChain Dstar) * G.card + 80 * (dem ω run G : ℝ) + 369 * (lp ω run G : ℝ)
-- optional sharper twin with 739 in place of 745 (the 'exact accounting')
```

**hazards:**

- **[risk] KRED-CAUSALITY.** The last assertion ('objects produced at round l depend only on stage-1/stage-3, on Lentext(Z) for round-l Z, and on rounds > l') and the 'for-all form' paragraph are what s6:thmMIXC(b) uses to identify step (2) of Construction s6:consOrder, run interleaved with TPV/JS-LC/J-consumer, with the output of K-RED for the FINAL Lentext family. A 'depends only on' clause has no direct Lean meaning. Options: (A) K-RED as pure existence (∀ admissible Lentext, ∃ D), and restructure the Lean MIX-C to first run the TPV/JS-LC/J-consumer recursion (which never reads K-RED's outputs: they use Erem(Z) of STANDALONE parts, LJS/LJV classes and J_l, all disjoint from U-classes and from light-part edge sets), obtain the final Lentext family, and apply K-RED once; (B) define K-RED's procedure as a function of (ω, stage 3, Lentext) by round recursion and prove a locality lemma. (A) is much cheaper and equally faithful for the Main Theorem, but it must be confirmed by the s6/s7 blueprints that no s6/s7 step at round l reads a K-RED output of rounds > l (s7:lemOneOutcome runs 'steps (1)-(3) of consOrder at round l' before drawing xi_l; the event of s7:consRound(f) must not depend on K-RED objects). Cross-chunk decision before the s6 Spec is written.
- **[risk] KRED-RECURSION.** The proof is a downward recursion: H_0(Z) at round l depends on the U-lent edges LentU_{l',c} chosen by lemParent at rounds l' >= l+2, which depend on the arcs chosen at those rounds. In Lean: strong downward induction on l (or recursion on R - l) carrying the state (set of used U-lent edges, list of objects, invariants: used U-edges lie in U-classes of good parents of rounds <= current-2, pairwise disjoint over (l,c), objects decompose exactly the processed edges). Needs: LentU(Z) final when Z is processed (lemParent at l' uses only parents of rounds <= l'-2), Own_Z ⊆ H_0(Z) (lent sets ⊆ Lend_Z disjoint from Own_Z), arcs from ChildExistsStatement, and the per-round counts. ~500 lines.
- **[note] KRED-EDGE-PARTITION.** Relies on propStructure(iii) as a Finset partition statement (pairwise disjoint pieces whose union is G.edges) with Kstd and the light-part pieces indexed by (round, address); and on Lentext(Y) ⊆ E_r(Y) (hypothesis + JS/JV classes ⊆ Lend_Y ⊆ E(X_Y) ⊆ E_r(Y)). The set to decompose is G.edges \ Kstd \ ⋃ Lentext; the proof's D-set equals ⊔ Cyc ⊔ E_0 ⊔ ⊔_Y (E_r(Y) \ Lentext(Y)).
- **[note] KRED-STAGE3-EXISTENTIAL.** The manuscript fixes stage-3 outcomes in all good events as hypotheses; in Lean these only provide existence of the child and demoted decompositions (ChildExistsStatement, DemotedExistsStatement), so the Spec can omit them (∃ D is as strong for every use: s6:thmMIXC needs only the edge set and the count of O_K).
- **[note] KRED-SUPPORT.** 'Fix a stage-1 outcome': quantify over ω in the support of stage1Law (STAGES-STAGE1-SUPPORT); for such ω the JS/JV/U classes of each Y partition Lend_Y and Own_Y is disjoint from them (s3 COL(g), holds for every well-formed ω).
- **[note] KRED-CONSTANTS.** Counts: long cycles sum_l |Cyc_l| <= n and |E_0| < D_* n/2 (propStructure(iii)); child 369(2n + lp) = 738n + 369 lp (eqPl); U-chaining epsChain n (lemParent(ii), summed over l >= 3); demoted 80 dem. 1 + 738 = 739 <= 745. Mixed ℝ/ℕ: cast dem, lp, D.length. Objects are Obj.edge for single edges (not loops: G simple) and Obj.cycle (length >= 3) for long cycles, child, VX+ and chaining cycles.
- **[note] KRED-LEL-UNUSED.** s2:lemEL is declared but only mentioned as an alternative reason why arc edges and connector edges differ; (F-c) (propStructure(iii)) already gives it. Do not add it as a Lean dependency.
- **[note] KRED-L-LE-2.** Rounds l <= 2: lemParent is not applied; correctness needs lemChild(d) (Rt(Z) = ∅ ⇒ no arcs), since Rt(Z) = ∅ for l <= 2 (no round <= l-2 >= 1 with 1-indexed rounds; write the condition as Y.1 + 2 <= l, s2a ANC-ROUND-OFFSET).

**effort:** ~900 Lean lines, difficulty 4/5 (edge partition bookkeeping ~200; downward recursion with invariants ~400; coverage/exactness ~150; cost ~150.)

### `s5:remConstants` — remark: the constants 369 and 745 (s5.tex:399)

- **Manuscript referee status:** --; (a) rewritten in v6 (R1): no referee yet
- **Formalization:** No Spec. (a) is internal to the proof of s4:lemPV (its Spec states the constant 369); (b) is a one-line numeric fact (norm_num) plus 0 <= other summands of eps1; (c) is dependency commentary. Optionally a sanity lemma in EGTest.

**Statement (precise restatement).** (a) c_PV = 369 >= 28*8 + 64 + 16 = 304: in the proof of s4:lemPV a vortex step j costs at most 4|W_j| + 12(2|Pl ∩ U_{j+1}| + 2|W_j|) <= 28|Pl ∩ U_j| objects (eq s4:eqPVstep, using Pl ∩ U_j = W_j ⊔ (Pl ∩ U_{j+1})); (G5) gives sum_j |Pl ∩ U_j| <= 8|Pl|, so all steps cost <= 224|Pl|; the finish costs <= 64|Pl| objects for the edges inside Pl ∩ U_J (Fact s1:factEG0(b) on <= 64|Pl|/L vertices) and <= 8|Pl ∩ U_J| <= 16|Pl| stripped single edges; total <= 304|Pl|; 369 kept (earlier accounting 44*8 + 16 + 1 = 369). (b) c_KRED = 745 exceeds the exact K-RED accounting 739 = 1 + 2*369 by 6, so 745 >= 1 + 2*369 + epsK(D_*) whenever epsK(D_*) <= 6, which holds under Gamma4 (eps1 <= 6 and eps1 contains epsK as a summand); this slack is not needed because K-RED carries epsK separately. (c) 369 and 745 depend on the hierarchy only through: one light part per vertex per round (propStructure(iv)); sum_Z |Pl(Z)| <= 2n + lp (propParentless(iii)); the overlap counts (1.37 n/P_r ancestors of round r, nu_l <= 2.74 n/P_{l-2}), which enter only epsU and epsChain; 80 is the constant of thmVXp; none depends on the Markov multiplier.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| c_PV = 369, c_VX = 80, c_KRED = 745, c_KRED^exact = 739 | absolute constants | preamble macros; s1:defConstants | no: numerals in Specs (no Def needed) |
| eps1, Gamma4 | s7:propCost, s1:condGamma | s7, s1 | no (s7 layer) |

**deps_declared** (manuscript \deps): s4:lemPV, s5:lemKRED, s2:propStructure, s2:propParentless, s2:propOV, s2:lemTower, s4:thmVXp, s1:condGamma, s1:factEG0

**deps_from_proof:** s4:lemPV, s1:factEG0, s5:lemKRED, s1:condGamma, s2:propStructure, s2:propParentless, s2:propOV, s2:lemTower, s4:thmVXp, s5:lemZones, s5:defStages, s5:lemParent

**deps_notes:** Undeclared references (ms_deps): s5:lemZones, s5:defStages, s5:lemParent (in (c)). (a) refers to internals of the proof of s4:lemPV (eq s4:eqPVstep, event (G5)), not to its statement.

**used_by:** s1:condGamma (Gamma4 pointer); s1 overview/cost line (commentary)

**randomness:** none

**lean_shape:**

```lean
-- no Spec; optional EGTest sanity checks
example : (28 * 8 + 64 + 16 : ℕ) ≤ 369 := by norm_num
example : (1 + 2 * 369 : ℕ) = 739 := by norm_num
example (eK : ℝ) (h : eK ≤ 6) : 1 + 2 * 369 + eK ≤ 745 := by linarith
```

**hazards:**

- **[risk] REM-A-UNREVIEWED.** (a) was rewritten in v6 (R1: Fact EG0 replaces B-M Theorem 2 in the finish) and has NO referee yet. It asserts the per-step re-accounting 4|W_j| + 12(2|Pl∩U_{j+1}| + 2|W_j|) <= 28|Pl∩U_j| and the finish bound 64|Pl| + 16|Pl|; if the s4:lemPV Lean proof cannot reach 369 (e.g. the finish via EG0 needs x(log2 x + 2) <= 64|Pl| with x <= 64|Pl|/L, i.e. log2 x + 2 <= L, fine for L >= 2^10), c_PV and hence 745 would change linearly. The s4 blueprint must re-derive it; nothing to formalize in s5.
- **[note] REM-B-EPS-NONNEG.** 'epsK <= 6 because Gamma4's left side contains epsK as a summand' needs every other summand of eps1 to be >= 0 (true under Gamma1: all logs positive, log* >= 0). Not needed by any Spec (K-RED carries epsK separately).
- **[note] REM-C-COMMENTARY.** (c) asserts independence of the constants from colour probabilities and from the Markov multiplier: meta-mathematical commentary with no Lean content.

**effort:** ~20 Lean lines, difficulty 1/5 (optional norm_num sanity checks only.)
