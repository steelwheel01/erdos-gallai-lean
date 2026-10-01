# P2-U formalization blueprint: chunk s1 (Introduction, conventions, cited inputs, constants)

Manuscript: `proofs/manuscript/s1.tex` (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s1.json` (same content, one object per label, same field names). Line numbers refer to `s1.tex`. Lean names in `code` that already exist were checked against `formal/EG/**`; all other names are proposals.

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s1:thmMain` | theorem | Tier-1 target: existing locked Spec EG.Spec.MainInternal | 120 | 2 | risk (MAIN-N0-HIDDEN) |
| `s1:remStatus` | remark | no mathematical content | 0 | 1 | note (STATUS-PRIORITY) |
| `s1:convGraphs` | convention | definitions | 250 | 2 | risk (CONV-MGRAPH) |
| `s1:defObject` | definition | existing Defs | 10 | 1 | note (OBJ-LOOPS) |
| `s1:factAdd` | fact | proved | 0 | 1 | note (ADD-LIB) |
| `s1:factEG0` | fact | Spec + proof | 700 | 3 | risk (EG0-UNREVIEWED) |
| `s1:citNotation` | cited result | no content beyond s1:convGraphs | 0 | 1 | note (NOT-B-M-DIFF) |
| `s1:citChernoff` | cited result | proved | 0 | 1 | note (CH-BINDEF) |
| `s1:citDef7` | cited result (definition) | existing Defs: EG.FGraph.IsPathConnected G ℓ t W | 0 | 1 | note (DEF7-REALT) |
| `s1:citProp8` | cited result | Spec + proof | 600 | 3 | risk (P8-PROOF-EXTERNAL) |
| `s1:citLem9` | cited result | not formalized | 0 | 1 | note (L9-NOLEAN) |
| `s1:citDef11` | cited result (definition) | existing Defs EG.FGraph.IsExpander | 0 | 1 | note (DEF11-EPS) |
| `s1:citProp12` | cited result | Spec + proof | 200 | 2 | note (P12-INCL) |
| `s1:citProp13` | cited result | not formalized | 0 | 1 | note (P13-ASYMP) |
| `s1:citLem14` | cited result | not formalized | 0 | 1 | note (L14-NOLEAN) |
| `s1:citLem15` | cited result | not formalized | 0 | 1 | note (L15-UNUSED) |
| `s1:citThm16` | cited result | not formalized | 0 | 1 | note (T16-WHP) |
| `s1:citLem17` | cited result | not formalized | 0 | 1 | note (L17-ASYMP) |
| `s1:citProp18` | cited result | not formalized | 0 | 1 | note (P18-THETA) |
| `s1:citLem19` | cited result | not formalized | 0 | 1 | note (L19-ASYMP) |
| `s1:citThm21` | cited result | Stage-α explicit Prop hypothesis | 40 | 2 | risk (LOV-TRUTH) |
| `s1:citCor22` | cited result | Spec + proof from the stage-α Lovász hypothesis | 700 | 3 | risk (C22-PROOF-EXTERNAL) |
| `s1:citLem25` | cited result | existing locked Spec EG.Spec.BMLemma25Statement | 1200 | 4 | risk (L25-CONST18) |
| `s1:remBMused` | remark | no mathematical content | 0 | 1 | note (BMUSED-LEANSET) |
| `s1:citChernoffGen` | cited result (with derivation) | proved | 0 | 1 | note (CHG-COND) |
| `s1:citMarkov` | cited result (with derivation) | proved | 0 | 1 | note (MARKOV-FIXED) |
| `s1:lemBBD` | lemma | Spec + proof | 850 | 3 | risk (BBD-TRANSPORT) |
| `s1:citHall` | cited result | Mathlib: Finset.all_card_le_biUnion_card_iff_exists_injective | 20 | 1 | note (HALL-TRUSTED) |
| `s1:citHaxell` | cited result (with derivation) | Stage-α explicit Prop hypothesis | 60 | 2 | risk (HAX-TRUTH) |
| `s1:citEuler` | cited result (with derivation) | (a) Lib theorem, stated for forests of an edge-indexed multigraph | 1300 | 4 | risk (EUL-MULTI-USE) |
| `s1:defConstants` | definition | Defs | 200 | 2 | risk (CONST-N0-INPROOF) |
| `s1:remOrder` | remark | no statement | 0 | 1 | note (ORDER-AUTO) |
| `s1:condGamma` | condition | Defs | 250 | 2 | risk (GAM-2BC) |
| `s1:remNotUsed` | remark | no content | 0 | 1 | note (NOTUSED-EXCLUDE) |

Estimated new Lean for this chunk: **~6500 lines** (P2/P3 scope; excludes the stage-β discharges of Lovász ~2000-4000, Haxell ~1500-2500 and (if not landed in Mathlib) Euler for simple graphs ~800, and excludes the proof of the Main Theorem itself). Already done in P1b (0 new lines): s1:defObject, s1:factAdd, s1:citChernoff, s1:citChernoffGen, s1:citMarkov, s1:citDef7, s1:citDef11 (+ remark); Spec exists, proof `sorry`: s1:citLem25.

No blocker was found in s1: every hazard below can be resolved by a Lean-side decision (listed in §2) without changing the manuscript. The risks that most affect other chunks are MAIN-GAMMA2BC/GAM-2BC (Γ2(b),(c) are lemmas, not conditions), CONST-N0-INPROOF (N0 is defined by size conditions hidden in s4 proofs), CONST-LAYERING/GAM-1F-FORWARD/GAM-4-FORWARD (forward definitional dependencies of the constants), EUL-MULTI-USE (Euler/T-join used on multigraphs), HAX-TRUTH/LOV-TRUTH/EUL-STAGEALPHA (stage-α hypotheses must be exactly true), and L25-CONST18 (thin margin of s2:lemCap on the constant 18).

## 2. Cross-cutting decisions proposed for the integrator

- **Formalization classes of the cited results.** Lean proofs needed: s1:factEG0 (new, R1), s1:citProp8, s1:citProp12, s1:citLem25 (Spec exists), s1:citCor22 (from Lovász), s1:lemBBD, s1:citEuler(a) (forest T-join) and the multigraph Euler derivation. Stage-α hypotheses (explicit locked Props, PLAN §1): s1:citThm21 (Lovász), s1:citHaxell, s1:citEuler(b) (Euler for simple graphs). Mathlib directly: s1:citHall. Not formalized (proof-structure citations whose content is re-proved in s2/s3): s1:citLem9, s1:citProp13, s1:citLem14, s1:citLem17, s1:citProp18, s1:citLem19. Not used: s1:citLem15, s1:citThm16, s1:citEuler(c). No content: s1:remStatus, s1:citNotation, s1:remBMused, s1:remOrder, s1:remNotUsed. Blueprint tooling (checkdecls/msreport) must accept nodes without a Lean declaration for these classes.
- **Stage-α hypotheses in their weakest sufficient true form.** Haxell: lock the d²-form (nonempty A', |Z| < d²|A'|), which follows from every published variant and suffices for s3:lemL9rho; avoid ℕ-subtraction at A' = ∅. Lovász: simple FGraph, ⌊n/2⌋ with n = |V| (isolated vertices counted). Euler: Mathlib SimpleGraph, all degrees even, positive-degree vertices mutually reachable ⇒ Eulerian circuit; derive the multigraph-with-loops version by subdivision. Each must be checked against its source before locking; a false stage-α Prop makes the stage-α theorem vacuous.
- **New Defs** (with approval): `EG.logIter`, `EG.logStar` (reals); move `EG.Obj.isEdge` from Lib to `EG/Defs/Objects.lean`; `EG.IsPathDecomp`, `EG.pathEndCount`, `EG.IsPathCycleDecomp`; `EG.FGraph.nbrSetDeg` (N_{G,d}(U), shared with s3:propP13s); `EG.MGraph` with loop-degree 2, components, forests, closed trails (prerequisite for s5/s7 Specs); `EG/Defs/Constants.lean` (ε, σ, C', A).
- **Constants and layering.** Split: `Gamma1Items`/`Gamma1core` (items (a)-(e)) early; Γ1(f) (COL-JV column 3) in the s3 layer; `N0Cond` after the s4 size predicates; `Gamma4`, `GammaCond`, `C0`, `cEG` after the s7 ε-functions. Γ2(b),(c) are lemmas, never fields of `GammaCond`. s2-s6 statements take only the Γ items they cite (never `GammaCond`). s4 statements take explicit size predicates at N = |Z| (`EG.S4.TPVSize Z.card` etc.), which the s4 blueprint must extract from the proofs (size conditions (i)-(iv) and η_TPV, η_PV, η_VX).
- **Main Theorem.** Keep `EG.Spec.MainInternal` (existence of c) as the only Tier-1 statement; optionally add an unlocked `MainExplicit` (c_EG = max(C0/(1-2θ_Q), N0/2)) as a fidelity check. Prove eps1 D ≥ 0, eps2 D ≥ 0 from Γ1 (needed by `EG.Spec.HIStatement`).
- **Probability.** BBD is stated on `FinDist.pi` of Bernoulli coordinates over a Fintype index, with a transport corollary for laws `μ.map I = pi bernoulli` and a restriction lemma for ρ-random subsets (needed by s3:lemL17s case (b)).

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| risk | `s1:thmMain` | MAIN-N0-HIDDEN | N0-admissibility refers to size thresholds that exist only inside the PROOFS of s4:lemTPV/lemPV/thmVXp ('size conditions (i)-(iv)', with the explicit o(1) functions eta_TPV, eta_PV, eta_VX). An explicit Lean statement needs them as named Defs; the s4 blueprint must export them (or state s4 lemmas with a ∀ᶠ N threshold). |
| risk | `s1:thmMain` | MAIN-GAMMA2BC | (Gamma2)(b),(c) are NOT predicates of D_* (they quantify over rounds of runs and over failure probabilities of s3:lemCOL/s5:lemE1). Any explicit Lean statement must assume only Gamma1 ∧ Gamma2a ∧ Gamma3 ∧ Gamma4; (b),(c) must be lemmas (s2:lemTower(b), s3:lemCOL, s5:lemE1). |
| risk | `s1:convGraphs` | CONV-MGRAPH | Multigraphs with loops (s5 UQ_{l,c,i}, s7 B_kappa) have no Defs type yet; s1:citEuler(a),(b) are applied to them (s5:lemParent Step 3). EG.MGraph (with loop-degree 2, components, spanning forests, closed trails) must be designed and locked before the s5/s7 Specs. |
| risk | `s1:factEG0` | EG0-UNREVIEWED | New in v6 (R1), no clean-room review. I re-derived (a) and (b): the claim (m' <= (h-1)(d-1) <= (h-1)m'/h < m'), (1-1/h)^h <= 1/2 (via (1-x^2)^h <= 1 and (1+x)^h >= 2), t <= (q+1)h <= h log h, and h <= N/4 => log h <= L-2 are all correct. The residual risk is in the s4 consumers (the per-step re-accounting 84\|P\|, 28 per step that keeps 169/369/80 unchanged), not in EG0 itself. |
| risk | `s1:citProp8` | P8-PROOF-EXTERNAL | The manuscript cites Prop 8 as a black box; the Lean proof must be reconstructed from B-M (papers/2211.07689.txt l.393-424). Hidden work: walk concatenation through a meeting vertex z ∈ V and shortcutting while keeping 'interior in V' (x or y may reappear inside the other half), the x/y WLOG symmetry, the maximal-r argument with the real bound t(2/3)^r (finiteness of feasible r), r <= 2 log t (uses log_{3/2} <= 2 log), and floors of the real radius 2 ell log n. I checked the argument: it is correct. |
| risk | `s1:citThm21` | LOV-TRUTH | A stage-α hypothesis is TRUSTED: if the Lean LovaszStatement were false (e.g. stated for multigraphs, where a double edge on 2 vertices needs 2 > 1 paths, or with loops allowed, or with n counting only non-isolated vertices in the wrong direction), the stage-α theorem would be vacuous. State it for FGraph (simple, loopless) with n = \|V(H)\| including isolated vertices, exactly Lovász's ⌊n/2⌋; have it reviewed against the paper before locking. |
| risk | `s1:citCor22` | C22-PROOF-EXTERNAL | The manuscript gives only a one-line sketch; the Lean proof must reconstruct B-M's parity/counting argument: exact integer bound ⌊(n+1)/2⌋ from Lovász, 'odd degree ⇒ end of an odd number of paths' (parity of path ends), no cycles, then list surgery when deleting v0 (a path with v0 interior splits into two, v0 an end shortens it, a path v0-v becomes trivial and must be dropped). Moderate but fiddly. |
| risk | `s1:citLem25` | L25-CONST18 | The explicit constant 18 is read off B-M's sketch, and s2:lemCap has a razor-thin numeric margin built on it (18432 = 18·2^10 at eps = 2^-5; cap_const: 18432·1.37317^4 ≈ 65535.9 <= 2^16 = 65536). If the Lean proof only reaches a worse constant, lemCap and M_l := max(2^40, 2^16 t d log^4(t d)) break. I re-derived the rounding B-M skip: a := eps^2 m/(18 log^4 m) >= 23 (since eps^2 m >= 2^30 and log m <= log(eps^2 m) + 10), so \|Y\| := ⌈a⌉ < 2a; non-vacuity of the expander forces eps <= log^2 m, so \|Y\| <= \|P\|/6 + 1 and X, Z with \|X\|,\|Z\| >= \|P\|/3 exist once \|P\| >= 12. The constant 18 survives, but the Lean proof must do this arithmetic explicitly. |
| risk | `s1:citLem25` | L25-DFS | DFS must be formalized as an invariant-preserving relation on (U, P, R) (PLAN: 'as an invariant relation'), with a discrete intermediate-value step for \|U\| = \|R\|; plus connectivity from expansion and the shortest X-Z path whose interior avoids P. ~1000+ lines. |
| risk | `s1:lemBBD` | BBD-TRANSPORT | The consumer (s3:lemL17s case (b)) does not have a product space on {0,1}^\|W\|: it has a p_*-random subset V_i (IsRSubset) inside a union of independent layers, conditioned on the earlier layers. The Lean use needs (i) the restriction lemma 'indicators of a ρ-random subset on W ⊆ S have the product Bernoulli law' (not in Lib: only IsRSubset.indepEvents exists), and (ii) Fubini over the layers. Budget these in s3; state BBD for an arbitrary Fintype index and prove the transport corollary here. |
| risk | `s1:citHaxell` | HAX-TRUTH | Stage-α hypotheses are trusted. The manuscript itself says the factor 2d-1 (and whether edges meet B in 'at most' or 'exactly' d vertices) has NOT been checked against [Hax95]. A false locked HaxellStatement would make every stage-α result vacuous. Mitigation (recommended): lock the d²-form above, which is implied by the standard statement (Haxell 1995: \|e ∩ B\| <= r-1, bound (2r-3)(\|A'\|-1)) and by any variant with factor <= d², and still suffices for s3:lemL9rho; and check the paper before stage β. |
| risk | `s1:citHaxell` | HAX-NATSUB | With ℕ subtraction, (2d-1)(\|A'\|-1) = 0 for A' = ∅, which would demand an edge with e ∩ A ⊆ ∅: the hypothesis becomes unsatisfiable, the Prop vacuously true and useless. Quantify over A'.Nonempty (as above) or work in ℤ. |
| risk | `s1:citEuler` | EUL-MULTI-USE | Definition-vs-use mismatch: (a) and (b) are stated for (simple) connected graphs, but s5:lemParent applies them to the multigraph UQ_{l,c,i} with loops and parallel edges (a T-join inside a spanning FOREST, with the size bound \|T_i\| <= nu_l - 1, then Euler circuits of multigraph components, including a single loop, k = 1). The mathematics is fine (a forest of a multigraph is a simple forest; Euler holds for multigraphs with loops), but the Lean statements must be for edge-indexed multigraphs/forests; FGraph cannot express UQ. Requires EG.MGraph first. |
| risk | `s1:citEuler` | EUL-STAGEALPHA | PLAN lists Euler as a stage-α hypothesis. Decide its form before locking: for Mathlib SimpleGraph (small trusted statement, matches pending Mathlib PRs #41524/#41631, but then the multigraph-with-loops version needs a ~800-line subdivision derivation) or directly for multigraphs (larger trusted surface, easier to get wrong). A mis-stated stage-α Euler Prop (e.g. requiring Connected on all vertices while isolated vertices exist, or allowing zero-edge graphs incorrectly) is either false (vacuous theorem) or unusable. Recommendation: SimpleGraph form with connectivity only among positive-degree vertices, as above. |
| risk | `s1:citEuler` | EUL-EMPTY | Concrete trap for the stage-α Euler Prop: the natural shape '(all degrees even) → (edges connected) → ∃ (u : V) (w : G.Walk u u), w.IsEulerian' is FALSE when V is empty (hypotheses vacuous, no u exists), so locking it would make the stage-α theorem vacuous. Quantify the start vertex (∀ u with 0 < deg u, ∃ Eulerian closed walk at u) or assume [Nonempty V]. Every stage-α Prop needs such a degenerate-case audit (empty vertex set, no edges, d = 1, A = ∅) plus a non-vacuity test in EGTest. |
| risk | `s1:defConstants` | CONST-N0-INPROOF | (ii) defines N0 through thresholds that are listed only inside the PROOFS of three s4 lemmas ('size conditions', including the o(1) functions eta_TPV/eta_PV/eta_VX defined in those proofs). A Lean definition of N0Cond needs these as named explicit Defs, so the s4 statements must expose them (hypothesis 'TPVSize \|Z\|') -- a statement-shape decision for the s4 blueprint. Alternative: s4 Specs with an existential threshold (∀ᶠ N in atTop), which makes N0 non-explicit but equally faithful. |
| risk | `s1:defConstants` | CONST-LAYERING | Forward definitional dependencies: N0Cond needs s4 Defs; (iii)/(iv)/(v)/(vi) need s3 (COL-JV column 3), s5 (epsU, epsK), s6 (epsCONC), s7 (epsX, F, eps1, eps2). Lean modules cannot reference later modules, so constants must be split: absolute constants early (Defs/Constants), N0Cond after s4, GammaCond/C0/cEG after s7. Statements of s2-s6 must NOT take GammaCond (would import s7); they take only the items they use (Gamma1core, Gamma2a, Gamma3, N0Cond). |
| risk | `s1:condGamma` | GAM-2BC | (Gamma2)(b),(c) are listed as conditions on D_* but are not predicates of D_*: (b) quantifies over the rounds of a run (M_l, P_l, R), (c) over failure probabilities of s3:lemCOL and s5:lemE1. They must be formalized as LEMMAS (s2:lemTower(b), s3:lemCOL, s5:lemE1(b),(c)), never as fields of GammaCond; otherwise GammaCond would depend on the s3/s5 probability spaces (module cycle) and s7:lemGammaSat would have to prove probabilistic statements. The manuscript confirms no proof uses (b),(c) as hypotheses. |
| risk | `s1:condGamma` | GAM-1F-FORWARD | (Gamma1)(f) is a forward pointer to 18 inequalities of s3:tabCOLJV. Split Gamma1 into Gamma1core (items (a)-(e), defined early, usable by s2) and the (f) part (s3 layer). Each s2 statement citing Gamma1 must be checked to use only (a)-(e) (s2:propDegRec, s2:lemLacunary, s2:lemTower, s2:propStructure). |
| risk | `s1:condGamma` | GAM-4-FORWARD | (Gamma4) depends on eps1, eps2, which collect explicit functions from s2 (epsA), s5 (epsU, epsK), s6 (epsCONC, needs log*), s7 (epsX, F with real exponent -90.2); these must be Defs with exactly the s7 formulas (s7.tex:1072, 1239). The bullet list in the condition (coefficients 169/12, 3/12, 291.9/D, 363.6/D) is only a summary and must not be used as the definition. |
| note | `s1:thmMain` | MAIN-EXISTENTIAL | The locked target MainInternal only asserts existence of c (CONVENTIONS). The explicit c_EG, and the constants 1085/1091, are machine-checked only if MainExplicit is also stated and proved; its lock closure would contain every s2/s4/s5/s6/s7 constant definition (eps-functions, size predicates, COL-JV column 3). Recommendation: keep MainExplicit unlocked (Tier-2). |
| note | `s1:thmMain` | MAIN-NONNEG | EG.Spec.HIStatement needs D/2 ≤ C0 and 0 ≤ theta_Q, i.e. eps1 D ≥ 0 and eps2 D ≥ 0. In Lean logb of numbers ≤ 1 is ≤ 0 (and logb of negatives is logb \|x\|), so these hold only under Gamma1 (log2 log2 D ≥ 2^8); prove them as lemmas from Gamma1core, do not assume them. |
| note | `s1:thmMain` | MAIN-CEIL | c_EG is real; MainInternal needs c : ℕ: use ⌈c_EG⌉₊ (already done in EG/Proof/Quot/HIMain.lean). |
| note | `s1:remStatus` | STATUS-PRIORITY | Parts written for v6 and not yet clean-room reviewed should be probed first in Lean: s1:factEG0 (R1) and the s4 per-step re-accounting, s1:lemBBD + s3:lemL17s case (b) (R2), s1:citHaxell + new claim/final step of s3:lemL9rho (R3), s3:lemHB via Hall (R4), finite probability spaces of s4 (R5), eventualities s1:condGamma/s3:lemCOLJV/s7:lemGammaSat (R6), integration corrections (citDef11 eps>0, citLem25 m>=2, EG0(b) simple, s3:lemCOLJV(ii) at every mu). |
| note | `s1:remStatus` | STATUS-REFUTE | Refutation targets (v)(3) (lifted cycle repeating a vertex) and (v)(4) (an edge covered twice) are excluded by construction in Lean (Obj.WF = Nodup, IsDecomp = Nodup of the concatenated edge lists), so the formalization tests them automatically; (v)(1),(2),(5) are quantitative and are tested by s6:thmCONCL(iv), s6:lemJSLC and the s7 cost lemmas. |
| note | `s1:remStatus` | STATUS-HOTSPOTS | (iv)(a)-(d) name the most likely error sites (JS-LC routing engine s6; Lemma 14^tau + CONC-L(iv); JV+* composition s7; the CR1-PV sites where a per-vertex multiplicity feeds a path-connectivity parameter t). Use for P2 probe ordering. |
| note | `s1:convGraphs` | CONV-LOGSTAR | log* is not defined in EG/Defs; needed by epsCONC (s6:thmCONCL(iv), hence Gamma4), s2:lemTower(a),(d) (R - r <= 2 log* d_r + 2 <= log lambda_r) and the tower facts. Define on reals via Nat.find; requires a small termination lemma. |
| note | `s1:convGraphs` | CONV-LOGJUNK | Real.logb 2 is total: logb 2 x ≤ 0 for x ≤ 1 and logb 2 (-x) = logb 2 x. Iterates beyond log* are junk; no lemma may use log^[k] x for k > log* x. Every 'log log D' needs D > 2 to be positive (Gamma1 assumes D > 2). |
| note | `s1:convGraphs` | CONV-LOGPOW | 'log^k x' = (log_2 x)^k (Lean: Real.logb 2 x ^ k), 'log^[k] x' = iterate, 'log log x' = logb 2 (logb 2 x), '(log D)^{1/2}' = rpow or Real.sqrt. Statement reviewers must check each translation (easy to write logb 2 (x^k)). |
| note | `s1:convGraphs` | CONV-FIN | [k] = {1..k} vs Lean Fin k = {0..k-1} (colours, indices, [2t-1] in s1:citProp8): state with Fin and shift indices in docstrings. |
| note | `s1:convGraphs` | CONV-BALLRADIUS | Ball radii are ℕ in EG.ball; B-M radii such as log^4 n are real: use ⌊r⌋₊ (CONVENTIONS). In the manuscript's own statements the radius ell_* = ⌊2^10 L^3⌋ is already an integer. |
| note | `s1:convGraphs` | CONV-TRIVIALPATH | EG.IsPathIn allows the one-vertex path [v] for any v (also v ∉ V(H)) and ball H i U W ⊇ U ∩ W: statements must keep the manuscript's inclusions U, W ⊆ V(H) (CONVENTIONS). |
| note | `s1:convGraphs` | CONV-LOCALG | 'G always denotes the input graph, n := \|V(G)\|' is overridden inside cited results (s1:citProp8, citLem9, citDef11, citLem25, ...), where G, n are arbitrary; in Lean all are bound variables, so reviewers must not import n = \|V(G_input)\| into those statements. |
| note | `s1:convGraphs` | CONV-EAB | E_H(A,B) is defined in Lean for all A,B but meant for disjoint A,B only (CONVENTIONS). |
| note | `s1:defObject` | OBJ-LOOPS | EG.fnum ignores loops (T0 encoding); apply only to loopless sets (H.edges, G.edgeFinset) or add ∀ e ∈ F, ¬ e.IsDiag; 'F decomposes' for a raw F is IsDecomp + looplessness (CONVENTIONS). |
| note | `s1:defObject` | OBJ-MULTI | Obj cannot represent 2-cycles or loops: decompositions are only ever taken of edge sets of the simple input graph G or of the simple quotients Q_l; multigraph edges (s5 UQ, s7 B_kappa) are lifted before decomposing. Any Spec that would 'decompose' a multigraph edge set is a modelling error. |
| note | `s1:defObject` | OBJ-ISEDGE | Counting single edges (s1:factEG0 'at most h-1 / \|W\| single edges', s4:thmVXp) needs Obj.isEdge in Defs; it is currently Lib (EG/Lib/Found/Fnum.lean, @[expose]). Move it (two lines) through the approval procedure, or inline the match in the Spec. |
| note | `s1:factAdd` | ADD-LIB | Proved as Lib lemmas, not locked Specs; downstream Specs never need to state them. Nothing open. |
| note | `s1:factEG0` | EG0-LOOP | T0-eg0-loop (recorded; integrated in v6): (b) needs ∀ e ∈ F, ¬ e.IsDiag (a raw Finset (Sym2 V) cannot have parallel edges, so only loops matter). |
| note | `s1:factEG0` | EG0-ISEDGE | The single-edge counts are load-bearing for s4:thmVXp ('N + o(N) single edges', RT2-I13): the Spec must include them, so Obj.isEdge must be a Defs definition (see s1:defObject). |
| note | `s1:factEG0` | EG0-LONGESTPATH | The claim needs (i) the k-core by iterated deletion (well-founded peeling; Mathlib has no k-core for SimpleGraph in this form) and (ii) existence of a longest path in a finite graph (maximum over a finite set of Nodup lists). Both are routine but not in Lib; with FGraph they are best done via FGraph.toSimpleGraph + Mathlib walks, or directly on lists. |
| note | `s1:factEG0` | EG0-REAL | Bounds are real (h (log_2 h + 1), beta alpha); m <= h^2/2 needs 2\|E\| <= h(h-1) (exists as FGraph.two_mul_card_edges_le in EG/Proof/Quot/HI.lean -- move to Lib). |
| note | `s1:citNotation` | NOT-B-M-DIFF | No semantic difference from s1:convGraphs; the only B-M/Lean gap is the real ball radius (floor). |
| note | `s1:citChernoff` | CH-BINDEF | FinDist.binomial is a Lib definition; keep 'X ~ Bin' out of locked Specs (consumers use it inside proofs), or move it to Defs with approval. |
| note | `s1:citChernoff` | CH-USEFORM | Consumers apply it to sizes of ρ-random sets, conditionally on earlier independent layers (fixed prefix, compProd). The Lib covers the unconditional random-set forms; conditional use needs the Fubini/cond lemmas of EG/Lib/Prob/Basic.lean (exist: prob_compProd, cond_prod_fst). |
| note | `s1:citDef7` | DEF7-REALT | t is real (s4 uses t = 2^9 L^8 etc.); the property depends only on ⌊t⌋₊ and is trivial for t < 1; integer multiplicities are passed as (k : ℝ). |
| note | `s1:citDef7` | DEF7-ORDERED | Pairs are ordered in Lean (V × V); harmless by path reversal. The multiset clause (RT2-I14) is built in (indices = occurrences). |
| note | `s1:citProp8` | P8-UNUSEDHYP | The hypothesis ell <= n is not used by the proof; keep it for faithfulness (s3:lemL9rho verifies 1 <= ell_* <= 2^10 L^3 <= n). |
| note | `s1:citProp8` | P8-GF | Applied to G - F (FGraph.deleteEdges; same vertex set and n), with the ball hypothesis for U ⊆ V(G) of size t0 only. |
| note | `s1:citLem9` | L9-NOLEAN | Blueprint/checkdecls tooling: this node has no Lean declaration; mark it 'cited, not formalized (proof structure only)' so msreport/checkdecls do not demand one. The multiset counting step it justifies is re-proved inside s3:lemL9rho. |
| note | `s1:citDef11` | DEF11-EPS | T0-def11-eps resolved in v6 (remark assumes eps > 0). Lean lemmas already require 0 < ε and 2 ≤ \|G\|. |
| note | `s1:citDef11` | DEF11-N | n is the expander's own vertex count (for spanning expanders on a part Z, n = \|Z\|), so log^2 n differs between G and its parts; Specs must use O.card of the relevant graph. |
| note | `s1:citProp12` | P12-INCL | B-M leave U ⊆ V(G) and F ⊆ E(G) implicit; the Spec must include them (CONVENTIONS: keep inclusion hypotheses). |
| note | `s1:citProp12` | P12-DREAL | d is real in B-M, integer d_* in the only use; the hypothesis d <= s is not used by the proof (keep it). |
| note | `s1:citProp12` | P12-NEWDEF | N_{G,d}(U) is a new definition shared with s3:propP13s; define once in Defs (Graph.lean) so both Specs use the same constant. |
| note | `s1:citProp13` | P13-ASYMP | Asymptotic ('there is n0') with non-integer star/leaf counts (log^7 n, log^9 n); do not formalize. s3:propP13s is the explicit replacement. Mark the blueprint node as not formalized. |
| note | `s1:citLem14` | L14-NOLEAN | No Lean theorem needed: every s2 use is 'this recursion is the one of B-M' plus a full re-proof (s2:lemOVgeneric counting with 1/(1-3.42 eps)). Mark as not formalized. |
| note | `s1:citLem14` | L14-INEQ9 | The quoted derivation of (9) via log n1 < log n - 2/5 only yields (9) for log n > 1.09 (8L^2 > (2+L)^2); at n = 2 inequality (9) still holds by direct evaluation. Irrelevant for Lean (not formalized) but do not reuse the quoted chain verbatim. |
| note | `s1:citLem15` | L15-UNUSED | Must not appear in any \uses edge (remBMused: not a dependency). |
| note | `s1:citThm16` | T16-WHP | 'with high probability' has no explicit error bound; not formalizable as stated and not needed. |
| note | `s1:citLem17` | L17-ASYMP | Asymptotic error e^{-Ω(·)}; not formalized. s3:lemL17s is the explicit version (exp(-7\|U\|L)). |
| note | `s1:citProp18` | P18-THETA | B-M's statement is slightly wrong for non-integer theta (needs s >= theta + 1); already corrected in s3:lemP18s. Do not formalize the B-M form. |
| note | `s1:citLem19` | L19-ASYMP | Asymptotic; not formalized. s3:lemP18s(ii) gives the explicit 1 - n^-6. |
| note | `s1:citThm21` | LOV-UNIV | The Cor 22 proof applies Lovász to G + v0 on Option V; if LovaszStatement is at universe Type, Cor22 and all consumers must stay in Type (consistent with MainInternal, V : Type). |
| note | `s1:citThm21` | LOV-BETA | Stage β/γ discharge (Lovász's proof) is a large separate task (~2000-4000 lines, difficulty 5); outside P2. |
| note | `s1:citCor22` | C22-DEPS | The manuscript's deps line says 'none (published)', but any Lean proof depends on Lovász (s1:citThm21) -> the stage-α hypothesis enters the s4 lemmas through Cor 22. Record the edge s1:citCor22 -> s1:citThm21 in the blueprint. |
| note | `s1:citCor22` | C22-SIMPLE | Only for simple graphs (s4 says so); all s4 applications decompose edge sets of G. Loops must be excluded in the Spec (∀ e ∈ F, ¬ e.IsDiag). |
| note | `s1:citCor22` | C22-TRIVIAL | Paths must be non-trivial (>= 1 edge) for 'two distinct ends in W' and the \|W\| bound; IsPathDecomp requires length >= 2 vertices. |
| note | `s1:citLem25` | L25-M2 | T0-cap-1 (m >= 2) is integrated in v6 and in the locked Spec; EG.bmLemma25_literal_false documents the m = 1 counterexample. |
| note | `s1:remBMused` | BMUSED-LEANSET | Consequence for Lean: the only B-M results needing Lean proofs are Prop 8, Prop 12, Lemma 25 and Cor 22 (+ Lovász as stage-α hypothesis); Defs 7 and 11 and Theorem 4 exist; Lemma 9, Props 13/18, Lemmas 14/17/19 are proof-structure citations only; Lemma 15, Theorem 16 unused. |
| note | `s1:citChernoffGen` | CHG-COND | All uses are conditional on a fixed prefix (earlier layers / fixed past); the Lib lemmas are stated for an arbitrary FinDist, so consumers instantiate them at the conditional/kernel distribution (compProd second stage) -- consumers must build that distribution explicitly. |
| note | `s1:citMarkov` | MARKOV-FIXED | 'Given a fixed outcome' is a slice of a product (no σ-algebras), consistent with the outline and s7:defSchedule; Past_l is a fixed value, not a random object (RT2-J5). Consumers in s7 must model the round-l randomness xi_l as a fresh FinDist parametrised by the past. |
| note | `s1:lemBBD` | BBD-UNREVIEWED | New in v6 (R2), no clean-room review. I re-checked all steps: the identity Ψ_{k-1} = pΨ_k(·,1) + (1-p)Ψ_k(·,0), \|Ξ_k\| <= c_k, χ'' = (1-(1-u)e^u)/3, the division by 1-u/3 >= 1-ζ/3 > 0, the one-coordinate bound (cross terms cancel, p(1-p)^2 + (1-p)p^2 = p(1-p)), and the optimisation η = a/(β+ba/3) giving -a²/(2(β+ba/3)). Correct; m = 0 and a = 0 are fine. |
| note | `s1:lemBBD` | BBD-COORDS | The manuscript inducts over the ordered coordinates 1..m (prefix sums over {0,1}^k); over a general Fintype ι use Fintype.equivFin or Finset induction on the set of revealed coordinates. 'Differ only in coordinate k' ↔ Function.update form (equivalent). |
| note | `s1:lemBBD` | BBD-CALC | The analytic part needs 'derivative >= 0 on an interval ⇒ monotone' (Mathlib: monotoneOn_of_deriv_nonneg) and exp facts; no martingales. Choice b >= 0 matters only when some c_k = 0 for all k (then b could be negative otherwise); keep the hypothesis 0 <= b. |
| note | `s1:citHall` | HALL-TRUSTED | Mathlib theorem: no trust issue and no Spec. Both directions are available (iff), which the s7 contrapositive use needs. |
| note | `s1:citHaxell` | HAX-HYPERGRAPH | Hypergraph = Finset (Finset α): distinct paths with the same edge set give one hyperedge (harmless: the matching picks one path per index). The application's vertex type is ι ⊕ Sym2 V with A := image inl, B := image inr of E(G). |
| note | `s1:citHaxell` | HAX-PADDING | The padding derivation (\|e∩B\| = d ⇒ <= d) is only needed if the locked form uses '= d'; with the '<= d' form it is unnecessary. |
| note | `s1:citHaxell` | HAX-BETA | Stage β discharge (Haxell's alternating-tree proof) ~1500-2500 lines, difficulty 4-5; outside P2. |
| note | `s1:citEuler` | EUL-TREE | Spanning trees/forests: Mathlib has trees for SimpleGraph but not for edge-indexed multigraphs; the forest version of (a) is simplest by induction on edges (remove a leaf edge) rather than via rooted subtrees as in the text. |
| note | `s1:citEuler` | EUL-C-UNUSED | (c) is used nowhere by label; do not formalize (saves ~300 lines). Its directed part would allow 2-cycles for general digraphs; not an issue since unused. |
| note | `s1:defConstants` | CONST-NONNEG | (v) C0 >= D_*/2 (used in s7:thmMainProof and HI) needs eps1(D) >= 0; theta_Q >= 0 is needed by HI. Both require D large (log log D > 0 etc.): prove from Gamma1core. |
| note | `s1:defConstants` | CONST-REALN0 | N0 as a real (EG.Spec.HIHyp uses N₀ : ℝ); 'n >= N0' is (n : ℝ) ≥ N0. The claim 'N0 depends only on sigma, C', A' has no Lean content (existential choice). |
| note | `s1:defConstants` | CONST-EXPLICIT | (vii): every named small quantity must have an explicit formula; checked: epsU (s5.tex:140), epsChain (s5.tex:227), eps2 (s7.tex:1072), eps1 (s7.tex:1239) are explicit. The Gamma4 bullet list in s1:condGamma is descriptive only; Lean must use the s7 formulas. |
| note | `s1:remOrder` | ORDER-AUTO | Lean term structure enforces the order automatically if eps1/eps2 are functions of D only and c_EG appears only in HI; the statement reviewers should check that no s2-s7 Spec takes c_EG (or C0/theta_Q as free parameters with conditions depending on G). |
| note | `s1:condGamma` | GAM-NUMERICS | Never evaluate: (e) has (105 mu)^4830 and (a) forces D_* >= 2^{2^256}; all uses must be symbolic/eventual (CONVENTIONS: no norm_num on galactic constants, no native_decide). The eventuality proofs are s7:lemGammaSat and s3:lemCOLJVev. |
| note | `s1:condGamma` | GAM-RAY | Gamma1 is a condition on the whole real ray mu >= log2 log2 D (upward closed in D). In Lean logb is total; keep 2 < D so log2 log2 D > 0, and prove the transfer lemmas (mu = log2 lambda_r >= log2 log2 D_* from d_r >= D_*; t >= log2 t for t > 0). |
| note | `s1:condGamma` | GAM-ORDER | Gamma3 involves N0: GammaCond N0 D, quantified ∀ N0, ∀ᶠ D (N0 chosen first); no condition involves c_EG. |
| note | `s1:condGamma` | GAM-UNREVIEWED | Rewritten in v6 (R6) and (R7), no clean-room review; the logic (eventualities, non-circularity) checks out, but its correctness depends on s3:lemCOLJVev and s7:lemGammaSat. |
| note | `s1:remNotUsed` | NOTUSED-EXCLUDE | The usesgen/blueprint must create no nodes for these items, and conditions (G), (G+), (G_XL) must never be assumed; HALL/HALL' must not be confused with s1:citHall (Mathlib Hall). VX-parts: V = ∅ throughout, so s6/s7 Specs need no VX-part case. |

## 4. Nodes

### `s1:thmMain` — theorem: Main Theorem (candidate) (s1.tex:80)

- **Manuscript referee status:** composition x2 (JV+* referees); this text x0
- **Formalization:** Tier-1 target: existing locked Spec EG.Spec.MainInternal (existence of c only); optional unlocked explicit-constant form MainExplicit

**Statement (precise restatement).** Fix eps = 2^-5, sigma = 100, C' = 103, A = 105 (s1:defConstants(i)). FOR EVERY number N0 satisfying s1:defConstants(ii) [N0 >= 2^40 and every size condition of the proofs of s4:lemTPV, s4:lemPV, s4:thmVXp holds at every N >= N0] and FOR EVERY real D_* satisfying (Gamma1), (Gamma2)(a), (Gamma3) [w.r.t. this N0] and (Gamma4) of s1:condGamma ((Gamma2)(b),(c) are consequences, not conditions), put C0 := D_*/2 + 1085 + eps1(D_*), theta_Q := eps2(D_*) (eps1, eps2 the explicit functions of s7:propCost and s7:lemUHsplit), c_EG := max{ C0/(1 - 2 theta_Q), N0/2 }. Then FOR EVERY n in N and EVERY finite simple graph G with |V(G)| = n: f(G) <= c_EG * n. In particular f(n) = O(n), i.e. EXISTS c, FOR ALL n, f(n) <= c n. Quantifier order: the constants are universally quantified over admissible values and fixed BEFORE G; c_EG depends only on (N0, D_*). Existence of admissible N0 is 'finitely many eventualities in N'; existence of admissible D_* given N0 is s7:lemGammaSat(iii).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| f(G), f(n) | least number of objects in a decomposition of E(G); max over n-vertex graphs | s1:defObject | yes: EG.fnum, EG.fmax (EG/Defs/Fnum.lean) |
| object, decomposition | cycle (>=3 distinct vertices) or single non-loop edge; partition of the edge set | s1:defObject | yes: EG.Obj, EG.Obj.WF, EG.IsDecomp (EG/Defs/Objects.lean) |
| eps, sigma, C', A | 2^-5, 100, 103, 105 | s1:defConstants(i) | no: new EG/Defs/Constants.lean (EG.epsC, EG.sigmaC, EG.Cp, EG.Aexp) |
| N0-admissibility | N0 >= 2^40 and, for all N >= N0, the explicit size conditions (i)-(iv) of the proofs of s4:lemTPV, s4:lemPV, s4:thmVXp | s1:defConstants(ii) + s4 proofs | no: EG.N0Cond (needs s4 size predicates EG.S4.TPVSize/PVSize/VXSize) |
| Gamma1..Gamma4 | galactic conditions on D_* | s1:condGamma | no: EG.GammaCond N0 D (see s1:condGamma node) |
| eps1(D), eps2(D) = theta_Q | explicit finite sums of explicit functions of D: eps1 := epsK + 169 epsA + 252/D + 1.5 epsCONC + 3 epsX + 9/D; eps2 := 12 epsX + 4(3 epsA + 60/D + 2F(log2 D)) | s7:propCost (s7.tex:1239), s7:lemUHsplit (s7.tex:1072) | no: EG.eps1, EG.eps2 (s7 layer; depend on epsA s2:lemTower, epsU s5:lemExpect, epsK s5:lemKRED, epsCONC s6:thmCONCL, epsX s7:lemEXprime, F s7:lemUHsplit(iv)) |
| C0, c_EG | C0 := D/2 + 1085 + eps1 D; c_EG := max(C0/(1-2 eps2 D), N0/2) | s1:defConstants(v),(vi) | no: EG.C0, EG.cEG (s7 layer) -- or inline as in EG.Spec.HIStatement |

**deps_declared** (manuscript \deps): `s7:thmMainProof`

**deps_from_proof:** s7:thmMainProof (forward; its proof uses s7:thmHI, s7:thmJVps, s2:propExists, s7:lemGammaSat, s6:defDesign, s1:condGamma) — Statement-level references (not proof deps): s1:defConstants, s1:condGamma, s7:propCost, s7:lemUHsplit (definitions of eps1, eps2). The only forward edge of the DAG.

**used_by:** EGCheck bridge (via EG.Spec.MainInternal)

**randomness:** None in the statement. The proof (s3-s7) selects outcomes of the finite product spaces of s7:defSchedule (stage-1 COL-JV colours + JS labels + zones + pool labels, stage-3 vortex labels, per-round xi_l) by positive-probability / Markov arguments; the conclusion is deterministic.

**lean_shape:**

```lean
Locked Tier-1 (exists): def EG.Spec.MainInternal : Prop := ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V.
Proof route (exists): EG.mainInternal_of_hiHyp (hC : Dstar/2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1/2) (h : Spec.HIHyp Dstar N₀ C ϑ) : MainInternal, with C := EG.C0 D, ϑ := EG.eps2 D, N₀ := N0 from EG.exists_N0 and D from s7:lemGammaSat.
Optional explicit form (Tier-2, unlocked fidelity check): def EG.Spec.MainExplicit : Prop := ∀ (N0 D : ℝ), EG.N0Cond N0 → EG.GammaCond N0 D → ∀ (V : Type) (G : EG.FGraph V), (EG.fnum G.edges : ℝ) ≤ EG.cEG N0 D * G.card.
```

**hazards:**

- **[note] MAIN-EXISTENTIAL.** The locked target MainInternal only asserts existence of c (CONVENTIONS). The explicit c_EG, and the constants 1085/1091, are machine-checked only if MainExplicit is also stated and proved; its lock closure would contain every s2/s4/s5/s6/s7 constant definition (eps-functions, size predicates, COL-JV column 3). Recommendation: keep MainExplicit unlocked (Tier-2).
- **[risk] MAIN-N0-HIDDEN.** N0-admissibility refers to size thresholds that exist only inside the PROOFS of s4:lemTPV/lemPV/thmVXp ('size conditions (i)-(iv)', with the explicit o(1) functions eta_TPV, eta_PV, eta_VX). An explicit Lean statement needs them as named Defs; the s4 blueprint must export them (or state s4 lemmas with a ∀ᶠ N threshold).
- **[risk] MAIN-GAMMA2BC.** (Gamma2)(b),(c) are NOT predicates of D_* (they quantify over rounds of runs and over failure probabilities of s3:lemCOL/s5:lemE1). Any explicit Lean statement must assume only Gamma1 ∧ Gamma2a ∧ Gamma3 ∧ Gamma4; (b),(c) must be lemmas (s2:lemTower(b), s3:lemCOL, s5:lemE1).
- **[note] MAIN-NONNEG.** EG.Spec.HIStatement needs D/2 ≤ C0 and 0 ≤ theta_Q, i.e. eps1 D ≥ 0 and eps2 D ≥ 0. In Lean logb of numbers ≤ 1 is ≤ 0 (and logb of negatives is logb |x|), so these hold only under Gamma1 (log2 log2 D ≥ 2^8); prove them as lemmas from Gamma1core, do not assume them.
- **[note] MAIN-CEIL.** c_EG is real; MainInternal needs c : ℕ: use ⌈c_EG⌉₊ (already done in EG/Proof/Quot/HIMain.lean).

**effort:** ~120 Lean lines, difficulty 2/5 (Only the explicit-form statement and its reduction to MainInternal; the proof of the theorem itself is the whole project (s7:thmMainProof).).

### `s1:remStatus` — remark: status of this manuscript (s1.tex:106)

- **Manuscript referee status:** --
- **Formalization:** no mathematical content; not formalized

**Statement (precise restatement).** Status remark: candidate proof, AI-reviewed only; review history; v6 changes R1-R7 and integration corrections (statements marked 'no referee yet'); most likely error locations (iv)(a)-(d); refutation targets (v)(1)-(5).

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Only pointers.

**used_by:** -

**randomness:** none

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] STATUS-PRIORITY.** Parts written for v6 and not yet clean-room reviewed should be probed first in Lean: s1:factEG0 (R1) and the s4 per-step re-accounting, s1:lemBBD + s3:lemL17s case (b) (R2), s1:citHaxell + new claim/final step of s3:lemL9rho (R3), s3:lemHB via Hall (R4), finite probability spaces of s4 (R5), eventualities s1:condGamma/s3:lemCOLJV/s7:lemGammaSat (R6), integration corrections (citDef11 eps>0, citLem25 m>=2, EG0(b) simple, s3:lemCOLJV(ii) at every mu).
- **[note] STATUS-REFUTE.** Refutation targets (v)(3) (lifted cycle repeating a vertex) and (v)(4) (an edge covered twice) are excluded by construction in Lean (Obj.WF = Nodup, IsDecomp = Nodup of the concatenated edge lists), so the formalization tests them automatically; (v)(1),(2),(5) are quantitative and are tested by s6:thmCONCL(iv), s6:lemJSLC and the s7 cost lemmas.
- **[note] STATUS-HOTSPOTS.** (iv)(a)-(d) name the most likely error sites (JS-LC routing engine s6; Lemma 14^tau + CONC-L(iv); JV+* composition s7; the CR1-PV sites where a per-vertex multiplicity feeds a path-connectivity parameter t). Use for P2 probe ordering.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:convGraphs` — convention: graphs, logarithms, neighbourhoods, balls (s1.tex:453)

- **Manuscript referee status:** --
- **Formalization:** definitions (mostly existing in EG/Defs/Graph.lean, Walk.lean); new: logIter, logStar, MGraph

**Statement (precise restatement).** (a) Graphs are finite and simple (no loops, no parallel edges) unless explicitly called multigraphs (auxiliary multigraphs, loops allowed, occur only in s5 (U-quotients UQ_{l,c,i}) and s7 (layers B_kappa)); G denotes the input graph and n := |V(G)|; |H| := |V(H)|; [k] := {1,...,k}. (b) log = log_2; log^[0] x := x, log^[k] x := log(log^[k-1] x); log* x := least integer k >= 0 with log^[k] x <= 1. Powers log^k x mean (log x)^k. (c) N_H(v) neighbours, d_H(v) = |N_H(v)|, delta(H), Delta(H) min/max degree; for U ⊆ V(H): Nbr_H(U) := {v ∈ V(H)\U : v has a neighbour in U}; H[U] induced; H-U = H\U := H[V(H)\U]; for F ⊆ E(H), H-F := (V(H), E(H)\F); for disjoint A,B ⊆ V(H): E_H(A,B) := edges with one end in A and one in B, e_H(A,B) := |E_H(A,B)|; deg_F(v) := #{e ∈ F : v ∈ e}. (d) A path through V: a path (distinct vertices) all of whose INTERIOR vertices lie in V (ends unrestricted). For U, V ⊆ V(H) and integer i >= 0: B^i_H(U,V) := {w ∈ V : ∃ u ∈ U, ∃ u-w path in H through V of length <= i}; so B^i_H(U,V) ⊆ V and u need not lie in V. (e) Families of pairs of vertices are multisets; 'every vertex lies in at most t pairs' counts occurrences.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| FGraph | finite simple graph with explicit verts : Finset V, edges : Finset (Sym2 V), ends in verts, loopless | s1:convGraphs(a) | yes: EG.FGraph |
| \|H\|, N_H(v), d_H(v), delta, Delta, Nbr_H(U), H[U], H-U, H-F, E_H(A,B), e_H(A,B), deg_F(v) | as in (a),(c) | s1:convGraphs(a),(c) | yes: FGraph.card, nbrs, deg, minDeg, maxDeg, nbrSet, induce, deleteVerts, deleteEdges, edgesBetween, eBetween, EG.edgesAt/EG.degE |
| paths, through V, ball | list paths; IsThrough on interior; B^i_H(U,W) with i : ℕ | s1:convGraphs(d) | yes: EG.IsPathIn, EG.IsPathBetween, EG.interior, EG.IsThrough, EG.pathLength, EG.ball |
| multiset of pairs | indexed family P : ι → V × V over a finite type | s1:convGraphs(e), s1:citDef7 | yes (inside FGraph.IsPathConnected) |
| log^[k], log* | iterated log_2 and the iterated-log count on real arguments | s1:convGraphs(b) | NO: new EG.logIter k x := (Real.logb 2)^[k] x and EG.logStar x := Nat.find (∃ k, logIter k x ≤ 1) |
| multigraph | finite vertex set, edges indexed by a finite type, each edge a Sym2 (loops allowed); degree counts a loop twice | s1:convGraphs(a); used in s5:lemParent, s7:consRound | NO: EG.MGraph (PLAN §3) -- not yet in Defs |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Pointer to s1:citDef7 in (e) is not a dependency.

**used_by:** everywhere (listed only by s2, s3, s4, s6 statements that cite it)

**randomness:** none

**lean_shape:**

```lean
Existing Defs as listed. New (EG/Defs/Log.lean or Found):
noncomputable def EG.logIter (k : ℕ) (x : ℝ) : ℝ := (Real.logb 2)^[k] x
theorem EG.exists_logIter_le_one (x : ℝ) : ∃ k, EG.logIter k x ≤ 1   -- for x ≥ 2, logb 2 x ≤ x - 1; for 1 < x < 2, logb 2 x < 1
noncomputable def EG.logStar (x : ℝ) : ℕ := by classical exact Nat.find (EG.exists_logIter_le_one x)
Lib API: logStar x = 0 ↔ x ≤ 1; 1 < x → logStar x = logStar (logb 2 x) + 1; monotone on [1,∞).
New multigraph type (before s5/s7 Specs): structure EG.MGraph (N E : Type*) where verts : Finset N; edges : Finset E; ends : E → Sym2 N; ends_mem : ∀ e ∈ edges, ∀ v ∈ ends e, v ∈ verts; with deg (loop counted twice), component relation, closed trails.
```

**hazards:**

- **[note] CONV-LOGSTAR.** log* is not defined in EG/Defs; needed by epsCONC (s6:thmCONCL(iv), hence Gamma4), s2:lemTower(a),(d) (R - r <= 2 log* d_r + 2 <= log lambda_r) and the tower facts. Define on reals via Nat.find; requires a small termination lemma.
- **[note] CONV-LOGJUNK.** Real.logb 2 is total: logb 2 x ≤ 0 for x ≤ 1 and logb 2 (-x) = logb 2 x. Iterates beyond log* are junk; no lemma may use log^[k] x for k > log* x. Every 'log log D' needs D > 2 to be positive (Gamma1 assumes D > 2).
- **[note] CONV-LOGPOW.** 'log^k x' = (log_2 x)^k (Lean: Real.logb 2 x ^ k), 'log^[k] x' = iterate, 'log log x' = logb 2 (logb 2 x), '(log D)^{1/2}' = rpow or Real.sqrt. Statement reviewers must check each translation (easy to write logb 2 (x^k)).
- **[note] CONV-FIN.** [k] = {1..k} vs Lean Fin k = {0..k-1} (colours, indices, [2t-1] in s1:citProp8): state with Fin and shift indices in docstrings.
- **[note] CONV-BALLRADIUS.** Ball radii are ℕ in EG.ball; B-M radii such as log^4 n are real: use ⌊r⌋₊ (CONVENTIONS). In the manuscript's own statements the radius ell_* = ⌊2^10 L^3⌋ is already an integer.
- **[note] CONV-TRIVIALPATH.** EG.IsPathIn allows the one-vertex path [v] for any v (also v ∉ V(H)) and ball H i U W ⊇ U ∩ W: statements must keep the manuscript's inclusions U, W ⊆ V(H) (CONVENTIONS).
- **[risk] CONV-MGRAPH.** Multigraphs with loops (s5 UQ_{l,c,i}, s7 B_kappa) have no Defs type yet; s1:citEuler(a),(b) are applied to them (s5:lemParent Step 3). EG.MGraph (with loop-degree 2, components, spanning forests, closed trails) must be designed and locked before the s5/s7 Specs.
- **[note] CONV-LOCALG.** 'G always denotes the input graph, n := |V(G)|' is overridden inside cited results (s1:citProp8, citLem9, citDef11, citLem25, ...), where G, n are arbitrary; in Lean all are bound variables, so reviewers must not import n = |V(G_input)| into those statements.
- **[note] CONV-EAB.** E_H(A,B) is defined in Lean for all A,B but meant for disjoint A,B only (CONVENTIONS).

**effort:** ~250 Lean lines, difficulty 2/5 (logIter/logStar + API (~250). MGraph basics (~200) are counted under s1:citEuler.).

### `s1:defObject` — definition: objects and f (s1.tex:486)

- **Manuscript referee status:** --
- **Formalization:** existing Defs (EG.Obj, EG.IsDecomp, EG.fnum, EG.fmax)

**Statement (precise restatement).** An object is a cycle (of length >= 3) or a single edge. A decomposition of an edge set F is a partition of F into the edge sets of objects (pairwise disjoint edge sets whose union is F); a decomposition of a graph H is one of E(H). f(F) := least number of objects in a decomposition of F (f(∅) = 0); f(H) := f(E(H)); f(n) := max{ f(H) : |V(H)| = n }.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| Obj, Obj.edges, Obj.WF, cycleEdges | edge e (¬ e.IsDiag) \| cycle c (c.Nodup ∧ 3 ≤ c.length, edges zipWith c (rotate 1)) | s1:defObject | yes: EG/Defs/Objects.lean |
| IsDecomp E D | all objects WF; concatenated edge list Nodup; membership ↔ E | s1:defObject | yes |
| fnum F | sInf of lengths of decompositions of F \ diagSet (loops ignored) | s1:defObject | yes: EG/Defs/Fnum.lean |
| fmax n | sup over SimpleGraph (Fin n) of fnum edgeFinset | s1:defObject | yes |
| Obj.isEdge | Bool: the object is a single edge (counts single edges in s1:factEG0, s4:thmVXp) | s1:factEG0, s4:thmVXp | Lib only (EG/Lib/Found/Fnum.lean): move to EG/Defs/Objects.lean if a Spec uses it |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none

**used_by:** s1:factAdd; s1:factEG0; s6 (2x); s7:thmHI

**randomness:** none

**lean_shape:**

```lean
Existing: EG.Obj, EG.IsDecomp (EG/Defs/Objects.lean), EG.fnum, EG.fmax (EG/Defs/Fnum.lean); f(H) written EG.fnum H.edges (FGraph) or EG.fnum G.edgeFinset (SimpleGraph).
```

**hazards:**

- **[note] OBJ-LOOPS.** EG.fnum ignores loops (T0 encoding); apply only to loopless sets (H.edges, G.edgeFinset) or add ∀ e ∈ F, ¬ e.IsDiag; 'F decomposes' for a raw F is IsDecomp + looplessness (CONVENTIONS).
- **[note] OBJ-MULTI.** Obj cannot represent 2-cycles or loops: decompositions are only ever taken of edge sets of the simple input graph G or of the simple quotients Q_l; multigraph edges (s5 UQ, s7 B_kappa) are lifted before decomposing. Any Spec that would 'decompose' a multigraph edge set is a modelling error.
- **[note] OBJ-ISEDGE.** Counting single edges (s1:factEG0 'at most h-1 / |W| single edges', s4:thmVXp) needs Obj.isEdge in Defs; it is currently Lib (EG/Lib/Found/Fnum.lean, @[expose]). Move it (two lines) through the approval procedure, or inline the match in the Spec.

**effort:** ~10 Lean lines, difficulty 1/5 (Only moving Obj.isEdge to Defs.).

### `s1:factAdd` — fact: elementary properties of f (s1.tex:496)

- **Manuscript referee status:** elem.
- **Formalization:** proved (Lib, no sorry): EG/Lib/Found/Fnum.lean, FGraphFnum.lean

**Statement (precise restatement).** (a) ∀ edge set F: f(F) <= |F|. (b) ∀ disjoint edge sets F1, F2: f(F1 ∪ F2) <= f(F1) + f(F2). (c) If H is the vertex-disjoint union of H1 and H2 then f(H) = f(H1) + f(H2). (d) Adding or deleting isolated vertices does not change f; hence n ↦ f(n) is non-decreasing.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| fnum, fmax, IsDecomp | see s1:defObject | s1:defObject | yes |

**deps_declared** (manuscript \deps): `s1:defObject`

**deps_from_proof:** s1:defObject — (c) uses that the edge set of an object induces a connected graph.

**used_by:** s6 (2x); s7 (4x, incl. s7:thmHI steps (1),(2))

**randomness:** none

**lean_shape:**

```lean
Existing Lib theorems: EG.fnum_le_card; EG.fnum_union_le (Disjoint F₁ F₂); EG.fnum_union_eq_of_vertexDisjoint and FGraph.fnum_edges_eq_add_of_disjoint_verts; EG.fnum_map (relabelling/isolated vertices), FGraph.fnum_edges_deleteVerts_of_forall_not_mem, EG.fmax_mono; iterated EG.fnum_biUnion_le / exists_isDecomp_biUnion.
```

**hazards:**

- **[note] ADD-LIB.** Proved as Lib lemmas, not locked Specs; downstream Specs never need to state them. Nothing open.

**effort:** ~0 Lean lines, difficulty 1/5 (Done in P1b.).

### `s1:factEG0` — fact: the long-cycle bound (Fact EG0) (s1.tex:522)

- **Manuscript referee status:** new in v6 (R1); no referee yet
- **Formalization:** Spec + proof (new): EG/Spec/Ext/EG0.lean, EG/Proof/Ext/EG0.lean

**Statement (precise restatement).** (a) FOR EVERY finite simple graph H with h := |V(H)| >= 1 there is a decomposition D of E(H) with |D| <= h (log_2 h + 1) and at most h - 1 single edges in D. In particular f(H) <= h(log_2 h + 1). (b) FOR ALL reals N > 1, alpha, beta with 0 <= alpha <= N, beta > 0 and 4 beta <= L := log_2 N, FOR EVERY finite vertex set W and EVERY edge set F of a simple graph (no loops, no parallel edges) such that every edge of F has both ends in W and |W| <= beta alpha / L: F has a decomposition into at most beta alpha objects, at most |W| of which are single edges. Proof (written in full): Claim: a graph on V(H) with m' >= h edges has a cycle of length >= m'/h (peel vertices of current degree <= d-1, d := max(2, ⌈m'/h⌉); not all vertices go since m' <= (h-1)(d-1) < m'; in the remaining min-degree->=d subgraph close a longest path v0..vr at the neighbour v_i of v0 of largest index, i >= d). Iterate while m_i >= h: m_{i+1} <= (1 - 1/h) m_i; with (1-1/h)^h <= 1/2 and m <= h^2/2 the number t of removals satisfies 2^{q+1} <= h for t-1 = qh + r', so t <= (q+1)h <= h log h; leftover m_t <= h-1 single edges. (b): W = ∅ trivial; else h = |W| <= beta N/L <= N/4 so log h <= L-2 and h(log h + 1) <= hL <= beta alpha.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| FGraph, IsDecomp, Obj | - | s1:convGraphs, s1:defObject | yes |
| Obj.isEdge | single-edge indicator | counts in (a),(b) | Lib only -> move to Defs |
| FGraph.ofEdges W F | graph on W with edge set F (loopless F with ends in W) | (b) proof | yes |
| longest path / min-degree core | proof-internal | (a) Claim | no (Lib lemmas to write) |

**deps_declared** (manuscript \deps): `s1:convGraphs`, `s1:defObject`

**deps_from_proof:** s1:convGraphs (simplicity: degree >= d gives >= d neighbours; |E(H)| <= C(h,2)); s1:defObject — Declared = used. No cited result used (B-M Theorem 2 is no longer used, R1).

**used_by:** s4:lemTPV finish ((b) with beta=48, alpha=|P|<=N, W=P∩U_J, F=H_J); s4:lemPV finish ((b) with beta=64, alpha=|Pl|, W=Pl_J, F=E_1); s4:thmVXp finish ((b) with beta=13, alpha=N, W=U_J; uses the single-edge count <= |U_J|); s5:remConstants(a), s7:remNonCirc (pointers)

**randomness:** none

**lean_shape:**

```lean
def EG.Spec.EG0aStatement : Prop := ∀ (V : Type u) [DecidableEq V] (H : EG.FGraph V), 1 ≤ H.card →
  ∃ D : List (EG.Obj V), EG.IsDecomp ↑H.edges D ∧ (D.length : ℝ) ≤ H.card * (Real.logb 2 H.card + 1) ∧ D.countP EG.Obj.isEdge + 1 ≤ H.card
def EG.Spec.EG0bStatement : Prop := ∀ (V : Type u) [DecidableEq V] (N α β : ℝ) (W : Finset V) (F : Finset (Sym2 V)),
  1 < N → 0 ≤ α → α ≤ N → 0 < β → 4 * β ≤ Real.logb 2 N → (∀ e ∈ F, ¬ e.IsDiag) → (∀ e ∈ F, ∀ v ∈ e, v ∈ W) →
  (W.card : ℝ) ≤ β * α / Real.logb 2 N →
  ∃ D : List (EG.Obj V), EG.IsDecomp ↑F D ∧ (D.length : ℝ) ≤ β * α ∧ D.countP EG.Obj.isEdge ≤ W.card
```

**hazards:**

- **[note] EG0-LOOP.** T0-eg0-loop (recorded; integrated in v6): (b) needs ∀ e ∈ F, ¬ e.IsDiag (a raw Finset (Sym2 V) cannot have parallel edges, so only loops matter).
- **[note] EG0-ISEDGE.** The single-edge counts are load-bearing for s4:thmVXp ('N + o(N) single edges', RT2-I13): the Spec must include them, so Obj.isEdge must be a Defs definition (see s1:defObject).
- **[risk] EG0-UNREVIEWED.** New in v6 (R1), no clean-room review. I re-derived (a) and (b): the claim (m' <= (h-1)(d-1) <= (h-1)m'/h < m'), (1-1/h)^h <= 1/2 (via (1-x^2)^h <= 1 and (1+x)^h >= 2), t <= (q+1)h <= h log h, and h <= N/4 => log h <= L-2 are all correct. The residual risk is in the s4 consumers (the per-step re-accounting 84|P|, 28 per step that keeps 169/369/80 unchanged), not in EG0 itself.
- **[note] EG0-LONGESTPATH.** The claim needs (i) the k-core by iterated deletion (well-founded peeling; Mathlib has no k-core for SimpleGraph in this form) and (ii) existence of a longest path in a finite graph (maximum over a finite set of Nodup lists). Both are routine but not in Lib; with FGraph they are best done via FGraph.toSimpleGraph + Mathlib walks, or directly on lists.
- **[note] EG0-REAL.** Bounds are real (h (log_2 h + 1), beta alpha); m <= h^2/2 needs 2|E| <= h(h-1) (exists as FGraph.two_mul_card_edges_le in EG/Proof/Quot/HI.lean -- move to Lib).

**effort:** ~700 Lean lines, difficulty 3/5 (Claim ~300 (core + longest path), iteration/counting ~250, (b) ~100, Spec ~50.).

### `s1:citNotation` — cited result: B-M notation (s1.tex:610)

- **Manuscript referee status:** pub.
- **Formalization:** no content beyond s1:convGraphs; not formalized separately

**Statement (precise restatement).** B-M notation: d_G(v), N_G(v), Delta(G), Nbr_G(U) (outside neighbourhood), G[V], G\V := G[V(G)\V], G-F, |G|, log = log_2, log^[k], log*, paths through V, balls B^i_G(U,V) ⊆ V (start in U need not lie in V). Identical to s1:convGraphs.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| as s1:convGraphs | - | s1:convGraphs | yes (except logStar) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Undeclared backward pointer to s1:convGraphs (notation identity only).

**used_by:** s3 (1x, pointer)

**randomness:** none

**lean_shape:**

```lean
none (maps to the Defs of s1:convGraphs)
```

**hazards:**

- **[note] NOT-B-M-DIFF.** No semantic difference from s1:convGraphs; the only B-M/Lean gap is the real ball radius (floor).

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citChernoff` — cited result: B-M Theorem 4 (Chernoff, binomial) (s1.tex:627)

- **Manuscript referee status:** pub.
- **Formalization:** proved (Lib, no sorry): EG.chernoff_binomial (EG/Lib/Prob/Chernoff.lean)

**Statement (precise restatement).** FOR EVERY n ∈ ℕ, δ, p ∈ [0,1], and random variable X ~ Bin(n,p) with μ := EX = np: P(X > (1+δ)μ) <= exp(-δ²μ/3) and P(X < (1-δ)μ) <= exp(-δ²μ/2).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| binomial law | law of #successes of n independent Bernoulli(p) | B-M Thm 4 | Lib: FinDist.binomial (EG/Lib/Prob/Chernoff.lean); move to Defs only if a Spec quotes 'X ~ Bin(n,p)' |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Published; Lean proves it directly (exponential moments).

**used_by:** s3:lemL15p, s3:lemL17s (Steps 3,5), s3:thmT16s; s4:lemTPV, s4:lemPV, s4:thmVXp

**randomness:** X : Ω → ℕ on any FinDist μ with μ.map X = binomial n p; typical instance |V| or |V ∩ E| for a ρ-random subset V (IsRSubset).

**lean_shape:**

```lean
theorem EG.FinDist.chernoff_binomial (hX : μ.map X = binomial n p h0 h1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : μ.expect (X ·) = n*p ∧ μ.prob {ω | (1+δ)*(n*p) < X ω} ≤ exp (-(δ^2*(n*p))/3) ∧ μ.prob {ω | (X ω:ℝ) < (1-δ)*(n*p)} ≤ exp (-(δ^2*(n*p))/2). Direct random-set forms: IsRSubset.chernoff_card_upper/_lower/_lower_half, IsRSubset.chernoff_card_inter_*.
```

**hazards:**

- **[note] CH-BINDEF.** FinDist.binomial is a Lib definition; keep 'X ~ Bin' out of locked Specs (consumers use it inside proofs), or move it to Defs with approval.
- **[note] CH-USEFORM.** Consumers apply it to sizes of ρ-random sets, conditionally on earlier independent layers (fixed prefix, compProd). The Lib covers the unconditional random-set forms; conditional use needs the Fubini/cond lemmas of EG/Lib/Prob/Basic.lean (exist: prob_compProd, cond_prod_fst).

**effort:** ~0 Lean lines, difficulty 1/5 (Done in P1b.).

### `s1:citDef7` — cited result (definition): B-M Definition 7 ((ell,t)-path connected through V), multiset form (s1.tex:639)

- **Manuscript referee status:** pub.
- **Formalization:** existing Defs: EG.FGraph.IsPathConnected G ℓ t W (EG/Defs/Expander.lean)

**Statement (precise restatement).** G is (ell,t)-path connected through V ⊆ V(G) iff FOR EVERY finite multiset P of pairs {x,y} of DISTINCT vertices of G (indexed family (x_i,y_i)_{i∈I}) in which every vertex v lies in at most t pairs, counted with multiplicity (#{i : v ∈ {x_i,y_i}} <= t), THERE ARE paths P_i (i ∈ I) such that P_i is an x_i y_i-path in G whose interior vertices lie in V, of length <= ell, and P_i, P_j are edge-disjoint for i ≠ j. A pair occurring k times receives k pairwise edge-disjoint paths; ends need not lie in V.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| IsPathConnected | ∀ (ι : Type) [Fintype ι] (P : ι → V × V), entries vertices and distinct → (∀ v, #{i \| v is an entry of P i} ≤ t) → ∃ Q : ι → List V, paths through W of length ≤ ℓ, pairwise edge-disjoint | s1:citDef7 | yes (ℓ t : ℝ) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none

**used_by:** s3 (L9rho, T16*, remMultiset, lemMonotone); s4 (vortex routing); s5 (U-lent classes, transitions); s6 (JS-LC joint routing)

**randomness:** none

**lean_shape:**

```lean
Existing EG.FGraph.IsPathConnected; Lib: IsPathConnected.exists_paths (any universe), exists_paths_sigma (joint routing, summed multiplicity), IsPathConnected.mono, isPathConnected_natFloor_iff, isPathConnected_of_lt_one.
```

**hazards:**

- **[note] DEF7-REALT.** t is real (s4 uses t = 2^9 L^8 etc.); the property depends only on ⌊t⌋₊ and is trivial for t < 1; integer multiplicities are passed as (k : ℝ).
- **[note] DEF7-ORDERED.** Pairs are ordered in Lean (V × V); harmless by path reversal. The multiset clause (RT2-I14) is built in (indices = occurrences).

**effort:** ~0 Lean lines, difficulty 1/5 (Done in P1b.).

### `s1:citProp8` — cited result: B-M Proposition 8 (one pair out of 2t-1) (s1.tex:656)

- **Manuscript referee status:** pub.
- **Formalization:** Spec + proof (new, proof from B-M l.393-424): EG/Spec/Ext/BMProp8.lean, EG/Proof/Ext/BMProp8.lean

**Statement (precise restatement).** FOR ALL n, ell, t ∈ ℕ with 1 <= ell <= n and 1 <= t <= n, EVERY graph G with |V(G)| = n, EVERY V ⊆ V(G) with |V| >= 4t - 2 such that FOR EVERY U ⊆ V(G) with |U| = t: |B^ell_G(U,V)| > |V|/2, and EVERY choice of vertices x_1..x_{2t-1}, y_1..y_{2t-1} of G that are 4t-2 pairwise distinct: THERE IS j ∈ [2t-1] and an x_j y_j-path in G through V of length <= 4 ell log_2 n. Proof (B-M, not reproduced in the manuscript): I_x := {i : |B^{⌊2 ell log n⌋}_G(x_i,V)| <= |V|/2}, I_y likewise; a j outside I_x ∪ I_y gives two balls of size > |V|/2 inside V that meet, hence a walk x_j -> z -> y_j through V (z ∈ V) of length <= 4 ell log n, shortcut to a path. Otherwise WLOG |I_x| >= t; take r maximal such that some X ⊆ {x_i : i ∈ I_x} has |X| <= t(2/3)^r and |B^{(r+1)ell}(X,V)| > |V|/2 (r = 0 feasible by hypothesis; r <= 2 log t); then (r+1) ell < 2 ell log n so |X| >= 2; split X = X0 ∪ X1, |Xi| <= 2|X|/3; some |B^{(r+1)ell}(Xi,V)| >= t; a t-subset T of it has |B^ell(T,V)| > |V|/2 and B^ell(T,V) ⊆ B^{(r+2)ell}(Xi,V), contradicting maximality.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| FGraph, ball, IsPathBetween, IsThrough, pathLength | - | s1:convGraphs | yes |
| ball composition | B^a(B^b(U,W) , W) ⊆ B^{a+b}(U,W) when the middle set lies in W (walk concatenation + shortcut keeping 'through W') | proof-internal | no (Lib lemma to write) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — No manuscript result used; Lean needs new Lib lemmas on balls/walk shortcutting.

**used_by:** s3:lemL9rho (applied to G - F with ell := ell_* = ⌊2^10 L^3⌋ and t0 := t_{0*})

**randomness:** none

**lean_shape:**

```lean
def EG.Spec.BMProp8Statement : Prop := ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (W : Finset V) (ℓ t : ℕ),
  1 ≤ ℓ → ℓ ≤ G.card → 1 ≤ t → t ≤ G.card → W ⊆ G.verts → 4 * t - 2 ≤ W.card →
  (∀ U ⊆ G.verts, U.card = t → (W.card : ℝ) / 2 < ((EG.ball G ℓ U W).card : ℝ)) →
  ∀ x y : Fin (2 * t - 1) → V, (∀ i, x i ∈ G.verts ∧ y i ∈ G.verts) → Function.Injective (Sum.elim x y) →
  ∃ j p, EG.IsPathBetween G.edges (x j) (y j) p ∧ EG.IsThrough W p ∧ (EG.pathLength p : ℝ) ≤ 4 * ℓ * Real.logb 2 G.card
```

**hazards:**

- **[risk] P8-PROOF-EXTERNAL.** The manuscript cites Prop 8 as a black box; the Lean proof must be reconstructed from B-M (papers/2211.07689.txt l.393-424). Hidden work: walk concatenation through a meeting vertex z ∈ V and shortcutting while keeping 'interior in V' (x or y may reappear inside the other half), the x/y WLOG symmetry, the maximal-r argument with the real bound t(2/3)^r (finiteness of feasible r), r <= 2 log t (uses log_{3/2} <= 2 log), and floors of the real radius 2 ell log n. I checked the argument: it is correct.
- **[note] P8-UNUSEDHYP.** The hypothesis ell <= n is not used by the proof; keep it for faithfulness (s3:lemL9rho verifies 1 <= ell_* <= 2^10 L^3 <= n).
- **[note] P8-GF.** Applied to G - F (FGraph.deleteEdges; same vertex set and n), with the ball hypothesis for U ⊆ V(G) of size t0 only.

**effort:** ~600 Lean lines, difficulty 3/5 (Ball/walk Lib lemmas ~250, main argument ~300, Spec ~50.).

### `s1:citLem9` — cited result: B-M Lemma 9 (with proof structure) (s1.tex:665)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (proof-structure citation; s3:lemL9rho is proved in full with Haxell)

**Statement (precise restatement).** n >= 2, 1 <= ell, k <= n, G n-vertex, V ⊆ V(G), |V| >= n/8 + 1; if FOR EVERY non-empty U ⊆ V(G) and F ⊆ E(G) with |F| <= 2^9 k |U| (ell log n)^2: |B^ell_{G-F}(U,V)| > |V|/2, then G is (4 ell log n, k)-path connected through V. Proof structure quoted (maximal matchings M_I, Prop 8 on G-F, Aharoni-Haxell); applies verbatim to multisets.

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citProp8 (B-M proof); B-M Theorem 6 (Aharoni-Haxell; not used in this manuscript) — Structure only; s3:lemL9rho and s3:remMultiset list it but re-prove everything.

**used_by:** s3:lemL9rho (structure); s3:remMultiset (counting step 2k|I'| >= |I|)

**randomness:** none

**lean_shape:**

```lean
none (blueprint node without a Lean declaration)
```

**hazards:**

- **[note] L9-NOLEAN.** Blueprint/checkdecls tooling: this node has no Lean declaration; mark it 'cited, not formalized (proof structure only)' so msreport/checkdecls do not demand one. The multiset counting step it justifies is re-proved inside s3:lemL9rho.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citDef11` — cited result (definition): B-M Definition 11 ((eps,s)-expander) and its remark (s1.tex:697)

- **Manuscript referee status:** pub.; remark eps > 0 added in v6 (integration): no referee yet
- **Formalization:** existing Defs EG.FGraph.IsExpander; remark proved (IsExpander.lt_deg, IsExpander.lt_minDeg)

**Statement (precise restatement).** An n-vertex graph G is an (eps,s)-expander iff FOR EVERY U ⊆ V(G) and F ⊆ E(G) with 1 <= |U| <= 2n/3 and |F| <= s|U|: |Nbr_{G-F}(U)| >= eps|U| / (log_2 n)^2. Remark: if n >= 2 and eps > 0 then δ(G) > s (take U = {v}, F = edges at v). For eps <= 0 every graph qualifies; every use has eps >= 2^-7.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| IsExpander G ε s | as stated, n = G.card, log² n = (Real.logb 2 n)^2, ε s : ℝ | s1:citDef11 | yes |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none

**used_by:** s2 (witness, lemCap, lemHS, propStructure); s3 (13x); indirectly everywhere

**randomness:** none

**lean_shape:**

```lean
Existing: EG.FGraph.IsExpander; Lib: IsExpander.lt_deg / lt_minDeg (0 < ε, 2 ≤ G.card), isExpander_of_card_le_one, isExpander_of_nonpos, IsExpander.mono, IsExpander.of_le.
```

**hazards:**

- **[note] DEF11-EPS.** T0-def11-eps resolved in v6 (remark assumes eps > 0). Lean lemmas already require 0 < ε and 2 ≤ |G|.
- **[note] DEF11-N.** n is the expander's own vertex count (for spanning expanders on a part Z, n = |Z|), so log^2 n differs between G and its parts; Specs must use O.card of the relevant graph.

**effort:** ~0 Lean lines, difficulty 1/5 (Done in P1b.).

### `s1:citProp12` — cited result: B-M Proposition 12 (expansion or d-fold neighbourhood) (s1.tex:713)

- **Manuscript referee status:** pub.
- **Formalization:** Spec + proof (new; proof quoted in full): EG/Spec/Ext/BMProp12.lean, EG/Proof/Ext/BMProp12.lean

**Statement (precise restatement).** For U ⊆ V(G) and real d > 0 let N_{G,d}(U) := {v ∈ V(G)\U : v has at least d neighbours in U}. FOR EVERY n-vertex (eps,s)-expander G, EVERY U ⊆ V(G) with 1 <= |U| <= 2n/3, EVERY F ⊆ E(G) with |F| <= s|U|/2 and EVERY real d with 0 < d <= s: (a) |Nbr_{G-F}(U)| >= s|U|/(2d), or (b) |N_{G-F,d}(U)| >= eps|U|/log_2^2 n. Proof: if (a) fails, X := Nbr_{G-F}(U) \ N_{G-F,d}(U) has |X| < s|U|/(2d); F' := E_{G-F}(U,X) has |F'| <= d|X| <= s|U|/2 (each x ∈ X has < d neighbours in U); |F ∪ F'| <= s|U| and Nbr_{G-F-F'}(U) = N_{G-F,d}(U); expansion of G at (U, F ∪ F') gives (b).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| IsExpander, nbrSet, deleteEdges, edgesBetween | - | s1:citDef11, s1:convGraphs | yes |
| N_{H,d}(U) | (H.verts \ U).filter (fun v => d ≤ #(H.nbrs v ∩ U)) | s1:citProp12; also s3:propP13s (Nbr_{G-F,d}) | NO: new EG.FGraph.nbrSetDeg H U d (Defs, since s3:propP13s's Spec uses it) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citDef11 (expansion applied to (U, F ∪ F')) — Declared 'none (published)'; the proof uses Def 11.

**used_by:** s3:propP13s (d := d_* integer >= 1, U := W \ Bl, |F| <= s_1|W|/4 <= s_1|U|/2)

**randomness:** none

**lean_shape:**

```lean
def EG.FGraph.nbrSetDeg (H : EG.FGraph V) (U : Finset V) (d : ℝ) : Finset V := (H.verts \ U).filter (fun v => d ≤ ((H.nbrs v ∩ U).card : ℝ))
def EG.Spec.BMProp12Statement : Prop := ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (ε s d : ℝ) (U : Finset V) (F : Finset (Sym2 V)),
  G.IsExpander ε s → U ⊆ G.verts → 1 ≤ U.card → (U.card : ℝ) ≤ 2 * G.card / 3 → F ⊆ G.edges → (F.card : ℝ) ≤ s * U.card / 2 →
  0 < d → d ≤ s →
  s * U.card / (2 * d) ≤ ((G.deleteEdges F).nbrSet U).card ∨ ε * U.card / Real.logb 2 G.card ^ 2 ≤ ((G.deleteEdges F).nbrSetDeg U d).card
```

**hazards:**

- **[note] P12-INCL.** B-M leave U ⊆ V(G) and F ⊆ E(G) implicit; the Spec must include them (CONVENTIONS: keep inclusion hypotheses).
- **[note] P12-DREAL.** d is real in B-M, integer d_* in the only use; the hypothesis d <= s is not used by the proof (keep it).
- **[note] P12-NEWDEF.** N_{G,d}(U) is a new definition shared with s3:propP13s; define once in Defs (Graph.lean) so both Specs use the same constant.

**effort:** ~200 Lean lines, difficulty 2/5.

### `s1:citProp13` — cited result: B-M Proposition 13 (stars or bipartite subgraph), with proof structure (s1.tex:730)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (proof-structure citation; s3:propP13s is proved in full with explicit parameters)

**Statement (precise restatement).** There is n0 such that for n >= n0, 1 >= eps >= 2^-9, s >= 8 log^13 n, every n-vertex (eps,s)-expander G, U ⊆ V(G) with |U| <= 2n/3 and F with |F| <= s|U|/4: G-F contains (a) |U|/log^7 n vertex-disjoint stars with log^9 n leaves, centre in U, leaves outside U, or (b) a bipartite H with classes U and X ⊆ V(G)\U, |X| >= eps|U|/(2 log^2 n), X-degrees >= log^4 n, U-degrees <= 2 log^9 n.

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citProp12 (B-M proof) — Structure only.

**used_by:** s3:propP13s (structure)

**randomness:** none

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] P13-ASYMP.** Asymptotic ('there is n0') with non-integer star/leaf counts (log^7 n, log^9 n); do not formalize. s3:propP13s is the explicit replacement. Mark the blueprint node as not formalized.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citLem14` — cited result: B-M Lemma 14 (expander decomposition), with proof structure (s1.tex:761)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (proof-structure citation; s2:lemOVgeneric, s2:lem14tau, s2:defHBtp re-prove / define everything)

**Statement (precise restatement).** Given an n-vertex G, integer s >= 0 and eps <= 2^-5, one can delete at most 4sn log n edges so that the rest partitions into (eps,s)-expanders G_1..G_r with Σ|G_i| <= 2n (s = 0: nothing deleted). Proof: induction under Σ|G_i| <= 2n - 2n/(2+log n); witness (U,F); G_1 := G[U ∪ Nbr_{G-F}(U)] - F, G_2 := G\U - E(G_1) - F; inequalities (6)-(9).

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citDef11 (B-M proof) — s2 uses it only to identify the s = 0 recursion of (R3) with B-M's recursion.

**used_by:** s2:lemOVgeneric, s2:lem14tau, s2:defHBtp, s2:propStructure (structure/identification only)

**randomness:** none

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] L14-NOLEAN.** No Lean theorem needed: every s2 use is 'this recursion is the one of B-M' plus a full re-proof (s2:lemOVgeneric counting with 1/(1-3.42 eps)). Mark as not formalized.
- **[note] L14-INEQ9.** The quoted derivation of (9) via log n1 < log n - 2/5 only yields (9) for log n > 1.09 (8L^2 > (2+L)^2); at n = 2 inequality (9) still holds by direct evaluation. Irrelevant for Lean (not formalized) but do not reuse the quoted chain verbatim.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citLem15` — cited result: B-M Lemma 15 (not used) (s1.tex:802)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (not used; replaced by s3:lemL15p)

**Statement (precise restatement).** n,k,s ∈ ℕ, 0 < eps <= 1, G n-vertex (eps,s)-expander with s >= 2^12 eps^-1 k^2 log^4 n: E(G) splits into k edge-disjoint spanning (eps/4, sqrt(s eps)/(8k log n))-expanders.

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Quoted for comparison only.

**used_by:** -

**randomness:** none

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] L15-UNUSED.** Must not appear in any \uses edge (remBMused: not a dependency).

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citThm16` — cited result: B-M Theorem 16 (not used as a black box) (s1.tex:816)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (not used; s3:thmT16s is proved in full)

**Statement (precise restatement).** An n-vertex (eps,s)-expander with 1 >= eps >= 2^-7 and s >= log^135 n is, with high probability, (4 log^5 n, 2^8 log^5 n)-path connected through a random set containing each vertex independently with probability 1/3.

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** B-M Lemma 15, Lemma 19, Lemma 9 (its proof)

**used_by:** -

**randomness:** (1/3)-random vertex subset; 'with high probability' is asymptotic in n (no explicit bound) -- one reason it is not used.

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] T16-WHP.** 'with high probability' has no explicit error bound; not formalizable as stated and not needed.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citLem17` — cited result: B-M Lemma 17 (ball growth under sprinkling), with proof structure (s1.tex:831)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (proof-structure citation; s3:lemL17s proved in full with explicit rho)

**Statement (precise restatement).** n >= 2, G n-vertex (eps,s)-expander, 2^-9 <= eps <= 1, s >= 8 log^13 n; U with |Nbr_G(U)| >= |U| log^24 n, F with |F| <= |U|, V a (1/3)-random subset: with probability 1 - e^{-Ω(|U| log^2 n)}, |B^{log^4 n}_{G-F}(U,V)| > |V|/2. Proof structure: layers V_1..V_ell, p with (1-p)^{ell-1} = 11/12, growth via Prop 13 (Chernoff / bounded differences), last stage density q = 3/11.

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citProp13; s1:citChernoff; a bounded-differences inequality (replaced by s1:lemBBD in s3:lemL17s)

**used_by:** s3:lemL17s (structure)

**randomness:** (1/3)-random subset realised as a union of independent layers; asymptotic error term.

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] L17-ASYMP.** Asymptotic error e^{-Ω(·)}; not formalized. s3:lemL17s is the explicit version (exp(-7|U|L)).

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citProp18` — cited result: B-M Proposition 18 (well-expanding subset), with proof and remark RT2-I12 (s1.tex:855)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (proof-structure citation; s3:lemP18s part (i) proved in full with s_1 >= theta_* + 1)

**Statement (precise restatement).** n >= 2, 0 < eps <= 1, s >= log^24 n, G n-vertex (eps,s)-expander, U ⊆ V(G) with |U| <= 2n/3: ∃ U' ⊆ U with |Nbr_G(U')| >= |U'| log^24 n and |U'| >= eps|U|/(3 log^26 n). Remark: the maximality step gives fewer than theta + 1 outside neighbours, so the proof needs s >= theta + 1.

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citDef11 (B-M proof)

**used_by:** s3:lemP18s (structure; the theta+1 correction)

**randomness:** none

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] P18-THETA.** B-M's statement is slightly wrong for non-integer theta (needs s >= theta + 1); already corrected in s3:lemP18s. Do not formalize the B-M form.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citLem19` — cited result: B-M Lemma 19 (all balls large, whp), with proof structure (s1.tex:879)

- **Manuscript referee status:** pub.
- **Formalization:** not formalized (proof-structure citation; s3:lemP18s part (ii) proved in full)

**Statement (precise restatement).** G n-vertex (eps,s)-expander, 2^-9 <= eps <= 1, s >= 2 log^24 n, V a (1/3)-random subset: with probability 1 - o(1/n), for every non-empty U and F with |F| <= |U|/log^27 n, |B^{log^4 n}_{G-F}(U,V)| > |V|/2. Proof: union bound of Lemma 17 over well-expanding U' and |F| <= |U'|; Prop 18; large U via a subset of size in [n/2, 2n/3].

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citLem17; s1:citProp18

**used_by:** s3:lemP18s (structure)

**randomness:** (1/3)-random subset; asymptotic o(1/n).

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] L19-ASYMP.** Asymptotic; not formalized. s3:lemP18s(ii) gives the explicit 1 - n^-6.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citThm21` — cited result: B-M Theorem 21 = Lovász 1968 (paths and cycles), not used directly (s1.tex:898)

- **Manuscript referee status:** pub.
- **Formalization:** Stage-α explicit Prop hypothesis (PLAN §1) consumed only by the Lean proof of s1:citCor22; stage β: formal proof of Lovász's theorem

**Statement (precise restatement).** FOR EVERY finite simple graph G on n vertices, E(G) decomposes into at most ⌊n/2⌋ paths (length >= 1) and cycles (length >= 3), i.e. edge-disjoint paths and cycles whose edge sets partition E(G), their number p + c satisfying 2(p + c) <= n.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| path/cycle decomposition | lists P (paths, >= 2 distinct vertices) and C (well-formed cycles) whose edge lists concatenate to a Nodup list with exactly the edges of F | s1:citThm21, s1:citCor22 | NO: new EG.IsPathCycleDecomp (Defs, because the stage-α hypothesis is a locked Prop) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Published (Lovász, On covering of graphs, 1968).

**used_by:** s1:citCor22 (its B-M proof) only

**randomness:** none

**lean_shape:**

```lean
def EG.IsPathCycleDecomp (F : Set (Sym2 V)) (P C : List (List V)) : Prop :=
  (∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup) ∧ (∀ c ∈ C, (EG.Obj.cycle c).WF) ∧
  (P.flatMap EG.walkEdges ++ C.flatMap EG.cycleEdges).Nodup ∧ ∀ e, e ∈ P.flatMap EG.walkEdges ++ C.flatMap EG.cycleEdges ↔ e ∈ F
def EG.Spec.LovaszStatement : Prop := ∀ (V : Type) [DecidableEq V] (H : EG.FGraph V),
  ∃ P C : List (List V), EG.IsPathCycleDecomp ↑H.edges P C ∧ 2 * (P.length + C.length) ≤ H.card
```

**Recorded (P2-D small, fix round 1).** `EG.IsPathCycleDecomp` now exists in `EG/Defs/PathDecomp.lean` with exactly the shape above (reviewed as faithful). The stage-α Lovász hypothesis is stated with `IsPathCycleDecomp`: its paths have ≥ 2 distinct vertices, which loses nothing, since trivial paths carry no edges and dropping them only lowers `P.length`, so `2 * (P.length + C.length) ≤ H.card` stays a true statement. `isPathCycleDecomp_nil_right` connects it to `IsPathDecomp` (no cycles).

**hazards:**

- **[risk] LOV-TRUTH.** A stage-α hypothesis is TRUSTED: if the Lean LovaszStatement were false (e.g. stated for multigraphs, where a double edge on 2 vertices needs 2 > 1 paths, or with loops allowed, or with n counting only non-isolated vertices in the wrong direction), the stage-α theorem would be vacuous. State it for FGraph (simple, loopless) with n = |V(H)| including isolated vertices, exactly Lovász's ⌊n/2⌋; have it reviewed against the paper before locking.
- **[note] LOV-UNIV.** The Cor 22 proof applies Lovász to G + v0 on Option V; if LovaszStatement is at universe Type, Cor22 and all consumers must stay in Type (consistent with MainInternal, V : Type).
- **[note] LOV-BETA.** Stage β/γ discharge (Lovász's proof) is a large separate task (~2000-4000 lines, difficulty 5); outside P2.

**effort:** ~40 Lean lines, difficulty 2/5 (Spec only; the theorem's own proof is a stage-β task.).

### `s1:citCor22` — cited result: B-M Corollary 22 (path decomposition, each vertex an end of <= 2 paths) and consequence (s1.tex:904)

- **Manuscript referee status:** pub.
- **Formalization:** Spec + proof from the stage-α Lovász hypothesis (new): EG/Spec/Ext/Cor22.lean, EG/Proof/Ext/Cor22.lean

**Statement (precise restatement).** (main) FOR EVERY finite simple graph G there is a decomposition of E(G) into paths of length >= 1 such that every vertex of G is an end of at most two of the paths. (consequence) FOR EVERY finite simple graph H and EVERY vertex set W containing both ends of every edge of H, E(H) decomposes into at most |W| paths; s4 uses a 'Corollary-22 decomposition' = a path decomposition with BOTH properties (end-count <= 2 at every vertex, and hence <= |W| paths when all edges lie in W). Proof (B-M l.1428-1442, only sketched in the manuscript): G' := G + v0, v0 joined to every vertex of even degree; Lovász gives <= ⌊(n+1)/2⌋ paths and cycles of G'; every vertex of G has odd degree in G', so it is an end of an odd number (>= 1) of paths; counting ends forces: each vertex of G is an end of exactly one path and there are no cycles; deleting v0 splits/shortens the paths through v0; each vertex of G is then an end of <= 2 paths (its own, plus one created by removing its edge to v0).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| path decomposition | list P of vertex lists, each Nodup with >= 2 vertices, whose walkEdges concatenate Nodup and equal F | s1:citCor22, s4 (E) | NO: new EG.IsPathDecomp (Defs; s4 Specs need it) |
| end count | #{p ∈ P : v is the first or last vertex of p} | s1:citCor22, s4 (E), s4:lemPV(c) | NO: new EG.pathEndCount (Defs or inline) |
| graph G + v0 | FGraph on Option V | proof-internal | no (Lib) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citThm21 (Lovász; undeclared -- the manuscript lists 'none (published)'); parity of path ends (the s4 observation (E), to be proved in Lib) — The consequence is proved in the manuscript (double counting of ends).

**used_by:** s4:lemTPV, s4:lemPV, s4:thmVXp (Corollary-22 decompositions of step edge sets E_{2,c}, F_j; stripping in the PV finish; PV(c) degree bound 'Cor 22 does not limit the number of such paths at x')

**randomness:** none

**lean_shape:**

```lean
def EG.IsPathDecomp (F : Set (Sym2 V)) (P : List (List V)) : Prop :=
  (∀ p ∈ P, 2 ≤ p.length ∧ p.Nodup) ∧ (P.flatMap EG.walkEdges).Nodup ∧ ∀ e, e ∈ P.flatMap EG.walkEdges ↔ e ∈ F
def EG.pathEndCount [DecidableEq V] (P : List (List V)) (v : V) : ℕ := P.countP (fun p => p.head? = some v ∨ p.getLast? = some v)
def EG.Spec.Cor22Statement : Prop := ∀ (V : Type) [DecidableEq V] (F : Finset (Sym2 V)), (∀ e ∈ F, ¬ e.IsDiag) →
  ∃ P, EG.IsPathDecomp (F : Set (Sym2 V)) P ∧ ∀ v, EG.pathEndCount P v ≤ 2
theorem EG.cor22_of_lovasz : EG.Spec.LovaszStatement → EG.Spec.Cor22Statement
theorem EG.IsPathDecomp.length_le_card (W) (hW : ∀ e ∈ F, ∀ v ∈ e, v ∈ W) (hP : EG.IsPathDecomp (F : Set (Sym2 V)) P) (h2 : ∀ v, EG.pathEndCount P v ≤ 2) : P.length ≤ W.card
```

**hazards:**

- **[risk] C22-PROOF-EXTERNAL.** The manuscript gives only a one-line sketch; the Lean proof must reconstruct B-M's parity/counting argument: exact integer bound ⌊(n+1)/2⌋ from Lovász, 'odd degree ⇒ end of an odd number of paths' (parity of path ends), no cycles, then list surgery when deleting v0 (a path with v0 interior splits into two, v0 an end shortens it, a path v0-v becomes trivial and must be dropped). Moderate but fiddly.
- **[note] C22-DEPS.** The manuscript's deps line says 'none (published)', but any Lean proof depends on Lovász (s1:citThm21) -> the stage-α hypothesis enters the s4 lemmas through Cor 22. Record the edge s1:citCor22 -> s1:citThm21 in the blueprint.
- **[note] C22-SIMPLE.** Only for simple graphs (s4 says so); all s4 applications decompose edge sets of G. Loops must be excluded in the Spec (∀ e ∈ F, ¬ e.IsDiag).
- **[note] C22-TRIVIAL.** Paths must be non-trivial (>= 1 edge) for 'two distinct ends in W' and the |W| bound; IsPathDecomp requires length >= 2 vertices.

**effort:** ~700 Lean lines, difficulty 3/5 (Parity lemma (E) ~150, G+v0 construction and Lovász application ~200, deletion surgery ~250, consequence ~100.).

### `s1:citLem25` — cited result: B-M Lemma 25, explicit form (long cycle in (eps,0)-expanders) (s1.tex:918)

- **Manuscript referee status:** pub.; hypothesis m >= 2 added in v6 (integration): no referee yet
- **Formalization:** existing locked Spec EG.Spec.BMLemma25Statement; proof EG.bmLemma25 = sorry (to do: DFS proof)

**Statement (precise restatement).** FOR EVERY real eps >= 2^-5, EVERY m ∈ ℕ with m >= max(2, 2^30/eps^2) and EVERY m-vertex (eps,0)-expander G: G contains a cycle of length >= eps^2 m / (18 log_2^4 m). Proof (B-M DFS): G is connected (a component of size <= m/2 would not expand); run DFS with unexplored U, stack path P, processed R; |U| - |R| drops by 1 per step from m-1 to -m, so at some time |U| = |R|; no U-R edges, so Nbr(U) ⊆ P and |P| >= eps m/(3 log^2 m); split P into consecutive X, Y, Z with |X|,|Z| >= |P|/3 and eps^2 m/(18 log^4 m) <= |Y| < eps^2 m/(9 log^4 m); a shortest X-Z path avoiding Y closes a cycle through Y; otherwise the side X' of size <= m/2 has |Nbr(X')| <= |Y| < eps|X|/log^2 m, contradicting expansion.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| IsExpander, Obj.cycle WF, cycleEdges | - | s1:citDef11, s1:defObject | yes |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citDef11 (connectivity, |P| bound, final contradiction)

**used_by:** s2:lemCap (ii) at eps = 2^-5, m >= 2^40 (via EG.Spec.CapGraphStatement)

**randomness:** none

**lean_shape:**

```lean
Existing (EG/Spec/Ext/BMLemma25.lean): def EG.Spec.BMLemma25Statement : Prop := ∀ (V : Type u) [DecidableEq V] (G : EG.FGraph V) (ε : ℝ), (2:ℝ)^(-5:ℤ) ≤ ε → (2:ℝ)^30/ε^2 ≤ G.card → 2 ≤ G.card → G.IsExpander ε 0 → ∃ c : List V, (EG.Obj.cycle c).WF ∧ (∀ e ∈ EG.cycleEdges c, e ∈ G.edges) ∧ ε^2 * G.card / (18 * Real.logb 2 G.card ^ 4) ≤ c.length.
```

**hazards:**

- **[risk] L25-CONST18.** The explicit constant 18 is read off B-M's sketch, and s2:lemCap has a razor-thin numeric margin built on it (18432 = 18·2^10 at eps = 2^-5; cap_const: 18432·1.37317^4 ≈ 65535.9 <= 2^16 = 65536). If the Lean proof only reaches a worse constant, lemCap and M_l := max(2^40, 2^16 t d log^4(t d)) break. I re-derived the rounding B-M skip: a := eps^2 m/(18 log^4 m) >= 23 (since eps^2 m >= 2^30 and log m <= log(eps^2 m) + 10), so |Y| := ⌈a⌉ < 2a; non-vacuity of the expander forces eps <= log^2 m, so |Y| <= |P|/6 + 1 and X, Z with |X|,|Z| >= |P|/3 exist once |P| >= 12. The constant 18 survives, but the Lean proof must do this arithmetic explicitly.
- **[risk] L25-DFS.** DFS must be formalized as an invariant-preserving relation on (U, P, R) (PLAN: 'as an invariant relation'), with a discrete intermediate-value step for |U| = |R|; plus connectivity from expansion and the shortest X-Z path whose interior avoids P. ~1000+ lines.
- **[note] L25-M2.** T0-cap-1 (m >= 2) is integrated in v6 and in the locked Spec; EG.bmLemma25_literal_false documents the m = 1 counterexample.

**effort:** ~1200 Lean lines, difficulty 4/5 (Spec exists; proof outstanding (sorry).).

### `s1:remBMused` — remark: where the results of B-M are used (s1.tex:942)

- **Manuscript referee status:** --; table and last sentence rewritten in v6 (R1): no referee yet
- **Formalization:** no mathematical content; not formalized

**Statement (precise restatement).** Table of uses: Def 7 (s3-s6), Lemma 9 + Prop 8 (s3:lemL9rho), Theorem 6 not used (Haxell instead), Def 11 everywhere, Props 12-13, Lemma 17, Prop 18, Lemma 19 (s3, T16*), Lemma 14 (s2), Cor 22 (s4), Lemma 25 (s2:lemCap), Thm 4 (s3, s4); Lemma 15, Theorem 16, Theorem 21 not used directly. B-M Theorem 2, Theorem 24, Lemma 26 not used (vortex finishes use s1:factEG0).

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): `s1:citNotation`, `s1:citChernoff`, `s1:citDef7`, `s1:citProp8`, `s1:citLem9`, `s1:citDef11`, `s1:citProp12`, `s1:citProp13`, `s1:citLem14`, `s1:citLem17`, `s1:citProp18`, `s1:citLem19`, `s1:citCor22`, `s1:citLem25`, `s1:factEG0`

**deps_from_proof:** none — A remark's row lists what it is about.

**used_by:** -

**randomness:** none

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] BMUSED-LEANSET.** Consequence for Lean: the only B-M results needing Lean proofs are Prop 8, Prop 12, Lemma 25 and Cor 22 (+ Lovász as stage-α hypothesis); Defs 7 and 11 and Theorem 4 exist; Lemma 9, Props 13/18, Lemmas 14/17/19 are proof-structure citations only; Lemma 15, Theorem 16 unused.

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:citChernoffGen` — cited result (with derivation): Chernoff bounds for sums of independent indicators [JLR00 2.1, 2.8] (s1.tex:986)

- **Manuscript referee status:** standard
- **Formalization:** proved (Lib, no sorry): EG/Lib/Prob/Chernoff.lean

**Statement (precise restatement).** Let X = Σ_{i=1}^m I_i with I_i independent indicators, P(I_i = 1) = p_i, and 0 <= δ <= 1. (a) If μ >= EX then P(X >= (1+δ)μ) <= exp(-δ²μ/3); if 0 <= μ <= EX then P(X <= (1-δ)μ) <= exp(-δ²μ/2); in particular s1:citChernoff with μ = EX. (b) If EX <= μ then for every integer j >= 1: P(X >= j) <= μ^j/j! <= (eμ/j)^j.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| FinDist, prob, expect, iIndepFun | - | EG/Defs/Prob/FinDist.lean | yes |
| IndepEvents | mutual independence of events | Lib core hypothesis | Lib only (EG/Lib/Prob/Chernoff.lean) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** s1:citChernoff ('in particular' clause; trivial) — The JLR t-forms of the derivation are not needed: Lean proves the stated forms directly.

**used_by:** s3:lemL17s (Step 5, (a) lower tail with mean lower bound, conditional on V_1..V_{ell-1}); s5:lemE1(a) (χ_u, independent only on Aw_Y(w): _on forms); s7:lemCand(iii), s7:lemCC(ii), s7:lemUltra(ii) ((a) and (b))

**randomness:** Any FinDist μ; indicators I : ι → Ω → ℝ, 0/1-valued (on the summation range) and mutually independent (μ.iIndepFun, possibly only on the subtype of the summation range).

**lean_shape:**

```lean
Existing: chernoffGen_upper / chernoffGen_lower / chernoffGen_tail / chernoffGen_tail_exp / chernoffGen_lower_half and the _on variants (hypotheses only on s), IndepEvents.chernoff_*; corollaries chernoff_pi_bernoulli_*, chernoff_pi_dependsOn_*, IsRSubset.chernoff_card_*, chernoff_randColouring_*.
```

**hazards:**

- **[note] CHG-COND.** All uses are conditional on a fixed prefix (earlier layers / fixed past); the Lib lemmas are stated for an arbitrary FinDist, so consumers instantiate them at the conditional/kernel distribution (compProd second stage) -- consumers must build that distribution explicitly.

**effort:** ~0 Lean lines, difficulty 1/5 (Done in P1b.).

### `s1:citMarkov` — cited result (with derivation): Markov's inequality and its two uses (s1.tex:1021)

- **Manuscript referee status:** standard
- **Formalization:** proved (Lib, no sorry): EG/Lib/Prob/Basic.lean

**Statement (precise restatement).** If X >= 0 and a > 0 then P(X >= a) <= EX/a. Consequently (a) X >= 0 ⇒ P(X <= 3EX) >= 2/3; (b) X1, X2 >= 0 ⇒ P(X1 <= 4EX1 and X2 <= 4EX2) >= 1/2; (c) (a),(b) hold for the conditional probability given any event of positive probability, or given any fixed outcome of variables independent of the variables being drawn.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| FinDist.cond, prod/compProd | conditioning on an event; fixing a prefix | EG/Defs/Prob/FinDist.lean | yes |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none

**used_by:** s4:lemTPV, s4:lemPV (good event (G5)); s7:consRound(f), s7:lemWellDef(iii), s7:lemOneOutcome (stage-1 selection X' <= 3 E X'; per-round copies and payments <= 4 E)

**randomness:** Any FinDist; (c): μ.cond A hA, or the second stage of μ.prod ν / compProd given a first-stage outcome.

**lean_shape:**

```lean
Existing: prob_le_expect_div, mul_prob_le_expect, one_sub_inv_le_prob_le_mul_expect, two_thirds_le_prob_le_three_mul_expect, half_le_prob_le_four_mul_expect_and, two_thirds_mul_prob_le_prob_inter_cond, half_mul_prob_le_prob_inter_cond, cond_prod_fst, map_snd_cond_prod_fst.
```

**hazards:**

- **[note] MARKOV-FIXED.** 'Given a fixed outcome' is a slice of a product (no σ-algebras), consistent with the outline and s7:defSchedule; Past_l is a fixed value, not a random object (RT2-J5). Consumers in s7 must model the round-l randomness xi_l as a fresh FinDist parametrised by the past.

**effort:** ~0 Lean lines, difficulty 1/5 (Done in P1b.).

### `s1:lemBBD` — lemma: Lemma BBD (Bernstein inequality for bounded differences) (s1.tex:1044)

- **Manuscript referee status:** new in v6 (R2), a standard result; no referee yet
- **Formalization:** Spec + proof (delivered, [bbd]): EG/Spec/Found/BBD.lean (`EG.Spec.BBDStatement`, `EG.Spec.BBDRVStatement`), EG/Proof/Found/BBD.lean (`EG.bbd`, `EG.bbdRV`); modules EG.Spec.Found.BBD / EG.Proof.Found.BBD. Delivered statements are universe-polymorphic (`ι : Type v`, `Ω : Type u`), carry no `[DecidableEq ι]`, and state 'differ only in coordinate k' literally as `∀ j, j ≠ k → x j = x' j`; the sketch below is the pre-delivery plan.

**Statement (precise restatement).** FOR EVERY integer m >= 0, p_1..p_m ∈ [0,1], independent I_1..I_m with P(I_k = 1) = p_k, P(I_k = 0) = 1 - p_k (I := (I_1..I_m)), EVERY Ψ : {0,1}^m → ℝ, b >= 0 and c_1..c_m ∈ [0,b] such that |Ψ(x) - Ψ(x')| <= c_k whenever x, x' differ only in coordinate k, EVERY β > 0 with β >= Σ_k p_k(1-p_k)c_k², and EVERY a >= 0: P(Ψ(I) >= EΨ(I) + a) <= exp(-a²/(2(β + ba/3))) and P(Ψ(I) <= EΨ(I) - a) <= exp(-a²/(2(β + ba/3))). Proof (in full, finite sums): partial averages Ψ_k (Ψ_{k-1}(y) = p_k Ψ_k(y,1) + (1-p_k) Ψ_k(y,0), |Ξ_k| <= c_k); (1 - u/3)e^u <= 1 + 2u/3 + u²/6 for all real u (χ'' = (1 - (1-u)e^u)/3 >= 0), hence e^u <= 1 + u + u²/(2(1 - ζ/3)) for u <= ζ < 3; one-coordinate mgf bound; induction over coordinates; Markov on e^{η(Ψ - EΨ)} with η := a/(β + ba/3); lower tail = upper tail of -Ψ.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| FinDist.pi, FinDist.bernoulli, prob, expect | product of Bernoulli coordinates on ι → Bool | EG/Defs/Prob/FinDist.lean | yes |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Self-contained (elementary exp facts, derivative sign => monotone).

**used_by:** s3:lemL17s case (b): conditional on V_1..V_{i-1} (fixed W = B_i), I_k := 1[w_k ∈ V_i] (V_i p_*-random), Ψ := #{x ∈ X : N_H(x) ∩ V_i ≠ ∅}, c_k := deg_H(w_k) <= Δ_* = b, β := 2Δ_*|X|, a := 0.3|X|, second bound

**randomness:** Sample space {0,1}^m (Lean: ι → Bool for a Fintype ι) with the product law Π_k Bernoulli(p_k); nothing conditioned inside the lemma. At the use site: conditional on the earlier layers V_1..V_{i-1} of s3:lemL17s (fixed prefix of independent layers), the indicator vector of V_i on W.

**lean_shape:**

```lean
def EG.Spec.BBDStatement : Prop := ∀ (ι : Type v) [Fintype ι] (p : ι → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
  (Ψ : (ι → Bool) → ℝ) (b : ℝ) (c : ι → ℝ) (β a : ℝ),
  0 ≤ b → (∀ k, 0 ≤ c k ∧ c k ≤ b) → (∀ k (x : ι → Bool) (v : Bool), |Ψ (Function.update x k v) - Ψ x| ≤ c k) →
  0 < β → ∑ k, p k * (1 - p k) * c k ^ 2 ≤ β → 0 ≤ a →
  let μ := EG.FinDist.pi (fun k => EG.FinDist.bernoulli (p k) (hp0 k) (hp1 k))
  μ.prob {x | μ.expect Ψ + a ≤ Ψ x} ≤ Real.exp (-(a ^ 2) / (2 * (β + b * a / 3))) ∧
  μ.prob {x | Ψ x ≤ μ.expect Ψ - a} ≤ Real.exp (-(a ^ 2) / (2 * (β + b * a / 3)))
Lib transport corollaries: (i) any μ' : FinDist Ω, I : Ω → ι → Bool with μ'.map I = pi bernoulli ⇒ same bounds for Ψ ∘ I; (ii) IsRSubset V S ρ and W ⊆ S ⇒ the indicator vector (fun w : W => decide (w ∈ V ω)) has law pi (fun _ => bernoulli ρ).
```

**hazards:**

- **[risk] BBD-TRANSPORT.** The consumer (s3:lemL17s case (b)) does not have a product space on {0,1}^|W|: it has a p_*-random subset V_i (IsRSubset) inside a union of independent layers, conditioned on the earlier layers. The Lean use needs (i) the restriction lemma 'indicators of a ρ-random subset on W ⊆ S have the product Bernoulli law' (not in Lib: only IsRSubset.indepEvents exists), and (ii) Fubini over the layers. Budget these in s3; state BBD for an arbitrary Fintype index and prove the transport corollary here.
- **[note] BBD-UNREVIEWED.** New in v6 (R2), no clean-room review. I re-checked all steps: the identity Ψ_{k-1} = pΨ_k(·,1) + (1-p)Ψ_k(·,0), |Ξ_k| <= c_k, χ'' = (1-(1-u)e^u)/3, the division by 1-u/3 >= 1-ζ/3 > 0, the one-coordinate bound (cross terms cancel, p(1-p)^2 + (1-p)p^2 = p(1-p)), and the optimisation η = a/(β+ba/3) giving -a²/(2(β+ba/3)). Correct; m = 0 and a = 0 are fine.
- **[note] BBD-COORDS.** The manuscript inducts over the ordered coordinates 1..m (prefix sums over {0,1}^k); over a general Fintype ι use Fintype.equivFin or Finset induction on the set of revealed coordinates. 'Differ only in coordinate k' ↔ Function.update form (equivalent).
- **[note] BBD-CALC.** The analytic part needs 'derivative >= 0 on an interval ⇒ monotone' (Mathlib: monotoneOn_of_deriv_nonneg) and exp facts; no martingales. Choice b >= 0 matters only when some c_k = 0 for all k (then b could be negative otherwise); keep the hypothesis 0 <= b.

**effort:** ~850 Lean lines, difficulty 3/5 (Analytic inequality ~150, partial averages + induction ~450, tails ~100, transport corollaries ~150.).

### `s1:citHall` — cited result: Hall's theorem (systems of distinct representatives) (s1.tex:1173)

- **Manuscript referee status:** new in v6 (R4), a standard result; no referee yet
- **Formalization:** Mathlib: Finset.all_card_le_biUnion_card_iff_exists_injective (Mathlib/Combinatorics/Hall/Basic.lean); no Spec needed

**Statement (precise restatement).** FOR EVERY finite set J and finite sets T(a) (a ∈ J): if |∪_{a∈J'} T(a)| >= |J'| for every J' ⊆ J, then there is an injective χ : J → ∪_a T(a) with χ(a) ∈ T(a) for all a. (Used also contrapositively: an SDR fails to exist only if some J' violates Hall's condition.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| Hall (Mathlib) | (∀ s : Finset ι, s.card ≤ (s.biUnion t).card) ↔ ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x | Mathlib | yes (Mathlib) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none

**used_by:** s3:lemHB (index set E_X-arrows, slot sets T(a)); s7:lemWellDef(iii) (items at u, 3-subsets of [K]; contrapositive); s7:consRound(f)

**randomness:** none (in s7 applied inside a probability bound for a random family of lists).

**lean_shape:**

```lean
Use Mathlib directly: Finset.all_card_le_biUnion_card_iff_exists_injective (t : ι → Finset α) [DecidableEq α]. A thin EG wrapper with the manuscript's wording is optional (~20 lines).
```

**hazards:**

- **[note] HALL-TRUSTED.** Mathlib theorem: no trust issue and no Spec. Both directions are available (iff), which the s7 contrapositive use needs.

**effort:** ~20 Lean lines, difficulty 1/5.

### `s1:citHaxell` — cited result (with derivation): Haxell's condition for matchability [Hax95] (s1.tex:1184)

- **Manuscript referee status:** pub. (not yet checked against [Hax95]); derivation new in v6 (R3): no referee yet
- **Formalization:** Stage-α explicit Prop hypothesis (PLAN §1); stage β: formal proof (alternating trees)

**Statement (precise restatement).** FOR EVERY integer d >= 1 and EVERY finite hypergraph H on a vertex set A ⊔ B (disjoint) such that every edge e satisfies |e ∩ A| = 1 and |e ∩ B| <= d: IF for every A' ⊆ A and every Z ⊆ B with |Z| <= (2d-1)(|A'| - 1) there is an edge e with e ∩ A ⊆ A' and e ∩ Z = ∅ (vacuous for A' = ∅ because the bound is negative), THEN H has an A-saturating matching (pairwise disjoint edges covering every vertex of A). Derivation in the text: the form '|e ∩ B| <= d' follows from the form '|e ∩ B| = d' by padding every edge with private new B-vertices (edges {a} matched directly). The only application (s3:lemL9rho) verifies the hypothesis for every Z with |Z| < d²|A'| (d := h = ⌊4 ell_* L⌋), so any factor <= d² would do.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| hypergraph, A-saturating matching | Finset (Finset α) with A, B : Finset α; matching = subfamily of pairwise disjoint edges covering A | s1:citHaxell | NO: stated inline in the stage-α Prop (no new Defs needed) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — The padding derivation uses nothing else.

**used_by:** s3:lemL9rho (A := [r] (pair indices), B := E(G), edges {i} ∪ E(P), P ∈ Y_i)

**randomness:** none

**lean_shape:**

```lean
Recommended stage-α hypothesis = the weakest form the proof needs (a corollary of every quoted form of Haxell's theorem):
def EG.Spec.HaxellStatement : Prop := ∀ (α : Type) [DecidableEq α] (A B : Finset α) (H : Finset (Finset α)) (d : ℕ),
  1 ≤ d → Disjoint A B → (∀ e ∈ H, e ⊆ A ∪ B ∧ (e ∩ A).card = 1 ∧ (e ∩ B).card ≤ d) →
  (∀ A' ⊆ A, A'.Nonempty → ∀ Z ⊆ B, Z.card < d ^ 2 * A'.card → ∃ e ∈ H, e ∩ A ⊆ A' ∧ Disjoint e Z) →
  ∃ M ⊆ H, (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧ ∀ a ∈ A, ∃ e ∈ M, a ∈ e
(Published form for stage β: replace 'Z.card < d^2 * A'.card' by 'Z.card ≤ (2*d-1)*(A'.card-1)' -- implied, since d²|A'| - 1 - (2d-1)(|A'|-1) = (d-1)²|A'| + 2(d-1) >= 0.)
```

**hazards:**

- **[risk] HAX-TRUTH.** Stage-α hypotheses are trusted. The manuscript itself says the factor 2d-1 (and whether edges meet B in 'at most' or 'exactly' d vertices) has NOT been checked against [Hax95]. A false locked HaxellStatement would make every stage-α result vacuous. Mitigation (recommended): lock the d²-form above, which is implied by the standard statement (Haxell 1995: |e ∩ B| <= r-1, bound (2r-3)(|A'|-1)) and by any variant with factor <= d², and still suffices for s3:lemL9rho; and check the paper before stage β.
- **[risk] HAX-NATSUB.** With ℕ subtraction, (2d-1)(|A'|-1) = 0 for A' = ∅, which would demand an edge with e ∩ A ⊆ ∅: the hypothesis becomes unsatisfiable, the Prop vacuously true and useless. Quantify over A'.Nonempty (as above) or work in ℤ.
- **[note] HAX-HYPERGRAPH.** Hypergraph = Finset (Finset α): distinct paths with the same edge set give one hyperedge (harmless: the matching picks one path per index). The application's vertex type is ι ⊕ Sym2 V with A := image inl, B := image inr of E(G).
- **[note] HAX-PADDING.** The padding derivation (|e∩B| = d ⇒ <= d) is only needed if the locked form uses '= d'; with the '<= d' form it is unnecessary.
- **[note] HAX-BETA.** Stage β discharge (Haxell's alternating-tree proof) ~1500-2500 lines, difficulty 4-5; outside P2.

**effort:** ~60 Lean lines, difficulty 2/5 (Spec + the implication published-form ⇒ d²-form (~40). Stage-β proof not counted.).

### `s1:citEuler` — cited result (with derivation): T-joins and Euler circuits (s1.tex:1246)

- **Manuscript referee status:** standard
- **Formalization:** (a) Lib theorem, stated for forests of an edge-indexed multigraph; (b) stage-α Euler hypothesis (PLAN §1) + Lib derivation for multigraphs with loops; (c) not used -- do not formalize

**Statement (precise restatement).** (a) FOR EVERY connected graph H, EVERY T ⊆ V(H) with |T| even and EVERY spanning tree S of H: there is J ⊆ E(S) whose set of odd-J-degree vertices is exactly T (a T-join). (b) EVERY connected graph or multigraph (loops allowed, a loop adds 2 to the degree) in which every vertex has even degree has a closed trail using every edge exactly once. (c) A graph with all degrees even is an edge-disjoint union of cycles; a loopless digraph with d⁺ = d⁻ everywhere is an arc-disjoint union of directed cycles.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| MGraph | edge-indexed multigraph with loops; deg counts a loop twice | s1:convGraphs(a); s5:lemParent | NO (new Defs) |
| forest / spanning forest of an MGraph | edge subset without cycles (no loops, no parallel pair), one tree per component | s5:lemParent Step 3 | NO |
| T-join | J ⊆ E with {v : deg_J(v) odd} = T | s1:citEuler(a) | NO: EG.IsTJoin (or inline) |
| closed trail / Euler circuit | cyclic list of distinct edges with orientations, consecutive ends matching, using every edge once | s1:citEuler(b); s5:lemParent (cyclic sequence (a_1..a_k) of oriented arcs, k >= 1) | NO (MGraph layer); Mathlib has SimpleGraph.Walk.IsEulerian for simple graphs |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — (a) rooted-subtree parity; (b) Euler's theorem; (c) greedy cycle extraction. Pointer to s1:citCor22 (Lovász only through Cor 22) is not a dependency.

**used_by:** s6:lemPAR ((a) on a spanning tree of a connected component C' of a simple bipartite graph); s5:lemParent Step 3 ((a) on a spanning forest F_i of the MULTIGRAPH UQ_{l,c,i} with loops, using T_i ⊆ E(F_i) and |T_i| <= |E(F_i)| <= nu_l - 1; (b) on each component of UQ_{l,c,i} - T_i, a multigraph with loops); (c): no use by label (s6:lemGATE proves its own directed-cycle decomposition)

**randomness:** none

**lean_shape:**

```lean
(a) theorem EG.exists_tJoin_of_forest {N E : Type*} [DecidableEq N] [DecidableEq E] (ends : E → Sym2 N) (S : Finset E) (hS : EG.IsForest ends S) (T : Finset N)
    (hT : ∀ K, EG.IsComponentOf ends S K → Even (T ∩ K).card) : ∃ J ⊆ S, ∀ v, Odd (EG.degOn ends J v) ↔ v ∈ T
  plus FGraph corollary: connected H, spanning tree S ⊆ H.edges, Even T.card ⇒ ∃ J ⊆ S, odd-degree set = T.
(b) stage-α: def EG.Spec.EulerStatement : Prop := ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, Even (G.degree v)) → (∀ u v, 0 < G.degree u → 0 < G.degree v → G.Reachable u v) → ∀ u, 0 < G.degree u → ∃ w : G.Walk u u, w.IsEulerian
  (NOT '∃ (u : V) (w : G.Walk u u), ...': that form is FALSE for V = ∅, see hazard EUL-EMPTY.)
  and Lib: EG.MGraph.exists_eulerCircuit (M : EG.MGraph N E) (hconn) (heven : ∀ v, Even (M.deg v)) : ∃ c : List (E × Bool), closed trail using every edge of M exactly once -- via subdivision (loop ↦ triangle on 2 new vertices; every other edge ↦ path of length 2 through a new vertex) and transport back.
(c) not formalized.
```

**hazards:**

- **[risk] EUL-MULTI-USE.** Definition-vs-use mismatch: (a) and (b) are stated for (simple) connected graphs, but s5:lemParent applies them to the multigraph UQ_{l,c,i} with loops and parallel edges (a T-join inside a spanning FOREST, with the size bound |T_i| <= nu_l - 1, then Euler circuits of multigraph components, including a single loop, k = 1). The mathematics is fine (a forest of a multigraph is a simple forest; Euler holds for multigraphs with loops), but the Lean statements must be for edge-indexed multigraphs/forests; FGraph cannot express UQ. Requires EG.MGraph first.
- **[risk] EUL-STAGEALPHA.** PLAN lists Euler as a stage-α hypothesis. Decide its form before locking: for Mathlib SimpleGraph (small trusted statement, matches pending Mathlib PRs #41524/#41631, but then the multigraph-with-loops version needs a ~800-line subdivision derivation) or directly for multigraphs (larger trusted surface, easier to get wrong). A mis-stated stage-α Euler Prop (e.g. requiring Connected on all vertices while isolated vertices exist, or allowing zero-edge graphs incorrectly) is either false (vacuous theorem) or unusable. Recommendation: SimpleGraph form with connectivity only among positive-degree vertices, as above.
- **[risk] EUL-EMPTY.** Concrete trap for the stage-α Euler Prop: the natural shape '(all degrees even) → (edges connected) → ∃ (u : V) (w : G.Walk u u), w.IsEulerian' is FALSE when V is empty (hypotheses vacuous, no u exists), so locking it would make the stage-α theorem vacuous. Quantify the start vertex (∀ u with 0 < deg u, ∃ Eulerian closed walk at u) or assume [Nonempty V]. Every stage-α Prop needs such a degenerate-case audit (empty vertex set, no edges, d = 1, A = ∅) plus a non-vacuity test in EGTest.
- **[note] EUL-TREE.** Spanning trees/forests: Mathlib has trees for SimpleGraph but not for edge-indexed multigraphs; the forest version of (a) is simplest by induction on edges (remove a leaf edge) rather than via rooted subtrees as in the text.
- **[note] EUL-C-UNUSED.** (c) is used nowhere by label; do not formalize (saves ~300 lines). Its directed part would allow 2-cycles for general digraphs; not an issue since unused.

**effort:** ~1300 Lean lines, difficulty 4/5 ((a) forest T-join ~400; MGraph basics ~200; (b) subdivision derivation from the stage-α SimpleGraph Euler ~700.).

### `s1:defConstants` — definition: the constants (s1.tex:1276)

- **Manuscript referee status:** x0 (collected from refereed sources); (ii) changed and former item (vii) removed in v6 (R1): no referee yet
- **Formalization:** Defs (new): EG/Defs/Constants.lean (absolute constants) + definitions placed after the s4 and s7 Defs (N0Cond, C0, cEG)

**Statement (precise restatement).** (i) eps := 2^-5, sigma := 100, C' := 103, A := 105. (ii) N0 is any number with N0 >= 2^40 such that every size condition recorded in the proofs of s4:lemTPV, s4:lemPV, s4:thmVXp (explicit inequalities in N with L := log_2 N, e.g. (i) L >= 2^10, (ii) N >= L^3, (iii) 4 beta <= L, (iv) eta_•(N) <= 1/100) holds for EVERY N >= N0; each is an eventuality in N, so such N0 exists (finitely many eventualities); only existence is used. The s5 lemmas carry n >= N0 and use it only to apply these three statements; s3:lemL15p and s3:thmT16s need no size bound. (iii) D_* is any constant satisfying (Gamma1)-(Gamma4) of s1:condGamma; existence by s7:lemGammaSat. (iv) eps1(D_*), eps2(D_*) are the explicit functions of s7:propCost and s7:lemUHsplit; theta_Q := eps2(D_*). (v) C0 := D_*/2 + 1085 + eps1(D_*) (eps1 counted once); by (Gamma4) C0 <= D_*/2 + 1091. (vi) c_EG := max{C0/(1 - 2 theta_Q), N0/2}. (vii) eps_D: generic shorthand inside proofs only (always an explicit expression in D_*, sigma, C', A tending to 0).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| absolute constants | EG.epsC := 2^(-5:ℤ), EG.sigmaC := 100, EG.Cp := 103, EG.Aexp := 105 | (i) | NO (new EG/Defs/Constants.lean) |
| size predicates of the vortex runs | explicit conjunctions of the size conditions (i)-(iv) with eta_TPV, eta_PV, eta_VX | proofs of s4:lemTPV (s4.tex:202), s4:lemPV (s4.tex:459), s4:thmVXp (s4.tex:673) | NO (s4 blueprint must define EG.S4.TPVSize/PVSize/VXSize) |
| N0Cond | 2^40 ≤ N0 ∧ ∀ N ≥ N0, TPVSize N ∧ PVSize N ∧ VXSize N | (ii) | NO |
| eps1, eps2 | explicit (s7.tex:1239, s7.tex:1072), built from epsA (s2:lemTower(e)), epsU = 2462 (log2 D)^-205 (s5:lemExpect), epsK = epsChain (s5:lemParent/lemKRED), epsCONC (s6:thmCONCL(iv), uses log*), epsX (s7:lemEXprime), F(x) = (3184 + 30400 log2 x) x^-90.2 (s7:lemUHsplit(iv)) | (iv) | NO (s7 layer) |
| C0, cEG | as (v), (vi) | (v),(vi) | NO (s7 layer); EG.Spec.HIStatement already inlines max (C/(1-2ϑ)) (N₀/2) |

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none — Forward pointers (not dependencies): s4:lemTPV, s4:lemPV, s4:thmVXp, s3:lemL15p, s3:thmT16s, s1:condGamma, s7:lemGammaSat, s7:propCost, s7:lemUHsplit. In Lean these become DEFINITIONAL dependencies of N0Cond / GammaCond / cEG.

**used_by:** s2:defWitness, s2:defHBtp (eps, sigma, C', A); s3 (eps); s4:lemTPV/lemPV/thmVXp (N0); s5 setting (n >= N0); s7:thmHI, s7:lemGammaSat, s7:thmMainProof

**randomness:** none

**lean_shape:**

```lean
-- EG/Defs/Constants.lean (no dependencies)
def EG.epsC : ℝ := 2 ^ (-5 : ℤ)
def EG.sigmaC : ℕ := 100
def EG.Cp : ℕ := 103
def EG.Aexp : ℕ := 105
-- after the s4 Defs
def EG.N0Cond (N0 : ℝ) : Prop := 2 ^ 40 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N → EG.S4.TPVSize N ∧ EG.S4.PVSize N ∧ EG.S4.VXSize N
theorem EG.exists_N0 : ∃ N0, EG.N0Cond N0     -- from (∀ᶠ N in atTop, TPVSize N ∧ PVSize N ∧ VXSize N) and Filter.eventually_atTop
-- after the s7 Defs
def EG.C0 (D : ℝ) : ℝ := D / 2 + 1085 + EG.eps1 D
def EG.cEG (N0 D : ℝ) : ℝ := max (EG.C0 D / (1 - 2 * EG.eps2 D)) (N0 / 2)
Recommended s4/s5 Spec style: s4 lemmas take the explicit predicate at N = |Z| (hypothesis EG.S4.TPVSize Z.card), s5/s6/s7 statements take N0 with EG.N0Cond N0 and n ≥ N0.
```

**hazards:**

- **[risk] CONST-N0-INPROOF.** (ii) defines N0 through thresholds that are listed only inside the PROOFS of three s4 lemmas ('size conditions', including the o(1) functions eta_TPV/eta_PV/eta_VX defined in those proofs). A Lean definition of N0Cond needs these as named explicit Defs, so the s4 statements must expose them (hypothesis 'TPVSize |Z|') -- a statement-shape decision for the s4 blueprint. Alternative: s4 Specs with an existential threshold (∀ᶠ N in atTop), which makes N0 non-explicit but equally faithful.
- **[risk] CONST-LAYERING.** Forward definitional dependencies: N0Cond needs s4 Defs; (iii)/(iv)/(v)/(vi) need s3 (COL-JV column 3), s5 (epsU, epsK), s6 (epsCONC), s7 (epsX, F, eps1, eps2). Lean modules cannot reference later modules, so constants must be split: absolute constants early (Defs/Constants), N0Cond after s4, GammaCond/C0/cEG after s7. Statements of s2-s6 must NOT take GammaCond (would import s7); they take only the items they use (Gamma1core, Gamma2a, Gamma3, N0Cond).
- **[note] CONST-NONNEG.** (v) C0 >= D_*/2 (used in s7:thmMainProof and HI) needs eps1(D) >= 0; theta_Q >= 0 is needed by HI. Both require D large (log log D > 0 etc.): prove from Gamma1core.
- **[note] CONST-REALN0.** N0 as a real (EG.Spec.HIHyp uses N₀ : ℝ); 'n >= N0' is (n : ℝ) ≥ N0. The claim 'N0 depends only on sigma, C', A' has no Lean content (existential choice).
- **[note] CONST-EXPLICIT.** (vii): every named small quantity must have an explicit formula; checked: epsU (s5.tex:140), epsChain (s5.tex:227), eps2 (s7.tex:1072), eps1 (s7.tex:1239) are explicit. The Gamma4 bullet list in s1:condGamma is descriptive only; Lean must use the s7 formulas.

**effort:** ~200 Lean lines, difficulty 2/5 (Definitions and small lemmas (exists_N0, nonnegativity, C0 ≤ D/2 + 1091 from Gamma4).).

### `s1:remOrder` — remark: order of the constants (s1.tex:1325)

- **Manuscript referee status:** x0 (as for s1:defConstants)
- **Formalization:** no statement; realised by the quantifier structure of the Lean proof

**Statement (precise restatement).** The constants are fixed in the order: (1) sigma, C', A, eps; (2) N0; (3) D_*; (4) eps1(D_*), eps2(D_*) = theta_Q, C0; (5) c_EG. Nothing earlier depends on anything later. C0 and theta_Q depend on D_* only (not on G, n, the run, the designation or c_EG); c_EG enters only as the constant c of s7:thmHI, applied last (non-circular). Every condition on N0 (resp. D_*) is an eventuality in that constant given the earlier ones (Table s1:tabOrder).

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): `s1:defConstants`

**deps_from_proof:** s1:defConstants — Forward pointers s7:thmHI, s1:condGamma, s1:tabOrder are descriptions.

**used_by:** -

**randomness:** none

**lean_shape:**

```lean
No declaration. Enforced by: EG.exists_N0 : ∃ N0, EG.N0Cond N0 (independent of D); s7:lemGammaSat : ∀ N0, ∀ᶠ D in Filter.atTop, EG.GammaCond N0 D; EG.eps1 EG.eps2 : ℝ → ℝ (functions of D only); EG.Spec.HIStatement quantifies C, ϑ before forming c.
```

**hazards:**

- **[note] ORDER-AUTO.** Lean term structure enforces the order automatically if eps1/eps2 are functions of D only and c_EG appears only in HI; the statement reviewers should check that no s2-s7 Spec takes c_EG (or C0/theta_Q as free parameters with conditions depending on G).

**effort:** ~0 Lean lines, difficulty 1/5.

### `s1:condGamma` — condition: the galactic conditions on D_* (Gamma1)-(Gamma4) (s1.tex:1349)

- **Manuscript referee status:** x0; R6: no referee yet; where (Gamma2)(b),(c) are proved corrected in v6 (R7): no referee yet
- **Formalization:** Defs (new): Gamma1Items/Gamma1core (early), Gamma1 with item (f) (s3 layer), Gamma2a, Gamma3, Gamma4 and GammaCond (s7 layer); satisfiability = s7:lemGammaSat

**Statement (precise restatement).** (Gamma1) D_* > 2, and FOR EVERY real mu >= log2 log2 D_*, with lambda := 2^mu: (a) mu >= 2^8; (b) 2^mu >= 2^14 A mu^3; (c) 2A log2(A mu) <= 1.6 mu; (d) 2 log2 mu + 8 <= mu; (e) (G*) lambda^36 >= 2^240 (A mu)^{46A}; (f) every column-3 inequality of every row of the COL-JV table s3:tabCOLJV holds at lambda, with Mbar := (A mu)^{2A}, kbar := 192 lambda^3 + (4/3) Mbar^2 (18 explicit inequalities; row 13 = (G*), row 12 = (c)). Consequences: (a)-(f) hold at mu = log2 lambda_r for every round r <= R (d_r >= D_*), at mu = log2 log2 d (d >= D_*) and at mu = log2 D_*; log2 D_* >= 2^256. (Gamma2) (a) D_* >= 2^117; (b) P_{l-2}/2 >= M_l log^4 M_l for 3 <= l <= R; (c) every per-ancestor failure probability of s3:lemCOL and s5:lemE1 is <= |V(Y)|^-2. (b),(c) are consequences of (Gamma1),(Gamma3), proved in s2:lemTower(b), s3:lemCOL, s5:lemE1(b),(c); none of these proofs uses (b) or (c). (Gamma3) (log2 D_*)^{C'} >= 2 N0. (Gamma4) eps1(D_*) <= 6 and theta_Q = eps2(D_*) <= 1/4 (eps1, eps2 explicit, s7:propCost, s7:lemUHsplit). Remarks: each condition is an eventuality in D_* once N0 is fixed (s7:lemGammaSat); order of choice (Table s1:tabOrder); off-route conditions (G), (G+), (G_XL) never assumed.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| Gamma1Items mu | conjunction of items (a)-(e) at mu (lambda = (2:ℝ)^mu rpow; A = 105) | (Gamma1)(a)-(e) | NO |
| COL-JV column 3 at mu | 18 explicit inequalities in mu, lambda, Mbar, kbar | s3:tabCOLJV (via s3:lemCOLJV, s3:lemCOLJVev) | NO (s3 blueprint) |
| Gamma1core, Gamma1, Gamma2a, Gamma3, Gamma4, GammaCond | as stated; Gamma2(b),(c) excluded (lemmas) | s1:condGamma | NO |
| eps1, eps2 | see s1:defConstants | s7:propCost, s7:lemUHsplit | NO |
| round data d_r, lambda_r, M_l, P_l, R, ancestors Y | hierarchy parameters (only in the consequences / Gamma2(b),(c)) | s2:defHBtp, s2:defAncestors | NO (s2 blueprint) |

**deps_declared** (manuscript \deps): `s1:defConstants`, `s1:remOrder`

**deps_from_proof:** s1:defConstants; s1:remOrder — Forward (definitional) references: s3:tabCOLJV (item (f)), s7:propCost and s7:lemUHsplit (Gamma4), s7:lemGammaSat (satisfiability), s2:lemTower(b), s3:lemCOL, s5:lemE1 (where Gamma2(b),(c) are proved), s2:defHBtp (d_r).

**used_by:** s2 (Gamma1 x7, Gamma2 x3: lemCap uses (a); propDegRec, lemLacunary, lemTower, propStructure); s3 (Gamma1 x4, G* x1, lemCOLJV, lemCOL); s4 (Gamma3 x4); s5 (Gamma1 x8, Gamma3 x3, Gamma4 x2); s6 (Gamma1 x5, Gamma3 x2); s7 (Gamma1..Gamma4; lemGammaSat)

**randomness:** None in the conditions. (Gamma2)(c) mentions failure probabilities of random stage-1 colourings (s3:lemCOL) and zones (s5:lemE1) -- this is exactly why (c) cannot be a condition on D_*.

**lean_shape:**

```lean
def EG.Gamma1Items (μ : ℝ) : Prop :=
  (2:ℝ) ^ 8 ≤ μ ∧ 2 ^ 14 * 105 * μ ^ 3 ≤ (2:ℝ) ^ μ ∧ 2 * 105 * Real.logb 2 (105 * μ) ≤ 1.6 * μ ∧
  2 * Real.logb 2 μ + 8 ≤ μ ∧ 2 ^ 240 * (105 * μ) ^ (46 * 105) ≤ ((2:ℝ) ^ μ) ^ 36
def EG.Gamma1core (D : ℝ) : Prop := 2 < D ∧ ∀ μ : ℝ, Real.logb 2 (Real.logb 2 D) ≤ μ → EG.Gamma1Items μ
def EG.Gamma1 (D : ℝ) : Prop := EG.Gamma1core D ∧ ∀ μ : ℝ, Real.logb 2 (Real.logb 2 D) ≤ μ → EG.S3.COLJVcol3 μ   -- s3 layer
def EG.Gamma2a (D : ℝ) : Prop := 2 ^ 117 ≤ D
def EG.Gamma3 (N0 D : ℝ) : Prop := 2 * N0 ≤ Real.logb 2 D ^ 103
def EG.Gamma4 (D : ℝ) : Prop := EG.eps1 D ≤ 6 ∧ EG.eps2 D ≤ 1 / 4   -- s7 layer
def EG.GammaCond (N0 D : ℝ) : Prop := EG.Gamma1 D ∧ EG.Gamma2a D ∧ EG.Gamma3 N0 D ∧ EG.Gamma4 D
-- s7:lemGammaSat: theorem EG.gammaSat (N0 : ℝ) : ∀ᶠ D in Filter.atTop, EG.GammaCond N0 D
-- consequence lemmas: Gamma1core D → d ≥ D → Gamma1Items (logb 2 (logb 2 d)); Gamma1core D → Gamma1Items (logb 2 D); Gamma1core D → 2^256 ≤ logb 2 D.
```

**hazards:**

- **[risk] GAM-2BC.** (Gamma2)(b),(c) are listed as conditions on D_* but are not predicates of D_*: (b) quantifies over the rounds of a run (M_l, P_l, R), (c) over failure probabilities of s3:lemCOL and s5:lemE1. They must be formalized as LEMMAS (s2:lemTower(b), s3:lemCOL, s5:lemE1(b),(c)), never as fields of GammaCond; otherwise GammaCond would depend on the s3/s5 probability spaces (module cycle) and s7:lemGammaSat would have to prove probabilistic statements. The manuscript confirms no proof uses (b),(c) as hypotheses.
- **[risk] GAM-1F-FORWARD.** (Gamma1)(f) is a forward pointer to 18 inequalities of s3:tabCOLJV. Split Gamma1 into Gamma1core (items (a)-(e), defined early, usable by s2) and the (f) part (s3 layer). Each s2 statement citing Gamma1 must be checked to use only (a)-(e) (s2:propDegRec, s2:lemLacunary, s2:lemTower, s2:propStructure).
- **[risk] GAM-4-FORWARD.** (Gamma4) depends on eps1, eps2, which collect explicit functions from s2 (epsA), s5 (epsU, epsK), s6 (epsCONC, needs log*), s7 (epsX, F with real exponent -90.2); these must be Defs with exactly the s7 formulas (s7.tex:1072, 1239). The bullet list in the condition (coefficients 169/12, 3/12, 291.9/D, 363.6/D) is only a summary and must not be used as the definition.
- **[note] GAM-NUMERICS.** Never evaluate: (e) has (105 mu)^4830 and (a) forces D_* >= 2^{2^256}; all uses must be symbolic/eventual (CONVENTIONS: no norm_num on galactic constants, no native_decide). The eventuality proofs are s7:lemGammaSat and s3:lemCOLJVev.
- **[note] GAM-RAY.** Gamma1 is a condition on the whole real ray mu >= log2 log2 D (upward closed in D). In Lean logb is total; keep 2 < D so log2 log2 D > 0, and prove the transfer lemmas (mu = log2 lambda_r >= log2 log2 D_* from d_r >= D_*; t >= log2 t for t > 0).
- **[note] GAM-ORDER.** Gamma3 involves N0: GammaCond N0 D, quantified ∀ N0, ∀ᶠ D (N0 chosen first); no condition involves c_EG.
- **[note] GAM-UNREVIEWED.** Rewritten in v6 (R6) and (R7), no clean-room review; the logic (eventualities, non-circularity) checks out, but its correctness depends on s3:lemCOLJVev and s7:lemGammaSat.

**effort:** ~250 Lean lines, difficulty 2/5 (Definitions ~120, transfer/consequence lemmas ~130. Satisfiability belongs to s7:lemGammaSat and s3:lemCOLJVev.).

### `s1:remNotUsed` — remark: not used on this route (s1.tex:1537)

- **Manuscript referee status:** --
- **Formalization:** no content; exclusion list for the blueprint

**Statement (precise restatement).** Not used anywhere: zone sets ZS and rootedness, routes XL, QI, QI+, NZ functionals, SP_delta, HC_delta; the star split of JS-LC and tau'_l; VX-parts (V = ∅); HALL, HALL' and the 'corrected Theorem JV'; COLL, RAND-JV+, payments (D5'), (D7'), RULE, W, 32/15; RH, Theorem C, calibration families; RT2-I15/I16 bookkeeping.

**defs_needed.**
 none.

**deps_declared** (manuscript \deps): none

**deps_from_proof:** none

**used_by:** -

**randomness:** none

**lean_shape:**

```lean
none
```

**hazards:**

- **[note] NOTUSED-EXCLUDE.** The usesgen/blueprint must create no nodes for these items, and conditions (G), (G+), (G_XL) must never be assumed; HALL/HALL' must not be confused with s1:citHall (Mathlib Hall). VX-parts: V = ∅ throughout, so s6/s7 Specs need no VX-part case.

**effort:** ~0 Lean lines, difficulty 1/5.
