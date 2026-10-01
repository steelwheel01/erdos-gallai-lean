# P2-U formalization blueprint: chunk s7a (s7: pools, candidates, the randomness schedule, the JV+* round step, well-definedness, MULT, simplicity, the lift, Lemma CC, ultra hubs)

Manuscript: `proofs/manuscript/s7.tex` lines 1-879 (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s7a.json` (same content, one object per label, same field names as `nodes_s1.json` / `nodes_s2a.json`). Line numbers refer to `s7.tex`. Existing Lean names were checked against `formal/EG/**` (EG.FGraph with `edge_verts`/`loopless`, EG.Obj, EG.IsDecomp, EG.fnum, EG.FinDist with `pi`/`prod`/`uniform`/`cond`/`expect`, EG.FinDist.iIndepFun, the Chernoff lemmas `chernoffGen_lower_half` / `chernoffGen_tail_exp`, the Markov lemmas `half_le_prob_le_four_mul_expect_and` / `two_thirds_le_prob_le_three_mul_expect`, EG.Spec.HIHyp); all other names are proposals. The s2 run API (`HB.Run`, `run.Valid`, `run.R`, `run.Mr`, ancestors by address) is the one proposed in `blueprint_s2a.md`; s3/s5/s6 objects (COL-JV colourings, zones, designation, lending statuses, J_l) are referenced by the names their blueprints will fix.

Every proof in this chunk was re-derived line by line, including all numerical constants (Cuckoo SDR series, the constants 44.7/29.8 of Lemma CC, 312.36 + 7.5 < 320 of the ultra-hub bound, (eqCandExp), the palette and list bounds). **No mathematical error was found.** The hazards are formalization hazards: two manuscript decisions (blockers) — M_l must be an integer (inherited from s2a), and the text must say which randomness each "fixed rule" of the round step may read (otherwise Lemma CC, the ultra-hub lemma and Cuckoo SDR are false for some admissible rules) — and a cluster of design risks around how "the past" and "given the lists" are encoded.

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s7:defPool` | definition | Defs | 150 | 2 | risk (POOL-LAW-NEEDS-GAMMA) |
| `s7:defCand` | definition | Defs | 120 | 2 | risk (CAND-MEAN-DEF) |
| `s7:lemCand` | lemma | Spec | 400 | 3 | risk (CAND-GAMMA-IMPLICIT) |
| `s7:defSchedule` | definition | Defs | 350 | 3 | blocker (SCHED-M-INTEGER) |
| `s7:consRound` | construction | Defs | 1000 | 4 | blocker (ROUND-M-INTEGER) |
| `s7:lemWellDef` | lemma | Spec | 1000 | 4 | risk (WD-SDR-UNIONBOUND) |
| `s7:lemMULT` | lemma | Spec | 180 | 2 | risk (MULT-J1) |
| `s7:lemSimple` | lemma | Mostly definitional with the tagged encoding | 120 | 2 | note (SIMPLE-TAGGED-DEFINITIONAL) |
| `s7:lemLift` | lemma | Spec | 900 | 4 | risk (LIFT-CYCLE-WF) |
| `s7:lemCC` | lemma | Spec | 650 | 4 | risk (CC-CONDITIONING) |
| `s7:lemUltra` | lemma | Spec | 450 | 3 | note (ULTRA-NUMERICS) |

Estimated new Lean for this chunk: **~5320 lines**. Hazards: 3 blocker entries (M_l ∈ ℕ, inherited from s2a HB-M-INTEGER, in two nodes; the argument types of the fixed rules of the round step, ROUND-RULE-DEPENDENCE), 16 risks, 59 notes. No mathematical error found; all constants re-derived.

## 2. Cross-cutting decisions proposed for the integrator

- **M_l ∈ ℕ (blocker, inherited from s2a HB-M-INTEGER).** s7 needs the sets [3M_l] (PAR palette) and [4M_l] (HUB colours; eta_h is a bijection of [4M_l]; zeta_{h,u} a 3-subset of [4M_l]). The s2a proposal (R2): M_l := ⌈max(2^40, 2^16 T_l log^4 T_l)⌉ was re-checked against every s7a inequality that involves M_l: M_l >= 2^40, K = 4M_l >= 10^4 (Cuckoo), 3k_h <= 4M_l (needs M_l >= 21/4), Hcd_l >= 2^10 M_l^10 (COL-JV row 11, slack enormous), M_l <= lambda_{l-2}^{1.6} (slack enormous). All survive the ceiling. RoundInput.M is then a natural number.
- **The past is a parameter; no joint law over rounds (SCHED-PAST-PARAMETER).** Round-level Specs (WellDef(iii), CC, Ultra, and later Pay(c), UHsplit(ii)) are stated `∀ I : RoundInput V, I.Valid → ∀ R : Rules I, R.Valid → …` with `roundLaw = uniform (Lists × Orders)`. "E[·|Past_l]" is `(roundLaw …).expect`, "E[·|Past_l, lists]" is `(ordersLaw …).expect` with `L : Lists` fixed. Markov (c) and "xi_l is fresh" become definitional; s7:lemOneOutcome picks outcomes sequentially by existence (PLAN decision 3).
- **RoundInput interface (ROUND-INPUT-INTERFACE).** The past enters only through an abstract record (graph, M_l, lambda_{l-2}, ancestors with round/vertex set/LJV class/lend-goodness, pool with pool round, the four role sets, the class map, JV-bad, the four J-classes) and a `Valid` predicate listing exactly: M >= 2^40; Hcd >= 2^10 M^10; roles pairwise disjoint (J3); typed endpoints of Jlost/Jhub/Jfr/Jpar and J ⊆ E(G); **J1 aggregated over all parts**; J2 (<= M-1 J-edges at every non-hub vertex, |J| <= n(M-1)); classes of round in [1, l-2] containing their port; LJV classes inside their ancestor, pairwise disjoint, disjoint from J; ports' classes lend-good; JV-good ports have |Cand| >= Hcd; pool ⊆ V(G). Hcd and Cand are *defined* from the fields (Hcd := lam^95/(8M^2); Cand := pool ∩ {poolRound = round of class, uw ∈ LJV}). s7:thmJVps needs an instantiation lemma `RoundInput.ofPast_valid` (from s6:lemJplus, s6:defLending, s7:lemCand, s2:propStructure) — review it together with the s6 blueprint.
- **Fixed rules with restricted arguments (blocker ROUND-RULE-DEPENDENCE; T0 wording).** The probabilistic lemmas are false for rules that look at the orders. Proposed manuscript sentence for s7:consRound: "Every fixed rule and fixed order below is a function of Past_l and, from step (d) on, of the lists; none depends on the orders ≺_u." Lean: a `Rules I` structure whose fields have exactly these argument types (pairing/colouring/grouping: past; SDR/(e1) order/(e2) order: past + `Lists`; rank order and Dec_l: arbitrary), and every Spec is `∀ R, R.Valid → …` (PLAN decision 7).
- **Total definitions with fallbacks (ROUND-TOTALITY).** Greedy colouring, lists, (e1), (e2), Dec_l are total (Option/defaults/Classical.choose); s7:lemWellDef states that no fallback is taken. No proof terms inside definitions.
- **Pool law is total (POOL-LAW-NEEDS-GAMMA).** `poolLabelLaw` uses a `dite` fallback (Dirac at ⊥) when the mass exceeds 1; `poolMass_le_one` is proved under Gamma.
- **JV-bad threshold in closed form (CAND-MEAN-DEF; T0).** `candMean := q_l pi_{l,r} p_Y deg_{H_Y}(u)`, proved equal to the stage-1 expectation in s7:lemCand(ii). Keeps stage-2 statuses independent of the s3/s5 law definitions.
- **Quotient encoding (ROUND-LAYERS-ENCODING).** No general MGraph: layer edges are indexed by PAR objects / coloured hub items; ranks by any order; `Q_l : FGraph (QVert V)` with `QVert V := (P|H) × κ × ι × side × V`, `verts :=` endpoints of edges. `Q_l` feeds EG.Spec.HIHyp directly (each Q_i on its own vertex type).
- **Random families indexed by ↥G.verts** (EG.Spec.HIHyp has no `Fintype V`).
- **New probability infrastructure (SCHED-UNIFORM-LEMMAS, ~300-400 lines, EG/Lib/Prob/Uniform.lean):** uniform on a product = product of uniforms; image of a fixed k-set under a uniform permutation is a uniform k-subset; the i-th element of a fixed set in a uniform random order is uniform; conditioning a product law on a product event factorizes; total expectation over the atoms of a finite indicator family.
- **Modules.** Defs: `EG/Defs/Quot/Pool.lean` (defPool, defCand), `EG/Defs/Quot/Schedule.lean` (Stage1, stage1Law, Lists, Orders, roundLaw), `EG/Defs/Quot/Round.lean` (RoundInput, Rules, the construction, goodXi). Specs: `EG/Spec/Quot/{Pool, Cand, WellDef, MULT, Simple, Lift, CC, Ultra}.lean`. Proofs mirror them; `EG/Proof/Quot/Cuckoo.lean` for WellDef(iii).
- **Undeclared dependencies found in proofs** (for msreport): s7:defPool uses s2:defHBtp and s1:condGamma (D_* > 2); s7:lemCand uses s7:defSchedule, s2:defAncestors, s6:defDesign, s1:condGamma (via s3:lemCOLJV); s7:consRound uses s6:defLending, s2:defAncestors, s3:defCOL, s1:defObject and forward s7:lemWellDef; s7:lemWellDef uses s7:defSchedule, s2:defHBtp; s7:lemMULT uses s6:defDesign, s2:defAncestors; s7:lemLift uses s6:defLending, s6:defDesign, s1:defObject; s7:lemCC uses s7:lemMULT (rank argument) and s7:defSchedule; s7:lemUltra uses s7:defSchedule. Declared but not logically used: s4:lemTPV, s4:lemPV, s4:thmVXp, s5:lemChild, s5:lemDemoted in s7:defSchedule (pointers to stage-3 good events).
- **Effort.** ~5,320 Lean lines for the chunk (Defs ~1,300 incl. the round construction; Lib ~350; proofs ~3,650). Critical path: RoundInput/Rules design → round construction → WellDef(iii) (Cuckoo) and Lift(ii) (cycle lifting) → CC conditioning.

## 3. Hazard index (all nodes, most severe first)

| severity | node | hazard | description |
|---|---|---|---|
| blocker | `s7:defSchedule` | SCHED-M-INTEGER | Inherited from s2a HB-M-INTEGER: the round variables are bijections of [4M_l], 3-subsets of [4M_l] (and PAR colours [3M_l] in s7:consRound). These sets exist only if M_l ∈ ℕ, while (R2) defines M_l = max(2^40, 2^16 T_l log^4 T_l), in general irrational. The Lean types Perm (Fin K), Fin (3*M) require the manuscript decision proposed in s2a (M_l := ⌈...⌉ ∈ ℕ); the s7 inequalities re-checked in this chunk (M_l >= 2^40, M_l <= lambda_{l-2}^{1.6} with slack, 3k_h <= 4M_l for M_l >= 21/4, K = 4M_l >= 10^4) are unaffected by the ceiling. Fallback (K^HUB := ⌈4M_l⌉, PAR palette ⌈3M_l⌉) would require re-checking lemWellDef(i),(ii) and lemUltra(iii) with ceilings. |
| blocker | `s7:consRound` | ROUND-M-INTEGER | Same decision as s2a HB-M-INTEGER / SCHED-M-INTEGER: [3M_l] (PAR palette), [4M_l] (HUB colours), K^HUB_l = 4M_l, eta_h : [4M_l] → [4M_l], '3k_h <= 4M_l' and 'at most M_l - 1 J-edges' all presuppose M_l ∈ ℕ. RoundInput.M must be a natural number; this requires the (R2) ceiling (proposed in s2a) before EG/Defs/Quot/Round.lean can be written. |
| blocker | `s7:consRound` | ROUND-RULE-DEPENDENCE | Manuscript decision needed before Round.lean can be locked (the Rules argument types ARE the decision). See SCHED-RULE-DEPENDENCE. The construction has nine 'fixed' choices ((b) pairing, (b) greedy order/colouring, (c) grouping, (d) SDR, (e1) processing order, (e1) order of V(G), (e2) order of E'(u), (g) rank order, (h) Dec_l). s7:lemCC, s7:lemUltra, s7:lemPay(c) and s7:lemWellDef(iii) are FALSE for rules that read the orders ≺ (e.g. an (e2) end order chosen after looking at ≺_u can force coincidences), and (iii) of s7:lemWellDef fails if the grouping reads eta. Decision needed (wording, T0): rules (b),(c) are functions of the past, rules (d),(e1),(e2) of the past and the lists; (g),(h) arbitrary. Lean: Rules fields with exactly these argument types; Specs ∀ R : Rules I, R.Valid. |
| risk | `s7:defPool` | POOL-LAW-NEEDS-GAMMA | The weight of ⊥ is 1 - Σ q_l pi_{l,r}, which is >= 0 only because Σ_{l<=R} 1/M_l <= 2/D_* < 1 (s2:lemTower(b) under Gamma, plus D_* > 2). With M_l >= 2^40 alone the mass is <= (R-2)·2^-80, and R is not bounded unconditionally, so the Lean law cannot be defined without a proof obligation. Two faithful encodings: (A) a total definition with a `dite` fallback (Dirac at ⊥ when poolMass > 1) and a Spec lemma poolMass_le_one under Gamma (recommended: no proof terms inside JV-bad, Cand, X' and the stage-1 law); (B) a definition taking the proof as an argument (proof-irrelevant but threads a hypothesis through every stage-1 definition). Must be fixed before EG/Defs/Quot/Pool.lean is locked; either way every Spec that uses the law must carry GammaCond (or the weaker poolMass <= 1). |
| risk | `s7:defCand` | CAND-MEAN-DEF | Definition-vs-use: the threshold is (1/2)·E\|Cand_l(u)\| with E over the WHOLE stage-1 law. Encoding it literally as FinDist.expect over stage1Law makes JVBad (a stage-2 status used in s7:consRound, s7:defXprime, s7:lemEXprime, s7:lemPay) depend on the s3 (1a,1c) and s5 (1b) law definitions and on POOL-LAW-NEEDS-GAMMA. Recommended T0 decision: define the threshold by the closed form candMean := q_l pi_{l,r} p_Y deg_{H_Y}(u) and prove the equality with the expectation as s7:lemCand(ii) (first equality). Both readings define the same predicate once lemCand(ii) is proved; the decision must be taken before the Defs are locked because it changes which lemmas every downstream Spec needs. |
| risk | `s7:lemCand` | CAND-GAMMA-IMPLICIT | Implicit hypotheses: the lemma has no hypothesis in its statement, but (ii) needs p_Y >= lambda_r^{-4} (s3:lemCOLJV(i), which ASSUMES Gamma1 including item (f)), (iv) needs COL-JV row 11 (Gamma1(f)) or M_l <= lambda_{l-2}^{1.6} (s2:lemTower(b), Gamma1), and s2:propStructure(i)/s2:lemTower need a valid run with n >= N_0, d_1 >= D_*. The Spec must carry GammaCond N0 Dstar (or at least Gamma1 Dstar), run.Valid, N0 <= n, Dstar <= d_1 and the designation's validity. Without them (ii)-(iv) are false (e.g. p_Y can be tiny for small lambda). |
| risk | `s7:lemCand` | CAND-INDEP-MODEL | (i) needs a stage-1 sample space in which '[uw ∈ LJV_{Y,l}]' is a function of the coordinates of the single edge uw of H_Y (s3:defCOL 'Formally': three independent uniform variables per edge) and '[plab(w) = (l,r)]' a function of the coordinate w. If the s3 Lean model draws Own/Lend first and then a uniform colouring of Lend (a compProd/dependent sample), per-edge independence has to be proved separately (~150 lines). Coordinate with the s3 blueprint: the per-edge-triple model makes (i) a direct application of indepEvents_pi_of_dependsOn. Also the summand family is indexed by N_{H_Y}(u) (u ∉ N since H_Y is loopless), and the edges uw for distinct w are distinct Sym2 values (needed for disjoint coordinates). |
| risk | `s7:defSchedule` | SCHED-PAST-PARAMETER | Design decision (P2-D), not a manuscript change: the 'past' must NOT be modelled as a sigma-algebra or a joint law over all rounds. Every round-level Spec (s7:lemWellDef(iii), s7:lemCC, s7:lemUltra, s7:lemPay(c), s7:lemUHsplit(ii)) is stated for every past, as a parameter I : RoundInput with I.Valid, and roundLaw is the uniform law on Xi. This makes Markov (c) and 'xi_l is fresh' definitional, and lets s7:lemOneOutcome pick outcomes sequentially by existence. The risk is the interface: RoundInput.Valid must contain exactly the properties that s6:lemJplus, s6:defLending, s7:defCand/lemCand and s2 provide for the actual past (see ROUND-INPUT-INTERFACE); a missing field makes a round lemma unprovable, an extra field makes the instantiation in s7:thmJVps unprovable. |
| risk | `s7:defSchedule` | SCHED-RULE-DEPENDENCE | The probability claims ('given Past_l and the lists, e_i ↦ w_i is a uniform injection, independent over ports'; Cuckoo SDR independence) are TRUE ONLY IF each 'fixed rule' / 'fixed order' of s7:consRound depends on no more randomness than allowed: pairing of fresh legs, PAR colouring and grouping must be functions of the past only; the SDR choice, the (e1) processing order, the order e_1..e_q of E'(u) and the order of V(G) in (e1) must be functions of the past and the lists (eta, zeta) only, never of the orders ≺. The manuscript says only 'fixed'. Proposed wording (T0 class): 'every fixed rule and fixed order below is a function of Past_l, and, from step (d) on, of the lists; none depends on the orders ≺_u'. Lean: a Rules structure whose fields have exactly these argument types, with every Spec quantified ∀ rules (PLAN decision 7). |
| risk | `s7:defSchedule` | SCHED-UNIFORM-LEMMAS | New probability infrastructure with no Mathlib/EG counterpart: (1) uniform law on a finite product = product of uniform laws (so coordinates are independent); (2) the image of a fixed 3-set under a uniform permutation of Fin K is a uniform 3-subset (used for non-ultra lists in s7:lemWellDef(iii)); (3) for a fixed set C and position i < \|C\|, the i-th element of C in a uniform random order of V(G) is uniform on C (the junction marginals in s7:lemCC, s7:lemUltra, s7:lemPay(c)); (4) conditioning a product law on a product event is the product of the conditioned laws, and total expectation over the atoms of a finite family of indicators (s7:lemCC). Estimate 300-400 lines in EG/Lib/Prob/Uniform.lean. |
| risk | `s7:consRound` | ROUND-INPUT-INTERFACE | The construction reads the past only through J_l and its J+ properties, the pool, the classes, the LJV classes and the JV-bad statuses. The RoundInput.Valid field list above was extracted from every proof step of s7:lemWellDef, s7:lemMULT, s7:lemSimple, s7:lemLift, s7:lemCC, s7:lemUltra (and s7:lemPay): J1 aggregated over parts (MULT), J2 at ports and fresh centres + \|J_l\| <= n(M-1) (WellDef, CC, Ultra, Pay), J3 roles (Lift), typed endpoints (Lift, Pay), s6:lemJplus(iii) disjointness of E(H_Y) from E_l(Z) and of distinct E(H_Y) (Lift), u ∈ V(Y(u)) and r(u) <= l-2 (MULT, Lift), ports' classes lend-good (Lift (iii), JC1), JV-good ⇒ \|Cand\| >= Hcd (lemCand(iv)), M >= 2^40 and Hcd >= 2^10 M^10 (Gamma). mult_r(w) for s7:lemMULT additionally needs the set of ancestors of each round (field ancOfRound or a Fintype A with ancRound). s7:thmJVps must instantiate it from the real past (a lemma RoundInput.ofPast_valid using s6:lemJplus, s6:defLending, s7:lemCand, s2:propStructure). Getting this interface wrong silently changes all round Specs; it must be reviewed together with the s6 blueprint. |
| risk | `s7:consRound` | ROUND-TOTALITY | Every step has a side condition proved only later: (b) greedy colouring succeeds (lemWellDef(i)), (c) 3k_h <= 4M_l (ii), (e1) the candidate set is non-empty (iv), (e2) \|C(u)\| >= \|E'(u)\| (v), (h) a decomposition with f(Q_l) objects exists. The Lean definitions must be total with explicit fallbacks (Option / default colour / default junction / Classical.choose) and s7:lemWellDef must state that no fallback is ever taken; otherwise the definitions depend on the lemmas (circular) or carry proof arguments that leak into every Spec. Every lemma about junctions must be stated for the total definition under I.Valid ∧ R.Valid. |
| risk | `s7:consRound` | ROUND-DATAMODEL-SIZE | This is the largest single definition of s7 (items, PAR objects, cherries, colouring, groups, lists, SDR, a sequential fold for (e1) with two families of Used sets, per-port injections for (e2), loops, two layer families, ranks, a tagged simple graph, the lift of cycles). Estimated 900-1100 lines of Defs + API before any lemma. The sequential (e1) must be a List.foldl over the processing order with state (Used : V → Finset V, UsedK : V → Fin K → Finset V, junction : Item → Option V). |
| risk | `s7:consRound` | ROUND-LIFT-ROTATION | Dec_l's cycles come as Obj.cycle (c : List (QVert V)) with arbitrary start and direction. The lift must read the alternation (HUB: hub copy / junction copy; PAR: junction copies only), recover each Q_l edge's PAR object or hub item from its (sub-layer, endpoints) via the rank-injectivity of s7:lemSimple, orient each object (which end has junction w_i), insert middles, and produce a Nodup list of V. For HUB cycles starting at a junction copy, rotate first. Proof obligations (Nodup, adjacency, cycleEdges membership) are in s7:lemLift(ii). |
| risk | `s7:lemWellDef` | WD-SDR-UNIONBOUND | (iii) is the hardest numerical step of the chunk. Formal route: Hall (Mathlib, iff form) ⇒ failure ⊆ ⋃_{4 <= s <= m} ⋃_{\|S\| = s} ⋃_{\|T\| = s-1} {all lists of S ⊆ T}; independence of the m lists (distinct hubs ⇒ distinct coordinates of the uniform product; SCHED-UNIFORM-LEMMAS (1),(2)); P(list ⊆ T) = C(s-1,3)/C(K,3); then the analytic bound Σ_s T_s <= K^{-4}. Re-derived: T_s <= e^{2s-1}4^{-s}s^{-s}(s-1)^{2s+1}K^{-s-1} <= a_s = (1/e)(s/K)(e^2 s/(4K))^s; a_4 = 4e^7 K^{-5} = 4386.5 K^{-5} < 4400 K^{-5}; a_{s+1}/a_s <= (5e^3/16)(s+1)/K <= 6.2768·(1/13 + 10^{-4}) = 0.4772 < 0.49 for 4 <= s < K/13, K >= 10^4; for s > K/13, a_s <= (e^2/16)^s/(4e) with e^2/16 = 0.4618 <= 0.47; total <= 8800K^{-5} + 2·0.47^{K/13} <= K^{-4} for K >= 10^4. All correct. Lean cost: binomial estimates C(m,s) <= (em/s)^s need s! >= (s/e)^s (Mathlib Stirling-type bounds or a direct induction), real powers 0.47^{K/13}, e bounds (Real.exp_one_lt_d9). Since K >= 2^42 in every use, a Lean proof may replace the manuscript's series by cruder bounds (the Spec only fixes (4M_l)^{-4}). ~500 lines. |
| risk | `s7:lemMULT` | MULT-J1 | The lemma rests entirely on (J1) of s6:lemJplus in its AGGREGATED form: at most one Jhub edge of class Y at the hub h in round l over ALL standalone parts of round l. The manuscript lists this as one of the most delicate points and 'a valid run on which JS-LC emits two Jhub edges of one class at one hub in one round' as a refutation target (s7:ssecNotEstablished). RoundInput.Valid.J1 must be stated aggregated (filter over all of Jhub, not per part), and the s6 Spec of lemJplus must export exactly this form; a per-part J1 would make MULT unprovable (m_kappa(h,w) could reach the number of parts containing h). |
| risk | `s7:lemLift` | LIFT-CYCLE-WF | (ii) is where 'a lifted sub-layer cycle that repeats a vertex' (a refutation target) is excluded. The distinctness argument combines six facts: junction copies in one sub-layer are distinct vertices of G; ports of distinct same-colour objects/items are distinct (i); p_i ≠ q_i (two ends of an object at distinct ports; u ≠ u' for cherries by simplicity); middles of same-colour cherries are distinct (i); ports, middles, hubs pairwise disjoint (J3); live vs pooled (a2). Re-derived: correct. Lean cost is high: the lift is a function on List (QVert V) with rotations (ROUND-LIFT-ROTATION), and Nodup/adjacency/length >= 3 must be proved for the output list to be Obj.WF; the edge sets of the lift must be computed to prove edge-disjointness across members. ~500 lines. |
| risk | `s7:lemLift` | LIFT-JC-INTERFACE | (iv) must produce EXACTLY the predicate of the s6 Spec of s6:defJconsumer (PLAN decision 6: s6 proves MIX-C for any consumer satisfying JC1-JC3, s7 supplies the instance). Recommended phrasing of JC2+JC3 in both places: IsDecomp (J_l ∪ LentJV_l) Obj_l with every object WF. This needs J_l ∩ LentJV_l = ∅ (items ⊆ E_l(Z), junction edges ⊆ E(H_Y), disjoint by s6:lemJplus(iii); RoundInput.Valid.ljv_J) and the cover statement 'every item is paid or covered by the lift of its Q_l edge'. If the s6 blueprint phrases JC2 differently (e.g. as a Finset union equality without multiplicity), the object count used by s7:propCost may silently lose the 'each edge once' information. |
| risk | `s7:lemCC` | CC-CONDITIONING | The manuscript flags 'the conditioning in Lemma CC' as one of the most delicate points. Formally: conditioning the product law ordersLaw on the atom {(I_x)_x = b}, where each I_x depends only on the coordinate ≺_x, yields the product over ports of the conditioned coordinate laws; the partner port v_o is conditioned only on {I_{v_o} = 0}; the partner junction is then uniform on C(v_o) \ {w} (if w ∉ C(v_o) the event is sure). (iii) follows from (ii) by the law of total expectation over the finitely many atoms of positive probability, then Σ_{kappa,w} \|S_w\| <= 2·#PAR objects pointwise. Re-derived: correct, PROVIDED the (e2) end order and everything before (e2) are functions of past and lists only (ROUND-RULE-DEPENDENCE). Needs the new lemmas of SCHED-UNIFORM-LEMMAS (3),(4); ~250 lines of conditioning infrastructure. |
| note | `s7:defPool` | POOL-INDEX-VERTS | The HI Spec quantifies over V : Type WITHOUT Fintype V (EG.Spec.HIHyp: ∀ (V : Type) (G : EG.FGraph V)). All random families 'for every vertex v of G' must therefore be indexed by the Fintype subtype ↥G.verts, not by V (FinDist.pi needs Fintype of the index). |
| note | `s7:defPool` | POOL-ROUND-OFFSET | Write the support as 1 <= r ∧ r + 2 <= l (not r <= l - 2 with ℕ subtraction; cf. s2a ANC-ROUND-OFFSET) and pi_{l,r} = (1/2)^(l-1-r) with a natural exponent (valid since r + 2 <= l); rounds are 1-indexed. |
| note | `s7:defPool` | POOL-M-TYPE | q_l = M_l^{-2} is real in either resolution of the blocker HB-M-INTEGER (s2a); the only property used is M_l >= 1 (for M_l^{-2} <= M_l^{-1}). Take M as a function ℕ → ℝ (the cast of the integer M_l if HB-M-INTEGER is resolved by a ceiling). |
| note | `s7:defPool` | POOL-DISJOINT-DEFINITIONAL | Disjointness of the Pool_l and uniqueness of r(w) are immediate from 'one label per vertex'; poolRound must be total (value 0 off the pool) and every lemma must use it only under w ∈ Pool_l. Lemma MULT relies on exactly this uniqueness (r(u_i) = r). |
| note | `s7:defPool` | POOL-STAGE1-INDEP | 'Independent of all other stage-1 data' is a consequence of defining the stage-1 law as a product (s7:defSchedule), not a separate hypothesis; do not state it as an assumption in any Spec (that would be an unprovable/vacuous-risk interface). |
| note | `s7:defCand` | CAND-CLASS-INDEX | Y(u) depends on (l, u) only (Z_u is unique by s2:propStructure(iv)); a vertex can be a classed port in several rounds with different classes. The designation type (s6 blueprint) must expose cls l u (or cls l Z u with a lemma removing Z). Classes are ancestors identified by (round, address) (s2a HB-ADDRESS-IDENTITY); comparing classes by vertex set would break Lemma MULT (distinct classes). |
| note | `s7:defCand` | CAND-LJV-DOMAIN | LJV_{Y,l} exists only for r(Y) <= R-2 and r+2 <= l <= R (s3:defCOL(ii)); for a classed port of round l both hold because r <= l-2 and l <= R. The Lean ljv must be total (empty outside this domain) and p_Y must be total (klend >= 1 here, so p_Y = 1/(2 klend) is the manuscript value). |
| note | `s7:defCand` | CAND-TOTAL | cand, candMean and JVBad are total functions of (l, u); JVBad includes 'u is a classed port of round l' so that non-ports are never JV-bad (the manuscript defines JV-badness only for classed ports; (a3) of s7:consRound only asks it at port ends). |
| note | `s7:defCand` | CAND-STRICT | JV-bad uses the strict inequality \|Cand\| < mean/2; lemCand(iii) bounds P(X <= mean/2) (lower-tail Chernoff with <=), which contains the strict event: consistent. Keep < in the definition (JV-good ⇔ \|Cand\| >= mean/2 is what (iv) uses). |
| note | `s7:defCand` | CAND-HCD-REAL | Hcd_l is real; thresholds built from it (⌈Hcd_l/8⌉, ⌊M_l Hcd_l/7⌋, ⌈8c/Hcd_l⌉) are Nat.ceil/Nat.floor of nonnegative reals. l >= 3 guarantees l - 2 >= 1 so lambda_{l-2} is a real round quantity (lambda_{l-2} >= 2^25 > 0). |
| note | `s7:lemCand` | CAND-MINDEG | deg_{H_Y}(u) > s_Y >= s_r/2 >= lambda_r^{100}/2 uses s2:propStructure(i) ('every H_Y has minimum degree greater than s_Y'), which itself comes from the expander property with eps > 0 (CONVENTIONS T0-def11-eps) and u ∈ V(Y) (s6:defDesign). EG.FGraph.minDeg is 0 on the empty graph: state the degree bound pointwise for u ∈ (run.H Y).verts. |
| note | `s7:lemCand` | CAND-NUMERICS | All inequalities are exact in ℝ with natural exponents: M_l^{-2}·2^{-(l-1-r)}·lambda_r^{-4}·(lambda_r^{100}/2) = lambda_r^{96} 2^{-(l-r)}/M_l^2; (eqCandExp) from lambda_r^{95} >= lambda_{l-2}^{95} (monotone, lambda_{l-2} >= 1) and lambda_r >= 2^{l-r} >= 2^{l-r-2}; (iii) exp(-mu/8) <= exp(-Hcd/4) from mu >= 2 Hcd; (iv) 2^13 M^12 <= 2^13 lambda^{19.2} <= lambda^95 needs lambda^{75.8} >= 2^13 (lambda >= 2^25): uses rpow with exponent 1.6 if taken via lemTower(b); via COL-JV row 11 it is a direct citation. No galactic constant is evaluated. |
| note | `s7:lemCand` | CAND-M-TYPE | Inherited from s2a HB-M-INTEGER: 2^10 M_l^10 is real either way; no change needed in this lemma under the proposed ceiling fix (M_l enters only through q_l and Hcd_l). |
| note | `s7:lemCand` | CAND-DECLARED-OVERREACH | (iii) is used downstream only in s7:lemEXprime (expected JV-bad weight) and (iv) in s7:lemWellDef and s7:lemUltra; (i) is used only inside this proof. Keep (i) as a separate conjunct/lemma so that its model-dependence (CAND-INDEP-MODEL) is isolated. |
| note | `s7:defSchedule` | SCHED-XI-TYPES | Representation choices: eta_h as Equiv.Perm (Fin K) (0-based; the i-th group gets {eta(3i), eta(3i+1), eta(3i+2)} for i < k_h, see ROUND-FIN-OFFSET); zeta for ALL ordered pairs (including h = u and pairs never used) — extra independent coordinates are harmless and avoid a subtype; ≺_u as a bijection V(G) ≃ Fin n (rank), since 'linear order' is not a convenient Fintype. All are Fintype, so roundLaw := FinDist.uniform needs only Nonempty (K >= 3). |
| note | `s7:defSchedule` | SCHED-INDEX-VERTS | Families 'for every vertex' are indexed by ↥G.verts (HIHyp has no Fintype V; see POOL-INDEX-VERTS). |
| note | `s7:defSchedule` | SCHED-SELECTION | (1e) and the stage-3 'fixed inside good events' are existence statements proved in s7:lemOneOutcome (Markov (a) and non-emptiness); they are not Lean definitions. The stage-1 law must be defined without reference to (1e); later statements never condition on {X' <= 3EX'} (the manuscript states this explicitly, and the Lean architecture enforces it). |
| note | `s7:defSchedule` | SCHED-STAGE3-SCOPE | Stage-3 laws and good events (s4:lemTPV, s4:lemPV, s4:thmVXp) are outside this chunk; the schedule only fixes that they are drawn per part and independent given stage 1. The declared deps s4:lemTPV, s4:lemPV, s4:thmVXp, s5:lemChild, s5:lemDemoted are pointers (ms_deps: declared_but_unreferenced). |
| note | `s7:defSchedule` | SCHED-PAST-CONTENT | The past includes decompositions of rounds l' > l (through J_l and junk). Since Dec_{l'} is chosen by a deterministic rule (Classical.choose in Lean) and every round bound holds for every past, this dependence is harmless (s7:remNonCirc(3)); the Lean recursion producing successive pasts is s6:consOrder's recursion on R - l (PLAN decision 6). |
| note | `s7:consRound` | ROUND-LAYERS-ENCODING | The multigraph layers need no general MGraph type (PLAN §3 decision 2): a layer edge is indexed by its unpaid PAR object (PAR) or coloured hub item (HUB); its endpoints are (junction copies) resp. (hub, junction copy); the rank is its position among indices with the same endpoints in the (arbitrary) order R.rank. Q_l := FGraph on QVert V = tag × V with tag = (P/H, kappa, iota, side); edges = images of layer edges tagged by (kappa, rank); verts = endpoints of edges (so 'isolated vertices deleted' is definitional). |
| note | `s7:consRound` | ROUND-RANK-UNBOUNDED | iota ranges over all of ℕ≥1; only ranks <= (number of layer edges) occur. Defining Q_l by its edge set (image of a finite index set) keeps everything finite; do not define it as a union over iota ∈ ℕ. |
| note | `s7:consRound` | ROUND-DEC-CHOICE | 'Lexicographically first' decomposition: PLAN decision 7 — Dec_l := Classical.choose (exists a decomposition of Q_l.edges of length fnum Q_l.edges) (fnum is attained by definition). All properties are proved for every decomposition (s7:lemLift(ii)), so the rule is immaterial; the past of later rounds depends on Dec_l only through the deterministic choice (s7:remNonCirc(3)). |
| note | `s7:consRound` | ROUND-MARKOV-EXISTENCE | (f) contains a probability claim (>= 1/2) that belongs in a lemma: goodXi is a Prop on Xi and 1/2 <= prob{goodXi} is EG.FinDist.half_le_prob_le_four_mul_expect_and applied to roundLaw (the '(c) conditional' part of s1:citMarkov is automatic because the past is a parameter). The choice of xi_l in the event is made in s7:lemOneOutcome. |
| note | `s7:consRound` | ROUND-PAY-DEF | pay_l counts only edges paid in (d) and (e3) (random); payments of (a1)-(a3) and unpaired fresh legs (b) are deterministic in the past and are bounded by stage-1 functionals in s7:lemPay. An SDR failure at u pays all live hub items at u (each one edge); a looped Jpar item 1 edge, a looped cherry 2 edges. |
| note | `s7:consRound` | ROUND-PORT-TERM | In s7 'port' means a vertex of ⋃_Z Q*_Z (a classed non-lost port), whereas s2:defAncestors' ports U_Z include fresh ports; fresh ports appear here as 'fresh centres' and lost ports as 'lost centres'. Define RoundInput.ports := ⋃ Q*_Z and never reuse the s2 name. |
| note | `s7:consRound` | ROUND-JPAR-CLASSES-UNUSED | 'Y(u) ≠ Y(v)' for Jpar items (s6:lemEL) is stated but used by no proof in s7; the cherry pairing does not ask for distinct classes either. Do not put it into RoundInput.Valid unless s6 exports it anyway (harmless but unnecessary). |
| note | `s7:consRound` | ROUND-FIN-OFFSET | Colours [3M_l], [4M_l] become Fin (3M), Fin (4M) (0-based); group i ∈ {0..k_h-1} gets {eta(3i), eta(3i+1), eta(3i+2)}, needing 3k_h <= 4M exactly as in the manuscript. |
| note | `s7:consRound` | ROUND-OBJ-LIST | Obj_l must be a List (Obj V) (the count of objects matters: s7:propCost adds \|Obj_l\|); LentJV_l a Finset (Sym2 V). The JC predicates of s6:defJconsumer should be phrased with IsDecomp on (J_l ∪ LentJV_l) and WF of every object. |
| note | `s7:lemWellDef` | WD-SDR-INDEP-SIMPLE | Independence of the m lists at u uses that the live hub items at u are distinct edges hu, so their hubs are distinct (G simple; in Lean items are distinct Sym2 values at u, hence distinct other ends). It also uses that ultra/non-ultra status, grouping and group index are functions of the past (ROUND-RULE-DEPENDENCE): otherwise the non-ultra list is not a fixed-set image under eta_h. |
| note | `s7:lemWellDef` | WD-HYPS | Hypotheses to carry (via RoundInput.Valid): M_l >= 2^40 (needed: M_l >= 21/4 in (ii), K = 4M_l >= 10^4 in (iii)); Hcd_l >= 2^10 M_l^10 (needed: (7/8)Hcd_l > M_l - 2 in (iv); Hcd_l - (M_l - 1) >= Hcd_l/2 >= M_l in (v)); J2 at ports and fresh centres. The statement 'for every past' hides these; without Hcd >= 2^10 M^10 (a Gamma consequence) (iv) and (v) fail. |
| note | `s7:lemWellDef` | WD-I-COUNT | (i) counts: each port of the object carries <= M_l - 2 further live items and each further PAR object at that port uses exactly one of them (a PAR object has two ends at distinct ports and uses one item per end); the middle is the middle of <= ⌊(M_l-1)/2⌋ - 1 further cherries. 2(M_l-2) + (M_l-1)/2 - 1 < 3M_l. A PAR object never conflicts through 'port = middle' because ports ⊆ ⋃Q*_Z and middles ⊆ ⋃F_Z are disjoint (J3). In Lean the greedy colouring can be replaced by 'any proper colouring into Fin (3M)' (Rules.Valid) plus the existence lemma (degree < palette ⇒ greedy succeeds). |
| note | `s7:lemWellDef` | WD-II-ARITH | (ii): c_h <= thult_l = ⌊M_l Hcd_l/7⌋ <= M_l Hcd_l/7 ⇒ 8c_h/Hcd_l <= 8M_l/7 ⇒ k_h <= ⌈8M_l/7⌉ <= 8M_l/7 + 1 ⇒ 3k_h <= 24M_l/7 + 3 <= 4M_l iff M_l >= 21/4. Exact; Nat.ceil_le / Nat.ceil_mono. |
| note | `s7:lemWellDef` | WD-IV-GROUPS | (iv) uses: the lists of the groups of a non-ultra h are pairwise disjoint (eta_h injective), so all coloured items of h with colour kappa lie in ONE group (<= ⌈Hcd_l/8⌉ items, so \|Used_kappa(h)\| <= ⌈Hcd_l/8⌉ - 1 < Hcd_l/8), and \|Used(u)\| <= M_l - 2 (one junction per earlier (e1) item at u). Remaining >= Hcd_l - (M_l - 2) - Hcd_l/8 > 0. The Lean (e1) fold must maintain these invariants explicitly. |
| note | `s7:lemWellDef` | WD-V-LIVE-JVGOOD | (v) is claimed for 'every port carrying a live item'; such a port is JV-good because (a3) pays every item with a JV-bad port end, so \|Cand_l(u)\| >= Hcd_l by s7:lemCand(iv) (RoundInput.good_cand). \|Used(u)\| + \|E'(u)\| <= M_l - 1 because non-ultra coloured items, ultra coloured items and PAR ends at u correspond to pairwise distinct live items at u (J2). |
| note | `s7:lemWellDef` | WD-REMARK-NOT-USED | The 'Remark on numerics (not used)' (union bound maximum 0.0502 near M_l = 19, limit 9/256) must not be formalized; it is explicitly unused and small-M values are outside the hypothesis M_l >= 2^40. |
| note | `s7:lemWellDef` | WD-FORWARD-DEFINITION | s7:consRound refers forward to (ii) and (v) for well-definedness; with the total definitions of ROUND-TOTALITY the lemma is stated about the total construction ('no fallback is taken'), which removes the circularity. |
| note | `s7:lemMULT` | MULT-VY | w ∈ V(Y(u_i)) needs LJV_{Y,l} ⊆ E(H_Y) and every edge of H_Y inside V(Y) (EG.FGraph.edge_verts; RoundInput.Valid.ljv_in). This is 'where it matters that candidates are taken in the class graph H_{Y(u_i)} itself'. |
| note | `s7:lemMULT` | MULT-ADDRESS | Distinct classes are distinct ANCESTORS (addresses), and mult_r counts ancestors by address (s2a HB-ADDRESS-IDENTITY, ANC-BIJECTION). Two ancestors with equal vertex sets are counted twice by mult_r and are also distinct classes, so the inequality is consistent only with address identity on both sides. |
| note | `s7:lemMULT` | MULT-SUBLAYER-COUNT | The sub-layer statements need the rank definition 'the edges on one pair get ranks 1..m' (R.rank a bijection onto 1..m per pair). State the count as the number of iota with a vertex copy present; 'max over h' is Finset.sup over I.hubs (0 if none). For a hub h, 'max_w' ranges over the pool. |
| note | `s7:lemMULT` | MULT-COLOUR-UNUSED | The colour kappa plays no role in the first inequality; the summed version Σ_kappa m_kappa(h,w) <= mult_r(w) is free and may simplify s7:lemUHsplit. The second inequality mult_r <= mu_r belongs to s2 (propOV F11) and is only transported. |
| note | `s7:lemSimple` | SIMPLE-TAGGED-DEFINITIONAL | With QVert = tag × V and hub copies tagged 'hub side', junction copies 'pool side', a HUB edge can never be a loop, whatever h and w are; 'h ≠ w as vertices of G' is then a separate fact (still true by (a2)) needed only if someone identifies [w] with w. In Lean, Q_l : FGraph is simple by construction; the substantive content that must be proved is: (1) looplessness of PAR edges (w_1 ≠ w_2 from (e3)), required to build Q_l as an FGraph at all (FGraph.loopless); (2) rank-injectivity: the map (layer edge ↦ tagged Sym2) is injective, so that each Q_l edge has a unique PAR object / hub item (needed by the lift and by 'every item lies in exactly one edge of Q_l'). |
| note | `s7:lemSimple` | SIMPLE-DEF-ORDER | Because FGraph requires loopless edges, the Q_l definition must filter or prove w_1 ≠ w_2 at definition time: define PAR layer edges only for unpaid (non-looped) objects, which makes (1) definitional, and prove (2) here. |
| note | `s7:lemSimple` | SIMPLE-NO-ISOLATED | 'Isolated vertices deleted' is definitional if Q_l.verts := endpoints of Q_l.edges; then \|V(Q_l)\| = copies_l counts exactly the non-isolated copies used in s7:lemCC/lemUltra/lemUHsplit. |
| note | `s7:lemLift` | LIFT-COLG-META | 'The only consumer of this class is the round-l step' (COL(g)) is a property of the whole assembly (s6:consOrder, s6:lemLent), not a proposition about one round; formalize (iii)'s class statement as 'uw ∈ ljv Y ↔ Y = Y(u)' plus lend-goodness and the round bound, and leave exclusivity to the s6 recursion (JC1 + s6:lemLent). |
| note | `s7:lemLift` | LIFT-LENDGOOD | 'Y(u) is lend-good' uses u ∈ Q*_Z = Q_Z \ Lost_Z and Lost_Z ⊇ {classed ports with lend-bad class} (s6:defLending): RoundInput.Valid.lendGood_ports must be instantiated from s6:defLending, not assumed. |
| note | `s7:lemLift` | LIFT-ANY-DEC | (ii) is quantified over EVERY decomposition of E(Q_l) into cycles and single edges (not only Dec_l); with Obj.WF this includes the requirement that cycles are simple cycles of Q_l (length >= 3, Nodup). Keep the universal form: s7:thmJVps only needs Dec_l, but the universal statement is what makes the choice rule immaterial. |
| note | `s7:lemLift` | LIFT-DISJ-SOURCES | Edge-disjointness uses three sources of disjointness from outside s7: E(H_Y) pairwise disjoint over ancestors (s2:propStructure(iii)), E(H_Y) ⊆ E_r(Y) disjoint from E_l(Z) (s6:lemJplus(iii)), and one colour per Lend edge (s3:defCOL). In RoundInput these are ljv_disj and ljv_J; they must be derived in the instantiation lemma. |
| note | `s7:lemLift` | LIFT-COUNT | 'Objects other than paid single edges number at most 2\|Dec_l\| = 2f(Q_l)': a PAR single edge lifts to 1 or 2 single edges, a HUB single edge to 1, a cycle to 1 cycle. Dec_l has length fnum Q_l.edges (ROUND-DEC-CHOICE), so the bound is 2·fnum; Q_l.edges is loopless (FGraph) so fnum is used on a loopless set as CONVENTIONS require. |
| note | `s7:lemCC` | CC-EDGES-AT-W | 'The edges at [w] in B^P_kappa are exactly the objects of S_w' needs: looped objects are not layer edges (paid in (e3), ROUND/SIMPLE-DEF-ORDER), objects with no end at junction w are not incident to [w]. Then m_kappa(w,w') = #{o ∈ S_w : partner junction = w'} for w' ≠ w, and Σ_{w'} mu_{w'} = \|S_w\|. |
| note | `s7:lemCC` | CC-NUMERICS | Chernoff tail with T := max(t, ⌈6e\|S_w\|/Hcd_l⌉): for j >= T, j >= 2e mu_{w'} (mu_{w'} <= 3\|S_w\|/Hcd_l), so P(m >= j) <= (e mu/j)^j <= (e mu/j) 2^{1-j}; E[m 1{m >= T}] = T P(m >= T) + Σ_{j>T} P(m >= j) <= e mu 2^{2-T} <= e mu 2^{2-t}; max <= (T-1) + Σ_{w'} m 1{m >= T}. Constants: 6e·2.74 = 44.689 < 44.7 and 4e·2.74 = 29.792 < 29.8 (slack ~0.01: needs e < 2.7188; Real.exp_one_lt_d9 suffices); 2^{-⌈2 log_2 M⌉} <= M^{-2}; \|C \ {w}\| >= Hcd/2 - 1 >= Hcd/3 (Hcd >= 6). All re-checked. |
| note | `s7:lemCC` | CC-PARCOUNT | (iii) uses #PAR objects <= \|J_l\| <= n(M_l - 1) <= 1.37 n M_l (J2 total, deliberately loosened); n = \|V(G)\| = I.G.card. Each PAR object lies in at most two sets S_w (one per end), summed over kappa it lies in S_w only for its own colour. |
| note | `s7:lemCC` | CC-ATOMS | Statement (ii) is for each value pattern b of positive probability; patterns of probability 0 are excluded (FinDist.cond needs 0 < prob). Index the indicator family by the finite set of ports carrying a kappa-object (a past-and-lists-determined Finset). |
| note | `s7:lemCC` | CC-UNDECLARED-MULT | The identity '#copies of [w] in PAR sub-layers = max_{w'} m_kappa(w,w')' is the PAR analogue of s7:lemMULT's second statement ('As in Lemma MULT', s7.tex:712) and is used in (iii); s7:lemMULT is not declared. Prove one generic rank lemma for both layer kinds. |
| note | `s7:lemUltra` | ULTRA-NUMERICS | Re-derived: (ii) T := max(⌈2e mu*⌉, ⌈log_2 N⌉ + 1); for j >= T, e mu_w/j <= 1/2; Σ_w P(m_w >= j) <= (eN/j) 2^{1-j}; E max <= (T-1) + (eN/T)2^{2-T} <= T - 1 + 2e/T (as 2^{-T} <= 1/(2N)); T - 1 <= log_2 N + 2e mu* + 1; 2e/T <= 2e < 7. (iv): M Hcd/7 = lambda^95/(56M); lambda^95/M = 8M Hcd >= 2^13 M^11 >= 2^453; thult >= lambda^95/(56M) - 1 >= lambda^95/(57M) and thult >= 2^8; 4·1.37·57 = 312.36; 4e·1.37·8 = 119.17 <= 119.2; 119.2/16 = 7.45 <= 7.5; 312.36 + 7.5 < 320 (slack 0.14). All correct; small-constant checks by norm_num with Real.exp_one_lt_d9. |
| note | `s7:lemUltra` | ULTRA-G-DECREASING | (iv) uses that g(x) = (log_2 x + 8)/x is decreasing on [1, ∞) (x^2 g'(x) = 1/ln 2 - 8 - log_2 x < 0). Only integer arguments c_h > thult_l >= 1 occur; a Lean proof can use the real derivative (Mathlib antitoneOn from deriv) or a direct integer inequality (log_2 c + 8) thult <= (log_2 thult + 8) c for c >= thult >= 1. |
| note | `s7:lemUltra` | ULTRA-I-SIMPLICITY | Distinctness of the ports u_i comes from simplicity of G (items at h are distinct edges hu), not from J1 (the manuscript says so). In Lean: items are distinct Sym2 values containing h, hence distinct other ends. |
| note | `s7:lemUltra` | ULTRA-HCD-LAMBDA | (iv) mixes Hcd_l and lambda_{l-2}; RoundInput must fix Hcd := lam^95/(8M^2) definitionally (not as an independent field), otherwise the identity M Hcd/7 = lambda^95/(56M) is lost. |
| note | `s7:lemUltra` | ULTRA-CONDITIONAL-SCOPE | (ii)-(iv) are expectations over the orders with the past AND the lists fixed (N, c_h, which items are coloured depend on the lists through the SDR). s7:lemUHsplit averages over the lists afterwards; state (ii)-(iv) with L : Lists as a parameter, as in the sketch. |
| note | `s7:lemUltra` | ULTRA-LOG-NAT | log_2 N and log_2 c_h are Real.logb 2 of naturals >= 1 (nonnegative). For N = 0 the manuscript's (ii) is not claimed (max = 0); (iii) sums only over kappa with N_kappa >= 1 (at most 4M_l of them) and uses log_2 N_kappa <= log_2 c_h. |

## 4. Nodes

### `s7:defPool` — definition (with two proved facts: the law is a probability distribution; P(v in Pool_l) <= q_l): Round-split pool labels (stage 1d) (s7.tex:30)

- **Manuscript referee status:** x2
- **Formalization:** Defs (EG/Defs/Quot/Pool.lean: PoolLabel, poolMass, poolLabelLaw, poolLaw, poolSet, poolL, poolRound) + Spec (EG/Spec/Quot/Pool.lean: PoolLawStatement for the two facts and the marginal P(v in Pool_l))

**Statement (precise restatement).** Setting (section preamble s7.tex:9-25): a valid HB*^{tau+} run on a graph G with n = |V(G)| vertices, rounds 1..R, the integers/reals M_l of (R2) (s2:defHBtp), D_* satisfying Gamma. LABEL SPACE: L_R := {⊥} ∪ {(l,r) ∈ ℕ×ℕ : 3 <= l <= R, 1 <= r <= l-2}. LAW: q_l := M_l^{-2}, pi_{l,r} := 2^{-(l-1-r)} (for 1 <= r <= l-2 the exponent l-1-r ∈ {1,...,l-2}); P(lab = (l,r)) := q_l pi_{l,r}; P(lab = ⊥) := 1 - Σ_{l=3}^{R} Σ_{r=1}^{l-2} q_l pi_{l,r}. FACT 1 (it is a probability distribution): for each l, Σ_{r=1}^{l-2} pi_{l,r} = 1 - 2^{-(l-2)} < 1; and Σ_{l=3}^{R} q_l <= Σ_{l<=R} M_l^{-1} <= 2/D_* < 1 (uses M_l >= 1 and s2:lemTower(b); needs D_* > 2). Hence P(⊥) = 1 - Σ_l q_l(1 - 2^{-(l-2)}) ∈ (0,1]. SAMPLE: every vertex v ∈ V(G) independently draws plab(v) with this law (an i.i.d. family indexed by V(G)). SETS: Pool_{l,r} := plab^{-1}(l,r); Pool_l := ⋃_{r=1}^{l-2} Pool_{l,r} (a disjoint union). FACT 2: P(v ∈ Pool_l) = q_l(1 - 2^{-(l-2)}) <= q_l for every v ∈ V(G) and 3 <= l <= R. FACT 3 (deterministic): the sets Pool_l (3 <= l <= R) are pairwise disjoint and, for w ∈ Pool_l, r(w) := the unique r with w ∈ Pool_{l,r} is well defined (single label per vertex). The pool labels form stage (1d) of the schedule (s7:defSchedule) and are independent of all other stage-1 data (the colourings and JS labels of s3:defCOL and the zones of s5:defZones): the stage-1 law is the product of the four family laws.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| valid run; R; M_l; D_* | s2:defHBtp (R0)-(R5); R = last round with d_R >= D_*; M_l = max(2^40, 2^16 T_l log^4 T_l) | s2:defHBtp | no: EG.HB.Run / run.Valid / run.R / run.M (s2a blueprint, not yet in EG) |
| FinDist, FinDist.pi, ofFinset, dirac, prob, expect | finite real-weighted distributions; product over a Fintype index | PLAN §3 decision 3 | yes: EG.FinDist (EG/Defs/Prob/FinDist.lean) |
| PoolLabel | Option (ℕ × ℕ): none = ⊥, some (l, r) = (l, r) | s7:defPool | no: new EG.Quot.PoolLabel (abbrev) |
| poolMass R M | Σ_{l ∈ Icc 3 R} Σ_{r ∈ Icc 1 (l-2)} (M l : ℝ)^(-2:ℤ) * 2^(-((l-1-r : ℕ) : ℤ)) | s7:defPool | no: new |
| poolLabelLaw R M | FinDist PoolLabel with the weights above; total definition: if poolMass <= 1 then ofFinset ... else dirac none (see POOL-LAW-NEEDS-GAMMA) | s7:defPool | no: new |
| poolLaw G run | FinDist.pi (fun _ : ↥G.verts => poolLabelLaw run.R run.M) : FinDist (↥G.verts → PoolLabel) | s7:defPool | no: new |
| poolSet plab l r / poolL plab l / poolRound plab w | Pool_{l,r} = {v ∈ V(G) : plab v = some (l,r)}; Pool_l = {v : ∃ r, plab v = some (l,r)}; r(w) (total: 0 if w unpooled) | s7:defPool | no: new |
| stage-1 law | product of (1a) COL-JV colourings, (1b) zones, (1c) JS labels, (1d) pool labels | s7:defSchedule | no: new EG.Quot.stage1Law (see s7:defSchedule) |

**deps_declared** (manuscript \deps): s2:lemTower, s3:defCOL

**deps_from_proof:** s2:lemTower, s2:defHBtp, s1:condGamma

**deps_notes:** s2:lemTower(b) gives Σ_{l<=R} 1/M_l <= 2/D_*; s2:defHBtp gives M_l >= 2^40 >= 1 (so M_l^{-2} <= M_l^{-1}); '2/D_* < 1' needs D_* > 2, which comes from Gamma (s1:condGamma, Gamma1core: 2 < D) and is not declared. s3:defCOL is cited only for 'independent of the colourings', which is a property of the product construction of the stage-1 law (s7:defSchedule).

**used_by:** s7:defCand; s7:lemCand; s7:defSchedule; s7:consRound (a2), (e), (g); s7:lemMULT; s7:lemVstar; s7:lemPay; s7:defXprime; s7:lemEXprime; s7:lemUHsplit

**randomness:** Sample space ∏_{v ∈ V(G)} PoolLabel (index type ↥G.verts), i.i.d. coordinates with law poolLabelLaw (parameters R, M_3..M_R: deterministic functions of the run). Nothing is conditioned. It is the (1d) factor of the stage-1 product law (s7:defSchedule).

**lean_shape:**

```lean
namespace EG.Quot
abbrev PoolLabel := Option (ℕ × ℕ)
/-- support of the label law: (l, r) with 3 ≤ l ≤ R, 1 ≤ r, r + 2 ≤ l -/
def PoolLabel.Admissible (R : ℕ) : PoolLabel → Prop
  | none => True
  | some (l, r) => 3 ≤ l ∧ l ≤ R ∧ 1 ≤ r ∧ r + 2 ≤ l
noncomputable def poolWt (M : ℕ → ℝ) (l r : ℕ) : ℝ := (M l)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ (l - 1 - r)
noncomputable def poolMass (R : ℕ) (M : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Icc 3 R, ∑ r ∈ Finset.Icc 1 (l - 2), poolWt M l r
/-- [s7:defPool] the law of one pool label; total (Dirac at ⊥ if the mass exceeds 1, which never
happens under Gamma: `poolMass_le_one`). -/
noncomputable def poolLabelLaw (R : ℕ) (M : ℕ → ℝ) : FinDist PoolLabel := by
  classical
  exact if h : poolMass R M ≤ 1 ∧ ∀ l, 0 < M l then
    FinDist.ofFinset (poolSupport R) (fun
      | none => 1 - poolMass R M
      | some (l, r) => if PoolLabel.Admissible R (some (l, r)) then poolWt M l r else 0) ..
  else FinDist.dirac none
/-- [s7:defPool] stage (1d): i.i.d. labels over V(G) -/
noncomputable def poolLaw (G : FGraph V) (R : ℕ) (M : ℕ → ℝ) : FinDist (↥G.verts → PoolLabel) :=
  FinDist.pi fun _ => poolLabelLaw R M
def poolSet (G : FGraph V) (plab : ↥G.verts → PoolLabel) (l r : ℕ) : Finset V :=
  (G.verts.attach.filter fun v => plab v = some (l, r)).map (Function.Embedding.subtype _)
def poolL (G) (plab) (l : ℕ) : Finset V := (G.verts.attach.filter fun v => ∃ r, plab v = some (l, r)).map ..
def poolRound (G) (plab) (w : V) : ℕ := if h : w ∈ G.verts then (match plab ⟨w, h⟩ with | some (_, r) => r | none => 0) else 0
-- Spec (EG/Spec/Quot/Pool.lean)
def PoolLawStatement : Prop := ∀ (V : Type) [DecidableEq V] (G : FGraph V) (Dstar N0 : ℝ) run,
  EG.GammaCond N0 Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
  poolMass (run.R G) (run.Mr G) ≤ 1 ∧ poolMass (run.R G) (run.Mr G) < 1 ∧
  (∀ l, 3 ≤ l → ∑ r ∈ Finset.Icc 1 (l - 2), (2:ℝ)⁻¹ ^ (l - 1 - r) = 1 - (2:ℝ)⁻¹ ^ (l - 2)) ∧
  ∀ v : ↥G.verts, ∀ l, 3 ≤ l → l ≤ run.R G →
    (poolLaw G (run.R G) (run.Mr G)).prob {plab | (v : V) ∈ poolL G plab l}
      = (run.Mr G l)⁻¹ ^ 2 * (1 - (2:ℝ)⁻¹ ^ (l - 2))
-- deterministic facts (no Spec needed; Lib lemmas): poolL disjoint for l ≠ l'; w ∈ poolL l → w ∈ poolSet l (poolRound w)
```

**hazards:**

- **[risk] POOL-LAW-NEEDS-GAMMA.** The weight of ⊥ is 1 - Σ q_l pi_{l,r}, which is >= 0 only because Σ_{l<=R} 1/M_l <= 2/D_* < 1 (s2:lemTower(b) under Gamma, plus D_* > 2). With M_l >= 2^40 alone the mass is <= (R-2)·2^-80, and R is not bounded unconditionally, so the Lean law cannot be defined without a proof obligation. Two faithful encodings: (A) a total definition with a `dite` fallback (Dirac at ⊥ when poolMass > 1) and a Spec lemma poolMass_le_one under Gamma (recommended: no proof terms inside JV-bad, Cand, X' and the stage-1 law); (B) a definition taking the proof as an argument (proof-irrelevant but threads a hypothesis through every stage-1 definition). Must be fixed before EG/Defs/Quot/Pool.lean is locked; either way every Spec that uses the law must carry GammaCond (or the weaker poolMass <= 1).
- **[note] POOL-INDEX-VERTS.** The HI Spec quantifies over V : Type WITHOUT Fintype V (EG.Spec.HIHyp: ∀ (V : Type) (G : EG.FGraph V)). All random families 'for every vertex v of G' must therefore be indexed by the Fintype subtype ↥G.verts, not by V (FinDist.pi needs Fintype of the index).
- **[note] POOL-ROUND-OFFSET.** Write the support as 1 <= r ∧ r + 2 <= l (not r <= l - 2 with ℕ subtraction; cf. s2a ANC-ROUND-OFFSET) and pi_{l,r} = (1/2)^(l-1-r) with a natural exponent (valid since r + 2 <= l); rounds are 1-indexed.
- **[note] POOL-M-TYPE.** q_l = M_l^{-2} is real in either resolution of the blocker HB-M-INTEGER (s2a); the only property used is M_l >= 1 (for M_l^{-2} <= M_l^{-1}). Take M as a function ℕ → ℝ (the cast of the integer M_l if HB-M-INTEGER is resolved by a ceiling).
- **[note] POOL-DISJOINT-DEFINITIONAL.** Disjointness of the Pool_l and uniqueness of r(w) are immediate from 'one label per vertex'; poolRound must be total (value 0 off the pool) and every lemma must use it only under w ∈ Pool_l. Lemma MULT relies on exactly this uniqueness (r(u_i) = r).
- **[note] POOL-STAGE1-INDEP.** 'Independent of all other stage-1 data' is a consequence of defining the stage-1 law as a product (s7:defSchedule), not a separate hypothesis; do not state it as an assumption in any Spec (that would be an unprovable/vacuous-risk interface).

**effort:** ~150 Lean lines, difficulty 2/5 (Defs ~60 lines; Fact 1 (geometric sum, lemTower(b) import) ~40; marginal P(v ∈ Pool_l) via FinDist.pi coordinate lemma ~50.)

### `s7:defCand` — definition: Candidates and JV-bad ports (s7.tex:54)

- **Manuscript referee status:** x2
- **Formalization:** Defs (EG/Defs/Quot/Pool.lean: cand, Hcd, candMean, JVBad) + characterization lemmas (Cand ⊆ N_{H_Y}(u) ⊆ V(Y)); the remark 'JV-good ⇒ |Cand| >= Hcd' is s7:lemCand(iv).

**Statement (precise restatement).** Fix a valid run, a designation delta (s6:defDesign) and a stage-1 outcome (colourings (1a) and pool labels (1d)); let 3 <= l <= R. Let u be a classed port of round l: u ∈ Q_Z for the unique Z = Z_u ∈ Std_l (port sets of one round are disjoint, s2:propStructure(iv)); its class Y := Y(u) = delta(l, u) ∈ anc_l(u) is an ancestor of round r := r(Y) with 1 <= r and r + 2 <= l, and u ∈ V(Y). CANDIDATE SET: Cand_l(u) := {w ∈ Pool_{l,r} : uw ∈ LJV_{Y,l}}, where LJV_{Y,l} is the JV-lent class of Y for round l (s3:defCOL(ii); it exists because r <= l-2 <= R-2). Automatic facts: LJV_{Y,l} ⊆ Lend_Y ⊆ E(H_Y) and H_Y is a graph on V(Y), hence Cand_l(u) ⊆ N_{H_Y}(u) ⊆ V(Y) (candidates are taken in the class graph H_{Y(u)} itself; used by Lemma MULT). CONSTANT: Hcd_l := lambda_{l-2}^{95} / (8 M_l^2) (a real number, deterministic in the run). JV-BAD: u is JV-bad iff |Cand_l(u)| < (1/2)·E|Cand_l(u)| (strict), where E is the UNCONDITIONAL expectation over the stage-1 law, a real number determined by the run and delta (by s7:lemCand(ii) it equals q_l pi_{l,r} p_Y deg_{H_Y}(u)); u is JV-good otherwise. The definition applies to every classed port, lost or not; JV-badness is a deterministic function of the stage-1 outcome (a stage-2 status). Remark (proved in s7:lemCand(ii),(iv), not part of the definition): (1/2)E|Cand_l(u)| >= Hcd_l for every classed port of round l, so every JV-good port has |Cand_l(u)| >= Hcd_l.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| classed port, Q_Z, U_Z, A_Z, F_Z, D_l, Std_l, anc_l(x), ancestor, V(Y), H_Y, r(Y), s_Y | s2:defAncestors (ancestors indexed by (round, address), s2a HB-ADDRESS-IDENTITY) | s2:defAncestors, s2:defHBtp | no: EG.HB (s2a blueprint) |
| designation delta, class Y(u), Z_u | delta assigns to every classed port u of round l >= 3 an ancestor Y(u) ∈ anc_l(u); any deterministic function of the run | s6:defDesign | no: new (s6 blueprint); Lean: δ : ℕ → V → Anc with property δ l u ∈ anc l u for classed u |
| Lend_Y, LJV_{Y,l}, klend(Y), p_Y | stage-1 COL-JV colouring: per edge of H_Y a fair Own/Lend bit and a lent index uniform on IU ⊔ IJS ⊔ IJV; LJV_{Y,l} = Lend edges with JV index l; p_Y = 1/(2 klend(Y)) | s3:defCOL | no: new (s3 blueprint); needs a per-edge coordinate model (CAND-INDEP-MODEL) |
| Pool_{l,r} | pool labels (1d) | s7:defPool | no: new (this chunk) |
| lambda_l, M_l | lambda_l = log_2 d_l; M_l from (R2) | s2:defHBtp | no: EG.HB run API |
| FGraph.nbrs, FGraph.deg | N_H(u), deg_H(u) | s1:convGraphs | yes: EG.FGraph.nbrs / deg (EG/Defs/Graph.lean) |
| stage1Law | product law of (1a)-(1d) | s7:defSchedule | no: new |
| cand, Hcd, candMean, JVBad | as in the statement; candMean := q_l * pi_{l,r} * p_Y * deg_{H_Y}(u) (see CAND-MEAN-DEF) | s7:defCand | no: new EG.Quot.cand / Hcd / candMean / JVBad |

**deps_declared** (manuscript \deps): s7:defPool, s3:defCOL, s6:defDesign

**deps_from_proof:** s7:defPool, s3:defCOL, s6:defDesign, s2:defAncestors, s2:defHBtp, s7:lemCand

**deps_notes:** Definition; the embedded 'automatic' facts use s3:defCOL (LJV ⊆ Lend ⊆ E(H_Y)), s2:defAncestors (H_Y is a graph on V(Y)) and s6:defDesign (Y(u) ∈ anc_l(u), so u ∈ V(Y(u)), r <= l-2). The statement text refers forward to s7:lemCand for the remark 'Hcd_l is a lower bound for the threshold' (ms_deps: forward_refs = [s7:lemCand]); this is explanatory and not part of the definition. ms_deps also flags all three declared deps as unreferenced in the text; they are logically used.

**used_by:** s7:lemCand; s7:defSchedule (stage 2); s7:consRound (a3), (e1), (e2); s7:lemWellDef (iv), (v); s7:lemMULT; s7:lemLift; s7:lemCC; s7:lemUltra; s7:lemPay (a3); s7:defXprime; s7:lemEXprime

**randomness:** Cand_l(u) is a random finite set on the stage-1 space: a function of the (1a) colour variables of the edges uw (w ∈ N_{H_Y}(u)) of the colouring of Y and of the (1d) labels of the vertices of N_{H_Y}(u). E is over the full stage-1 product law (equivalently over the (1a)×(1d) marginal). JV-bad is a stage-1 event; nothing is conditioned. After the stage-1 selection (1e) the outcome is fixed and JV-badness is a deterministic status.

**lean_shape:**

```lean
namespace EG.Quot
variable {V : Type} [DecidableEq V] (G : FGraph V) (run : HB.Run V) (δ : Designation run)
/-- [s7:defCand] Hcd_l = λ_{l-2}^95 / (8 M_l^2) -/
noncomputable def Hcd (l : ℕ) : ℝ := run.lam G (l - 2) ^ 95 / (8 * run.Mr G l ^ 2)
/-- [s7:defCand] Cand_l(u) for a stage-1 outcome ω (colouring ω.col, pool labels ω.pool) -/
noncomputable def cand (ω : Stage1 G run) (l : ℕ) (u : V) : Finset V :=
  let Y := δ.cls l u
  (poolSet G ω.pool l (run.ancRound Y)).filter fun w => s(u, w) ∈ S3.ljv run ω.col Y l
/-- the mean, in closed form (T0 decision CAND-MEAN-DEF; = expectation by s7:lemCand(ii)) -/
noncomputable def candMean (l : ℕ) (u : V) : ℝ :=
  let Y := δ.cls l u; let r := run.ancRound Y
  (run.Mr G l)⁻¹ ^ 2 * (2:ℝ)⁻¹ ^ (l - 1 - r) * S3.pY run Y * ((run.H Y).deg u : ℝ)
/-- [s7:defCand] JV-bad (only classed ports can be JV-bad) -/
def JVBad (ω : Stage1 G run) (l : ℕ) (u : V) : Prop :=
  run.IsClassedPort G l u ∧ ((cand G run δ ω l u).card : ℝ) < candMean G run δ l u / 2
-- characterization lemmas (Lib): cand ⊆ (run.H (δ.cls l u)).nbrs u ⊆ (run.H _).verts = run.ancVerts _
-- alternative faithful form (if CAND-MEAN-DEF is decided the other way):
--   ((cand ..).card : ℝ) < (stage1Law G run).expect (fun ω' => (cand G run δ ω' l u).card) / 2
```

**hazards:**

- **[risk] CAND-MEAN-DEF.** Definition-vs-use: the threshold is (1/2)·E|Cand_l(u)| with E over the WHOLE stage-1 law. Encoding it literally as FinDist.expect over stage1Law makes JVBad (a stage-2 status used in s7:consRound, s7:defXprime, s7:lemEXprime, s7:lemPay) depend on the s3 (1a,1c) and s5 (1b) law definitions and on POOL-LAW-NEEDS-GAMMA. Recommended T0 decision: define the threshold by the closed form candMean := q_l pi_{l,r} p_Y deg_{H_Y}(u) and prove the equality with the expectation as s7:lemCand(ii) (first equality). Both readings define the same predicate once lemCand(ii) is proved; the decision must be taken before the Defs are locked because it changes which lemmas every downstream Spec needs.
- **[note] CAND-CLASS-INDEX.** Y(u) depends on (l, u) only (Z_u is unique by s2:propStructure(iv)); a vertex can be a classed port in several rounds with different classes. The designation type (s6 blueprint) must expose cls l u (or cls l Z u with a lemma removing Z). Classes are ancestors identified by (round, address) (s2a HB-ADDRESS-IDENTITY); comparing classes by vertex set would break Lemma MULT (distinct classes).
- **[note] CAND-LJV-DOMAIN.** LJV_{Y,l} exists only for r(Y) <= R-2 and r+2 <= l <= R (s3:defCOL(ii)); for a classed port of round l both hold because r <= l-2 and l <= R. The Lean ljv must be total (empty outside this domain) and p_Y must be total (klend >= 1 here, so p_Y = 1/(2 klend) is the manuscript value).
- **[note] CAND-TOTAL.** cand, candMean and JVBad are total functions of (l, u); JVBad includes 'u is a classed port of round l' so that non-ports are never JV-bad (the manuscript defines JV-badness only for classed ports; (a3) of s7:consRound only asks it at port ends).
- **[note] CAND-STRICT.** JV-bad uses the strict inequality |Cand| < mean/2; lemCand(iii) bounds P(X <= mean/2) (lower-tail Chernoff with <=), which contains the strict event: consistent. Keep < in the definition (JV-good ⇔ |Cand| >= mean/2 is what (iv) uses).
- **[note] CAND-HCD-REAL.** Hcd_l is real; thresholds built from it (⌈Hcd_l/8⌉, ⌊M_l Hcd_l/7⌋, ⌈8c/Hcd_l⌉) are Nat.ceil/Nat.floor of nonnegative reals. l >= 3 guarantees l - 2 >= 1 so lambda_{l-2} is a real round quantity (lambda_{l-2} >= 2^25 > 0).

**effort:** ~120 Lean lines, difficulty 2/5 (Definitions ~40 lines (given the s2/s3/s6 Defs); inclusion lemmas Cand ⊆ N_{H_Y}(u) ⊆ V(Y) ~50 lines (FGraph.edge_verts).)

### `s7:lemCand` — lemma: Candidate counts (s7.tex:84)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec (EG/Spec/Quot/Cand.lean: CandCountStatement, four conjuncts (i)-(iv)); proof in EG/Proof/Quot/Cand.lean

**Statement (precise restatement).** Hypotheses (section setting, IMPLICIT in the lemma): D_* satisfies Gamma (only Gamma1 including its item (f) = COL-JV column 3, through s3:lemCOLJV, and the facts of s2:lemTower are used), G with n >= N_0 and d_1 >= D_*, a valid run, a designation delta, 3 <= l <= R, u a classed port of round l with class Y = Y(u) of round r (1 <= r, r + 2 <= l). Probabilities and expectations are over the stage-1 product law. (i) |Cand_l(u)| = Σ_{w ∈ N_{H_Y}(u)} 1[plab(w) = (l,r)]·1[uw ∈ LJV_{Y,l}], and the |N_{H_Y}(u)| summands are MUTUALLY INDEPENDENT {0,1}-variables, the one for w having success probability q_l pi_{l,r} p_Y (P(plab(w) = (l,r)) = q_l pi_{l,r}; P(uw ∈ LJV_{Y,l}) = (1/2)(1/klend(Y)) = p_Y, the two indicators being independent). (ii) E|Cand_l(u)| = q_l pi_{l,r} p_Y deg_{H_Y}(u) >= lambda_r^{96} 2^{-(l-r)} / M_l^2 >= 2 Hcd_l (= lambda_{l-2}^{95}/(4 M_l^2)). The last step is equivalent to (eqCandExp) lambda_r^{96} >= 2^{l-r-2} lambda_{l-2}^{95}. (iii) P(u is JV-bad) <= exp(-Hcd_l / 4). (iv) For every stage-1 outcome in which u is JV-good: |Cand_l(u)| >= Hcd_l; and (deterministically) Hcd_l >= 2^{10} M_l^{10}.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| Cand_l(u), Hcd_l, JV-bad, candMean | see s7:defCand | s7:defCand | no: new (this chunk) |
| pool law, q_l, pi_{l,r} | see s7:defPool | s7:defPool | no: new (this chunk) |
| COL-JV colouring model, Lend_Y, LJV_{Y,l}, klend(Y), p_Y | per-edge independent (bit, lent index, own label) triple on E(H_Y), independent across ancestors (s3:defCOL 'Formally' paragraph) | s3:defCOL | no: s3 blueprint |
| H_Y, s_Y, s_r, lambda_r | s2:defAncestors; (R2) | s2:defAncestors, s2:defHBtp | no: s2a blueprint |
| stage1Law | product of the four stage-1 family laws | s7:defSchedule | no: new |
| iIndepFun, chernoffGen_lower_half | mutual independence; Chernoff lower tail at delta = 1/2 | s1:citChernoffGen | yes: EG.FinDist.iIndepFun, EG.FinDist.chernoffGen_lower_half (EG/Lib/Prob/Chernoff.lean) |
| GammaCond / Gamma1 | galactic conditions | s1:condGamma | no: s1 blueprint (EG.GammaCond) |

**deps_declared** (manuscript \deps): s7:defCand, s7:defPool, s3:defCOL, s3:lemCOLJV, s2:propStructure, s2:lemTower, s1:citChernoffGen

**deps_from_proof:** s7:defCand, s7:defPool, s7:defSchedule, s3:defCOL, s3:lemCOLJV, s2:propStructure, s2:defAncestors, s2:lemTower, s6:defDesign, s1:citChernoffGen, s1:condGamma

**deps_notes:** (i): s3:defCOL (per-edge independence, P(Lend) = 1/2, uniform lent index, r+2 <= l <= R so l ∈ IJV(Y)), s7:defPool (per-vertex independence, independence from colourings), s7:defSchedule (product law). (ii): s2:propStructure(i) (min degree of H_Y > s_Y; s_r >= lambda_r^{100}), s2:defAncestors (s_Y >= s_r/2), s3:lemCOLJV(i) (p_Y >= lambda_r^{-4}; needs Gamma1), s2:lemTower(a) (lambda_r >= lambda_{l-2} for r <= l-2 <= R) and (d) (lambda_r >= 2^{l-r}), s6:defDesign (u ∈ V(Y), r <= l-2). (iii): s1:citChernoffGen(a) lower tail with delta = 1/2 and mu = E X. (iv): s3:lemCOLJV(ii) row 11 (or s2:lemTower(b) M_l <= lambda_{l-2}^{1.6}). s1:condGamma (Gamma1(f)) is used through s3:lemCOLJV but not declared. ms_deps flags s7:defCand as declared-but-unreferenced in the proof text; it is used throughout.

**used_by:** s7:defCand (remark); s7:lemWellDef (via (iv)); s7:lemUltra (iv); s7:lemEXprime ((iii),(iv)); s7:lemPay (indirectly)

**randomness:** Stage-1 product law (1a)×(1b)×(1c)×(1d); (i)-(iii) only involve the (1a) colouring of the single ancestor Y (edges uw, w ∈ N_{H_Y}(u)) and the (1d) labels of N_{H_Y}(u). No conditioning. (iv) is deterministic (for every outcome).

**lean_shape:**

```lean
-- EG/Spec/Quot/Cand.lean
def CandCountStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : HB.Run V) (δ : Designation run),
  EG.GammaCond N0 Dstar → run.Valid G Dstar → N0 ≤ G.card → Dstar ≤ run.d G 1 → δ.Valid G →
  ∀ l u, 3 ≤ l → l ≤ run.R G → run.IsClassedPort G l u →
  let Y := δ.cls l u; let r := run.ancRound Y; let N := (run.H Y).nbrs u
  let I : V → Stage1 G run → ℝ := fun w ω =>
    if ω.poolLabel w = some (l, r) ∧ s(u, w) ∈ S3.ljv run ω.col Y l then 1 else 0
  -- (i)
  (∀ ω, ((cand G run δ ω l u).card : ℝ) = ∑ w ∈ N, I w ω) ∧
  (stage1Law G run).iIndepFun (fun (w : N) => I w) ∧
  (∀ w ∈ N, (stage1Law G run).prob {ω | I w ω = 1} = (run.Mr G l)⁻¹^2 * (2:ℝ)⁻¹^(l-1-r) * S3.pY run Y) ∧
  -- (ii)
  (stage1Law G run).expect (fun ω => (cand G run δ ω l u).card) = candMean G run δ l u ∧
  run.lam G r ^ 96 * (2:ℝ)⁻¹ ^ (l - r) / run.Mr G l ^ 2 ≤ candMean G run δ l u ∧
  2 * Hcd G run l ≤ run.lam G r ^ 96 * (2:ℝ)⁻¹ ^ (l - r) / run.Mr G l ^ 2 ∧
  -- (iii)
  (stage1Law G run).prob {ω | JVBad G run δ ω l u} ≤ Real.exp (-(Hcd G run l) / 4) ∧
  -- (iv)
  (∀ ω, ¬ JVBad G run δ ω l u → Hcd G run l ≤ (cand G run δ ω l u).card) ∧
  (2:ℝ) ^ 10 * run.Mr G l ^ 10 ≤ Hcd G run l
```

**hazards:**

- **[risk] CAND-GAMMA-IMPLICIT.** Implicit hypotheses: the lemma has no hypothesis in its statement, but (ii) needs p_Y >= lambda_r^{-4} (s3:lemCOLJV(i), which ASSUMES Gamma1 including item (f)), (iv) needs COL-JV row 11 (Gamma1(f)) or M_l <= lambda_{l-2}^{1.6} (s2:lemTower(b), Gamma1), and s2:propStructure(i)/s2:lemTower need a valid run with n >= N_0, d_1 >= D_*. The Spec must carry GammaCond N0 Dstar (or at least Gamma1 Dstar), run.Valid, N0 <= n, Dstar <= d_1 and the designation's validity. Without them (ii)-(iv) are false (e.g. p_Y can be tiny for small lambda).
- **[risk] CAND-INDEP-MODEL.** (i) needs a stage-1 sample space in which '[uw ∈ LJV_{Y,l}]' is a function of the coordinates of the single edge uw of H_Y (s3:defCOL 'Formally': three independent uniform variables per edge) and '[plab(w) = (l,r)]' a function of the coordinate w. If the s3 Lean model draws Own/Lend first and then a uniform colouring of Lend (a compProd/dependent sample), per-edge independence has to be proved separately (~150 lines). Coordinate with the s3 blueprint: the per-edge-triple model makes (i) a direct application of indepEvents_pi_of_dependsOn. Also the summand family is indexed by N_{H_Y}(u) (u ∉ N since H_Y is loopless), and the edges uw for distinct w are distinct Sym2 values (needed for disjoint coordinates).
- **[note] CAND-MINDEG.** deg_{H_Y}(u) > s_Y >= s_r/2 >= lambda_r^{100}/2 uses s2:propStructure(i) ('every H_Y has minimum degree greater than s_Y'), which itself comes from the expander property with eps > 0 (CONVENTIONS T0-def11-eps) and u ∈ V(Y) (s6:defDesign). EG.FGraph.minDeg is 0 on the empty graph: state the degree bound pointwise for u ∈ (run.H Y).verts.
- **[note] CAND-NUMERICS.** All inequalities are exact in ℝ with natural exponents: M_l^{-2}·2^{-(l-1-r)}·lambda_r^{-4}·(lambda_r^{100}/2) = lambda_r^{96} 2^{-(l-r)}/M_l^2; (eqCandExp) from lambda_r^{95} >= lambda_{l-2}^{95} (monotone, lambda_{l-2} >= 1) and lambda_r >= 2^{l-r} >= 2^{l-r-2}; (iii) exp(-mu/8) <= exp(-Hcd/4) from mu >= 2 Hcd; (iv) 2^13 M^12 <= 2^13 lambda^{19.2} <= lambda^95 needs lambda^{75.8} >= 2^13 (lambda >= 2^25): uses rpow with exponent 1.6 if taken via lemTower(b); via COL-JV row 11 it is a direct citation. No galactic constant is evaluated.
- **[note] CAND-M-TYPE.** Inherited from s2a HB-M-INTEGER: 2^10 M_l^10 is real either way; no change needed in this lemma under the proposed ceiling fix (M_l enters only through q_l and Hcd_l).
- **[note] CAND-DECLARED-OVERREACH.** (iii) is used downstream only in s7:lemEXprime (expected JV-bad weight) and (iv) in s7:lemWellDef and s7:lemUltra; (i) is used only inside this proof. Keep (i) as a separate conjunct/lemma so that its model-dependence (CAND-INDEP-MODEL) is isolated.

**effort:** ~400 Lean lines, difficulty 3/5 ((i) independence under the product law ~150 (depends on the s3 colouring model); (ii) closed-form expectation + inequalities ~120; (iii) Chernoff application ~50; (iv) ~40.)

### `s7:defSchedule` — definition (with Table s7:tabSchedule): The randomness schedule (s7.tex:158)

- **Manuscript referee status:** x2
- **Formalization:** Defs (EG/Defs/Quot/Schedule.lean: Stage1 record and stage1Law (product of 4 laws); Lists/Orders/Xi types and roundLaw := uniform) + Lib lemmas (uniform on a product = product of uniforms; image of a fixed 3-set under a uniform permutation is a uniform 3-subset; the i-th element of a fixed set C in a uniform random order is uniform on C). No Spec of its own: the schedule is an architecture decision, realized by quantifying round-level Specs over the past (RoundInput) and by the existence proof s7:lemOneOutcome.

**Statement (precise restatement).** All random choices are made in the order: STAGE 1 = four mutually independent families: (1a) the COL-JV colourings of s3:defCOL(i)-(iii) (all ancestors; independent per ancestor and per edge); (1b) the vertex choices and sublabels of s5:defZones (independent per vertex); (1c) the JS labels lab_{Y,l}(y) of s3:defCOL(iv); (1d) the pool labels of s7:defPool (independent per vertex). SELECTION (1e), not random: a stage-1 outcome is fixed in the event {X' <= 3 E X'} (X' >= 0 the stage-1 functional s7:defXprime, a deterministic function of run, delta and stage 1; E X' is the unconditional expectation). After (1e) stage 1 is a fixed outcome; no later step uses the stage-1 law or conditions on the (1e) event; E X' and E|Cand_l(u)| used later are unconditional numbers fixed in advance. STAGE 2 (deterministic given stage 1): demotion, parent-bad, Bad (s5:defStages); lend-bad, Lost, Ret, Q* (s6:defLending); JV-bad (s7:defCand). STAGE 3, drawn part by part: TPV labels of every standalone pre-part, P-vortex labels of every non-demoted light part, VX+ labels of every demoted light part; given stage 1 the families of distinct parts are independent; each part's labels are fixed inside that part's good event. ROUNDS l = R, R-1, ..., 3: the round randomness xi_l consists of mutually independent variables: a uniformly random bijection eta_h : [4M_l] → [4M_l] for every vertex h; a uniformly random 3-subset zeta_{h,u} ⊆ [4M_l] for every ordered pair (h,u) of distinct vertices; a uniformly random linear order ≺_u of V(G) for every vertex u. xi_l is fresh: independent of stage 1, stage 3 and all xi_{l'} (l' > l). PAST: Past_l := the fixed outcome of stage 1, stage 3 and xi_{l'} (l' > l), with everything they determine (in particular the decompositions fixed at rounds l' > l and the set J_l); a fixed outcome, not a sigma-algebra. E[·|Past_l], P(·|Past_l) denote expectation/probability over xi_l with Past_l fixed. At each round xi_l is chosen in the event of step (f) of s7:consRound. All draws are mutually independent; outcomes are chosen inside events (stage 1 in {X' <= 3EX'}, stage 3 in the good events, each xi_l in the (f) event); afterwards only deterministic properties of the chosen outcome are used, and every later probability is over fresh variables with the past fixed. TABLE s7:tabSchedule restates this (1e: probability >= 2/3; stage 3: >= 1/2 - o(1); rounds: >= 1/2).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| COL-JV colourings and JS labels (1a), (1c) | s3:defCOL | s3:defCOL | no: s3 blueprint |
| vertex choices and sublabels (1b) | s5:defZones | s5:defZones | no: s5 blueprint |
| pool labels (1d) | s7:defPool | s7:defPool | no: new (this chunk) |
| X' | XU + Xpool + XV | s7:defXprime | no: new (chunk s7b) |
| stage-2 statuses | s5:defStages, s6:defLending, s7:defCand | s5/s6/s7 | no: new |
| stage-3 label families and good events | s4:lemTPV, s4:lemPV (via s5:lemChild), s4:thmVXp (via s5:lemDemoted) | s4/s5 | no: s4/s5 blueprints |
| Stage1 G run / stage1Law G run | record (col, zone, js, pool) and ((colLaw.prod zoneLaw).prod jsLaw).prod poolLaw (or FinDist.pi over a 4-element index) | s7:defSchedule | no: new |
| Lists G K / Orders G / Xi G K | Lists := (↥G.verts → Equiv.Perm (Fin K)) × (↥G.verts × ↥G.verts → {s : Finset (Fin K) // s.card = 3}); Orders := ↥G.verts → (↥G.verts ≃ Fin G.card) (rank of each vertex in ≺_u); Xi := Lists × Orders; K = 4 M_l | s7:defSchedule | no: new |
| roundLaw G K | FinDist.uniform (Xi G K) (= (uniform Lists).prod (uniform Orders), = product of all uniform coordinates; lemma) | s7:defSchedule | no: new; uses EG.FinDist.uniform |
| RoundInput (the past as read by the round step) | see s7:consRound | s7:consRound / s6:lemJplus | no: new |

**deps_declared** (manuscript \deps): s3:defCOL, s5:defZones, s7:defPool, s6:defLending, s5:defStages, s7:defCand, s4:lemTPV, s4:lemPV, s4:thmVXp, s5:lemChild, s5:lemDemoted

**deps_from_proof:** s3:defCOL, s5:defZones, s7:defPool, s5:defStages, s6:defLending, s7:defCand, s7:defXprime, s7:consRound, s1:citMarkov

**deps_notes:** Definition. The text refers forward to X' (s7:defXprime) and to step (f) of s7:consRound; the probability claims of the table (>= 2/3, >= 1/2) are s1:citMarkov (proved in s7:lemOneOutcome). The declared s4/s5 lemmas are pointers to the stage-3 good events (ms_deps: declared_but_unreferenced); nothing in this definition uses their content.

**used_by:** s7:consRound; s7:lemWellDef (iii); s7:lemCC; s7:lemUltra; s7:lemPay (c); s7:lemUHsplit; s7:lemOneOutcome; s7:propCost; s7:remNonCirc

**randomness:** STAGE 1: product of four finite laws ((1a) per-edge triples over all ancestors' H_Y; (1b) per-vertex choice+sublabel; (1c) per-(Y,l,y) JS label; (1d) per-vertex pool label), all parameters deterministic in the run. STAGE 3: per-part label laws (s4), product over parts given stage 1. ROUND l: uniform law on Xi_l = (Perm(Fin 4M_l))^{V(G)} × (3-subsets of Fin 4M_l)^{V(G)×V(G)} × (linear orders of V(G))^{V(G)} — a single finite uniform law, independent of everything else by construction because the past enters only as a parameter. 'Given Past_l' = the past is a parameter of the random variable; 'given Past_l and the lists' = additionally fix the Lists component and take the uniform law on Orders.

**lean_shape:**

```lean
namespace EG.Quot
structure Stage1 (G : FGraph V) (run : HB.Run V) where
  col  : S3.ColOutcome G run      -- (1a)
  zone : S5.ZoneOutcome G run     -- (1b)
  js   : S3.JSOutcome G run       -- (1c)
  pool : ↥G.verts → PoolLabel     -- (1d)
noncomputable def stage1Law (G) (run) : FinDist (Stage1 G run) :=
  (((S3.colLaw G run).prod (S5.zoneLaw G run)).prod (S3.jsLaw G run)).prod
    (poolLaw G (run.R G) (run.Mr G)) |>.map Stage1.mk'
abbrev Lists (G : FGraph V) (K : ℕ) :=
  (↥G.verts → Equiv.Perm (Fin K)) × (↥G.verts × ↥G.verts → {s : Finset (Fin K) // s.card = 3})
abbrev Orders (G : FGraph V) := ↥G.verts → (↥G.verts ≃ Fin G.card)   -- rank_u : V(G) ≃ Fin n
abbrev Xi (G : FGraph V) (K : ℕ) := Lists G K × Orders G
noncomputable def listsLaw (G) (K) [NeZero K] (hK : 3 ≤ K) : FinDist (Lists G K) := FinDist.uniform _
noncomputable def ordersLaw (G) : FinDist (Orders G) := FinDist.uniform _
noncomputable def roundLaw (G) (K) (hK) : FinDist (Xi G K) := (listsLaw G K hK).prod (ordersLaw G)
-- Lib lemmas needed (EG/Lib/Prob/Uniform.lean, new):
--  uniform_prod : uniform (α × β) = (uniform α).prod (uniform β); uniform_pi : uniform (ι → α) = pi (fun _ => uniform α)
--  perm_image_uniform : (uniform (Perm (Fin K))).map (fun σ => B.map σ) = uniform {s // s.card = B.card}
--  order_kth_uniform : for C ⊆ V(G), i < C.card: (uniform (V(G) ≃ Fin n)).map (kth C i) = uniform ↥C
-- Round-level statements take the past as a parameter:  ∀ (I : RoundInput V) (hI : I.Valid) (rules), ...
-- 'E[X | Past_l]'            ≡ (roundLaw I.G (4*I.M) _).expect (X I rules)
-- 'E[X | Past_l, lists]'     ≡ (ordersLaw I.G).expect (fun o => X I rules (L, o))   for fixed L : Lists
```

**hazards:**

- **[blocker] SCHED-M-INTEGER.** Inherited from s2a HB-M-INTEGER: the round variables are bijections of [4M_l], 3-subsets of [4M_l] (and PAR colours [3M_l] in s7:consRound). These sets exist only if M_l ∈ ℕ, while (R2) defines M_l = max(2^40, 2^16 T_l log^4 T_l), in general irrational. The Lean types Perm (Fin K), Fin (3*M) require the manuscript decision proposed in s2a (M_l := ⌈...⌉ ∈ ℕ); the s7 inequalities re-checked in this chunk (M_l >= 2^40, M_l <= lambda_{l-2}^{1.6} with slack, 3k_h <= 4M_l for M_l >= 21/4, K = 4M_l >= 10^4) are unaffected by the ceiling. Fallback (K^HUB := ⌈4M_l⌉, PAR palette ⌈3M_l⌉) would require re-checking lemWellDef(i),(ii) and lemUltra(iii) with ceilings.
- **[risk] SCHED-PAST-PARAMETER.** Design decision (P2-D), not a manuscript change: the 'past' must NOT be modelled as a sigma-algebra or a joint law over all rounds. Every round-level Spec (s7:lemWellDef(iii), s7:lemCC, s7:lemUltra, s7:lemPay(c), s7:lemUHsplit(ii)) is stated for every past, as a parameter I : RoundInput with I.Valid, and roundLaw is the uniform law on Xi. This makes Markov (c) and 'xi_l is fresh' definitional, and lets s7:lemOneOutcome pick outcomes sequentially by existence. The risk is the interface: RoundInput.Valid must contain exactly the properties that s6:lemJplus, s6:defLending, s7:defCand/lemCand and s2 provide for the actual past (see ROUND-INPUT-INTERFACE); a missing field makes a round lemma unprovable, an extra field makes the instantiation in s7:thmJVps unprovable.
- **[risk] SCHED-RULE-DEPENDENCE.** The probability claims ('given Past_l and the lists, e_i ↦ w_i is a uniform injection, independent over ports'; Cuckoo SDR independence) are TRUE ONLY IF each 'fixed rule' / 'fixed order' of s7:consRound depends on no more randomness than allowed: pairing of fresh legs, PAR colouring and grouping must be functions of the past only; the SDR choice, the (e1) processing order, the order e_1..e_q of E'(u) and the order of V(G) in (e1) must be functions of the past and the lists (eta, zeta) only, never of the orders ≺. The manuscript says only 'fixed'. Proposed wording (T0 class): 'every fixed rule and fixed order below is a function of Past_l, and, from step (d) on, of the lists; none depends on the orders ≺_u'. Lean: a Rules structure whose fields have exactly these argument types, with every Spec quantified ∀ rules (PLAN decision 7).
- **[risk] SCHED-UNIFORM-LEMMAS.** New probability infrastructure with no Mathlib/EG counterpart: (1) uniform law on a finite product = product of uniform laws (so coordinates are independent); (2) the image of a fixed 3-set under a uniform permutation of Fin K is a uniform 3-subset (used for non-ultra lists in s7:lemWellDef(iii)); (3) for a fixed set C and position i < |C|, the i-th element of C in a uniform random order of V(G) is uniform on C (the junction marginals in s7:lemCC, s7:lemUltra, s7:lemPay(c)); (4) conditioning a product law on a product event is the product of the conditioned laws, and total expectation over the atoms of a finite family of indicators (s7:lemCC). Estimate 300-400 lines in EG/Lib/Prob/Uniform.lean.
- **[note] SCHED-XI-TYPES.** Representation choices: eta_h as Equiv.Perm (Fin K) (0-based; the i-th group gets {eta(3i), eta(3i+1), eta(3i+2)} for i < k_h, see ROUND-FIN-OFFSET); zeta for ALL ordered pairs (including h = u and pairs never used) — extra independent coordinates are harmless and avoid a subtype; ≺_u as a bijection V(G) ≃ Fin n (rank), since 'linear order' is not a convenient Fintype. All are Fintype, so roundLaw := FinDist.uniform needs only Nonempty (K >= 3).
- **[note] SCHED-INDEX-VERTS.** Families 'for every vertex' are indexed by ↥G.verts (HIHyp has no Fintype V; see POOL-INDEX-VERTS).
- **[note] SCHED-SELECTION.** (1e) and the stage-3 'fixed inside good events' are existence statements proved in s7:lemOneOutcome (Markov (a) and non-emptiness); they are not Lean definitions. The stage-1 law must be defined without reference to (1e); later statements never condition on {X' <= 3EX'} (the manuscript states this explicitly, and the Lean architecture enforces it).
- **[note] SCHED-STAGE3-SCOPE.** Stage-3 laws and good events (s4:lemTPV, s4:lemPV, s4:thmVXp) are outside this chunk; the schedule only fixes that they are drawn per part and independent given stage 1. The declared deps s4:lemTPV, s4:lemPV, s4:thmVXp, s5:lemChild, s5:lemDemoted are pointers (ms_deps: declared_but_unreferenced).
- **[note] SCHED-PAST-CONTENT.** The past includes decompositions of rounds l' > l (through J_l and junk). Since Dec_{l'} is chosen by a deterministic rule (Classical.choose in Lean) and every round bound holds for every past, this dependence is harmless (s7:remNonCirc(3)); the Lean recursion producing successive pasts is s6:consOrder's recursion on R - l (PLAN decision 6).

**effort:** ~350 Lean lines, difficulty 3/5 (Types and laws ~60 lines; the four uniform/conditioning lemma families of SCHED-UNIFORM-LEMMAS ~300 lines (Lib).)

### `s7:consRound` — construction: The JV+* round step at round l >= 3 (the J-consumer) (s7.tex:231)

- **Manuscript referee status:** x2 (JV+* referees); the citation in step (f) was added in v6 (R7): no referee yet
- **Formalization:** Defs (EG/Defs/Quot/Round.lean: RoundInput + RoundInput.Valid (the past, as read by the step), Rules + Rules.Valid (the fixed rules), items/live/paid, ParObj, PAR colouring, hub groups and lists, SDR, junction assignment (e1)/(e2), loops, layers, ranks, the quotient Q_l : FGraph (QVert V), lift, Obj_l, LentJV_l, copies_l, pay_l, the (f) event goodXi). Existence of an xi in the (f) event: EG/Proof/Quot/Round.lean (Markov (b)); well-definedness facts: s7:lemWellDef.

**Statement (precise restatement).** INPUT: 3 <= l <= R and a past Past_l; from it the set J_l = Jlost_l ⊔ Jhub_l ⊔ Jfr_l ⊔ Jpar_l produced by JS-LC at round l, with (J1)-(J3) and (i)-(v) of s6:lemJplus; the stage-1 outcome (pool labels, LJV classes, JV-bad statuses). Round randomness xi_l = (eta_h, zeta_{h,u}, ≺_u) (s7:defSchedule). ITEMS: the edges of J_l \ Jlost_l. Vertices of an item: its port end(s) (in Q*_Z) and its centre (a hub h ∈ D_l for a Jhub item, a fresh centre x ∈ F_Z for a Jfr item; a Jpar item u–v has two port ends, no centre). A Jhub item is written (h,u). (a) PAYMENTS: paid (output as single edges): (a1) every edge of Jlost_l; (a2) every item with a vertex in Pool_l; (a3) every item with a JV-bad port end. The remaining items are LIVE; Live := set of vertices of live items; Live ∩ Pool_l = ∅. (b) PAR OBJECTS: every live Jpar item u–v is a PAR object with ends at u and v (u, v ∈ Q*_Z, Y(u) ≠ Y(v)). At each fresh centre x the live Jfr items at x are paired by a fixed rule into cherries u–x–u' (u ≠ u' since distinct items at x are distinct edges); a cherry is a PAR object with ends at u, u' and middle x; if the number of live Jfr items at x is odd, one of them (fixed rule) is paid (the unpaired fresh leg). The PAR objects are coloured greedily in a fixed order with colours from [3M_l] so that two PAR objects sharing a port or sharing a middle receive different colours. (c) HUB LISTS: c_h := number of live Jhub items at the hub h ∈ D_l; thult_l := ⌊M_l Hcd_l / 7⌋; K^HUB_l := 4M_l. h is ULTRA iff c_h > thult_l. For non-ultra h with c_h >= 1: its live items are split (fixed rule) into k_h := ⌈8 c_h / Hcd_l⌉ groups of at most ⌈Hcd_l/8⌉ items (possible as k_h⌈Hcd_l/8⌉ >= c_h); group i (1 <= i <= k_h) receives the list {eta_h(3i-2), eta_h(3i-1), eta_h(3i)} ⊆ [4M_l] (needs 3k_h <= 4M_l, s7:lemWellDef(ii)); lists of groups of h are pairwise disjoint and form a uniformly random sequence of k_h disjoint 3-subsets; lists of distinct hubs are independent. For ultra h every live item (h,u) is its own group with list zeta_{h,u}. (d) SDR: every port u carrying >= 1 live hub item chooses (fixed rule) pairwise distinct colours for its live hub items, each from its group's list (an SDR); if none exists, all live hub items of u are paid (SDR failure at u). Items that receive a colour are COLOURED HUB ITEMS; every port carries at most one coloured hub item of each HUB colour. (e) JUNCTIONS: Used(u) := ∅ for every port u, Used_kappa(h) := ∅ for every hub h and kappa ∈ [4M_l]. (e1) the coloured hub items of NON-ultra hubs are processed in a fixed order; item (h,u) of colour kappa receives as junction the first vertex w, in a fixed order of V(G), of Cand_l(u) \ Used(u) \ Used_kappa(h); then w is added to Used(u) and Used_kappa(h). (e2) for every port u, E'(u) := the ends at u of the PAR objects and of the coloured hub items (h,u) with h ultra, listed in a fixed order e_1..e_q; let w_1 ≺_u w_2 ≺_u ... be the elements of C(u) := Cand_l(u) \ Used(u) in the order ≺_u; e_i receives the junction w_i (well defined by s7:lemWellDef(v)). With Past_l and the lists fixed, e_i ↦ w_i is a uniformly random injection E'(u) → C(u), independent over ports. No payment for coincidences of junctions at ultra hubs. (e3) LOOPS: a PAR object whose two ends received the same junction is paid (a looped Jpar item costs 1 single edge, a looped cherry its 2 edges). Every end of a coloured hub item or of an unpaid PAR object now has a junction w ∈ Cand_l(u) ⊆ Pool_l with uw ∈ LJV_{Y(u),l}: the JUNCTION EDGE of that end. (f) MARKOV CHOICE: pay_l := number of edges paid in (d) and (e3); copies_l := |V(Q_l)|; both functions of (Past_l, xi_l). xi_l is chosen in {copies_l <= 4 E[copies_l | Past_l]} ∩ {pay_l <= 4 E[pay_l | Past_l]}, which has probability >= 1/2 given Past_l (s1:citMarkov (b),(c)). (g) LAYERS AND QUOTIENT: for kappa ∈ [3M_l] the PAR layer B^P_kappa is the multigraph on {[w] : w ∈ Pool_l} with one edge [w_1][w_2] for every unpaid PAR object of colour kappa whose ends have junctions w_1, w_2 (w_1 ≠ w_2 by (e3)). For kappa ∈ [4M_l] the HUB layer B^H_kappa is the bipartite multigraph with sides D_l and {[w] : w ∈ Pool_l} and one edge h[w] for every coloured hub item (h,u) of colour kappa with junction w. RANK SPLIT: in each layer the edges joining the same two vertices are listed in a fixed order; the i-th has rank i; for iota >= 1 the sub-layer B^{(iota)} is the spanning subgraph of rank-iota edges. Q_l := vertex-disjoint union of all sub-layers B^{P,(iota)}_kappa (kappa ∈ [3M_l], iota >= 1) and B^{H,(iota)}_kappa (kappa ∈ [4M_l], iota >= 1), isolated vertices of each sub-layer deleted; vertices of distinct sub-layers are distinct, so every cycle of Q_l lies in one sub-layer. (h) DECOMPOSE AND LIFT: Dec_l := a decomposition of E(Q_l) into f(Q_l) objects (fixed deterministic rule). Lift: a single edge of a PAR sub-layer (a PAR object) → its one (Jpar) or two (cherry) J-edges as single edges; a single edge h[w] of a HUB sub-layer (a coloured hub item (h,u)) → the single edge hu; a PAR-sub-layer cycle [w_0]...[w_{m-1}] (m >= 3, indices mod m; edge [w_i][w_{i+1}] = PAR object o_i with end p_i (junction w_i) and end q_i (junction w_{i+1})) → the closed walk w_0 p_0 (x_0) q_0 w_1 p_1 (x_1) q_1 w_2 ... q_{m-1} w_0 (x_i = middle of o_i if a cherry, omitted for a Jpar item); a HUB-sub-layer cycle h_0[w_0]h_1[w_1]...h_{m-1}[w_{m-1}]h_0 (m >= 2; h_i[w_i] = item (h_i,u_i) with junction w_i, [w_i]h_{i+1} = item (h_{i+1},u'_i) with junction w_i) → the closed walk h_0 u_0 w_0 u'_0 h_1 u_1 w_1 u'_1 h_2 ... u'_{m-1} h_0. OUTPUT: Obj_l := (single edges paid in (a), (b), (d), (e3)) together with (the lifted objects of all members of Dec_l); LentJV_l := the set of junction edges lying on lifted cycles. Junction edges assigned in (e) but not on a lifted cycle are not used (junk for their owner).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| J_l and its typed partition; J1-J3, (i)-(v) | s6:lemJplus | s6:lemJSLC, s6:lemJplus | no: s6 blueprint; enters as fields of RoundInput.Valid |
| D_l (hubs), A_Z, F_Z (fresh centres), Q*_Z (ports), Lost_Z | s2:defAncestors, s6:defLending | s2:defAncestors, s6:defLending | no: s2a/s6 blueprints; RoundInput fields hubs/fresh/ports/lost |
| J-consumer, JC1-JC3 | s6:defJconsumer | s6:defJconsumer | no: s6 blueprint (EG.Chain.IsJConsumerOutput) |
| Cand_l(u), Hcd_l, JV-bad | s7:defCand | s7:defCand | no: new (this chunk) |
| Pool_l, r(w) | s7:defPool | s7:defPool | no: new (this chunk) |
| xi_l = (lists, orders), roundLaw | s7:defSchedule | s7:defSchedule | no: new (this chunk) |
| RoundInput V / RoundInput.Valid | abstract past: G; l; M (ℕ); lam (= lambda_{l-2}); ancestor type A with ancRound, ancVerts, ljv (LJV_{Y,l}), lendGood; pool, poolRound; hubs, fresh, ports, lost; cls : V → A; jvBad; Jlost, Jhub, Jfr, Jpar. Valid: M >= 2^40; 2^10 M^10 <= Hcd; roles pairwise disjoint (J3); typed endpoints of the four J-classes; J ⊆ G.edges; J1 (≤ 1 Jhub edge per (hub, class), aggregated); J2 (every non-hub vertex has <= M-1 J-edges; \|J\| <= n(M-1)); cls u ∈ anc of round <= l-2 with u ∈ ancVerts (cls u); ljv Y ⊆ edges inside ancVerts Y, ljv pairwise disjoint, ljv ∩ J = ∅; lendGood (cls u) for ports; JV-good ports have \|cand u\| >= Hcd; pool ⊆ G.verts | s7:consRound (input paragraph) | no: new |
| Rules I / Rules.Valid | the fixed rules with restricted arguments (SCHED-RULE-DEPENDENCE): freshPairing (past), parColour (past; proper w.r.t. shared port/middle), hubGroups (past; k_h groups of size <= ⌈Hcd/8⌉), sdrChoice (past, lists; an SDR whenever one exists), e1Order (past, lists), vertOrder (fixed), e2Order (past, lists), rankOrder (any), decChoice (any decomposition of size f(Q_l)) | s7:consRound | no: new |
| Item, ParObj, End | Item := Sym2 V (an edge of J_l \ Jlost_l); ParObj := par (e : Sym2 V) \| cherry (x : V) (e₁ e₂ : Sym2 V); End := (object, port) | s7:consRound | no: new |
| QVert V | tagged copy: (kind : P \| H, kappa : ℕ, iota : ℕ, side : pool \| hub, v : V); Q_l : FGraph (QVert V) with vertex set = endpoints of edges | s7:consRound (g) | no: new (PLAN §3 decision 2: tagged vertex type, simple graph) |
| fnum, Obj, IsDecomp, cycleEdges | f(Q_l) and decompositions | s1:defObject | yes: EG.fnum, EG.Obj, EG.IsDecomp (EG/Defs/Objects.lean, Fnum.lean) |
| FinDist.expect, half_le_prob_le_four_mul_expect_and | Markov (b) | s1:citMarkov | yes: EG/Lib/Prob/Basic.lean |

**deps_declared** (manuscript \deps): s6:lemJplus, s6:defJconsumer, s7:defCand, s7:defPool, s7:defSchedule, s1:citMarkov

**deps_from_proof:** s6:lemJplus, s6:defJconsumer, s6:defLending, s2:defAncestors, s7:defCand, s7:defPool, s7:defSchedule, s7:lemWellDef, s1:citMarkov, s1:defObject, s3:defCOL

**deps_notes:** Construction. The text uses s6:lemJplus (types and properties of J_l), s6:defLending (Q*_Z, Lost_Z), s2:defAncestors (D_l, F_Z), s7:defCand/defPool (Cand, Pool, JV-bad), s3:defCOL (LJV_{Y,l}: junction edges), s1:defObject (f(Q_l), objects), s1:citMarkov (b),(c) for the claim in (f), and refers FORWARD to s7:lemWellDef (ii) and (v) for well-definedness of (c) and (e2) (and implicitly (i), (iv) for (b), (e1)). s6:defJconsumer is declared because the construction is the J-consumer; ms_deps flags it and s7:defCand, s7:defPool as unreferenced in the text.

**used_by:** s7:lemWellDef; s7:lemMULT; s7:lemSimple; s7:lemLift; s7:lemCC; s7:lemUltra; s7:lemPay; s7:lemUHsplit; s7:lemOneOutcome; s7:propCost; s7:thmJVps; s6:consOrder (step (4), as the J-consumer instance)

**randomness:** Given the past (a parameter), the only randomness is xi_l ~ roundLaw = uniform on Lists × Orders. Steps (a), (b), (c)-grouping, ultra status and Live are deterministic in the past; the lists (step (c)) and (d), (e1) depend on the Lists component; (e2), (e3), (g), (h), Q_l, copies_l, pay_l depend on all of xi_l. 'E[·|Past_l]' = expectation under roundLaw with the past fixed. The event of (f) is a subset of Xi; its probability >= 1/2 is Markov (b) under roundLaw.

**lean_shape:**

```lean
namespace EG.Quot
structure RoundInput (V : Type) [DecidableEq V] where
  G : FGraph V
  l : ℕ
  M : ℕ                       -- M_l (HB-M-INTEGER)
  lam : ℝ                     -- λ_{l-2}
  A : Type                    -- ancestors (round, address)
  [instA : Fintype A] [decA : DecidableEq A]
  ancRound : A → ℕ
  ancVerts : A → Finset V
  ljv : A → Finset (Sym2 V)   -- LJV_{Y,l} of the fixed stage-1 outcome
  lendGood : A → Prop
  pool : Finset V
  poolRound : V → ℕ
  hubs fresh ports lost : Finset V
  cls : V → A
  jvBad : V → Prop
  Jlost Jhub Jfr Jpar : Finset (Sym2 V)
noncomputable def RoundInput.Hcd (I) : ℝ := I.lam ^ 95 / (8 * (I.M : ℝ) ^ 2)
def RoundInput.cand (I) (u : V) : Finset V :=
  I.pool.filter fun w => I.poolRound w = I.ancRound (I.cls u) ∧ s(u, w) ∈ I.ljv (I.cls u)
structure RoundInput.Valid (I : RoundInput V) : Prop where
  M_ge : 2 ^ 40 ≤ I.M
  Hcd_ge : (2:ℝ) ^ 10 * (I.M : ℝ) ^ 10 ≤ I.Hcd
  roles : pairwise disjoint [I.hubs, I.fresh, I.ports, I.lost]            -- J3 + defLending
  typed : (∀ e ∈ I.Jhub, ∃ h ∈ I.hubs, ∃ u ∈ I.ports, e = s(h, u)) ∧ (Jfr: fresh–port) ∧
          (Jpar: port–port) ∧ (Jlost: lost–port) ∧ pairwise disjoint classes ∧ all ⊆ I.G.edges
  J1 : ∀ h (Y : I.A), ((I.Jhub.filter fun e => ∃ u ∈ I.ports, e = s(h, u) ∧ I.cls u = Y).card ≤ 1
  J2 : ∀ v ∉ I.hubs, degE (I.Jlost ∪ I.Jhub ∪ I.Jfr ∪ I.Jpar) v ≤ I.M - 1
  J2tot : (I.Jlost ∪ I.Jhub ∪ I.Jfr ∪ I.Jpar).card ≤ I.G.card * (I.M - 1)
  cls_round : ∀ u ∈ I.ports, 1 ≤ I.ancRound (I.cls u) ∧ I.ancRound (I.cls u) + 2 ≤ I.l
  cls_mem : ∀ u ∈ I.ports, u ∈ I.ancVerts (I.cls u)
  ljv_in : ∀ Y, ∀ e ∈ I.ljv Y, e ∈ I.G.edges ∧ ∀ v ∈ e, v ∈ I.ancVerts Y
  ljv_disj : ∀ Y Y', Y ≠ Y' → Disjoint (I.ljv Y) (I.ljv Y')
  ljv_J : ∀ Y, Disjoint (I.ljv Y) (I.Jlost ∪ I.Jhub ∪ I.Jfr ∪ I.Jpar)       -- s6:lemJplus(iii)
  lendGood_ports : ∀ u ∈ I.ports, I.lendGood (I.cls u)
  good_cand : ∀ u ∈ I.ports, ¬ I.jvBad u → I.Hcd ≤ (I.cand u).card      -- s7:lemCand(iv)
  pool_sub : I.pool ⊆ I.G.verts
structure Rules (I : RoundInput V) where
  freshPairing : V → List (Sym2 V × Sym2 V)            -- (b): past only
  parColour : ParObj V → ℕ                             -- (b): past only, values < 3M
  hubGroups : V → Sym2 V → ℕ                           -- (c): past only
  sdr : Lists I.G (4 * I.M) → Sym2 V → Option (Fin (4 * I.M))   -- (d)
  e1Order : Lists I.G (4 * I.M) → List (Sym2 V)        -- (e1)
  vertOrder : List V                                   -- (e1) fixed order of V(G)
  e2Order : Lists I.G (4 * I.M) → V → List (End V)     -- (e2)
  rank : Xi I.G (4 * I.M) → LayerEdge V → ℕ            -- (g): any
def Rules.Valid (R : Rules I) : Prop := ...            -- the specifications of (b)-(e2),(g)
structure RoundOutput (V) where
  Q : FGraph (QVert V)
  obj : List (Obj V)
  lentJV : Finset (Sym2 V)
  copies : ℕ        -- = Q.card
  pay : ℕ           -- edges paid in (d) and (e3)
noncomputable def roundStep (I) (R : Rules I) (ξ : Xi I.G (4 * I.M)) : RoundOutput V   -- total; fallbacks never used (s7:lemWellDef)
def goodXi (I) (R) (ξ) : Prop :=
  ((roundStep I R ξ).copies : ℝ) ≤ 4 * (roundLaw _ _ _).expect (fun ξ' => (roundStep I R ξ').copies) ∧
  ((roundStep I R ξ).pay : ℝ) ≤ 4 * (roundLaw _ _ _).expect (fun ξ' => (roundStep I R ξ').pay)
theorem exists_goodXi (I) (hI : I.Valid) (R) : 1/2 ≤ (roundLaw _ _ _).prob {ξ | goodXi I R ξ}   -- Markov (b)
```

**hazards:**

- **[blocker] ROUND-M-INTEGER.** Same decision as s2a HB-M-INTEGER / SCHED-M-INTEGER: [3M_l] (PAR palette), [4M_l] (HUB colours), K^HUB_l = 4M_l, eta_h : [4M_l] → [4M_l], '3k_h <= 4M_l' and 'at most M_l - 1 J-edges' all presuppose M_l ∈ ℕ. RoundInput.M must be a natural number; this requires the (R2) ceiling (proposed in s2a) before EG/Defs/Quot/Round.lean can be written.
- **[blocker] ROUND-RULE-DEPENDENCE.** Manuscript decision needed before Round.lean can be locked (the Rules argument types ARE the decision). See SCHED-RULE-DEPENDENCE. The construction has nine 'fixed' choices ((b) pairing, (b) greedy order/colouring, (c) grouping, (d) SDR, (e1) processing order, (e1) order of V(G), (e2) order of E'(u), (g) rank order, (h) Dec_l). s7:lemCC, s7:lemUltra, s7:lemPay(c) and s7:lemWellDef(iii) are FALSE for rules that read the orders ≺ (e.g. an (e2) end order chosen after looking at ≺_u can force coincidences), and (iii) of s7:lemWellDef fails if the grouping reads eta. Decision needed (wording, T0): rules (b),(c) are functions of the past, rules (d),(e1),(e2) of the past and the lists; (g),(h) arbitrary. Lean: Rules fields with exactly these argument types; Specs ∀ R : Rules I, R.Valid.
- **[risk] ROUND-INPUT-INTERFACE.** The construction reads the past only through J_l and its J+ properties, the pool, the classes, the LJV classes and the JV-bad statuses. The RoundInput.Valid field list above was extracted from every proof step of s7:lemWellDef, s7:lemMULT, s7:lemSimple, s7:lemLift, s7:lemCC, s7:lemUltra (and s7:lemPay): J1 aggregated over parts (MULT), J2 at ports and fresh centres + |J_l| <= n(M-1) (WellDef, CC, Ultra, Pay), J3 roles (Lift), typed endpoints (Lift, Pay), s6:lemJplus(iii) disjointness of E(H_Y) from E_l(Z) and of distinct E(H_Y) (Lift), u ∈ V(Y(u)) and r(u) <= l-2 (MULT, Lift), ports' classes lend-good (Lift (iii), JC1), JV-good ⇒ |Cand| >= Hcd (lemCand(iv)), M >= 2^40 and Hcd >= 2^10 M^10 (Gamma). mult_r(w) for s7:lemMULT additionally needs the set of ancestors of each round (field ancOfRound or a Fintype A with ancRound). s7:thmJVps must instantiate it from the real past (a lemma RoundInput.ofPast_valid using s6:lemJplus, s6:defLending, s7:lemCand, s2:propStructure). Getting this interface wrong silently changes all round Specs; it must be reviewed together with the s6 blueprint.
- **[risk] ROUND-TOTALITY.** Every step has a side condition proved only later: (b) greedy colouring succeeds (lemWellDef(i)), (c) 3k_h <= 4M_l (ii), (e1) the candidate set is non-empty (iv), (e2) |C(u)| >= |E'(u)| (v), (h) a decomposition with f(Q_l) objects exists. The Lean definitions must be total with explicit fallbacks (Option / default colour / default junction / Classical.choose) and s7:lemWellDef must state that no fallback is ever taken; otherwise the definitions depend on the lemmas (circular) or carry proof arguments that leak into every Spec. Every lemma about junctions must be stated for the total definition under I.Valid ∧ R.Valid.
- **[risk] ROUND-DATAMODEL-SIZE.** This is the largest single definition of s7 (items, PAR objects, cherries, colouring, groups, lists, SDR, a sequential fold for (e1) with two families of Used sets, per-port injections for (e2), loops, two layer families, ranks, a tagged simple graph, the lift of cycles). Estimated 900-1100 lines of Defs + API before any lemma. The sequential (e1) must be a List.foldl over the processing order with state (Used : V → Finset V, UsedK : V → Fin K → Finset V, junction : Item → Option V).
- **[risk] ROUND-LIFT-ROTATION.** Dec_l's cycles come as Obj.cycle (c : List (QVert V)) with arbitrary start and direction. The lift must read the alternation (HUB: hub copy / junction copy; PAR: junction copies only), recover each Q_l edge's PAR object or hub item from its (sub-layer, endpoints) via the rank-injectivity of s7:lemSimple, orient each object (which end has junction w_i), insert middles, and produce a Nodup list of V. For HUB cycles starting at a junction copy, rotate first. Proof obligations (Nodup, adjacency, cycleEdges membership) are in s7:lemLift(ii).
- **[note] ROUND-LAYERS-ENCODING.** The multigraph layers need no general MGraph type (PLAN §3 decision 2): a layer edge is indexed by its unpaid PAR object (PAR) or coloured hub item (HUB); its endpoints are (junction copies) resp. (hub, junction copy); the rank is its position among indices with the same endpoints in the (arbitrary) order R.rank. Q_l := FGraph on QVert V = tag × V with tag = (P/H, kappa, iota, side); edges = images of layer edges tagged by (kappa, rank); verts = endpoints of edges (so 'isolated vertices deleted' is definitional).
- **[note] ROUND-RANK-UNBOUNDED.** iota ranges over all of ℕ≥1; only ranks <= (number of layer edges) occur. Defining Q_l by its edge set (image of a finite index set) keeps everything finite; do not define it as a union over iota ∈ ℕ.
- **[note] ROUND-DEC-CHOICE.** 'Lexicographically first' decomposition: PLAN decision 7 — Dec_l := Classical.choose (exists a decomposition of Q_l.edges of length fnum Q_l.edges) (fnum is attained by definition). All properties are proved for every decomposition (s7:lemLift(ii)), so the rule is immaterial; the past of later rounds depends on Dec_l only through the deterministic choice (s7:remNonCirc(3)).
- **[note] ROUND-MARKOV-EXISTENCE.** (f) contains a probability claim (>= 1/2) that belongs in a lemma: goodXi is a Prop on Xi and 1/2 <= prob{goodXi} is EG.FinDist.half_le_prob_le_four_mul_expect_and applied to roundLaw (the '(c) conditional' part of s1:citMarkov is automatic because the past is a parameter). The choice of xi_l in the event is made in s7:lemOneOutcome.
- **[note] ROUND-PAY-DEF.** pay_l counts only edges paid in (d) and (e3) (random); payments of (a1)-(a3) and unpaired fresh legs (b) are deterministic in the past and are bounded by stage-1 functionals in s7:lemPay. An SDR failure at u pays all live hub items at u (each one edge); a looped Jpar item 1 edge, a looped cherry 2 edges.
- **[note] ROUND-PORT-TERM.** In s7 'port' means a vertex of ⋃_Z Q*_Z (a classed non-lost port), whereas s2:defAncestors' ports U_Z include fresh ports; fresh ports appear here as 'fresh centres' and lost ports as 'lost centres'. Define RoundInput.ports := ⋃ Q*_Z and never reuse the s2 name.
- **[note] ROUND-JPAR-CLASSES-UNUSED.** 'Y(u) ≠ Y(v)' for Jpar items (s6:lemEL) is stated but used by no proof in s7; the cherry pairing does not ask for distinct classes either. Do not put it into RoundInput.Valid unless s6 exports it anyway (harmless but unnecessary).
- **[note] ROUND-FIN-OFFSET.** Colours [3M_l], [4M_l] become Fin (3M), Fin (4M) (0-based); group i ∈ {0..k_h-1} gets {eta(3i), eta(3i+1), eta(3i+2)}, needing 3k_h <= 4M exactly as in the manuscript.
- **[note] ROUND-OBJ-LIST.** Obj_l must be a List (Obj V) (the count of objects matters: s7:propCost adds |Obj_l|); LentJV_l a Finset (Sym2 V). The JC predicates of s6:defJconsumer should be phrased with IsDecomp on (J_l ∪ LentJV_l) and WF of every object.

**effort:** ~1000 Lean lines, difficulty 4/5 (RoundInput/Rules ~150; items, PAR objects, colouring, groups, lists, SDR ~250; (e1) fold and (e2) injections ~200; layers, ranks, Q_l ~200; lift ~200; goodXi + Markov ~50.)

### `s7:lemWellDef` — lemma: The round step is well defined (s7.tex:393)

- **Manuscript referee status:** x2+RT; the citation in the proof of (iii) was added in v6 (R7): no referee yet
- **Formalization:** Spec (EG/Spec/Quot/WellDef.lean: five statements WellDefParStatement (i), WellDefListsStatement (ii), CuckooSDRStatement (iii), WellDefE1Statement (iv), WellDefE2Statement (v)); proofs in EG/Proof/Quot/WellDef.lean (+ EG/Proof/Quot/Cuckoo.lean for (iii))

**Statement (precise restatement).** For every past Past_l (3 <= l <= R) — in Lean: every I : RoundInput with I.Valid — and every admissible choice of the fixed rules: (i) PAR PALETTE: every PAR object shares a port or a middle with at most 2(M_l - 2) + ⌊(M_l - 1)/2⌋ - 1 < 3M_l other PAR objects, so the greedy colouring of (b) with [3M_l] succeeds; consequently every port carries at most one PAR object of each PAR colour, and every fresh centre is the middle of at most one cherry of each PAR colour. (ii) DISJOINT LISTS: every non-ultra hub h (with c_h >= 1) has k_h <= ⌈8M_l/7⌉ and 3k_h <= 4M_l. (iii) CUCKOO SDR: for every port u, P(SDR failure at u | Past_l) <= (K^HUB_l)^{-4} = (4M_l)^{-4}, the probability over xi_l ~ roundLaw (only the lists matter). (iv) GREEDY STEP: for every xi_l, step (e1) always finds a junction (Cand_l(u) \ Used(u) \ Used_kappa(h) ≠ ∅ when the coloured item (h,u) of colour kappa of a non-ultra hub is processed), and two coloured items of the same non-ultra hub h with the same colour kappa receive distinct junctions. (v) INJECTIONS: for every xi_l and every port u carrying a live item, with Used(u) its value after (e1): |Cand_l(u) \ Used(u)| >= Hcd_l - (M_l - 1) >= Hcd_l/2 >= M_l > |E'(u)|; so (e2) is well defined. Implicit hypotheses used: M_l >= 2^40 (definition (R2)); Hcd_l >= 2^10 M_l^10 (s7:lemCand(iv) / COL-JV row 11, needs Gamma1); (J2) of s6:lemJplus (every port carries <= M_l - 1 J-edges; every fresh centre <= M_l - 1 Jfr edges, s6:lemJplus(ii)).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| round step objects (items, live, PAR objects, groups, lists, SDR, Used, E'(u)) | s7:consRound | s7:consRound | no: new (this chunk) |
| RoundInput.Valid | the J+ interface | s7:consRound / s6:lemJplus | no: new |
| roundLaw, Lists | uniform law on xi_l | s7:defSchedule | no: new |
| Hall's theorem | Finset.all_card_le_biUnion_card_iff_exists_injective | s1:citHall | yes: Mathlib |
| Hcd_l, Cand_l(u) | s7:defCand | s7:defCand | no: new |

**deps_declared** (manuscript \deps): s7:consRound, s6:lemJplus, s7:lemCand, s3:lemCOLJV, s1:citHall

**deps_from_proof:** s7:consRound, s7:defSchedule, s6:lemJplus, s7:lemCand, s3:lemCOLJV, s1:citHall, s2:defHBtp

**deps_notes:** (i): J2 and s6:lemJplus(ii) (<= M_l - 1 J-edges at a port / Jfr edges at a fresh centre). (ii): definition of thult_l, k_h and M_l >= 21/4. (iii): s7:defSchedule (independent uniform eta_h, zeta_{h,u}), J2 (m <= M_l - 1), simplicity of G (distinct items at u have distinct hubs), s1:citHall, the union bound, K = 4M_l >= 2^42 >= 10^4 (s2:defHBtp: M_l >= 2^40). (iv), (v): s7:lemCand(iv) (JV-good ⇒ |Cand| >= Hcd_l), s3:lemCOLJV row 11 (Hcd_l >= 2^10 M_l^10), J2, (a3) of s7:consRound (live ⇒ JV-good port). ms_deps: s7:consRound declared but not \ref'd in the proof (used throughout); s2:defHBtp (M_l >= 2^40) undeclared.

**used_by:** s7:consRound ((b), (c), (e1), (e2) well defined); s7:lemMULT (indirectly); s7:lemLift ((i)); s7:lemCC ((i), (v)); s7:lemUltra ((v)); s7:lemPay ((c): (iii), (v)); s7:lemUHsplit ((iv), (v))

**randomness:** (i), (ii), (iv), (v): deterministic, for every past and every xi_l. (iii): probability over xi_l ~ roundLaw with the past fixed; the event depends only on the Lists component (the lists of the live hub items at u: for non-ultra h the image under eta_h of a fixed 3-set determined by the past, for ultra h the coordinate zeta_{h,u}); these m lists are independent (distinct hubs ⇒ distinct coordinates) and each is a uniform 3-subset of [4M_l].

**lean_shape:**

```lean
-- EG/Spec/Quot/WellDef.lean  (all ∀ V [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid → ...)
def WellDefParStatement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid →
  (∀ o ∈ parObjs I, ((parObjs I).filter fun o' => o' ≠ o ∧ (sharePort o o' ∨ shareMiddle o o')).card < 3 * I.M) ∧
  (∀ u, ∀ κ, ((parObjs I).filter fun o => u ∈ o.ports ∧ R.parColour o = κ).card ≤ 1) ∧
  (∀ x, ∀ κ, ((cherries I R).filter fun o => o.middle = x ∧ R.parColour o = κ).card ≤ 1)
def WellDefListsStatement : Prop := ∀ V _ I, I.Valid → ∀ h ∈ I.hubs, ¬ isUltra I h → 1 ≤ cLive I h →
  kGroups I h ≤ ⌈(8 * I.M : ℝ) / 7⌉₊ ∧ 3 * kGroups I h ≤ 4 * I.M
def CuckooSDRStatement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid → ∀ u ∈ I.ports,
  (roundLaw I.G (4 * I.M) _).prob {ξ | sdrFails I R ξ.1 u} ≤ ((4 * I.M : ℕ) : ℝ)⁻¹ ^ 4
  -- sdrFails := ¬ ∃ SDR (Hall form), independent of R.sdr
def WellDefE1Statement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid → ∀ ξ,
  (∀ it ∈ colouredNonUltra I R ξ.1, (e1Junction I R ξ.1 it).isSome) ∧
  (∀ it it' ∈ colouredNonUltra I R ξ.1, it ≠ it' → hub it = hub it' → colour it = colour it' →
      e1Junction I R ξ.1 it ≠ e1Junction I R ξ.1 it')
def WellDefE2Statement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid → ∀ ξ, ∀ u ∈ livePorts I,
  I.Hcd - (I.M - 1 : ℝ) ≤ ((I.cand u \ used I R ξ.1 u).card : ℝ) ∧ I.Hcd - (I.M - 1 : ℝ) ≥ I.Hcd / 2 ∧
  I.Hcd / 2 ≥ I.M ∧ (endsE' I R ξ.1 u).card < I.M
```

**hazards:**

- **[risk] WD-SDR-UNIONBOUND.** (iii) is the hardest numerical step of the chunk. Formal route: Hall (Mathlib, iff form) ⇒ failure ⊆ ⋃_{4 <= s <= m} ⋃_{|S| = s} ⋃_{|T| = s-1} {all lists of S ⊆ T}; independence of the m lists (distinct hubs ⇒ distinct coordinates of the uniform product; SCHED-UNIFORM-LEMMAS (1),(2)); P(list ⊆ T) = C(s-1,3)/C(K,3); then the analytic bound Σ_s T_s <= K^{-4}. Re-derived: T_s <= e^{2s-1}4^{-s}s^{-s}(s-1)^{2s+1}K^{-s-1} <= a_s = (1/e)(s/K)(e^2 s/(4K))^s; a_4 = 4e^7 K^{-5} = 4386.5 K^{-5} < 4400 K^{-5}; a_{s+1}/a_s <= (5e^3/16)(s+1)/K <= 6.2768·(1/13 + 10^{-4}) = 0.4772 < 0.49 for 4 <= s < K/13, K >= 10^4; for s > K/13, a_s <= (e^2/16)^s/(4e) with e^2/16 = 0.4618 <= 0.47; total <= 8800K^{-5} + 2·0.47^{K/13} <= K^{-4} for K >= 10^4. All correct. Lean cost: binomial estimates C(m,s) <= (em/s)^s need s! >= (s/e)^s (Mathlib Stirling-type bounds or a direct induction), real powers 0.47^{K/13}, e bounds (Real.exp_one_lt_d9). Since K >= 2^42 in every use, a Lean proof may replace the manuscript's series by cruder bounds (the Spec only fixes (4M_l)^{-4}). ~500 lines.
- **[note] WD-SDR-INDEP-SIMPLE.** Independence of the m lists at u uses that the live hub items at u are distinct edges hu, so their hubs are distinct (G simple; in Lean items are distinct Sym2 values at u, hence distinct other ends). It also uses that ultra/non-ultra status, grouping and group index are functions of the past (ROUND-RULE-DEPENDENCE): otherwise the non-ultra list is not a fixed-set image under eta_h.
- **[note] WD-HYPS.** Hypotheses to carry (via RoundInput.Valid): M_l >= 2^40 (needed: M_l >= 21/4 in (ii), K = 4M_l >= 10^4 in (iii)); Hcd_l >= 2^10 M_l^10 (needed: (7/8)Hcd_l > M_l - 2 in (iv); Hcd_l - (M_l - 1) >= Hcd_l/2 >= M_l in (v)); J2 at ports and fresh centres. The statement 'for every past' hides these; without Hcd >= 2^10 M^10 (a Gamma consequence) (iv) and (v) fail.
- **[note] WD-I-COUNT.** (i) counts: each port of the object carries <= M_l - 2 further live items and each further PAR object at that port uses exactly one of them (a PAR object has two ends at distinct ports and uses one item per end); the middle is the middle of <= ⌊(M_l-1)/2⌋ - 1 further cherries. 2(M_l-2) + (M_l-1)/2 - 1 < 3M_l. A PAR object never conflicts through 'port = middle' because ports ⊆ ⋃Q*_Z and middles ⊆ ⋃F_Z are disjoint (J3). In Lean the greedy colouring can be replaced by 'any proper colouring into Fin (3M)' (Rules.Valid) plus the existence lemma (degree < palette ⇒ greedy succeeds).
- **[note] WD-II-ARITH.** (ii): c_h <= thult_l = ⌊M_l Hcd_l/7⌋ <= M_l Hcd_l/7 ⇒ 8c_h/Hcd_l <= 8M_l/7 ⇒ k_h <= ⌈8M_l/7⌉ <= 8M_l/7 + 1 ⇒ 3k_h <= 24M_l/7 + 3 <= 4M_l iff M_l >= 21/4. Exact; Nat.ceil_le / Nat.ceil_mono.
- **[note] WD-IV-GROUPS.** (iv) uses: the lists of the groups of a non-ultra h are pairwise disjoint (eta_h injective), so all coloured items of h with colour kappa lie in ONE group (<= ⌈Hcd_l/8⌉ items, so |Used_kappa(h)| <= ⌈Hcd_l/8⌉ - 1 < Hcd_l/8), and |Used(u)| <= M_l - 2 (one junction per earlier (e1) item at u). Remaining >= Hcd_l - (M_l - 2) - Hcd_l/8 > 0. The Lean (e1) fold must maintain these invariants explicitly.
- **[note] WD-V-LIVE-JVGOOD.** (v) is claimed for 'every port carrying a live item'; such a port is JV-good because (a3) pays every item with a JV-bad port end, so |Cand_l(u)| >= Hcd_l by s7:lemCand(iv) (RoundInput.good_cand). |Used(u)| + |E'(u)| <= M_l - 1 because non-ultra coloured items, ultra coloured items and PAR ends at u correspond to pairwise distinct live items at u (J2).
- **[note] WD-REMARK-NOT-USED.** The 'Remark on numerics (not used)' (union bound maximum 0.0502 near M_l = 19, limit 9/256) must not be formalized; it is explicitly unused and small-M values are outside the hypothesis M_l >= 2^40.
- **[note] WD-FORWARD-DEFINITION.** s7:consRound refers forward to (ii) and (v) for well-definedness; with the total definitions of ROUND-TOTALITY the lemma is stated about the total construction ('no fallback is taken'), which removes the circularity.

**effort:** ~1000 Lean lines, difficulty 4/5 ((i) ~120 (proper colouring existence); (ii) ~40; (iii) ~550 (Hall, union bound, independence, uniform 3-subsets, series numerics); (iv) ~150 (fold invariants); (v) ~100.)

### `s7:lemMULT` — lemma: Lemma MULT (HUB-layer multiplicities are bounded by ancestor multiplicities) (s7.tex:517)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec (EG/Spec/Quot/MULT.lean: MultStatement (inequality) + MultSublayerStatement (the two sub-layer counts)); proof EG/Proof/Quot/MULT.lean

**Statement (precise restatement).** Notation (s7.tex:513-515): for a HUB colour kappa, a hub h and w ∈ Pool_l, m_kappa(h,w) := number of edges h[w] of B^H_kappa = number of coloured hub items (h,u) of colour kappa with junction w. Let 3 <= l <= R, any past, any xi_l, kappa ∈ [4M_l], h a hub (h ∈ D_l; for other h, m = 0), r >= 1 and w ∈ Pool_{l,r}. Then m_kappa(h,w) <= mult_r(w) <= mu_r(w), where mult_r(w) = number of ANCESTORS of round r whose vertex set contains w and mu_r(w) = number of round-r pre-parts containing w (s2:defAncestors). Moreover: #{iota >= 1 : [w] is not isolated in B^{H,(iota)}_kappa} = max_{h} m_kappa(h,w), and #{iota >= 1 : h is not isolated in B^{H,(iota)}_kappa} = max_{w} m_kappa(h,w). (The proof gives more: Σ_kappa m_kappa(h,w) <= mult_r(w), since the colour is never used.)

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| coloured hub items, junctions, B^H_kappa, ranks, sub-layers | s7:consRound (d), (e), (g) | s7:consRound | no: new (this chunk) |
| mult_r(w), mu_r(w) | numbers of round-r ancestors / pre-parts containing w (by address) | s2:defAncestors | no: s2a blueprint (EG.HB.mult, EG.HB.mu) |
| Pool_{l,r}, r(w) | s7:defPool | s7:defPool | no: new |
| Cand_l(u) | s7:defCand | s7:defCand | no: new |
| J1 | at most one Jhub edge of class Y at h in J_l, aggregated over all parts of round l | s6:lemJplus | no: RoundInput.Valid.J1 |

**deps_declared** (manuscript \deps): s7:consRound, s6:lemJplus, s7:defCand, s7:defPool, s2:propOV

**deps_from_proof:** s7:consRound, s7:defCand, s7:defPool, s6:lemJplus, s6:defDesign, s2:defAncestors, s2:propOV

**deps_notes:** Junction of (h,u_i) ∈ Cand_l(u_i) ⊆ Pool_{l,r(u_i)} (s7:consRound (e), s7:defCand); single pool label ⇒ r(u_i) = r (s7:defPool); w ∈ Cand ⊆ N_{H_{Y(u_i)}}(u_i) ⊆ V(Y(u_i)) (s7:defCand; H_Y a graph on V(Y), s2:defAncestors); classes Y(u_i) pairwise distinct by J1 (s6:lemJplus); Y(u_i) are ancestors (s6:defDesign); mult_r(w) <= mu_r(w) is s2:propOV (F11). The sub-layer statements use only the rank definition (s7:consRound (g)).

**used_by:** s7:lemUltra (iii); s7:lemUHsplit (ii): non-ultra hub copies and junction copies; s7:lemCC (the analogous PAR statement 'as in Lemma MULT')

**randomness:** None: deterministic for every past and every xi_l.

**lean_shape:**

```lean
-- EG/Spec/Quot/MULT.lean
def MultStatement : Prop := ∀ V [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
  ∀ ξ h w, w ∈ I.pool →
    (∑ κ : Fin (4 * I.M), hubMult I R ξ κ h w) ≤ I.mult (I.poolRound w) w ∧
    ∀ κ, hubMult I R ξ κ h w ≤ I.mult (I.poolRound w) w
-- I.mult r w := ((Finset.univ : Finset I.A).filter fun Y => I.ancRound Y = r ∧ w ∈ I.ancVerts Y).card
-- (s2 part, separate: HB.mult r w ≤ HB.mu r w is s2:propOV (F11); the instantiation lemma identifies I.mult with HB.mult)
def MultSublayerStatement : Prop := ∀ V _ (I : RoundInput V), I.Valid → ∀ R, R.Valid → ∀ ξ κ w h,
  ((Finset.range (bigRank I R ξ)).filter fun ι => poolCopy .H κ (ι+1) w ∈ (roundStep I R ξ).Q.verts).card
      = I.hubs.sup (fun h' => hubMult I R ξ κ h' w) ∧
  ((Finset.range (bigRank I R ξ)).filter fun ι => hubCopy κ (ι+1) h ∈ (roundStep I R ξ).Q.verts).card
      = I.pool.sup (fun w' => hubMult I R ξ κ h w')
```

**hazards:**

- **[risk] MULT-J1.** The lemma rests entirely on (J1) of s6:lemJplus in its AGGREGATED form: at most one Jhub edge of class Y at the hub h in round l over ALL standalone parts of round l. The manuscript lists this as one of the most delicate points and 'a valid run on which JS-LC emits two Jhub edges of one class at one hub in one round' as a refutation target (s7:ssecNotEstablished). RoundInput.Valid.J1 must be stated aggregated (filter over all of Jhub, not per part), and the s6 Spec of lemJplus must export exactly this form; a per-part J1 would make MULT unprovable (m_kappa(h,w) could reach the number of parts containing h).
- **[note] MULT-VY.** w ∈ V(Y(u_i)) needs LJV_{Y,l} ⊆ E(H_Y) and every edge of H_Y inside V(Y) (EG.FGraph.edge_verts; RoundInput.Valid.ljv_in). This is 'where it matters that candidates are taken in the class graph H_{Y(u_i)} itself'.
- **[note] MULT-ADDRESS.** Distinct classes are distinct ANCESTORS (addresses), and mult_r counts ancestors by address (s2a HB-ADDRESS-IDENTITY, ANC-BIJECTION). Two ancestors with equal vertex sets are counted twice by mult_r and are also distinct classes, so the inequality is consistent only with address identity on both sides.
- **[note] MULT-SUBLAYER-COUNT.** The sub-layer statements need the rank definition 'the edges on one pair get ranks 1..m' (R.rank a bijection onto 1..m per pair). State the count as the number of iota with a vertex copy present; 'max over h' is Finset.sup over I.hubs (0 if none). For a hub h, 'max_w' ranges over the pool.
- **[note] MULT-COLOUR-UNUSED.** The colour kappa plays no role in the first inequality; the summed version Σ_kappa m_kappa(h,w) <= mult_r(w) is free and may simplify s7:lemUHsplit. The second inequality mult_r <= mu_r belongs to s2 (propOV F11) and is only transported.

**effort:** ~180 Lean lines, difficulty 2/5 (Injection of items into classes + card bound ~80; rank/sub-layer counts ~100 (shared with lemCC's PAR analogue).)

### `s7:lemSimple` — lemma: Q_l is simple (s7.tex:553)

- **Manuscript referee status:** x2+RT
- **Formalization:** Mostly definitional with the tagged encoding (Q_l : FGraph (QVert V) is simple by type); Spec (EG/Spec/Quot/Simple.lean: SimpleStatement = rank-injectivity + looplessness facts that the lift needs); proof EG/Proof/Quot/Simple.lean

**Statement (precise restatement).** For every past and xi_l: every sub-layer of s7:consRound(g) is a simple graph: it has no parallel edges (at most one edge of rank iota between any two vertices); PAR sub-layers have no loops (an edge [w_1][w_2] has w_1 ≠ w_2, because looped PAR objects were paid in (e3)); HUB sub-layers are bipartite between hubs and junction copies [w], and for any edge h[w] the hub h and the junction w are distinct vertices of G (h is the hub of a coloured, hence live, item, so h ∉ Pool_l by (a2), while w ∈ Pool_l). Consequently Q_l is a simple graph without isolated vertices; every edge of Q_l is the image of exactly one unpaid PAR object or coloured hub item.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| layers, ranks, sub-layers, Q_l, QVert | s7:consRound (g) | s7:consRound | no: new |
| FGraph | finite simple graph with verts/edges finsets | s1:convGraphs | yes: EG.FGraph |

**deps_declared** (manuscript \deps): s7:consRound

**deps_from_proof:** s7:consRound

**deps_notes:** Uses (a2) (Live ∩ Pool = ∅), (e3) (loops paid) and the rank definition of s7:consRound only.

**used_by:** s7:lemLift (ii); s7:thmJVps (Q_l simple, the induction applies); s7:remNonCirc (2)

**randomness:** None: deterministic for every past and every xi_l.

**lean_shape:**

```lean
-- EG/Spec/Quot/Simple.lean
def SimpleStatement : Prop := ∀ V [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid → ∀ ξ,
  let out := roundStep I R ξ
  -- every edge of Q comes from exactly one layer edge (rank injectivity)
  (∀ e ∈ out.Q.edges, ∃! le : LayerEdge V, le ∈ layerEdges I R ξ ∧ layerEdgeSym2 I R ξ le = e) ∧
  -- PAR edges join distinct junctions; HUB edges join a live hub and a pooled junction, distinct in V
  (∀ o ∈ unpaidParObjs I R ξ, junctionAt I R ξ o.end₁ ≠ junctionAt I R ξ o.end₂) ∧
  (∀ it ∈ colouredHubItems I R ξ, hub it ≠ junctionOf I R ξ it) ∧
  -- no isolated vertices
  (∀ v ∈ out.Q.verts, ∃ e ∈ out.Q.edges, v ∈ e)
-- 'Q_l is a simple graph' itself is by type (FGraph.loopless, Finset edges).
```

**hazards:**

- **[note] SIMPLE-TAGGED-DEFINITIONAL.** With QVert = tag × V and hub copies tagged 'hub side', junction copies 'pool side', a HUB edge can never be a loop, whatever h and w are; 'h ≠ w as vertices of G' is then a separate fact (still true by (a2)) needed only if someone identifies [w] with w. In Lean, Q_l : FGraph is simple by construction; the substantive content that must be proved is: (1) looplessness of PAR edges (w_1 ≠ w_2 from (e3)), required to build Q_l as an FGraph at all (FGraph.loopless); (2) rank-injectivity: the map (layer edge ↦ tagged Sym2) is injective, so that each Q_l edge has a unique PAR object / hub item (needed by the lift and by 'every item lies in exactly one edge of Q_l').
- **[note] SIMPLE-DEF-ORDER.** Because FGraph requires loopless edges, the Q_l definition must filter or prove w_1 ≠ w_2 at definition time: define PAR layer edges only for unpaid (non-looped) objects, which makes (1) definitional, and prove (2) here.
- **[note] SIMPLE-NO-ISOLATED.** 'Isolated vertices deleted' is definitional if Q_l.verts := endpoints of Q_l.edges; then |V(Q_l)| = copies_l counts exactly the non-isolated copies used in s7:lemCC/lemUltra/lemUHsplit.

**effort:** ~120 Lean lines, difficulty 2/5 (Rank-injectivity ~60; looplessness and non-isolation ~40; glue ~20.)

### `s7:lemLift` — lemma: Lemma JV-L: the lift (s7.tex:575)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec (EG/Spec/Quot/Lift.lean: LiftRolesStatement (i), LiftDecompStatement (ii), LiftAccountingStatement (iii), LiftJConsumerStatement (iv)); proof EG/Proof/Quot/Lift.lean (largest proof file of the chunk)

**Statement (precise restatement).** Let 3 <= l <= R; fix any past (I : RoundInput with I.Valid, admissible rules) and any xi_l; Live = the set of live vertices of round l. (i) Live ∩ Pool_l = ∅; every port carries at most one PAR object of each PAR colour and at most one coloured hub item of each HUB colour; hence at most one edge of each sub-layer is an object/item with an end at a given port; every fresh centre is the middle of at most one cherry of each PAR colour; hubs (D_l), fresh centres (⋃F_Z) and ports (⋃Q*_Z) are pairwise disjoint. (ii) For EVERY decomposition Dec of E(Q_l) into cycles and single edges: the lift (s7:consRound(h)) of each cycle of Dec is a cycle of G (length Σ_i(3 or 4) >= 3m >= 9 for a PAR cycle of length m >= 3; length 4m >= 8 for a HUB cycle of length 2m, m >= 2); the lift of each single edge of Dec is one or two single edges of G (edges of J_l); the lifts of distinct members of Dec are pairwise edge-disjoint; hence the lift of Dec is a family of at most 2|Dec| pairwise edge-disjoint objects of G. (iii) Every item is either paid (in (a2), (a3), (b), (d) or (e3)) or lies in exactly one edge of Q_l. Every junction edge uw is the junction edge of at most one item-end, and that end is at u, never at w. The edge uw lies in exactly one lent class, namely LJV_{Y(u),l}, where Y(u) is a lend-good ancestor of round <= l-2 (the only consumer of this class is the round-l step). Junction edges lie in E_r(Y) for ancestors Y of rounds r <= l-2, items lie in E_l(Z) for Z ∈ Std_l, and these edge sets are disjoint. (iv) Consequently the round step, applied at every round 3 <= l <= R, is a J-consumer: Obj_l and LentJV_l satisfy JC1-JC3 of s6:defJconsumer (JC1: LentJV_l ⊆ ⋃{LJV_{Y,l} : Y lend-good of round <= l-2}; JC2: the objects of Obj_l are pairwise edge-disjoint cycles and single edges of G whose union is exactly J_l ∪ LentJV_l; JC3: Obj_l uses no other edge); and the objects of Obj_l other than paid single edges number at most 2|Dec_l| = 2 f(Q_l).

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| round step, lift, Obj_l, LentJV_l, junction edges | s7:consRound (e), (h) | s7:consRound | no: new |
| J-consumer, JC1-JC3 | s6:defJconsumer | s6:defJconsumer | no: s6 blueprint |
| Obj, Obj.WF, IsDecomp, cycleEdges, fnum | objects, decompositions and f | s1:defObject | yes: EG.Obj, EG.IsDecomp, EG.fnum |
| E_r(Y), E_l(Z), lend-good, Lend_Y, LJV_{Y,l} | s2:defHBtp (R5), s6:defLending, s3:defCOL | s2/s3/s6 | no: enter as RoundInput fields (ljv_J, ljv_disj, lendGood_ports) |

**deps_declared** (manuscript \deps): s7:consRound, s7:lemSimple, s7:lemWellDef, s6:lemJplus, s6:defJconsumer, s3:defCOL, s2:propStructure

**deps_from_proof:** s7:consRound, s7:lemSimple, s7:lemWellDef, s6:lemJplus, s6:defJconsumer, s6:defLending, s6:defDesign, s3:defCOL, s2:propStructure, s1:defObject

**deps_notes:** (i): (a2), s7:lemWellDef(i), (d), J3 of s6:lemJplus. (ii): s7:lemSimple (m >= 3 PAR, bipartite HUB), (i), J3, Live ∩ Pool = ∅, (e1)/(e2) injectivity of junctions at a port, s6:lemJplus(iii) and s2:propStructure(iii) (junction edges ⊆ E(H_Y) ⊆ E_r(Y) disjoint from items ⊆ E_l(Z)). (iii): s3:defCOL (one colour per edge of Lend_Y; COL(g) exclusive consumer), s2:propStructure(iii) (E(H_Y) pairwise edge-disjoint), s6:defLending (Q*_Z excludes ports with lend-bad class), s6:defDesign (r(u) <= l-2). (iv): s6:defJconsumer, (ii), (iii). s1:defObject (cycle objects) and s6:defLending, s6:defDesign are undeclared.

**used_by:** s7:propCost (the object count 2 f(Q_l)); s7:thmJVps; s6:thmMIXC (via the J-consumer interface JC1-JC3); s6:lemLent (LentJV sets)

**randomness:** None: deterministic for every past and every xi_l (and (ii) for every decomposition Dec).

**lean_shape:**

```lean
-- EG/Spec/Quot/Lift.lean
def LiftDecompStatement : Prop := ∀ V [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid → ∀ ξ,
  let Q := (roundStep I R ξ).Q
  ∀ Dec : List (Obj (QVert V)), IsDecomp (Q.edges : Set _) Dec → (∀ o ∈ Dec, o.WF) →
    let L := liftDec I R ξ Dec                           -- List (Obj V)
    (∀ o ∈ L, o.WF ∧ ∀ e ∈ o.edges, e ∈ I.G.edges) ∧
    (L.flatMap Obj.edges).Nodup ∧                         -- pairwise edge-disjoint, each edge once
    L.length ≤ 2 * Dec.length ∧
    (∀ c ∈ Dec, c.isCycle → (liftObj I R ξ c).length = 1 ∧ ∀ o ∈ liftObj I R ξ c, o.isCycle)
def LiftAccountingStatement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid → ∀ ξ,
  (∀ it ∈ items I, isPaid I R ξ it ∨ ∃! e ∈ (roundStep I R ξ).Q.edges, it ∈ itemsOfQEdge I R ξ e) ∧
  (∀ uw ∈ junctionEdges I R ξ, ∃! en, junctionEdgeOf I R ξ en = uw ∧ ...) ∧
  (∀ en u w, junctionEdgeOf I R ξ en = s(u, w) → endPort en = u → w ∉ I.ports ∧ w ∈ I.pool) ∧
  (∀ en, ∀ Y, junctionEdgeOf I R ξ en ∈ I.ljv Y ↔ Y = I.cls (endPort en)) ∧
  (∀ en, I.lendGood (I.cls (endPort en)) ∧ I.ancRound (I.cls (endPort en)) + 2 ≤ I.l)
def LiftJConsumerStatement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid → ∀ ξ,
  let out := roundStep I R ξ
  Chain.JC1 I out.lentJV ∧                                -- ⊆ ⋃ {I.ljv Y | lend-good, round ≤ l-2}
  IsDecomp ((I.Jlost ∪ I.Jhub ∪ I.Jfr ∪ I.Jpar ∪ out.lentJV : Finset _) : Set _) out.obj ∧   -- JC2 + JC3
  (∀ o ∈ out.obj, o.WF) ∧
  ((out.obj.filter fun o => ¬ isPaidSingle I R ξ o).length ≤ 2 * fnum out.Q.edges)
```

**hazards:**

- **[risk] LIFT-CYCLE-WF.** (ii) is where 'a lifted sub-layer cycle that repeats a vertex' (a refutation target) is excluded. The distinctness argument combines six facts: junction copies in one sub-layer are distinct vertices of G; ports of distinct same-colour objects/items are distinct (i); p_i ≠ q_i (two ends of an object at distinct ports; u ≠ u' for cherries by simplicity); middles of same-colour cherries are distinct (i); ports, middles, hubs pairwise disjoint (J3); live vs pooled (a2). Re-derived: correct. Lean cost is high: the lift is a function on List (QVert V) with rotations (ROUND-LIFT-ROTATION), and Nodup/adjacency/length >= 3 must be proved for the output list to be Obj.WF; the edge sets of the lift must be computed to prove edge-disjointness across members. ~500 lines.
- **[risk] LIFT-JC-INTERFACE.** (iv) must produce EXACTLY the predicate of the s6 Spec of s6:defJconsumer (PLAN decision 6: s6 proves MIX-C for any consumer satisfying JC1-JC3, s7 supplies the instance). Recommended phrasing of JC2+JC3 in both places: IsDecomp (J_l ∪ LentJV_l) Obj_l with every object WF. This needs J_l ∩ LentJV_l = ∅ (items ⊆ E_l(Z), junction edges ⊆ E(H_Y), disjoint by s6:lemJplus(iii); RoundInput.Valid.ljv_J) and the cover statement 'every item is paid or covered by the lift of its Q_l edge'. If the s6 blueprint phrases JC2 differently (e.g. as a Finset union equality without multiplicity), the object count used by s7:propCost may silently lose the 'each edge once' information.
- **[note] LIFT-COLG-META.** 'The only consumer of this class is the round-l step' (COL(g)) is a property of the whole assembly (s6:consOrder, s6:lemLent), not a proposition about one round; formalize (iii)'s class statement as 'uw ∈ ljv Y ↔ Y = Y(u)' plus lend-goodness and the round bound, and leave exclusivity to the s6 recursion (JC1 + s6:lemLent).
- **[note] LIFT-LENDGOOD.** 'Y(u) is lend-good' uses u ∈ Q*_Z = Q_Z \ Lost_Z and Lost_Z ⊇ {classed ports with lend-bad class} (s6:defLending): RoundInput.Valid.lendGood_ports must be instantiated from s6:defLending, not assumed.
- **[note] LIFT-ANY-DEC.** (ii) is quantified over EVERY decomposition of E(Q_l) into cycles and single edges (not only Dec_l); with Obj.WF this includes the requirement that cycles are simple cycles of Q_l (length >= 3, Nodup). Keep the universal form: s7:thmJVps only needs Dec_l, but the universal statement is what makes the choice rule immaterial.
- **[note] LIFT-DISJ-SOURCES.** Edge-disjointness uses three sources of disjointness from outside s7: E(H_Y) pairwise disjoint over ancestors (s2:propStructure(iii)), E(H_Y) ⊆ E_r(Y) disjoint from E_l(Z) (s6:lemJplus(iii)), and one colour per Lend edge (s3:defCOL). In RoundInput these are ljv_disj and ljv_J; they must be derived in the instantiation lemma.
- **[note] LIFT-COUNT.** 'Objects other than paid single edges number at most 2|Dec_l| = 2f(Q_l)': a PAR single edge lifts to 1 or 2 single edges, a HUB single edge to 1, a cycle to 1 cycle. Dec_l has length fnum Q_l.edges (ROUND-DEC-CHOICE), so the bound is 2·fnum; Q_l.edges is loopless (FGraph) so fnum is used on a loopless set as CONVENTIONS require.

**effort:** ~900 Lean lines, difficulty 4/5 ((i) ~60; (ii) PAR and HUB cycle lifts ~450, single edges ~50, disjointness ~150; (iii) ~100; (iv) JC1-JC3 and the count ~100.)

### `s7:lemCC` — lemma: Lemma CC: PAR copies (s7.tex:715)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec (EG/Spec/Quot/CC.lean: CCPartnerStatement (i), CCMaxStatement (ii), CCCopiesStatement (iii)); proof EG/Proof/Quot/CC.lean (needs the conditioning lemmas of SCHED-UNIFORM-LEMMAS)

**Statement (precise restatement).** Setting (s7.tex:700-713): 3 <= l <= R, the past fixed; 'the lists are fixed' = eta_h and zeta_{h,u} fixed; then (a)-(d), (e1) are determined and only the orders ≺_u are random (independent, uniform). For a PAR colour kappa and w ≠ w' in Pool_l, m_kappa(w,w') := number of edges [w][w'] of B^P_kappa; [w] is non-isolated in exactly max_{w'} m_kappa(w,w') of the sub-layers B^{P,(iota)}_kappa. Fix a PAR colour kappa ∈ [3M_l] and w ∈ Pool_l. For every port x carrying a PAR object of colour kappa let I_x := 1[the end at x of the kappa-object at x receives junction w] (well defined: x carries exactly one kappa-object and it has exactly one end at x). Let S_w := set of PAR objects of colour kappa with exactly one end whose junction is w (a function of (I_x)_x). (i) The partner ports v_o (o ∈ S_w; the ports of the ends whose junction is not w) are pairwise distinct. Conditionally on (I_x)_x (for every value pattern of positive probability), the junctions of the partner ends are independent, and the junction of the partner end of o is uniform on (Cand_l(v_o) \ Used(v_o)) \ {w}; in particular it equals a given w' with probability <= 3/Hcd_l. (ii) For every integer t >= 1: E[max_{w'} m_kappa(w,w') | Past_l, lists, (I_x)_x] <= t·1[S_w ≠ ∅] + 6e|S_w|/Hcd_l + 4e·2^{-t}|S_w|. (iii) With t := t^CC_l := ⌈2 log_2 M_l⌉, the number of vertices of Q_l lying in PAR sub-layers (#PAR copies = Σ_{kappa ∈ [3M_l]} Σ_{w ∈ Pool_l} max_{w'} m_kappa(w,w')) satisfies E[#PAR copies | Past_l, lists] <= 3M_l (t^CC_l + 1)|Pool_l| + 44.7 n M_l/Hcd_l + 29.8 n/M_l. These bounds hold for every past (every realized J_l) and every outcome of the lists, the SDR and (e1); only the orders are random.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| PAR objects, ends, junctions (e2), loops (e3), B^P_kappa, sub-layers, m_kappa(w,w') | s7:consRound (b), (e), (g) | s7:consRound | no: new |
| C(v) = Cand_l(v) \ Used(v) | after (e1); determined by the past and the lists | s7:consRound (e2) | no: new |
| ordersLaw, FinDist.cond, expect | uniform independent orders; conditioning on an event of positive probability | s7:defSchedule, EG.FinDist | partly: EG.FinDist.cond exists; ordersLaw new |
| chernoffGen_tail_exp | P(X >= j) <= (e mu/j)^j for sums of independent indicators, E X <= mu | s1:citChernoffGen(b) | yes: EG/Lib/Prob/Chernoff.lean |
| t^CC_l | ⌈2 log_2 M_l⌉ | s7:lemCC (iii) | no: new (Nat.ceil (2 * Real.logb 2 M)) |

**deps_declared** (manuscript \deps): s7:consRound, s7:lemWellDef, s1:citChernoffGen, s6:lemJplus

**deps_from_proof:** s7:consRound, s7:defSchedule, s7:lemWellDef, s7:lemMULT, s1:citChernoffGen, s6:lemJplus

**deps_notes:** (i): s7:lemWellDef(i) (<= 1 kappa-object per port) and (v) (|C(v)| >= Hcd_l/2, so |C(v) \ {w}| >= Hcd_l/2 - 1 >= Hcd_l/3), s7:defSchedule/consRound (e2) (junction of a fixed end is a function of ≺_x alone; orders independent). (ii): s1:citChernoffGen(b). (iii): the rank argument 'as in Lemma MULT' (s7.tex:712; s7:lemMULT not declared), J2 of s6:lemJplus (#PAR objects <= |J_l| <= n(M_l-1) <= 1.37 n M_l), numerics 6e·2.74 < 44.7, 4e·2.74 < 29.8, 2^{-t} <= M_l^{-2}. ms_deps: s7:consRound and s6:lemJplus declared but not \ref'd in the proof.

**used_by:** s7:lemUHsplit (ii) (PAR copies); s7:remNonCirc (3)

**randomness:** Sample space: Orders = ∏_{u ∈ V(G)} (uniform linear orders ≺_u), i.e. ordersLaw, with the past and the Lists component FIXED (parameters). (i),(ii) additionally condition on the atom {(I_x)_x = b} of the finite family of indicators (FinDist.cond, positive-probability atoms only); (iii) is unconditional over the orders. Independence across ports holds because the junction of any end at x is a function of ≺_x alone given past and lists (requires ROUND-RULE-DEPENDENCE).

**lean_shape:**

```lean
-- EG/Spec/Quot/CC.lean  (L : Lists fixed; the orders random)
def CCMaxStatement : Prop := ∀ V [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
  ∀ (L : Lists I.G (4 * I.M)) (κ : Fin (3 * I.M)) (w : V), w ∈ I.pool → ∀ (t : ℕ), 1 ≤ t →
  ∀ b : (parPortsOfColour I R κ) → Bool,
    ∀ hb : 0 < (ordersLaw I.G).prob {o | indI I R L κ w o = b},
      ((ordersLaw I.G).cond {o | indI I R L κ w o = b} hb).expect
          (fun o => (maxParMult I R (L, o) κ w : ℝ))
        ≤ t * (if (S_w I R κ b).Nonempty then 1 else 0) + 6 * Real.exp 1 * (S_w I R κ b).card / I.Hcd
          + 4 * Real.exp 1 * (2:ℝ)⁻¹ ^ t * (S_w I R κ b).card
def CCCopiesStatement : Prop := ∀ V _ (I : RoundInput V), I.Valid → ∀ R, R.Valid → ∀ L,
  (ordersLaw I.G).expect (fun o => (parCopies I R (L, o) : ℝ))
    ≤ 3 * I.M * (⌈2 * Real.logb 2 I.M⌉₊ + 1) * I.pool.card + 44.7 * I.G.card * I.M / I.Hcd
      + 29.8 * I.G.card / I.M
-- CCPartnerStatement (i): distinct partner ports; under cond, iIndepFun of partner junctions and each
--   partner junction has the uniform law on (I.cand v \ used I R L v).erase w; prob ≤ 3 / I.Hcd.
```

**hazards:**

- **[risk] CC-CONDITIONING.** The manuscript flags 'the conditioning in Lemma CC' as one of the most delicate points. Formally: conditioning the product law ordersLaw on the atom {(I_x)_x = b}, where each I_x depends only on the coordinate ≺_x, yields the product over ports of the conditioned coordinate laws; the partner port v_o is conditioned only on {I_{v_o} = 0}; the partner junction is then uniform on C(v_o) \ {w} (if w ∉ C(v_o) the event is sure). (iii) follows from (ii) by the law of total expectation over the finitely many atoms of positive probability, then Σ_{kappa,w} |S_w| <= 2·#PAR objects pointwise. Re-derived: correct, PROVIDED the (e2) end order and everything before (e2) are functions of past and lists only (ROUND-RULE-DEPENDENCE). Needs the new lemmas of SCHED-UNIFORM-LEMMAS (3),(4); ~250 lines of conditioning infrastructure.
- **[note] CC-EDGES-AT-W.** 'The edges at [w] in B^P_kappa are exactly the objects of S_w' needs: looped objects are not layer edges (paid in (e3), ROUND/SIMPLE-DEF-ORDER), objects with no end at junction w are not incident to [w]. Then m_kappa(w,w') = #{o ∈ S_w : partner junction = w'} for w' ≠ w, and Σ_{w'} mu_{w'} = |S_w|.
- **[note] CC-NUMERICS.** Chernoff tail with T := max(t, ⌈6e|S_w|/Hcd_l⌉): for j >= T, j >= 2e mu_{w'} (mu_{w'} <= 3|S_w|/Hcd_l), so P(m >= j) <= (e mu/j)^j <= (e mu/j) 2^{1-j}; E[m 1{m >= T}] = T P(m >= T) + Σ_{j>T} P(m >= j) <= e mu 2^{2-T} <= e mu 2^{2-t}; max <= (T-1) + Σ_{w'} m 1{m >= T}. Constants: 6e·2.74 = 44.689 < 44.7 and 4e·2.74 = 29.792 < 29.8 (slack ~0.01: needs e < 2.7188; Real.exp_one_lt_d9 suffices); 2^{-⌈2 log_2 M⌉} <= M^{-2}; |C \ {w}| >= Hcd/2 - 1 >= Hcd/3 (Hcd >= 6). All re-checked.
- **[note] CC-PARCOUNT.** (iii) uses #PAR objects <= |J_l| <= n(M_l - 1) <= 1.37 n M_l (J2 total, deliberately loosened); n = |V(G)| = I.G.card. Each PAR object lies in at most two sets S_w (one per end), summed over kappa it lies in S_w only for its own colour.
- **[note] CC-ATOMS.** Statement (ii) is for each value pattern b of positive probability; patterns of probability 0 are excluded (FinDist.cond needs 0 < prob). Index the indicator family by the finite set of ports carrying a kappa-object (a past-and-lists-determined Finset).
- **[note] CC-UNDECLARED-MULT.** The identity '#copies of [w] in PAR sub-layers = max_{w'} m_kappa(w,w')' is the PAR analogue of s7:lemMULT's second statement ('As in Lemma MULT', s7.tex:712) and is used in (iii); s7:lemMULT is not declared. Prove one generic rank lemma for both layer kinds.

**effort:** ~650 Lean lines, difficulty 4/5 ((i) conditioning + uniform marginals ~250 (shares SCHED-UNIFORM-LEMMAS); (ii) Chernoff + max bound ~200; (iii) total expectation + summation + constants ~200.)

### `s7:lemUltra` — lemma: Ultra-hub copies (s7.tex:805)

- **Manuscript referee status:** x2+RT
- **Formalization:** Spec (EG/Spec/Quot/Ultra.lean: UltraIndepStatement (i), UltraMaxStatement (ii), UltraCopiesStatement (iii), UltraSumStatement (iv)); proof EG/Proof/Quot/Ultra.lean

**Statement (precise restatement).** Let 3 <= l <= R; the past and the lists fixed (only the orders ≺_u random). (i) Let h be an ultra hub (c_h > thult_l), kappa ∈ [4M_l], and omega_1, ..., omega_N the junctions of the coloured hub items of h of colour kappa. These items lie at N distinct ports u_1..u_N (distinct items at h are distinct edges hu; G simple). The omega_i are independent, and omega_i is uniform on C(u_i) = Cand_l(u_i) \ Used(u_i), a set of size >= Hcd_l/2 (s7:lemWellDef(v)). (ii) If N >= 1 then, with mu* := 2N/Hcd_l: E[max_w m_kappa(h,w) | Past_l, lists] <= log_2 N + 2e mu* + 8. (iii) The number of vertices of HUB sub-layers that are copies of h satisfies E[· | Past_l, lists] <= 4M_l (log_2 c_h + 8) + 4e c_h / Hcd_l (c_h = number of live hub items of h). (iv) Summed over all ultra hubs: E[#hub copies of ultra hubs | Past_l, lists] <= 320 n M_l^3 (log_2 thult_l + 8) / lambda_{l-2}^{95}. The bound depends on the past only through deterministic counts, so it holds for every past and every realized J_l.

**defs_needed.**

| name | definition | where | existing EG definition |
|---|---|---|---|
| ultra hub, c_h, thult_l, coloured hub items, junctions (e2), m_kappa(h,w), HUB sub-layers | s7:consRound (c)-(g) | s7:consRound | no: new |
| ordersLaw | uniform independent orders | s7:defSchedule | no: new |
| chernoffGen_tail_exp | s1:citChernoffGen(b) | s1:citChernoffGen | yes: EG/Lib/Prob/Chernoff.lean |
| Hcd_l, lambda_{l-2} | s7:defCand | s7:defCand | no: new (RoundInput.Hcd, RoundInput.lam) |

**deps_declared** (manuscript \deps): s7:consRound, s7:lemWellDef, s6:lemJplus, s1:citChernoffGen, s7:lemMULT, s7:lemCand

**deps_from_proof:** s7:consRound, s7:defSchedule, s7:lemWellDef, s7:lemMULT, s7:lemCand, s6:lemJplus, s1:citChernoffGen

**deps_notes:** (i): (e2) of s7:consRound, s7:lemWellDef(v), independence of orders at distinct ports (s7:defSchedule). (ii): s1:citChernoffGen(b). (iii): s7:lemMULT (copies of h in colour kappa = max_w m_kappa(h,w)). (iv): J2 of s6:lemJplus (Σ_h c_h <= |J_l| <= 1.37 n M_l), s7:lemCand(iv) (M_l Hcd_l >= 2^10 M_l^11), Hcd_l = lambda_{l-2}^{95}/(8M_l^2). ms_deps: s7:consRound declared but not \ref'd in the proof.

**used_by:** s7:lemUHsplit (ii) (copies of ultra hubs); s7:thmJVps; s7:remNonCirc (3)

**randomness:** Sample space: ordersLaw (uniform independent orders ≺_u), with the past and the Lists component fixed (parameters); no further conditioning. The junctions of ultra-hub items are images of fixed ends under the per-port (e2) injections.

**lean_shape:**

```lean
-- EG/Spec/Quot/Ultra.lean
def UltraMaxStatement : Prop := ∀ V [DecidableEq V] (I : RoundInput V), I.Valid → ∀ R : Rules I, R.Valid →
  ∀ (L : Lists I.G (4 * I.M)) (h : V), isUltra I h → ∀ κ : Fin (4 * I.M),
    let N := (colouredItemsOf I R L h κ).card
    1 ≤ N →
    (ordersLaw I.G).expect (fun o => (I.pool.sup fun w => hubMult I R (L, o) κ h w : ℝ))
      ≤ Real.logb 2 N + 2 * Real.exp 1 * (2 * N / I.Hcd) + 8
def UltraCopiesStatement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid → ∀ L h, isUltra I h →
  (ordersLaw I.G).expect (fun o => (hubCopies I R (L, o) h : ℝ))
    ≤ 4 * I.M * (Real.logb 2 (cLive I h) + 8) + 4 * Real.exp 1 * cLive I h / I.Hcd
def UltraSumStatement : Prop := ∀ V _ I, I.Valid → ∀ R, R.Valid → ∀ L,
  (ordersLaw I.G).expect (fun o => (∑ h ∈ I.hubs.filter (isUltra I), hubCopies I R (L, o) h : ℝ))
    ≤ 320 * I.G.card * (I.M : ℝ) ^ 3 * (Real.logb 2 (thult I) + 8) / I.lam ^ 95
-- UltraIndepStatement (i): the junctions ω_i are iIndepFun under ordersLaw and each has the uniform law on
--   I.cand u_i \ used I R L u_i, a set of size ≥ I.Hcd / 2.
```

**hazards:**

- **[note] ULTRA-NUMERICS.** Re-derived: (ii) T := max(⌈2e mu*⌉, ⌈log_2 N⌉ + 1); for j >= T, e mu_w/j <= 1/2; Σ_w P(m_w >= j) <= (eN/j) 2^{1-j}; E max <= (T-1) + (eN/T)2^{2-T} <= T - 1 + 2e/T (as 2^{-T} <= 1/(2N)); T - 1 <= log_2 N + 2e mu* + 1; 2e/T <= 2e < 7. (iv): M Hcd/7 = lambda^95/(56M); lambda^95/M = 8M Hcd >= 2^13 M^11 >= 2^453; thult >= lambda^95/(56M) - 1 >= lambda^95/(57M) and thult >= 2^8; 4·1.37·57 = 312.36; 4e·1.37·8 = 119.17 <= 119.2; 119.2/16 = 7.45 <= 7.5; 312.36 + 7.5 < 320 (slack 0.14). All correct; small-constant checks by norm_num with Real.exp_one_lt_d9.
- **[note] ULTRA-G-DECREASING.** (iv) uses that g(x) = (log_2 x + 8)/x is decreasing on [1, ∞) (x^2 g'(x) = 1/ln 2 - 8 - log_2 x < 0). Only integer arguments c_h > thult_l >= 1 occur; a Lean proof can use the real derivative (Mathlib antitoneOn from deriv) or a direct integer inequality (log_2 c + 8) thult <= (log_2 thult + 8) c for c >= thult >= 1.
- **[note] ULTRA-I-SIMPLICITY.** Distinctness of the ports u_i comes from simplicity of G (items at h are distinct edges hu), not from J1 (the manuscript says so). In Lean: items are distinct Sym2 values containing h, hence distinct other ends.
- **[note] ULTRA-HCD-LAMBDA.** (iv) mixes Hcd_l and lambda_{l-2}; RoundInput must fix Hcd := lam^95/(8M^2) definitionally (not as an independent field), otherwise the identity M Hcd/7 = lambda^95/(56M) is lost.
- **[note] ULTRA-CONDITIONAL-SCOPE.** (ii)-(iv) are expectations over the orders with the past AND the lists fixed (N, c_h, which items are coloured depend on the lists through the SDR). s7:lemUHsplit averages over the lists afterwards; state (ii)-(iv) with L : Lists as a parameter, as in the sketch.
- **[note] ULTRA-LOG-NAT.** log_2 N and log_2 c_h are Real.logb 2 of naturals >= 1 (nonnegative). For N = 0 the manuscript's (ii) is not claimed (max = 0); (iii) sums only over kappa with N_kappa >= 1 (at most 4M_l of them) and uses log_2 N_kappa <= log_2 c_h.

**effort:** ~450 Lean lines, difficulty 3/5 ((i) ~80 (shares uniform-order lemmas); (ii) ~150; (iii) ~70; (iv) ~150 (monotonicity of g, constants).)
