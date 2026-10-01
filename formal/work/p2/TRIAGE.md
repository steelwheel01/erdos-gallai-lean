# P2 triage: hazards, shared data model, Defs order, probe inputs, size

Triage lead, 2026-09-26. Inputs:
- the 11 blueprints `formal/work/p2/blueprint_{s1,s2a,s2b,s3a,s3b,s4,s5,s6a,s6b,s7a,s7b}.md` and their `nodes_*.json`;
- the three blocker checks `blocker_mint.md`, `blocker_rules.opus.md` and `blocker_rules.fable.md`;
- the manuscript v6 TeX at HEAD `4fcfe88` (`proofs/manuscript/s1.tex`–`s7.tex`).

Every item in §1 was checked against the TeX, not against the blueprints' paraphrases. Classes follow PLAN §7:
- **T0**: encoding; fix the Lean only.
- **T1**: statement true, but the proof or the wording has a gap; patch the manuscript.
- **T2**: statement false, repairable.
- **T3**: fatal.

The manuscript is a CANDIDATE proof, reviewed by AI only.

## 0. Verdict

- **No T2 or T3 found.** No statement of s1–s7 was shown false for the construction the manuscript intends.
- **Two T1 repairs gate the Defs lock.** Both manuscript patches must be applied, and get a targeted re-review, before the Defs they affect are locked:
  1. **M-INTEGER**: M_l must be a natural number. This blocks `EG/Defs/HB/Round.lean`, `Stage1/COL.lean`, `Chain/*` and `Quot/*`.
  2. **ROUND-RULES**: the "fixed rules" of s7:consRound need declared arguments. This blocks `EG/Defs/Quot/Round.lean`.
- **Three wording items are T1**: T16\*(c), the JS-LC statement's g_{Y,l}, and one cited-result sketch. None of them blocks anything.
- **Every other blueprint "risk" is T0**: an encoding decision or a statement-shape decision. The hard cases, EX-GAMMA-NEEDED and the implicit-Γ family, are T0 because s1:defConstants(iii) *defines* D_* as a constant satisfying Γ1–Γ4.
- **Commit `ee8b589` is superseded on M-INTEGER.** Its message calls M_l integrality "T0". This triage classifies it **T1**, because the manuscript text itself is ill-defined.
- **Staleness (s1, s2a).** `blueprint_s1.md` (08:11) and `blueprint_s2a.md` (08:21) predate the G0-fix commit `4fcfe88` (09:28), which rewrote about 500 lines of `s1.tex`. Their s1 line numbers are stale. Two of their hazards changed:
  - GAM-2BC is fixed in the text: G0 fix F3 says Γ2(b),(c) are "implied by Γ1".
  - HAX-TRUTH changed: G0 fix 12 added a full, still unrefereed proof of the stated Haxell form to s1:citHaxell.

  Neither change alters a decision below.

---

## 1. Hazards that could be mathematical errors (each checked against the TeX)

### 1a. Confirmed manuscript defects (T1)

| ID | Where (TeX) | Class | Confirmed | Finding and action |
|---|---|---|---|---|
| **M-INTEGER** | s2.tex:511–514 (R2); uses in s3.tex:1048,1075,1092,1135; s6 JS-LC; s5.tex:244; s7.tex:183–184, 263–351 | **T1** | yes | (R2) makes M_l the real `max(2^40, 2^16 T log^4 T)`. The rest of the manuscript uses it as a count: `K^JS_l = M_l^2` classes `0 ≤ j < K^JS_l`, with law `K^JS_l·ρ_l = M_l^-2`; palettes `[3M_l]`, `[4M_l]`; bijections `η_h: [4M_l]→[4M_l]`; `binom(K,s-1)`; "M_l−1 cherry systems"; and `max(2M_l−2, (M_l−1)+⌈M_l/2⌉) = 2M_l−2`. For non-integer M_l these are ill-defined, so the defect is not merely a Lean typing issue. **Repair**, as in `blocker_mint.md` §2 (re-checked by me): (R2) `M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ ∈ ℕ`, `Λ_l := log M_l`. Two proof patches: s2:propDegRec needs `⌈B⌉ ≤ B+1 ≤ 2^{2x}`, and s3:lemCOLJV (B6) (TeX 1243–1246) needs `log⌈B⌉ ≤ log B + 2^-160` and `4 log(λ+2μ) ≤ 4μ + 0.01`, slack ≈4. One wording fix: lemCap(ii) "=" becomes "≥". Also update the symbol-table row. No statement changes. The fallback of ceilings at each use is **rejected**: it changes the JS label law and s6:lemLost(i). |
| **ROUND-RULES** (SCHED-/ROUND-RULE-DEPENDENCE) | s7.tex:257–306 (steps (b)–(e2)), 346, 358; claims at 280–282, 308–312, 697–703; proofs of WellDef(iii), CC(i), Ultra(i), Pay(c) | **T1** (see note) | yes | Nine choices are only "fixed". The text never says which data they may read, and ξ_l is drawn *before* the round step. The proofs assert properties that hold only if the rules are restricted: (c) "lists form a uniformly random sequence"; (e2) "Used(u) is determined by Past_l and the lists"; CC(i) "junction of the κ-end at x is a function of ≺_x alone". Both checks exhibit explicit rules that falsify these claims: a grouping that reads η makes SDR failure almost sure, and an (e2) order that reads ≺_u steers junctions. For the intended construction every statement is true. **Classification: T1, not T0.** The opus check's T0 is overruled: the repair is manuscript text, since the construction does not define what its own proofs assume, and a Lean-only fix would leave the manuscript proofs unsupported. **Repair:** patch set R below. The fable check's text is adopted, merged with the opus corrections: (g) and (h) are exempt and must read ξ_l; Past_l contains the ξ_{l'} with l'>l, so the prohibition is on "the orders ≺_u **of ξ_l**". The sentence proposed in `blueprint_s7a.md` ("none depends on the orders ≺_u") is **rejected** as written. |
| **T16-C-META** | s3.tex, thmT16s item (c) and proof Step 0 | **T1** (wording) | yes | Item (c) claims "The proof uses only s ≥ 2K_*(θ_*+1)". But Step 0 uses the full hypothesis `s ≥ 2^135 t L^28 ρ^-5` to get `N ≥ 2^30`, `ρN ≥ 84` and `e^{-ρN/8} ≤ N^-3`. The meta-claim is false as written. No consumer uses (c). **Patch:** "Apart from Step 0, which uses the full hypothesis on s to obtain N ≥ 2^30, ρN ≥ 84 and e^{−ρN/8} ≤ N^{−3}, the proof uses only …". Do not formalize (c). |
| **JSLC-G-UNDEFINED** | s6.tex:449–452 (statement), 541–543, 602–603, 860 | **T1** (wording) | yes | The statement of s6:lemJSLC bounds the cycles by `126n/M_l + Σ_giant sc_{Y,l}` with `sc = (3g_{Y,l}−6M_l)^+`, where g_{Y,l} is "the number of cherry classes (Step 5 of the proof)". So the statement refers to an object that exists only inside its proof. The only downstream use (MIX-C, s6.tex:860) is `≤ 1.5 Σ m_{Y,l}`. **Patch:** the statement says `126 n/M_l + 1.5 Σ_{(Y,l) giant} m_{Y,l}`, and sc and g move into Step 8 of the proof. The Spec uses the 1.5m form. |
| **L14-INEQ9** | s1.tex, citLem14 derivation of (9) | T1 (cosmetic) | yes | The quoted chain `log n_1 < log n − 2/5 ⇒ (9)` yields (9) only for log n > 1.09. At n = 2, (9) holds by direct evaluation. This is a cited result, not on the Lean route (not formalized) and used by nothing. Optional one-line fix; no ledger priority. |
| **GLOB-FACTADD-MISCITE** | s6.tex, proof of lemHCCglob | T1 (cosmetic) | yes | The proof cites Fact factAdd(b), which is a bound on f, the *minimum*. What is used is concatenation of given decompositions, and the proof's own first sentence already says so. Optional citation fix. Lean: an IsDecomp-concatenation lemma. |

**Patch set R (ROUND-RULES), to be applied to s7.tex.**
- **R-1.** Insert after "…(i)–(v) of Lemma~\ref{s6:lemJplus}." in s7:consRound:

  > *Fixed rules.* The rules and orders called fixed in steps (b)–(e) below are deterministic functions, chosen once before any randomness is drawn, with the following arguments.
  > - Functions of Past_l alone: the pairing of the live J^fr items at a fresh centre and the choice of its unpaired fresh leg; the order in which the PAR objects are coloured in (b); and the split of the live items of a non-ultra hub into groups, together with the numbering of the groups, in (c).
  > - Functions of Past_l and of the lists (that is, of the variables η_h and ζ_{h,u} of ξ_l): the choice of the system of distinct representatives in (d); the processing order and the order of V(G) in (e1); and the order e_1,…,e_q of E'(u) in (e2).
  > - None of these rules reads the orders ≺_u of ξ_l; the orders enter the construction only through the assignment e_i ↦ w_i of (e2). Through Past_l the rules may depend on the draws ξ_{l'} with l' > l.
  > - The rank order in (g) and the rule choosing Dec_l in (h) are arbitrary deterministic functions of Past_l and ξ_l. They must read ξ_l, since Q_l does.
  > - Rules with these arguments exist, for instance lexicographically first choices for fixed orders of the finite sets involved. Every statement of this section about the round step holds for every choice of rules that obeys these restrictions.
- **R-2.** In (c), "…and they form a uniformly random sequence of" becomes "…and, since the groups and their numbering are functions of Past_l while η_h is independent of Past_l, they form a uniformly random sequence of".
- **R-3.** In (e2), "Used(u) is determined by Past_l and the lists" becomes "by the restrictions on the fixed rules, Used(u), E'(u) and its order e_1,…,e_q are determined by Past_l and the lists".
- **R-4.** In the proof of s7:lemWellDef(iii), after "which group each item belongs to", add "(the grouping rule of step (c) reads Past_l only)".
- **R-5.** In the proof of s7:lemCC(i), prefix: "With the past and the lists fixed, C(x), E'(x) and its order are fixed for every port x (restrictions on the fixed rules), so …".
- **R-6.** In the preamble of the subsection "Quotient size and payments", "steps (a)–(d) and (e1) … are determined" becomes "steps (a)–(d) and (e1), the sets E'(u) and their orders e_1,…,e_q are determined (by the restrictions on the fixed rules)".

Lean side (T0 half): a structure `Rules I`.
- Fields: `pairing`, `unpairedLeg`, `parOrder` and `hubGroups`, each taking `Past` only; `sdr`, `e1Order`, `vertOrder` and `e2Order`, each taking `Past → Lists`; `rank` and `dec`, each taking `Past → Xi`.
- `Rules.Valid` holds the correctness side conditions: the SDR is valid iff one exists, and the dec output has length `fnum`.
- `Rules.exists_valid` is a lemma, and the consumer uses `Classical.choose Rules.exists_valid`.
- Every round-level Spec reads `∀ R : Rules I, R.Valid → …`.

### 1b. Checked and found not to be manuscript errors (T0: Lean or statement-shape decision)

| ID(s) | Where | Class | Confirmed error? | Why not an error / Lean decision |
|---|---|---|---|---|
| EX-GAMMA-NEEDED, MAIN-PROPEXISTS-HYPS | s2.tex:987 (propExists) | T0 | no | The counterexample is correct: D_* = 2^117, G = K_{2^117+1} loops forever. But D_* is by definition a constant satisfying Γ1–Γ4 (s1:defConstants(iii)), so the statement is true as intended. The Spec carries `Gamma1core Dstar`. Optional manuscript wording: s2 has no standing-assumption sentence (s5.tex:9 and s7.tex:10 have one). |
| OV-IMPLICIT-DSTAR, CAP-GAMMA-EXPLICIT, CAND-GAMMA-IMPLICIT, CONC-IMPLICIT-HYPS, CONCL-HYPS, LOST-HYPS, GC-IV-GAMMA, EXP-HYPS | s2 propOV/lemCap, s7 lemCand, s6 CONC/CONC-L/Lost | T0 | no | These are the same mechanism. Each Spec takes exactly the Γ items its proof uses (§2.6). |
| STR-N0, COLJV-N0-IMPLICIT, COL-N0-IMPLICIT | s2.tex:710 (propStructure hypothesis n ≥ N_0) | T0 | no | The hypothesis is unused in the proof (s2b re-derivation). The Spec drops it; this is a strengthening, and the prover must confirm it. It is then no longer needed by lemCOLJV and lemCOL. |
| E1-ROW3-GAP | s3.tex:1285 (row-3 derivation), s5 lemE1(b) | T0 | no | The row-3 derivation in the proof of lemCOLJV explicitly covers all three L15⁺ levels. Column 2 of the table lists only the lent level. The COLJV Spec must state all three (C1–C13 of s3b). |
| E1-COL-A-BOUND | s5 lemE1(b) | T0 | no | The proof re-derives the COL(a) bound directly from three L15⁺ applications; it is self-contained. The COL Spec exports `P(COL(a) fails) ≤ 2(2+k_lend+k_own)N^-5` so that the plumbing is not written twice. |
| E1-C-INTERFACE, COL-CONDITIONAL-T16 | s3 lemCOL(c) | T0 | no | The TeX explicitly allows the family to be dependent across indices, and requires independence from the lending data (a joint family). The Spec uses `IndepFun μ D Vs` (joint). |
| EUL-MULTI-USE | s1 citEuler(b); s5 lemParent Step 3 | T0 | no | citEuler(b) says "(or multigraph)", and (a) is applied to a spanning tree (a simple forest) of each component. Lean: a multigraph Euler theorem in Lib, derived from the stage-α SimpleGraph form by subdivision. |
| PAR-SIDES-DISJOINT | s6 lemPAR | T0 | no | "Bipartite graph with sides V_a, V_b" implies disjoint sides. The Spec states `Disjoint Va Vb`. |
| GLOB-OUTPUT-LEVEL-HYP | s6 lemHCCglob(2) | T0 | no | The Spec uses input-level disjointness (beads and path edges), which JS-LC Step 7 verifies and which implies the output-level condition. |
| HB-R5-ORDER | s2.tex:555–568 ((R5)(3) "the first such pre-part") | T0 | no | The order is unnamed. The Lean decision is the home order; downstream uses are order-independent. Optional wording: "(in the home order)", as in (R5)(2). |
| HB-STOPRULE, LEM14-TERMINATION, EX-TERMINATION-SHAPE, HB-VALID-NO-TERMINATION | s2 (R3), lem14tau | T0 | no | (R3) states "leaf iff (ε,0)-expander", and lem14tau assumes τ ≥ 128 s log² n_0 with s ≥ 1. Valid must carry both directions of the stopping rule. Termination is (T1)+(T2) as in s2a. |
| MULT-J1 | s6 lemJplus (J1); s7 lemMULT | T0 | no | (J1) is stated **aggregated** over all parts of round l, and JS-LC Step 2b does aggregate. `JPlusProps.J1` must be stated in the aggregated form. It remains a named refutation target, so probe P-2 must hit it. |
| S7-UNLABELLED-PAR-MULT, UH-VERTEX-DECOMP | s7.tex:710–713 | T0 | no | The PAR identity follows from the rank definition exactly as MULT's second statement does. Make it a named lemma; `QVert` must carry the rank. |
| TPV-/PV-/VX-DET-SPEC, ORDER-STAGE3, MIXC-STAGE3-ABSTRACT, OO-STAGE3-DETERMINISTIC | s4 TPV statement (conclusion label-free, checked), PV, VX⁺ | T0 | no | Specs are deterministic (§2.8). |
| KRED-CAUSALITY, ORDER-DECOUPLE, LENT-KRED-FORM | s6 consOrder steps (1)–(4) | T0 | no | Checked: steps (1), (3) and (4) of round l read only Lent(Z) for standalone Z (LentU(Z) = ∅), E^Q(Z), J_l and stage 1, never a light-part output. So the standalone chain can be built first and K-RED applied once to the final Lentext (§2.9). |
| JPLUS-EXISTENTIAL, JSLC-JPLUS-MERGE, JSLC-USED, JCONS-TYPE, JCONS-CONDITIONAL, OO-PROCEDURAL, MIXC-SUMOBJ, S7-MIXC-INTERFACE, JV-SAME-Q | s6 J⁺, J-consumer, MIX-C; s7 OneOutcome, JV⁺* | T0 | no | Statements about constructions are re-encoded as conjuncts and interfaces (§2.9, §2.10). |
| CAND-MEAN-DEF, POOL-LAW-NEEDS-GAMMA, ZONE-LAW-WELLDEF, STAGES-AY-CHOICE, COL-EMPTY-INDEX | s7 defCand/defPool, s5 defZones/defStages, s3 defCOL | T0 | no | Definitions that are total only under a theorem get `dite` or Option fallbacks plus characterization lemmas (§2.7). |
| OV-CONST-546, LEM14-CONST-546, OV-CONST-TIGHT | s2 OV, lem14tau(b) | T0 | no (thin, correct) | 5.46 needs `log₂(4/3) ≥ 0.414508`. Use 17/41 (`2^65 ≥ 3^41`); 12/29 is not enough. Prove OV(a) in its sharp c_OV form. |
| HB-PLAN-MISMATCH | s3 lemHB vs PLAN §2 R4 | — | no | The PLAN text is out of date: v6 uses a single Hall application with exactly b, not b+m. Formalize the manuscript; update PLAN §2 R4. |
| DR-COUNTERFACTUAL, GC-III-WHICH-PART, DES-BEAD-CLAUSE-VACUOUS, JPLUS-CLASS-JPAR (vestigial 1.37), EQ-USE-EMPTY-S0, LOST-UNION-SLACK, CONCL-TOWER-ANALYSIS / GS-LOGSTAR ("ε_CONC → 0" elided), P18-THETA (B-M's own statement; corrected in s3:lemP18s), T16-RHO-POS, HB-MMAX-INACTIVE | various | T0 / none | no | These are commentary, vacuous clauses, elided standard facts, or traps for Spec reviewers. The notes in the blueprints stand. |

### 1c. Unconfirmed risks (no counterexample; they could become T1 or T2 if a Lean proof fails)

| ID | Where | Potential class | Status and mitigation |
|---|---|---|---|
| CAP-L25-CONST / L25-CONST18 | s1:citLem25 constant 18; s2:lemCap(i) margin (`18432·1.37317^4 ≈ 65534 ≤ 65536`) | T1, or T2 limited to Γ2(a) | The s1 blueprint re-derived the rounding, and 18 survives. The lock is still `sorry` (`EG.bmLemma25`). If only a larger C < 64 is reached, Γ2(a) becomes an eventuality `D_* ≥ 2^{x_0(C)}` (R6 style) and no other statement changes. **Prove `EG.bmLemma25` early** (cheap numeric probe). |
| HAX-TRUTH / L9-HAXELL-FORM | s1:citHaxell (proof added after G0, unrefereed); s3:lemL9rho | stage-α trust (T3 for stage γ only) | Lock the **q²-form** (nonempty X′, `|Z| < q²|X′|`). L9ρ verifies exactly this, so no statement depends on the unchecked factor 2q−1. Check [Hax95] by hand before stage β. |
| Unreviewed v6 text | EG0 (R1), BBD (R2), L17\* case (b) (margins 0.7% and 3%), L9ρ claim (R3), lemHB via Hall (R4), TPV/PV/VX⁺ re-accounting 84/28/19 (R1), (MC)/(B)/truncation (R5), COLJV(ii) rows, s5:remConstants(a) | T1 or T2 | Each was re-derived line by line by the blueprint authors, with no error found. These are the P2b and P3 priorities: the thinnest margins go first. |

---

## 2. Cross-chunk data-model decisions (one shared definition per object)

These are binding for P2-D. Where chunks disagreed, the resolution is stated.

### 2.1 Integers, rounds, identities
- **M_l ∈ ℕ** (T1 repair above).
  - Lean: `EG.HB.MOf (d : ℝ) : ℕ := ⌈max (2^40) (2^16 * TOf d * (logb 2 (TOf d))^4)⌉₊` with `TOf d := d * (logb 2 d)^2`.
  - `ΛOf d := logb 2 (MOf d : ℝ)`.
  - `KJS := MOf^2 : ℕ`, `KHUB := 4*MOf : ℕ`, palettes `Fin (3*M)` and `Fin (4*M)`, `tJS := 2*M+2 : ℕ`.
  - Real inequalities use the cast `(MOf d : ℝ)`.
  - `s_l`, `P_l`, `τ_l` and `θ^GC` are ℕ ceilings; `d_l`, `λ_l`, `T_l` and `Λ_l` are ℝ.
- **Rounds are 1-indexed ℕ.** Offsets are written `r + 2 ≤ l`, never with ℕ subtraction. There is a test `anc G l x = ∅` for `l ≤ 2`.
- **Stationarity.** `G_l` is stationary for `l > R+1`, and `Std_l = ∅` and `E_l = ∅` for `l > R`; there is a lemma saying edges are antitone in l.
- **Part identity.** `EG.HB.Addr := List Bool` (split-tree address), and `EG.HB.PartId := ℕ × Addr` (round, pre-part address). This is the one type for pre-parts, parts, light parts (s5's `LP`), ancestors, classes and designation values; it is never a vertex set.
  - `run.Std G l : Finset Addr`, `run.lightParts G : Finset PartId`, `run.ancestors G : Finset PartId`.
  - `run.partVerts` is the vertex set of the part: `Z^0 \ S_Z` if the part is light, `Z^0` otherwise.

### 2.2 s2 Run model (resolves s2a vs s2b)
- **Adopt the s2b round-local API** (DR-ROUND-LOCAL). Every round object is a function of `(n, H := G_l, c : RoundChoice)`:
  - `Round.graph'`, `twoLevel`, `prePartAddrs`, `D`, `home`, `guests`;
  - `isL1`, `isL2`, `isGC`, `isLight` (the components are named separately);
  - `assign`, `E`, `next`.
- `Round.Valid n H Dstar c` lists:
  - cycles: pairwise edge-disjoint, of length `≥ T_l`, maximal. This is (R1) encoded as *any* maximal family; it strengthens every ∀-run statement.
  - the s=0 tree stops **exactly** at (ε,0)-expanders, and τ-runs at big pieces stop exactly at (ε,s_l)-expanders;
  - `homeOrder` lists all pre-parts.
- The run is built on top:
  - `Run V := List (RoundChoice V)`;
  - `run.graph G (l+1) := Round.next …`;
  - `Run.Valid G Dstar run := (∀ l ∈ [1,R], Dstar ≤ d l ∧ Round.Valid …) ∧ d (R+1) < Dstar`.
  - `Valid` never presupposes Lemma 14^τ's hypotheses.
- **Round-level Specs:** lemCap(ii), propOV and propDegRec are stated at round level (hypotheses `Round.Valid`, `Dstar ≤ Round.d n H`), with run-level corollaries. propExists quantifies over choice lists that are not yet valid runs.
- **Split trees:** `EG.HB.STree V := BinaryTree (Finset V × Finset V)`, addressed by `List Bool`, with a total `graphAtD`. The children are the shared (eqSplit) constructors `splitFst`/`splitSnd`/`splitDel`, used by both levels.
  - The **graft API** is part of SplitTree.lean: WF, addresses `a ++ b`, graphs, leaves, Dup correspondences, and deleted-set union.
- **(R5)(3) order** = the home order.
- **Design constraint** (checked by the Defs reviewer): `D`, `home`, `guests` and `prePartAddrs` do not reference `isLight`/`isGC` (lemGC(i), EX-GC-DEFINITIONAL).

### 2.3 Logs, tower, log*
- Module `EG/Defs/Log.lean`:
  - `EG.logIter (k : ℕ) (x : ℝ) := (logb 2)^[k] x`;
  - `EG.tower : ℕ → ℝ` (`tw 0 = 1`, `tw (k+1) = 2^{tw k}`);
  - `EG.logStar (x : ℝ) : ℕ := sInf {k | logIter k x ≤ 1}`.
- `sInf` is used rather than `Nat.find`, so the Defs contain no proof term. Characterization lemmas in Lib: `logStar_le_iff_le_tower`, `logStar_two_rpow`, `logStar_le_one_add_log`, and the growth fact `logStar = o(log log)`. **Provided** (`EG.Lib.Found.Log`, P2-D small fix round 1) as `logStar_le_one_add_logb` (s6.tex:262 verbatim, `log* x ≤ 1 + log₂ x` for `x ≥ 1`; this is the item listed here as `logStar_le_one_add_log`, added in P2-D small fix round 2), the sharper `logStar_le_two_add_loglog` (`log* y ≤ 2 + log₂log₂ y` for `y ≥ 4`), `logStar_le_three_add_logloglog` and `logStar_isLittleO_loglog`.
- The same constant is used by s2 lemLacunary(iv)/lemTower(a),(d), s5 eqLY, s6 CONC/CONC-L tower facts and ε_CONC, and s7 lemGammaSat.
- Real exponents (1.6, 102.5, 42.1, …) are exact rationals under `Real.rpow`.

### 2.4 Constants and Γ (layering; resolves the s1 / s3b / s7b naming)
- `EG/Defs/Constants.lean`: `ε := 2^(-5:ℤ)`, `σ := 100`, `Cp := 103`, `Aexp := 105`. **Final Lean names** (P2-D small, locked): `EG.epsC : ℝ`, `EG.sigmaC : ℕ`, `EG.Cp : ℕ`, `EG.Aexp : ℕ` (simp casts `cast_sigmaC/Cp/Aexp`). Spec authors use these, not `ε`/`σ` or the blueprint names `CpC`/`AexpC`.
- `EG.Gamma1core D` covers items (a)–(e) of Γ1 on the ray `μ ≥ log₂log₂ D`, with `2 < D`. `EG.Gamma2a D := 2^117 ≤ D`, with the lemma `Gamma1core → Gamma2a`. Γ2(b),(c) are lemmas, never fields; the TeX now says "implied by Γ1".
- **One table predicate:** `EG.COLTable.col3 (μ : ℝ) : Prop` (18 inequalities) in `EG/Defs/Lend/COLTable.lean`.
  - `EG.Gamma1f D := ∀ μ ≥ log₂log₂ D, COLTable.col3 μ` and `EG.Gamma1 := Gamma1core ∧ Gamma1f`.
  - The names `EG.S3.COLJVcol3` (s1, s7b) are **dropped**. COLJV, COLJVev(iii) and GammaSat all refer to `col3`.
- `EG/Defs/Vortex.lean` (namespace **`EG.Vortex`**, not `EG.S4`):
  - `etaTPV/PV/VX`, `TPVSize/PVSize/VXSize` (size conditions (i), (ii), (iv));
  - `tpvJ/pvJ/vxJ`, `pvM`, `pvB`;
  - names are run-specific (CONV-SYMBOL-CLASH).
  - **Argument type (P2-D [params], decision D-VX-1; supersedes blueprint s1:1271 and s4:122–126, 187, 272, 348).** The η's, the size predicates and `tpvJ/pvJ/vxJ/pvM/pvB` take `N : ℕ` (N = |Z| is a vertex count). Specs write `EG.Vortex.TPVSize O.card` (no cast), all in namespace `EG.Vortex` (never `EG.S4`). `pvJ N = ⌊logb 2 (L N / 8)⌋₊` (literal floor of the real log, not `Nat.log 2 ⌊L/8⌋₊`; bounds in `EG.Lib.Vortex.Params`).
- `EG.N0Cond (N0 : ℝ) := 2^40 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ (N : ℝ) → Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N` (this shape elaborates; checked by the P2-D [params] reviewer), and `EG.Gamma3 N0 D := 2*N0 ≤ (log₂ D)^103`.
- ε-functions are Defs with exactly the formulas of the defining statements; the Γ4 bullet list is descriptive only:
  - `epsA`, `psiPool` (HB);
  - `epsU`, `epsChain` (Light);
  - `epsCONC`, `epsM` (Chain);
  - `epsX`, `detl`, `FQ`, `eps2`, `eps1`, `C0` (Quot).
- `EG/Defs/Main/Gamma.lean` (last): `Gamma4`, `GammaCond N0 D`, `cEG`.

### 2.5 Vertex and index types, universes
- Every Spec for s2–s7 is stated for `V : Type` with `[DecidableEq V]` and `G : FGraph V`.
- **Per-vertex random families are indexed by `↥G.verts`** (resolves s5's [Fintype V] vs s7a's subtype). Per-edge families use `↥(H Y).edges` of the fixed ambient graph.
- The HI adapter (HIHyp has no `Fintype V`) is done once in thmMainProof.
- "Arbitrary finite space" Specs (L17\*, P18\*(ii), T16\*, COL) quantify `Ω : Type`.
- `HaxellStatement` is locked universe-polymorphic (`α : Type u`), since it is only a hypothesis of proof terms. It is locked in the q²-form with nonempty X′.

### 2.6 One hypothesis bundle
- `EG.RunHyp N0 D G run := Gamma1 D ∧ Gamma3 N0 D ∧ N0Cond N0 ∧ N0 ≤ G.card ∧ D ≤ run.d G 1 ∧ run.Valid G D`.
  - This one name replaces s5 `S5Hyp`, s7b `S7Hyp` and s3b `RunCtx`.
  - `Gamma2a` is derived.
- Which Specs take what:
  - s5, s6b (Lost, JS-LC, MIX-C) and s7 take `RunHyp`.
  - s3 COL/COLJV take `Gamma1 D ∧ run.Valid G D` (propStructure without N0).
  - s2 Specs and s6a CONC take only the items they use (none, `Gamma2a`, or `Gamma1core`), as listed in the s2b §2 table.
  - Only thmJVps, `C0_le`, thmMainProof and s7:lemUHsplit (iv) ("`θ_Q ≤ 1/4` by condition Γ4", s7.tex 1120, 1190) take `Gamma4` / `GammaCond` (s5:remConstants (b) also cites Γ4, for a slack the remark itself calls unnecessary). A UHsplit (iv) Spec on `RunHyp` must add `Gamma4 D`, or drop the `θ_Q ≤ 1/4` clause and derive it where used (GAMMA fix round 1, m1).

### 2.7 Stage-1 law (shared by s3/s5/s6/s7; resolves `stage1Law` (s5) vs `S3.stage1Dist` (s6b))
- **One record** `EG.Stage1.Outcome G run` with four named projections, **one law** `EG.Stage1.law G run`, and marginal and independence lemmas (`IndepFun` of projections). All four component laws need only s2 data, so they are defined after Run, before any s3–s7 Spec:
  - **1a `col`**: per ancestor Y and per edge of the *fixed* E(H_Y), a triple `(bit : Bool, idx : Option LentTag, own : Fin (kown Y))`.
    - `idx` is uniform on `lentIdx Y`, and `dirac none` if that set is empty (r ≥ R−1).
    - `kown := 4·pvJ|Y| + 1` is defined for every ancestor.
    - `kown Y ≥ 1` for every ancestor, with no separate guard: `pvJ` is a `Nat.floor` (junk value 0 when `L_Y < 8`, and 0 whenever `L_Y < 16`), so `Fin (kown Y)` is never empty (only the label M exists for tiny ancestors). (P2-D [params] fix round 2.)
    - This resolves L15-RANDOM-EDGESET and COL-EMPTY-INDEX: L15⁺ applies slice-wise given the bits.
    - The named own classes go through the bijection `ownIdx : Option (Fin (pvJ N) × Fin 4) ≃ Fin (4·pvJ N + 1)`, with `none` ↦ M. `pvJ` is from `EG.Vortex`, so the PV Spec's index type is definitionally the one COL uses (PV-OWNCLASS-INDEX).
  - **1b `zone`**: `↥G.verts → Option ZIdx`, a one-step label with weight ρ_Y on each (Y,l,c,u). It has a `dite` guard that is *exactly* `Σ zp ≤ 1`, with a `dirac none` fallback.
  - **1c `js`**: `Option ℕ` on sites `{(l,y) : r+2 ≤ l ≤ R, y ∈ V(Y)}`, with weights `ρ_l = M_l^-4` and `P(none) = 1 − M_l^-2`. This is exact because M_l ∈ ℕ.
  - **1d `pool`**: `↥G.verts → Option (ℕ×ℕ)`, weights `q_l π_{l,r}`, with a `dite` guard `poolMass ≤ 1`.
- Characterization lemmas under `RunHyp` give the true laws.
- s3 lemCOL Specs are in the "any μ with `μ.map D = colLaw Y`" form (and joint `IndepFun` for (c)). The joint law meets that form through the marginal lemma.
- Statements about a fixed stage-1 outcome quantify `ω ∈ (Stage1.law G run).supp`, and every selection returns positive weight (OO-SUPP).
- The JV-bad threshold is the closed form `candMean := q_l π_{l,r} p_Y deg_{H_Y}(u)` (CAND-MEAN-DEF). lemCand(ii) proves it equals the expectation, so no Defs depend on the law.

### 2.8 Stage 3 (s4 ↔ s5/s6/s7)
- **Deterministic Tier-1 Specs** for TPV, PV and VX⁺ (∀ admissible E ∃ decomposition with (T1)–(T3), resp. PV(a)–(d), resp. VX⁺). The TeX conclusions are label-free; the TPV statement was checked.
  - The explicit good events and their probability bounds are Tier-2 fidelity Specs or Lib lemmas, consumed by nothing in the chain.
  - `S4.TPVGood` hypotheses in MIX-C are therefore **not** introduced, contrary to the s6b proposal. MIX-C applies the deterministic TPV Spec, plus `MixCTPVApplicable` for its hypotheses.
- s5 lemChild and lemDemoted: a Tier-1 existence form (∀ H_0 ∃ decomposition), and optionally a Tier-2 probabilistic form. The PV Spec must export its data record and hypotheses as named Defs, with `PVSize`.
  - **PV-DATA-RECORD** (P2-D [light] fix round 1, 2026-09-26): the canonical data record is `EG.Vortex.PVData V` in `EG/Defs/Vortex/PVData.lean` (fields `Z O sO A R M sOwn Rt Pl ext`). The PV Spec takes `D : PVData V` and states its hypotheses about the fields; s5 passes `EG.Light.childData ω Z : PVData V` with no bridge. Own classes `R : Fin (pvJ Z.card) × Fin 4 → FGraph V`, indexed by the vertex-set field `Z`, not by `O.card` (PV-OWNCLASS-INDEX); `J`, `m`, `b` are not fields (`pvJ`, `pvM`, `pvB` at `Z.card`); `ext : V → Option (Fin 4)`, `none` = `*` (PV-EXT-ENCODING). The PV hypotheses as named Defs remain the s4 Spec author's job.
  - **HB-FAMILY** (same round): `EG.IsHBFamily X m b A` lives in `EG/Defs/Link/HBFamily.lean` (neutral namespace), and the s3 lemHB Spec, the PV hypothesis (1) and s5 `AY` all use it.
  - **lemChild (b)–(d) per part** (same round): `EG.Light.ArcSys ω Z H0 as`, with the `H_0` condition `EG.Light.H0Adm ω Z H0` (`Own_Z ⊆ H_0 ⊆ E_l(Z)`). The lemChild Spec concludes `ArcSys`, and `ArcHyp ω l H0 arcs := ∀ Z ∈ childParts ω l, H0Adm ω Z (H0 Z) ∧ ArcSys ω Z (H0 Z) (arcs Z)`.
- Inputs that are only asserted to exist become universally quantified: lemParent takes **any** arc systems with the child-side properties (PAR-ARCS-INPUT). K-RED is pure existence for any admissible family Lentext.

### 2.9 s6 interfaces
- **JS-LC and J⁺ are one existential Spec**, `JSLCStatement`, whose conclusion contains `JPlusProps ω l J`. `EG/Defs/Chain/JSet.lean` has exactly the fields that s7a's `RoundInput.Valid` needs:
  - types and role partition (J3);
  - **J1 aggregated over all parts** (hubs, fresh centres, lost centres);
  - J2 per part, at vertices outside D_l, and in total (`|J| ≤ n(M−1)`);
  - `J ⊆ ⋃ B_Z ⊆ ⋃ E_l(Z)`;
  - (ii) the fresh-centre cap.
  (iii) and (iv) are run lemmas, and (v) is a Stage1-law lemma; they stay out of JPlusProps. The bound in JSLCStatement uses `1.5 Σ m` (T1 patch).
- **J-consumer:** `structure JConsumer` with `out : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V)`. JC1 and JC2 are required **only for J with JPlusProps**. JC2+JC3 are phrased as `IsDecomp (J ∪ LentJV) Obj` with every object WF, so that s7:lemLift(iv) produces exactly this predicate.
- **MIX-C = Option B′** (s7b; it contains s6b's Option B as a special case). The hypothesis is a J-dependent bound `b : ℕ → Finset (Sym2 V) → ℝ` with `∀ l J, JPlusProps ω l J → (C.out l J).1.length ≤ b l J`. The conclusion is `∃ Js, (∀ l ∈ [3,R], JPlusProps ω l (Js l)) ∧ ∃ D, IsDecomp E(G) D ∧ D.length ≤ … + Σ_l b l (Js l)`. Then s7 takes `Q_l := quotient ω l (Js l)` for both conclusions of JV⁺*.
- The chain (consOrder) and the Lent sets stay **proof-internal**, by strong recursion on R+1−l. The standalone chain is built first, and K-RED is applied once (ORDER-DECOUPLE, checked).
- **Designation:** `δ : ℕ → V → PartId`, a parameter quantified before any FinDist; `IsDesignation` constrains only classed ports. Existence comes from `anc_l(u) ≠ ∅`. Class degrees count edges of `E_l(Z)` at `h` (the literal text of s6:defDesign; D-DES-3 of work/p2d/design.md), with the equivalence lemma `classDeg_eq_card_ports` to port counting.
- **Clusters:** G-free and indexed by `Fin N` with a layer map. Admissibility is balance at hubs (never `IsBalanced`).
- **HCC-P:** uniform in k, with `succ j := (j+1) mod k`. Path families are `List (List V)`.
- **Components of edge sets** (`edgeVerts`, `edgeComps`, `compEdges`, `IsNonBridge`, `IsPendant`) live in `EG/Defs/Components.lean`, shared by PAR and defDesign ("giant").

### 2.10 s7 interfaces
- **The past is a parameter.**
  - `RoundInput V` is an abstract record: graph, `M : ℕ`, `lam`, ancestors with round, vertex set, LJV class and lend-goodness, pool with pool round, role sets, class map, JV-bad, and the J-classes.
  - `RoundInput.Valid` holds exactly the JPlusProps fields plus the pool, candidate and Γ consequences (`M ≥ 2^40`, `Hcd ≥ 2^10 M^10`, JV-good ⇒ `|Cand| ≥ Hcd`).
  - `Hcd := lam^95/(8M^2)` and `Cand` are *defined* from the fields.
  - The instantiation lemma `RoundInput.ofPast_valid` is reviewed jointly with s6.
  - `roundLaw := uniform (Lists × Orders)`. Here `η_h : Equiv.Perm (Fin (4M))`, `ζ` is over all ordered pairs, and `≺_u` is a rank `↥G.verts ≃ Fin n`.
- `Rules I` as in §1a.
- **The round step lives in Defs** (`EG/Defs/Quot/Round.lean`), with total fallbacks; lemWellDef states "no fallback is taken". The Markov choice is `xiChosen ω l J := if h : ∃ ξ, 0 < w ξ ∧ markovEvent … then Classical.choose h else default`.
  - Tier-1 Specs: lemVstar, lemEXprime, thmJVps and lemGammaSat.
  - Tier-2 Specs: lemPay (with per-round forms), lemUHsplit, propCost and lemOneOutcome (split into `exists_stage1_selected`, deterministic stage 3, and `xiChosen_mem`).
- **QVert (resolves s7a vs s7b):**
  - `EG.Quot.QVert V := QTag × V` with `QTag := Bool × ℕ × ℕ × Bool` (P/H kind, colour, **rank**, **side**).
  - The side tag makes HUB edges non-loops by construction, and the rank tag keeps parallel edges apart; both are mandatory.
  - `Q_l.verts :=` the endpoints of the edges, so isolated vertices are deleted by definition. PAR layer edges exist only for unpaid (non-looped) objects, so `FGraph.loopless` is definitional.
- `tCC` is one Defs constant, used by lemCC(iii) and X_{V,l}. The weight ω_l(v) is named `poolWeight`.
- `Dec_l := Classical.choose (exists_isDecomp_length_eq_fnum …)`. lemLift(ii) is proved for every decomposition.

### 2.11 Graph-level objects (s1, s3, s4)
- Move `Obj.isEdge` into `EG/Defs/Objects.lean`.
- New in Defs:
  - `EG.IsPathDecomp`: at least 2 vertices per path;
  - `EG.pathEndCount`;
  - `EG.FGraph.nbrSetDeg`: N_{G,d}(U), shared by B-M Prop 12 and P13\*.
- `EG/Defs/Link/Star.lean` (owned by s3a) holds the (eqStar) parameters `EG.Star.*` as functions of `(n, ε', ρ, t)`, with p_* in rpow closed form. No s3 Spec inlines copies of these constants. `IsWellExpanding` is **not** in Star.lean: it is `EG.FGraph.IsWellExpanding` in `EG/Defs/Graph.lean` (P2-D small, since it depends on θ only); Star.lean uses it and must not redefine it.
- **Multigraphs** (`MGraph N E := E → Sym2 N`, loops allowed, loop degree 2, components, forests, T-join, Euler) are needed only inside proofs (s5:lemParent Step 3). They go in **Lib** (`EG/Lib/Found/Multigraph.lean`), not Defs, because no Spec mentions them. The stage-α Euler hypothesis is the SimpleGraph form, with connectivity only among positive-degree vertices (EUL-EMPTY), and the multigraph version is derived by subdivision.
- The s7 layers use the tagged encoding, not MGraph.

### 2.12 Recorded T0 decisions (add to CONVENTIONS.md T0 record)
- (R1) as any maximal family.
- (R5)(3) home order.
- s5:lemParent/K-RED "depends only on" clauses are dropped: pure existence, and MIX-C is restructured.
- JS-LC's hypothesis "not used" is encoded as disjointness in MIX-C.
- lemOneOutcome is split into three parts.
- TPV, PV and VX⁺ are deterministic.
- propStructure drops `n ≥ N_0`.
- OV constants use 17/41.
- `logStar` uses `sInf`.
- Stage-1 `dite` guards for zones and pool.
- Γ2(b),(c) are lemmas.
- Final names of the P2-D small Defs: constants `epsC`, `sigmaC`, `Cp`, `Aexp`; `FGraph.nbrSetDeg`, `FGraph.IsWellExpanding` (in `EG/Defs/Graph.lean`, not Star.lean); `logIter`, `tower`, `logStar`; `IsPathDecomp`, `pathEndCount`, `IsPathCycleDecomp`; `edgeVerts`, `edgeGraph`, `edgeComps`, `compVerts`, `compEdges`, `IsNonBridge`, `IsPendant`; `Gamma1a`–`Gamma1e`, `Gamma1Items`, `Gamma1core`, `Gamma2a`.
- Components / bridges / pendant edges / path decompositions are for loopless edge sets only (as `fnum`).

---

## 3. Defs modules, in dependency order

Existing and locked-candidate modules: `Defs/Graph`, `Walk`, `Expander`, `Objects`, `Fnum`, `Orient`, `Prob/FinDist`.

1. `EG/Defs/Objects.lean` (edit): add `Obj.isEdge`; `EG/Defs/Graph.lean` (edit): add `nbrSetDeg`.
2. `EG/Defs/Log.lean`: logIter, tower, logStar.
3. `EG/Defs/Constants.lean`: ε, σ, Cp, Aexp.
4. `EG/Defs/PathDecomp.lean`: IsPathDecomp, pathEndCount (Cor 22, PV).
5. `EG/Defs/Components.lean`: components, bridges and pendant edges of edge sets.
6. `EG/Defs/Gamma/Core.lean`: Gamma1core, Gamma2a.
7. `EG/Defs/HB/Witness.lean`: IsWitness, witN, witF0, split constructors, τ-rule sets.
8. `EG/Defs/HB/SplitTree.lean`: STree, addresses, graphAtD, leaf/internal addresses, Dup, deleted, graft, IsS0Rec, IsTauSplitTree, IsTauRun, DeltaGe, dupGe, cOV.
9. `EG/Defs/HB/Round.lean`: MOf, TOf, sOf, POf, tauOf, thetaGC, RoundChoice, the round-local objects, Round.Valid.
10. `EG/Defs/HB/Run.lean`: Run, graph/d/R, Run.Valid, PartId, Std, lightParts, ancestors, anc, classed/fresh ports, mult, mu, nuAnc, j0/j1, epsA, psiPool, HypH.
11. `EG/Defs/Link/Star.lean`: the (eqStar) parameters (uses `FGraph.IsWellExpanding` from `EG/Defs/Graph.lean`, item 1; no redefinition).
12. `EG/Defs/Vortex.lean`: size predicates, η functions, tpvJ/pvJ/vxJ, pvM, pvB.
13. `EG/Defs/Lend/COLTable.lean`: `col3`, rows, triples.
14. `EG/Defs/Gamma/Full.lean`: Gamma1f, Gamma1, N0Cond, Gamma3, RunHyp.
    - **Required Lib lemma (not optional):** `EG.Vortex.eventually_size : ∀ᶠ N in Filter.atTop, Vortex.TPVSize N ∧ Vortex.PVSize N ∧ Vortex.VXSize N` (in `EG/Lib/Vortex/`). `N0Cond` is satisfiable only through it, so `EG.exists_N0` and every s5–s7 Spec assuming `N0Cond` depend on it. Route (work/p2d/params.md): bound each η term by 2^{-20} for L ≥ 2^{10} via `two_pow_mul_exp_neg_le` and log₂L ≤ L/16; prove `TPVSize N ↔ 2^10 ≤ L N` (same for PV, VX). Only the point N = 2^{1024} is proved so far (EGTest/Params). (P2-D [params] review 2.)
15. `EG/Defs/Stage1/COL.lean`: lentIdx, Tslot (needed by `IU`), kown, ownIdx, per-edge labels, JS sites, T_j(Y,l), the classes Own/Lend/LJS/LJV/LU, and the event predicates COLa, COLb, COLc, COLe, COLg.
    - Design note must state: `kown Y = 4·pvJ|Y| + 1 ≥ 1` for every ancestor (`pvJ` is a `Nat.floor`, junk 0 for tiny Y), so `Fin (kown Y)` is nonempty and needs no guard (§2.7).
16. `EG/Defs/Stage1/Zones.lean`: zone law (with `dite`), Zone, zonePhase, ρ_Y (Tslot is in COL.lean; stage1 fix round 1).
17. `EG/Defs/Stage1/Pool.lean`: pool law (with `dite`), Pool_l, poolRound.
18. `EG/Defs/Stage1/Law.lean`: `Stage1.Outcome`, `Stage1.law`, projections.
19. `EG/Defs/Light/Stages.lean`: A_Y (Classical.epsilon of IsHBFamily), (E1), demoted, parent-bad, Bad, Rt, Pl, par, dem, lp.
20. `EG/Defs/Light/Constants.lean`: epsU, epsChain.
    - **G-S5-1 (design review 2, MINOR-B):** `noncomputable def epsChain (D : ℝ) : ℝ := EG.Chain.epsK D` (import `EG.Defs.Chain.Constants`); never a second literal copy of the ε_ch formula. For item 19, keep the types `StageData.ofOutcome` takes: `demoted ω run G : PartId → Prop` (total; the light guard is inside `lendBad`), `dem ω run G`, `lp ω run G : ℕ`, so the s6 record is `StageData.ofOutcome ω (demoted ω run G) (dem ω run G) (lp ω run G)` with no cast.
21. `EG/Defs/Chain/Cluster.lean`: Cluster, beadCount, ParityClean, IsAdmissible, exc, load, medOrient.
22. `EG/Defs/Chain/EqLpt.lean`: IsGreedyLPT, layerLoad.
23. `EG/Defs/Chain/HCCP.lean`: HccpData, Valid.
24. `EG/Defs/Chain/Design.lean`: IsDesignation and the class data (m_{Y,l}, d\*, α, c^agg, γ_l).
25. `EG/Defs/Chain/Lending.lean`: lend-bad, Lost, Ret, Qs, O_Z, lostRound, X_U.
26. `EG/Defs/Chain/JSet.lean`: JPlusProps.
27. `EG/Defs/Chain/JConsumer.lean`: JConsumer.
28. `EG/Defs/Chain/Constants.lean`: epsCONC, epsM.
29. `EG/Defs/Quot/Cand.lean`: Hcd, cand, candMean, JVBad.
30. `EG/Defs/Quot/Schedule.lean`: Lists, Orders, Xi, roundLaw.
31. `EG/Defs/Quot/Round.lean`: RoundInput (+Valid, ofPast), Rules (+Valid), items, PAR objects, groups, lists, SDR, the (e1) fold, (e2), loops, layers, ranks, QVert, quotient, lift, Obj_l, LentJV_l, payrd, copies, markovEvent, xiChosen.
    - **Joint review with 26/27 (design review 2, MINOR-A):** `ofPast` must use `hubs := run.D G l`, `fresh := freshCentres`, `ports := qsRound`, `lost := lostRound`, `cls := δ l` (with a nonempty ancestor type), `ljv Y := S.ljv Y l`, `lendGood := ¬ lendBad`; discharge each `Valid` field with the Lib lemmas named in work/p2d/design.md ("Interface map", "Fix round 2"); the s7 Specs carry `S.Coherent run G` (or `ω ∈ supp` with `coherent_ofOutcome`).
32. `EG/Defs/Quot/Xprime.lean`: tCC, XVl, XV, poolWeight, jvBadPorts, Xpool, Xprime.
33. `EG/Defs/Quot/Constants.lean`: epsX, detl, FQ, eps2, eps1, C0.
34. `EG/Defs/Main/Gamma.lean`: Gamma4, GammaCond, cEG.

Items 11–13 depend only on items 2–6 and may be written in parallel with items 7–10. Items 21–23 depend only on item 5 and the existing Orient, so they can start immediately.

Lock gates:
- items 9, 15 and 31 cannot be locked before the M-INTEGER patch lands in s2.tex;
- item 31 cannot be locked before patch set R lands in s7.tex;
- items 26, 27 and 31 are reviewed together (JPlusProps ↔ RoundInput.Valid ↔ MIX-C B′).
- `EG/Defs/Chain/StageInst.lean` (`StageData.ofOutcome`, `StageData.Coherent`) is locked only after items 15–18; any change to `Outcome.labAt`, `COLa`/`COLb`, `Own`/`LJS`/`LJV`, `jsSites`, `lateRounds`, `KJS`, `tJS` forces a re-review of it (design review 2, MINOR-C).

---

## 4. Probe closures (PLAN §6 P2b) and the Defs each one needs

| Probe | Chain | Defs needed (numbers from §3) | Can start |
|---|---|---|---|
| **P-1** s7 lift, Q_l simple, MULT, WellDef (J⁺ assumed) | lemSimple → lemMULT (+ PAR-MULT identity) → lemWellDef(i)–(v), including the Cuckoo SDR bound (iii) → lemLift(i)–(iv) | 1, 29, 30, **31** with `RoundInput` abstract (so s2/s6 are not needed; mult_r comes from RoundInput's ancestor data; `mult ≤ μ` stays an s2 input). Also Lib `Prob/Uniform.lean` (uniform product = product; image of a k-set under a uniform permutation; i-th element of a set in a uniform order; conditioning on product atoms). | After M-INTEGER and patch set R. Independent of the s2 lock; `ofPast_valid` is deferred. |
| **P-2** GATE/MED/EQ-LPT/PAR/HCC-P → JS-LC → J⁺ | Engine: MED, EQ-LPT (+existence), PAR (+existence), HCC-P, HCCglob; then the JS-LC Step 6/7 hypothesis checks (joint multiplicity `≤ 2M_l−2 ≤ t^JS`, distinct pair ends, T-avoidance, aggregated J1); then JSLCStatement with JPlusProps | Engine: 5, 21, 22, 23 plus the existing Orient/Gate (**immediate**). JS-LC/J⁺: 9, 10, 15 (JS labels, T_j, LJS classes, COLb), 24, 25, **26**, and Lib greedy (Δ+1)-colouring and edge-set components. | Engine now. JS-LC after the Run.lean and Stage1/COL drafts (M ∈ ℕ). |
| **P-3** τ-rules → Lemma 14^τ → thin cut → GC → ORIGIN → CONC/CONC-L(iv) | defTauRules facts → SEP → thinCut → OV(sharp) → lem14tau → lemGC → propOrigin(a),(b) (graft lemmas) → CONC(i)–(iii) → CONC-L(iv) (the shared τ- and d\*-sums, the tower facts eqTowerHalf/eqTowerEnd) | 2, 3, 6, 7, **8 (graft API)**, 9, 10, 24, 28. Lib: log\* API, OV potential lemma. | Items 7–8 now. ORIGIN/CONC after Run.lean. |
| **P-4** CR1-PV sites | PV(c) core (type (1)/(2)/arc analysis, stripping, per-vertex bound) → lemChild (PV instance, (E1′)) → lemParent Steps 1–9 (quotient multigraph, T-join, Euler, trail surgery, slots, multiplicity `M_l−1 ≤ t_Y`, η halving) → COL(c) (T16\* per U-index, joint independence) → COL-JV rows 4, 7, 8 → (P4) | 1, 4, 11, 12, 13, 14, 15, 16, 19, 10 (light parts, L_Y, ν_l). Lib: Multigraph/T-join/Euler (stage-α Euler hypothesis), vortex step engine (Trail, Ends, (S)/(C)). | PV(c) core and rows 4/7/8 as soon as 11–13 exist. Child/Parent after Stage1 and Stages. |
| Cheap numeric probes | Cap(i) (depends on `EG.bmLemma25`: prove Lemma 25 with constant 18); L17\* margins (0.09/4.2 vs 1/47; 2^19/28200 ≥ 18); WellDef(iii) series `Σ T_s ≤ K^-4` for K ≥ 10^4; OV 17/41; CC 44.7/29.8 (needs e < 2.7188) | Cap: existing. L17\*: 11. WellDef(iii): none (pure reals). | Now. |

Refutation targets that each probe must hit explicitly (s1:remStatus(iv), s7 "What is not established"):
- P-1: a lifted cycle repeating a vertex (lemLift(ii)).
- P-2: two J^hub edges of one class at one hub in one round (J1 aggregated).
- P-3: CONC-L(iv) per-ancestor bound.
- P-4: a per-vertex multiplicity feeding a path-connectivity parameter t: PV(c) deg bound; Parent Step 5 `M_l − 1 ≤ t_Y`; COL(b)/(c) t^JS and t_Y.

---

## 5. Size estimate

| Source | New Lean lines |
|---|---|
| Chunk estimates from the blueprints: s1 6.5k, s2a 4.47k, s2b 4.33k, s3a 4.01k, s3b 4.29k, s4 6.28k, s5 6.34k, s6a 3.72k, s6b 7.94k, s7a 5.32k, s7b 3.99k | **57.2k** |
| Stage-β discharges: Lovász 2–4k, Haxell 1.5–2.5k, Euler about 0.8k if the Mathlib PRs do not land | 4.3–7.3k |
| Glue not counted by any chunk: `RoundInput.ofPast_valid`, RunHyp transfer lemmas, Stage1 marginal and independence lemmas, the MIX-C B′ ↔ s7 bridge, the HI Fintype adapter, EGTest non-vacuity and definition tests (Run.Valid satisfiable, JConsumer trivial instance, Rules.exists_valid) | 5–8k |
| **Total new** | **≈ 70k (range 60–105k)** |

- About 11.1k lines of Lean already exist (`EG`, `EGTest`, `EGCheck`), so the finished project comes to about 80k (range 70–115k).
- This is below PLAN's 115k (range 80–170k). Blueprint self-estimates have historically been optimistic, so the upper end of the range is a factor of about 1.5 on the chunk sum.
- The **locked Defs surface is about 7–8k lines** (items 1–34). The largest are Round.lean (s7, ~1k), Run.lean + Round.lean (s2, ~1.1k plus a ~600-line API) and Stage1/COL.lean (~0.75k). Budget Defs review accordingly.
- The largest single proofs: JS-LC (~4.2k), TPV engine (~3k), lemParent (~3k), L17\* (~1.7k), PV (~1.6k), VX⁺ (~1.3k), B-M Lemma 25 (~1.2k), HCC-P (~1.1k).

## 6. Actions (in order)
1. Apply the M-INTEGER patch: (R2), propDegRec, (B6), lemCap(ii) wording, symbol table.
2. Apply patch set R to s7.tex.
3. Apply the T16\*(c) and JS-LC statement wording fixes.
4. Get a targeted clean-room re-review of the patched lines (G0 pattern), and record the patches in the ledger/errata as T1.
5. Correct commit `ee8b589`'s characterisation of M-INTEGER as "T0" in `STATE.md`.
6. Refresh `blueprint_s1.md` and `blueprint_s2a.md` line references against `4fcfe88`. Their decisions are unchanged.
7. Update PLAN §2 R4 (single Hall, exactly b).
8. Add the §2.12 decisions to `CONVENTIONS.md`.
9. P2-D: write the Defs in the §3 order.
10. Start probe P-2's engine, P-3's items 7–8 and the cheap numeric probes now. Start P-1 as soon as items 1–2 above land.
