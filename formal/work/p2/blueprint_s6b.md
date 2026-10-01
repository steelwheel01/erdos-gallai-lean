# P2-U formalization blueprint: chunk s6b (s6: CONC-L, lending statuses, Lost, JS-LC, J+, J-consumer, the processing order, Lent sets, MIX-C)

Manuscript: `proofs/manuscript/s6.tex` lines 335-865 (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s6b.json` (same content, one object per label, same field names as `nodes_s1.json`/`nodes_s2a.json`). Line numbers refer to `s6.tex`. Lean names in `code` that already exist were checked against `formal/EG/**` (EG.Obj, EG.IsDecomp, EG.FGraph, IsExpander, IsPathConnected, IsOrientation, FinDist); run/ancestor names follow the proposals of `blueprint_s2a.md` (EG.HB.Run.*); everything else is a proposal.

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s6:thmCONCL` | theorem | Spec EG/Spec/Chain/ConcL.lean (ConcLStatement, parts (i)-(iv) as one conjunction per (Y,l,h) plus the global s... | 650 | 3 | risk (CONCL-TOWER-ANALYSIS) |
| `s6:defLending` | definition | Defs EG/Defs/Chain/Lending.lean (lendBad, lost, ret, qs, OZ, lostRound, XU) + API lemmas (partition Z^0 = Ret ... | 220 | 2 | blocker (M-INTEGER) |
| `s6:lemLost` | lemma | Spec EG/Spec/Chain/Lost.lean (LostStatement: (i) chain of three inequalities per classed port, (K6), (iii)) | 380 | 3 | blocker (M-INTEGER) |
| `s6:lemJSLC` | lemma | Spec EG/Spec/Chain/JSLC.lean: ONE existential statement JSLCStatement that also carries the J+ interface (s6:l... | 4200 | 5 | blocker (M-INTEGER) |
| `s6:remStar` | remark | nothing to formalize (no statement) | 0 | 1 | note (STAR-NONE) |
| `s6:lemJplus` | lemma | Defs: structure EG.S6.JPlusProps (EG/Defs/Chain/JSet.lean), a conjunct of JSLCStatement (no standalone Spec: t... | 350 | 3 | risk (JPLUS-EXISTENTIAL) |
| `s6:defJconsumer` | definition | Defs EG/Defs/Chain/JConsumer.lean: structure EG.S6.JConsumer (a function (l, J) ↦ (Obj_l, LentJV_l) with JC1, ... | 90 | 2 | risk (JCONS-TYPE) |
| `s6:consOrder` | construction | Proof-internal definitions (recommended: EG/Proof/Chain/MixC/Chain.lean, `noncomputable irreducible_def` with ... | 450 | 4 | risk (ORDER-RECURSION) |
| `s6:lemLent` | lemma | Proof-internal lemmas of the MIX-C proof (EG/Proof/Chain/MixC/Lent.lean) | 300 | 3 | risk (LENT-KRED-FORM) |
| `s6:thmMIXC` | theorem | Spec EG/Spec/Chain/MixC.lean: MixCStatement (Option B: decomposition + cost, with a per-round bound hypothesis... | 1300 | 4 | risk (MIXC-SUMOBJ) |

Estimated new Lean for this chunk: **~7940 lines** (JS-LC alone ~4200, difficulty 5). One **blocker**, inherited: M-INTEGER (= HB-M-INTEGER of blueprint_s2a): K^JS_l = M_l^2 is a number of classes and K^JS_l rho_l = M_l^-2 an exact probability, while M_l is real in (R2); the s2a proposal (M_l := ceil(...) ∈ ℕ) was re-checked against every inequality of this chunk and has ample slack. The mathematics of all ten items was re-derived (CONC-L sums; Lost probabilities; every step of JS-LC incl. eqSzeroCost, eqCherryCost, the multiplicity 2M_l-2 <= t^JS_l, the Step-8 count; J+; the coverage and cost of MIX-C) and found correct as stated, modulo the implicit hypotheses listed. The real risks are architectural: J+ and the J-consumer are statements about constructions (they must become conjuncts/structures), the J-consumer and MIX-C's Σ|Obj_l| need an interface decided jointly with s7, and the stage-3 good events must be passed as abstract conclusions.

## 2. Cross-cutting decisions proposed for the integrator

- **M_l ∈ ℕ (blocker M-INTEGER, inherited).** Same decision as blueprint_s2a HB-M-INTEGER. Uses in this chunk: K^JS_l = M_l^2 junction classes and label values, K^JS_l rho_l = M_l^-2 (s6:lemLost(i)), k_0 = min(K^JS_l, ...), k_i = min(K^JS_l, ...), 'M_l - 1 cherry systems', pad <= ceil(M_l/2), t^JS_l = 2M_l + 2. Fallback: K^JS_l := ceil(M_l^2) and s6:lemLost(i) reads <= M_l^-2 + M_l^-4 (final bound 2M_l^-2 unchanged).
- **JS-LC and J+ are one Spec (JSLC-JPLUS-MERGE).** `JSLCStatement` is an existential over (J_l, LentJS_l, D) whose conclusion includes `JPlusProps ω l J` (types, J1 at hubs/fresh/lost centres, J2cap, J2card, (ii)). J3, (iii), (iv) are J-independent run lemmas; (v) is a Stage1-law lemma (s3). The 'for every choice / Steps 3-8 delete nothing' clause is not formalized (not used downstream).
- **g_{Y,l} does not appear in any Spec (JSLC-G-UNDEFINED).** The JS-LC cycle bound is stated as 126 n/M_l + 1.5 Σ_{Y: (Y,l) giant} m_{Y,l}.
- **'Used' is not a predicate (JSLC-USED).** JS-LC assumes nothing about prior use and outputs LentJS_l ⊆ the round-l JS classes of lend-good ancestors of rounds <= l-2; exclusivity (COL(g)) is proved as disjointness inside MIX-C.
- **J-consumer interface (JCONS-TYPE, JCONS-CONDITIONAL).** `structure JConsumer ctx := (out : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V)) (jc : ∀ l J, 3 ≤ l → l ≤ R → JPlusProps ω l J → JC1 ∧ JC2)`; JC3 is implied by IsDecomp. Fresh randomness is resolved inside the consumer (s7 picks xi_l by choice in the Markov event, which is nonempty for every past). Verified: s7:consRound depends on the past only through J_l and stage-1 data.
- **MIX-C Option B (MIXC-SUMOBJ).** Spec = 'there is a decomposition D of E(G) with |D| <= (D_*/2+745+338)n + eps_M n + [80dem+369lp+169Σ|Lost_l|] + 1.5Σm + Σ_l b_l' for every consumer whose output length is <= b_l on every admissible J. The chain (s6:consOrder) and the Lent sets (s6:lemLent) are proof-internal. Verified that s7's per-round bounds are uniform in the past (payments, fresh legs, SDR/loops, |V(Q_l)|), so Option B suffices for s7:propCost; to be confirmed by the s7 blueprint. Fallback Option A: the chain as a Classical.epsilon definition in EG/Defs/Chain/Order.lean and Σ_l |(C.out l (chain l).J).1|.
- **Decoupling (ORDER-DECOUPLE).** The standalone chain (TPV, JS-LC, consumer; rounds R..1) never reads light-part outputs, and s5:lemKRED holds for any admissible family Lentext. Lean builds the standalone chain alone and applies the K-RED Spec once with the final Lentext(Y) = LentJS(Y) ∪ LentJV(Y). Requires the K-RED Spec in the 'for any family' form (LENT-KRED-FORM; coordinate with the s5 blueprint).
- **Stage-3 good events as abstract conclusions (ORDER-STAGE3, MIXC-STAGE3-ABSTRACT).** MIX-C takes `TPVGood (Z^0) (O_Z ω) (Ret_Z ω)` for every Z ∈ Std and K-RED's light-part predicates as hypotheses; the TPV applicability bullet of (a) is a separate Spec `MixCTPVApplicable` used by s7:lemOneOutcome to show the good events are nonempty.
- **Stage-1 space (LOST-SPACE-MARGINALS).** One joint FinDist `S3.stage1Dist run G` over families 1a-1d; lemCOL, lemE1 and lemExpect must be stated on it (or transported by marginal lemmas) before s6:lemLost can be proved.
- **Index conventions.** Sums 'over (Y,l)' are Σ_{l ∈ [1,R]} Σ_{Y ∈ run.allAncestors} with a vanishing lemma (m_{Y,l} = 0 unless r(Y)+2 <= l, l >= 3). X_U and Σ|Lost_l| sum over l ∈ [1,R].
- **Γ hypotheses.** s6:thmCONCL: Gamma1, Gamma2a, d_1 >= D_*. s6:lemLost, s6:lemJSLC, s6:thmMIXC: the s5 setting (N0Cond N0, GammaCond N0 D_*, n >= N0, d_1 >= D_*).
- **Undeclared dependencies found in proofs** (for msreport): s6:thmCONCL uses s6:eqTowerHalf/s6:eqTowerEnd (labelled equations, chunk s6a) and s2:defAncestors; s6:defLending uses s2:defAncestors, s2:defHBtp (and names s4:lemTPV); s6:lemLost uses s1:condG1, s2:defHBtp; s6:lemJSLC uses s6:defCluster, s3:remMultiset, s2:defAncestors, s1:defObject, s1:factAdd; s6:defJconsumer uses s6:defLending, s1:defObject; s6:consOrder uses s5:lemKRED; s6:thmMIXC uses s6:defLending, s1:factAdd. Declared but not logically used: s2:lemSEP, s2:lemThinCut in s6:thmCONCL (only via propOrigin); s4:lemTPV, s5:lemChild, s5:lemDemoted, s4:thmVXp in s6:lemLent; s4:lemPV, s4:thmVXp in s6:thmMIXC (only via s5).
- **Modules.** Defs: `EG/Defs/Chain/Constants.lean` (epsCONC, epsM), `EG/Defs/Chain/Lending.lean`, `EG/Defs/Chain/JSet.lean` (JPlusProps), `EG/Defs/Chain/JConsumer.lean`, `S4.TPVGood` (s4 Defs). Specs: `EG/Spec/Chain/{ConcL, Lost, JSLC, MixC}.lean`. Proofs: `EG/Proof/Chain/{ConcL, Lost}.lean`, `EG/Proof/Chain/JSLC/*.lean`, `EG/Proof/Chain/MixC/{Chain, Lent, Coverage, Cost}.lean`.

## 3. Hazard index (all nodes, most severe first)

| severity | label | node | summary |
|---|---|---|---|
| blocker | M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a) | `s6:defLending` | K^JS_l := M_l^2 is used as the NUMBER of JS classes / label values (0 <= j < K^JS_l) and K^JS_l * rho_l = M_l^-2 is used as an exact probability; M_l of (R2) is a real. This chunk also uses 'M_l - 1 c... |
| blocker | M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a) | `s6:lemLost` | K^JS_l := M_l^2 is used as the NUMBER of JS classes / label values (0 <= j < K^JS_l) and K^JS_l * rho_l = M_l^-2 is used as an exact probability; M_l of (R2) is a real. This chunk also uses 'M_l - 1 c... |
| blocker | M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a) | `s6:lemJSLC` | K^JS_l := M_l^2 is used as the NUMBER of JS classes / label values (0 <= j < K^JS_l) and K^JS_l * rho_l = M_l^-2 is used as an exact probability; M_l of (R2) is a real. This chunk also uses 'M_l - 1 c... |
| risk | CONCL-TOWER-ANALYSIS | `s6:thmCONCL` | (iv) rests on the unlabelled analysis before thmCONC (s6:eqTowerHalf, s6:eqTowerEnd; chunk s6a): monotonicity of t ↦ (2log t+6)/t, (7+2log t)/t, (2log t+5)/t^{1/2} for t >= 4, log* identities (log* x ... |
| risk | LEND-COL-EVENTS | `s6:defLending` | 'An event of Lemma COL(a)/(b) fails' refers to the conclusion events of a probabilistic lemma. Lean needs named predicates COLaEvent/COLbEvent in the s3 Defs with exactly these parameters: (eps_Y, s_Y... |
| risk | LOST-HYPS | `s6:lemLost` | 'Fix a valid run and a designation' hides: Γ1 (lemCOL, lemE1, lemExpect all assume it), n >= N0 and d_1 >= D_* (propStructure(iv), lemTower(b)), and 3 <= l <= R for (i). Without Γ1 the probability bou... |
| risk | LOST-SPACE-MARGINALS | `s6:lemLost` | The events 'Y lend-bad' combine COL(a),(b) (coordinates 1a,1c of Y) and demotion (which contains (E1), depending on 1a of Y and on the zones 1b of ALL vertices of Y). s3:lemCOL is stated 'over the sta... |
| risk | JSLC-G-UNDEFINED | `s6:lemJSLC` | Definition-vs-use: the statement's bound Σ_{giant} sc_{Y,l}, sc = (3g_{Y,l} - 6M_l)^+, uses g_{Y,l} = number of cherry classes, an object that exists only inside the proof (Step 5, a greedy colouring)... |
| risk | JSLC-JPLUS-MERGE | `s6:lemJSLC` | s6:lemJplus asserts properties of 'the' J_l built in Step 2 of THIS proof ('for every choice of which edges are deleted'). In Lean JS-LC is an existential, so J_l has no identity outside it: the J+ pr... |
| risk | JSLC-USED | `s6:lemJSLC` | The hypothesis 'no edge of any class LJS_{Y,l,j} has been used' is not a mathematical predicate (it refers to the state of the assembly). Lean encoding: JS-LC assumes nothing and outputs LentJS_l ⊆ le... |
| risk | JSLC-PROOF-SIZE | `s6:lemJSLC` | The proof is the largest single combinatorial construction of s6: (1) classification of B_Z edges; (2) PAR per part and per class pair, parity moves with hub degrees AGGREGATED over all parts of round... |
| risk | JSLC-HCCP-INTERFACE | `s6:lemJSLC` | JS-LC applies HCC-P to systems whose clusters come from two different sources (MED-oriented components; cherries u -> h -> u') with padding, depth k=1 special case (X^out/X^in, no padding) and path fa... |
| risk | JPLUS-EXISTENTIAL | `s6:lemJplus` | The lemma is a statement about the CONSTRUCTION inside another lemma's proof ('J_l consists exactly of the deletions of Step 2 ... for every choice'; 'Steps 3-8 delete nothing'). Not formalizable as a... |
| risk | JPLUS-S7-INTERFACE | `s6:lemJplus` | JPlusProps is the ONLY information the s7 J-consumer gets about J_l (in the recommended MIX-C design). Before the freeze, cross-check every s7 proof that cites 'properties of J_l' against the conjunct... |
| risk | JCONS-TYPE | `s6:defJconsumer` | 'A rule that, given everything constructed at rounds > l, the stage-1 outcome and J_l (and possibly fresh randomness), outputs ...' is not a mathematical object. Decision needed before freeze: type of... |
| risk | JCONS-CONDITIONAL | `s6:defJconsumer` | Definition-vs-use: the definition demands JC1-JC3 of the output, implicitly only for the actual J_l ('Here J_l has the properties of Lemma J+'). The s7 round step is NOT a J-consumer on arbitrary edge... |
| risk | ORDER-RECURSION | `s6:consOrder` | The chain is a recursion over rounds with choices from existential Specs (TPV split, JS-LC outputs). In EG/Defs/** a definition may not depend on proofs: use Classical.epsilon of the defining predicat... |
| risk | ORDER-STAGE3 | `s6:consOrder` | 'Stage-3 outcomes ... each fixed in its good event' refers to events that exist only inside existential Specs (s4:lemTPV, s4:lemPV/s5:lemChild, s4:thmVXp/s5:lemDemoted). Lean: the construction/MIX-C t... |
| risk | LENT-KRED-FORM | `s6:lemLent` | (iv) presupposes that the s5:lemKRED Spec is stated in the 'for any family' form with LentU and H_0 internal to K-RED ('H_0(Y) of that lemma'). If the s5 blueprint states K-RED with H_0 as input or wi... |
| risk | MIXC-SUMOBJ | `s6:thmMIXC` | (c) contains Σ_l /Obj_l/ for the consumer's outputs on the J_l that the construction produces; stating this needs either the construction in the Spec (Option A: the chain as an epsilon-definition in D... |
| risk | MIXC-STAGE3-ABSTRACT | `s6:thmMIXC` | Same as ORDER-STAGE3: the good events of TPV/PV/VX+ are ∃-bound in their Specs; MIX-C must take their conclusions (TPVGood etc.) as hypotheses, and bullet 'Lemma TPV at step (1)' of (a) becomes the se... |
| risk | MIXC-COVERAGE-BOOKKEEPING | `s6:thmMIXC` | The coverage proof is a disjoint-union identity over rounds, parts, ancestors and colour classes: E(G) = E_K ⊔ ⊔_{Z∈Std} E_l(Z) ⊔ ⊔_{Y light} Lentext(Y); ⊔_l LentJS_l = ⊔_Y LentJS(Y); ⊔_l LentJV_l = ⊔... |
| note | CONCL-HYPS | `s6:thmCONCL` | The statement says 'for every valid run'; the proof needs d_1 >= D_* (lemTower), Γ1(D_*) (k_* >= 6, tower facts, lemLacunary) and possibly n >= N0 through lemTower's dependence on propStructure. Put G... |
| note | CONCL-VERBATIM | `s6:thmCONCL` | The τ- and d*-terms are bounded 'verbatim' by the computation in thmCONC(iii), now over ALL ancestors. Re-derived: the τ-term uses only #ancestors of round r <= 1.37n/P_r ((K1) covers light and standa... |
| note | CONCL-GC-TERM | `s6:thmCONCL` | θGC-terms: Σ_{Y light, round r} θGC_r(Y^0) <= 1.37 n λ_r^{-1/2} + 1.37 n/P_r <= 1.38 n λ_r^{-1/2} needs P_r >= 137 λ_r^{1/2} (true: P_r >= λ_r^103, λ_r >= 2^256); 2.76(2k+3) <= 4(2k+2) for k >= 1. Che... |
| note | CONCL-SUM-RANGE | `s6:thmCONCL` | The manuscript sums over 'pairs (Y,l)' without an index set. Fix: l ∈ [1,R], Y over all ancestors of all rounds, plus a vanishing lemma m_{Y,l} = 0 unless r(Y)+2 <= l (and l >= 3). The same index conv... |
| note | CONCL-ALPHA-DOMAIN | `s6:thmCONCL` | alpha_{Y,l} is defined for light Y via max over x ∈ S_Y (0 if S_Y = ∅); (iv)'s alpha < θGC needs θGC >= 1 when S_Y = ∅ (true: /Y^0/ >= P_r > 0). The header 'l >= r+1' is harmless: for l <= r+1 there a... |
| note | LEND-LAB-DOMAIN | `s6:defLending` | lab_{Y,l}(u) exists only for r(Y)+2 <= l <= R and u ∈ V(Y); here it is evaluated at Y = Y(u) ∈ anc_l(u), which guarantees both. If Lean stores labels as a total function with default none (= *), a wro... |
| note | LEND-L2-CASE | `s6:defLending` | For l <= 2 the manuscript sets Lost_Z := ∅ separately; with anc_l = ∅ we get F_Z = U_Z, Q_Z = ∅, so the uniform definition already gives Lost = Q* = ∅ and Ret = Z^0. Define uniformly (with the `3 ≤ l`... |
| note | LEND-OZ-SPANNING | `s6:defLending` | O_Z must be a graph ON Z^0 (spanning) for TPV: build Own_Z as FGraph.ofEdges (Z0) (Own_Z), not on V(G). For lend-bad Z the switch to X^0_Z is what makes TPV applicable for EVERY ω (MIX-C takes 'any st... |
| note | LEND-XU-RANGE | `s6:defLending` | Σ_l in X_U has no stated range; use l ∈ [1,R] (Lost_l = ∅ for l <= 2). |
| note | LOST-UNION-SLACK | `s6:lemLost` | Re-derived: P(lend-bad) <= /V(Y)/^-2/2 (lemCOL: (a),(b),(e) jointly fail w.p. <= /V/^-2/2) + /Y/^-2/2 (lemE1(b), light only) <= /V(Y)/^-2; the stated 2/V(Y)/^-2 is loose. 2/V(Y)/^-2 <= 8 P_r^-2 <= 8 M... |
| note | LOST-K6-COUNT | `s6:lemLost` | (K6) needs 'at most n classed ports per round': the Q_Z ⊆ U_Z are pairwise disjoint over Z ∈ Std_l (propStructure(iv)), so Σ_{Z}/Q_Z/ <= n and /Lost_l/ = Σ_Z /Lost_Z/. For l <= 2, Lost_l = ∅. |
| note | LOST-III-ARITH | `s6:lemLost` | (iii): Σ_l (338n/M_l^2 + 2n/M_l) <= (2 + 338/2^40) n Σ_l 1/M_l <= (2+338/2^40)(2n/D_*) <= 5.5n/D_* (actual constant ~4.0000006). Needs lemTower(b) Σ_{l<=R} 1/M_l <= 2/D_* and M_l >= 2^40. Small consta... |
| note | JSLC-HUB-AGGREGATE | `s6:lemJSLC` | Parity at a hub h ∈ D_l is taken over R^0_Y summed over ALL parts containing h (one move per (h, Y)); clusters of S_0(Y,l) may span several parts. A per-part formalization would break (J1) and the eqJ... |
| note | JSLC-EQJBOUND | `s6:lemJSLC` | (eqJbound) is part of the statement but 'not used later'. It is cheap once Step 2 is formalized (~150 lines); recommend keeping it as a conjunct (no weakening). If the integrator drops it, record a T0... |
| note | JSLC-PATHCONN | `s6:lemJSLC` | Joint routing: pairs are vertices of V(Y) (ports, in V(Y) since Y = Y(u) ∈ anc_l(u)), distinct (different layers / X^out ∩ X^in = ∅), multiplicity counted over the UNION of all systems of (Y,l) at jun... |
| note | JSLC-CONST | `s6:lemJSLC` | The proof gives 15 n/M_l; the statement keeps 126 (value carried into MIX-C's 252/D_*). Spec uses 126 (as stated). Step-8 arithmetic: 0.75 + 13.7 + 0.5 + 16.44 M_l^-11 <= 15 needs M_l >= 2^40 and P_{l... |
| note | STAR-NONE | `s6:remStar` | No content. Make sure no later Spec/definition reintroduces tau'_l or HC (s1:remNotUsed lists them). |
| note | JPLUS-V-PROB | `s6:lemJplus` | (v) 'colours of distinct edges are independent' is a property of the stage-1 law, not of J_l; it is listed as an interface fact for s7:lemCand. Formalize as an iIndepFun lemma of S3.stage1Dist (s3 lay... |
| note | JPLUS-J3-III-IV | `s6:lemJplus` | (J3), (iii), (iv) do not mention J_l; they are run/designation lemmas (propStructure(iii),(iv), defDesign). Keep them out of JPlusProps to avoid proving them per call. |
| note | JPLUS-CLASS-JPAR | `s6:lemJplus` | 'The class' is defined only for centre-port J-edges; a J^par edge has two classes. The factor 1.37 in (J2) is vestigial (n(M_l-1) is already proved). |
| note | JCONS-JC3 | `s6:defJconsumer` | (JC3) is implied by (JC2) once 'union is exactly J ∪ LentJV' is IsDecomp; do not state it separately (or state it as a derived lemma). |
| note | JCONS-COLG | `s6:defJconsumer` | 'By COL(g), LJV_{Y,l} is used by nothing except the round-l J-consumer' is a property of the whole assembly; in Lean it is the disjointness step of MIX-C (LJV ⊆ Lend_Y ⊆ E(H_Y), excluded from Erem/H_0... |
| note | JCONS-NONVAC | `s6:defJconsumer` | Provide the trivial consumer as an EGTest instance (checks the structure is satisfiable; needs J ⊆ E(G), which follows from JPlusProps.inE). |
| note | ORDER-DECOUPLE | `s6:consOrder` | Simplification checked against the text: the standalone steps (1),(3),(4) of round l read only Lent(Z) = LentJS(Z) ∪ LentJV(Z) for Z ∈ Std_l (LentU(Z) = ∅ for standalone Z), E^Q(Z), J_l and stage-1 da... |
| note | ORDER-LENTU-INTERNAL | `s6:consOrder` | LentU(Y) is internal to K-RED (s5:lemKRED defines LentU(Z) := E(H_Z) ∩ ∪_{l' >= l+2, c} LentU_{l',c}); under ORDER-DECOUPLE no s6 object needs it. Do not duplicate it in s6 Lean. |
| note | ORDER-RETURNED | `s6:consOrder` | LentJS(Y) must contain only edges on OUTPUT cycles (LentJS_l = ∪ F_j of HCC-P), not the routed-but-returned edges; in Lean LentJS_l is exactly JS-LC's output set, so this is automatic. Returned and un... |
| note | LENT-LIGHT-LENDBAD | `s6:lemLent` | A light Y can be lend-bad without being demoted (COL(b) fails). Then Lentext(Y) = ∅ (no Q* port has class Y; JC1) but LentU(Y) may be non-empty (Y may be a good parent). (ii) claims emptiness only for... |
| note | LENT-OZ-LENDBAD | `s6:lemLent` | (iii) for lend-bad standalone Z uses (ii) (Lent(Z) = ∅) so Erem(Z) = E_l(Z) ⊇ E(X^0_Z) = E(O_Z); for lend-good Z it uses Lent(Z) ⊆ Lend_Z and Own_Z ∩ Lend_Z = ∅. Both re-derived. |
| note | LENT-LATE-ROUNDS | `s6:lemLent` | For r >= R-1 there are no lent classes and Lent(Y) = ∅ automatically (Finset.Icc (r+2) R = ∅). |
| note | MIXC-DETAILS-INTERNAL | `s6:thmMIXC` | (a) and the itemized parts of (b) are statements about internal objects of the construction (Lent, Erem, H_0, E^V, E^Q, J_l). Downstream (s7:propCost, s7:thmJVps) uses only 'decomposition of E(G)' and... |
| note | MIXC-HYPS | `s6:thmMIXC` | Hypotheses: GammaCond(N0, D_*) (Γ1 for lemCOL(e)/lemTower, Γ3 for /Z^0/ >= N0, Γ4 only through K-RED's cKRED slack, which K-RED does not need), N0Cond, n >= N0, d_1 >= D_*. The cost uses c_KRED = 745 ... |
| note | MIXC-EPSM | `s6:thmMIXC` | eps_M depends on D_* only (eps_K = eps_Chain of s5:lemParent, eps_A of s2:lemTower(e)); 252/D_* = 2·126/D_* uses Σ_{l<=R} 1/M_l <= 2/D_* and the stated JS-LC constant 126 (proof gives 15). |

## 4. Nodes

### `s6:thmCONCL` — theorem: Theorem CONC-L (hub concentration, light and all ancestors) (s6.tex:335)

**Status:** x2+RT (four AI passes, two with simulators). **Formalization:** Spec EG/Spec/Chain/ConcL.lean (ConcLStatement, parts (i)-(iv) as one conjunction per (Y,l,h) plus the global sum) + Defs EG.epsCONC (EG/Defs/Chain/Constants.lean) + a separate proved lemma epsCONC_tendsto; proof EG/Proof/Chain/ConcL.lean

**Statement (precise restatement).** Setting: G a finite simple graph on n vertices, a valid HB*^{tau+} run with d_1 >= D_* (implicitly Γ1(D_*) for the tower facts; see CONCL-HYPS), and a designation delta (s6:defDesign). Let Y be a LIGHT part of round r (V(Y) = Y = Y^0 \ S_Y), l a round with l >= r+1, and h ∈ V(G). Write C(h) := {u ∈ Y \ Dup*_r : hu ∈ E(G_l)}. (i) If h ∉ S_Y then |C(h)| <= tau_r - 1; and if h ∈ Y then C(h) = ∅. (ii) If h ∈ S_Y then every edge hu with u ∈ C(h) lies in E(X^0_Y), hence |C(h)| <= e_{X^0_Y}(h, Y) (edges of X^0_Y between h and Y). (iii) For every designation: m_{Y,l} <= max(tau_r - 1, alpha_{Y,l}) + d*_{Y,l}. (iv) alpha_{Y,l} < theta^GC_r(Y^0) = ceil(|Y^0| lambda_r^{-1/2}); and, for every valid run and every designation, Σ_{l=1}^{R} Σ_{Y ancestor (light or standalone, GC-parts included)} m_{Y,l} <= eps_CONC(D_*) n, where eps_CONC(D) := 2^{sigma+15} log*D / log D + 200 eps log*D / (C' log log D) + 4(2 log*D + 2)/(log D)^{1/2} (log = log_2, sigma=100, C'=103, eps=2^-5; log* x = least k >= 0 with x <= T_k, T_0=1, T_{k+1}=2^{T_k}); eps_CONC depends only on D_* and eps_CONC(D) -> 0 as D -> ∞. (m_{Y,l} = 0 unless 3 <= r(Y)+2 <= l <= R, so the double sum is finite and may be taken over l ∈ [3,R] and ancestors of rounds <= l-2.)

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), m_{Y,l}, d*_{Y,l}, alpha_{Y,l}, Bead_{Y,l}, gamma_l, giant (Y,l), c^agg_{h,l}, c_x(Z), c_pp(u)* — s6:defDesign; delta assigns to every classed port u of round l>=3 an ancestor Y(u) ∈ anc_l(u); m_{Y,l} = max_h d_{Y,l}(h); (Y,l) giant iff a component of Bead_{Y,l} has > 2 gamma_l edges, gamma_l = floor(P_{l-2}/M_l) [s6:defDesign (chunk s6a)] — EG: no: proposed EG.S6.Designation (structure: cls : ℕ → V → ℕ × List Bool, valid : ∀ l a u, 3 ≤ l → a ∈ Std l → u ∈ classed l a → cls l u ∈ anc l u) with derived m, dStar, alpha, bead, giant, cAgg, cx, cpp
- *constants and conditions: eps=2^-5, sigma=100, C'=103, A=105, N0, D*, Gamma1-Gamma4* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condG1..G4] — EG: no: proposed EG.epsC, EG.sigmaC, EG.Cp, EG.Aexp, EG.N0Cond, EG.Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1)
- *log* and the tower T_k; the functions a(d), b(d), c(d); k_* = log* D_** — log* x := min{k >= 0 : x <= T_k}; a(d)=(2log*d+2)/log d, b(d)=(2log*d+1)/log log d, c(d)=(2log*d+1)/(log d)^{1/2}; facts (s6:eqTowerHalf) a,b,c halve from round r to r+1 and (s6:eqTowerEnd) a(d) <= (2k_*+4)/log D_* etc. for d >= D_*; k_* >= 6 under Γ1(a) [s6 text before s6:thmCONC (labelled equations s6:eqTowerHalf, s6:eqTowerEnd; chunk s6a)] — EG: no: proposed EG.logStar (Found.Log), EG.S6.towA/towB/towC + lemmas towerHalf, towerEnd
- *eps_CONC(D)* — as in (iv) [s6:thmCONCL(iv)] — EG: no: proposed EG.epsCONC : ℝ → ℝ
- *e_{X}(h, W), theta^GC_r(Z^0), type (alpha)/(beta) edges* — number of X-edges between h and W; ceil(|Z^0| lambda_r^{-1/2}); ORIGIN^tau classification [s1:convGraphs, s2:defHBtp (GC), s2:propOrigin] — EG: partly: FGraph.eBetween exists (use with disjoint {h}, Y); thetaGC proposed (blueprint_s2a)

**Dependencies.** Declared: `s2:propOrigin`, `s2:lemSEP`, `s2:lemThinCut`, `s2:lemGC`, `s2:lemEL`, `s2:lemTower`, `s2:lemLacunary`, `s6:thmCONC`, `s2:propOV`, `s2:defHBtp`, `s6:defDesign`, `s1:condG1`.  
From the proof: `s2:propOrigin`, `s2:lemEL`, `s2:lemGC`, `s6:thmCONC`, `s2:propOV`, `s2:lemTower`, `s2:lemLacunary`, `s6:eqTowerHalf`, `s6:eqTowerEnd`, `s6:defDesign`, `s2:defHBtp`, `s2:defAncestors`, `s1:condG1`.  
(i)/(ii): propOrigin(a),(b) (types (alpha)/(beta); lemSEP and lemThinCut enter only through propOrigin, cited as provenance). h ∈ Y: lemEL. (iii): definition of alpha and d* + the case split. (iv): lemGC(ii) (guest cap), lemGC(iii) (GC-parts standalone), thmCONC(ii),(iii) (standalone bound and the τ/d* computations, reused 'verbatim' for all ancestors), propOV (K1) (#ancestors of round r <= 1.37n/P_r, Σ|Y^0| <= 1.37n), (K3) (d* term), lemTower(a) (R-r <= 2log*d_r+2), (c) (tau_r/P_r <= 2^{sigma+11}/lambda_r), lemLacunary(i), the labelled equations s6:eqTowerHalf/eqTowerEnd (UNDECLARED in \deps; they are equations of chunk s6a), P_r >= lambda_r^{C'} (R2), k_* >= 6 from Γ1(a). s2:lemSEP, s2:lemThinCut declared but used only via propOrigin.

**Used by:** s6:thmMIXC, s7:propCost, s7:lemGammaSat, s1:condG4 (eps_CONC in eps_1).

**Randomness.** none: deterministic statement about the run and a (deterministic) designation; holds for every designation.

**Lean shape.**

```lean
-- EG/Defs/Chain/Constants.lean
noncomputable def EG.epsCONC (D : ℝ) : ℝ :=
  2 ^ (EG.sigmaC + 15) * EG.logStar D / Real.logb 2 D
  + 200 * EG.epsC * EG.logStar D / (EG.Cp * Real.logb 2 (Real.logb 2 D))
  + 4 * (2 * EG.logStar D + 2) / Real.sqrt (Real.logb 2 D)
-- EG/Spec/Chain/ConcL.lean
def ConcLStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : FGraph V) (Dstar : ℝ) (run : HB.Run V)
    (δ : S6.Designation run G), EG.Gamma1 Dstar → EG.Gamma2a Dstar → run.Valid G Dstar → Dstar ≤ run.d G 1 →
    (∀ r a, a ∈ run.prePartAddrs G r → run.isLight G r a → ∀ l, r + 1 ≤ l → ∀ h : V,
      let Y := run.partVerts G r a; let S := run.guests G r a
      let C := (Y \ run.DupStar G r).filter (fun u => s(h, u) ∈ (run.graph G l).edges)
      (h ∉ S → C.card ≤ run.tau G r - 1 ∧ (h ∈ Y → C = ∅)) ∧
      (h ∈ S → (∀ u ∈ C, s(h, u) ∈ (run.X0 G r a).edges) ∧ C.card ≤ (run.X0 G r a).eBetween {h} Y) ∧
      δ.m (r, a) l ≤ max (run.tau G r - 1) (δ.alpha (r, a) l) + δ.dStar (r, a) l ∧
      δ.alpha (r, a) l < run.thetaGC G r a) ∧
    (∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.allAncestors G, (δ.m Y l : ℝ)) ≤ EG.epsCONC Dstar * G.card
theorem EG.epsCONC_tendsto : Filter.Tendsto EG.epsCONC Filter.atTop (nhds 0)   -- separate Spec
-- run.allAncestors G : Finset (ℕ × List Bool) := (Icc 1 R).sigma-like union of prePartAddrs r (one ancestor per pre-part)
-- tau is ℕ-valued (>= 1), so `tau - 1` is exact; alpha < thetaGC gives alpha <= thetaGC - 1 used in (iv).
```

**Hazards.**

- **CONCL-TOWER-ANALYSIS** (risk): (iv) rests on the unlabelled analysis before thmCONC (s6:eqTowerHalf, s6:eqTowerEnd; chunk s6a): monotonicity of t ↦ (2log t+6)/t, (7+2log t)/t, (2log t+5)/t^{1/2} for t >= 4, log* identities (log* x = 1 + log*(log x), log* x <= 1 + log x), Γ1 inequalities (2^14 A v^3 <= 2^v etc.). All real analysis with logb 2 and a new log* function; ~300 lines shared with thmCONC. The 'eps_CONC -> 0' claim is justified only by 'log* grows more slowly than every iterate of log' (hidden work: need log* D <= 3 + log log log D for large D, then each term -> 0).
- **CONCL-HYPS** (note): The statement says 'for every valid run'; the proof needs d_1 >= D_* (lemTower), Γ1(D_*) (k_* >= 6, tower facts, lemLacunary) and possibly n >= N0 through lemTower's dependence on propStructure. Put Gamma1, Gamma2a, d_1 >= D_* (and N0Cond/n >= N0 if lemTower's Spec takes them) as hypotheses. If d_1 < D_*, R = 0 and the sum is empty, so nothing is lost.
- **CONCL-VERBATIM** (note): The τ- and d*-terms are bounded 'verbatim' by the computation in thmCONC(iii), now over ALL ancestors. Re-derived: the τ-term uses only #ancestors of round r <= 1.37n/P_r ((K1) covers light and standalone together, not separately), the d*-term only u ∈ V(Y(u)) ⊆ Y(u)^0 and (K3); both correct. In Lean, prove the thmCONC(iii) computation as a lemma parametrized by the ancestor set so that CONC and CONC-L share it.
- **CONCL-GC-TERM** (note): θGC-terms: Σ_{Y light, round r} θGC_r(Y^0) <= 1.37 n λ_r^{-1/2} + 1.37 n/P_r <= 1.38 n λ_r^{-1/2} needs P_r >= 137 λ_r^{1/2} (true: P_r >= λ_r^103, λ_r >= 2^256); 2.76(2k+3) <= 4(2k+2) for k >= 1. Checked.
- **CONCL-SUM-RANGE** (note): The manuscript sums over 'pairs (Y,l)' without an index set. Fix: l ∈ [1,R], Y over all ancestors of all rounds, plus a vanishing lemma m_{Y,l} = 0 unless r(Y)+2 <= l (and l >= 3). The same index convention must be used in s6:lemJSLC's giant sum and s6:thmMIXC(c).
- **CONCL-ALPHA-DOMAIN** (note): alpha_{Y,l} is defined for light Y via max over x ∈ S_Y (0 if S_Y = ∅); (iv)'s alpha < θGC needs θGC >= 1 when S_Y = ∅ (true: |Y^0| >= P_r > 0). The header 'l >= r+1' is harmless: for l <= r+1 there are no classed ports of class Y.

**Effort.** ~650 lines, difficulty 3/5. (i)-(ii) ~120 given propOrigin/lemEL/lemGC Specs; (iii) ~120 (edge counting via the injective edge ↦ other end); (iv) sums ~250 (shared helper with thmCONC); tendsto ~150. Excludes the shared tower lemmas of chunk s6a.

### `s6:defLending` — definition: stage-2 lending statuses, retirement sets and the functional X_U (s6.tex:390)

**Status:** x2. **Formalization:** Defs EG/Defs/Chain/Lending.lean (lendBad, lost, ret, qs, OZ, lostRound, XU) + API lemmas (partition Z^0 = Ret ⊔ Q*, disjointness, u ∈ Q* ⇒ class lend-good and u ∉ ⋃_j T_j) in EG/Lib/Chain/Lending.lean; no Spec

**Statement (precise restatement).** Fix a valid run, a designation delta and a stage-1 outcome ω (colourings and JS labels of s3:defCOL, zones of s5:defZones). (1) An ancestor Y is LEND-BAD iff (Y is a light part that is demoted in the sense of s5:defStages) or (some COL(a) event of s3:lemCOL fails for Y) or (some COL(b) event fails for Y); otherwise LEND-GOOD. Consequently for lend-good Y: Own_Y, Lend_Y are (eps_Y, s_Y/4)-expanders on V(Y), every lent class is an (eps_Y, s_Y/(8k_lend(Y)))-expander on V(Y), and every LJS_{Y,l,j} is (2^12 L_Y^4, t^JS_l)-path connected through T_j(Y,l) (r+2 <= l <= R, j < K^JS_l). (2) For l >= 3 and Z ∈ Std_l: Lost_Z := {u ∈ Q_Z : Y(u) lend-bad or lab_{Y(u),l}(u) != *}; Ret_Z := A_Z ∪ F_Z ∪ Lost_Z; Q*_Z := Q_Z \ Lost_Z. For l <= 2: Lost_Z := ∅, Ret_Z := A_Z ∪ F_Z (= Z^0), Q*_Z := ∅. Facts: Z^0 = Ret_Z ⊔ Q*_Z; A_Z, F_Z, Lost_Z pairwise disjoint. (3) O_Z := Own_Z (as a graph on Z^0) if the standalone ancestor Z is lend-good, O_Z := X^0_Z otherwise. (4) Lost_l := ∪_{Z ∈ Std_l} Lost_Z. (5) X_U := 80 dem + 369 lp + Σ_{l=1}^{R} (169 + M_l)|Lost_l| (dem, lp from s5:defStages). All are deterministic functions of (run, delta, ω). Fact: for every u ∈ Q*_Z (l >= 3), Y(u) is lend-good and u ∉ ∪_j T_j(Y(u), l).

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), m_{Y,l}, d*_{Y,l}, alpha_{Y,l}, Bead_{Y,l}, gamma_l, giant (Y,l), c^agg_{h,l}, c_x(Z), c_pp(u)* — s6:defDesign; delta assigns to every classed port u of round l>=3 an ancestor Y(u) ∈ anc_l(u); m_{Y,l} = max_h d_{Y,l}(h); (Y,l) giant iff a component of Bead_{Y,l} has > 2 gamma_l edges, gamma_l = floor(P_{l-2}/M_l) [s6:defDesign (chunk s6a)] — EG: no: proposed EG.S6.Designation (structure: cls : ℕ → V → ℕ × List Bool, valid : ∀ l a u, 3 ≤ l → a ∈ Std l → u ∈ classed l a → cls l u ∈ anc l u) with derived m, dStar, alpha, bead, giant, cAgg, cx, cpp
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)
- *COL(a) and COL(b) events of an ancestor Y (as predicates on ω)* — COLa: Own_Y, Lend_Y are (eps_Y, s_Y/4)-expanders on V(Y); every lent class is an (eps_Y, s_Y/(8 k_lend(Y)))-expander on V(Y); if Y light every own class is a (2^-6, s_r/(16 k_own))-expander on V(Y). COLb: ∀ l ∈ [r+2,R], ∀ j < K^JS_l, LJS_{Y,l,j} (graph on V(Y)) is (2^12 L_Y^4, t^JS_l)-path connected through T_j(Y,l) [s3:lemCOL(a),(b)] — EG: partly: FGraph.IsExpander, FGraph.IsPathConnected exist; the event predicates EG.S3.COLaEvent/COLbEvent are proposed (s3 layer)
- *demoted, parent-bad, Bad, good parent, dem, lp (stage-2 statuses of light parts)* — s5:defStages: Y demoted iff (E1) fails or a COL(a) event fails (light parameters); dem = Σ_{Y demoted}|Y|; lp = Σ_{Y ∈ Bad}|Y|(R-r(Y)) [s5:defStages] — EG: no: proposed EG.S5.demoted, EG.S5.Bad, EG.S5.dem, EG.S5.lp (s5 layer)
- *K^JS_l := M_l^2, rho_l := M_l^-4, t^JS_l := 2M_l+2* — number of JS junction classes, JS label density, JS multiplicity [s3:defCOL(ii),(iv), Derived quantities] — EG: no: proposed EG.S3.KJS l : ℕ (needs M_l ∈ ℕ, blocker HB-M-INTEGER), EG.S3.rhoJS, EG.S3.tJS

**Dependencies.** Declared: `s3:defCOL`, `s3:lemCOL`, `s5:defStages`, `s6:defDesign`, `s5:defZones`.  
From the proof: `s3:defCOL`, `s3:lemCOL`, `s5:defStages`, `s5:defZones`, `s6:defDesign`, `s2:defAncestors`, `s2:defHBtp`, `s4:lemTPV`.  
A definition; 'deps_from_proof' = what its text needs. s3:lemCOL is used only to NAME the events (a),(b) (their failure defines lend-bad), not its probability bound. s2:defAncestors (A_Z, U_Z, F_Z, Q_Z) and s2:defHBtp (D_l, Std_l) are undeclared but used. s4:lemTPV is referenced in the text only to name Ret_Z as TPV's retirement set (undeclared, harmless). s6:defDesign supplies Y(u).

**Used by:** s6:lemLost, s6:lemJSLC, s6:lemJplus, s6:consOrder, s6:lemLent, s6:thmMIXC, s7:defSchedule, s7:consRound, s7:defXprime, s7:lemEXprime.

**Randomness.** Definition only: every object is a deterministic function of the stage-1 outcome ω ∈ Stage1 (families 1a-1c; 1d unused). The law of ω is used later (s6:lemLost).

**Lean shape.**

```lean
-- EG/Defs/Chain/Lending.lean   (namespace EG.S6; ctx: G, run, δ; ω : S3.Stage1 run G)
def lendBad (ω) (Y : ℕ × List Bool) : Prop :=
  (run.isLight G Y.1 Y.2 ∧ S5.demoted ω Y) ∨ ¬ S3.COLaEvent ω Y ∨ ¬ S3.COLbEvent ω Y
def lost (ω) (l : ℕ) (a : List Bool) : Finset V :=
  if 3 ≤ l then (run.classed G l a).filter (fun u => lendBad ω (δ.cls l u) ∨ ω.lab (δ.cls l u) l u ≠ none) else ∅
def ret ω l a : Finset V := run.hubs G l a ∪ run.fresh G l a ∪ lost ω l a
def qs ω l a : Finset V := run.classed G l a \ lost ω l a           -- = ∅ for l ≤ 2 (classed = ∅)
def OZ ω l a : FGraph V := if lendBad ω (l, a) then run.X0 G l a else FGraph.ofEdges (run.Z0 G l a) (ω.own (l, a))
def lostRound ω l : Finset V := (run.Std G l).biUnion (lost ω l)
noncomputable def XU ω : ℝ := 80 * S5.dem ω + 369 * S5.lp ω
  + ∑ l ∈ Finset.Icc 1 run.R, (169 + (run.M G l : ℝ)) * (lostRound ω l).card
-- API (EG/Lib/Chain/Lending.lean): Z0 = ret ∪ qs, Disjoint (ret) (qs); pairwise Disjoint hubs fresh lost;
--   u ∈ qs ω l a → ¬ lendBad ω (δ.cls l u) ∧ ω.lab (δ.cls l u) l u = none;  ω.lab returns Option (Fin (KJS l)), none = '*'
```

**Hazards.**

- **M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a)** (blocker): K^JS_l := M_l^2 is used as the NUMBER of JS classes / label values (0 <= j < K^JS_l) and K^JS_l * rho_l = M_l^-2 is used as an exact probability; M_l of (R2) is a real. This chunk also uses 'M_l - 1 cherry systems', pad <= ceil(M_l/2), t^JS_l = 2M_l+2 and k_0 := min(K^JS_l, ...). Needs the manuscript decision proposed in blueprint_s2a (M_l := ceil(...) ∈ ℕ). Checked for this chunk: every inequality of s6:lemLost, s6:lemJSLC, s6:thmMIXC survives with integer M_l (all only use M_l >= 2^40, P_{l-2} >= M_l^13, Σ1/M_l <= 2/D*). Fallback without manuscript change: K^JS_l := ceil(M_l^2), and s6:lemLost(i) becomes P(lab != *) = ceil(M_l^2) M_l^-4 <= M_l^-2 + M_l^-4 (the final '<= 2M_l^-2' still holds since 8M_l^-26 + M_l^-4 <= M_l^-2).
- **LEND-COL-EVENTS** (risk): 'An event of Lemma COL(a)/(b) fails' refers to the conclusion events of a probabilistic lemma. Lean needs named predicates COLaEvent/COLbEvent in the s3 Defs with exactly these parameters: (eps_Y, s_Y/4) for Own/Lend; (eps_Y, s_Y/(8 k_lend)) for lent classes (k_lend = 0 when r >= R-1: no classes, real division by 0 must not matter); own classes (2^-6, s_r/(16k_own)) for light Y; path connectivity (2^12 L_Y^4, t^JS_l) through T_j(Y,l) for all r+2 <= l <= R, j < K^JS_l, graphs with vertex set V(Y). Must be identical to the events whose probability s3:lemCOL bounds and to the COL(a) part of 'demoted' in s5:defStages (checked: (2^-6, s_r/8) = (eps_Y, s_Y/4) and s_r/(16k_lend) = s_Y/(8k_lend) for light Y). Coordinate with the s3/s5 blueprints.
- **LEND-LAB-DOMAIN** (note): lab_{Y,l}(u) exists only for r(Y)+2 <= l <= R and u ∈ V(Y); here it is evaluated at Y = Y(u) ∈ anc_l(u), which guarantees both. If Lean stores labels as a total function with default none (= *), a wrong index would silently make a port non-lost; state the API lemma 'lab is only read on its domain' or use a dependent index type.
- **LEND-L2-CASE** (note): For l <= 2 the manuscript sets Lost_Z := ∅ separately; with anc_l = ∅ we get F_Z = U_Z, Q_Z = ∅, so the uniform definition already gives Lost = Q* = ∅ and Ret = Z^0. Define uniformly (with the `3 ≤ l` guard only in `lost`) and prove the l <= 2 values.
- **LEND-OZ-SPANNING** (note): O_Z must be a graph ON Z^0 (spanning) for TPV: build Own_Z as FGraph.ofEdges (Z0) (Own_Z), not on V(G). For lend-bad Z the switch to X^0_Z is what makes TPV applicable for EVERY ω (MIX-C takes 'any stage-1 outcome').
- **LEND-XU-RANGE** (note): Σ_l in X_U has no stated range; use l ∈ [1,R] (Lost_l = ∅ for l <= 2).

**Effort.** ~220 lines, difficulty 2/5. Definitions ~60, API lemmas ~160 (partition, disjointness, lend-good facts). Depends on the s3 Stage1 type and s5 statuses being fixed first.

### `s6:lemLost` — lemma: lost ports; the constant (K6) (s6.tex:409)

**Status:** x2+RT. **Formalization:** Spec EG/Spec/Chain/Lost.lean (LostStatement: (i) chain of three inequalities per classed port, (K6), (iii)); proof EG/Proof/Chain/Lost.lean

**Statement (precise restatement).** Setting (implicit, see LOST-HYPS): n >= N0, d_1 >= D_*, Γ1-Γ3 for D_*, a valid run, a designation delta. Probabilities/expectations are over the stage-1 outcome ω ~ stage1Dist (families 1a-1d, independent). (i) For every round 3 <= l <= R, every Z ∈ Std_l and every classed port u ∈ Q_Z, with Y := Y(u) (a fixed ancestor of round r <= l-2): P(u ∈ Lost_Z) <= K^JS_l rho_l + P(Y lend-bad), P(Y lend-bad) <= 2|V(Y)|^{-2}, K^JS_l rho_l = M_l^{-2}, 2|V(Y)|^{-2} <= M_l^{-2}; hence P(u ∈ Lost_Z) <= 2 M_l^{-2}. (K6) For every round l: E|Lost_l| <= 2n / M_l^2. (iii) E X_U <= eps_U(D_*) n + Σ_{l=1}^{R} 2n(169 + M_l)/M_l^2 <= eps_U(D_*) n + 5.5 n / D_*, with eps_U(D) = 2462 (log D)^{-205} (s5:lemExpect).

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), m_{Y,l}, d*_{Y,l}, alpha_{Y,l}, Bead_{Y,l}, gamma_l, giant (Y,l), c^agg_{h,l}, c_x(Z), c_pp(u)* — s6:defDesign; delta assigns to every classed port u of round l>=3 an ancestor Y(u) ∈ anc_l(u); m_{Y,l} = max_h d_{Y,l}(h); (Y,l) giant iff a component of Bead_{Y,l} has > 2 gamma_l edges, gamma_l = floor(P_{l-2}/M_l) [s6:defDesign (chunk s6a)] — EG: no: proposed EG.S6.Designation (structure: cls : ℕ → V → ℕ × List Bool, valid : ∀ l a u, 3 ≤ l → a ∈ Std l → u ∈ classed l a → cls l u ∈ anc l u) with derived m, dStar, alpha, bead, giant, cAgg, cx, cpp
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)
- *COL(a) and COL(b) events of an ancestor Y (as predicates on ω)* — COLa: Own_Y, Lend_Y are (eps_Y, s_Y/4)-expanders on V(Y); every lent class is an (eps_Y, s_Y/(8 k_lend(Y)))-expander on V(Y); if Y light every own class is a (2^-6, s_r/(16 k_own))-expander on V(Y). COLb: ∀ l ∈ [r+2,R], ∀ j < K^JS_l, LJS_{Y,l,j} (graph on V(Y)) is (2^12 L_Y^4, t^JS_l)-path connected through T_j(Y,l) [s3:lemCOL(a),(b)] — EG: partly: FGraph.IsExpander, FGraph.IsPathConnected exist; the event predicates EG.S3.COLaEvent/COLbEvent are proposed (s3 layer)
- *demoted, parent-bad, Bad, good parent, dem, lp (stage-2 statuses of light parts)* — s5:defStages: Y demoted iff (E1) fails or a COL(a) event fails (light parameters); dem = Σ_{Y demoted}|Y|; lp = Σ_{Y ∈ Bad}|Y|(R-r(Y)) [s5:defStages] — EG: no: proposed EG.S5.demoted, EG.S5.Bad, EG.S5.dem, EG.S5.lp (s5 layer)
- *lendBad, Lost_Z, Ret_Z, Q*_Z (qs), O_Z, Lost_l, X_U* — s6:defLending (this chunk) [s6:defLending] — EG: no: proposed EG.S6.lendBad/lost/ret/qs/OZ/lostRound/XU (EG/Defs/Chain/Lending.lean)
- *K^JS_l := M_l^2, rho_l := M_l^-4, t^JS_l := 2M_l+2* — number of JS junction classes, JS label density, JS multiplicity [s3:defCOL(ii),(iv), Derived quantities] — EG: no: proposed EG.S3.KJS l : ℕ (needs M_l ∈ ℕ, blocker HB-M-INTEGER), EG.S3.rhoJS, EG.S3.tJS
- *constants and conditions: eps=2^-5, sigma=100, C'=103, A=105, N0, D*, Gamma1-Gamma4* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condG1..G4] — EG: no: proposed EG.epsC, EG.sigmaC, EG.Cp, EG.Aexp, EG.N0Cond, EG.Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1)
- *FinDist prob / expect* — real-weighted finite distribution; prob of a Set, expectation of a real function [PLAN §3 decision 3] — EG: yes: EG.FinDist.prob, EG.FinDist.expect (EG/Defs/Prob/FinDist.lean); linearity/union bound in EG.Lib.Prob.*
- *eps_U(D)* — 2462 (log_2 D)^{-205} [s5:lemExpect] — EG: no: proposed EG.epsU (s5 layer)

**Dependencies.** Declared: `s6:defLending`, `s3:lemCOL`, `s5:lemE1`, `s5:lemExpect`, `s2:propStructure`, `s2:lemTower`, `s3:defCOL`.  
From the proof: `s6:defLending`, `s3:defCOL`, `s3:lemCOL`, `s5:lemE1`, `s5:lemExpect`, `s2:propStructure`, `s2:lemTower`, `s2:defHBtp`, `s2:defAncestors`, `s1:condG1`.  
(i): label law s3:defCOL(iv) (P(lab != *) = K rho); lemCOL (P((a) or (b) fails) <= |V(Y)|^-2/2); lemE1(b) (P(demoted) <= |Y|^-2/2); propStructure(iv) (|V(Y)| >= P_r/2 for light Y; |Y^0| >= P_r for standalone by (R3)); lemTower(b) (P_r >= 2P_{r+1}, P_{l-2} >= M_l^13). (K6): propStructure(iv) (port sets U_Z of one round disjoint ⇒ <= n classed ports) + linearity. (iii): lemExpect, (R2) M_l >= 2^40, lemTower(b) Σ1/M_l <= 2/D_*. Γ1 is needed by lemCOL/lemE1/lemExpect (undeclared). s2:defAncestors for V(Y).

**Used by:** s7:lemEXprime, s7:propCost (through X_U), s1:condG4 (through eps_X).

**Randomness.** Sample space: the full stage-1 space Stage1(run, G) = product of (1a) per ancestor Y and per edge e ∈ E(H_Y): (fair bit, uniform lent index on I_U ⊔ I_JS ⊔ I_JV when r(Y) <= R-2, uniform own label on [k_own] for light Y); (1b) per vertex v: choice(v) with P(choice = Y) = L_Y^-2 over light Y ∋ v with r(Y) <= R-2, remaining mass on none, and a uniform sublabel on I_U(Y); (1c) per (Y, l ∈ [r(Y)+2, R], y ∈ V(Y)): lab ∈ {*} ∪ [0, K^JS_l) with P(j) = M_l^-4; (1d) pool labels (unused here). Nothing is conditioned on: run and delta are fixed (deterministic). The events used are functions of coordinates of one ancestor Y (COL(a),(b), labels of Y) and of zones (E1 inside demotion): the proof needs marginal/pushforward lemmas so that lemCOL and lemE1, stated on their own sub-spaces, transfer to the joint space.

**Lean shape.**

```lean
-- EG/Spec/Chain/Lost.lean
def LostStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : HB.Run V) (δ : S6.Designation run G),
    EG.N0Cond N0 → EG.GammaCond N0 Dstar → run.Valid G Dstar → N0 ≤ G.card → Dstar ≤ run.d G 1 →
    let μ := S3.stage1Dist run G
    (∀ l a u, 3 ≤ l → l ≤ run.R → a ∈ run.Std G l → u ∈ run.classed G l a →
       let Y := δ.cls l u
       μ.prob {ω | u ∈ S6.lost ω l a} ≤ (S3.KJS run G l : ℝ) * S3.rhoJS run G l + μ.prob {ω | S6.lendBad ω Y} ∧
       μ.prob {ω | S6.lendBad ω Y} ≤ 2 * ((run.ancVerts G Y.1 Y.2).card : ℝ) ^ (-2 : ℤ) ∧
       (S3.KJS run G l : ℝ) * S3.rhoJS run G l = (run.M G l : ℝ) ^ (-2 : ℤ) ∧
       2 * ((run.ancVerts G Y.1 Y.2).card : ℝ) ^ (-2 : ℤ) ≤ (run.M G l : ℝ) ^ (-2 : ℤ) ∧
       μ.prob {ω | u ∈ S6.lost ω l a} ≤ 2 * (run.M G l : ℝ) ^ (-2 : ℤ)) ∧
    (∀ l, μ.expect (fun ω => ((S6.lostRound ω l).card : ℝ)) ≤ 2 * G.card / (run.M G l : ℝ) ^ 2) ∧
    μ.expect S6.XU ≤ EG.epsU Dstar * G.card
        + ∑ l ∈ Finset.Icc 1 run.R, 2 * G.card * (169 + (run.M G l : ℝ)) / (run.M G l : ℝ) ^ 2 ∧
    μ.expect S6.XU ≤ EG.epsU Dstar * G.card + 5.5 * G.card / Dstar
-- (the 3rd conjunct of (i) becomes '≤ M^-2 + M^-4' under the ceiling fallback of M-INTEGER)
```

**Hazards.**

- **M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a)** (blocker): K^JS_l := M_l^2 is used as the NUMBER of JS classes / label values (0 <= j < K^JS_l) and K^JS_l * rho_l = M_l^-2 is used as an exact probability; M_l of (R2) is a real. This chunk also uses 'M_l - 1 cherry systems', pad <= ceil(M_l/2), t^JS_l = 2M_l+2 and k_0 := min(K^JS_l, ...). Needs the manuscript decision proposed in blueprint_s2a (M_l := ceil(...) ∈ ℕ). Checked for this chunk: every inequality of s6:lemLost, s6:lemJSLC, s6:thmMIXC survives with integer M_l (all only use M_l >= 2^40, P_{l-2} >= M_l^13, Σ1/M_l <= 2/D*). Fallback without manuscript change: K^JS_l := ceil(M_l^2), and s6:lemLost(i) becomes P(lab != *) = ceil(M_l^2) M_l^-4 <= M_l^-2 + M_l^-4 (the final '<= 2M_l^-2' still holds since 8M_l^-26 + M_l^-4 <= M_l^-2).
- **LOST-HYPS** (risk): 'Fix a valid run and a designation' hides: Γ1 (lemCOL, lemE1, lemExpect all assume it), n >= N0 and d_1 >= D_* (propStructure(iv), lemTower(b)), and 3 <= l <= R for (i). Without Γ1 the probability bounds of lemCOL are not available and the statement may fail. The Spec must carry the s5 setting (N0Cond, GammaCond, n >= N0, d_1 >= D_*).
- **LOST-SPACE-MARGINALS** (risk): The events 'Y lend-bad' combine COL(a),(b) (coordinates 1a,1c of Y) and demotion (which contains (E1), depending on 1a of Y and on the zones 1b of ALL vertices of Y). s3:lemCOL is stated 'over the stage-1 lending data of Y' and s5:lemE1 'over the stage-1 randomness'. In Lean both Specs must be stated on (or transported to) the single joint FinDist stage1Dist via map/pi-marginal lemmas; otherwise the union bound cannot be formed. Decide the Stage1 type (a dependent pi over ancestors/edges/vertices) before the s3/s5 Specs are locked.
- **LOST-UNION-SLACK** (note): Re-derived: P(lend-bad) <= |V(Y)|^-2/2 (lemCOL: (a),(b),(e) jointly fail w.p. <= |V|^-2/2) + |Y|^-2/2 (lemE1(b), light only) <= |V(Y)|^-2; the stated 2|V(Y)|^-2 is loose. 2|V(Y)|^-2 <= 8 P_r^-2 <= 8 M_l^-26 <= M_l^-2 uses |V(Y)| >= P_r/2, P_r >= P_{l-2} >= M_l^13, M_l >= 2^40. OK.
- **LOST-K6-COUNT** (note): (K6) needs 'at most n classed ports per round': the Q_Z ⊆ U_Z are pairwise disjoint over Z ∈ Std_l (propStructure(iv)), so Σ_{Z}|Q_Z| <= n and |Lost_l| = Σ_Z |Lost_Z|. For l <= 2, Lost_l = ∅.
- **LOST-III-ARITH** (note): (iii): Σ_l (338n/M_l^2 + 2n/M_l) <= (2 + 338/2^40) n Σ_l 1/M_l <= (2+338/2^40)(2n/D_*) <= 5.5n/D_* (actual constant ~4.0000006). Needs lemTower(b) Σ_{l<=R} 1/M_l <= 2/D_* and M_l >= 2^40. Small constants: norm_num.

**Effort.** ~380 lines, difficulty 3/5. (i) ~150 (union bound, label marginal = M^-2, size chain); (K6) ~60 (linearity over the classed ports, disjoint union); (iii) ~90; marginal/transport lemmas ~80 (may be shared with s5:lemExpect/s7:lemEXprime).

### `s6:lemJSLC` — lemma: Lemma JS-LC (one round l >= 3; cherry split for giant pairs) (s6.tex:443)

**Status:** x2+RT (hypotheses, multiplicities); +RA. **Formalization:** Spec EG/Spec/Chain/JSLC.lean: ONE existential statement JSLCStatement that also carries the J+ interface (s6:lemJplus) as conjuncts (structure JPlusProps in EG/Defs/Chain/JSet.lean). Proof split over EG/Proof/Chain/JSLC/{Types, Parity, Components, SystemS0, Cherry, Routing, Assemble, Count}.lean

**Statement (precise restatement).** Setting: n >= N0, d_1 >= D_*, Γ1-Γ3, a valid run, delta, a stage-1 outcome ω with its stage-2 data (s6:defLending), a round 3 <= l <= R. Input: for every Z ∈ Std_l a set B_Z ⊆ E_l(Z) such that every edge of B_Z has an end in Q*_Z. (Manuscript hypothesis 'no edge of any class LJS_{Y,l,j} (j < K^JS_l, Y lend-good of round <= l-2) has been used': in Lean ALL edges of these classes are available; see JSLC-USED.) Conclusion: there exist J_l ⊆ ∪_Z B_Z, LentJS_l ⊆ ∪ {LJS_{Y,l,j} : Y lend-good ancestor, r(Y) <= l-2, 0 <= j < K^JS_l}, and a family D of cycles of G such that (1) D decomposes (∪_Z B_Z \ J_l) ∪ LentJS_l (so ∪B_Z ∪ LentJS_l is partitioned into the single edges of J_l and the cycles of D; ∪B_Z and LentJS_l are disjoint); (2) |D| <= 126 n/M_l + Σ_{(Y,l) giant} sc_{Y,l} with sc_{Y,l} = (3g_{Y,l} - 6M_l)^+ <= 1.5 m_{Y,l} (g_{Y,l} = number of cherry classes, defined in Step 5 of the proof; Lean form: |D| <= 126 n/M_l + 1.5 Σ_{Y: (Y,l) giant} m_{Y,l}); the proof gives 15 in place of 126; (3) each cycle of D consists of edges of ∪_Z B_Z and of ∪_j LJS_{Y,l,j} for a single ancestor Y; (4) (eqJbound) |J_l| <= Σ_{h ∈ D_l} c^agg_{h,l} + Σ_{Z ∈ Std_l} [Σ_{x ∈ F_Z} c_x(Z) + (M_l - 1)|Lost_Z| + (1/2) Σ_{u ∈ Q_Z} c_pp(u)] (computed from the E_l(Z); not used later); (5) [s6:lemJplus] J_l has the interface properties J1, J2, types (i) and (ii) (merged here, see JSLC-JPLUS-MERGE). Edges of the classes LJS outside LentJS_l (including returned edges inside G[T_j(Y,l)]) are not used (junk for the owner).

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), m_{Y,l}, d*_{Y,l}, alpha_{Y,l}, Bead_{Y,l}, gamma_l, giant (Y,l), c^agg_{h,l}, c_x(Z), c_pp(u)* — s6:defDesign; delta assigns to every classed port u of round l>=3 an ancestor Y(u) ∈ anc_l(u); m_{Y,l} = max_h d_{Y,l}(h); (Y,l) giant iff a component of Bead_{Y,l} has > 2 gamma_l edges, gamma_l = floor(P_{l-2}/M_l) [s6:defDesign (chunk s6a)] — EG: no: proposed EG.S6.Designation (structure: cls : ℕ → V → ℕ × List Bool, valid : ∀ l a u, 3 ≤ l → a ∈ Std l → u ∈ classed l a → cls l u ∈ anc l u) with derived m, dStar, alpha, bead, giant, cAgg, cx, cpp
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)
- *COL(a) and COL(b) events of an ancestor Y (as predicates on ω)* — COLa: Own_Y, Lend_Y are (eps_Y, s_Y/4)-expanders on V(Y); every lent class is an (eps_Y, s_Y/(8 k_lend(Y)))-expander on V(Y); if Y light every own class is a (2^-6, s_r/(16 k_own))-expander on V(Y). COLb: ∀ l ∈ [r+2,R], ∀ j < K^JS_l, LJS_{Y,l,j} (graph on V(Y)) is (2^12 L_Y^4, t^JS_l)-path connected through T_j(Y,l) [s3:lemCOL(a),(b)] — EG: partly: FGraph.IsExpander, FGraph.IsPathConnected exist; the event predicates EG.S3.COLaEvent/COLbEvent are proposed (s3 layer)
- *lendBad, Lost_Z, Ret_Z, Q*_Z (qs), O_Z, Lost_l, X_U* — s6:defLending (this chunk) [s6:defLending] — EG: no: proposed EG.S6.lendBad/lost/ret/qs/OZ/lostRound/XU (EG/Defs/Chain/Lending.lean)
- *K^JS_l := M_l^2, rho_l := M_l^-4, t^JS_l := 2M_l+2* — number of JS junction classes, JS label density, JS multiplicity [s3:defCOL(ii),(iv), Derived quantities] — EG: no: proposed EG.S3.KJS l : ℕ (needs M_l ∈ ℕ, blocker HB-M-INTEGER), EG.S3.rhoJS, EG.S3.tJS
- *objects, decomposition* — Obj = edge | cycle (list); IsDecomp E D: WF objects, edge lists pairwise disjoint, union exactly E [s1:defObject] — EG: yes: EG.Obj, EG.Obj.WF, EG.Obj.edges, EG.IsDecomp (EG/Defs/Objects.lean)
- *(eps,s)-expander; (l,t)-path connected through W* — Def 11 / Def 7 of B-M (multiset form) [s1:citDef11, s1:citDef7, s3:remMultiset] — EG: yes: EG.FGraph.IsExpander, EG.FGraph.IsPathConnected (+ Lib IsPathConnected.exists_paths, exists_paths_sigma for joint routing)
- *constants and conditions: eps=2^-5, sigma=100, C'=103, A=105, N0, D*, Gamma1-Gamma4* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condG1..G4] — EG: no: proposed EG.epsC, EG.sigmaC, EG.Cp, EG.Aexp, EG.N0Cond, EG.Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1)
- *clusters, admissible orientation, MED, loads, EQ-LPT layering, HCC-P systems (layers, junction sets, padding, demands, path families), union of systems* — s6:defCluster, s6:lemMED, s6:lemEQLPT, s6:lemHCCP, s6:lemHCCglob [s6 routing engine (chunk s6a)] — EG: partly: EG.IsOrientation, outDeg/inDeg, IsAcyclic, IsDirCycle (EG/Defs/Orient.lean), Gate Spec exists (EG/Spec/Chain/Gate.lean); Cluster/HCC-P structures proposed by chunk s6a
- *PAR split of a bipartite edge set* — s6:lemPAR: one edge per odd component removed (J'), rest split S_a ⊔ S_b with parity conditions [s6:lemPAR (chunk s6a)] — EG: no (s6a Spec)
- *JPlusProps ctx ω l J (the J-interface)* — see s6:lemJplus [s6:lemJplus] — EG: no: proposed EG.S6.JPlusProps (EG/Defs/Chain/JSet.lean)
- *internal objects of the proof (not in the Spec)* — centre-port / port-port edges, E_ab(Z), R^0_Y, R_Y (realized class-Y beads), pseudo-hubs, S_0(Y,l), cherries, conflict colouring classes S_i(Y,l), g_{Y,l}, junction-j pair multisets 𝔓_j(Y,l) [proof Steps 1-7] — EG: no: proof-local

**Dependencies.** Declared: `s6:lemPAR`, `s6:lemMED`, `s6:lemEQLPT`, `s6:lemHCCP`, `s6:lemHCCglob`, `s6:defDesign`, `s6:defLending`, `s3:lemCOL`, `s3:lemMonotone`, `s2:lemEL`, `s2:lemCap`, `s2:propOV`, `s2:lemTower`, `s2:defHBtp`, `s2:propStructure`, `s3:defCOL`, `s1:citDef7`.  
From the proof: `s6:lemPAR`, `s6:defCluster`, `s6:lemMED`, `s6:lemEQLPT`, `s6:lemHCCP`, `s6:lemHCCglob`, `s6:defDesign`, `s6:defLending`, `s3:defCOL`, `s3:lemCOL`, `s3:lemMonotone`, `s3:remMultiset`, `s1:citDef7`, `s2:lemEL`, `s2:lemCap`, `s2:lemTower`, `s2:defHBtp`, `s2:propStructure`, `s2:defAncestors`, `s1:defObject`, `s1:factAdd`.  
Step 1: (R5) E_l(Z) ⊆ E(G[Z^0]); lemEL (Y(v) != Y(u), centres outside V(Y)). Step 2: lemPAR; lemCap(ii) (degree <= M_l-1 in E_l(Z)); propStructure(iv) (vertex outside D_l in one pre-part). Step 3: defDesign (Bead, gamma, giant, m). Step 4: defCluster (UNDECLARED), lemMED, lemEQLPT. Step 5: greedy colouring (no citation; must be proved). Step 6: lemCOL(b) via lend-good (defLending), citDef7 + remMultiset (UNDECLARED) + lemMonotone(iii) (joint routing of a union multiset). Step 7: lemHCCP, lemHCCglob, defCOL (T_j disjoint, LJS ⊆ Lend_Y ⊆ E(H_Y)), propStructure(iii) (E(H_Y) ⊆ E_r(Y) disjoint from E_l(Z)). Step 8: lemTower(b) (nu_l <= 2.74n/P_{l-2}, P_{l-2} >= M_l^13; this is the completion of (K1), so s2:propOV is only indirect). Forward mentions of s6:lemJplus and s6:thmMIXC in the statement's commentary are not logical dependencies. s4:lemTPV in the statement is commentary (B_Z := E^Q(Z) in the assembly).

**Used by:** s6:remStar, s6:lemJplus, s6:consOrder, s6:lemLent, s6:thmMIXC.

**Randomness.** none inside the lemma: deterministic for EVERY stage-1 outcome ω (the path-connectivity it uses is the lend-good property of ω, a deterministic predicate). The adaptivity point (pairs chosen after ω, s3:lemMonotone(iii)) is automatic in Lean: IsPathConnected quantifies over all index families.

**Lean shape.**

```lean
-- EG/Spec/Chain/JSLC.lean
def lendGoodAnc (ω) (l : ℕ) : Finset (ℕ × List Bool) := (run.allAncestors G).filter (fun Y => Y.1 + 2 ≤ l ∧ ¬ S6.lendBad ω Y)
def lentJSClasses ω l : Finset (Sym2 V) := (lendGoodAnc ω l).biUnion (fun Y => (Finset.range (S3.KJS run G l)).biUnion (ω.LJS Y l))
def JSLCStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : HB.Run V) (δ : S6.Designation run G)
    (ω : S3.Stage1 run G) (l : ℕ) (B : List Bool → Finset (Sym2 V)),
    EG.N0Cond N0 → EG.GammaCond N0 Dstar → run.Valid G Dstar → N0 ≤ G.card → Dstar ≤ run.d G 1 →
    3 ≤ l → l ≤ run.R →
    (∀ a ∈ run.Std G l, B a ⊆ run.E G l a ∧ ∀ e ∈ B a, ∃ u ∈ S6.qs ω l a, u ∈ e) →
    let BU := (run.Std G l).biUnion B
    ∃ (J LentJS : Finset (Sym2 V)) (D : List (Obj V)),
      J ⊆ BU ∧ LentJS ⊆ lentJSClasses ω l ∧
      IsDecomp (((BU \ J) ∪ LentJS : Finset (Sym2 V)) : Set (Sym2 V)) D ∧ (∀ o ∈ D, ∃ c, o = Obj.cycle c) ∧
      (∀ o ∈ D, ∃ Y ∈ lendGoodAnc ω l, ∀ e ∈ o.edges, e ∈ BU ∨ ∃ j < S3.KJS run G l, e ∈ ω.LJS Y l j) ∧
      (D.length : ℝ) ≤ 126 * G.card / run.M G l
          + ∑ Y ∈ (run.allAncestors G).filter (fun Y => δ.giant Y l), 1.5 * (δ.m Y l : ℝ) ∧
      (J.card : ℝ) ≤ S6.jBoundRHS ω l ∧            -- eqJbound (optional, see JSLC-EQJBOUND)
      S6.JPlusProps ω l J                          -- s6:lemJplus J1, J2, types (i), (ii)
```

**Hazards.**

- **M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a)** (blocker): K^JS_l := M_l^2 is used as the NUMBER of JS classes / label values (0 <= j < K^JS_l) and K^JS_l * rho_l = M_l^-2 is used as an exact probability; M_l of (R2) is a real. This chunk also uses 'M_l - 1 cherry systems', pad <= ceil(M_l/2), t^JS_l = 2M_l+2 and k_0 := min(K^JS_l, ...). Needs the manuscript decision proposed in blueprint_s2a (M_l := ceil(...) ∈ ℕ). Checked for this chunk: every inequality of s6:lemLost, s6:lemJSLC, s6:thmMIXC survives with integer M_l (all only use M_l >= 2^40, P_{l-2} >= M_l^13, Σ1/M_l <= 2/D*). Fallback without manuscript change: K^JS_l := ceil(M_l^2), and s6:lemLost(i) becomes P(lab != *) = ceil(M_l^2) M_l^-4 <= M_l^-2 + M_l^-4 (the final '<= 2M_l^-2' still holds since 8M_l^-26 + M_l^-4 <= M_l^-2).
- **JSLC-G-UNDEFINED** (risk): Definition-vs-use: the statement's bound Σ_{giant} sc_{Y,l}, sc = (3g_{Y,l} - 6M_l)^+, uses g_{Y,l} = number of cherry classes, an object that exists only inside the proof (Step 5, a greedy colouring). A Lean statement cannot mention it. Decision: state the bound with 1.5 m_{Y,l} over giant pairs (the manuscript's own inequality sc <= 1.5m, and the only form used downstream, MIX-C(c)). Alternative (not recommended): existentially quantify g with g <= m/2 + 2M_l - 4.
- **JSLC-JPLUS-MERGE** (risk): s6:lemJplus asserts properties of 'the' J_l built in Step 2 of THIS proof ('for every choice of which edges are deleted'). In Lean JS-LC is an existential, so J_l has no identity outside it: the J+ properties must be conjuncts of JSLCStatement (JPlusProps), or else s7 has nothing to apply them to. Everything s7 needs about J_l must be in JPlusProps before the statement freeze (see JPLUS-S7-INTERFACE).
- **JSLC-USED** (risk): The hypothesis 'no edge of any class LJS_{Y,l,j} has been used' is not a mathematical predicate (it refers to the state of the assembly). Lean encoding: JS-LC assumes nothing and outputs LentJS_l ⊆ lentJSClasses ω l (i.e. it may use every edge of every such class); the 'not used before' obligation becomes a disjointness argument in s6:thmMIXC (LentJS_l ⊆ Lend_Y of ancestors of rounds <= l-2, distinct classes for distinct l, excluded from Erem/H_0 by definition). This is faithful because the manuscript's hypothesis is only used in the claim (d) 'the whole class is available'.
- **JSLC-PROOF-SIZE** (risk): The proof is the largest single combinatorial construction of s6: (1) classification of B_Z edges; (2) PAR per part and per class pair, parity moves with hub degrees AGGREGATED over all parts of round l; (3) connected components of each R_Y (need a finite component API on edge sets); (4) per non-giant component a cluster, MED orientation, EQ-LPT layering of loads, padding spread with pad(u) <= ceil((M_l-1)/2); (5) cherry pairing at centres, conflict graph, greedy (Δ+1)-colouring (NOT in Mathlib: grep found no maxDegree colouring lemma; ~100 lines), depth k_i with three cases; (6) for each (Y,l,j) the union multiset of junction pairs as an indexed family (ι := Σ over systems, junction units), multiplicity <= 2M_l-2 <= t^JS_l, joint routing through IsPathConnected.exists_paths; (7) HCC-P per system with its hypotheses (D),(P),(JC-P) and HCCglob; (8) the count. Estimated 4000+ lines, difficulty 5. Several numeric facts are 'clearly' steps: k_0 <= #clusters, raw loads >= Φ_max, eqSzeroCost's three cases, ceil(η/floor(η/2)) <= 3, conflict degree <= m/2 + 2M_l - 5; all re-derived and correct.
- **JSLC-HCCP-INTERFACE** (risk): JS-LC applies HCC-P to systems whose clusters come from two different sources (MED-oriented components; cherries u -> h -> u') with padding, depth k=1 special case (X^out/X^in, no padding) and path families given by the joint routing. The s6a HCC-P Spec must accept exactly this data (fixed admissible orientation per cluster; paths as vertex lists with first/last vertex and interior in T_j; demands via pad; output F_j ⊆ E(P_j) with the rest inside G[T_j], cycles only, count <= Φ). Also HCCglob must allow vertices shared across systems. Lock s6a's HCC-P Spec with this consumer in view.
- **JSLC-HUB-AGGREGATE** (note): Parity at a hub h ∈ D_l is taken over R^0_Y summed over ALL parts containing h (one move per (h, Y)); clusters of S_0(Y,l) may span several parts. A per-part formalization would break (J1) and the eqJbound count. Pseudo-hubs (port-port centres) are not in D_l, so they lie in one part.
- **JSLC-EQJBOUND** (note): (eqJbound) is part of the statement but 'not used later'. It is cheap once Step 2 is formalized (~150 lines); recommend keeping it as a conjunct (no weakening). If the integrator drops it, record a T0 decision.
- **JSLC-PATHCONN** (note): Joint routing: pairs are vertices of V(Y) (ports, in V(Y) since Y = Y(u) ∈ anc_l(u)), distinct (different layers / X^out ∩ X^in = ∅), multiplicity counted over the UNION of all systems of (Y,l) at junction j; LJS_{Y,l,j} is an FGraph on V(Y) and IsPathConnected requires ends in G.verts (true). Interior vertices lie in T_j(Y,l); ports are outside every T_j (lab = *), centres outside V(Y): this gives (D) of HCC-P. The path-length bound 2^12 L_Y^4 is not used.
- **JSLC-CONST** (note): The proof gives 15 n/M_l; the statement keeps 126 (value carried into MIX-C's 252/D_*). Spec uses 126 (as stated). Step-8 arithmetic: 0.75 + 13.7 + 0.5 + 16.44 M_l^-11 <= 15 needs M_l >= 2^40 and P_{l-2} >= M_l^13.

**Effort.** ~4200 lines, difficulty 5/5. Types+parity+J-set ~700; components & Bead inclusion ~350; S_0 system (MED, EQ-LPT, padding, eqSzeroCost) ~700; cherries + greedy colouring + depth cases (eqCherryCost) ~700; joint routing multisets ~600; HCC-P application + HCCglob + partition ~600; count ~250; JPlusProps proofs ~300 (listed under s6:lemJplus). Requires chunk s6a Specs (PAR, MED, EQ-LPT, HCC-P, HCCglob) first.

### `s6:remStar` — remark: the star split is not used (s6.tex:612)

**Status:** --. **Formalization:** nothing to formalize (no statement); the JS-LC Spec simply has no star-split option. A one-line docstring cross-reference in EG/Spec/Chain/JSLC.lean.

**Statement (precise restatement).** Remark: earlier versions allowed a 'star split' for giant pairs with a threshold tau'_l and a functional HC; not used here; its cost (<= HC_{Y,l}/2) is not controlled on this route; the cherry split costs <= #cherries/K^JS_l + 6M_l + 1.5 m_{Y,l} (eqCherryCost). Neither split emits single edges (all single edges of JS-LC come from Step 2), so J_l and all properties of J_l are independent of the split choice.

**Dependencies.** Declared: `s6:lemJSLC`.  
From the proof: `s6:lemJSLC`.  
Commentary on the proof of s6:lemJSLC.

**Used by:** none.

**Randomness.** none

**Lean shape.**

```lean
-- no declaration. (Non-vacuity: the claim 'J_l does not depend on the split' is subsumed by the existential JSLC Spec.)
```

**Hazards.**

- **STAR-NONE** (note): No content. Make sure no later Spec/definition reintroduces tau'_l or HC (s1:remNotUsed lists them).

**Effort.** ~0 lines, difficulty 1/5. none

### `s6:lemJplus` — lemma: Lemma J+: the J-interface (s6.tex:618)

**Status:** x2+RT. **Formalization:** Defs: structure EG.S6.JPlusProps (EG/Defs/Chain/JSet.lean), a conjunct of JSLCStatement (no standalone Spec: the J_l exists only inside JS-LC). Run-level facts J3, (iii), (iv) as Lib lemmas (EG/Lib/Chain/JSet.lean); (v) belongs to the Stage1 API (s3).

**Statement (precise restatement).** In s6:lemJSLC (round l >= 3, data as there): J_l is exactly the set of Step-2 deletions (PAR deletions per part and per class pair; then one bead per (centre, class) with odd realized class degree, hub degrees aggregated over all standalone parts of round l), for every choice of deleted edges; Steps 3-8 delete nothing. TYPES: J_l = J^lost ⊔ J^hub ⊔ J^fr ⊔ J^par where, for some Z ∈ Std_l with the edge in E_l(Z) (in fact in B_Z): a J^par-edge uv has u, v ∈ Q*_Z with Y(u) != Y(v); a J^hub-edge hu has h ∈ A_Z ⊆ D_l, u ∈ Q*_Z; a J^fr-edge xu has x ∈ F_Z, u ∈ Q*_Z; a J^lost-edge vu has v ∈ Lost_Z, u ∈ Q*_Z. The class of a J^hub/J^fr/J^lost edge hu is Y(u). (J1) For each hub h ∈ D_l and class Y: at most one J^hub-edge of class Y at h (aggregated over all parts of round l); for each fresh centre x and class Y: at most one J^fr-edge of class Y at x; likewise at lost centres. (J2) Every J-edge lying in E_l(Z) has an end in Q*_Z; for every Z and every vertex v at most M_l - 1 J-edges at v lie in E_l(Z); hence a vertex outside D_l carries at most M_l - 1 J-edges of round l; |J_l| <= n(M_l - 1) (<= 1.37n(M_l-1)). (J3) D_l, ∪_Z F_Z, ∪_Z Q*_Z are pairwise disjoint; each vertex outside D_l lying in a round-l pre-part lies in exactly one. (i) the types are exhaustive and exclusive; (ii) a fresh centre carries at most M_l - 1 J^fr-edges; (iii) E(H_Y) ⊆ E_r(Y) for every ancestor Y of round r, and the sets E_r(Y) (Y light) and E_l(Z) (Z ∈ Std_l) are pairwise disjoint; (iv) u ∈ V(Y(u)) for every classed port u; (v) in the colourings of s3:defCOL colours of distinct edges are independent.

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), m_{Y,l}, d*_{Y,l}, alpha_{Y,l}, Bead_{Y,l}, gamma_l, giant (Y,l), c^agg_{h,l}, c_x(Z), c_pp(u)* — s6:defDesign; delta assigns to every classed port u of round l>=3 an ancestor Y(u) ∈ anc_l(u); m_{Y,l} = max_h d_{Y,l}(h); (Y,l) giant iff a component of Bead_{Y,l} has > 2 gamma_l edges, gamma_l = floor(P_{l-2}/M_l) [s6:defDesign (chunk s6a)] — EG: no: proposed EG.S6.Designation (structure: cls : ℕ → V → ℕ × List Bool, valid : ∀ l a u, 3 ≤ l → a ∈ Std l → u ∈ classed l a → cls l u ∈ anc l u) with derived m, dStar, alpha, bead, giant, cAgg, cx, cpp
- *lendBad, Lost_Z, Ret_Z, Q*_Z (qs), O_Z, Lost_l, X_U* — s6:defLending (this chunk) [s6:defLending] — EG: no: proposed EG.S6.lendBad/lost/ret/qs/OZ/lostRound/XU (EG/Defs/Chain/Lending.lean)
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)

**Dependencies.** Declared: `s6:lemJSLC`, `s6:lemPAR`, `s6:defDesign`, `s2:propStructure`, `s2:lemEL`, `s2:lemCap`, `s3:defCOL`, `s2:defHBtp`, `s6:lemHCCP`, `s6:defLending`.  
From the proof: `s6:lemJSLC`, `s6:lemPAR`, `s6:lemHCCP`, `s6:defLending`, `s6:defDesign`, `s2:lemCap`, `s2:propStructure`, `s2:lemEL`, `s3:defCOL`, `s2:defAncestors`.  
Composition: proof of JS-LC (Steps 2-8; HCC-P outputs cycles only). Types/(i): defLending (A, F, Lost, Q* disjoint), lemEL (J^par ends have different classes). (J1): the move rule. (J2)/(ii): lemCap(ii), propStructure(iv). (J3): propStructure(iv). (iii): propStructure(iii). (iv): defDesign + defAncestors. (v): defCOL.

**Used by:** s6:defJconsumer, s6:lemLent, s6:thmMIXC, s7:consRound, s7:lemWellDef, s7:lemMULT, s7:lemLift, s7:lemCC, s7:lemUltra, s7:lemPay, s7:lemUHsplit, s7:lemEXprime (proof).

**Randomness.** none for J1-J3, (i)-(iv) (deterministic given ω). (v) is a property of the stage-1 LAW (product structure of edge colours), not of J_l.

**Lean shape.**

```lean
-- EG/Defs/Chain/JSet.lean
def isJpar ω l a (e : Sym2 V) : Prop := ∃ u v, e = s(u, v) ∧ u ∈ S6.qs ω l a ∧ v ∈ S6.qs ω l a ∧ δ.cls l u ≠ δ.cls l v
def isCentrePort (C : Finset V) ω l a (e : Sym2 V) (Y) : Prop := ∃ h u, e = s(h, u) ∧ h ∈ C ∧ u ∈ S6.qs ω l a ∧ δ.cls l u = Y
structure JPlusProps (ω) (l : ℕ) (J : Finset (Sym2 V)) : Prop where
  inE    : ∀ e ∈ J, ∃ a ∈ run.Std G l, e ∈ run.E G l a
  types  : ∀ a ∈ run.Std G l, ∀ e ∈ J, e ∈ run.E G l a →
             isJpar ω l a e ∨ ∃ Y, isCentrePort (run.hubs G l a ∪ run.fresh G l a ∪ S6.lost ω l a) ω l a e Y
  J1hub  : ∀ h ∈ run.D G l, ∀ Y, (J.filter (fun e => ∃ a ∈ run.Std G l, e ∈ run.E G l a ∧
             ∃ u, e = s(h, u) ∧ h ∈ run.hubs G l a ∧ u ∈ S6.qs ω l a ∧ δ.cls l u = Y)).card ≤ 1
  J1fr   : ∀ a ∈ run.Std G l, ∀ x ∈ run.fresh G l a, ∀ Y, (J.filter (isCentrePort {x} ω l a · Y)).card ≤ 1
  J1lost : ∀ a ∈ run.Std G l, ∀ v ∈ S6.lost ω l a, ∀ Y, (J.filter (isCentrePort {v} ω l a · Y)).card ≤ 1
  J2cap  : ∀ a ∈ run.Std G l, ∀ v, (J.filter (fun e => e ∈ run.E G l a ∧ v ∈ e)).card ≤ run.M G l - 1
  J2card : (J.card : ℝ) ≤ G.card * ((run.M G l : ℝ) - 1)
-- 'exclusive' part of (i): a lemma from the disjointness API of s6:defLending (independent of J).
-- EG/Lib/Chain/JSet.lean (J-independent run facts): J3 (hubs/fresh/qs disjoint; one pre-part outside D_l),
--   (iii) = HB.Run.ancGraph_edges_subset_E & disjointness (propStructure(iii)), (iv) = δ.cls_mem_anc ⇒ u ∈ V(Y(u)).
-- (v): EG.S3.stage1Dist is a product over edges (iIndepFun of edge colours) -- s3 API, not here.
```

**Hazards.**

- **JPLUS-EXISTENTIAL** (risk): The lemma is a statement about the CONSTRUCTION inside another lemma's proof ('J_l consists exactly of the deletions of Step 2 ... for every choice'; 'Steps 3-8 delete nothing'). Not formalizable as a standalone Spec. Resolution: JPlusProps as a conjunct of the JS-LC existential (JSLC-JPLUS-MERGE). The 'exactly the Step-2 deletions / every choice' clause is dropped: downstream (s7) uses only types, J1, J2, (ii) (checked in s7.tex: consRound (a)-(h); lemWellDef l.418-420 (J2, (ii)); lemMULT l.540 (J1hub); lemLift l.596-666 (J3, (iii): items in E_l(Z), junction edges in E(H_Y)); the CC preamble l.700-712 (J2card); lemUltra l.864 (J2); lemPay l.914-960 ((a1) J2 at lost centres + J3, (a2) J1hub + J3 + items are edges of E_l(Z) with d_{Y,l}(v) >= 1, (a3) J2, (b) one unpaired leg per fresh centre)).
- **JPLUS-S7-INTERFACE** (risk): JPlusProps is the ONLY information the s7 J-consumer gets about J_l (in the recommended MIX-C design). Before the freeze, cross-check every s7 proof that cites 'properties of J_l' against the conjuncts: e.g. s7:lemPay (fresh legs per fresh centre, J^lost payments (M_l-1)|Lost_l| via J2cap at lost centres), s7:lemMULT/Ultra (J1hub), s7:lemCand (ports in Q*_Z, classes lend-good, u ∉ T_j), lemLift (J ⊆ ∪E_l(Z), disjoint from LJV). Any missing fact (e.g. 'the port end u of an item has Y(u) lend-good', 'J ⊆ ∪_Z B_Z') must be added to JPlusProps now; adding it later changes a locked statement.
- **JPLUS-V-PROB** (note): (v) 'colours of distinct edges are independent' is a property of the stage-1 law, not of J_l; it is listed as an interface fact for s7:lemCand. Formalize as an iIndepFun lemma of S3.stage1Dist (s3 layer).
- **JPLUS-J3-III-IV** (note): (J3), (iii), (iv) do not mention J_l; they are run/designation lemmas (propStructure(iii),(iv), defDesign). Keep them out of JPlusProps to avoid proving them per call.
- **JPLUS-CLASS-JPAR** (note): 'The class' is defined only for centre-port J-edges; a J^par edge has two classes. The factor 1.37 in (J2) is vestigial (n(M_l-1) is already proved).

**Effort.** ~350 lines, difficulty 3/5. Definitions ~60; proofs of the conjuncts inside JS-LC ~250 (types from Step-1 classification, J1 from the move rule, J2 from lemCap(ii) and the charging argument); run facts ~40.

### `s6:defJconsumer` — definition: round-l J-consumer (s6.tex:665)

**Status:** x0 (interface made explicit here). **Formalization:** Defs EG/Defs/Chain/JConsumer.lean: structure EG.S6.JConsumer (a function (l, J) ↦ (Obj_l, LentJV_l) with JC1, JC2 required for admissible J); JC3 is implied by IsDecomp. Test EGTest: the trivial consumer (J as single edges, LentJV = ∅) is a JConsumer.

**Statement (precise restatement).** A J-consumer is a rule acting at each round 3 <= l <= R: given everything constructed at rounds > l, the stage-1 outcome and J_l (which has the properties of s6:lemJplus), possibly with fresh randomness, it outputs a family Obj_l of objects and an edge set LentJV_l with (JC1) LentJV_l ⊆ ∪{LJV_{Y,l} : Y a lend-good ancestor of round <= l-2}; (JC2) the objects of Obj_l are pairwise edge-disjoint cycles and single edges of G whose union is exactly J_l ∪ LentJV_l; (JC3) Obj_l uses no other edge. By COL(g) the classes LJV_{Y,l} are used by nothing else. Example: Obj_l := J_l as single edges, LentJV_l := ∅. The final J-consumer is the round step s7:consRound.

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)
- *lendBad, Lost_Z, Ret_Z, Q*_Z (qs), O_Z, Lost_l, X_U* — s6:defLending (this chunk) [s6:defLending] — EG: no: proposed EG.S6.lendBad/lost/ret/qs/OZ/lostRound/XU (EG/Defs/Chain/Lending.lean)
- *objects, decomposition* — Obj = edge | cycle (list); IsDecomp E D: WF objects, edge lists pairwise disjoint, union exactly E [s1:defObject] — EG: yes: EG.Obj, EG.Obj.WF, EG.Obj.edges, EG.IsDecomp (EG/Defs/Objects.lean)
- *JPlusProps* — admissibility of the input J (s6:lemJplus) [s6:lemJplus] — EG: no: proposed
- *LJV_{Y,l}* — JV-lent class of ancestor Y for round l (graph on V(Y)) [s3:defCOL(ii)] — EG: no: part of S3.Stage1 derived data

**Dependencies.** Declared: `s3:defCOL`, `s6:lemJplus`.  
From the proof: `s3:defCOL`, `s6:lemJplus`, `s6:defLending`, `s1:defObject`.  
s6:defLending (lend-good) and s1:defObject (objects) are used but undeclared.

**Used by:** s6:consOrder, s6:lemLent, s6:thmMIXC, s7:consRound, s7:lemLift, s7:propCost.

**Randomness.** The consumer may use fresh randomness (s7: xi_l). In the deterministic Lean interface the randomness is resolved inside the consumer (the s7 instance picks xi_l in the event of consRound(f) by choice; that event is nonempty for every past by Markov), so a consumer is a deterministic function.

**Lean shape.**

```lean
-- EG/Defs/Chain/JConsumer.lean   (ctx = (G, run, δ, ω) as a structure MixCtx)
def JC1 (ctx) (l : ℕ) (L : Finset (Sym2 V)) : Prop :=
  L ⊆ (S6.lendGoodAnc ctx.ω l).biUnion (fun Y => ctx.ω.LJV Y l)
def JC2 (J L : Finset (Sym2 V)) (Ob : List (Obj V)) : Prop :=
  IsDecomp ((J ∪ L : Finset (Sym2 V)) : Set (Sym2 V)) Ob      -- cycles/edges, disjoint, union exactly J ∪ L (⇒ JC3)
structure JConsumer (ctx : MixCtx V) where
  out : ℕ → Finset (Sym2 V) → List (Obj V) × Finset (Sym2 V)
  jc  : ∀ l J, 3 ≤ l → l ≤ ctx.run.R → S6.JPlusProps ctx.ω l J →
          JC1 ctx l (out l J).2 ∧ JC2 J (out l J).2 (out l J).1
def trivialConsumer (ctx) : JConsumer ctx := ⟨fun _ J => (J.toList.map Obj.edge, ∅), by ...⟩  -- WF: J ⊆ E(G) loopless
-- Variant needed only under MIX-C Option A: `out` may also take the past (the RoundData of rounds > l).
```

**Hazards.**

- **JCONS-TYPE** (risk): 'A rule that, given everything constructed at rounds > l, the stage-1 outcome and J_l (and possibly fresh randomness), outputs ...' is not a mathematical object. Decision needed before freeze: type of `out`. Recommended: function of (l, J_l) only (stage-1 data fixed in ctx). Checked against s7:consRound (a)-(h): the round step reads J_l, stage-1 data (Pool_l, Cand_l, JV-bad, LJV classes) and xi_l; the Markov event (f) uses E[·|Past_l], a function of J_l given stage 1. So the (l, J) interface suffices for the s7 instance. If some s7 step needs more of the past, extend `out` to take the RoundData of rounds > l (Option A in s6:thmMIXC).
- **JCONS-CONDITIONAL** (risk): Definition-vs-use: the definition demands JC1-JC3 of the output, implicitly only for the actual J_l ('Here J_l has the properties of Lemma J+'). The s7 round step is NOT a J-consumer on arbitrary edge sets (it needs port ends in Q*_Z, lend-good classes, J1/J2 caps for its colour palettes). So JC1-JC2 must be required only for J satisfying JPlusProps; MIX-C then proves that the J_l it feeds are admissible. Decide and lock together with JPlusProps.
- **JCONS-JC3** (note): (JC3) is implied by (JC2) once 'union is exactly J ∪ LentJV' is IsDecomp; do not state it separately (or state it as a derived lemma).
- **JCONS-COLG** (note): 'By COL(g), LJV_{Y,l} is used by nothing except the round-l J-consumer' is a property of the whole assembly; in Lean it is the disjointness step of MIX-C (LJV ⊆ Lend_Y ⊆ E(H_Y), excluded from Erem/H_0 via Lent).
- **JCONS-NONVAC** (note): Provide the trivial consumer as an EGTest instance (checks the structure is satisfiable; needs J ⊆ E(G), which follows from JPlusProps.inE).

**Effort.** ~90 lines, difficulty 2/5. Definitions ~40; trivial consumer + test ~50.

### `s6:consOrder` — construction: the processing order R, R-1, ..., 1, and the Lent sets (s6.tex:678)

**Status:** x2 (JV+* referees, assembly audit). **Formalization:** Proof-internal definitions (recommended: EG/Proof/Chain/MixC/Chain.lean, `noncomputable irreducible_def` with Classical.epsilon so no Spec depends on a proof): the STANDALONE chain chainRound (rounds R..1: Erem, TPV split, JS-LC, consumer) and the Lent sets; light parts are NOT interleaved (K-RED applied once with the final Lentext; decision ORDER-DECOUPLE). Only needed in Specs under MIX-C Option A.

**Statement (precise restatement).** Input: a valid run on G with n >= N0 and d_1 >= D_*, a designation delta; a stage-1 outcome ω with stage-2 data; stage-3 outcomes fixed in their good events (TPV labels for every Z ∈ Std; child-vortex labels for non-demoted light parts; VX+ labels for demoted light parts); a J-consumer. Lent sets of an ancestor Y of round r: LentU(Y) := U-lent edges of Y used by s5:lemParent at rounds l >= r+2 (light Y; ∅ for standalone); LentJS(Y) := ∪_{l >= r+2} (LentJS_l ∩ ∪_j LJS_{Y,l,j}) (edges on output cycles; returned edges excluded); LentJV(Y) := ∪_{l >= r+2} (LentJV_l ∩ E(H_Y)); Lent(Y) := LentU ∪ LentJS ∪ LentJV. Standalone Y: Erem(Y) := E_r(Y) \ Lent(Y); light non-demoted Y: H_0(Y) := E_r(Y) \ Lent(Y). For l = R, R-1, ..., 1: (1) for every Z ∈ Std_l apply s4:lemTPV (on its good event) to (Z^0, O := O_Z, E := Erem(Z), P := Ret_Z, Q := Q*_Z): Erem(Z) = E^V(Z) ⊔ E^Q(Z), E^V(Z) decomposed into <= 169|Ret_Z| objects (output); (2) every non-demoted light part of round l runs s5:lemChild on H_0(Y); every demoted light part runs VX+ on E_l(Y) (s5:lemDemoted); if l >= 3 the U-bundles Bdl_{l,c} (c ∈ [4]) are chained by s5:lemParent and the used U-lent edges recorded; (3) if l >= 3: s6:lemJSLC with B_Z := E^Q(Z) for all Z ∈ Std_l; its cycles are output, LentJS_l recorded; this yields J_l; (4) if l >= 3: the J-consumer on J_l; Obj_l output, LentJV_l recorded. Finally output the cycles of every Cyc_l and every edge of E_0 as a single edge. Rounds 1, 2: no classed ports, J_1 = J_2 = ∅.

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), m_{Y,l}, d*_{Y,l}, alpha_{Y,l}, Bead_{Y,l}, gamma_l, giant (Y,l), c^agg_{h,l}, c_x(Z), c_pp(u)* — s6:defDesign; delta assigns to every classed port u of round l>=3 an ancestor Y(u) ∈ anc_l(u); m_{Y,l} = max_h d_{Y,l}(h); (Y,l) giant iff a component of Bead_{Y,l} has > 2 gamma_l edges, gamma_l = floor(P_{l-2}/M_l) [s6:defDesign (chunk s6a)] — EG: no: proposed EG.S6.Designation (structure: cls : ℕ → V → ℕ × List Bool, valid : ∀ l a u, 3 ≤ l → a ∈ Std l → u ∈ classed l a → cls l u ∈ anc l u) with derived m, dStar, alpha, bead, giant, cAgg, cx, cpp
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)
- *lendBad, Lost_Z, Ret_Z, Q*_Z (qs), O_Z, Lost_l, X_U* — s6:defLending (this chunk) [s6:defLending] — EG: no: proposed EG.S6.lendBad/lost/ret/qs/OZ/lostRound/XU (EG/Defs/Chain/Lending.lean)
- *objects, decomposition* — Obj = edge | cycle (list); IsDecomp E D: WF objects, edge lists pairwise disjoint, union exactly E [s1:defObject] — EG: yes: EG.Obj, EG.Obj.WF, EG.Obj.edges, EG.IsDecomp (EG/Defs/Objects.lean)
- *TPVGood Z O P (abstract good-event conclusion of s4:lemTPV)* — ∀ E with E(O) ⊆ E ⊆ (Z choose 2): ∃ partition E = E^V ⊔ E^Q with (T1) edges inside P are in E^V, (T2) E^V edges with an end in Q are in O, (T3) E^V decomposes into <= 169|P| objects [s4:lemTPV conclusion] — EG: no: proposed EG.S4.TPVGood (Defs), with a lemma 'labels in the TPV good event ⇒ TPVGood' from the s4 Spec
- *K-RED data: LentU_{l,c}, H_0, Lentext, the light-part good events* — s5:lemParent, s5:lemKRED [s5] — EG: no: s5 layer
- *JConsumer* — s6:defJconsumer [s6:defJconsumer] — EG: no: proposed
- *RoundData (per-round record of the standalone chain)* — EV, EQ : addr → edge set; DT : addr → objects; J, LentJS, LentJV : edge sets; DS, DJ : objects [Construction steps (1),(3),(4)] — EG: no: proof-internal

**Dependencies.** Declared: `s4:lemTPV`, `s5:lemChild`, `s5:lemParent`, `s5:lemDemoted`, `s6:lemJSLC`, `s6:defJconsumer`, `s6:defLending`, `s5:defStages`, `s4:thmVXp`, `s3:defCOL`.  
From the proof: `s4:lemTPV`, `s5:lemChild`, `s5:lemParent`, `s5:lemDemoted`, `s5:lemKRED`, `s6:lemJSLC`, `s6:defJconsumer`, `s6:defLending`, `s5:defStages`, `s4:thmVXp`, `s3:defCOL`, `s2:defHBtp`, `s2:defAncestors`.  
A construction; well-definedness is s6:lemLent(i) and s6:thmMIXC(a). s5:lemKRED is the light-part half of the construction (steps (2) + Cyc + E_0), undeclared here but declared in lemLent/MIXC.

**Used by:** s6:lemLent, s6:thmMIXC, s7:lemOneOutcome, s7:propCost.

**Randomness.** Deterministic given (ω, stage-3 outcomes in the good events, the J-consumer). Stage-3 labels enter only through the abstract good-event conclusions (TPVGood; K-RED's hypotheses), which hold for EVERY admissible edge set, so no conditioning on later edge sets is needed.

**Lean shape.**

```lean
-- EG/Proof/Chain/MixC/Chain.lean (proof-internal; Option B)   -- ctx : MixCtx V, C : JConsumer ctx
structure RoundData (V) where
  EV EQ : List Bool → Finset (Sym2 V); DT : List Bool → List (Obj V)
  J LentJS LentJV : Finset (Sym2 V); DS DJ : List (Obj V)
def lentJS (past : ℕ → RoundData V) (Y : ℕ × List Bool) : Finset (Sym2 V) :=
  (Finset.Icc (Y.1 + 2) R).biUnion (fun l => (past l).LentJS ∩ (run.ancGraph G Y.1 Y.2).edges)
def lentJV (past) (Y) := (Finset.Icc (Y.1 + 2) R).biUnion (fun l => (past l).LentJV ∩ (run.ancGraph G Y.1 Y.2).edges)
def erem (past) (l a) := run.E G l a \ (lentJS past (l, a) ∪ lentJV past (l, a))
noncomputable def chain : ℕ → RoundData V   -- well-founded on R + 1 - l; round l reads only rounds ≥ l + 2
  -- EV/EQ/DT := Classical.epsilon (TPV split of erem past l a);  (J, LentJS, DS) := Classical.epsilon (JSLC outputs
  --   for B := EQ) if 3 ≤ l else (∅, ∅, []);  (DJ, LentJV) := C.out l J if 3 ≤ l else ([], ∅)
def lentext (Y) := lentJS chain Y ∪ lentJV chain Y      -- light Y: fed to K-RED once (ORDER-DECOUPLE)
-- Option A (chain exposed in the MIX-C Spec): move to EG/Defs/Chain/Order.lean with Classical.epsilon only (no proof terms).
```

**Hazards.**

- **ORDER-RECURSION** (risk): The chain is a recursion over rounds with choices from existential Specs (TPV split, JS-LC outputs). In EG/Defs/** a definition may not depend on proofs: use Classical.epsilon of the defining predicate (properties then follow from the existence theorems), or keep the chain proof-internal (Option B of s6:thmMIXC, recommended). Well-foundedness: round l needs rounds l' >= l+2 only (lent classes of Z exist only for l' >= r(Z)+2); define by strong recursion on R + 1 - l. Proving that each round's hypotheses hold (TPV: E(O_Z) ⊆ Erem(Z); JS-LC: B_Z edges have an end in Q*_Z) is an induction carried alongside.
- **ORDER-STAGE3** (risk): 'Stage-3 outcomes ... each fixed in its good event' refers to events that exist only inside existential Specs (s4:lemTPV, s4:lemPV/s5:lemChild, s4:thmVXp/s5:lemDemoted). Lean: the construction/MIX-C take the abstract conclusions as hypotheses (TPVGood (Z^0, O_Z ω, Ret_Z ω) for every Z ∈ Std; K-RED's per-part good predicates). The link 'labels in the good event ⇒ conclusion' is proved where the labels are chosen (s7:lemOneOutcome). The separate obligation 'TPV's input hypotheses hold for (Z^0, O_Z, Ret_Z)' (|Z^0| >= N0, O_Z spanning (2^-5, s)-expander with s >= 2^150 L^42) becomes a stand-alone lemma (MIX-C(a)) that s7 uses to show the good event is nonempty.
- **ORDER-DECOUPLE** (note): Simplification checked against the text: the standalone steps (1),(3),(4) of round l read only Lent(Z) = LentJS(Z) ∪ LentJV(Z) for Z ∈ Std_l (LentU(Z) = ∅ for standalone Z), E^Q(Z), J_l and stage-1 data; they never read the light-part outputs of step (2). The light-part half is exactly s5:lemKRED run with the family Lentext(Y) = LentJS(Y) ∪ LentJV(Y), which K-RED accepts for ANY family of the stated kind. So Lean can (a) build the standalone chain R..1 alone, (b) apply the K-RED Spec once, post hoc, with the final Lentext. The interleaved order and s5:lemKRED's 'Moreover' (dependence on rounds > l) are then not needed.
- **ORDER-LENTU-INTERNAL** (note): LentU(Y) is internal to K-RED (s5:lemKRED defines LentU(Z) := E(H_Z) ∩ ∪_{l' >= l+2, c} LentU_{l',c}); under ORDER-DECOUPLE no s6 object needs it. Do not duplicate it in s6 Lean.
- **ORDER-RETURNED** (note): LentJS(Y) must contain only edges on OUTPUT cycles (LentJS_l = ∪ F_j of HCC-P), not the routed-but-returned edges; in Lean LentJS_l is exactly JS-LC's output set, so this is automatic. Returned and unused lent edges stay in Erem/H_0 as junk.

**Effort.** ~450 lines, difficulty 4/5. RoundData + lent sets ~100; chain recursion with epsilon choices ~150; invariants carried through the recursion (hypotheses of TPV/JS-LC at each round, finality) ~200.

### `s6:lemLent` — lemma: Lent sets (s6.tex:712)

**Status:** x2 (JV+* referees). **Formalization:** Proof-internal lemmas of the MIX-C proof (EG/Proof/Chain/MixC/Lent.lean); no Spec (under Option B the Lent sets are proof-internal). Under Option A: Spec EG/Spec/Chain/Lent.lean with the four parts.

**Statement (precise restatement).** In s6:consOrder, for every ancestor Y of round r: (i) Lent(Y) ⊆ Lend_Y, and Lent(Y) depends only on the steps at rounds >= r+2 (so it is final when Y is processed at round r); (ii) if Y is standalone and lend-bad then Lent(Y) = ∅ (every port of class Y is lost, so Y has no JS system; JC1 excludes its JV classes); if Y is light and demoted then Lent(Y) = ∅; (iii) Erem(Z) ⊇ E(O_Z) for every Z ∈ Std, and H_0(Y) ⊇ Own_Y for every non-demoted light Y; (iv) with Lentext(Y) := LentJS(Y) ∪ LentJV(Y) for light Y, the family (Lentext(Y))_Y satisfies the hypothesis of s5:lemKRED (Lentext(Y) ⊆ ∪_{l,j} LJS_{Y,l,j} ∪ ∪_l LJV_{Y,l}, and = ∅ if Y demoted), H_0(Y) = E_r(Y) \ (LentU(Y) ∪ Lentext(Y)) is the H_0(Y) of that lemma, and LentU(Y), LentJS(Y), LentJV(Y) are pairwise disjoint.

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)
- *lendBad, Lost_Z, Ret_Z, Q*_Z (qs), O_Z, Lost_l, X_U* — s6:defLending (this chunk) [s6:defLending] — EG: no: proposed EG.S6.lendBad/lost/ret/qs/OZ/lostRound/XU (EG/Defs/Chain/Lending.lean)
- *demoted, parent-bad, Bad, good parent, dem, lp (stage-2 statuses of light parts)* — s5:defStages: Y demoted iff (E1) fails or a COL(a) event fails (light parameters); dem = Σ_{Y demoted}|Y|; lp = Σ_{Y ∈ Bad}|Y|(R-r(Y)) [s5:defStages] — EG: no: proposed EG.S5.demoted, EG.S5.Bad, EG.S5.dem, EG.S5.lp (s5 layer)
- *Lent(Y), LentU, LentJS, LentJV, Erem, H_0, Lentext* — s6:consOrder [s6:consOrder] — EG: no: proof-internal (see s6:consOrder lean_shape)

**Dependencies.** Declared: `s6:consOrder`, `s6:defLending`, `s6:defJconsumer`, `s6:lemJSLC`, `s5:lemParent`, `s5:lemKRED`, `s3:defCOL`, `s6:lemJplus`, `s5:defStages`, `s4:lemTPV`, `s5:lemChild`, `s5:lemDemoted`, `s4:thmVXp`.  
From the proof: `s6:consOrder`, `s6:defLending`, `s6:defJconsumer`, `s6:lemJSLC`, `s6:lemJplus`, `s5:lemParent`, `s5:lemKRED`, `s5:defStages`, `s3:defCOL`, `s2:propStructure`.  
(i): lemParent(i) (U-lent edges in classes of good parents), JS-LC output ⊆ LJS classes, JC1 + J+(iii) (= propStructure(iii): E(H_Y) pairwise disjoint), defCOL(ii) (classes exist only for r+2 <= l <= R) and COL(g). (ii): defLending (lend-bad ⇒ all class-Y ports lost ⇒ R_Y = ∅ in JS-LC), JC1, defStages (demoted ⇒ not a good parent). (iii): defCOL(i) (Own ∩ Lend = ∅), J+(iii). (iv): K-RED's hypothesis and defCOL(ii). Declared but not logically used: s4:lemTPV, s5:lemChild, s5:lemDemoted, s4:thmVXp (they appear only as the devices whose inputs are discussed).

**Used by:** s6:thmMIXC.

**Randomness.** none (deterministic given ω, stage-3 outcomes and the consumer).

**Lean shape.**

```lean
-- EG/Proof/Chain/MixC/Lent.lean (proof-internal lemmas about `chain`)
lemma lent_subset_lend (Y) : lentJS chain Y ∪ lentJV chain Y ⊆ ω.lend Y
lemma lent_eq_empty_of_lendBad (Y) (hY : run.isStd Y) (hb : S6.lendBad ω Y) : lentJS chain Y ∪ lentJV chain Y = ∅
lemma lentext_eq_empty_of_demoted (Y) (hY : light) (hd : S5.demoted ω Y) : lentext Y = ∅
lemma OZ_edges_subset_erem (l a) (ha : a ∈ run.Std G l) : (S6.OZ ω l a).edges ⊆ erem chain l a
lemma lentext_KREDhyp : S5.LentextHyp ω lentext          -- the hypothesis of the s5:lemKRED Spec
lemma disjoint_lentJS_lentJV (Y) : Disjoint (lentJS chain Y) (lentJV chain Y)
-- 'final when processed' (i, second half) is definitional (chain round l reads rounds ≥ l+2).
```

**Hazards.**

- **LENT-KRED-FORM** (risk): (iv) presupposes that the s5:lemKRED Spec is stated in the 'for any family' form with LentU and H_0 internal to K-RED ('H_0(Y) of that lemma'). If the s5 blueprint states K-RED with H_0 as input or with an interleaved construction, (iv) and ORDER-DECOUPLE break. Coordinate with the s5 blueprint: K-RED Spec := ∀ family Lentext with Lentext(Y) ⊆ ∪LJS_Y ∪ ∪LJV_Y and Lentext(Y) = ∅ for demoted Y, ∃ decomposition of E(G) \ Kstd \ ∪Lentext with the cost bound.
- **LENT-LIGHT-LENDBAD** (note): A light Y can be lend-bad without being demoted (COL(b) fails). Then Lentext(Y) = ∅ (no Q* port has class Y; JC1) but LentU(Y) may be non-empty (Y may be a good parent). (ii) claims emptiness only for demoted light Y, consistent; K-RED only needs Lentext(Y) = ∅ for demoted Y.
- **LENT-OZ-LENDBAD** (note): (iii) for lend-bad standalone Z uses (ii) (Lent(Z) = ∅) so Erem(Z) = E_l(Z) ⊇ E(X^0_Z) = E(O_Z); for lend-good Z it uses Lent(Z) ⊆ Lend_Z and Own_Z ∩ Lend_Z = ∅. Both re-derived.
- **LENT-LATE-ROUNDS** (note): For r >= R-1 there are no lent classes and Lent(Y) = ∅ automatically (Finset.Icc (r+2) R = ∅).

**Effort.** ~300 lines, difficulty 3/5. Each part ~60-80 lines of set bookkeeping over classes, rounds and the H_Y-disjointness.

### `s6:thmMIXC` — theorem: Theorem MIX-C: the assembly with V = ∅, deterministic form (s6.tex:757)

**Status:** x2 (assembly audit, JV+* referees); this formulation x0. **Formalization:** Spec EG/Spec/Chain/MixC.lean: MixCStatement (Option B: decomposition + cost, with a per-round bound hypothesis on the consumer) + MixCTPVApplicable (the TPV bullet of (a), used by s7 to make the good events nonempty); proof EG/Proof/Chain/MixC/*.lean (chain, Lent, coverage, cost).

**Statement (precise restatement).** Fix: G with n >= N0, a valid HB*^{tau+} run with d_1 >= D_* (Γ1-Γ4, N0 as in s1), a designation delta; ANY stage-1 outcome ω; stage-3 outcomes in the good events of s4:lemTPV for every Z ∈ Std (with data (Z^0, O_Z, Ret_Z)), of s4:lemPV via s5:lemChild for every non-demoted light part, and of s4:thmVXp via s5:lemDemoted for every demoted light part; ANY J-consumer. Run s6:consOrder. Then: (a) (order) at step (1) of round l, Lent(Z) is final for Z ∈ Std_l; JS-LC at round l uses only classes LJS_{Y,l,·} and the consumer only LJV_{Y,l}, of ancestors of rounds <= l-2; the hypotheses of s6:lemJSLC hold at every l >= 3; every device is applied within its hypotheses (TPV: |Z^0| >= P_l >= N0, O_Z a spanning (2^-5, s_l/4) resp. (2^-5, s_l)-expander on Z^0 with s_l/4 >= 2^150 L_Z^42, E(O_Z) ⊆ Erem(Z) ⊆ (Z^0 choose 2); child vortex: Own_Y ⊆ H_0(Y) ⊆ E_l(Y); VX+: Lent(Y) = ∅ for demoted Y). (b) (coverage) the output is a decomposition of E(G); in detail E_r(Y) = LentU(Y) ⊔ LentJS(Y) ⊔ LentJV(Y) ⊔ H_0(Y) for light non-demoted Y (Lent(Y) = ∅ if demoted); E_l(Z) = Lent(Z) ⊔ E^V(Z) ⊔ (E^Q(Z) \ J_l) ⊔ (J_l ∩ E_l(Z)) for Z ∈ Std_l; each lent edge in at most one object; unused/returned lent edges covered by their owner's device. (c) (cost) #objects <= (D_*/2 + 745 + 338) n + eps_M(D_*) n + [80 dem + 369 lp + 169 Σ_l |Lost_l|] + 1.5 Σ_{(Y,l)} m_{Y,l} + Σ_l |Obj_l|, with eps_M(D) := eps_K(D) + 169 eps_A(D) + 252/D, eps_A(D) = 31 eps/(C' log log D) (s2:lemTower(e)), eps_K = eps_Chain (s5:lemParent); moreover 1.5 Σ m_{Y,l} <= 1.5 eps_CONC(D_*) n (s6:thmCONCL(iv)). Itemization: K-RED (D_*/2 + 745 + eps_K)n + 80dem + 369lp; TPV 169 Σ(|A_Z| + |F_Z| + |Lost_Z|) <= 169(2 + eps_A)n + 169 Σ_l |Lost_l|; JS-LC Σ_l 126n/M_l + 1.5Σm <= 252n/D_* + 1.5Σm; consumer Σ_l |Obj_l|.

**Definitions needed.**

- *valid run and round objects: run.Valid G Dstar, R, G_l = run.graph G l, d_l, lambda_l, M_l, s_l, P_l, tau_l, Std_l, Z^0, X^0_Z, D_l, S_Z (guests), light/standalone, E_l(Z) (= run.E G l a), Dup*_l, E_0, Cyc_l* — s2:defHBtp (R0)-(R5), (GC); pre-parts identified by (round, address) [s2:defHBtp] — EG: no: proposed EG.HB.Run API (blueprint_s2a: Run.Valid, graph, d, Std, Z0, X0, D, guests, isLight, E, DupStar, MOf/POf/sOf/tauOf/thetaGC)
- *ancestors Y=(r,a), V(Y), H_Y, eps_Y, s_Y, L_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z* — s2:defAncestors: light part (V=Y^0\S_Y, H=X_Y) or standalone pre-part (V=Y^0, H=X^0_Y); anc_l(x) = ancestors of rounds <= l-2 containing x (empty for l<=2); A_Z=Z^0∩D_l, U_Z=Z^0\D_l, F_Z={x∈U_Z: anc_l(x)=∅}, Q_Z=U_Z\F_Z [s2:defAncestors] — EG: no: proposed EG.HB.Run.ancVerts/ancGraph/ancEps/ancS/LY/anc/hubs/ports/fresh/classed (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), m_{Y,l}, d*_{Y,l}, alpha_{Y,l}, Bead_{Y,l}, gamma_l, giant (Y,l), c^agg_{h,l}, c_x(Z), c_pp(u)* — s6:defDesign; delta assigns to every classed port u of round l>=3 an ancestor Y(u) ∈ anc_l(u); m_{Y,l} = max_h d_{Y,l}(h); (Y,l) giant iff a component of Bead_{Y,l} has > 2 gamma_l edges, gamma_l = floor(P_{l-2}/M_l) [s6:defDesign (chunk s6a)] — EG: no: proposed EG.S6.Designation (structure: cls : ℕ → V → ℕ × List Bool, valid : ∀ l a u, 3 ≤ l → a ∈ Std l → u ∈ classed l a → cls l u ∈ anc l u) with derived m, dStar, alpha, bead, giant, cAgg, cx, cpp
- *stage-1 outcome ω and its law: EG.S3.Stage1 run G, EG.S3.stage1Dist* — product of independent families: (1a) per ancestor Y and edge e ∈ E(H_Y): fair bit (Own/Lend), lent index uniform on I_U(Y) ⊔ I_JS(Y) ⊔ I_JV(Y) (only if r(Y) <= R-2), own label uniform on [k_own] (light Y); (1b) per vertex v: choice(v) ∈ {none} ∪ {light Y ∋ v, r(Y) <= R-2} with P(Y)=L_Y^-2, sublabel uniform on I_U(Y); (1c) per (Y, l ∈ [r+2,R], y ∈ V(Y)): lab_{Y,l}(y) ∈ {*} ∪ [0,K^JS_l) with P(j)=rho_l=M_l^-4; (1d) pool labels (s7:defPool). Derived: Own_Y, Lend_Y, LU_{Y,l,c,slot}, LJS_{Y,l,j}, LJV_{Y,l} (graphs on V(Y)), own classes, T_j(Y,l)={y: lab=j}, zones [s3:defCOL, s5:defZones, s7:defPool, s7:defSchedule (1a)-(1d)] — EG: no: EG.Defs.Prob.FinDist exists (pi, prod, ofFintype, uniform, rsubset); the Stage1 type and law are proposed in the s3 layer (PLAN §3 'Stage1'); JS label law built with FinDist.ofFintype (reviewers check weights)
- *lendBad, Lost_Z, Ret_Z, Q*_Z (qs), O_Z, Lost_l, X_U* — s6:defLending (this chunk) [s6:defLending] — EG: no: proposed EG.S6.lendBad/lost/ret/qs/OZ/lostRound/XU (EG/Defs/Chain/Lending.lean)
- *demoted, parent-bad, Bad, good parent, dem, lp (stage-2 statuses of light parts)* — s5:defStages: Y demoted iff (E1) fails or a COL(a) event fails (light parameters); dem = Σ_{Y demoted}|Y|; lp = Σ_{Y ∈ Bad}|Y|(R-r(Y)) [s5:defStages] — EG: no: proposed EG.S5.demoted, EG.S5.Bad, EG.S5.dem, EG.S5.lp (s5 layer)
- *objects, decomposition* — Obj = edge | cycle (list); IsDecomp E D: WF objects, edge lists pairwise disjoint, union exactly E [s1:defObject] — EG: yes: EG.Obj, EG.Obj.WF, EG.Obj.edges, EG.IsDecomp (EG/Defs/Objects.lean)
- *constants and conditions: eps=2^-5, sigma=100, C'=103, A=105, N0, D*, Gamma1-Gamma4* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condG1..G4] — EG: no: proposed EG.epsC, EG.sigmaC, EG.Cp, EG.Aexp, EG.N0Cond, EG.Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1)
- *JConsumer, JPlusProps* — s6:defJconsumer, s6:lemJplus [s6] — EG: no: proposed
- *TPVGood; K-RED hypotheses (light-part good predicates)* — abstract conclusions of the stage-3 good events [s4:lemTPV, s5:lemChild, s5:lemDemoted, s5:lemKRED] — EG: no: proposed EG.S4.TPVGood, EG.S5.LightStage3OK (s5 blueprint)
- *eps_M, eps_K (= eps_Chain), eps_A, eps_CONC; c_KRED = 745, c_Fresh = 338* — functions of D_* only [s6:thmMIXC(c), s5:lemParent, s2:lemTower(e), s6:thmCONCL] — EG: no: proposed EG.epsM, EG.epsChain, EG.epsA, EG.epsCONC
- *Kstd, E_K* — Kstd = ⊔_l ⊔_{Z ∈ Std_l} E_l(Z); E_K = E(G) \ Kstd \ ∪_{Y light} Lentext(Y) [s5 (before lemKRED), MIX-C proof] — EG: no

**Dependencies.** Declared: `s6:consOrder`, `s4:lemTPV`, `s5:lemKRED`, `s5:lemDemoted`, `s6:lemJSLC`, `s6:lemJplus`, `s6:defJconsumer`, `s6:lemLent`, `s6:thmCONCL`, `s2:propStructure`, `s2:propParentless`, `s2:propOV`, `s2:lemTower`, `s3:defCOL`, `s3:lemCOL`, `s4:lemPV`, `s5:lemChild`, `s4:thmVXp`, `s2:defHBtp`, `s1:condG3`.  
From the proof: `s6:consOrder`, `s6:lemLent`, `s6:lemJSLC`, `s6:lemJplus`, `s6:defJconsumer`, `s6:defLending`, `s4:lemTPV`, `s5:lemKRED`, `s5:lemChild`, `s5:lemDemoted`, `s3:defCOL`, `s3:lemCOL`, `s2:propStructure`, `s2:propOV`, `s2:propParentless`, `s2:lemTower`, `s2:defHBtp`, `s6:thmCONCL`, `s1:condG3`, `s1:factAdd`.  
(a): lemLent(i),(iii), JC1, COL(g) (defCOL), (R5), TPV (T1), condG3 (P_l >= N0), lemCOL(a),(e), propStructure(i). (b): lemLent(iv) + K-RED, TPV (T3),(T4), JS-LC, JC2, J+(iii) (J_l ⊆ ∪E_l(Z) disjoint from LentJV_l ⊆ ∪E(H_Y)), propStructure(iii) (edge partition), s1:factAdd (union of decompositions; UNDECLARED). (c): K-RED cost, TPV (T3) with |Ret_Z| = |A_Z|+|F_Z|+|Lost_Z|, propOV(K2) + lemTower(e) (Σ|A_Z| <= eps_A n), propParentless(i) (K4) (Σ|F_Z| <= 2n), propStructure(iv) (Lost_Z of one round disjoint), JS-LC bound + lemTower(b) (Σ1/M_l <= 2/D_*), thmCONCL(iv). s4:lemPV and s4:thmVXp enter only through s5:lemChild/s5:lemDemoted.

**Used by:** s7:propCost, s7:thmJVps, s7:lemOneOutcome (via consOrder).

**Randomness.** none: deterministic for ANY stage-1 outcome and ANY consumer; stage-3 outcomes enter only via hypotheses (abstract good-event conclusions). The probabilistic choices (stage-1 Markov selection, stage-3 labels in good events, xi_l) are made in s7:lemOneOutcome.

**Lean shape.**

```lean
-- EG/Defs/S4 (or Chain): abstract TPV conclusion
def TPVGood (Z : Finset V) (O : FGraph V) (P : Finset V) : Prop :=
  ∀ E : Finset (Sym2 V), O.edges ⊆ E → (∀ e ∈ E, ∀ v ∈ e, v ∈ Z) →
    ∃ (EV EQ : Finset (Sym2 V)) (D : List (Obj V)), Disjoint EV EQ ∧ EV ∪ EQ = E ∧
      (∀ e ∈ E, (∀ v ∈ e, v ∈ P) → e ∈ EV) ∧ (∀ e ∈ EV, (∃ v ∈ e, v ∉ P) → e ∈ O.edges) ∧
      IsDecomp (EV : Set (Sym2 V)) D ∧ D.length ≤ 169 * P.card
-- EG/Spec/Chain/MixC.lean  (Option B, recommended)
def MixCStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : FGraph V) (N0 Dstar : ℝ) (run : HB.Run V) (δ : S6.Designation run G)
    (ω : S3.Stage1 run G), EG.N0Cond N0 → EG.GammaCond N0 Dstar → run.Valid G Dstar → N0 ≤ G.card → Dstar ≤ run.d G 1 →
    (∀ l a, a ∈ run.Std G l → S4.TPVGood (run.Z0 G l a) (S6.OZ ω l a) (S6.ret ω l a)) →
    S5.LightStage3OK ω →                              -- whatever the s5:lemKRED Spec takes
    ∀ (C : S6.JConsumer ⟨G, run, δ, ω⟩) (b : ℕ → ℝ),
    (∀ l J, 3 ≤ l → l ≤ run.R → S6.JPlusProps ω l J → ((C.out l J).1.length : ℝ) ≤ b l) →
    ∃ D : List (Obj V), IsDecomp (G.edges : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ (Dstar / 2 + 745 + 338) * G.card + EG.epsM Dstar * G.card
        + (80 * S5.dem ω + 369 * S5.lp ω + 169 * ∑ l ∈ Finset.Icc 1 run.R, ((S6.lostRound ω l).card : ℝ))
        + 1.5 * ∑ l ∈ Finset.Icc 1 run.R, ∑ Y ∈ run.allAncestors G, (δ.m Y l : ℝ)
        + ∑ l ∈ Finset.Icc 3 run.R, b l
def MixCTPVApplicable : Prop :=   -- bullet 'Lemma TPV at step (1)' of (a); used by s7:lemOneOutcome
  ∀ ... ω l a, a ∈ run.Std G l → S4.TPVHyps (run.Z0 G l a) (S6.OZ ω l a) (S6.ret ω l a)
--   (|Z0| ≥ N0, OZ spanning (ε_O, s)-expander on Z0 with ε_O ∈ [2^-7, 2^-5], s ≥ 2^150 L^42)
noncomputable def EG.epsM (D : ℝ) : ℝ := EG.epsChain D + 169 * EG.epsA D + 252 / D
-- Option A (fallback): expose `chain` (s6:consOrder) and replace Σ b l by Σ_l ((C.out l (chain l).J).1.length).
```

**Hazards.**

- **MIXC-SUMOBJ** (risk): (c) contains Σ_l |Obj_l| for the consumer's outputs on the J_l that the construction produces; stating this needs either the construction in the Spec (Option A: the chain as an epsilon-definition in Defs, heavy and fragile) or (Option B, recommended) a hypothesis that the consumer's output length is <= b_l for EVERY admissible J (JPlusProps), giving Σ_l b_l. Option B is faithful for the s7 use only if s7's per-round bounds are uniform in the past. Checked in s7.tex: payments (a1) <= (M_l-1)|Lost_l| (J2cap at lost centres), (a2)/(a3) <= round-l summand of Xpool (stage 1), unpaired fresh legs <= Σ_{Z∈Std_l}|F_Z| per round (≤ 2n in total), SDR failures + loops payrd_l <= 4E[payrd_l|Past] <= uniform bound (lemPay(c) 'for every past'), lifted objects 2f(Q_l) with |V(Q_l)| = copies_l <= 4E[copies|Past] <= 4(X_{V,l} + det_l) (lemUHsplit(ii) 'for every past'). So b_l can be a function of (run, δ, ω, l) (and of the induction constant for f(Q_l)). Decision must be made jointly with the s7 blueprint (s7:propCost, s7:lemOneOutcome, s7:thmJVps).
- **MIXC-STAGE3-ABSTRACT** (risk): Same as ORDER-STAGE3: the good events of TPV/PV/VX+ are ∃-bound in their Specs; MIX-C must take their conclusions (TPVGood etc.) as hypotheses, and bullet 'Lemma TPV at step (1)' of (a) becomes the separate Spec MixCTPVApplicable (for EVERY ω: lend-good Z uses COL(a) for Own_Z, which is part of lend-good; lend-bad Z uses X^0_Z, a (2^-5, s_l)-expander by propStructure(i); s_l/4 >= 2^150 L_Z^42 by lemCOL(e), a colouring-free inequality under Γ1). If the TPV Spec's hypotheses differ (e.g. an explicit size predicate TPVSize N instead of N >= N0, per blueprint_s1), adapt TPVHyps.
- **MIXC-COVERAGE-BOOKKEEPING** (risk): The coverage proof is a disjoint-union identity over rounds, parts, ancestors and colour classes: E(G) = E_K ⊔ ⊔_{Z∈Std} E_l(Z) ⊔ ⊔_{Y light} Lentext(Y); ⊔_l LentJS_l = ⊔_Y LentJS(Y); ⊔_l LentJV_l = ⊔_Y LentJV(Y) (needs JC1 and pairwise disjoint E(H_Y), and distinct classes for distinct l); J_l ∩ LentJV_l = ∅; E^Q \ J ⊔ J ∩ E_l(Z). Each step is 'clear' in the text but needs explicit Finset lemmas (~600 lines). IsDecomp is on Set (Sym2 V); combine via factAdd (EG.exists_isDecomp_biUnion exists).
- **MIXC-DETAILS-INTERNAL** (note): (a) and the itemized parts of (b) are statements about internal objects of the construction (Lent, Erem, H_0, E^V, E^Q, J_l). Downstream (s7:propCost, s7:thmJVps) uses only 'decomposition of E(G)' and the cost (c). Recommendation: Spec = decomposition + cost (+ MixCTPVApplicable); (a),(b) details are proof obligations (Lean lemmas in EG/Proof/Chain/MixC/). This is not a weakening of anything used; record as a T0 encoding decision.
- **MIXC-HYPS** (note): Hypotheses: GammaCond(N0, D_*) (Γ1 for lemCOL(e)/lemTower, Γ3 for |Z^0| >= N0, Γ4 only through K-RED's cKRED slack, which K-RED does not need), N0Cond, n >= N0, d_1 >= D_*. The cost uses c_KRED = 745 > exact 739 (s5:remConstants(b)); keep 745 as stated.
- **MIXC-EPSM** (note): eps_M depends on D_* only (eps_K = eps_Chain of s5:lemParent, eps_A of s2:lemTower(e)); 252/D_* = 2·126/D_* uses Σ_{l<=R} 1/M_l <= 2/D_* and the stated JS-LC constant 126 (proof gives 15).

**Effort.** ~1300 lines, difficulty 4/5. Chain & invariants (under s6:consOrder) excluded; coverage ~600; cost ~300; (a) applicability lemmas ~200; K-RED interface ~100; statement files ~100.

