# P2-U formalization blueprint: chunk s7b (s7: X_V, payments, X', E X', UH*-split, one outcome, cost, Theorem JV+*, HI'', GammaSat, main proof, non-circularity)

Manuscript: `proofs/manuscript/s7.tex` lines 881-1519 (v6, 2026-09-26; a CANDIDATE proof, AI-reviewed only). Machine-readable twin: `formal/work/p2/nodes_s7b.json` (same content, one object per label, same field names as `nodes_s6b.json`). Line numbers refer to `s7.tex`. Existing Lean names were checked against `formal/EG/**` (EG.FGraph, EG.fnum, EG.IsDecomp, EG.FinDist with expect/prob/prod/expect_prod and the Markov lemmas `two_thirds_le_prob_le_three_mul_expect`, `half_le_prob_le_four_mul_expect_and`, `exists_mem_le_mul_expect_ae`; EG.Spec.HIHyp/HIStatement, EG.hi, EG.mainInternal_of_hiHyp, EG.hiHyp_of_fintype_index, EG.Spec.MainInternal). Run/ancestor names follow blueprint_s2a (EG.HB.Run.*), J-interface and MIX-C names follow blueprint_s6b (S6.JPlusProps, S6.JConsumer, MixCStatement), s5 names follow blueprint_s5; the round-step objects (`S7.pool`, `S7.cand`, `S7.jvBad`, `S7.xiDist`, `S7.xiChosen`, `S7.quotient`, `S7.consumer`, ...) are proposals that must be matched with the s7a blueprint (s7:defPool ... s7:lemUltra). Everything else is a proposal.

## 1. Summary

| label | kind | formalization | Lean lines | diff. | worst hazard |
|---|---|---|---|---|---|
| `s7:lemVstar` | lemma | Defs EG/Defs/Quot/Xprime.lean (tCC if not already in s7a, XVl, XV) + Spec EG/Spec/Quot/Vstar.lean (VstarStatem... | 260 | 2 | blocker (M-INTEGER) |
| `s7:lemPay` | lemma | Tier-2 Spec EG/Spec/Quot/Pay.lean (PayStatement) over the s7a round-step Defs (or proof-internal lemmas, see S... | 700 | 3 | blocker (M-INTEGER) |
| `s7:defXprime` | definition | Defs EG/Defs/Quot/Xprime.lean (poolWeight, jvBadPorts, Xpool, Xprime) + API lemmas (nonnegativity, dependence ... | 90 | 1 | risk (S7-STAGE1-LAW) |
| `s7:lemEXprime` | lemma | Defs EG.S7.epsX (EG/Defs/Quot/Constants.lean) + Spec EG/Spec/Quot/EXprime.lean (EXprimeStatement); proof EG/Pr... | 360 | 3 | risk (S7-STAGE1-LAW) |
| `s7:lemUHsplit` | lemma | Defs EG.S7.detl, EG.S7.FQ, EG.eps2 (EG/Defs/Quot/Constants.lean) + Tier-2 Spec EG/Spec/Quot/UHsplit.lean (UHsp... | 850 | 4 | blocker (M-INTEGER) |
| `s7:lemOneOutcome` | lemma | No single Spec for the 'joint outcome' (it is a procedure). Split into: (1) proof lemma EG.S7.exists_stage1_se... | 160 | 2 | risk (S7-ROUNDSTEP-IN-DEFS) |
| `s7:propCost` | proposition | Defs EG.eps1, EG.C0 (EG/Defs/Quot/Constants.lean) + Tier-2 Spec EG/Spec/Quot/Cost.lean (CostStatement) + lemma... | 420 | 3 | risk (S7-MIXC-INTERFACE) |
| `s7:thmJVps` | theorem | Spec EG/Spec/Quot/JVps.lean (JVpsStatement), the statement consumed by the main assembly; proof EG/Proof/Quot/... | 300 | 3 | risk (S7-MIXC-INTERFACE) |
| `s7:thmHI` | theorem | EXISTS: Spec EG/Spec/Quot/HI.lean (EG.Spec.HIHyp, EG.Spec.HIStatement), proof EG/Proof/Quot/HI.lean (EG.hi, no... | 0 | 1 | note (HI-DONE) |
| `s7:lemGammaSat` | lemma | Spec EG/Spec/Main/GammaSat.lean (GammaSatStatement: (i) threshold mu_1, (ii) tendsto of eps1, eps2, (iii) ∀ N0... | 650 | 3 | risk (GS-LOGSTAR) |
| `s7:thmMainProof` | corollary | Proof of the locked Tier-1 target EG.Spec.MainInternal in EG/Proof/Main.lean (theorem EG.mainInternal); option... | 200 | 2 | risk (MAIN-PROPEXISTS-HYPS) |
| `s7:remNonCirc` | remark | No Lean statement. Realized by the structure: eps1/eps2/C0 are Defs functions of D only; c_EG appears only in ... | 0 | 1 | note (NONCIRC-STRUCTURAL) |

Estimated new Lean for this chunk: **~3990 lines** (Theorem HI'' already done; the largest items are lemUHsplit ~850, lemPay ~700, lemGammaSat ~650; excludes the s7a round-step construction). Hazards: 3 blocker entries (all the inherited M-INTEGER), 22 risks, 39 notes. The mathematics of all twelve items was re-derived: every inequality and constant checks (X_V: 11.48 <= 12; payments: 5.48 <= 5.5, 176 λ^-90.2 <= 1/M_l, Σ payrd <= 4n/D_* <= 9n/D_*; E X_pool: 2.37 + 0.03 = 2.4 per round; det_l: 44.7 + 32.9 <= 78, 624 + 2560 + 30400 log2 λ = F's numerator, 25·90.2 = 2255, 763184 < 2^20; cost: 745 + 338 + 2 = 1085 and the bracket <= X_U + X_pool; eps_1, eps_2 match the Gamma4 bullet list: 291.9/D and 363.6/D). No new manuscript error was found. The real risks are architectural: the MIX-C/consumer interface (per-round, J-dependent bounds), the round step as a Defs construction with an internal Markov choice, the 'joint outcome' as a procedure, one shared stage-1 law, and the unlabelled PAR multiplicity identity behind the quotient-size count.

## 2. Cross-cutting decisions proposed for the integrator

- **M_l ∈ ℕ (blocker M-INTEGER, inherited from blueprint_s2a HB-M-INTEGER).** This chunk counts colours of the palettes [3M_l] (PAR) and [4M_l] (HUB) in X_{V,l} and in the quotient size, uses the SDR bound (4M_l)^-4 and 3k_h <= 4M_l. Re-checked: with M_l := ⌈max(2^40, 2^16 T log^4 T)⌉ every inequality of this chunk holds unchanged (only M_l >= 2^40, M_l <= λ_{l-2}^1.6, M_{l-1} >= 2M_l, Σ1/M_l <= 2/D_*, Σψ(M_l) <= 2.1ψ(D_*) are used). Fallback (ceilings at each use) forces X_{V,l} to use the same ceilings.
- **MIX-C interface for the s7 consumer (S7-MIXC-INTERFACE; joint with s6b MIXC-SUMOBJ).** Recommended Option B': MIX-C takes a J-DEPENDENT per-round bound `b : ℕ → Finset (Sym2 V) → ℝ` valid for every admissible J (JPlusProps) and concludes `∃ Js admissible, ∃ D, IsDecomp E(G) D ∧ D.length ≤ ... + Σ_{l∈[3,R]} b l (Js l)`. For the s7 consumer `b l J := (M_l − 1)|Lost_l| + Xpool_l(ω) + Σ_{Z∈Std_l}|F_Z| + 2n/M_l + 2 fnum(Q_l(ω,J))`; then Q_l := quotient ω l (Js l) serves both conclusions of Theorem JV+*. Option B of s6b (J-independent b_l) also works, via b_l := max over the finite set of admissible J and Q_l := quotient at a maximizer (the copies bound is uniform in J). Verified that every per-round bound of this chunk is uniform in the past (lemPay (a1)-(d), lemUHsplit(ii)), so either option is faithful.
- **The J-consumer is a deterministic function of (ω, l, J) (S7-ROUNDSTEP-IN-DEFS, remNonCirc(3)).** The round randomness xi_l is resolved inside: `xiChosen ω l J := if h : ∃ ξ, 0 < (xiDist l).w ξ ∧ markovEvent ω l J ξ then Classical.choose h else default`; lemOneOutcome(3) proves the condition for every (ω, l, J) with JPlusProps. Decide with s7a whether the round step lives in Defs (needed if lemPay/lemUHsplit/propCost/lemOneOutcome get Specs; recommended as Tier-2 Specs) or only in Proof (then only thmJVps, lemVstar, lemEXprime, lemGammaSat are Specs).
- **lemOneOutcome is not one Lean statement (OO-PROCEDURAL).** It becomes (1) `exists_stage1_selected` (ω of positive weight with X' <= 3E X'), (2) nothing (the s4/s5 Specs are deterministic, blueprint_s4 TPV/PV/VX-DET-SPEC), (3) `xiChosen_mem`. Record as a T0 encoding decision.
- **Per-round forms of the payment bounds (PAY-PER-ROUND).** State lemPay(b),(d) per round (unpaired fresh legs <= Σ_{Z∈Std_l}|F_Z|, payrd_l <= 2n/M_l) as well as the manuscript's totals (<= 2n, <= 9n/D_*).
- **One stage-1 law (S7-STAGE1-LAW).** A single `S3.stage1Dist run G` (1a-1d) shared by s5/s6/s7 (the s5 blueprint calls it `stage1Law`); pool-label law with a dite guard and a characterization lemma under the hypotheses; all selections return ω ∈ supp.
- **Hypothesis bundle.** `S7Hyp N0 Dstar G run := Gamma1 Dstar ∧ Gamma2a Dstar ∧ Gamma3 N0 Dstar ∧ N0Cond N0 ∧ N0 ≤ G.card ∧ Dstar ≤ run.d G 1 ∧ run.Valid G Dstar   -- no Gamma4 (only lemUHsplit(iv)'s '≤ 1/4', propCost's '≤ D/2+1091' and thmJVps use it)`. Gamma4 appears only in GammaCond for thmJVps (theta_Q <= 1/4), in `C0_le`, and in thmMainProof.
- **Constants file.** `EG/Defs/Quot/Constants.lean`: epsX, detl, FQ, eps2, eps1, C0 (and Gamma4, GammaCond, cEG after them; blueprint_s1 CONST-LAYERING). The Gamma4 bullet list of s1:condGamma is a summary; the Lean formulas are exactly those of s7.tex l.1007 (eps_X), l.1055-1075 (det_l, F, eps_2), l.1239 (eps_1).
- **Unlabelled statement to label (S7-UNLABELLED-PAR-MULT).** '[w] is non-isolated in exactly max_{w'} m_kappa(w,w') PAR sub-layers' (s7.tex l.711-713) is used by lemCC(iii) and lemUHsplit(ii): make it a named lemma (chunk s7a) and require the rank tag in the quotient's vertex type.
- **Theorem HI'' is done** (EG.hi, approved). The remaining interface work is producer-side: Fintype adapter and d_1 = run.d G 1 (JV-FINTYPE-ADAPTER).
- **Undeclared dependencies found in proofs** (for msreport): lemVstar uses s7:lemCC (definition of t^CC_l), s2:defAncestors, s2:defHBtp; lemPay uses s7:defCand (H^cd_l), s6:defDesign (c^agg), s6:defLending, s2:propStructure, s2:defHBtp; defXprime uses s7:defCand, s7:defPool, s6:defDesign; lemEXprime uses s7:defPool, s6:defDesign, s2:defHBtp; lemUHsplit uses s7:defCand, s7:defXprime and the unlabelled PAR-MULT identity; lemOneOutcome uses s6:thmMIXC(a), s7:defXprime; propCost none beyond its list; thmJVps uses s1:defObject; lemGammaSat uses s5:lemParent (eps_Chain); thmMainProof uses s1:thmMain, s2:defAncestors. Declared but not logically used: s7:lemEXprime in lemOneOutcome; s3:lemCOL, s5:lemE1 in lemGammaSat; s2:propExists in thmJVps (pointer); s1:defConstants in thmHI (names only).
- **Modules.** Defs: `EG/Defs/Quot/Xprime.lean` (tCC if not in s7a, XVl, XV, poolWeight, jvBadPorts, Xpool, Xprime), `EG/Defs/Quot/Constants.lean`. Specs: `EG/Spec/Quot/{Vstar, EXprime, JVps}.lean` (Tier-1 chain), `EG/Spec/Quot/{Pay, UHsplit, Cost, OneOutcome}.lean` (Tier-2, over the s7a Defs), `EG/Spec/Main/GammaSat.lean`; existing `EG/Spec/Quot/HI.lean`, `EG/Spec/Main.lean`. Proofs: `EG/Proof/Quot/{Vstar, Pay, EXprime, UHsplit/*, OneOutcome, Cost, JVps}.lean`, `EG/Proof/Main/GammaSat.lean`, `EG/Proof/Main.lean`.

## 3. Hazard index (all nodes, most severe first)

| severity | label | node | summary |
|---|---|---|---|
| blocker | M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a) | `s7:lemVstar` | M_l is a REAL in (R2), but this chunk uses it as a NUMBER OF COLOURS: the copy counts of lemVstar/lemUHsplit sum over the 3M_l PAR colours and the 4M_l HUB colours ('summing over the 4M_l HUB colours'... |
| blocker | M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a) | `s7:lemPay` | M_l is a REAL in (R2), but this chunk uses it as a NUMBER OF COLOURS: the copy counts of lemVstar/lemUHsplit sum over the 3M_l PAR colours and the 4M_l HUB colours ('summing over the 4M_l HUB colours'... |
| blocker | M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a) | `s7:lemUHsplit` | M_l is a REAL in (R2), but this chunk uses it as a NUMBER OF COLOURS: the copy counts of lemVstar/lemUHsplit sum over the 3M_l PAR colours and the 4M_l HUB colours ('summing over the 4M_l HUB colours'... |
| risk | S7-STAGE1-LAW | `s7:lemVstar` | X' mixes all four stage-1 families (X_U: 1a-1c incl. zones; X_pool: pool labels 1d and JV-badness, which depends on the LJV colours 1a AND on the pool labels 1d; X_V: 1d only), and E X' is taken under... |
| risk | S7-ROUNDSTEP-IN-DEFS | `s7:lemPay` | lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get lock... |
| risk | PAY-PER-ROUND | `s7:lemPay` | (b) and (d) are stated in the manuscript as totals over rounds ('at most 2n', 'Σ payrd <= 9n/D_*'), but the MIX-C interface (Option B/B', S7-MIXC-INTERFACE) consumes a PER-ROUND bound b_l(J). The per-... |
| risk | PAY-E-INSPECTION | `s7:lemPay` | (e) 'no other item is paid' is a claim by inspection of the construction. In Lean it must be a property of the Defs (the paid set is DEFINED as the union of the six categories, and Obj_l = paid single... |
| risk | PAY-C-CONDITIONING | `s7:lemPay` | (c) needs: the xi_l law as a product lists × orders (Fubini: EG.FinDist.expect_prod); the fact from s7a that, with the lists fixed, the junction of an end in E'(u) is uniform on Cand_l(u) \ Used(u) an... |
| risk | S7-STAGE1-LAW | `s7:defXprime` | X' mixes all four stage-1 families (X_U: 1a-1c incl. zones; X_pool: pool labels 1d and JV-badness, which depends on the LJV colours 1a AND on the pool labels 1d; X_V: 1d only), and E X' is taken under... |
| risk | S7-STAGE1-LAW | `s7:lemEXprime` | X' mixes all four stage-1 families (X_U: 1a-1c incl. zones; X_pool: pool labels 1d and JV-badness, which depends on the LJV colours 1a AND on the pool labels 1d; X_V: 1d only), and E X' is taken under... |
| risk | S7-ROUNDSTEP-IN-DEFS | `s7:lemUHsplit` | lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get lock... |
| risk | S7-UNLABELLED-PAR-MULT | `s7:lemUHsplit` | The identity '[w] is not isolated in exactly max_{w'} m_kappa(w,w') of the PAR sub-layers B^{P,(iota)}_kappa' is stated only in the unlabelled preamble of the subsection 'Quotient size and payments' (... |
| risk | UH-VERTEX-DECOMP | `s7:lemUHsplit` | (ii) rests on an exact identity \|V(Q_l)\| = Σ_{kappa∈[3M_l]} Σ_{w∈Pool_l} max_{w'} m_kappa(w,w') + Σ_{kappa∈[4M_l]} (Σ_{h∈D_l} max_w m_kappa(h,w) + Σ_{w∈Pool_l} max_h m_kappa(h,w)), i.e. the quotient... |
| risk | UH-AVERAGE-LISTS | `s7:lemUHsplit` | 'Averaging over the lists gives (ii)': PAR copies and ultra-hub copies are bounded CONDITIONALLY on the lists (lemCC(iii), lemUltra(iv) hold for every outcome of the lists), non-ultra-hub and HUB-junc... |
| risk | UH-NUMERICS-F | `s7:lemUHsplit` | (iv) needs real-exponent analysis of F(x) = (3184 + 30400 log2 x) x^-90.2: F decreasing on [2^25, ∞) (derivative sign: 30400/ln 2 < 90.2 (3184 + 30400 log2 x)), F(2x) <= F(x)/2 (first factor at most d... |
| risk | S7-ROUNDSTEP-IN-DEFS | `s7:lemOneOutcome` | lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get lock... |
| risk | OO-PROCEDURAL | `s7:lemOneOutcome` | The lemma asserts the existence of a JOINT outcome built by a sequential procedure whose later steps depend on earlier choices (J_l depends on xi_{l'} for l' > l through the decompositions and junk). ... |
| risk | OO-SUPP | `s7:lemOneOutcome` | Step (i) must return an ω of POSITIVE weight: the s5 Specs (K-RED, Child, blueprint_s5) and hence MIX-C quantify ω ∈ supp. The manuscript's Markov step gives an event of probability >= 2/3; EG.FinDist... |
| risk | S7-MIXC-INTERFACE (joint with s6b MIXC-SUMOBJ) | `s7:propCost` | MIX-C Option B of blueprint_s6b bounds the consumer output by a J-INDEPENDENT b_l for every admissible J. The s7 consumer's output length is paid(J) + (lifted objects) <= [uniform stage-1/run bound] +... |
| risk | S7-ROUNDSTEP-IN-DEFS | `s7:propCost` | lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get lock... |
| risk | S7-MIXC-INTERFACE (joint with s6b MIXC-SUMOBJ) | `s7:thmJVps` | MIX-C Option B of blueprint_s6b bounds the consumer output by a J-INDEPENDENT b_l for every admissible J. The s7 consumer's output length is paid(J) + (lifted objects) <= [uniform stage-1/run bound] +... |
| risk | JV-SAME-Q | `s7:thmJVps` | (1) and (2) must hold for the SAME family Q_3..Q_R. Under MIX-C Option B' the J_l's of the actual chain are exposed and Q_l := quotient ω l J_l works for both; under Option B (J-independent b_l) one m... |
| risk | GS-LOGSTAR | `s7:lemGammaSat` | eps_CONC -> 0 needs log* D = o(log2 log2 D) (for the term 200 eps log*D/(C' log log D)) and log* D = o((log2 D)^{1/2}); this is a genuine growth lemma for log* (e.g. log* x <= 2 + log2 log2 x for x >=... |
| risk | GS-COLJV-COUPLING | `s7:lemGammaSat` | Item (f) of Gamma1 is the 18 column-3 inequalities of Table s3:tabCOLJV (a table, not a statement). GammaCond's (f)-part, s3:lemCOLJV's use of it, and s3:lemCOLJVev(iii)'s eventual form must all refer... |
| risk | MAIN-PROPEXISTS-HYPS | `s7:thmMainProof` | s2:propExists says 'for every graph G a valid run exists', but its proof uses lemCap(ii), propOV, propDegRec, which need d_l >= D_* and Gamma1/Gamma2a (termination: d_{l+1} < d_l while d_l >= D_*). It... |
| note | VSTAR-TCC-DEF | `s7:lemVstar` | t^CC_l is introduced inside the statement of s7:lemCC(iii) (chunk s7a) but used in the DEFINITION of X_{V,l}. It must be one Defs constant (EG.S7.tCC) used by both, else lemCC's PAR-copy bound and X_{... |
| note | VSTAR-POOL-MARGINAL | `s7:lemVstar` | The proof needs, for every w and every (l,r), P(plab(w) = (l,r)) = q_l pi_{l,r} (exact, or <=), hence E\|Pool_l\| <= n/M_l^2 and E Σ_{w∈Pool_l} mult_{r(w)}(w) <= q_l Σ_r pi_{l,r} Σ_w mult_r(w). With t... |
| note | VSTAR-SUM-RANGE | `s7:lemVstar` | lemTower(b) sums psi(M_l) over l <= R (from l = 1); X_V sums over l ∈ [3,R]. Use Finset.sum_le_sum_of_subset_of_nonneg (psi(M_l) >= 0 since M_l >= 2^40). The stated constant 12 has slack over the prov... |
| note | PAY-A1-ONE-LOST-END | `s7:lemPay` | (a1) counts J^lost edges by their lost end; needs (i) Q*_Z ∩ Lost_Z = ∅ (s6:defLending API), (ii) a lost vertex lies in exactly one round-l pre-part (it is outside D_l), so J2cap per part is a per-ver... |
| note | PAY-A2-HUB-ITEMS | `s7:lemPay` | (a2) at a pooled hub v ∈ D_l needs: items at v are exactly J^hub edges (types + J3: hubs are never ports, fresh or lost centres), J1hub aggregated over all parts of round l, and d_{Y,l}(v) >= 1 for ea... |
| note | PAY-D-NUMERICS | `s7:lemPay` | (d) uses real-exponent arithmetic: M_l <= lambda^1.6, lambda >= (2^40)^(1/1.6) = 2^25, 176 lambda^-90.2 <= lambda^-1.6 <= 1/M_l (rpow lemmas; small absolute constants only). 4n/(256 M^3) <= n/M since ... |
| note | XP-NAME-CLASH | `s7:defXprime` | The manuscript's omega_l(v) (weight) and the stage-1 outcome ω collide in Lean; name the weight poolWeight. It is defined inside the statement of s7:lemPay(a2); both lemPay and defXprime must referenc... |
| note | XP-JVBAD-LAW | `s7:defXprime` | JV-badness compares \|Cand_l(u)\| with (1/2) E\|Cand_l(u)\|, an expectation under the stage-1 law. Hence X' (a Defs object) depends on the law S3.stage1Dist itself, and E X' is an expectation of a fun... |
| note | XP-RANGES | `s7:defXprime` | Σ_l in X_pool is over l ∈ [3,R] (explicit); X_U sums over l ∈ [1,R] (blueprint_s6b LEND-XU-RANGE; Lost_l = ∅ for l <= 2). Classed ports of round l include LOST ports: JV-badness is counted for every c... |
| note | XP-M-MINUS-ONE | `s7:defXprime` | (M_l - 1) as a real (cast) avoids truncated subtraction; with M_l ∈ ℕ (M-INTEGER) cast before subtracting. |
| note | EXP-CAGG-DOUBLECOUNT | `s7:lemEXprime` | Σ_{h∈D_l} c^agg_{h,l} <= Σ_h Σ_Y d_{Y,l}(h) = #{(h, u): hu ∈ E_l(Z), Z ∈ Std_l, u ∈ Q_Z} = Σ_Z Σ_{u∈Q_Z} deg_{E_l(Z)}(u) is a double count over ordered pairs; needs the edge sets E_l(Z) of distinct Z ... |
| note | EXP-JVBAD-EXP | `s7:lemEXprime` | exp(-H^cd_l/4) <= M_l^-3 with H^cd_l >= 2^10 M_l^10: use exp(-y) <= 1/y (y > 0): exp(-H/4) <= 4/H <= 4/(2^10 M^10) <= M^-3. Real.exp lemmas only; no galactic evaluation. |
| note | EXP-HYPS | `s7:lemEXprime` | The statement has no hypotheses in the text; the proof needs those of s6:lemLost/s5:lemExpect (S5Hyp: Gamma1, Gamma3, N0Cond, n >= N0, d_1 >= D_*, valid run) and lemCap (Gamma2a: D_* >= 2^117). Use S7... |
| note | UH-DET-TERMS | `s7:lemUHsplit` | Re-derived: 78 n M_l/H^cd_l = 624 n M_l^3/λ^95; with log2 thult_l <= log2(M_l H^cd_l/7) = log2(λ^95/(56 M_l)) <= 95 log2 λ the last two det terms are <= n M_l^3 (624 + 2560 + 30400 log2 λ)/λ^95 <= n F... |
| note | UH-GAMMA4 | `s7:lemUHsplit` | theta_Q <= 1/4 is literally Gamma4; '2F(log2 D_*) < 2^-1000' is never used. The Spec should state the bound with eps2 Dstar and leave '<= 1/4' to Gamma4 (the manuscript's 'theta_Q <= 1/4 by condition ... |
| note | UH-SAME-OUTCOME | `s7:lemUHsplit` | (iii) needs the Markov event at EVERY round for the J_l actually fed to the consumer; with the J-consumer defined via xiChosen (dite on nonemptiness) this is the per-(ω, l, J) fact lemOneOutcome(3), s... |
| note | OO-STAGE3-DETERMINISTIC | `s7:lemOneOutcome` | With the deterministic TPV/PV/VX+ Specs (blueprint_s4), '(2) the stage-3 labels lie in the good events' has no Lean content beyond 'the deterministic conclusions hold for (Z^0, O_Z ω, Ret_Z ω) and the... |
| note | OO-MARKOV-ZERO | `s7:lemOneOutcome` | Markov with E X = 0 (possible in degenerate cases, e.g. no ports) is handled by the existing FinDist lemmas (they assume only X >= 0 on the support). |
| note | OO-UNDECL | `s7:lemOneOutcome` | Uses s6:thmMIXC(a) (TPV applicability) and s7:defXprime (X' >= 0), undeclared; s7:lemEXprime declared, unused. |
| note | COST-BRACKET | `s7:propCost` | The bracket identity needs MIX-C's [80 dem + 369 lp + 169 Σ_l \|Lost_l\|] to be stated with the SAME S5.dem, S5.lp, S6.lostRound as S6.XU (blueprint_s6b's MixCStatement does), and (169 + M_l - 1) <= (... |
| note | COST-OPTIMAL-DEC | `s7:propCost` | 'lifted objects <= 2\|Dec_l\| = 2 f(Q_l)' needs Dec_l to be an OPTIMAL decomposition of E(Q_l); in the Defs pick it with EG.exists_isDecomp_length_eq_fnum (Classical.choose) — the manuscript's 'lexico... |
| note | COST-FRESH-TWICE | `s7:propCost` | Σ\|F_Z\| <= 2n (K4) is used twice, legitimately: once for the TPV cost 169 Σ(\|A_Z\| + \|F_Z\| + \|Lost_Z\|) (the 338) and once for the unpaired fresh legs (the 2). Both appear in 1085 = 745 + 338 + 2... |
| note | COST-EPS1-NONNEG | `s7:propCost` | eps_1 >= 0 (needed for C_0 >= D_*/2 in thmMainProof/HI) holds only for large D (log2 log2 D > 0 for eps_A, and eps_Chain's inner log2(2A log2(A log2 log2 D)) >= 0); prove from Gamma1core, do not assum... |
| note | JV-FINTYPE-ADAPTER | `s7:thmJVps` | EG.Spec.HIHyp quantifies over V : Type WITHOUT Fintype (FGraph carries its vertex Finset), while the stage-1 and xi_l laws (FinDist.pi over vertices) need [Fintype V]. thmMainProof must restrict G to ... |
| note | JV-QTYPE | `s7:thmJVps` | W l must be in Type (HIHyp's universe): S7.QVert V := (Bool × ℕ × ℕ) × V is. The rank tag is mandatory (S7-UNLABELLED-PAR-MULT). HUB sub-layers identify [w] with w: fine because h ∉ Pool_l ∋ w (lemSim... |
| note | JV-HYPS | `s7:thmJVps` | The text says 'Assume D_* satisfies Gamma1-Gamma4', n >= N0, d_1 >= D_*. Gamma4 is used only for theta_Q <= 1/4 (and C_0 <= D_*/2 + 1091), so taking GammaCond (all four) is faithful; N0Cond is implici... |
| note | JV-ULTRA-PROSE | `s7:thmJVps` | The closing sentences about ultra hubs are commentary (lemPay(e) + lemUltra); not part of the Spec. |
| note | HI-DONE | `s7:thmHI` | Formalized, proved without sorry and approved in P1b (hi.review1.md). No change needed. The only interface work left is on the producer side (JV-FINTYPE-ADAPTER in s7:thmJVps: HIHyp's G has no Fintype... |
| note | HI-ISOLATED-UNUSED | `s7:thmHI` | The hypothesis gives 'G without isolated vertices' but thmJVps does not need it; harmless (the producer ignores it). |
| note | GS-TYPEE-REDUCTIONS | `s7:lemGammaSat` | Checked: (b) 2^mu >= 2^14·105·mu^3 <=> mu >= 14 + log2 105 + 3 log2 mu, implied by mu - (14 + log2 A) - 3 log2(A mu) >= 0 since log2 mu <= log2(A mu) for mu >= 1; (d) likewise; (e) log2 of both sides ... |
| note | GS-NONNEG | `s7:lemGammaSat` | thmMainProof/HI need C_0 >= D_*/2 (eps_1 >= 0) and theta_Q >= 0 (eps_2 >= 0). In Lean, logb of numbers in (0,1) is negative, so these are NOT true for all D; they hold under Gamma1core (log2 log2 D >=... |
| note | GS-GAMMA3-N0 | `s7:lemGammaSat` | Gamma3 (log2 D)^103 >= 2 N0 is eventual in D for every real N0 (take D >= 2^{max(0,2N0)^{1/103}}); quantifier order ∀ N0, ∀ᶠ D matches s1:remOrder (N0 before D_*). No condition involves c_EG. |
| note | GS-UNDECL | `s7:lemGammaSat` | eps_K = eps_Chain is DEFINED in s5:lemParent (undeclared dependency); s3:lemCOL, s5:lemE1 declared but not used. |
| note | MAIN-FINTYPE-D1 | `s7:thmMainProof` | HIHyp gives G : FGraph V on V : Type without Fintype and 'Dstar ≤ 2\|E\|/n'; thmJVps needs Fintype V and 'Dstar ≤ run.d G 1'. Adapter: subtype ↥G.verts + EG.fnum_map, and the s2 API lemma run.d G 1 = ... |
| note | MAIN-DESIGNATION-EXISTS | `s7:thmMainProof` | A designation must exist as a Lean term: define δ.cls l u := if h : (run.anc G l u).Nonempty then h.choose else default, and prove validity from 'u classed ⇒ anc_l(u) ≠ ∅'. The manuscript's 'fixed rul... |
| note | MAIN-CONST-NONNEG | `s7:thmMainProof` | mainInternal_of_hiHyp needs D/2 ≤ C0 D, 0 ≤ eps2 D, eps2 D < 1/2: from GS-NONNEG (under Gamma1core) and Gamma4 (eps2 ≤ 1/4). |
| note | MAIN-EXPLICIT-OPTIONAL | `s7:thmMainProof` | The locked target only asserts ∃ c. The explicit c_EG (and 1085/1091) is machine-checked only if MainExplicit is also stated; recommended as Tier-2 (blueprint_s1 MAIN-EXISTENTIAL). |
| note | NONCIRC-STRUCTURAL | `s7:remNonCirc` | Nothing to prove; the claims become syntactic properties of the Lean development (quantifier order in HI, Defs of eps1/eps2 as functions of D only, the module DAG). Point (3) is exactly the design dec... |
| note | NONCIRC-JUNK | `s7:remNonCirc` | 'Q_l depends on Dec_{l'} through junk': junk junction edges of round l' stay in Erem(Y) of their owner and can change the TPV split, hence E^Q(Z) and J_l of LATER-processed rounds; in Lean this depend... |

## 4. Nodes

### `s7:lemVstar` — lemma: The stage-1 weight X_V (s7.tex:881)

**Status:** x2+RT. **Formalization:** Defs EG/Defs/Quot/Xprime.lean (tCC if not already in s7a, XVl, XV) + Spec EG/Spec/Quot/Vstar.lean (VstarStatement); proof EG/Proof/Quot/Vstar.lean

**Statement (precise restatement).** Setting (implicit in the text, needed by the proof): G a finite simple graph with vertex set V(G), n = |V(G)|; a valid HB*^{tau+} run with d_1 >= D_*, Gamma1(D_*) (lemTower), and n >= N0 (propOV/propStructure); the stage-1 law, of which only the pool labels (s7:defPool) matter. For every round l with 3 <= l <= R define t^CC_l := ceil(2 log2 M_l) ∈ ℕ (defined in s7:lemCC(iii)) and X_{V,l} := 3 M_l (t^CC_l + 1) |Pool_l| + 4 M_l Σ_{w ∈ Pool_l} mult_{r(w)}(w), where Pool_l = {w ∈ V(G): plab(w) = (l,r) for some 1 <= r <= l-2}, r(w) is that r, and mult_r(w) = number of ancestors of round r whose vertex set contains w; X_V := Σ_{l=3}^{R} X_{V,l} (0 if R < 3). Claims: (a) each X_{V,l} is a deterministic function of the run and of the pool labels (plab(v))_{v ∈ V(G)} alone; (b) for every 3 <= l <= R, E X_{V,l} <= (6 log2 M_l + 12) n / M_l; (c) E X_V <= 2.1 (6 log2 D_* + 12) n / D_*. E is over the stage-1 law. (The proof gives the constant 11.48 in (b).)

**Definitions needed.**

- *valid run and round data: run.Valid G Dstar, R, d_l, lambda_l = log2 d_l, M_l, P_l, D_l, Std_l, Z^0, E_l(Z), pre-part addresses* — s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T_l log2^4 T_l), T_l = d_l log2^2 d_l (a REAL in the manuscript; see blocker M-INTEGER); D_l = vertices in >= 2 round-l pre-parts; R = last round with d_R >= D_* [s2:defHBtp] — EG: no: proposed EG.HB.Run / Run.Valid / run.d / run.M (HB.MOf) / run.D / run.Std / run.Z0 / run.E (blueprint_s2a)
- *ancestors Y = (r, address), V(Y), H_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z; mu_r(w), mult_r(w)* — s2:defAncestors: one ancestor per pre-part (light part or standalone pre-part); anc_l(x) = ancestors of rounds <= l-2 containing x; Q_Z = U_Z \ F_Z; mult_r(w) = #ancestors of round r whose vertex set contains w; mu_r(w) = #round-r pre-parts containing w [s2:defAncestors] — EG: no: proposed run.ancVerts / anc / hubs / ports / fresh / classed / mu / mult (blueprint_s2a)
- *pool labels plab(v), q_l, pi_{l,r}, Pool_{l,r}, Pool_l, r(w)* — s7:defPool: plab(v) in {bot} u {(l,r): 3 <= l <= R, 1 <= r <= l-2}, independent over v, P(plab(v) = (l,r)) = q_l pi_{l,r}, q_l = M_l^-2, pi_{l,r} = 2^-(l-1-r); Pool_l = plab^-1({l} x [1,l-2]); r(w) = second coordinate [s7:defPool (chunk s7a)] — EG: no: proposed EG.S7.plab (a field of the Stage1 outcome), EG.S7.pool omega l, EG.S7.poolRound omega w (EG/Defs/Quot/Pool.lean, chunk s7a)
- *t^CC_l* — ceil(2 log2 M_l) ∈ ℕ [s7:lemCC(iii) (chunk s7a; defined inside a lemma statement)] — EG: no: proposed EG.S7.tCC (Defs; shared with lemCC)
- *X_{V,l}, X_V* — as in the statement [s7:lemVstar] — EG: no: proposed EG.S7.XVl ω l, EG.S7.XV ω : ℝ
- *psi(x) = (6 log2 x + 12)/x* — the function summed in lemTower(b) [s2:lemTower(b)] — EG: no: proposed EG.HB.psi (s2 layer)
- *stage-1 outcome omega and its law (families 1a COL-JV colourings, 1b zones, 1c JS labels, 1d pool labels)* — s7:defSchedule stage 1: four mutually independent label families, one joint finite law; every stage-1 quantity (X_U, X_pool, X_V, JV-bad, Pool_l) is a function of omega [s7:defSchedule, s3:defCOL, s5:defZones, s7:defPool] — EG: partly: EG.FinDist (pi, prod, ofFinset, expect, Markov lemmas) exists; the Stage1 type/law is proposed in the s3 layer (blueprint_s6b calls it S3.stage1Dist, blueprint_s5 calls it stage1Law: names must be unified)
- *finite probability, expectation, Markov, Fubini* — s1:citMarkov [s1:citMarkov] — EG: yes: EG.FinDist, FinDist.expect, prob, prod/pi/compProd, expect_prod (Fubini), two_thirds_le_prob_le_three_mul_expect, half_le_prob_le_four_mul_expect_and, exists_mem_le_mul_expect_ae (EG/Defs/Prob/FinDist.lean, EG/Lib/Prob/Basic.lean)

**Dependencies.** Declared: `s7:defPool`, `s2:propOV`, `s2:lemTower`.  
From the proof: `s7:defPool`, `s7:lemCC`, `s2:propOV`, `s2:lemTower`, `s2:defAncestors`, `s2:defHBtp`.  
(a): M_l, t^CC_l, mult_r from the run (s2:defHBtp, s2:defAncestors); Pool_l, r(w) from the pool labels (s7:defPool). (b): t^CC_l + 1 <= 2 log2 M_l + 2 (ceil); E|Pool_l| = n q_l (1 - 2^-(l-2)) <= n/M_l^2 (s7:defPool law); E Σ_{w∈Pool_l} mult_{r(w)}(w) = q_l Σ_{r<=l-2} pi_{l,r} Σ_w mult_r(w) <= q_l · 1.37 n by propOV (F11) (Σ_w mult_r(w) <= 1.37 n for every round r <= R) and Σ_r pi_{l,r} < 1; total (6 log2 M_l + 11.48) n/M_l. (c): lemTower(b) Σ_{l<=R} psi(M_l) <= 2.1 psi(D_*) (the sum over l ∈ [3,R] is a sub-sum of nonnegative terms). Undeclared: s7:lemCC (definition of t^CC_l), s2:defAncestors (mult), s2:defHBtp (M_l). Declared s7:defPool is used (the JSON 'declared_but_unreferenced' flag is a \ref artefact).

**Used by:** s7:defXprime, s7:lemEXprime, s7:lemUHsplit.

**Randomness.** Sample space: the stage-1 outcome; X_{V,l} depends only on family 1d, the pool labels plab(v), v ∈ V(G), independent across v with P(plab(v) = (l,r)) = q_l pi_{l,r} (3 <= l <= R, 1 <= r <= l-2) and P(bot) = the rest. Unconditional expectation; nothing is conditioned on. Only the per-vertex marginals and linearity of expectation are used (no independence needed).

**Lean shape.**

```lean
-- EG/Defs/Quot/Xprime.lean   (namespace EG.S7; ω : S3.Stage1 run G carries ω.plab : V → Option (ℕ × ℕ))
noncomputable def tCC (run G) (l : ℕ) : ℕ := ⌈2 * Real.logb 2 (run.M G l)⌉₊            -- shared with s7:lemCC
noncomputable def XVl (ω) (l : ℕ) : ℝ :=
  3 * run.M G l * (tCC run G l + 1) * (S7.pool ω l).card
  + 4 * run.M G l * ∑ w ∈ S7.pool ω l, (run.mult G (S7.poolRound ω w) w : ℝ)
noncomputable def XV (ω) : ℝ := ∑ l ∈ Finset.Icc 3 run.R, XVl ω l
-- EG/Spec/Quot/Vstar.lean
def VstarStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V),
    S7Hyp N0 Dstar G run →
    (∀ ω ω' : S3.Stage1 run G, ω.plab = ω'.plab → ∀ l, XVl ω l = XVl ω' l) ∧                     -- (a)
    (∀ l ∈ Finset.Icc 3 run.R, (S3.stage1Dist run G).expect (fun ω => XVl ω l)
        ≤ (6 * Real.logb 2 (run.M G l) + 12) * G.card / run.M G l) ∧                             -- (b)
    (S3.stage1Dist run G).expect XV ≤ 2.1 * (6 * Real.logb 2 Dstar + 12) * G.card / Dstar          -- (c)
-- (a) is definitional (XVl reads only ω.plab); keep it as a one-line lemma rather than a Spec conjunct if preferred.
```

**Hazards.**

- **M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a)** (blocker): M_l is a REAL in (R2), but this chunk uses it as a NUMBER OF COLOURS: the copy counts of lemVstar/lemUHsplit sum over the 3M_l PAR colours and the 4M_l HUB colours ('summing over the 4M_l HUB colours'), lemPay(c) uses the SDR bound (4M_l)^-4 for lists in [4M_l] = [K^HUB_l], lemUHsplit(ii) uses 3k_h <= 4M_l, and (M_l - 1) is a J-edge cap. A Lean statement needs the manuscript decision proposed in blueprint_s2a (M_l := ceil(max(2^40, 2^16 T log2^4 T)) in N). Checked for this chunk: every inequality survives with integer M_l, because the chunk uses only M_l >= 2^40, M_l <= lambda_{l-2}^1.6, M_{l-1} >= 2M_l, sum_l 1/M_l <= 2/D_*, sum_l psi(M_l) <= 2.1 psi(D_*) (lemTower(b), re-checked by the s2a blueprint for the ceiling) and exact integer identities that do not involve M_l's value. Fallback without manuscript change: [ceil(3M_l)], [ceil(4M_l)] colours; then 3M_l, 4M_l in X_{V,l} must become the same ceilings (X_{V,l} is a stage-1 functional, its definition must match the palette size exactly).
- **S7-STAGE1-LAW** (risk): X' mixes all four stage-1 families (X_U: 1a-1c incl. zones; X_pool: pool labels 1d and JV-badness, which depends on the LJV colours 1a AND on the pool labels 1d; X_V: 1d only), and E X' is taken under ONE joint law. The joint law (product of 1a-1d) must be a single Defs object used by s5 (dem, lp, lemExpect), s6 (lemLost), s7a (lemCand) and this chunk; the blueprints currently use two names (S3.stage1Dist in s6b, stage1Law in s5). The pool-label law is a probability distribution only because sum_l q_l(1 - 2^-(l-2)) <= sum_l M_l^-2 < 1, which is lemTower(b) for VALID runs (same issue as s5 ZONE-LAW-WELLDEF): define it with a dite fallback and prove the characterization P(plab v = (l,r)) = q_l pi_{l,r} under S7Hyp. Also: s5 Specs (K-RED, Child) quantify ω ∈ supp, so the selected stage-1 outcome must have positive weight.
- **VSTAR-TCC-DEF** (note): t^CC_l is introduced inside the statement of s7:lemCC(iii) (chunk s7a) but used in the DEFINITION of X_{V,l}. It must be one Defs constant (EG.S7.tCC) used by both, else lemCC's PAR-copy bound and X_{V,l} could silently use different t. Undeclared dependency lemVstar -> lemCC (definition only).
- **VSTAR-POOL-MARGINAL** (note): The proof needs, for every w and every (l,r), P(plab(w) = (l,r)) = q_l pi_{l,r} (exact, or <=), hence E|Pool_l| <= n/M_l^2 and E Σ_{w∈Pool_l} mult_{r(w)}(w) <= q_l Σ_r pi_{l,r} Σ_w mult_r(w). With the dite-guarded pool law (S7-STAGE1-LAW) this is a characterization lemma under S7Hyp, proved once in s7a. The vertex set is V(G) = G.verts; if the Stage1 type draws labels for all of V (Fintype V), Pool_l must be intersected with G.verts, or the count n becomes |V|.
- **VSTAR-SUM-RANGE** (note): lemTower(b) sums psi(M_l) over l <= R (from l = 1); X_V sums over l ∈ [3,R]. Use Finset.sum_le_sum_of_subset_of_nonneg (psi(M_l) >= 0 since M_l >= 2^40). The stated constant 12 has slack over the proved 11.48.

**Effort.** ~260 lines, difficulty 2/5. Defs ~25; (b) linearity over vertices and pool rounds with the pool marginal ~140; (c) ~40 given lemTower(b) as a Spec; (a) trivial. Depends on the s7a pool-law characterization and the s2 mult / propOV (F11) API.

### `s7:lemPay` — lemma: Payments (s7.tex:914)

**Status:** x2+RT. **Formalization:** Tier-2 Spec EG/Spec/Quot/Pay.lean (PayStatement) over the s7a round-step Defs (or proof-internal lemmas, see S7-ROUNDSTEP-IN-DEFS); proof EG/Proof/Quot/Pay.lean

**Statement (precise restatement).** Setting: valid run with n >= N0, d_1 >= D_*, Gamma1 (for lemTower(b)); designation delta; a stage-1 outcome ω with its stage-2 data; a round 3 <= l <= R; ANY past, i.e. in Lean any J ⊆ E(G) with JPlusProps(ω,l,J) (the past enters the round step only through J_l, checked); the round step of s7:consRound applied to J. Items = edges of J \ J^lost; the vertices of an item are its port end(s) and its centre. Claims: (a1) |J^lost_l| <= (M_l - 1)|Lost_l|. (a2) #{items having a vertex in Pool_l} <= Σ_{v∈Pool_l} ω_l(v), where ω_l(v) := c^agg_{v,l} if v ∈ D_l and ω_l(v) := M_l otherwise. (a3) #{items having a JV-bad port end} <= (M_l - 1) · #{JV-bad classed ports of round l} (classed ports of round l = ∪_{Z∈Std_l} Q_Z). (b) at round l every fresh centre x has at most one unpaired fresh leg, so the round-l number of unpaired fresh legs is <= Σ_{Z∈Std_l}|F_Z|; over all rounds <= Σ_{l<=R} Σ_{Z∈Std_l}|F_Z| <= 2n (K4). (c) with E over xi_l (ω and J fixed): E[#items paid for SDR failures] <= n(M_l - 1)(4M_l)^-4 <= n/(256 M_l^3); E[#edges paid for loops] <= 2 (2/H^cd_l) #{PAR objects} <= 5.5 n M_l / H^cd_l; the loop bound holds also with the HUB lists (eta, zeta) fixed. (d) if xi_l lies in the event of consRound(f), then payrd_l <= 4(n/(256 M_l^3) + 5.5 n M_l/H^cd_l) <= 2n/M_l; if this holds at every round 3 <= l <= R, then Σ_{l=3}^{R} payrd_l <= 9n/D_*. (e) the single edges paid by the round step are exactly those of (a1), (a2), (a3), (b) [unpaired fresh legs], (d) [SDR failures] and (e3) [loops]; in particular nothing is paid for junction coincidences at ultra hubs or for concentrated pairs.

**Definitions needed.**

- *valid run and round data: run.Valid G Dstar, R, d_l, lambda_l = log2 d_l, M_l, P_l, D_l, Std_l, Z^0, E_l(Z), pre-part addresses* — s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T_l log2^4 T_l), T_l = d_l log2^2 d_l (a REAL in the manuscript; see blocker M-INTEGER); D_l = vertices in >= 2 round-l pre-parts; R = last round with d_R >= D_* [s2:defHBtp] — EG: no: proposed EG.HB.Run / Run.Valid / run.d / run.M (HB.MOf) / run.D / run.Std / run.Z0 / run.E (blueprint_s2a)
- *ancestors Y = (r, address), V(Y), H_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z; mu_r(w), mult_r(w)* — s2:defAncestors: one ancestor per pre-part (light part or standalone pre-part); anc_l(x) = ancestors of rounds <= l-2 containing x; Q_Z = U_Z \ F_Z; mult_r(w) = #ancestors of round r whose vertex set contains w; mu_r(w) = #round-r pre-parts containing w [s2:defAncestors] — EG: no: proposed run.ancVerts / anc / hubs / ports / fresh / classed / mu / mult (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), c^agg_{h,l}* — s6:defDesign: Y(u) in anc_l(u) for every classed port u of round l >= 3; d_{Y,l}(h) = #{hu in E_l(Z): Z in Std_l, u in Q_Z, Y(u) = Y}; c^agg_{h,l} = #{Y : d_{Y,l}(h) >= 1} [s6:defDesign] — EG: no: proposed EG.S6.Designation with cls, d, cAgg (blueprint_s6b)
- *J_l and its interface JPlusProps (types J^lost/J^hub/J^fr/J^par, J1, J2, J3, (ii))* — s6:lemJplus: the J-set produced by JS-LC at round l; the only information the J-consumer gets about the past [s6:lemJplus] — EG: no: proposed EG.S6.JPlusProps omega l J (blueprint_s6b)
- *Lost_Z, Lost_l, Q*_Z, Ret_Z, O_Z, X_U, dem, lp* — s6:defLending; X_U := 80 dem + 369 lp + sum_l (169 + M_l)|Lost_l| [s6:defLending, s5:defStages] — EG: no: proposed EG.S6.lost / lostRound / qs / ret / OZ / XU, EG.S5.dem / lp (blueprint_s6b, blueprint_s5)
- *pool labels plab(v), q_l, pi_{l,r}, Pool_{l,r}, Pool_l, r(w)* — s7:defPool: plab(v) in {bot} u {(l,r): 3 <= l <= R, 1 <= r <= l-2}, independent over v, P(plab(v) = (l,r)) = q_l pi_{l,r}, q_l = M_l^-2, pi_{l,r} = 2^-(l-1-r); Pool_l = plab^-1({l} x [1,l-2]); r(w) = second coordinate [s7:defPool (chunk s7a)] — EG: no: proposed EG.S7.plab (a field of the Stage1 outcome), EG.S7.pool omega l, EG.S7.poolRound omega w (EG/Defs/Quot/Pool.lean, chunk s7a)
- *candidates Cand_l(u), H^cd_l, JV-bad classed ports* — s7:defCand: Cand_l(u) = {w in Pool_{l,r(u)} : uw in LJV_{Y(u),l}}; H^cd_l = lambda_{l-2}^95/(8 M_l^2); u JV-bad iff |Cand_l(u)| < (1/2) E|Cand_l(u)| (E = unconditional stage-1 expectation) [s7:defCand (chunk s7a)] — EG: no: proposed EG.S7.cand, EG.S7.Hcd, EG.S7.jvBad (EG/Defs/Quot/Cand.lean, chunk s7a)
- *the round step at round l (items, live items, PAR objects, cherries, HUB lists, SDR, junctions, layers, rank split, quotient Q_l, lift, Obj_l, LentJV_l), its randomness xi_l, copies_l = |V(Q_l)|, payrd_l, the event (f)* — s7:consRound (a)-(h); xi_l = (eta_h uniform bijection of [4M_l], zeta_{h,u} uniform 3-subset of [4M_l], <_u uniform linear order of V(G)), mutually independent; copies_l := |V(Q_l)|; payrd_l := #edges paid in (d) and (e3); event (f) := {copies_l <= 4 E[copies_l|Past]} n {payrd_l <= 4 E[payrd_l|Past]} [s7:consRound, s7:defSchedule (chunk s7a)] — EG: no: proposed EG/Defs/Quot/Round.lean (chunk s7a): S7.RoundRand l, S7.xiDist run G l : FinDist, S7.roundOut omega l J xi (items, paid sets, quotient, objs, lentJV), S7.copies, S7.payrd, S7.markovEvent, S7.xiChosen omega l J (dite on the nonemptiness of the event, Classical.choose), S7.quotient omega l J : FGraph (S7.QVert V), S7.consumer omega : S6.JConsumer
- *finite probability, expectation, Markov, Fubini* — s1:citMarkov [s1:citMarkov] — EG: yes: EG.FinDist, FinDist.expect, prob, prod/pi/compProd, expect_prod (Fubini), two_thirds_le_prob_le_three_mul_expect, half_le_prob_le_four_mul_expect_and, exists_mem_le_mul_expect_ae (EG/Defs/Prob/FinDist.lean, EG/Lib/Prob/Basic.lean)
- *omega_l(v) (pooled-vertex weight)* — c^agg_{v,l} if v ∈ D_l, M_l otherwise [s7:lemPay(a2) (defined inside a lemma statement; reused by s7:defXprime)] — EG: no: proposed EG.S7.poolWeight run G δ l v : ℝ (Defs; avoid the name ω, which is the stage-1 outcome)
- *unpaired fresh leg, SDR failure, looped PAR object, PAR object, cherry* — s7:consRound (b), (d), (e3) [s7:consRound] — EG: no: part of the s7a round-step Defs

**Dependencies.** Declared: `s7:consRound`, `s7:lemWellDef`, `s6:lemJplus`, `s2:propParentless`, `s2:lemTower`.  
From the proof: `s7:consRound`, `s6:lemJplus`, `s7:lemWellDef`, `s2:propParentless`, `s2:lemTower`, `s7:defCand`, `s6:defDesign`, `s6:defLending`, `s2:propStructure`, `s2:defHBtp`.  
(a1): J^lost edges join a lost centre v ∈ Lost_Z to a port of Q*_Z; Q*_Z ∩ Lost_Z = ∅ so each has exactly one lost end; v ∉ D_l lies in one pre-part (J3 / propStructure(iv)), so all J-edges at v lie in E_l(Z) and J2 (per part) caps them at M_l - 1. (a2): v ∈ D_l: by J3 and the types, the items at v are J^hub items (v,u); J1 (aggregated over all parts) gives at most one per class Y, and each such Y has d_{Y,l}(v) >= 1 (the item is an edge vu ∈ E_l(Z), u ∈ Q_Z, Y(u) = Y), so <= c^agg_{v,l} (s6:defDesign); v ∉ D_l: J2. (a3): J2 at the port. (b): the pairing rule of consRound(b) + propParentless(i) (K4). (c): SDR: at most n ports (J3), each pays <= M_l - 1 items, failure probability <= (4M_l)^-4 by lemWellDef(iii); loops: with the lists fixed, the two ends of a PAR object lie at distinct ports p ≠ q, their junctions are independent (independent orders <_p, <_q) and the junction at q is uniform on Cand_l(q) \ Used(q), of size >= H^cd_l/2 (lemWellDef(v)), so P(same junction) <= 2/H^cd_l; a looped object costs <= 2 edges; #PAR objects <= |J_l| <= n(M_l - 1) (J2); 4·1.37 = 5.48 <= 5.5. (d): the event (f) + (c); H^cd_l = lambda_{l-2}^95/(8M_l^2) (s7:defCand, undeclared) gives 4·5.5 n M_l/H^cd_l = 176 n M_l^3/lambda_{l-2}^95; M_l <= lambda_{l-2}^1.6 (lemTower(b)) and M_l >= 2^40 (R2, s2:defHBtp, undeclared) give lambda_{l-2} >= 2^25 and 176 lambda^-90.2 <= lambda^-1.6 <= 1/M_l; Σ 1/M_l <= 2/D_* (lemTower(b)). (e): inspection of consRound. Undeclared but used: s7:defCand (H^cd_l), s6:defDesign (c^agg), s6:defLending (Lost), s2:propStructure(iv), s2:defHBtp (M_l >= 2^40).

**Used by:** s7:defXprime, s7:lemOneOutcome, s7:propCost, s7:thmJVps, s7:remNonCirc.

**Randomness.** (a1)-(b), (e): deterministic given (run, delta, stage-1 outcome ω, J). (c): expectation over the fresh round randomness xi_l = (eta_h)_{h∈V} × (zeta_{h,u})_{h≠u} × (<_u)_{u∈V} (uniform bijections of [4M_l], uniform 3-subsets of [4M_l], uniform linear orders of V(G); mutually independent), with ω and J (= the past) fixed; the loop bound further fixes the lists (eta, zeta) and averages over the orders only (Fubini on the product lists × orders). (d): deterministic on the chosen xi_l in the event (f); the Markov event's expectations are the xi_l-expectations with (ω, J) fixed.

**Lean shape.**

```lean
-- EG/Defs/Quot/Xprime.lean
noncomputable def poolWeight (run G δ) (l : ℕ) (v : V) : ℝ :=
  if v ∈ run.D G l then (δ.cAgg v l : ℝ) else (run.M G l : ℝ)
-- EG/Spec/Quot/Pay.lean  (Tier-2; S7.* are the s7a round-step Defs)
def PayStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V)
    (δ : S6.Designation run G), S7Hyp N0 Dstar G run →
  ∀ ω ∈ (S3.stage1Dist run G).supp, ∀ l ∈ Finset.Icc 3 run.R, ∀ J : Finset (Sym2 V), S6.JPlusProps ω l J →
    let n : ℝ := G.card; let M : ℝ := run.M G l; let H := S7.Hcd run G l
    ((S7.jLost ω l J).card : ℝ) ≤ (M - 1) * (S6.lostRound ω l).card ∧                                  -- (a1)
    (((S7.items ω l J).filter (fun e => ∃ v ∈ S7.itemVerts ω l J e, v ∈ S7.pool ω l)).card : ℝ)
        ≤ ∑ v ∈ S7.pool ω l, poolWeight run G δ l v ∧                                                -- (a2)
    (((S7.items ω l J).filter (fun e => ∃ u ∈ S7.portEnds ω l J e, S7.jvBad ω l u)).card : ℝ)
        ≤ (M - 1) * (S7.jvBadPorts ω l).card ∧                                                          -- (a3)
    (S7.unpairedFresh ω l J).card ≤ ∑ a ∈ run.Std G l, (run.fresh G l a).card ∧                        -- (b), per round
    (S7.xiDist run G l).expect (fun ξ => ((S7.sdrPaid ω l J ξ).card : ℝ)) ≤ n / (256 * M ^ 3) ∧          -- (c) SDR
    (S7.xiDist run G l).expect (fun ξ => ((S7.loopPaid ω l J ξ).card : ℝ)) ≤ 5.5 * n * M / H ∧         -- (c) loops
    (S7.markovEvent ω l J (S7.xiChosen ω l J) →
        (S7.payrd ω l J (S7.xiChosen ω l J) : ℝ) ≤ 4 * (n / (256 * M ^ 3) + 5.5 * n * M / H) ∧
        4 * (n / (256 * M ^ 3) + 5.5 * n * M / H) ≤ 2 * n / M) ∧                                      -- (d), per round
    S7.paidEdges ω l J (S7.xiChosen ω l J) =                                                          -- (e)
      S7.jLost ω l J ∪ S7.paidPool ω l J ∪ S7.paidJVbad ω l J ∪ S7.unpairedFresh ω l J
        ∪ S7.sdrPaid ω l J (S7.xiChosen ω l J) ∪ S7.loopPaid ω l J (S7.xiChosen ω l J)
-- global parts (separate conjuncts or lemmas): Σ_{l∈[1,R]} Σ_{a∈Std l} |F_a| ≤ 2n (= s2:propParentless K4);
--   Σ_{l∈[3,R]} 2n/M_l ≤ 9n/D_* (from lemTower(b)).
-- (e) could instead be the object count |Obj_l| ≤ |paidEdges| + 2 fnum(Q_l) (what propCost uses).
```

**Hazards.**

- **M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a)** (blocker): M_l is a REAL in (R2), but this chunk uses it as a NUMBER OF COLOURS: the copy counts of lemVstar/lemUHsplit sum over the 3M_l PAR colours and the 4M_l HUB colours ('summing over the 4M_l HUB colours'), lemPay(c) uses the SDR bound (4M_l)^-4 for lists in [4M_l] = [K^HUB_l], lemUHsplit(ii) uses 3k_h <= 4M_l, and (M_l - 1) is a J-edge cap. A Lean statement needs the manuscript decision proposed in blueprint_s2a (M_l := ceil(max(2^40, 2^16 T log2^4 T)) in N). Checked for this chunk: every inequality survives with integer M_l, because the chunk uses only M_l >= 2^40, M_l <= lambda_{l-2}^1.6, M_{l-1} >= 2M_l, sum_l 1/M_l <= 2/D_*, sum_l psi(M_l) <= 2.1 psi(D_*) (lemTower(b), re-checked by the s2a blueprint for the ceiling) and exact integer identities that do not involve M_l's value. Fallback without manuscript change: [ceil(3M_l)], [ceil(4M_l)] colours; then 3M_l, 4M_l in X_{V,l} must become the same ceilings (X_{V,l} is a stage-1 functional, its definition must match the palette size exactly).
- **S7-ROUNDSTEP-IN-DEFS** (risk): lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get locked Specs, the whole construction s7:consRound must be a Defs construction (chunk s7a) with the Markov choice written as `if h : ∃ ξ, 0 < (xiDist l).w ξ ∧ markovEvent ω l J ξ then Classical.choose h else default` (no proof term of a theorem inside a Def). Alternative: keep these four statements proof-internal (EG/Proof/Quot/*) and lock only thmJVps (whose statement mentions no construction). Decision needed with the s7a blueprint; recommendation: Specs for lemVstar, lemEXprime (pure stage-1 statements) and thmJVps/lemGammaSat; lemPay, lemUHsplit, propCost, lemOneOutcome as Tier-2 Specs over the s7a Defs, so that provers can work in parallel.
- **PAY-PER-ROUND** (risk): (b) and (d) are stated in the manuscript as totals over rounds ('at most 2n', 'Σ payrd <= 9n/D_*'), but the MIX-C interface (Option B/B', S7-MIXC-INTERFACE) consumes a PER-ROUND bound b_l(J). The per-round forms are: unpaired fresh legs at round l <= Σ_{Z∈Std_l}|F_Z| (<= number of fresh centres of round l) and payrd_l <= 2n/M_l; the totals follow from K4 and Σ1/M_l <= 2/D_*. State both forms; otherwise propCost cannot be assembled from MIX-C.
- **PAY-E-INSPECTION** (risk): (e) 'no other item is paid' is a claim by inspection of the construction. In Lean it must be a property of the Defs (the paid set is DEFINED as the union of the six categories, and Obj_l = paid single edges ++ lifted objects), else the object count |Obj_l| <= Σ categories + 2 f(Q_l) used by propCost is unproved. The categories overlap only harmlessly (an item can be both pooled and JV-bad; (d) pays hub items, (e3) pays PAR objects, disjoint), so the count uses the union bound, not a partition.
- **PAY-C-CONDITIONING** (risk): (c) needs: the xi_l law as a product lists × orders (Fubini: EG.FinDist.expect_prod); the fact from s7a that, with the lists fixed, the junction of an end in E'(u) is uniform on Cand_l(u) \ Used(u) and independent across ports (the restriction of a uniform linear order of V(G) to a set S is uniform on S; first q elements = uniform injection); lemWellDef(iii) (SDR failure <= (4M_l)^-4, itself a union-bound computation over Hall violators with K >= 10^4). The PAR objects (and cherries) are determined by (ω, J) (pairing 'by a fixed rule'), not by xi_l; the fixed rules must be Defs-level choices (Classical/list order), not existentials.
- **PAY-A1-ONE-LOST-END** (note): (a1) counts J^lost edges by their lost end; needs (i) Q*_Z ∩ Lost_Z = ∅ (s6:defLending API), (ii) a lost vertex lies in exactly one round-l pre-part (it is outside D_l), so J2cap per part is a per-vertex cap. JPlusProps (s6b shape: types, J2cap per part a) suffices; checked.
- **PAY-A2-HUB-ITEMS** (note): (a2) at a pooled hub v ∈ D_l needs: items at v are exactly J^hub edges (types + J3: hubs are never ports, fresh or lost centres), J1hub aggregated over all parts of round l, and d_{Y,l}(v) >= 1 for each realized class (the item vu ∈ E_l(Z) with u ∈ Q*_Z ⊆ Q_Z, Y(u) = Y). All present in s6b's JPlusProps; the items with BOTH ends pooled are counted twice, which is fine for an upper bound.
- **PAY-D-NUMERICS** (note): (d) uses real-exponent arithmetic: M_l <= lambda^1.6, lambda >= (2^40)^(1/1.6) = 2^25, 176 lambda^-90.2 <= lambda^-1.6 <= 1/M_l (rpow lemmas; small absolute constants only). 4n/(256 M^3) <= n/M since M >= 1. The final 9n/D_* has slack over the proved 4n/D_*.

**Effort.** ~700 lines, difficulty 3/5. (a1)-(a3), (b): counting from JPlusProps and the Lending/Design API ~260; (c) SDR ~80 given lemWellDef(iii), loops ~200 (Fubini, uniform-injection lemma from s7a, pair probability); (d) ~80 numerics; (e) ~80 once the Defs define the paid set as a union. Excludes the s7a construction itself.

### `s7:defXprime` — definition: The stage-1 functional X' (s7.tex:986)

**Status:** x2. **Formalization:** Defs EG/Defs/Quot/Xprime.lean (poolWeight, jvBadPorts, Xpool, Xprime) + API lemmas (nonnegativity, dependence only on ω) in EG/Lib/Quot/Xprime.lean; no Spec

**Statement (precise restatement).** Fix a valid run, a designation delta and a stage-1 outcome ω (families 1a-1d). With ω_l(v) as in s7:lemPay(a2) (c^agg_{v,l} for v ∈ D_l, M_l otherwise): X_pool := Σ_{l=3}^{R} [ Σ_{v∈Pool_l} ω_l(v) + (M_l - 1) · #{JV-bad classed ports of round l} ], where the classed ports of round l are ∪_{Z∈Std_l} Q_Z and JV-badness is s7:defCand (|Cand_l(u)| < (1/2) E|Cand_l(u)|, E the unconditional stage-1 expectation); X_V := Σ_{l=3}^{R} X_{V,l} (s7:lemVstar); X_U as in s6:defLending (80 dem + 369 lp + Σ_l (169 + M_l)|Lost_l|). X' := X_U + X_pool + X_V. Each term is >= 0 and is a deterministic function of (run, delta, ω). X' is the functional of stage (1e) of s7:defSchedule.

**Definitions needed.**

- *valid run and round data: run.Valid G Dstar, R, d_l, lambda_l = log2 d_l, M_l, P_l, D_l, Std_l, Z^0, E_l(Z), pre-part addresses* — s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T_l log2^4 T_l), T_l = d_l log2^2 d_l (a REAL in the manuscript; see blocker M-INTEGER); D_l = vertices in >= 2 round-l pre-parts; R = last round with d_R >= D_* [s2:defHBtp] — EG: no: proposed EG.HB.Run / Run.Valid / run.d / run.M (HB.MOf) / run.D / run.Std / run.Z0 / run.E (blueprint_s2a)
- *ancestors Y = (r, address), V(Y), H_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z; mu_r(w), mult_r(w)* — s2:defAncestors: one ancestor per pre-part (light part or standalone pre-part); anc_l(x) = ancestors of rounds <= l-2 containing x; Q_Z = U_Z \ F_Z; mult_r(w) = #ancestors of round r whose vertex set contains w; mu_r(w) = #round-r pre-parts containing w [s2:defAncestors] — EG: no: proposed run.ancVerts / anc / hubs / ports / fresh / classed / mu / mult (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), c^agg_{h,l}* — s6:defDesign: Y(u) in anc_l(u) for every classed port u of round l >= 3; d_{Y,l}(h) = #{hu in E_l(Z): Z in Std_l, u in Q_Z, Y(u) = Y}; c^agg_{h,l} = #{Y : d_{Y,l}(h) >= 1} [s6:defDesign] — EG: no: proposed EG.S6.Designation with cls, d, cAgg (blueprint_s6b)
- *Lost_Z, Lost_l, Q*_Z, Ret_Z, O_Z, X_U, dem, lp* — s6:defLending; X_U := 80 dem + 369 lp + sum_l (169 + M_l)|Lost_l| [s6:defLending, s5:defStages] — EG: no: proposed EG.S6.lost / lostRound / qs / ret / OZ / XU, EG.S5.dem / lp (blueprint_s6b, blueprint_s5)
- *pool labels plab(v), q_l, pi_{l,r}, Pool_{l,r}, Pool_l, r(w)* — s7:defPool: plab(v) in {bot} u {(l,r): 3 <= l <= R, 1 <= r <= l-2}, independent over v, P(plab(v) = (l,r)) = q_l pi_{l,r}, q_l = M_l^-2, pi_{l,r} = 2^-(l-1-r); Pool_l = plab^-1({l} x [1,l-2]); r(w) = second coordinate [s7:defPool (chunk s7a)] — EG: no: proposed EG.S7.plab (a field of the Stage1 outcome), EG.S7.pool omega l, EG.S7.poolRound omega w (EG/Defs/Quot/Pool.lean, chunk s7a)
- *candidates Cand_l(u), H^cd_l, JV-bad classed ports* — s7:defCand: Cand_l(u) = {w in Pool_{l,r(u)} : uw in LJV_{Y(u),l}}; H^cd_l = lambda_{l-2}^95/(8 M_l^2); u JV-bad iff |Cand_l(u)| < (1/2) E|Cand_l(u)| (E = unconditional stage-1 expectation) [s7:defCand (chunk s7a)] — EG: no: proposed EG.S7.cand, EG.S7.Hcd, EG.S7.jvBad (EG/Defs/Quot/Cand.lean, chunk s7a)
- *stage-1 outcome omega and its law (families 1a COL-JV colourings, 1b zones, 1c JS labels, 1d pool labels)* — s7:defSchedule stage 1: four mutually independent label families, one joint finite law; every stage-1 quantity (X_U, X_pool, X_V, JV-bad, Pool_l) is a function of omega [s7:defSchedule, s3:defCOL, s5:defZones, s7:defPool] — EG: partly: EG.FinDist (pi, prod, ofFinset, expect, Markov lemmas) exists; the Stage1 type/law is proposed in the s3 layer (blueprint_s6b calls it S3.stage1Dist, blueprint_s5 calls it stage1Law: names must be unified)
- *X_{V,l}, X_V* — s7:lemVstar [s7:lemVstar] — EG: no: EG.S7.XVl / XV (this chunk)
- *omega_l(v)* — s7:lemPay(a2) [s7:lemPay] — EG: no: EG.S7.poolWeight (this chunk)

**Dependencies.** Declared: `s6:defLending`, `s7:lemVstar`, `s7:lemPay`.  
From the proof: `s6:defLending`, `s7:lemVstar`, `s7:lemPay`, `s7:defCand`, `s7:defPool`, `s6:defDesign`, `s2:defAncestors`, `s2:defHBtp`, `s5:defStages`.  
A definition: the list is what its text needs. s7:lemPay and s7:lemVstar are used only for the DEFINITIONS of omega_l and X_V made inside their statements (move both to Defs). JV-badness (s7:defCand) and Pool_l (s7:defPool) are undeclared but essential; c^agg from s6:defDesign; classed ports and D_l from s2.

**Used by:** s7:defSchedule, s7:lemEXprime, s7:lemUHsplit, s7:lemOneOutcome, s7:propCost.

**Randomness.** Definition only: X' is a function of the stage-1 outcome ω (all of 1a-1d). Its definition refers to the stage-1 LAW once, through the JV-bad threshold (1/2) E|Cand_l(u)| (a fixed number). The law of X' is used in lemEXprime and in the selection (1e).

**Lean shape.**

```lean
-- EG/Defs/Quot/Xprime.lean  (namespace EG.S7; ctx run G δ; ω : S3.Stage1 run G)
def classedRound (run G) (l : ℕ) : Finset V := (run.Std G l).biUnion (run.classed G l)
noncomputable def jvBadPorts (ω) (l : ℕ) : Finset V := (classedRound run G l).filter (S7.jvBad ω l)
noncomputable def Xpool (ω) : ℝ :=
  ∑ l ∈ Finset.Icc 3 run.R,
    ((∑ v ∈ S7.pool ω l, poolWeight run G δ l v) + ((run.M G l : ℝ) - 1) * (jvBadPorts ω l).card)
noncomputable def Xprime (ω) : ℝ := S6.XU ω + Xpool ω + XV ω
-- API: 0 ≤ Xpool ω, 0 ≤ XV ω, 0 ≤ S6.XU ω, hence 0 ≤ Xprime ω (needs run.M G l ≥ 1).
```

**Hazards.**

- **S7-STAGE1-LAW** (risk): X' mixes all four stage-1 families (X_U: 1a-1c incl. zones; X_pool: pool labels 1d and JV-badness, which depends on the LJV colours 1a AND on the pool labels 1d; X_V: 1d only), and E X' is taken under ONE joint law. The joint law (product of 1a-1d) must be a single Defs object used by s5 (dem, lp, lemExpect), s6 (lemLost), s7a (lemCand) and this chunk; the blueprints currently use two names (S3.stage1Dist in s6b, stage1Law in s5). The pool-label law is a probability distribution only because sum_l q_l(1 - 2^-(l-2)) <= sum_l M_l^-2 < 1, which is lemTower(b) for VALID runs (same issue as s5 ZONE-LAW-WELLDEF): define it with a dite fallback and prove the characterization P(plab v = (l,r)) = q_l pi_{l,r} under S7Hyp. Also: s5 Specs (K-RED, Child) quantify ω ∈ supp, so the selected stage-1 outcome must have positive weight.
- **XP-NAME-CLASH** (note): The manuscript's omega_l(v) (weight) and the stage-1 outcome ω collide in Lean; name the weight poolWeight. It is defined inside the statement of s7:lemPay(a2); both lemPay and defXprime must reference the one Defs constant.
- **XP-JVBAD-LAW** (note): JV-badness compares |Cand_l(u)| with (1/2) E|Cand_l(u)|, an expectation under the stage-1 law. Hence X' (a Defs object) depends on the law S3.stage1Dist itself, and E X' is an expectation of a function defined through another expectation under the same law. This is fine in FinDist, but the Defs of jvBad must use exactly the law that lemEXprime and the selection (1e) use (not a marginal or a re-built law), else lemCand(iii)'s probability bound does not apply.
- **XP-RANGES** (note): Σ_l in X_pool is over l ∈ [3,R] (explicit); X_U sums over l ∈ [1,R] (blueprint_s6b LEND-XU-RANGE; Lost_l = ∅ for l <= 2). Classed ports of round l include LOST ports: JV-badness is counted for every classed port (defCand), although items only have port ends in Q*_Z; harmless over-count.
- **XP-M-MINUS-ONE** (note): (M_l - 1) as a real (cast) avoids truncated subtraction; with M_l ∈ ℕ (M-INTEGER) cast before subtracting.

**Effort.** ~90 lines, difficulty 1/5. Definitions ~40; nonnegativity and 'function of ω' lemmas ~50.

### `s7:lemEXprime` — lemma: Expectation of X' (s7.tex:1004)

**Status:** x2+RT. **Formalization:** Defs EG.S7.epsX (EG/Defs/Quot/Constants.lean) + Spec EG/Spec/Quot/EXprime.lean (EXprimeStatement); proof EG/Proof/Quot/EXprime.lean

**Statement (precise restatement).** Setting: a valid run with n >= N0, d_1 >= D_*, Gamma1, Gamma2a, Gamma3, N0Cond (the hypotheses of s6:lemLost / s5:lemExpect / lemTower / propStructure), a designation delta; E over the joint stage-1 law. Define eps_X(D) := eps_U(D) + 10.3/D + 2.1 (6 log2 D + 12)/D with eps_U(D) = 2462 (log2 D)^-205 (s5:lemExpect). Then E X' <= eps_X(D_*) n; more precisely E X_U <= eps_U(D_*) n + 5.5 n/D_*, E X_pool <= 4.8 n/D_*, and E X_V <= 2.1 (6 log2 D_* + 12) n/D_*. Per round (proof): E Σ_{v∈Pool_l} ω_l(v) <= q_l (Σ_{h∈D_l} c^agg_{h,l} + n M_l) <= 2.37 n/M_l using Σ_{h∈D_l} c^agg_{h,l} <= 1.37 n M_l; E[(M_l - 1)#JV-bad classed ports of round l] <= (M_l - 1) n e^{-H^cd_l/4} <= n/M_l^2 <= 0.03 n/M_l.

**Definitions needed.**

- *valid run and round data: run.Valid G Dstar, R, d_l, lambda_l = log2 d_l, M_l, P_l, D_l, Std_l, Z^0, E_l(Z), pre-part addresses* — s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T_l log2^4 T_l), T_l = d_l log2^2 d_l (a REAL in the manuscript; see blocker M-INTEGER); D_l = vertices in >= 2 round-l pre-parts; R = last round with d_R >= D_* [s2:defHBtp] — EG: no: proposed EG.HB.Run / Run.Valid / run.d / run.M (HB.MOf) / run.D / run.Std / run.Z0 / run.E (blueprint_s2a)
- *ancestors Y = (r, address), V(Y), H_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z; mu_r(w), mult_r(w)* — s2:defAncestors: one ancestor per pre-part (light part or standalone pre-part); anc_l(x) = ancestors of rounds <= l-2 containing x; Q_Z = U_Z \ F_Z; mult_r(w) = #ancestors of round r whose vertex set contains w; mu_r(w) = #round-r pre-parts containing w [s2:defAncestors] — EG: no: proposed run.ancVerts / anc / hubs / ports / fresh / classed / mu / mult (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), c^agg_{h,l}* — s6:defDesign: Y(u) in anc_l(u) for every classed port u of round l >= 3; d_{Y,l}(h) = #{hu in E_l(Z): Z in Std_l, u in Q_Z, Y(u) = Y}; c^agg_{h,l} = #{Y : d_{Y,l}(h) >= 1} [s6:defDesign] — EG: no: proposed EG.S6.Designation with cls, d, cAgg (blueprint_s6b)
- *Lost_Z, Lost_l, Q*_Z, Ret_Z, O_Z, X_U, dem, lp* — s6:defLending; X_U := 80 dem + 369 lp + sum_l (169 + M_l)|Lost_l| [s6:defLending, s5:defStages] — EG: no: proposed EG.S6.lost / lostRound / qs / ret / OZ / XU, EG.S5.dem / lp (blueprint_s6b, blueprint_s5)
- *pool labels plab(v), q_l, pi_{l,r}, Pool_{l,r}, Pool_l, r(w)* — s7:defPool: plab(v) in {bot} u {(l,r): 3 <= l <= R, 1 <= r <= l-2}, independent over v, P(plab(v) = (l,r)) = q_l pi_{l,r}, q_l = M_l^-2, pi_{l,r} = 2^-(l-1-r); Pool_l = plab^-1({l} x [1,l-2]); r(w) = second coordinate [s7:defPool (chunk s7a)] — EG: no: proposed EG.S7.plab (a field of the Stage1 outcome), EG.S7.pool omega l, EG.S7.poolRound omega w (EG/Defs/Quot/Pool.lean, chunk s7a)
- *candidates Cand_l(u), H^cd_l, JV-bad classed ports* — s7:defCand: Cand_l(u) = {w in Pool_{l,r(u)} : uw in LJV_{Y(u),l}}; H^cd_l = lambda_{l-2}^95/(8 M_l^2); u JV-bad iff |Cand_l(u)| < (1/2) E|Cand_l(u)| (E = unconditional stage-1 expectation) [s7:defCand (chunk s7a)] — EG: no: proposed EG.S7.cand, EG.S7.Hcd, EG.S7.jvBad (EG/Defs/Quot/Cand.lean, chunk s7a)
- *stage-1 outcome omega and its law (families 1a COL-JV colourings, 1b zones, 1c JS labels, 1d pool labels)* — s7:defSchedule stage 1: four mutually independent label families, one joint finite law; every stage-1 quantity (X_U, X_pool, X_V, JV-bad, Pool_l) is a function of omega [s7:defSchedule, s3:defCOL, s5:defZones, s7:defPool] — EG: partly: EG.FinDist (pi, prod, ofFinset, expect, Markov lemmas) exists; the Stage1 type/law is proposed in the s3 layer (blueprint_s6b calls it S3.stage1Dist, blueprint_s5 calls it stage1Law: names must be unified)
- *named small functions of D_*: eps_A, eps_U, eps_K = eps_Chain, eps_CONC, eps_X, eps_1, eps_2, F* — eps_A(D) = 31 eps/(C' log2 log2 D) (s2:lemTower(e)); eps_U(D) = 2462 (log2 D)^-205 (s5:lemExpect); eps_Chain(D) = 614/D + log2(2A log2(A log2 log2 D))/(371 (log2 log2 D)^2) (s5:lemParent); eps_CONC (s6:thmCONCL(iv)); eps_X (s7:lemEXprime); eps_1 (s7:propCost); eps_2 and F (s7:lemUHsplit) [s2:lemTower, s5:lemExpect, s5:lemParent, s6:thmCONCL, s7:lemEXprime, s7:propCost, s7:lemUHsplit] — EG: no: proposed EG.epsA, EG.S5.epsU, EG.S5.epsChain, EG.epsCONC, EG.S7.epsX, EG.S7.FQ, EG.eps1, EG.eps2 (EG/Defs/Quot/Constants.lean for the s7 ones)
- *finite probability, expectation, Markov, Fubini* — s1:citMarkov [s1:citMarkov] — EG: yes: EG.FinDist, FinDist.expect, prob, prod/pi/compProd, expect_prod (Fubini), two_thirds_le_prob_le_three_mul_expect, half_le_prob_le_four_mul_expect_and, exists_mem_le_mul_expect_ae (EG/Defs/Prob/FinDist.lean, EG/Lib/Prob/Basic.lean)
- *X', X_U, X_pool, X_V* — s7:defXprime [s7:defXprime] — EG: no: EG.S7.Xprime etc. (this chunk)
- *eps_X(D)* — eps_U(D) + 10.3/D + 2.1 (6 log2 D + 12)/D [s7:lemEXprime] — EG: no: proposed EG.S7.epsX (EG/Defs/Quot/Constants.lean)

**Dependencies.** Declared: `s7:defXprime`, `s6:lemLost`, `s7:lemCand`, `s7:lemVstar`, `s2:propOV`, `s2:propStructure`, `s2:lemTower`, `s5:lemExpect`, `s2:lemCap`.  
From the proof: `s7:defXprime`, `s6:lemLost`, `s5:lemExpect`, `s7:lemVstar`, `s7:lemCand`, `s7:defPool`, `s6:defDesign`, `s2:lemCap`, `s2:propOV`, `s2:propStructure`, `s2:lemTower`, `s2:defHBtp`.  
X_U: s6:lemLost(iii) (which uses s5:lemExpect). X_V: s7:lemVstar(c). Pooled weights: omega_l is deterministic (run, delta) so E Σ_{v∈Pool_l} omega_l(v) = Σ_v P(v ∈ Pool_l) omega_l(v) <= q_l Σ_v omega_l(v) (s7:defPool marginal); c^agg_{h,l} <= Σ_Y d_{Y,l}(h) (s6:defDesign) and Σ_h Σ_Y d_{Y,l}(h) = Σ_{Z∈Std_l} Σ_{u∈Q_Z} deg_{E_l(Z)}(u) <= (M_l - 1) Σ_Z |Z^0| (s2:lemCap(ii)) <= 1.37 n M_l (s2:propOV (K1)). JV-bad: at most n classed ports per round (port sets U_Z disjoint, s2:propStructure(iv)); each JV-bad w.p. <= exp(-H^cd_l/4) (s7:lemCand(iii)) and exp(-H^cd_l/4) <= M_l^-3 by H^cd_l >= 2^10 M_l^10 (s7:lemCand(iv)); (M_l - 1)/M_l^3 <= 1/M_l^2 <= 0.03/M_l (M_l >= 2^40, s2:defHBtp). Sum: Σ_l 2.4 n/M_l <= 4.8 n/D_* (s2:lemTower(b)). The mention of s6:lemJplus in the proof is a pointer to a parallel count, not a logical dependency.

**Used by:** s7:lemUHsplit, s7:propCost, s7:lemGammaSat, s1:condG4, s7:lemOneOutcome.

**Randomness.** Sample space: the full stage-1 outcome (product of 1a COL-JV colourings per ancestor and edge, 1b zone choices and sublabels per vertex, 1c JS labels, 1d pool labels per vertex), unconditional. X_U uses 1a-1c (through s6:lemLost / s5:lemExpect); the pooled-weight part uses only the 1d marginals; the JV-bad part uses the joint law of 1a (LJV colours of H_Y edges) and 1d (pool labels), which lemCand(i),(iii) needs to be independent (Chernoff over independent indicators).

**Lean shape.**

```lean
-- EG/Defs/Quot/Constants.lean
noncomputable def epsX (D : ℝ) : ℝ := S5.epsU D + 10.3 / D + 2.1 * (6 * Real.logb 2 D + 12) / D
-- EG/Spec/Quot/EXprime.lean
def EXprimeStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V)
    (δ : S6.Designation run G), S7Hyp N0 Dstar G run →
    let μ := S3.stage1Dist run G
    μ.expect (S6.XU (δ := δ)) ≤ S5.epsU Dstar * G.card + 5.5 * G.card / Dstar ∧
    μ.expect (S7.Xpool (δ := δ)) ≤ 4.8 * G.card / Dstar ∧
    μ.expect S7.XV ≤ 2.1 * (6 * Real.logb 2 Dstar + 12) * G.card / Dstar ∧
    μ.expect (S7.Xprime (δ := δ)) ≤ epsX Dstar * G.card
```

**Hazards.**

- **S7-STAGE1-LAW** (risk): X' mixes all four stage-1 families (X_U: 1a-1c incl. zones; X_pool: pool labels 1d and JV-badness, which depends on the LJV colours 1a AND on the pool labels 1d; X_V: 1d only), and E X' is taken under ONE joint law. The joint law (product of 1a-1d) must be a single Defs object used by s5 (dem, lp, lemExpect), s6 (lemLost), s7a (lemCand) and this chunk; the blueprints currently use two names (S3.stage1Dist in s6b, stage1Law in s5). The pool-label law is a probability distribution only because sum_l q_l(1 - 2^-(l-2)) <= sum_l M_l^-2 < 1, which is lemTower(b) for VALID runs (same issue as s5 ZONE-LAW-WELLDEF): define it with a dite fallback and prove the characterization P(plab v = (l,r)) = q_l pi_{l,r} under S7Hyp. Also: s5 Specs (K-RED, Child) quantify ω ∈ supp, so the selected stage-1 outcome must have positive weight.
- **EXP-CAGG-DOUBLECOUNT** (note): Σ_{h∈D_l} c^agg_{h,l} <= Σ_h Σ_Y d_{Y,l}(h) = #{(h, u): hu ∈ E_l(Z), Z ∈ Std_l, u ∈ Q_Z} = Σ_Z Σ_{u∈Q_Z} deg_{E_l(Z)}(u) is a double count over ordered pairs; needs the edge sets E_l(Z) of distinct Z disjoint and each edge counted once per classed-port end. Explicit Finset.sum_comm/card_sigma bookkeeping (~120 lines). The deliberately loose Σ_Z|Q_Z| <= Σ|Z^0| <= 1.37n (instead of <= n) is what the constant 2.37 uses.
- **EXP-JVBAD-EXP** (note): exp(-H^cd_l/4) <= M_l^-3 with H^cd_l >= 2^10 M_l^10: use exp(-y) <= 1/y (y > 0): exp(-H/4) <= 4/H <= 4/(2^10 M^10) <= M^-3. Real.exp lemmas only; no galactic evaluation.
- **EXP-HYPS** (note): The statement has no hypotheses in the text; the proof needs those of s6:lemLost/s5:lemExpect (S5Hyp: Gamma1, Gamma3, N0Cond, n >= N0, d_1 >= D_*, valid run) and lemCap (Gamma2a: D_* >= 2^117). Use S7Hyp. The bound on E X_U is IMPORTED verbatim from s6:lemLost(iii) (constant 5.5): the Lean Spec of lemLost must use the same X_U (with (169 + M_l)) and the same law.

**Effort.** ~360 lines, difficulty 3/5. Pooled weights ~160 (marginal, double count); JV-bad ~80 (lemCand(iii) as a Spec, exp bound, <= n classed ports); assembly with lemLost(iii), lemVstar ~60; Σ_l bounds ~60.

### `s7:lemUHsplit` — lemma: Lemma UH*-split: quotient size (s7.tex:1052)

**Status:** x2+RT. **Formalization:** Defs EG.S7.detl, EG.S7.FQ, EG.eps2 (EG/Defs/Quot/Constants.lean) + Tier-2 Spec EG/Spec/Quot/UHsplit.lean (UHsplitStatement: (ii) per round for every admissible J; (iii)+(iv) as the global bound) over the s7a round-step Defs; proof EG/Proof/Quot/UHsplit/{Copies,Numerics}.lean

**Statement (precise restatement).** Setting: S7Hyp (Gamma1, Gamma2a, Gamma3, N0Cond, n >= N0, d_1 >= D_*, valid run), a designation delta, a stage-1 outcome ω, and for each round the round step of s7:consRound. For 3 <= l <= R put det_l := 3|D_l| + 78 n M_l/H^cd_l + 30 n/M_l + 320 n M_l^3 (log2 thult_l + 8)/lambda_{l-2}^95, where H^cd_l = lambda_{l-2}^95/(8 M_l^2) and thult_l = floor(M_l H^cd_l / 7) (s7:consRound(c)); det_l is a deterministic function of the run. (i) X_{V,l} is the stage-1 weight of s7:lemVstar. (ii) For every ω and every past (in Lean: every J with JPlusProps(ω,l,J)): E_{xi_l}[copies_l] <= X_{V,l}(ω) + det_l, where copies_l = |V(Q_l)|. (iii) If X'(ω) <= 3 E X' and at every round 3 <= l <= R the chosen xi_l lies in the event of consRound(f), then Σ_{l=3}^{R} |V(Q_l)| <= 12 E X' + 4 Σ_{l=3}^{R} det_l. (iv) With F(x) := (3184 + 30400 log2 x) x^-90.2 (x >= 1): Σ_{l=3}^{R} det_l <= 3 eps_A n + 60 n/D_* + 2 F(log2 D_*) n, and 2F(log2 D_*) < 2^-1000. Hence, in the situation of (iii), Σ_{l=3}^{R} |V(Q_l)| <= theta_Q n with theta_Q := eps_2(D_*) := 12 eps_X(D_*) + 4(3 eps_A + 60/D_* + 2F(log2 D_*)), eps_A = 31 eps/(C' log2 log2 D_*); theta_Q depends on D_* only, and theta_Q <= 1/4 by Gamma4.

**Definitions needed.**

- *valid run and round data: run.Valid G Dstar, R, d_l, lambda_l = log2 d_l, M_l, P_l, D_l, Std_l, Z^0, E_l(Z), pre-part addresses* — s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T_l log2^4 T_l), T_l = d_l log2^2 d_l (a REAL in the manuscript; see blocker M-INTEGER); D_l = vertices in >= 2 round-l pre-parts; R = last round with d_R >= D_* [s2:defHBtp] — EG: no: proposed EG.HB.Run / Run.Valid / run.d / run.M (HB.MOf) / run.D / run.Std / run.Z0 / run.E (blueprint_s2a)
- *ancestors Y = (r, address), V(Y), H_Y, anc_l(x); hubs A_Z, ports U_Z, fresh ports F_Z, classed ports Q_Z; mu_r(w), mult_r(w)* — s2:defAncestors: one ancestor per pre-part (light part or standalone pre-part); anc_l(x) = ancestors of rounds <= l-2 containing x; Q_Z = U_Z \ F_Z; mult_r(w) = #ancestors of round r whose vertex set contains w; mu_r(w) = #round-r pre-parts containing w [s2:defAncestors] — EG: no: proposed run.ancVerts / anc / hubs / ports / fresh / classed / mu / mult (blueprint_s2a)
- *pool labels plab(v), q_l, pi_{l,r}, Pool_{l,r}, Pool_l, r(w)* — s7:defPool: plab(v) in {bot} u {(l,r): 3 <= l <= R, 1 <= r <= l-2}, independent over v, P(plab(v) = (l,r)) = q_l pi_{l,r}, q_l = M_l^-2, pi_{l,r} = 2^-(l-1-r); Pool_l = plab^-1({l} x [1,l-2]); r(w) = second coordinate [s7:defPool (chunk s7a)] — EG: no: proposed EG.S7.plab (a field of the Stage1 outcome), EG.S7.pool omega l, EG.S7.poolRound omega w (EG/Defs/Quot/Pool.lean, chunk s7a)
- *candidates Cand_l(u), H^cd_l, JV-bad classed ports* — s7:defCand: Cand_l(u) = {w in Pool_{l,r(u)} : uw in LJV_{Y(u),l}}; H^cd_l = lambda_{l-2}^95/(8 M_l^2); u JV-bad iff |Cand_l(u)| < (1/2) E|Cand_l(u)| (E = unconditional stage-1 expectation) [s7:defCand (chunk s7a)] — EG: no: proposed EG.S7.cand, EG.S7.Hcd, EG.S7.jvBad (EG/Defs/Quot/Cand.lean, chunk s7a)
- *the round step at round l (items, live items, PAR objects, cherries, HUB lists, SDR, junctions, layers, rank split, quotient Q_l, lift, Obj_l, LentJV_l), its randomness xi_l, copies_l = |V(Q_l)|, payrd_l, the event (f)* — s7:consRound (a)-(h); xi_l = (eta_h uniform bijection of [4M_l], zeta_{h,u} uniform 3-subset of [4M_l], <_u uniform linear order of V(G)), mutually independent; copies_l := |V(Q_l)|; payrd_l := #edges paid in (d) and (e3); event (f) := {copies_l <= 4 E[copies_l|Past]} n {payrd_l <= 4 E[payrd_l|Past]} [s7:consRound, s7:defSchedule (chunk s7a)] — EG: no: proposed EG/Defs/Quot/Round.lean (chunk s7a): S7.RoundRand l, S7.xiDist run G l : FinDist, S7.roundOut omega l J xi (items, paid sets, quotient, objs, lentJV), S7.copies, S7.payrd, S7.markovEvent, S7.xiChosen omega l J (dite on the nonemptiness of the event, Classical.choose), S7.quotient omega l J : FGraph (S7.QVert V), S7.consumer omega : S6.JConsumer
- *J_l and its interface JPlusProps (types J^lost/J^hub/J^fr/J^par, J1, J2, J3, (ii))* — s6:lemJplus: the J-set produced by JS-LC at round l; the only information the J-consumer gets about the past [s6:lemJplus] — EG: no: proposed EG.S6.JPlusProps omega l J (blueprint_s6b)
- *named small functions of D_*: eps_A, eps_U, eps_K = eps_Chain, eps_CONC, eps_X, eps_1, eps_2, F* — eps_A(D) = 31 eps/(C' log2 log2 D) (s2:lemTower(e)); eps_U(D) = 2462 (log2 D)^-205 (s5:lemExpect); eps_Chain(D) = 614/D + log2(2A log2(A log2 log2 D))/(371 (log2 log2 D)^2) (s5:lemParent); eps_CONC (s6:thmCONCL(iv)); eps_X (s7:lemEXprime); eps_1 (s7:propCost); eps_2 and F (s7:lemUHsplit) [s2:lemTower, s5:lemExpect, s5:lemParent, s6:thmCONCL, s7:lemEXprime, s7:propCost, s7:lemUHsplit] — EG: no: proposed EG.epsA, EG.S5.epsU, EG.S5.epsChain, EG.epsCONC, EG.S7.epsX, EG.S7.FQ, EG.eps1, EG.eps2 (EG/Defs/Quot/Constants.lean for the s7 ones)
- *constants and conditions: eps = 2^-5, C' = 103, A = 105, N0 (N0Cond), D_* with Gamma1..Gamma4, GammaCond* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condGamma] — EG: no: proposed EG.epsC, EG.N0Cond, EG.Gamma1core/Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1); Gamma4 and GammaCond must live after the s7 Defs (they mention eps1, eps2)
- *finite probability, expectation, Markov, Fubini* — s1:citMarkov [s1:citMarkov] — EG: yes: EG.FinDist, FinDist.expect, prob, prod/pi/compProd, expect_prod (Fubini), two_thirds_le_prob_le_three_mul_expect, half_le_prob_le_four_mul_expect_and, exists_mem_le_mul_expect_ae (EG/Defs/Prob/FinDist.lean, EG/Lib/Prob/Basic.lean)
- *det_l, F, eps_2 = theta_Q* — as in the statement [s7:lemUHsplit] — EG: no: proposed EG.S7.detl run G l, EG.S7.FQ, EG.eps2 (EG/Defs/Quot/Constants.lean)
- *thult_l, k_h, c^live_h (ultra / non-ultra hubs)* — s7:consRound(c): thult_l = floor(M_l H^cd_l/7); h ultra iff c^live_h > thult_l; k_h = ceil(8 c^live_h / H^cd_l) [s7:consRound] — EG: no: s7a Defs
- *m_kappa(h,w), m_kappa(w,w'), rank split, sub-layers, copies* — s7:consRound(g), s7:lemMULT, unlabelled PAR analogue (s7.tex l.711-713) [s7:consRound, s7:lemMULT] — EG: no: s7a Defs/lemmas
- *X_{V,l}, X'* — s7:lemVstar, s7:defXprime [this chunk] — EG: no: EG.S7.XVl, EG.S7.Xprime

**Dependencies.** Declared: `s7:lemCC`, `s7:lemMULT`, `s7:lemUltra`, `s7:lemVstar`, `s7:lemEXprime`, `s7:defSchedule`, `s2:propOV`, `s2:lemTower`, `s2:lemLacunary`, `s1:condG4`, `s1:condG1`, `s7:consRound`, `s7:lemWellDef`, `s2:defHBtp`, `s6:lemJplus`.  
From the proof: `s7:consRound`, `s7:lemCC`, `s7:lemMULT`, `s7:lemUltra`, `s7:lemWellDef`, `s7:lemVstar`, `s7:defXprime`, `s7:lemEXprime`, `s7:defSchedule`, `s7:defCand`, `s6:lemJplus`, `s2:propOV`, `s2:lemTower`, `s2:lemLacunary`, `s2:defHBtp`, `s1:condG1`, `s1:condG4`.  
(ii): V(Q_l) splits into PAR copies (lemCC(iii), conditional on the lists; needs the unlabelled PAR analogue of MULT), copies of non-ultra hubs (lemWellDef(iv): m_kappa(h,w) <= 1, lemMULT: copies = max_w m_kappa(h,w); colours used lie in the 3k_h-element union of the lists; k_h <= 1 + 8c_h/H^cd_l; Σ_h c^live_h <= |J_l| <= n(M_l - 1) by J2 of s6:lemJplus), junction copies in HUB layers (lemMULT: max_h m_kappa(h,w) <= mult_{r(w)}(w), summed over 4M_l colours), copies of ultra hubs (lemUltra(iv)); constants 44.7 + 32.9 <= 78, 29.8 <= 30; average over the lists (Fubini). (iii): Markov event (consRound(f)) + (ii) + X_V <= X' (X_U, X_pool >= 0, s7:defXprime) + X' <= 3E X' (s7:defSchedule (1e)). (iv): propOV (K2) |D_l| <= 7.6 eps n/log P_l; lemTower(e) Σ 15.2 eps/log P_l <= eps_A; lemTower(b) Σ 1/M_l <= 2/D_*, M_l <= lambda_{l-2}^1.6; H^cd_l (s7:defCand, undeclared); log2 thult_l <= 95 log2 lambda_{l-2}; F decreasing on [2^25, ∞) and F(2x) <= F(x)/2; lemLacunary(ii) lambda_r >= 2^{lambda_{r+1}/A} >= 2 lambda_{r+1} (x/105 >= 1 + log2 x for x >= 2^25) and lemLacunary(i) (halving sums); lambda_{R-2} >= lambda_R >= log2 D_* (lemTower(a), (R0) of s2:defHBtp: d_R >= D_*); log2 D_* >= 2^256 (Gamma1(a)); lemEXprime (E X' <= eps_X n); Gamma4 (theta_Q <= 1/4). Declared s6:lemJplus IS used (J2card for Σ c^live_h) despite the \ref-scanner flag.

**Used by:** s7:lemOneOutcome, s7:thmJVps, s7:lemGammaSat, s1:condG4, s1:defConstants, s1:thmMain, s7:remNonCirc.

**Randomness.** (ii): expectation over the round randomness xi_l with the past fixed; in Lean the past is (ω, J) and E is (S7.xiDist run G l).expect (the xi_l law does not depend on J or ω). The proof first fixes the lists (eta, zeta) and averages over the orders (<_u) only (lemCC, lemUltra are conditional on the lists), then averages over the lists: Fubini on the product lists × orders. (iii): deterministic on an outcome where stage 1 was selected in {X' <= 3 E X'} (E = unconditional stage-1 expectation, a fixed number) and each xi_l in the Markov event. (iv): deterministic (run only).

**Lean shape.**

```lean
-- EG/Defs/Quot/Constants.lean
noncomputable def detl (run G) (l : ℕ) : ℝ :=
  let n : ℝ := G.card; let M : ℝ := run.M G l; let lam := run.lam G (l - 2)
  3 * (run.D G l).card + 78 * n * M / S7.Hcd run G l + 30 * n / M
    + 320 * n * M ^ 3 * (Real.logb 2 (S7.thult run G l) + 8) / lam ^ 95
noncomputable def FQ (x : ℝ) : ℝ := (3184 + 30400 * Real.logb 2 x) * x ^ (-(90.2 : ℝ))
noncomputable def eps2 (D : ℝ) : ℝ := 12 * S7.epsX D + 4 * (3 * EG.epsA D + 60 / D + 2 * FQ (Real.logb 2 D))
-- EG/Spec/Quot/UHsplit.lean  (Tier-2)
def UHsplitStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V)
    (δ : S6.Designation run G), S7Hyp N0 Dstar G run →
  (∀ ω ∈ (S3.stage1Dist run G).supp, ∀ l ∈ Finset.Icc 3 run.R, ∀ J, S6.JPlusProps ω l J →
      (S7.xiDist run G l).expect (fun ξ => ((S7.quotient' ω l J ξ).card : ℝ)) ≤ S7.XVl ω l + detl run G l) ∧   -- (ii)
  (∀ ω ∈ (S3.stage1Dist run G).supp, S7.Xprime ω ≤ 3 * (S3.stage1Dist run G).expect S7.Xprime →
    ∀ Js : ℕ → Finset (Sym2 V), (∀ l ∈ Finset.Icc 3 run.R, S6.JPlusProps ω l (Js l)) →
      ∑ l ∈ Finset.Icc 3 run.R, ((S7.quotient ω l (Js l)).card : ℝ)
        ≤ 12 * (S3.stage1Dist run G).expect S7.Xprime + 4 * ∑ l ∈ Finset.Icc 3 run.R, detl run G l ∧       -- (iii)
      ∑ l ∈ Finset.Icc 3 run.R, ((S7.quotient ω l (Js l)).card : ℝ) ≤ eps2 Dstar * G.card) ∧              -- (iii)+(iv)
  ∑ l ∈ Finset.Icc 3 run.R, detl run G l
      ≤ 3 * EG.epsA Dstar * G.card + 60 * G.card / Dstar + 2 * FQ (Real.logb 2 Dstar) * G.card              -- (iv)
-- S7.quotient ω l J := S7.quotient' ω l J (S7.xiChosen ω l J)  (the chosen xi_l lies in the Markov event by lemOneOutcome(3)).
-- '2F(log2 D_*) < 2^-1000' and 'theta_Q <= 1/4' (= Gamma4) are not needed downstream; optional lemmas.
```

**Hazards.**

- **M-INTEGER (inherits HB-M-INTEGER, blueprint_s2a)** (blocker): M_l is a REAL in (R2), but this chunk uses it as a NUMBER OF COLOURS: the copy counts of lemVstar/lemUHsplit sum over the 3M_l PAR colours and the 4M_l HUB colours ('summing over the 4M_l HUB colours'), lemPay(c) uses the SDR bound (4M_l)^-4 for lists in [4M_l] = [K^HUB_l], lemUHsplit(ii) uses 3k_h <= 4M_l, and (M_l - 1) is a J-edge cap. A Lean statement needs the manuscript decision proposed in blueprint_s2a (M_l := ceil(max(2^40, 2^16 T log2^4 T)) in N). Checked for this chunk: every inequality survives with integer M_l, because the chunk uses only M_l >= 2^40, M_l <= lambda_{l-2}^1.6, M_{l-1} >= 2M_l, sum_l 1/M_l <= 2/D_*, sum_l psi(M_l) <= 2.1 psi(D_*) (lemTower(b), re-checked by the s2a blueprint for the ceiling) and exact integer identities that do not involve M_l's value. Fallback without manuscript change: [ceil(3M_l)], [ceil(4M_l)] colours; then 3M_l, 4M_l in X_{V,l} must become the same ceilings (X_{V,l} is a stage-1 functional, its definition must match the palette size exactly).
- **S7-ROUNDSTEP-IN-DEFS** (risk): lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get locked Specs, the whole construction s7:consRound must be a Defs construction (chunk s7a) with the Markov choice written as `if h : ∃ ξ, 0 < (xiDist l).w ξ ∧ markovEvent ω l J ξ then Classical.choose h else default` (no proof term of a theorem inside a Def). Alternative: keep these four statements proof-internal (EG/Proof/Quot/*) and lock only thmJVps (whose statement mentions no construction). Decision needed with the s7a blueprint; recommendation: Specs for lemVstar, lemEXprime (pure stage-1 statements) and thmJVps/lemGammaSat; lemPay, lemUHsplit, propCost, lemOneOutcome as Tier-2 Specs over the s7a Defs, so that provers can work in parallel.
- **S7-UNLABELLED-PAR-MULT** (risk): The identity '[w] is not isolated in exactly max_{w'} m_kappa(w,w') of the PAR sub-layers B^{P,(iota)}_kappa' is stated only in the unlabelled preamble of the subsection 'Quotient size and payments' (s7.tex l.711-713, 'As in Lemma MULT'). lemCC(iii) and lemUHsplit(ii) use it; the HUB analogue is lemMULT's second statement. It must become a named Lean lemma of chunk s7a (next to lemMULT), and msreport must record the edge lemUHsplit -> it. It also depends on the Lean quotient keeping PARALLEL edges apart: Q_l's vertex type must carry the rank iota (e.g. QVert V := (Bool × ℕ × ℕ) × V = (layer kind, colour, rank) × vertex); if the rank were dropped, Finset (Sym2 _) would merge parallel edges and both the vertex count and the lift would be wrong.
- **UH-VERTEX-DECOMP** (risk): (ii) rests on an exact identity |V(Q_l)| = Σ_{kappa∈[3M_l]} Σ_{w∈Pool_l} max_{w'} m_kappa(w,w') + Σ_{kappa∈[4M_l]} (Σ_{h∈D_l} max_w m_kappa(h,w) + Σ_{w∈Pool_l} max_h m_kappa(h,w)), i.e. the quotient's vertex set is the disjoint union over sub-layers of the non-isolated vertices, and the number of ranks iota at which a vertex is non-isolated equals its maximal multiplicity. The text calls these 'four kinds' without proof. In Lean: a Finset.card_sigma decomposition over the tag (kind, kappa, iota) plus the MULT-type counts (lemMULT's second statement and its unlabelled PAR analogue). ~300 lines; this is where a wrong Defs (e.g. dropping isolated vertices per layer instead of per sub-layer) would change the count.
- **UH-AVERAGE-LISTS** (risk): 'Averaging over the lists gives (ii)': PAR copies and ultra-hub copies are bounded CONDITIONALLY on the lists (lemCC(iii), lemUltra(iv) hold for every outcome of the lists), non-ultra-hub and HUB-junction copies deterministically. Lean: xiDist = lists-law ×ˢ orders-law and EG.FinDist.expect_prod; the s7a Specs of lemCC(iii)/lemUltra(iv) must be stated as 'for every list outcome, E_orders[...] <= bound' (not only unconditionally), else (ii) cannot be assembled.
- **UH-NUMERICS-F** (risk): (iv) needs real-exponent analysis of F(x) = (3184 + 30400 log2 x) x^-90.2: F decreasing on [2^25, ∞) (derivative sign: 30400/ln 2 < 90.2 (3184 + 30400 log2 x)), F(2x) <= F(x)/2 (first factor at most doubles, x^-90.2 gains 2^-90.2), and 2F(2^25) <= 2·2^20·2^-2255. Also the halving λ_{l-2} >= 2 λ_{l-1}: lemLacunary(ii) states only the F-sum consequence; the raw recursion λ_r >= 2^{λ_{r+1}/A} (from propDegRec) must be exported as its own Lean lemma, plus 2^{x/105} >= 2x for x >= 2^25. log2 thult_l needs thult_l >= 1 (true: thult_l >= 2^8, lemUltra proof) for monotonicity of log2 on the floor. Rpow/logb lemma work ~250 lines; no galactic evaluation (λ is only bounded below).
- **UH-DET-TERMS** (note): Re-derived: 78 n M_l/H^cd_l = 624 n M_l^3/λ^95; with log2 thult_l <= log2(M_l H^cd_l/7) = log2(λ^95/(56 M_l)) <= 95 log2 λ the last two det terms are <= n M_l^3 (624 + 2560 + 30400 log2 λ)/λ^95 <= n F(λ_{l-2}) using M_l^3 <= λ^4.8. Σ_l 3|D_l| <= 1.5 eps_A n (factor-2 slack is deliberate). Σ 30 n/M_l <= 60 n/D_*. All correct.
- **UH-GAMMA4** (note): theta_Q <= 1/4 is literally Gamma4; '2F(log2 D_*) < 2^-1000' is never used. The Spec should state the bound with eps2 Dstar and leave '<= 1/4' to Gamma4 (the manuscript's 'theta_Q <= 1/4 by condition G4' is not a separate claim).
- **UH-SAME-OUTCOME** (note): (iii) needs the Markov event at EVERY round for the J_l actually fed to the consumer; with the J-consumer defined via xiChosen (dite on nonemptiness) this is the per-(ω, l, J) fact lemOneOutcome(3), so (iii) can be stated for every admissible family Js (as above), which is what S7-MIXC-INTERFACE option B' provides.

**Effort.** ~850 lines, difficulty 4/5. (ii): vertex-count identity ~300, non-ultra-hub count ~120, junction count ~60, assembly with lemCC/lemUltra + Fubini ~100; (iii) ~50; (iv) numerics (F, lacunary, (K2)/lemTower(e) sums) ~250 (rpow).

### `s7:lemOneOutcome` — lemma: One joint outcome exists (s7.tex:1152)

**Status:** x2+RT. **Formalization:** No single Spec for the 'joint outcome' (it is a procedure). Split into: (1) proof lemma EG.S7.exists_stage1_selected (Markov, ω ∈ supp); (2) automatic from the deterministic s4/s5 Specs + MixCTPVApplicable (blueprint_s6b); (3) lemma EG.S7.xiChosen_mem (the Markov event is nonempty for every (ω, l, J)) and its consequences. Optional Tier-2 Spec EG/Spec/Quot/OneOutcome.lean bundling (1)-(3); proof EG/Proof/Quot/OneOutcome.lean

**Statement (precise restatement).** Setting: S7Hyp, a designation delta. There is a joint outcome (stage-1 outcome ω, stage-3 labels of all parts, draws xi_R, ..., xi_3) such that: (1) X'(ω) <= 3 E X'; (2) the stage-3 labels of every part lie in its good event (Lemma TPV for every standalone pre-part Z with the data (Z^0, O_Z, Ret_Z) of consOrder step (1); Lemma PV via s5:lemChild for every non-demoted light part; Theorem VX+ via s5:lemDemoted for every demoted light part); (3) at every round 3 <= l <= R, xi_l lies in the event of s7:consRound(f), consequently copies_l <= 4(X_{V,l} + det_l) and payrd_l <= 4(n/(256 M_l^3) + 5.5 n M_l/H^cd_l). The outcome is obtained sequentially: (i) stage 1 in {X' <= 3E X'} (probability >= 2/3 by Markov); stage 2 is then determined; (ii) each part's stage-3 labels in its own good event (each has probability >= 1/2 - o(1) > 0 with o(1) <= 1/100 by Gamma3; the events involve disjoint label families and hold for every admissible later edge set); (iii) for l = R, ..., 3: steps (1)-(3) of s6:consOrder (deterministic given the past), then xi_l chosen in the event (f) (conditional probability >= 1/2 by Markov, for EVERY past), build Q_l, fix Dec_l, lift, record LentJV_l; (iv) rounds 2, 1: steps (1)-(2) of consOrder, J_2 = J_1 = ∅.

**Definitions needed.**

- *stage-1 outcome omega and its law (families 1a COL-JV colourings, 1b zones, 1c JS labels, 1d pool labels)* — s7:defSchedule stage 1: four mutually independent label families, one joint finite law; every stage-1 quantity (X_U, X_pool, X_V, JV-bad, Pool_l) is a function of omega [s7:defSchedule, s3:defCOL, s5:defZones, s7:defPool] — EG: partly: EG.FinDist (pi, prod, ofFinset, expect, Markov lemmas) exists; the Stage1 type/law is proposed in the s3 layer (blueprint_s6b calls it S3.stage1Dist, blueprint_s5 calls it stage1Law: names must be unified)
- *the round step at round l (items, live items, PAR objects, cherries, HUB lists, SDR, junctions, layers, rank split, quotient Q_l, lift, Obj_l, LentJV_l), its randomness xi_l, copies_l = |V(Q_l)|, payrd_l, the event (f)* — s7:consRound (a)-(h); xi_l = (eta_h uniform bijection of [4M_l], zeta_{h,u} uniform 3-subset of [4M_l], <_u uniform linear order of V(G)), mutually independent; copies_l := |V(Q_l)|; payrd_l := #edges paid in (d) and (e3); event (f) := {copies_l <= 4 E[copies_l|Past]} n {payrd_l <= 4 E[payrd_l|Past]} [s7:consRound, s7:defSchedule (chunk s7a)] — EG: no: proposed EG/Defs/Quot/Round.lean (chunk s7a): S7.RoundRand l, S7.xiDist run G l : FinDist, S7.roundOut omega l J xi (items, paid sets, quotient, objs, lentJV), S7.copies, S7.payrd, S7.markovEvent, S7.xiChosen omega l J (dite on the nonemptiness of the event, Classical.choose), S7.quotient omega l J : FGraph (S7.QVert V), S7.consumer omega : S6.JConsumer
- *Lost_Z, Lost_l, Q*_Z, Ret_Z, O_Z, X_U, dem, lp* — s6:defLending; X_U := 80 dem + 369 lp + sum_l (169 + M_l)|Lost_l| [s6:defLending, s5:defStages] — EG: no: proposed EG.S6.lost / lostRound / qs / ret / OZ / XU, EG.S5.dem / lp (blueprint_s6b, blueprint_s5)
- *finite probability, expectation, Markov, Fubini* — s1:citMarkov [s1:citMarkov] — EG: yes: EG.FinDist, FinDist.expect, prob, prod/pi/compProd, expect_prod (Fubini), two_thirds_le_prob_le_three_mul_expect, half_le_prob_le_four_mul_expect_and, exists_mem_le_mul_expect_ae (EG/Defs/Prob/FinDist.lean, EG/Lib/Prob/Basic.lean)
- *X', E X'* — s7:defXprime [s7:defXprime] — EG: no: EG.S7.Xprime (this chunk)
- *stage-3 good events of TPV / PV (child) / VX+ (demoted)* — s4:lemTPV, s4:lemPV + s5:lemChild, s4:thmVXp + s5:lemDemoted [s4, s5] — EG: no: with the deterministic Specs recommended by blueprint_s4 (TPV-DET-SPEC, PV-DET-SPEC, VX-DET-SPEC) the good events are proof-internal (Lib) and the Specs' conclusions are label-free; MIX-C takes S4.TPVGood (Z0, O_Z ω, Ret_Z ω) etc. as hypotheses (blueprint_s6b)
- *processing order, Past_l, J_l* — s6:consOrder, s7:defSchedule [s6:consOrder] — EG: no: proof-internal chain of the MIX-C proof (blueprint_s6b ORDER-RECURSION)

**Dependencies.** Declared: `s7:defSchedule`, `s7:consRound`, `s6:consOrder`, `s4:lemTPV`, `s4:lemPV`, `s4:thmVXp`, `s5:lemChild`, `s5:lemDemoted`, `s7:lemEXprime`, `s7:lemPay`, `s7:lemUHsplit`, `s1:citMarkov`, `s1:condG3`.  
From the proof: `s1:citMarkov`, `s7:defSchedule`, `s7:defXprime`, `s7:consRound`, `s6:consOrder`, `s4:lemTPV`, `s4:lemPV`, `s5:lemChild`, `s4:thmVXp`, `s5:lemDemoted`, `s6:thmMIXC`, `s1:condG3`, `s7:lemUHsplit`, `s7:lemPay`.  
(i): citMarkov(a) with X' >= 0 (s7:defXprime). (ii): s4:lemTPV applicability to (Z^0, O_Z, Ret_Z) is MIX-C(a)'s TPV bullet (s6:thmMIXC, undeclared; blueprint_s6b MixCTPVApplicable); s5:lemChild / s5:lemDemoted for light parts; Gamma3 for the o(1) <= 1/100. (iii): citMarkov(b),(c) conditionally (xi_l independent of the past), s7:consRound(f); the explicit bounds of (3) from s7:lemUHsplit(ii) and s7:lemPay(c). s7:lemEXprime is declared but not used (only E X' >= 0 finite matters).

**Used by:** s7:propCost, s7:thmJVps.

**Randomness.** The full schedule: stage 1 (joint law of 1a-1d; the selection conditions nothing, it fixes an outcome in an event of probability >= 2/3); stage 3 (per part, independent label families, each fixed inside its good event; in Lean these disappear because the s4/s5 Specs are deterministic); rounds l = R..3 (xi_l fresh: independent of stage 1, stage 3 and xi_{l'}, l' > l; its law is (S7.xiDist run G l), not conditioned on anything; 'E[·|Past_l]' = expectation over xi_l with (ω, J_l) fixed). In Lean no joint probability space over all rounds is ever built: each choice is an existence statement for a FIXED earlier outcome.

**Lean shape.**

```lean
-- EG/Proof/Quot/OneOutcome.lean   (or Tier-2 Spec EG/Spec/Quot/OneOutcome.lean)
theorem exists_stage1_selected (h : S7Hyp N0 Dstar G run) (δ) :                                   -- (1)
    ∃ ω, 0 < (S3.stage1Dist run G).w ω ∧ S7.Xprime (δ := δ) ω ≤ 3 * (S3.stage1Dist run G).expect (S7.Xprime (δ := δ))
  -- from EG.FinDist.exists_mem_le_mul_expect_ae (A := univ, c := 3) and Xprime_nonneg
theorem stage3_ok (h : S7Hyp ...) : ∀ ω ∈ (S3.stage1Dist run G).supp,                              -- (2)
    (∀ l a, a ∈ run.Std G l → S4.TPVGood (run.Z0 G l a) (S6.OZ ω l a) (S6.ret ω l a)) ∧ S5.LightStage3OK ω
  -- = TPVStatement ∘ MixCTPVApplicable, ChildExistsStatement, DemotedExistsStatement (deterministic Specs)
theorem xiChosen_mem (h : S7Hyp ...) : ∀ ω l J, S6.JPlusProps ω l J →                               -- (3)
    0 < (S7.xiDist run G l).w (S7.xiChosen ω l J) ∧ S7.markovEvent ω l J (S7.xiChosen ω l J)
  -- from EG.FinDist.half_le_prob_le_four_mul_expect_and (copies, payrd ≥ 0); holds for EVERY J
-- consequences (with lemUHsplit(ii), lemPay(c)): copies ≤ 4 (XVl ω l + detl l), payrd ≤ 4 (n/(256 M^3) + 5.5 n M/H)
-- (iv) rounds 2,1: inside MIX-C (JS-LC/consumer not called for l ≤ 2).
```

**Hazards.**

- **S7-ROUNDSTEP-IN-DEFS** (risk): lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get locked Specs, the whole construction s7:consRound must be a Defs construction (chunk s7a) with the Markov choice written as `if h : ∃ ξ, 0 < (xiDist l).w ξ ∧ markovEvent ω l J ξ then Classical.choose h else default` (no proof term of a theorem inside a Def). Alternative: keep these four statements proof-internal (EG/Proof/Quot/*) and lock only thmJVps (whose statement mentions no construction). Decision needed with the s7a blueprint; recommendation: Specs for lemVstar, lemEXprime (pure stage-1 statements) and thmJVps/lemGammaSat; lemPay, lemUHsplit, propCost, lemOneOutcome as Tier-2 Specs over the s7a Defs, so that provers can work in parallel.
- **OO-PROCEDURAL** (risk): The lemma asserts the existence of a JOINT outcome built by a sequential procedure whose later steps depend on earlier choices (J_l depends on xi_{l'} for l' > l through the decompositions and junk). There is no Lean object 'joint outcome': the faithful encoding is (1) a stage-1 existence lemma, (2) the deterministic stage-3 Specs, (3) the per-(ω, l, J) nonemptiness of the Markov event used INSIDE the consumer (xiChosen), with the recursion over rounds done by the MIX-C chain (s6:consOrder). This re-encoding must be recorded as a T0 decision; it is sound because every bound used is uniform in the past (checked: lemUHsplit(ii), lemPay(c) hold 'for every past'; the consumer reads the past only through J_l and ω).
- **OO-SUPP** (risk): Step (i) must return an ω of POSITIVE weight: the s5 Specs (K-RED, Child, blueprint_s5) and hence MIX-C quantify ω ∈ supp. The manuscript's Markov step gives an event of probability >= 2/3; EG.FinDist.exists_mem_le_mul_expect_ae yields 0 < w ω directly. A statement 'for some ω' without the support condition would not feed K-RED.
- **OO-STAGE3-DETERMINISTIC** (note): With the deterministic TPV/PV/VX+ Specs (blueprint_s4), '(2) the stage-3 labels lie in the good events' has no Lean content beyond 'the deterministic conclusions hold for (Z^0, O_Z ω, Ret_Z ω) and the light parts', and the 'o(1) <= 1/100 by Gamma3' becomes the s4 size predicates (TPVSize etc.) at |Z| >= P_R >= 2 N0, supplied through N0Cond + Gamma3 in MIX-C(a). The manuscript's remark that the events of distinct parts involve disjoint label families (no union bound) is not needed in Lean.
- **OO-MARKOV-ZERO** (note): Markov with E X = 0 (possible in degenerate cases, e.g. no ports) is handled by the existing FinDist lemmas (they assume only X >= 0 on the support).
- **OO-UNDECL** (note): Uses s6:thmMIXC(a) (TPV applicability) and s7:defXprime (X' >= 0), undeclared; s7:lemEXprime declared, unused.

**Effort.** ~160 lines, difficulty 2/5. (1) ~40; (2) ~60 glue from the s4/s5/s6 Specs; (3) ~60 (Markov for two nonnegative variables, dite unfolding of xiChosen).

### `s7:propCost` — proposition: Cost on the chosen outcome (s7.tex:1230)

**Status:** x2+RT. **Formalization:** Defs EG.eps1, EG.C0 (EG/Defs/Quot/Constants.lean) + Tier-2 Spec EG/Spec/Quot/Cost.lean (CostStatement) + lemma C0_le (Gamma4 → C0 D ≤ D/2 + 1091); proof EG/Proof/Quot/Cost.lean

**Statement (precise restatement).** Setting: S7Hyp, a designation delta, an outcome as in s7:lemOneOutcome (stage-1 ω ∈ supp with X'(ω) <= 3 E X'; stage-3 in the good events; each xi_l in the event (f)), with the round step of s7:consRound as the J-consumer. Then the decomposition of E(G) given by s6:thmMIXC has at most (D_*/2 + 1085 + eps_1(D_*)) n + 2 Σ_{l=3}^{R} f(Q_l) objects, where eps_1(D) := eps_K(D) + 169 eps_A(D) + 252/D + 1.5 eps_CONC(D) + 3 eps_X(D) + 9/D, eps_K = eps_Chain (s5:lemParent), eps_A(D) = 31 eps/(C' log2 log2 D), eps_CONC as in s6:thmCONCL(iv), eps_X as in s7:lemEXprime. Itemization (Table s7:tabCost): K-RED (D_*/2 + 745 + eps_K)n + [80 dem + 369 lp]; TPV 169(2 + eps_A)n + [169 Σ_l |Lost_l|]; JS-LC cycles 252 n/D_* + 1.5 eps_CONC n; J^lost items [Σ_l (M_l - 1)|Lost_l|]; pooled and JV-bad items [X_pool]; unpaired fresh legs 2n; SDR failures and loops 9n/D_*; lifts 2 Σ_l f(Q_l); all bracketed terms together <= X_U + X_pool <= X' <= 3 E X' <= 3 eps_X n. The constant is 745 + 338 + 2 = 1085 and eps_1 is counted once. Consequently C_0 := D_*/2 + 1085 + eps_1(D_*) <= D_*/2 + 1091 under Gamma4 (eps_1 <= 6).

**Definitions needed.**

- *valid run and round data: run.Valid G Dstar, R, d_l, lambda_l = log2 d_l, M_l, P_l, D_l, Std_l, Z^0, E_l(Z), pre-part addresses* — s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T_l log2^4 T_l), T_l = d_l log2^2 d_l (a REAL in the manuscript; see blocker M-INTEGER); D_l = vertices in >= 2 round-l pre-parts; R = last round with d_R >= D_* [s2:defHBtp] — EG: no: proposed EG.HB.Run / Run.Valid / run.d / run.M (HB.MOf) / run.D / run.Std / run.Z0 / run.E (blueprint_s2a)
- *Lost_Z, Lost_l, Q*_Z, Ret_Z, O_Z, X_U, dem, lp* — s6:defLending; X_U := 80 dem + 369 lp + sum_l (169 + M_l)|Lost_l| [s6:defLending, s5:defStages] — EG: no: proposed EG.S6.lost / lostRound / qs / ret / OZ / XU, EG.S5.dem / lp (blueprint_s6b, blueprint_s5)
- *the round step at round l (items, live items, PAR objects, cherries, HUB lists, SDR, junctions, layers, rank split, quotient Q_l, lift, Obj_l, LentJV_l), its randomness xi_l, copies_l = |V(Q_l)|, payrd_l, the event (f)* — s7:consRound (a)-(h); xi_l = (eta_h uniform bijection of [4M_l], zeta_{h,u} uniform 3-subset of [4M_l], <_u uniform linear order of V(G)), mutually independent; copies_l := |V(Q_l)|; payrd_l := #edges paid in (d) and (e3); event (f) := {copies_l <= 4 E[copies_l|Past]} n {payrd_l <= 4 E[payrd_l|Past]} [s7:consRound, s7:defSchedule (chunk s7a)] — EG: no: proposed EG/Defs/Quot/Round.lean (chunk s7a): S7.RoundRand l, S7.xiDist run G l : FinDist, S7.roundOut omega l J xi (items, paid sets, quotient, objs, lentJV), S7.copies, S7.payrd, S7.markovEvent, S7.xiChosen omega l J (dite on the nonemptiness of the event, Classical.choose), S7.quotient omega l J : FGraph (S7.QVert V), S7.consumer omega : S6.JConsumer
- *J_l and its interface JPlusProps (types J^lost/J^hub/J^fr/J^par, J1, J2, J3, (ii))* — s6:lemJplus: the J-set produced by JS-LC at round l; the only information the J-consumer gets about the past [s6:lemJplus] — EG: no: proposed EG.S6.JPlusProps omega l J (blueprint_s6b)
- *named small functions of D_*: eps_A, eps_U, eps_K = eps_Chain, eps_CONC, eps_X, eps_1, eps_2, F* — eps_A(D) = 31 eps/(C' log2 log2 D) (s2:lemTower(e)); eps_U(D) = 2462 (log2 D)^-205 (s5:lemExpect); eps_Chain(D) = 614/D + log2(2A log2(A log2 log2 D))/(371 (log2 log2 D)^2) (s5:lemParent); eps_CONC (s6:thmCONCL(iv)); eps_X (s7:lemEXprime); eps_1 (s7:propCost); eps_2 and F (s7:lemUHsplit) [s2:lemTower, s5:lemExpect, s5:lemParent, s6:thmCONCL, s7:lemEXprime, s7:propCost, s7:lemUHsplit] — EG: no: proposed EG.epsA, EG.S5.epsU, EG.S5.epsChain, EG.epsCONC, EG.S7.epsX, EG.S7.FQ, EG.eps1, EG.eps2 (EG/Defs/Quot/Constants.lean for the s7 ones)
- *constants and conditions: eps = 2^-5, C' = 103, A = 105, N0 (N0Cond), D_* with Gamma1..Gamma4, GammaCond* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condGamma] — EG: no: proposed EG.epsC, EG.N0Cond, EG.Gamma1core/Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1); Gamma4 and GammaCond must live after the s7 Defs (they mention eps1, eps2)
- *objects, decompositions, f* — s1:defObject [s1:defObject] — EG: yes: EG.Obj, EG.IsDecomp, EG.fnum, EG.FGraph (EG/Defs/Objects.lean, Fnum.lean, Graph.lean); optimal decompositions via EG.exists_isDecomp_length_eq_fnum
- *J-consumer, MIX-C output* — s6:defJconsumer, s6:thmMIXC [s6] — EG: no: EG.S6.JConsumer, MixCStatement (blueprint_s6b)
- *eps_1, C_0* — as in the statement [s7:propCost] — EG: no: proposed EG.eps1, EG.C0 (blueprint_s1 proposes the same names)
- *X', X_pool* — s7:defXprime [s7:defXprime] — EG: no: this chunk

**Dependencies.** Declared: `s6:thmMIXC`, `s6:thmCONCL`, `s7:lemLift`, `s7:lemPay`, `s7:lemEXprime`, `s7:lemOneOutcome`, `s5:lemKRED`, `s2:propParentless`, `s2:propOV`, `s7:consRound`, `s2:lemTower`, `s1:condG4`, `s6:defLending`, `s7:defXprime`.  
From the proof: `s6:thmMIXC`, `s7:lemLift`, `s7:lemPay`, `s7:lemOneOutcome`, `s7:lemEXprime`, `s7:defXprime`, `s6:defLending`, `s6:thmCONCL`, `s5:lemKRED`, `s2:propParentless`, `s2:propOV`, `s2:lemTower`, `s7:consRound`, `s1:condG4`.  
MIX-C(c) gives (D_*/2 + 745 + 338)n + eps_M n + [80dem + 369lp + 169 Σ|Lost_l|] + 1.5 Σ m_{Y,l} + Σ_l |Obj_l| with eps_M = eps_K + 169 eps_A + 252/D_* (its itemization uses s5:lemKRED, s2:propParentless (K4), s2:propOV (K2), s2:lemTower(e)); s6:thmCONCL(iv): 1.5 Σ m <= 1.5 eps_CONC n. Σ_l |Obj_l|: lemPay (a1) (M_l - 1)|Lost_l|, (a2)+(a3) the round-l summand of X_pool, (b) 2n in total, (d) Σ payrd_l <= 9n/D_* on the outcome of lemOneOutcome(3); lemLift(iv): lifted objects <= 2|Dec_l| = 2 f(Q_l). Bracket: 80dem + 369lp + Σ_l (169 + M_l - 1)|Lost_l| + X_pool <= X_U + X_pool <= X' (X_V >= 0) <= 3 E X' (lemOneOutcome(1)) <= 3 eps_X n (lemEXprime). Gamma4 only for C_0 <= D_*/2 + 1091.

**Used by:** s7:thmJVps, s7:lemGammaSat, s1:condG4, s1:defConstants, s1:thmMain, s7:remNonCirc.

**Randomness.** None inside the proof: deterministic on a FIXED outcome with properties (1)-(3) of lemOneOutcome. E X' is the unconditional stage-1 expectation (a number).

**Lean shape.**

```lean
-- EG/Defs/Quot/Constants.lean
noncomputable def eps1 (D : ℝ) : ℝ :=
  S5.epsChain D + 169 * EG.epsA D + 252 / D + 1.5 * EG.epsCONC D + 3 * S7.epsX D + 9 / D
noncomputable def C0 (D : ℝ) : ℝ := D / 2 + 1085 + eps1 D
-- EG/Spec/Quot/Cost.lean  (Tier-2; assumes MIX-C interface B', S7-MIXC-INTERFACE)
def CostStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V)
    (δ : S6.Designation run G), S7Hyp N0 Dstar G run →
  ∀ ω ∈ (S3.stage1Dist run G).supp, S7.Xprime (δ := δ) ω ≤ 3 * (S3.stage1Dist run G).expect (S7.Xprime (δ := δ)) →
    ∃ (Js : ℕ → Finset (Sym2 V)) (D : List (Obj V)),
      (∀ l ∈ Finset.Icc 3 run.R, S6.JPlusProps ω l (Js l)) ∧ IsDecomp (G.edges : Set (Sym2 V)) D ∧
      (D.length : ℝ) ≤ C0 Dstar * G.card + 2 * ∑ l ∈ Finset.Icc 3 run.R, (fnum (S7.quotient ω l (Js l)).edges : ℝ)
theorem C0_le (h : Gamma4 D) : C0 D ≤ D / 2 + 1091
-- The consumer is S7.consumer ω (s7a); its per-round output bound
--   b l J := (M_l - 1)|Lost_l| + Xpool_l ω + Σ_{a∈Std l}|F_a| + 2n/M_l + 2 fnum (S7.quotient ω l J).edges
-- is what MIX-C (B') receives.
```

**Hazards.**

- **S7-MIXC-INTERFACE (joint with s6b MIXC-SUMOBJ)** (risk): MIX-C Option B of blueprint_s6b bounds the consumer output by a J-INDEPENDENT b_l for every admissible J. The s7 consumer's output length is paid(J) + (lifted objects) <= [uniform stage-1/run bound] + 2 f(Q_l(J)), and f(Q_l(J)) is NOT uniform in J. Two faithful encodings: (B') recommended: MIX-C takes b : ℕ → Finset (Sym2 V) → ℝ with ∀ l J, JPlusProps ω l J → (C.out l J).1.length ≤ b l J, and concludes ∃ Js, (∀ l ∈ [3,R], JPlusProps ω l (Js l)) ∧ ∃ D, IsDecomp E(G) D ∧ D.length ≤ ... + Σ_{l∈[3,R]} b l (Js l); then Q_l := quotient ω l (Js l) serves BOTH (1) and (2) of thmJVps. (B) as in s6b: b_l := max over the finite set of admissible J ⊆ E(G) (Finset.sup, 0 if none) and Q_l := quotient at an argmax J*_l; (2) still holds because lemUHsplit(ii)/lemOneOutcome(3) bound |V(Q_l(J))| for EVERY admissible J. Both verified to prove thmJVps; B' is simpler and keeps thmJVps's Q_l = the constructed quotients. Must be fixed together with the s6b MIX-C Spec before the freeze.
- **S7-ROUNDSTEP-IN-DEFS** (risk): lemPay, lemUHsplit, lemOneOutcome(3) and propCost speak about objects of the round step (items, paid sets, the quotient Q_l, copies_l, payrd_l, the xi_l law, the chosen xi_l). If these lemmas get locked Specs, the whole construction s7:consRound must be a Defs construction (chunk s7a) with the Markov choice written as `if h : ∃ ξ, 0 < (xiDist l).w ξ ∧ markovEvent ω l J ξ then Classical.choose h else default` (no proof term of a theorem inside a Def). Alternative: keep these four statements proof-internal (EG/Proof/Quot/*) and lock only thmJVps (whose statement mentions no construction). Decision needed with the s7a blueprint; recommendation: Specs for lemVstar, lemEXprime (pure stage-1 statements) and thmJVps/lemGammaSat; lemPay, lemUHsplit, propCost, lemOneOutcome as Tier-2 Specs over the s7a Defs, so that provers can work in parallel.
- **COST-BRACKET** (note): The bracket identity needs MIX-C's [80 dem + 369 lp + 169 Σ_l |Lost_l|] to be stated with the SAME S5.dem, S5.lp, S6.lostRound as S6.XU (blueprint_s6b's MixCStatement does), and (169 + M_l - 1) <= (169 + M_l) summed over l ∈ [1,R] (Lost_l = ∅ for l <= 2) vs the J^lost term summed over l ∈ [3,R]. Checked.
- **COST-OPTIMAL-DEC** (note): 'lifted objects <= 2|Dec_l| = 2 f(Q_l)' needs Dec_l to be an OPTIMAL decomposition of E(Q_l); in the Defs pick it with EG.exists_isDecomp_length_eq_fnum (Classical.choose) — the manuscript's 'lexicographically first' rule is irrelevant. Q_l is loopless (lemSimple), so fnum's loop convention does not matter.
- **COST-FRESH-TWICE** (note): Σ|F_Z| <= 2n (K4) is used twice, legitimately: once for the TPV cost 169 Σ(|A_Z| + |F_Z| + |Lost_Z|) (the 338) and once for the unpaired fresh legs (the 2). Both appear in 1085 = 745 + 338 + 2.
- **COST-EPS1-NONNEG** (note): eps_1 >= 0 (needed for C_0 >= D_*/2 in thmMainProof/HI) holds only for large D (log2 log2 D > 0 for eps_A, and eps_Chain's inner log2(2A log2(A log2 log2 D)) >= 0); prove from Gamma1core, do not assume.

**Effort.** ~420 lines, difficulty 3/5. Consumer per-round bound b l J from lemPay + lemLift(iv) ~150; applying MIX-C and summing ~150; the bracket and eps_1 arithmetic ~100; C0_le ~20.

### `s7:thmJVps` — theorem: Theorem JV+* (s7.tex:1322)

**Status:** x2 (written JV+*); this text x0. **Formalization:** Spec EG/Spec/Quot/JVps.lean (JVpsStatement), the statement consumed by the main assembly; proof EG/Proof/Quot/JVps.lean

**Statement (precise restatement).** Assume D_* satisfies Gamma1-Gamma4 (with N0 as in s1:defConstants). Let G be a (finite simple) graph with n >= N0 vertices and d_1 = 2|E(G)|/n >= D_*. Take any valid HB*^{tau+} run on G, any designation delta, and no VX-parts. Then there are simple graphs Q_3, ..., Q_R (none if R < 3), each without isolated vertices, such that (1) f(G) <= C_0 n + 2 Σ_{l=3}^{R} f(Q_l), C_0 := D_*/2 + 1085 + eps_1(D_*); (2) Σ_{l=3}^{R} |V(Q_l)| <= theta_Q n, theta_Q = eps_2(D_*) <= 1/4. eps_1, eps_2 are the explicit functions of s7:propCost and s7:lemUHsplit. (Descriptive, not a claim to formalize: items at ultra hubs cost no collision payments; they pay only the standard costs and add quotient vertices only through lemUHsplit.)

**Definitions needed.**

- *valid run and round data: run.Valid G Dstar, R, d_l, lambda_l = log2 d_l, M_l, P_l, D_l, Std_l, Z^0, E_l(Z), pre-part addresses* — s2:defHBtp (R0)-(R5); M_l := max(2^40, 2^16 T_l log2^4 T_l), T_l = d_l log2^2 d_l (a REAL in the manuscript; see blocker M-INTEGER); D_l = vertices in >= 2 round-l pre-parts; R = last round with d_R >= D_* [s2:defHBtp] — EG: no: proposed EG.HB.Run / Run.Valid / run.d / run.M (HB.MOf) / run.D / run.Std / run.Z0 / run.E (blueprint_s2a)
- *designation delta, class Y(u), d_{Y,l}(h), c^agg_{h,l}* — s6:defDesign: Y(u) in anc_l(u) for every classed port u of round l >= 3; d_{Y,l}(h) = #{hu in E_l(Z): Z in Std_l, u in Q_Z, Y(u) = Y}; c^agg_{h,l} = #{Y : d_{Y,l}(h) >= 1} [s6:defDesign] — EG: no: proposed EG.S6.Designation with cls, d, cAgg (blueprint_s6b)
- *constants and conditions: eps = 2^-5, C' = 103, A = 105, N0 (N0Cond), D_* with Gamma1..Gamma4, GammaCond* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condGamma] — EG: no: proposed EG.epsC, EG.N0Cond, EG.Gamma1core/Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1); Gamma4 and GammaCond must live after the s7 Defs (they mention eps1, eps2)
- *named small functions of D_*: eps_A, eps_U, eps_K = eps_Chain, eps_CONC, eps_X, eps_1, eps_2, F* — eps_A(D) = 31 eps/(C' log2 log2 D) (s2:lemTower(e)); eps_U(D) = 2462 (log2 D)^-205 (s5:lemExpect); eps_Chain(D) = 614/D + log2(2A log2(A log2 log2 D))/(371 (log2 log2 D)^2) (s5:lemParent); eps_CONC (s6:thmCONCL(iv)); eps_X (s7:lemEXprime); eps_1 (s7:propCost); eps_2 and F (s7:lemUHsplit) [s2:lemTower, s5:lemExpect, s5:lemParent, s6:thmCONCL, s7:lemEXprime, s7:propCost, s7:lemUHsplit] — EG: no: proposed EG.epsA, EG.S5.epsU, EG.S5.epsChain, EG.epsCONC, EG.S7.epsX, EG.S7.FQ, EG.eps1, EG.eps2 (EG/Defs/Quot/Constants.lean for the s7 ones)
- *objects, decompositions, f* — s1:defObject [s1:defObject] — EG: yes: EG.Obj, EG.IsDecomp, EG.fnum, EG.FGraph (EG/Defs/Objects.lean, Fnum.lean, Graph.lean); optimal decompositions via EG.exists_isDecomp_length_eq_fnum
- *the round step at round l (items, live items, PAR objects, cherries, HUB lists, SDR, junctions, layers, rank split, quotient Q_l, lift, Obj_l, LentJV_l), its randomness xi_l, copies_l = |V(Q_l)|, payrd_l, the event (f)* — s7:consRound (a)-(h); xi_l = (eta_h uniform bijection of [4M_l], zeta_{h,u} uniform 3-subset of [4M_l], <_u uniform linear order of V(G)), mutually independent; copies_l := |V(Q_l)|; payrd_l := #edges paid in (d) and (e3); event (f) := {copies_l <= 4 E[copies_l|Past]} n {payrd_l <= 4 E[payrd_l|Past]} [s7:consRound, s7:defSchedule (chunk s7a)] — EG: no: proposed EG/Defs/Quot/Round.lean (chunk s7a): S7.RoundRand l, S7.xiDist run G l : FinDist, S7.roundOut omega l J xi (items, paid sets, quotient, objs, lentJV), S7.copies, S7.payrd, S7.markovEvent, S7.xiChosen omega l J (dite on the nonemptiness of the event, Classical.choose), S7.quotient omega l J : FGraph (S7.QVert V), S7.consumer omega : S6.JConsumer
- *C_0, theta_Q* — C_0 = D/2 + 1085 + eps_1(D); theta_Q = eps_2(D) [s1:defConstants(iv),(v); s7:propCost; s7:lemUHsplit] — EG: no: EG.C0, EG.eps2 (this chunk)
- *simple graph without isolated vertices, on its own vertex type* — Q_l is simple (s7:lemSimple) with every vertex on an edge [s7:lemSimple] — EG: yes: EG.FGraph W (simple by construction); 'no isolated vertices' as ∀ v ∈ Q.verts, ∃ e ∈ Q.edges, v ∈ e (as in EG.Spec.HIHyp)

**Dependencies.** Declared: `s7:propCost`, `s7:lemUHsplit`, `s7:lemSimple`, `s7:lemLift`, `s7:lemOneOutcome`, `s6:thmMIXC`, `s2:propExists`, `s7:lemPay`, `s7:lemUltra`, `s1:condGamma`.  
From the proof: `s7:lemOneOutcome`, `s7:lemSimple`, `s7:lemLift`, `s6:thmMIXC`, `s7:propCost`, `s7:lemUHsplit`, `s7:lemPay`, `s7:lemUltra`, `s1:defObject`, `s1:condG4`.  
Outcome from lemOneOutcome; each Q_l simple without isolated vertices (lemSimple); the round step is a J-consumer (lemLift(iv)); MIX-C gives a decomposition; propCost bounds it, so f(G) <= its length (definition of f, s1:defObject). (2): lemUHsplit(iii),(iv) on the same outcome. The ultra-hub sentence: lemPay(e) + lemUltra. s2:propExists is only cited for the existence of a run (the theorem quantifies over runs); Gamma4 for theta_Q <= 1/4.

**Used by:** s7:thmMainProof, s7:remNonCirc.

**Randomness.** None in the statement (existential, deterministic). The proof selects: a stage-1 outcome ω ∈ supp with X' <= 3 E X' (stage-1 law), and inside the consumer, for every round, xi_l in the Markov event (xi_l law, past fixed). Stage-3 labels do not appear (deterministic s4/s5 Specs).

**Lean shape.**

```lean
-- EG/Spec/Quot/JVps.lean
def JVpsStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (N0 Dstar : ℝ) (G : FGraph V) (run : HB.Run V)
    (δ : S6.Designation run G),
    EG.N0Cond N0 → EG.GammaCond N0 Dstar → run.Valid G Dstar → N0 ≤ (G.card : ℝ) → Dstar ≤ run.d G 1 →
    ∃ (W : ℕ → Type) (Q : (l : ℕ) → FGraph (W l)),
      (∀ l ∈ Finset.Icc 3 run.R, ∀ v ∈ (Q l).verts, ∃ e ∈ (Q l).edges, v ∈ e) ∧
      (fnum G.edges : ℝ) ≤ EG.C0 Dstar * G.card + 2 * ∑ l ∈ Finset.Icc 3 run.R, (fnum (Q l).edges : ℝ) ∧
      ∑ l ∈ Finset.Icc 3 run.R, ((Q l).card : ℝ) ≤ EG.eps2 Dstar * G.card
-- 'theta_Q ≤ 1/4' is the hypothesis Gamma4 (inside GammaCond); no VX-parts: nothing to state (never defined).
-- Proof: W l := S7.QVert V ((layer kind, colour, rank) × V), Q l := S7.quotient ω l (Js l) from CostStatement (B').
-- Consumer side (s7:thmMainProof) needs: run.d G 1 = 2 |E(G)| / n  and a Fintype adapter (HIHyp has no Fintype V).
```

**Hazards.**

- **S7-MIXC-INTERFACE (joint with s6b MIXC-SUMOBJ)** (risk): MIX-C Option B of blueprint_s6b bounds the consumer output by a J-INDEPENDENT b_l for every admissible J. The s7 consumer's output length is paid(J) + (lifted objects) <= [uniform stage-1/run bound] + 2 f(Q_l(J)), and f(Q_l(J)) is NOT uniform in J. Two faithful encodings: (B') recommended: MIX-C takes b : ℕ → Finset (Sym2 V) → ℝ with ∀ l J, JPlusProps ω l J → (C.out l J).1.length ≤ b l J, and concludes ∃ Js, (∀ l ∈ [3,R], JPlusProps ω l (Js l)) ∧ ∃ D, IsDecomp E(G) D ∧ D.length ≤ ... + Σ_{l∈[3,R]} b l (Js l); then Q_l := quotient ω l (Js l) serves BOTH (1) and (2) of thmJVps. (B) as in s6b: b_l := max over the finite set of admissible J ⊆ E(G) (Finset.sup, 0 if none) and Q_l := quotient at an argmax J*_l; (2) still holds because lemUHsplit(ii)/lemOneOutcome(3) bound |V(Q_l(J))| for EVERY admissible J. Both verified to prove thmJVps; B' is simpler and keeps thmJVps's Q_l = the constructed quotients. Must be fixed together with the s6b MIX-C Spec before the freeze.
- **JV-SAME-Q** (risk): (1) and (2) must hold for the SAME family Q_3..Q_R. Under MIX-C Option B' the J_l's of the actual chain are exposed and Q_l := quotient ω l J_l works for both; under Option B (J-independent b_l) one must take Q_l := quotient at a maximizer J*_l of f(Q_l(J)) over admissible J (a finite set), and (2) holds because the copies bound is uniform over admissible J. A Spec that states (1) and (2) with separately quantified Q's would be weaker than the manuscript and useless for HI.
- **JV-FINTYPE-ADAPTER** (note): EG.Spec.HIHyp quantifies over V : Type WITHOUT Fintype (FGraph carries its vertex Finset), while the stage-1 and xi_l laws (FinDist.pi over vertices) need [Fintype V]. thmMainProof must restrict G to the subtype ↥G.verts (Fintype), transport edges and fnum (EG.fnum_map), and map the Q_l back unchanged (their types are free). Also run.d G 1 = 2|E(G)|/n needs run.graph G 1 = G (s2 API). ~100 lines; flagged in formal/work/p1b/hi.md.
- **JV-QTYPE** (note): W l must be in Type (HIHyp's universe): S7.QVert V := (Bool × ℕ × ℕ) × V is. The rank tag is mandatory (S7-UNLABELLED-PAR-MULT). HUB sub-layers identify [w] with w: fine because h ∉ Pool_l ∋ w (lemSimple).
- **JV-HYPS** (note): The text says 'Assume D_* satisfies Gamma1-Gamma4', n >= N0, d_1 >= D_*. Gamma4 is used only for theta_Q <= 1/4 (and C_0 <= D_*/2 + 1091), so taking GammaCond (all four) is faithful; N0Cond is implicit ('N0 as in s1:defConstants'). 'Any designation' is ∀ δ; 'no VX-parts' has no Lean content (VX-parts are never defined in the formalization).
- **JV-ULTRA-PROSE** (note): The closing sentences about ultra hubs are commentary (lemPay(e) + lemUltra); not part of the Spec.

**Effort.** ~300 lines, difficulty 3/5. Assembly: selection (lemOneOutcome(1)), MIX-C with the s7 consumer (B'), CostStatement, UHsplit(iii)+(iv), no-isolated-vertices and FGraph packaging of Q_l ~300. Depends on essentially all of s2-s7.

### `s7:thmHI` — theorem: Theorem HI'' (layered quotient induction) (s7.tex:1359)

**Status:** elementary (DAG: 'elem.'); Lean pilot done and approved (formal/work/p1b/hi.md, hi.review1.md: APPROVE). **Formalization:** EXISTS: Spec EG/Spec/Quot/HI.lean (EG.Spec.HIHyp, EG.Spec.HIStatement), proof EG/Proof/Quot/HI.lean (EG.hi, no sorry), main-theorem interface EG/Proof/Quot/HIMain.lean (EG.mainInternal_of_hiHyp, EG.hiHyp_of_fintype_index adapter).

**Statement (precise restatement).** Let D_*, N0 be the constants of s1:defConstants and let C >= D_*/2 and vartheta ∈ [0, 1/2) be constants such that every graph G without isolated vertices, with n >= N0 vertices and d_1 = 2|E(G)|/n >= D_*, admits finitely many simple graphs Q_1, ..., Q_k (k >= 0) with f(G) <= C n + 2 Σ_i f(Q_i) and Σ_i |V(Q_i)| <= vartheta n. Then f(G) <= c |V(G)| for every graph G, where c := max(C/(1 - 2 vartheta), N0/2). (Lean: all four constants universally quantified reals; c written inline.)

**Definitions needed.**

- *objects, decompositions, f* — s1:defObject [s1:defObject] — EG: yes: EG.Obj, EG.IsDecomp, EG.fnum, EG.FGraph (EG/Defs/Objects.lean, Fnum.lean, Graph.lean); optimal decompositions via EG.exists_isDecomp_length_eq_fnum
- *graph without isolated vertices; d_1 = 2|E(G)|/n* — every vertex lies on an edge; real division [s1:convGraphs, s2:defHBtp (R0)] — EG: yes: as written in EG.Spec.HIHyp

**Dependencies.** Declared: `s1:factAdd`, `s1:defObject`, `s1:defConstants`.  
From the proof: `s1:factAdd`, `s1:defObject`.  
Minimal counterexample: factAdd(d) (isolated vertices), factAdd(a) (f <= |E|) for n < N0 and d_1 < D_*; minimality applied to the Q_i (each |V(Q_i)| <= vartheta n < n). s1:defConstants only names N0, D_*; the Lean statement quantifies them. The Lean proof adds one step not in the text (c >= 0 via K_2, needed because the Spec allows arbitrary real constants).

**Used by:** s7:thmMainProof, s7:remNonCirc, s1:remOrder.

**Randomness.** none

**Lean shape.**

```lean
-- EXISTING (formal/EG/Spec/Quot/HI.lean), approved:
def HIHyp (Dstar N₀ C ϑ : ℝ) : Prop :=
  ∀ (V : Type) (G : EG.FGraph V), (∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e) → N₀ ≤ (G.card : ℝ) →
    Dstar ≤ 2 * (G.edges.card : ℝ) / (G.card : ℝ) →
    ∃ (k : ℕ) (W : Fin k → Type) (Q : (i : Fin k) → EG.FGraph (W i)),
      (EG.fnum G.edges : ℝ) ≤ C * (G.card : ℝ) + 2 * ∑ i, (EG.fnum (Q i).edges : ℝ) ∧ ∑ i, ((Q i).card : ℝ) ≤ ϑ * (G.card : ℝ)
def HIStatement : Prop :=
  ∀ (Dstar N₀ C ϑ : ℝ), Dstar / 2 ≤ C → 0 ≤ ϑ → ϑ < 1 / 2 → HIHyp Dstar N₀ C ϑ →
    ∀ (V : Type) (G : EG.FGraph V), (EG.fnum G.edges : ℝ) ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) * (G.card : ℝ)
-- proved: EG.hi : EG.Spec.HIStatement;  EG.mainInternal_of_hiHyp; EG.hiHyp_of_fintype_index (any Fintype index set).
```

**Hazards.**

- **HI-DONE** (note): Formalized, proved without sorry and approved in P1b (hi.review1.md). No change needed. The only interface work left is on the producer side (JV-FINTYPE-ADAPTER in s7:thmJVps: HIHyp's G has no Fintype instance and d_1 is written as 2|E|/n, not run.d G 1).
- **HI-ISOLATED-UNUSED** (note): The hypothesis gives 'G without isolated vertices' but thmJVps does not need it; harmless (the producer ignores it).

**Effort.** ~0 lines, difficulty 1/5. Done (existing ~400 lines in EG/Proof/Quot/HI.lean + HIMain.lean).

### `s7:lemGammaSat` — lemma: The galactic conditions are satisfiable (s7.tex:1403)

**Status:** x2; R6: one clean-room AI review (G0, 2026-09-26). **Formalization:** Spec EG/Spec/Main/GammaSat.lean (GammaSatStatement: (i) threshold mu_1, (ii) tendsto of eps1, eps2, (iii) ∀ N0, ∀ᶠ D in atTop, GammaCond N0 D); proof EG/Proof/Main/GammaSat.lean (+ tendsto lemmas for epsCONC (s6), epsU (s5), epsChain (s5), epsA (s2))

**Statement (precise restatement).** Let N0 be as in s1:defConstants(ii) (in Lean: any real N0). (i) Each item (a)-(f) of Gamma1 holds for all sufficiently large real mu; hence there is mu_1 >= 1 such that all of them hold for every mu >= mu_1, and Gamma1 holds for every D_* > 2 with log2 log2 D_* >= mu_1. [Reductions: (a) holds for mu >= 2^8; (b) 2^mu >= 2^14 A mu^3 follows from the type-(E) inequality mu - (14 + log2 A) - 3 log2(A mu) >= 0; (c) is 1.6 mu - 2A log2(A mu) >= 0 (type (E)); (d) follows from mu - 8 - 2 log2(A mu) >= 0 (type (E)); (e) lambda^36 >= 2^240 (A mu)^{46A} is, after log2, 36 mu - 240 - 46A log2(A mu) >= 0 (type (E)); (f) by s3:lemCOLJVev(iii); type-(E) inequalities hold eventually by s3:lemCOLJVev(i).] (ii) eps_1(D_*) -> 0 and eps_2(D_*) -> 0 as D_* -> ∞ (finite sums of nonnegative explicit functions each tending to 0: 1/D, (6 log2 D + 12)/D, eps_A, eps_CONC (log*D/log D, log*D/log log D, (2 log*D + 2)/(log D)^{1/2}), eps_U, eps_K = eps_Chain, and F(log2 D) in eps_2). (iii) There is D_0 such that every D_* >= D_0 satisfies Gamma1-Gamma4 simultaneously: D_0 := max(2^{2^{mu_1}}, 2^117, 2^{(2 N0)^{1/C'}}, D''), with D'' from (ii) (eps_1 <= 6, eps_2 <= 1/4 for D >= D''). In particular a constant D_* as in s1:defConstants(iii) exists; mu_1 and D_0 are not computed.

**Definitions needed.**

- *constants and conditions: eps = 2^-5, C' = 103, A = 105, N0 (N0Cond), D_* with Gamma1..Gamma4, GammaCond* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condGamma] — EG: no: proposed EG.epsC, EG.N0Cond, EG.Gamma1core/Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1); Gamma4 and GammaCond must live after the s7 Defs (they mention eps1, eps2)
- *named small functions of D_*: eps_A, eps_U, eps_K = eps_Chain, eps_CONC, eps_X, eps_1, eps_2, F* — eps_A(D) = 31 eps/(C' log2 log2 D) (s2:lemTower(e)); eps_U(D) = 2462 (log2 D)^-205 (s5:lemExpect); eps_Chain(D) = 614/D + log2(2A log2(A log2 log2 D))/(371 (log2 log2 D)^2) (s5:lemParent); eps_CONC (s6:thmCONCL(iv)); eps_X (s7:lemEXprime); eps_1 (s7:propCost); eps_2 and F (s7:lemUHsplit) [s2:lemTower, s5:lemExpect, s5:lemParent, s6:thmCONCL, s7:lemEXprime, s7:propCost, s7:lemUHsplit] — EG: no: proposed EG.epsA, EG.S5.epsU, EG.S5.epsChain, EG.epsCONC, EG.S7.epsX, EG.S7.FQ, EG.eps1, EG.eps2 (EG/Defs/Quot/Constants.lean for the s7 ones)
- *Gamma1Items mu (items (a)-(e)), COL-JV column-3 predicate (item (f))* — s1:condGamma Gamma1; Table s3:tabCOLJV column 3 [s1:condGamma, s3:tabCOLJV] — EG: no: proposed EG.Gamma1Items (blueprint_s1), EG.S3.COLJVcol3 (s3 layer)
- *inequalities of type (E)* — a mu - b - c log2(A mu) >= 0, a > 0, b, c >= 0 [s3:lemCOLJVev] — EG: no: s3 layer (lemCOLJVev Spec)
- *log* and the tower* — log* x = least k >= 0 with x <= T_k, T_0 = 1, T_{k+1} = 2^{T_k} [s6 (before s6:thmCONC)] — EG: no: proposed EG.logStar (Found.Log)

**Dependencies.** Declared: `s1:condGamma`, `s7:propCost`, `s7:lemUHsplit`, `s5:lemExpect`, `s5:lemKRED`, `s2:lemTower`, `s7:lemEXprime`, `s6:thmCONCL`, `s1:defConstants`, `s3:lemCOL`, `s5:lemE1`, `s3:lemCOLJVev`.  
From the proof: `s3:lemCOLJVev`, `s1:condGamma`, `s7:propCost`, `s7:lemEXprime`, `s7:lemUHsplit`, `s2:lemTower`, `s6:thmCONCL`, `s5:lemExpect`, `s5:lemKRED`, `s5:lemParent`.  
Only the DEFINITIONS (formulas) of eps_1 (propCost), eps_X (lemEXprime), eps_2 and F (lemUHsplit), eps_A (lemTower(e)), eps_CONC (thmCONCL(iv)), eps_U (lemExpect), eps_K = eps_Chain (s5:lemKRED names it, s5:lemParent defines it: undeclared) and their 'tends to 0' clauses are used, not the lemmas' probabilistic content. s3:lemCOL and s5:lemE1 are declared but unused (Gamma2(b),(c) are consequences, not conditions; blueprint_s1 GAM-2BC).

**Used by:** s7:thmMainProof, s1:defConstants, s1:condGamma, s1:remOrder.

**Randomness.** none (explicit real functions of D_* and mu)

**Lean shape.**

```lean
-- EG/Defs/Quot/Constants.lean (after the s7 Defs):  def EG.Gamma4 (D) := eps1 D ≤ 6 ∧ eps2 D ≤ 1/4
--   def EG.GammaCond N0 D := Gamma1 D ∧ Gamma2a D ∧ Gamma3 N0 D ∧ Gamma4 D      (blueprint_s1)
-- EG/Spec/Main/GammaSat.lean
def GammaSatStatement : Prop :=
  (∃ μ₁ : ℝ, 1 ≤ μ₁ ∧ ∀ μ, μ₁ ≤ μ → EG.Gamma1Items μ ∧ EG.S3.COLJVcol3 μ) ∧                    -- (i)
  Filter.Tendsto EG.eps1 Filter.atTop (nhds 0) ∧ Filter.Tendsto EG.eps2 Filter.atTop (nhds 0) ∧    -- (ii)
  ∀ N0 : ℝ, ∀ᶠ D in Filter.atTop, EG.GammaCond N0 D                                                 -- (iii)
-- helper Specs/lemmas (other layers): EG.epsCONC_tendsto (s6), S5.epsU_tendsto, S5.epsChain_tendsto (s5),
--   EG.epsA_tendsto (s2), S3.colJVev (s3:lemCOLJVev), logStar growth: logStar D = o(logb 2 (logb 2 D)).
-- also export: Gamma1core D → 0 ≤ eps1 D ∧ 0 ≤ eps2 D   (needed by s7:thmMainProof / HI).
```

**Hazards.**

- **GS-LOGSTAR** (risk): eps_CONC -> 0 needs log* D = o(log2 log2 D) (for the term 200 eps log*D/(C' log log D)) and log* D = o((log2 D)^{1/2}); this is a genuine growth lemma for log* (e.g. log* x <= 2 + log2 log2 x for x >= 4 applied to log2 log2 D), not provided by Mathlib. It must use the same EG.logStar (tower definition) as s6:thmCONCL and s5 (EqLY). The manuscript's '(each of which tends to 0)' hides this work (~150 lines).
- **GS-COLJV-COUPLING** (risk): Item (f) of Gamma1 is the 18 column-3 inequalities of Table s3:tabCOLJV (a table, not a statement). GammaCond's (f)-part, s3:lemCOLJV's use of it, and s3:lemCOLJVev(iii)'s eventual form must all refer to ONE Lean predicate EG.S3.COLJVcol3 mu; if the s3 blueprint encodes the table twice (once for use, once for the eventual form), gammaSat proves the wrong thing silently. Cross-check with the s3 blueprint before the freeze.
- **GS-TYPEE-REDUCTIONS** (note): Checked: (b) 2^mu >= 2^14·105·mu^3 <=> mu >= 14 + log2 105 + 3 log2 mu, implied by mu - (14 + log2 A) - 3 log2(A mu) >= 0 since log2 mu <= log2(A mu) for mu >= 1; (d) likewise; (e) log2 of both sides (both positive); (c) literally type (E). Γ1 is on the RAY mu >= log2 log2 D_*: from ∃ mu_1 ∀ mu >= mu_1 and log2 log2 D -> ∞ we get ∀ᶠ D. D_* > 2 is part of Gamma1core.
- **GS-NONNEG** (note): thmMainProof/HI need C_0 >= D_*/2 (eps_1 >= 0) and theta_Q >= 0 (eps_2 >= 0). In Lean, logb of numbers in (0,1) is negative, so these are NOT true for all D; they hold under Gamma1core (log2 log2 D >= 2^8). Export them as lemmas next to gammaSat.
- **GS-GAMMA3-N0** (note): Gamma3 (log2 D)^103 >= 2 N0 is eventual in D for every real N0 (take D >= 2^{max(0,2N0)^{1/103}}); quantifier order ∀ N0, ∀ᶠ D matches s1:remOrder (N0 before D_*). No condition involves c_EG.
- **GS-UNDECL** (note): eps_K = eps_Chain is DEFINED in s5:lemParent (undeclared dependency); s3:lemCOL, s5:lemE1 declared but not used.

**Effort.** ~650 lines, difficulty 3/5. (i) type-(E) reductions for (a)-(e) ~150 + (f) via lemCOLJVev ~30; (ii) tendsto of each summand ~300 (log* growth ~150, rpow/zpow terms, F∘log2); (iii) combining eventualities + nonnegativity lemmas ~120.

### `s7:thmMainProof` — corollary: Corollary JV+*-EG; proof of the Main Theorem (s7.tex:1466)

**Status:** composition x2; this text x0. **Formalization:** Proof of the locked Tier-1 target EG.Spec.MainInternal in EG/Proof/Main.lean (theorem EG.mainInternal); optional unlocked explicit form EG.Spec.MainExplicit (blueprint_s1) proved from the same ingredients

**Statement (precise restatement).** Theorem s1:thmMain holds: with eps, sigma, C', A, N0, D_* as in s1:defConstants and D_* satisfying Gamma1-Gamma4, C_0 := D_*/2 + 1085 + eps_1(D_*), theta_Q := eps_2(D_*), c_EG := max(C_0/(1 - 2 theta_Q), N0/2), every graph G on n vertices satisfies f(G) <= c_EG n; in particular f(n) = O(n). Proof: D_* exists (s7:lemGammaSat); apply s7:thmHI with C := C_0 >= D_*/2 (eps_1 >= 0) and vartheta := theta_Q ∈ [0, 1/4] ⊂ [0, 1/2); its hypothesis holds: for G without isolated vertices, n >= N0, d_1 >= D_*, a valid run exists (s2:propExists), a designation exists (anc_l(u) ≠ ∅ for classed ports; choose Y(u) by a fixed rule), and s7:thmJVps gives Q_3..Q_R.

**Definitions needed.**

- *constants and conditions: eps = 2^-5, C' = 103, A = 105, N0 (N0Cond), D_* with Gamma1..Gamma4, GammaCond* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condGamma] — EG: no: proposed EG.epsC, EG.N0Cond, EG.Gamma1core/Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1); Gamma4 and GammaCond must live after the s7 Defs (they mention eps1, eps2)
- *named small functions of D_*: eps_A, eps_U, eps_K = eps_Chain, eps_CONC, eps_X, eps_1, eps_2, F* — eps_A(D) = 31 eps/(C' log2 log2 D) (s2:lemTower(e)); eps_U(D) = 2462 (log2 D)^-205 (s5:lemExpect); eps_Chain(D) = 614/D + log2(2A log2(A log2 log2 D))/(371 (log2 log2 D)^2) (s5:lemParent); eps_CONC (s6:thmCONCL(iv)); eps_X (s7:lemEXprime); eps_1 (s7:propCost); eps_2 and F (s7:lemUHsplit) [s2:lemTower, s5:lemExpect, s5:lemParent, s6:thmCONCL, s7:lemEXprime, s7:propCost, s7:lemUHsplit] — EG: no: proposed EG.epsA, EG.S5.epsU, EG.S5.epsChain, EG.epsCONC, EG.S7.epsX, EG.S7.FQ, EG.eps1, EG.eps2 (EG/Defs/Quot/Constants.lean for the s7 ones)
- *objects, decompositions, f* — s1:defObject [s1:defObject] — EG: yes: EG.Obj, EG.IsDecomp, EG.fnum, EG.FGraph (EG/Defs/Objects.lean, Fnum.lean, Graph.lean); optimal decompositions via EG.exists_isDecomp_length_eq_fnum
- *designation delta, class Y(u), d_{Y,l}(h), c^agg_{h,l}* — s6:defDesign: Y(u) in anc_l(u) for every classed port u of round l >= 3; d_{Y,l}(h) = #{hu in E_l(Z): Z in Std_l, u in Q_Z, Y(u) = Y}; c^agg_{h,l} = #{Y : d_{Y,l}(h) >= 1} [s6:defDesign] — EG: no: proposed EG.S6.Designation with cls, d, cAgg (blueprint_s6b)
- *EG.Spec.MainInternal* — ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V [s1:thmMain (Tier-1 target)] — EG: yes: EG/Spec/Main.lean (locked)
- *c_EG* — max(C_0/(1 - 2 theta_Q), N0/2) [s1:defConstants(vi)] — EG: no: EG.cEG (blueprint_s1; only needed for MainExplicit); HIMain uses ⌈c⌉₊ inline

**Dependencies.** Declared: `s7:thmHI`, `s7:thmJVps`, `s2:propExists`, `s7:lemGammaSat`, `s6:defDesign`, `s1:condGamma`, `s1:defConstants`.  
From the proof: `s1:thmMain`, `s7:lemGammaSat`, `s7:thmHI`, `s2:propExists`, `s6:defDesign`, `s2:defAncestors`, `s7:thmJVps`, `s1:defConstants`, `s1:condGamma`.  
s1:thmMain is the statement proved (undeclared: the node proves it); s1:remStatus cited for status only. Designation existence uses the definition of classed ports (s2:defAncestors, undeclared): Q_Z = U_Z \ F_Z, F_Z = {x : anc_l(x) = ∅}. Existence of N0 (s1:defConstants(ii), eventualities of s4 size conditions) is also needed in Lean (EG.exists_N0, blueprint_s1).

**Used by:** s1:thmMain.

**Randomness.** none

**Lean shape.**

```lean
-- EG/Proof/Main.lean
theorem EG.mainInternal : EG.Spec.MainInternal := by
  obtain ⟨N0, hN0⟩ := EG.exists_N0                                   -- s1:defConstants(ii)
  obtain ⟨D, hD⟩ := (gammaSat.2.2.2 N0).exists                         -- s7:lemGammaSat(iii)
  refine EG.mainInternal_of_hiHyp (Dstar := D) (N₀ := N0) (C := EG.C0 D) (ϑ := EG.eps2 D)
    (C0_ge_half hD) (eps2_nonneg hD) (by linarith [hD.gamma4.2]) ?_
  refine EG.hiHyp_of_fintype_index (fun V G hiso hn hd => ?_)
  -- restrict G to ↥G.verts (Fintype), obtain run (s2:propExists Spec), δ (designation_exists),
  -- apply JVpsStatement, index set ι := ↥(Finset.Icc 3 run.R), transport fnum back (EG.fnum_map).
-- optional: def EG.Spec.MainExplicit : Prop := ∀ N0 D : ℝ, EG.N0Cond N0 → EG.GammaCond N0 D →
--   ∀ (V : Type) (G : EG.FGraph V), (EG.fnum G.edges : ℝ) ≤ EG.cEG N0 D * G.card      (Tier-2, unlocked)
```

**Hazards.**

- **MAIN-PROPEXISTS-HYPS** (risk): s2:propExists says 'for every graph G a valid run exists', but its proof uses lemCap(ii), propOV, propDegRec, which need d_l >= D_* and Gamma1/Gamma2a (termination: d_{l+1} < d_l while d_l >= D_*). Its Lean Spec will carry hypotheses (Gamma1core, Gamma2a, perhaps n >= 1); thmMainProof applies it under GammaCond with n >= N0 >= 2^40, so this is fine, but the s2 Spec must not require anything thmMainProof cannot supply (e.g. no isolated vertices is available; d_1 >= D_* is available as 2|E|/n >= D_*).
- **MAIN-FINTYPE-D1** (note): HIHyp gives G : FGraph V on V : Type without Fintype and 'Dstar ≤ 2|E|/n'; thmJVps needs Fintype V and 'Dstar ≤ run.d G 1'. Adapter: subtype ↥G.verts + EG.fnum_map, and the s2 API lemma run.d G 1 = 2|E(G)|/n (G_1 = G). Same as JV-FINTYPE-ADAPTER.
- **MAIN-DESIGNATION-EXISTS** (note): A designation must exist as a Lean term: define δ.cls l u := if h : (run.anc G l u).Nonempty then h.choose else default, and prove validity from 'u classed ⇒ anc_l(u) ≠ ∅'. The manuscript's 'fixed rule' is irrelevant (thmJVps holds for every designation).
- **MAIN-CONST-NONNEG** (note): mainInternal_of_hiHyp needs D/2 ≤ C0 D, 0 ≤ eps2 D, eps2 D < 1/2: from GS-NONNEG (under Gamma1core) and Gamma4 (eps2 ≤ 1/4).
- **MAIN-EXPLICIT-OPTIONAL** (note): The locked target only asserts ∃ c. The explicit c_EG (and 1085/1091) is machine-checked only if MainExplicit is also stated; recommended as Tier-2 (blueprint_s1 MAIN-EXISTENTIAL).

**Effort.** ~200 lines, difficulty 2/5. Glue ~200: constants/nonnegativity, Fintype and d_1 adapters, designation existence, index set to Fintype, HI interface (existing).

### `s7:remNonCirc` — remark: Why the argument is not circular (s7.tex:1496)

**Status:** --; (4) rewritten in v6 (R1): one clean-room AI review (G0, 2026-09-26). **Formalization:** No Lean statement. Realized by the structure: eps1/eps2/C0 are Defs functions of D only; c_EG appears only in HI's conclusion (inline max) and in the optional MainExplicit; the round-step consumer reads the past only through (ω, J_l); TPV/PV/VX+ Specs import Fact EG0, not any main-theorem module (module DAG). Checklist items for the statement reviewers + a lint check.

**Statement (precise restatement).** (1) C_0 and theta_Q are fixed functions of D_* (propCost, lemUHsplit), and D_* is fixed before any graph is considered; c_EG enters only as the constant c of thmHI and plays no other role in any construction or bound of s2-s7. (2) Minimality is applied only to the quotients Q_l, which are simple and have at most theta_Q n <= n/4 < n vertices in total; the induction uses about them only f(Q_l) <= c_EG |V(Q_l)|. (3) Q_l depends on the decompositions Dec_{l'} (l' > l) through J_l and through junk; harmless, because each Dec_{l'} is fixed by a deterministic rule, the Markov choice at round l succeeds with probability >= 1/2 whatever the past, and every bound of lemCC, lemUltra and lemPay holds for every past. (4) No other link calls itself: TPV, PV and VX+ finish with the elementary long-cycle bound (Fact s1:factEG0), which is proved directly; all three are unconditional.

**Definitions needed.**

- *constants and conditions: eps = 2^-5, C' = 103, A = 105, N0 (N0Cond), D_* with Gamma1..Gamma4, GammaCond* — s1:defConstants, s1:condGamma [s1:defConstants, s1:condGamma] — EG: no: proposed EG.epsC, EG.N0Cond, EG.Gamma1core/Gamma1/Gamma2a/Gamma3/Gamma4/GammaCond (blueprint_s1); Gamma4 and GammaCond must live after the s7 Defs (they mention eps1, eps2)

**Dependencies.** Declared: `s7:thmHI`, `s7:thmJVps`, `s7:propCost`, `s7:lemUHsplit`, `s7:lemCC`, `s7:lemUltra`, `s7:lemPay`, `s7:lemSimple`, `s7:consRound`, `s4:lemTPV`, `s4:lemPV`, `s4:thmVXp`, `s1:condG4`, `s1:factEG0`.  
From the proof: (none: no proof).  
A remark without proof; its references are pointers. (2) uses Gamma4 (theta_Q <= 1/4) and n >= N0 > 0.

**Used by:** (nothing).

**Randomness.** none (commentary on the randomness schedule: every probability is over fresh variables with the past fixed).

**Lean shape.**

```lean
-- no declaration. Enforcement (for the integrator / statement reviewers):
--  * EG.eps1, EG.eps2, EG.C0 : ℝ → ℝ (functions of D only; no G, run, n, c);
--  * no Spec in EG/Spec/{HB,Link,Lend,Vortex,Light,Chain,Quot} except Quot/HI mentions cEG or a free constant c
--    (lint: grep for cEG / 'max (C / (1 - 2' outside EG/Spec/Quot/HI.lean, EG/Spec/Main*.lean);
--  * S6.JConsumer.out : ℕ → Finset (Sym2 V) → ... (reads (l, J) only, blueprint_s6b JCONS-TYPE);
--  * import graph: EG.Spec.Vortex.* do not import EG.Spec.Main / EG.Proof.Quot.*.
```

**Hazards.**

- **NONCIRC-STRUCTURAL** (note): Nothing to prove; the claims become syntactic properties of the Lean development (quantifier order in HI, Defs of eps1/eps2 as functions of D only, the module DAG). Point (3) is exactly the design decision that the J-consumer is a function of (ω, l, J) (verified for s7:consRound: it reads J_l, stage-1/stage-2 data and xi_l only), with bounds uniform in J (lemUHsplit(ii), lemPay(c): 'for every past').
- **NONCIRC-JUNK** (note): 'Q_l depends on Dec_{l'} through junk': junk junction edges of round l' stay in Erem(Y) of their owner and can change the TPV split, hence E^Q(Z) and J_l of LATER-processed rounds; in Lean this dependence is entirely inside the MIX-C chain and reaches the consumer only via J_l. No extra obligation.

**Effort.** ~0 lines, difficulty 1/5. A lint rule (~20 lines of script, integrator-owned) optional.
