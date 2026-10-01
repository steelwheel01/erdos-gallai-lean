# Where the Lean proof differs from the manuscript

This note lists the places where the Lean 4 formalization in `formal/` takes a different route from the candidate proof in `proofs/manuscript/s1.tex` … `s7.tex` (v6.1). The Lean formalization is a Lean proof of the formal-conjectures statement `Erdos184.erdos_184`. The manuscript is a candidate proof that only AI systems have reviewed; no human has reviewed it.

These are route differences, not errors. The Lean kernel checks the Lean proof against the exact upstream statement. None of the differences below can therefore weaken the formal theorem. They matter for a human reader who compares the two texts: a manuscript lemma may be stated differently in Lean, proved by another argument, split into several statements, or not built at all. Manuscript errata are listed separately in `proofs/manuscript/ERRATA_v6.1.md`.

This note records 36 confirmed deviations, D1–D36, grouped by manuscript section. Each entry gives:

- the manuscript location;
- the manuscript route;
- the Lean route, with file:line and declaration names;
- why Lean differs;
- the effect.

Paths are relative to the repository root. `STATE.md` is the root project log. `TRIAGE.md` is `formal/work/p2/TRIAGE.md`.

---

## A. Statement shape and encodings (cross-cutting)

### D1. Main theorem and HI'': explicit constant not locked; ceiling constant; generalized HI''; bridge to the formal-conjectures statement

- **Manuscript location:** `s1.tex:92-110`; `s7.tex:1403`; `s7.tex:1510`.
- **Manuscript route:** an explicit constant c_EG = max{C_0/(1−2θ_Q), N_0/2}.
- **Lean route:**
  - `MainInternal := ∃ c : ℕ, ∀ V : Type [Fintype] (G : SimpleGraph V), ∃ D, IsDecomp ∧ D.length ≤ c·card V` (`formal/EG/Spec/Main.lean:18-20`).
  - `mainInternal_of_hiHyp` uses `⌈max(C/(1−2ϑ), N0/2)⌉₊` (`formal/EG/Proof/Quot/HIMain.lean:28-57`).
  - `HIStatement` quantifies over all real `Dstar`, `N0`, `C`, `ϑ` (`formal/EG/Spec/Quot/HI.lean:66`). `HIHyp` assumes that G has no isolated vertices (`:54`). `hiHyp_of_gammaCond` (`formal/EG/Proof/Main.lean:57-65`) never needs that assumption: `JVpsStatement` has no such hypothesis on G, and its no-isolated-vertex conclusion for Q_l is discarded.
  - The bridge is `of_mainInternal` and `solution` (`formal/EGCheck/Bridge.lean:27`, `:31`). It goes through `Fintype.equivFin` (`formal/EGCheck/BridgeCore.lean:18-24`).
- **Why:** the target is the formal-conjectures O(n) statement, and the locked surface stays small.
- **Effect:** the Lean end result is the O(n) statement; the explicit c_EG stays internal to the proof.
- **Evidence:** also `formal/EG/Proof/Quot/HIMain.lean:25-57`, `formal/EG/Proof/Quot/HI.lean:198`, `formal/CONVENTIONS.md:14-15`, `formal/work/p3/MAIN.md:10-40`.

### D2. Finite probability spaces encoded as `FinDist` (finitely supported real weights, no `[Fintype Ω]`)

- **Manuscript location:** `s1.tex:49` ff. and `:254-274` (R5); `s4.tex:173-176` (truncated level law P(lev ≥ j) = 2^−j for 0 ≤ j ≤ J), `s4.tex:655`.
- **Manuscript route:** arbitrary finite probability spaces, with truncated geometric levels in s4 (a v6 change, R5).
- **Lean route:**
  - `structure FinDist (Ω : Type*)` (`formal/EG/Defs/Prob/FinDist.lean:62`) has a weight function `w`, `w_nonneg`, and a finite set outside which `w = 0` and on which the weights sum to 1.
  - `prob` and `expect` sum over the canonical support (`:104`, `:108`). There is no `Fintype` parameter.
  - `ofFinset` (`:114`) and `ofFintype` (`:119`) build laws. `sum_w`, `expect_eq_sum` and `prob_eq_sum` are at `formal/EG/Lib/Prob/Basic.lean:94`, `:135`, `:234`.
  - This departs from PLAN §3 (instance robustness), not from the manuscript.
- **Why:** engineering; it avoids `Fintype`/`DecidableEq` instance diamonds (`formal/work/p1b/findist.md:48-61`).
- **Effect:** none on stated results. The truncated level law matches the v6.1 text (`s4.tex:173-174`).
- **Documentation issue:** `formal/CONVENTIONS.md:77` says "(proved: `no_geometric`)", but no declaration `no_geometric` exists in any `formal/**/*.lean` file. The name appears only in review prose (`formal/APPROVALS/reviews/findist.opus.md:254`, `findist.fable.md:285`) and in `formal/work/p2/blueprint_s4.md:95`. The fact itself is trivial: a finite support rules out P(lev ≥ j) = 2^−j for all j.
- **Evidence:** `formal/EG/Defs/Prob/FinDist.lean:55-68`; `formal/work/p1b/findist.md:19-27`; `formal/CONVENTIONS.md:75-78`; `STATE.md:321`; TRIAGE §2.5, §2.7.

### D3. Universe bridging: s7a round Specs on `V : Type`, s7b consumers on `V : Type u`, via `*_univ` re-proofs

- **Manuscript location:** `s7.tex:231-1195` (the s7a round lemmas), consumed by `s7:lemPay`, `s7:lemUHsplit` and `s7:propCost`.
- **Manuscript route:** no universe issue arises.
- **Lean route:**
  - The s7a Specs quantify `V : Type`, e.g. `formal/EG/Spec/Quot/CC.lean:117`, `MULT.lean:60`, `Lift.lean:121`, `Ultra.lean:82`, `WellDef.lean:63`, `RoundStep.lean:80`, `Cand.lean:77`. The s7b Specs quantify `V : Type u` (`Cost.lean:59`, `Pay.lean:79`, `UHsplit.lean:60`).
  - Universe-polymorphic copies exist: `formal/EG/Lib/Quot/MultUniv.lean:25`, `:91` and `LiftUniv.lean:26`, `:108`.
  - Each locked theorem is re-exported as `X := X_univ.{0}` in `formal/EG/Proof/Todo/`: CCPartner:244, CCMax:132, CCCopies:295, UltraIndep:118, UltraMax:75, UltraCopies:173, UltraSum:119, and CandCount:198 (with `candCount_univ` at :42).
  - `MainInternal` is stated at `V : Type` (`formal/EG/Spec/Main.lean:18-20`). The bridge to `erdos_184.{u}` goes through `Fintype.equivFin` (`formal/EGCheck/BridgeCore.lean:18-24`).
- **Why:** this avoids editing locked Specs; the lock has 0 violations.
- **Effect:** none. The statements are identical and the locked constants are unchanged.
- **Evidence:** `formal/work/p3/s7.md:46-57`, `:79-84`, `:102-104`; `formal/work/p2s/s3a.md:218` (T0-UNIV); `STATE.md:527`. The Specs PoolLaw and CandSubset named in `s7.md:80` live in `formal/EG/Spec/Stage1/Pool.lean` and `formal/EG/Spec/Quot/CandDef.lean`.

### D4. Declared-input statement splits, including `COLaProbStatement` (the failure bound of COL(a) exported separately)

- **Manuscript location:** `s3.tex:1453-1470` (`s3:lemCOL`); proof of (a) at `s3.tex:1545-1548` ("≤ N^−2/4"); used at `s3.tex:1583-1600` and `s5.tex:128-130` (`s5:lemE1`(b)).
- **Manuscript route:** P(COL(a) fails) ≤ N^−2/4 is proved inside (a) (`s3.tex:1548`) but not stated.
- **Lean route:**
  - `COLaProbStatement` (`formal/EG/Spec/Stage1/COLa.lean`) is proved by `EG.colaProb` (`formal/EG/Proof/Stage1/COLa.lean:26`), which is `COLaProof.colaProb` (`formal/EG/Lib/Stage1/COLa.lean:467`).
  - That proof uses L15+ (three stage applications), StructureExp, and COL-JV rows 3 and 9. It conditions on the edge-bit vector `edgeBits` (`formal/EG/Lib/Stage1/COLa.lean:31`, `:95-97`).
  - The other split Specs are proved: CapPrePart, TowerBLate, TowerBM, Structure*, EL, Tower*, OVRunK, T16s, Cor22, EulerMulti, EulerTreeTJoin and COLJVCount (e.g. `formal/EG/Proof/HB/CapPrePart.lean:25`, `TowerBLate.lean:27`, `Structure.lean:27`).
  - A grep finds 15 Spec files with "DECLARED INPUT" (22 case-insensitive) and none in `EG/Proof`.
- **Why:** consumers need a clause that the manuscript states only jointly with others or only inside a proof. The split also let probes run in parallel.
- **Effect:** none on truth. The approval record logs the unexported COL(a) bound as a T1 wording gap, and v6.1 does not state it in the lemma (`proofs/manuscript/v61/PATCHES.md` has no COL(a) entry). The errata file treats it as T0, "checked and not errata": inside the manuscript the proof of (c) cites a bound that the proof of (a) establishes.
- **Precision:** StructureHY, Structure and StructureLight carry lowercase "declared input" wording. eqLY, stagesHB, lemZones and pvLemma are not marked "DECLARED INPUT" in their Spec files; they were declared inputs of probe notes (e.g. `formal/work/p2b/P4B.md`).
- **Evidence:** `formal/EG/Spec/Stage1/COLa.lean:1-45`; `formal/APPROVALS/2026-09-30-P2-specs.md:18-22`; `STATE.md:494-500`.

### D5. Stage-1 randomness encoding: support restrictions and total definitions with guards

- **Manuscript location:** `s3.tex:1041-1184`; `s5.tex:28-45`; `s7.tex:30-53`; `s7.tex:1196`.
- **Manuscript route:** laws are defined where meaningful, statements speak of "any" outcome, and COL(g) holds always.
- **Lean route:**
  - There is one `Outcome` record and one law.
  - The zone law has a `dite` guard that is exactly Σ zp ≤ 1, and the pool law has the guard `poolMass ≤ 1`. Each falls back to `dirac none`.
  - `idx` is `dirac none` if `lentIdx` is empty. k_own ≥ 1 holds with no guard.
  - Statements quantify over ω ∈ supp. COL(g) is stated on the support (`COLg_of_mem_supp_colLaw`, `formal/EG/Lib/Stage1/COL.lean:426`; `COLg_of_map_eq`, `:436`).
  - `candMean` is a closed form.
- **Why:** Lean needs total definitions, and records off the support violate `Coherent`.
- **Effect:** none; the guards are inactive under `RunHyp`.
- **Evidence:** `formal/work/p2/TRIAGE.md:184-199`, `:87`; `formal/work/p2d/stage1.md:168`, `:206`; `formal/work/p2s/s6b.md:126`.

### D6. Superseded T0 records (def11-eps, eg0-loop, cap-1): now in the manuscript text

- **Manuscript location:**
  - `s1.tex:817-822`: the Def 11 remark, "n ≥ 2 and ε > 0".
  - `s1.tex:641-642`: Fact EG0(b), "edge set of a (simple) graph".
  - `s1.tex:1036-1042`: m ≥ max(2, 2^30/ε²).
- **Manuscript route:** the v5 text omitted ε > 0, looplessness and m ≥ 2. These were forwarded as T0 manuscript findings (`formal/APPROVALS/2026-09-26-P1-foundations.md:28-29`, "forwarded to v6") and integrated in v6 (commit `d6f3c49`). v6 and v6.1 both contain them.
- **Lean route:**
  - `ExpanderMinDeg` carries 0 < ε (`formal/EG/Proof/Todo/ExpanderMinDeg.lean:18`). `formal/EG/Proof/Todo/ExpanderEpsZero.lean:18` shows that with ε ≤ 0 every graph is an expander.
  - `factEG0b` is stated for loopless edge sets (`formal/work/ext/eg0.md:32`).
  - `BMLemma25Statement` has 2 ≤ m. The literal form is refuted by `bmLemma25_literal_false` (`formal/EG/Proof/Ext/BMLemma25.lean:216`).
- **Why:** each is a genuine requirement in a degenerate case.
- **Effect:** none. There is no current divergence from v6.1.
- **Evidence:** `formal/CONVENTIONS.md:96-98`; `formal/work/p3/s1.md:9`.

---

## B. Section 1: cited results and foundations

### D7. Lovász 1968 (`s1:citThm21`) proved in Lean, via Lovász's construction as given in Yan's 1998 thesis

- **Manuscript location:** `s1.tex:1015-1019` (`s1:citThm21`, `\deps{none (published)}`); `s1.tex:1500-1501` ("used only through Cited result s1:citCor22"); table row `s1.tex:1074`; Cor 22 at `s1.tex:1021-1033`.
- **Manuscript route:** cited from [BM, Theorem 21] / [Lov68] without proof and used only through Corollary 22.
- **Lean route:**
  - Lemma LC is `EG.LovaszC.lovasz_construction` (`formal/EG/Lib/Ext/LovaszCons.lean:673`), built on the `nxt` map and the `Reach` set (`:19`, `:60`).
  - The main theorem is proved by strong induction on \|E(H)\|; Yan inducts on 2m − n (`formal/work/p3/lovasz.md:8`).
  - `case0` (`formal/EG/Lib/Ext/LovaszThm.lean:394`): there is a vertex of even positive degree. Take a neighbour x of it and let Z be the set of even-degree neighbours of x; then conclude by parity and LC.
  - `case1` (`:529`): every degree is odd or 0. Either H is a matching, or the proof moves the x-end of an edge xy to a pendant vertex `none` on `Option V`, applies Case 0, drops the leaf, and restores xy.
  - The theorem is assembled in `concl_of_card` (`:676`) and `lovasz` (`:694`).
  - Python checks on about 10^4 random graphs and on K_1…K_11 are recorded in `formal/work/p3/lovasz.md:9-11`.
  - An alternative route, the measure μ(E) = 2\|E\| + [all degrees odd] (`formal/work/p3/s1.md:66`), is archived in `formal/work/p3/lovasz_alt/` and not built.
- **Why:** this was the last unproved stage-α hypothesis. Proving it removes Lovász from the trusted inputs.
- **Effect:** the stated result, 2(\|P\| + \|C\|) ≤ n with n counting isolated vertices, is unchanged. The Lean Spec is `2*(P.length + C.length) ≤ H.card` in ℕ. The citation is replaced by a kernel-checked proof, and no manuscript statement is affected.
- **Evidence:** `formal/EG/Lib/Ext/LovaszThm.lean:5-21`; `formal/EG/Proof/Todo/Lovasz.lean` (`Lovasz := EG.LovaszC.lovasz`); `formal/EG/Spec/Ext/Lovasz.lean:29-30` (`Type u`, LOV-UNIV), `:44-48`; `formal/EG/Lib/Ext/Cor22.lean:516` (`cor22_of_lovasz`); `formal/EG/Proof/Ext/Cor22.lean:22`; `formal/work/p3/lovasz.md:5-47`; `formal/work/p3/lovasz_alt/README.md:1`; `STATE.md:534-536`.

### D8. Haxell: both the stated (2q−1)(\|X′\|−1) form and the q²-form proved; termination by a maximal key

- **Manuscript location:** `s1.tex:1301-1330` (`s1:citHaxell`; the q² remark is at `:1323-1327`); termination at `s1.tex:1472-1487`; consumer `s3.tex:692` (`s3:lemL9rho`), which uses the q² form at `s3.tex:768-776`.
- **Manuscript route:** cites [Hax95] and writes out an alternating-tree proof of the stated form. Termination iterates moves that decrease the signature in ≺ (σ∞ <lex τ∞). L9ρ verifies \|Z\| < h²\|I\|.
- **Lean route:**
  - `EG.haxell_stated` (`formal/EG/Proof/Ext/Haxell.lean:624`) proves the stated form, with the bound compared in ℤ.
  - The locked `EG.haxell` (`:661`) is the q²-form. It is derived through `haxellStatement_of_statedForm` (`:640`), using (2q−1)(\|X′\|−1) < q²\|X′\|.
  - Termination: `augment` (`:505`) takes a good M and a configuration whose key is lexicographically maximal (entries \|H\| − s in `Fin(|H|+1)`) and derives a contradiction. This is the manuscript's order reversed.
- **Why:** the q²-form was locked (HAX-TRUTH / L9-HAXELL-FORM) so that no statement depends on the unchecked factor 2q−1. The maximal key avoids formalizing an iterated procedure.
- **Effect:** none. Both forms are proved, Haxell is no longer a stage-α hypothesis, and correctness no longer needs the [Hax95] citation. L9ρ's check in the TeX (`s3.tex:770-776`) is exactly the q² hypothesis.
- **Evidence:** `formal/EG/Proof/Ext/Haxell.lean:10-33`; `formal/EG/Spec/Ext/Haxell.lean:20-32`; `formal/work/ext/haxell.md:38-52`; TRIAGE §1c HAX-TRUTH, §2.5; `STATE.md:419-421`.

### D9. B–M Lemma 25 (explicit, constant 18): DFS with restarts, reachable set X*, explicit integer rounding, extra hypothesis 2 ≤ m

- **Manuscript location:** `s1.tex:1035-1057` (`s1:citLem25`; 2 ≤ m is already at `:1036-1042`; the sketch is at `:1044-1054`).
- **Manuscript route:** the sketch of [BM]:
  - run a DFS on G, which uses connectivity, until \|U\| = \|R\|;
  - split the path P into X, Y, Z with \|X\|, \|Z\| ≥ \|P\|/3 and ε²m/(18 log⁴ m) ≤ \|Y\| < ε²m/(9 log⁴ m), with integer existence left implicit;
  - take a shortest X–Z path avoiding Y.
- **Lean route:**
  - The DFS is an invariant relation with restarts, so connectivity is not needed (`formal/work/ext/lemma25.md:18-24`).
  - Explicit integer rounding: k = ⌈a⌉ and x = ⌊(p − k)/2⌋. The bound a ≥ 4/3 follows from 24L⁴ ≤ ε²n via `bm25_numeric` (`formal/EG/Proof/Ext/BMLemma25.lean:75`; case split at 2^40 plus monotonicity of y/log⁴ y).
  - The reachable set X* replaces the shortest path (`lemma25.md:42`). The side of size ≤ n/2 is X* or V \ (X* ∪ Y).
  - \|X\| = ⌊(\|P\| − \|Y\|)/2⌋ ≤ \|Z\| replaces \|X\|, \|Z\| ≥ \|P\|/3.
  - `bm25_eps_le` (`:42`) proves ε ≤ log² m.
  - The Spec has 2 ≤ m (T0-cap-1). `bmLemma25_literal_false` (`:216`) refutes the literal form with the one-vertex graph and ε = 2^15; a one-vertex graph has no cycle at all.
- **Why:** [BM] leaves integer sizes and connectivity implicit, and the DFS is simpler without connectivity. m = 1 is a genuine degenerate counterexample.
- **Effect:** the constant 18 is achieved exactly, and the proof gives cycle length ≥ ⌈a⌉ + 2. The margin in `s2:lemCap`(i), 18432·1.37317⁴ ≈ 65534 ≤ 65536 (`formal/work/p2/TRIAGE.md:96`), is thin. It depends on the constant 18, which is achieved exactly; the extra +2 in cycle length does not change it. The v6.1 text already has 2 ≤ m (`s1.tex:1036`), so the statements do not diverge.
- **Documentation issue:** the docstring at `formal/EG/Spec/Ext/BMLemma25.lean:9-10` still says the proof is "at present with sorry". It is proved (`bmLemma25`, `formal/EG/Proof/Ext/BMLemma25.lean:107`), as `formal/work/ext/lemma25.md:77` notes.
- **Evidence:** `formal/EG/Proof/Ext/BMLemma25.lean:8-17`, `:210-235`; `formal/work/ext/lemma25.md:40-44`, `:55-77`; `formal/work/p1b/cap.md:76-93`; `formal/APPROVALS/2026-09-26-P1-stageB-specs.md:4-6`, `:22-23`; `formal/CONVENTIONS.md:98`; `formal/work/p2/blueprint_s2a.md:50`.

### D10. Euler and T-joins: direct T-join constructions instead of spanning trees; multigraph Euler by maximal trails

- **Manuscript location:** `s1.tex:1489-1501` (`s1:citEuler`); `s6.tex:105-139` (`s6:lemPAR`); `s5.tex:252` (`s5:lemParent` Step 3).
- **Manuscript route:** T-joins from spanning trees; the Euler theorem is cited.
- **Lean route:**
  - `exists_tJoin` (`formal/EG/Lib/Chain/ParTJoin.lean:93`) builds a T-join inside any edge set whose components each contain an even number of T-vertices. It proceeds by induction on \|T\|, as a symmetric difference of paths.
  - `eulerTreeTJoin` (`formal/EG/Proof/Found/EulerTreeTJoin.lean:25`) follows by applying `exists_tJoin` to the tree S. It uses the connectivity of S (`hSconn`), but not the acyclicity of S or the connectivity of H.
  - `exists_even_complement` (`formal/EG/Lib/Light/Euler.lean:137`) is the pigeonhole argument over the 2^\|T\| subsets.
  - `exists_eulerian` (`formal/EG/Lib/Found/EulerMulti.lean:203`) is the maximal-trail proof on index-set multigraphs.
- **Why:** this avoids formalizing spanning trees and forests on multigraphs.
- **Effect:** none; the statements are the same, and Euler is no longer a stage-α hypothesis. `formal/work/p2b/P4B.md:407` notes that `lemParent` no longer uses `eulerTreeTJoin`.
- **Evidence:** `formal/EG/Lib/Chain/ParTJoin.lean:17-19`; `formal/EG/Proof/Found/EulerTreeTJoin.lean:1-25`; `formal/EG/Lib/Found/EulerMulti.lean:15`; `formal/EG/Proof/Found/EulerMulti.lean:20`; `formal/work/p2b/P4B.md:405-418`; `formal/work/p2b/P2E.audit.md:287` (F4).

### D11. Chernoff bounds proved by the exponential-moment method (the manuscript cites JLR/BM)

- **Manuscript location:** `s1.tex:740` (`citChernoff`); `s1.tex:1103-1137` (`citChernoffGen`; the lower tail is stated for 0 ≤ δ ≤ 1).
- **Manuscript route:** cites JLR 2.1/2.8 and reduces them to the stated forms.
- **Lean route:**
  - The exponential moment is taken with t = log(1+δ) for the upper tail and t = −δ for the lower tail.
  - `IndepEvents` (`formal/EG/Lib/Prob/Chernoff.lean:229`) is mutual independence of events.
  - The lower tails hold for all δ ≥ 0, and (b) holds for every j, including 0. The JLR forms are not formalized.
- **Why:** a self-contained proof with minimal hypotheses.
- **Effect:** the stated results are unchanged or stronger.
- **Evidence:** `formal/EG/Lib/Prob/Chernoff.lean` (1041 lines); `formal/work/p1b/chernoff.md:1-25`, `:122-135`.

### D12. Hall, B–M Prop 8, B–M Prop 12: cited results proved in Lean, with small statement adjustments

- **Manuscript location:** `s1.tex:1290-1299` (Hall); `s1.tex:769-777` (Prop 8); `s1.tex:826-842` (Prop 12).
- **Manuscript route:** cited without proof.
- **Lean route:**
  - Hall: `Finset.all_card_le_biUnion_card_iff_exists_injective` on `↥J` (`formal/EG/Proof/Todo/Hall.lean:17-21`). The system of distinct representatives lives on `↥J` (T0-s1-hall-dom).
  - Prop 8: `bmProp8` (`formal/EG/Lib/Ext/BMProp8.lean:299`) uses `ThroughW` walks, bypasses, ball composition and \|X\|·3^r ≤ t·2^r, with a contradiction at r = 2t. The hypotheses 1 ≤ ℓ, ℓ ≤ n and t ≤ n are unused.
  - Prop 12: `IsExpander.bmProp12` (`formal/EG/Lib/Ext/BMProp12.lean:25`). The hypothesis d ≤ s is unused, and F ⊆ E(G) is added (T0-s1-p12).
- **Why:** removes the citations. The integer form avoids real-valued maximality arguments.
- **Effect:** none; the statements are equivalent or stronger.
- **Evidence:** `formal/EG/Proof/Todo/Hall.lean:16-21`; `formal/work/p3/s1.md:12-14`; `formal/work/p2s/s1.md:236`, `:241-242`.

### D13. Fact EG0 and Lemma BBD: minor changes of proof technique

- **Manuscript location:** `s1.tex:635-710` (`s1:factEG0`); `s1.tex:1161-1289` (`s1:lemBBD`).
- **Manuscript route:** the proofs as written.
- **Lean route:**
  - EG0:
    - d = max(2, ⌊m′/h⌋);
    - (1 − 1/h)^h ≤ e^−1 ≤ 1/2 (`Real.one_sub_div_pow_le_exp_neg`);
    - \|E\| < C(h+1, 2) ≤ 2^⌊log h⌋·h, via E ⊊ W.sym2;
    - q = ⌊log_2 h⌋, with induction on q (`decomp_of_card_lt`);
    - the Claim is applied to edge sets.
  - BBD: `mgf_fin` reveals the first coordinate via `Fin.consEquiv` and is transported along `Fintype.equivFin`.
- **Why:** avoids ceilings in ℕ and reuses Mathlib.
- **Effect:** none; the count qh + h − 1 ≤ h log h + h and the BBD tails are the same.
- **Evidence:** `formal/work/ext/eg0.md:63-92`; `formal/work/ext/bbd.md:30-42`. The declaration names are cited from these notes.

### D14. Galactic conditions: Γ1(d) from (a) alone; satisfiability (`lemGammaSat`) by asymptotic routes; stronger eventuality

- **Manuscript location:** `s1.tex:1609-1610` (`condG1`(d)); `s7.tex:1447` (`s7:lemGammaSat`); `s3.tex:1357` (`s3:lemCOLJVev`).
- **Manuscript route:** (d) is said to follow from (a) and (b); explicit bounds; a type-(E) route for column 3.
- **Lean route:**
  - `Gamma1dOfAB` (`formal/EG/Proof/Todo/Gamma1dOfAB.lean:19`) uses only `Gamma1a`, via Bernoulli at log_2 μ − 5.
  - `eventually_size` (`formal/EG/Lib/Vortex/Size.lean:185`) gives η → 0 asymptotically.
  - `col3_of_le` (`formal/EG/Lib/Gamma/Col3.lean:94`) is a direct power-of-two comparison for μ ≥ 2^40; `eventually_col3` is at `:199`.
  - log* ≤ 2 + log log is used for ε_CONC (`formal/work/p2b/GAMMA.audit.md:133-135`).
  - `GammaSatStatement := ∀ N0 : ℝ, ∀ᶠ D in atTop, GammaCond N0 D` (`formal/EG/Spec/Gamma/Sat.lean`, about `:70`). This is stronger than the TeX (H2) (`formal/work/p2b/GAMMA.md:164`). The existence form `GammaCondExistsStatement` is `∃ N0 D, N0Cond N0 ∧ GammaCond N0 D` (`formal/EG/Spec/Gamma/Sat.lean:80-81`).
- **Why:** the shortest route in Lean.
- **Effect:** none on truth; the Γ-conditions are unchanged. The (d) attribution is listed as an open erratum (T1) in `proofs/manuscript/ERRATA_v6.1.md`.
- **Evidence:** `formal/EG/Proof/Todo/Gamma1dOfAB.lean:18-26`; `formal/EG/Proof/Gamma/Sat.lean:89-106`; `formal/EG/Spec/Gamma/Sat.lean:66-81`; `formal/work/p2b/GAMMA.md:160-168`, `:236-238`; `formal/work/p2b/GAMMA.audit.md:133-137`; `formal/APPROVALS/2026-09-30-P2-specs.md:21`.

---

## C. Section 2: the high-degree recursion

### D15. M_l as a natural-number ceiling (and s_l, P_l, τ_l as ℕ ceilings)

- **Manuscript location:** `s2.tex:517-528` ((R2), v6.1); `proofs/manuscript/v61/PATCHES.md:17-33` (M-INTEGER, T1).
- **Manuscript route:** in v6.1, M_l := ⌈max(2^40, 2^16 T_l log⁴ T_l)⌉ ∈ ℕ, s_l = ⌈Λ_l^σ⌉, P_l = ⌈λ_l^C′⌉, τ_l = ⌈128 s_l log² M_l⌉. In v6, M_l was real; that was a T1 item, now patched.
- **Lean route:**
  - `EG.HB.MOf d : ℕ := ⌈max (2^40) (2^16 * TOf d * logb 2 (TOf d)^4)⌉₊` (`formal/EG/Defs/HB/Round.lean:57`). Its logarithm is `LamOf` (`:60`), which TRIAGE calls ΛOf.
  - `sOf`, `POf`, `tauOf` and `thetaGC` are ℕ ceilings (`:64`, `:70`, `:73`, `:77`).
  - `KJS = M^2` and `tJS = 2M+2` (`formal/EG/Defs/Stage1/COL.lean:91`, `:97`); `KHUB = 4M` (`formal/EG/Defs/Quot/Round.lean:134`); the palette is `Fin (4*M)` (`formal/EG/Defs/Quot/Schedule.lean:28`, `:56`).
- **Why:** M_l counts classes and colours, and the JS label law with ρ_l = M_l^−4 is exact only for integer M_l.
- **Effect:** no divergence from v6.1. Compared with v6, v6.1 adapts the wording of `propDegRec`, (B6) and `lemCap`(ii) (PATCHES rows 1b–1d).
- **Evidence:** `formal/EG/Defs/HB/Round.lean:53-77`; `formal/work/p2/TRIAGE.md:106-117`; `STATE.md:398-399`; `formal/APPROVALS/2026-09-26-P2D-batch1-and-ext.md:6`.

### D16. (R1) encoded as any maximal family; (R5)(3) order fixed to the home order

- **Manuscript location:** `s2.tex:511-516` ((R1), lexicographically first); `s2.tex:568` ff. ((R5)).
- **Manuscript route:** a deterministic lexicographic greedy choice; (R5)(3) does not name its order.
- **Lean route:**
  - `CyclesValid` (`formal/EG/Defs/HB/Round.lean:125-134`) accepts any list of well-formed, pairwise edge-disjoint cycles of length ≥ T_l in E(G_l) such that G′_l has no cycle of length ≥ T_l. This enlarges the set of valid runs. The maximality condition is exactly the TeX's stopping condition.
  - (R5)(3) uses the home order of (R4) (`Round.lean:89`, `:97`, `:197`).
- **Why:** avoids formalizing a lexicographic enumeration.
- **Effect:** statements quantified over all runs become stronger, and existence is proved for the larger class. No effect on the main theorem. The unnamed (R5)(3) order is listed as an open T0 erratum.
- **Evidence:** `formal/EG/Defs/HB/Round.lean:83-89`, `:305-312`; TRIAGE §1b HB-R5-ORDER, §2.2, §2.12.

### D17. Γ1/Γ2(a) guard and T0-exists-gamma: termination needs Γ1; propExists carries `Gamma1core`; Γ2(a), (b), (c) derived

- **Manuscript location:** `s2.tex:1001-1008` (`s2:propExists`, no hypothesis on D_*); `s1.tex:1602-1612` (`condG1`); `s1.tex:1644-1660` (`condG2`; `:1656-1657` says each of (a)–(c) is implied by Γ1); the standing assumptions at `s5.tex:9` and `s7.tex:10`. v6.1 also adds a standing assumption at `s2.tex:24-29`.
- **Manuscript route:** propExists has no hypothesis on D_*. D_* is by definition the constant of `s1:defConstants`(iii), which satisfies Γ1–Γ4. `condG2` lists (a)–(c) and says that each follows from Γ1.
- **Lean route:**
  - `RoundTauTermStatement` (`formal/EG/Spec/HB/Exists.lean:108`) and `RoundExistsStatement` (`:148`) carry `Gamma2a`.
  - `RunTerminatesStatement` (`:156`) and `ExistsRunStatement` (`:166`) carry `Gamma1core`.
  - `Gamma1core.gamma2a` (`formal/EG/Lib/Found/Gamma.lean:97`) derives Γ2(a).
  - `GammaCond := Gamma1 ∧ Gamma2a ∧ Gamma3 ∧ Gamma4` (`formal/EG/Defs/Main/GammaCond.lean:34`), and Γ2(b), (c) are lemmas.
  - `GammaCond`, the standing hypothesis of the main theorem, contains `Gamma2a` as a redundant conjunct. The assembly does not use that conjunct; it derives Γ2(a) from Γ1 as `hΓ.gamma1core.gamma2a` (`formal/EG/Proof/Main.lean:76`; `formal/work/p3/MAIN.md:12-15`).
- **Why:** read without the definition of D_*, the TeX statement is false: D_* = 2^117 and G = K_{2^117+1} is a counterexample. But D_* is by definition a Γ-constant.
- **Effect:** none on the main theorem.
- **Evidence:** `formal/EG/Spec/HB/Exists.lean:60-66`; `formal/EG/Lib/Found/Gamma.lean:15-20`, `:95-99`; `formal/EG/Defs/Main/GammaCond.lean:20-34`; `formal/work/p2s/s2b.md:297-305`; `formal/work/p2s/s2a.review-vacuity-and-consumer-form.md:82`, `:146` (I2), `:157`; `formal/work/p2/TRIAGE.md:71` (EX-GAMMA-NEEDED); `STATE.md:500-502`; `formal/APPROVALS/2026-09-30-P2-specs.md` watch item (3).

### D18. Unused hypotheses dropped from s2/s6a statements; implicit standing assumptions added where used

- **Manuscript location:** `s2.tex:723` (`propStructure`: "n ≥ N_0 and d_1 ≥ D_*"); `s2.tex:1320` (`propOrigin`); `s6.tex:297`, `:335`; `s2.tex:1414`; `s2.tex:1035`.
- **Manuscript route:** n ≥ N_0, d_1 ≥ D_* and Γ as standing hypotheses.
- **Lean route:**
  - The `propStructure` Specs drop both n ≥ N_0 and d_1 ≥ D_*; (iii) carries 0 < G.card instead (`formal/EG/Spec/HB/Structure.lean:49-52`).
  - `StructureHYStatement` takes only `run.Valid` (`formal/EG/Spec/HB/StructureHY.lean:29-33`, `:50-52`).
  - The Origin Specs carry no Γ (`formal/EG/Spec/HB/Origin.lean:89`, `:110`, `:122`).
  - `AdmissibleParent` keeps `Gamma1core` (`formal/EG/Spec/HB/Parentless.lean:96-98`), while Fresh and ParentlessCount drop it.
  - The Lacunary sequence form is abstract.
  - `Gamma1core` is added where Γ is used (T0-CONCL-ALPHA, `formal/work/p2b/P3B.md:325`).
- **Why:** each Spec takes exactly the Γ items its proof uses.
- **Effect:** mostly strengthenings. The added `Gamma1core` hypotheses match the manuscript's standing assumption. No effect on the main theorem.
- **Evidence:** `formal/EG/Spec/HB/Structure.lean:45-52`; `formal/EG/Spec/HB/Parentless.lean:35`; `formal/work/p2b/P3B.md:323-327`; `formal/work/p2s/s2b.md:313-326`; TRIAGE §1b STR-N0.

### D19. propStructure(iii): long-cycle count by telescoping instead of dyadic grouping

- **Manuscript location:** `s2.tex:722-735` (`s2:propStructure`(iii)); the proof paragraph "Long cycles" at `s2.tex:802-815`.
- **Manuscript route:** \|Cyc_l\| ≤ (n/2)(y_l − y_{l+1})/(y_l log² y_l). Rounds are grouped by k = ⌊log y_l⌋. A group contributes at most n/k², and the sum over k ≥ k_0 is at most n/(k_0 − 1) ≤ n.
- **Lean route:**
  - `cyc_step` (`formal/EG/Lib/HB/Partition.lean:64`) proves (y − y′)/(y log² y) ≤ 1/log y′ − 1/log y for 2 ≤ y′ ≤ y. It uses 1 − t ≤ −ln t (`Real.log_le_sub_one_of_pos`) and log_2 y′ ≥ 1; ln 2 < 1 enters through the conversion between log_2 and ln.
  - `cycles_sum_le` (`:104`, proof to `:160`) telescopes over l = 1..R−1. The last round is bounded separately: y_{R+1} may be below D_*, so it uses only y_{R+1} ≥ 0 and 1/log_2 y_R ≤ 1/117, giving b_R ≤ n/(2·117).
  - The total is at most n/117 ≤ n, under the hypothesis y_l ≥ 2^117.
- **Why:** avoids the floor-indexed dyadic bookkeeping; a one-line real-analytic step is easier in Lean.
- **Effect:** none; the bound Σ_{l≤R} \|Cyc_l\| ≤ n is the same. Internally Lean gets n/117.
- **Evidence:** `formal/EG/Lib/HB/Partition.lean:62-64`, `:101-111`; `formal/work/p3/s2.md:29-32`; `STATE.md:520`.

### D20. Lemma OV(a) by a per-vertex potential induction instead of the charging/chain argument

- **Manuscript location:** `s2.tex:278-375` (`s2:lemOVgeneric`).
- **Manuscript route:** charge to pairs (ν,u), distribute the charge to leaf copies, and bound chain sums.
- **Lean route:**
  - The potential is Φ(x) = [x ≥ M](C − 1/(c_OV log x)), with w(x) = 1/log² x and ε factored out.
  - A per-vertex induction on the split tree (`STree.ov_vertex`, `formal/EG/Lib/HB/OVPotential.lean:261`) is summed over vertices (`STree.ov_charge`, `:330`).
  - c_OV ≥ 17/41 follows from 2^65 ≥ 3^41. `ovC_le_sharp` (`:182`) gives ovC ≤ (58/17)/log_2 M.
- **Why:** tree induction is natural in Lean.
- **Effect:** none; the statement is the same. `ovC_le_sharp` is used in `formal/EG/Proof/HB/Lemma14Tau.lean:128` and `formal/EG/Proof/Todo/OVRound.lean:74`, which covers the 5.46-versus-3.42 point listed as open erratum OV-CONST-546.
- **Evidence:** `formal/EG/Lib/HB/OVPotential.lean:1-22`; `formal/EG/Proof/HB/Overlap.lean:24`; `formal/work/p2b/P3A.md:524-527`; `formal/work/p2b/P3A.audit.md:148-150`.

### D21. Other s2 proof-route changes: GC(iii) via (R5)(3); CONC-L(i) via ORIGIN(a) rather than Lemma EL; thin cut from τ-labels; a sharper Lemma 14^τ; leaf non-emptiness in propDegRec made explicit

- **Manuscript location:** `s2.tex:1282`; `s6.tex:335`; `s2.tex:220`; `s2.tex:376`; `s2.tex:922`.
- **Manuscript route:** the proofs as written in the TeX.
- **Lean route:**
  - GC(iii): `Round.assign_ne_none_of_not_isLight` (`formal/EG/Lib/HB/GC.lean:54`) and `assign_ne_none_of_mem_partVerts` (`:68`).
  - CONC-L(i) is derived from ORIGIN(a) (T0-CONCL-EL, `formal/work/p2b/P3B.md:331-333`).
  - `thinCut` (`formal/EG/Proof/HB/ThinCut.lean:44`) is derived from `STree.TauLabels`.
  - Lemma 14^τ: \|U′ ∪ N″\| ≤ (1 + 1.25/32)(2/3)m ≈ 0.693m (`formal/work/p2b/P3A.md:528-531`).
  - DegRec: `STree.verts_nonempty`, `split_nonempty_of_isS0Rec` and `split_nonempty_of_isTauRun` (`formal/EG/Lib/HB/DegRecAux.lean:29`, `:60`, `:75`).
- **Why:** shorter dependency paths, and an implicit fact made explicit.
- **Effect:** none; the statements are unchanged or stronger. The implicit non-emptiness is listed as open erratum DR-LEAF-NONEMPTY (T0).
- **Evidence:** `formal/EG/Proof/HB/Lemma14Tau.lean:85`, `:112`; `formal/EG/Proof/HB/GC.lean:30`; `formal/work/p2b/P3A.audit.md:148-153`; `formal/work/p2b/P3A.md:521-533`; `formal/work/p2b/P3B.md:331-338`; `formal/work/p3/s2.md:33-36`.

---

## D. Section 3: splitting, colouring and lending

### D22. Lemma 15+ (random splitting), Step 4: exact binomial sum instead of the N^u count of sets U

- **Manuscript location:** `s3.tex:162-168` (Step 4 of `s3:lemL15p`).
- **Manuscript route:** e^{−5uL} ≤ N^{−7.2u}; at most N^u sets U and N^u sets T; \|T\| ≤ m − 1 with m = ⌈ε′u/L²⌉.
- **Lean route:**
  - The proof uses e^{−5uL} ≤ N^{−7u}.
  - The sum over U is computed exactly: Σ_{U≠∅} (N^−6)^{\|U\|} = (1 + N^−6)^N − 1 ≤ 2N^−5.
  - The count of sets T (at most N^u) is kept from the manuscript (`formal/work/p1b/l15.md:100-101`).
  - The ceiling is replaced by (\|T\| : ℝ) < ε′u/L².
  - Step 1 does not need T ⊆ 𝒩.
- **Why:** a cleaner bound with no ceiling.
- **Effect:** none; the statement is the same.
- **Evidence:** `formal/work/p1b/l15.md:94-103`; `formal/EG/Proof/Link/L15.lean:330` (`l15p`).

### D23. Numeric lemmas (L17* Step 4, WellDef series): alternative elementary bounds

- **Manuscript location:** `s3.tex:402-596` (`s3:lemL17s` Step 4); `s7.tex:432-557` (`s7:lemWellDef`(iii)).
- **Manuscript route:** ln(1+g) ≥ g − g²/2; the first group is 4 ≤ s ≤ ⌈K/13⌉.
- **Lean route:**
  - L17s: `Real.abs_log_sub_add_sum_range_le` at order 3 gives ln(1+g) ≥ 15g/16 for g ≤ 1/8. This is thin (0.5% slack) but true (`formal/EG/Proof/Num/L17s.lean:22`, `:343`).
  - WellDef:
    - splits into the cases 13s ≤ K and 13s > K (tail 0.47^s);
    - uses ((s−1)/K)^{2s+1} ≤ (s/K)^{2s+1};
    - shows 2·0.47^{K/13} ≤ 0.1K^−4 via e^{−z} ≤ 10!/z^10 (`formal/EG/Proof/Num/WellDef.lean:24-27`).
- **Why:** g − g²/2 is not in Mathlib, and the integer case split avoids ceilings.
- **Effect:** none; the statements are the same.
- **Evidence:** `formal/work/p2b/NUM.md:301-312`.

### D24. k_own bound: k_own ≤ L_Y/2 + 1 instead of k_own ≤ L_Y ≤ 2λ (COL(a), COL-JV rows 3/8, E1(a))

- **Manuscript location:** `s3.tex:1545-1548`; `s3.tex:1302`, `:1338`; `s5.tex:122` ("k_own = 4J_Y + 1 ≤ L_Y").
- **Manuscript route:** k_own ≤ L_Y ≤ 2λ. With the manuscript's integer floor this holds for every positive L_Y, and L_Y ≥ 103μ − 1 by (B4).
- **Lean route:** `Standing.kown_le` (`formal/EG/Lib/Lend/Standing.lean:98`) proves k_own ≤ L_Y/2 + 1. It is used in COLa (`formal/EG/Lib/Stage1/COLa.lean:36`, `:530`) and in E1(a), where it gives P ≥ 1/(4L).
- **Why:** no side condition L_Y ≥ 1 is needed. That condition arises only from Lean's truncated ℕ floor.
- **Effect:** none. The approval record (`formal/APPROVALS/2026-09-30-P2-specs.md:22`) logs the manuscript's k_own ≤ L_Y as T1. On re-examination it is not a manuscript defect; see "Checked and not errata" in `proofs/manuscript/ERRATA_v6.1.md`.
- **Documentation issue:** the docstring of `formal/EG/Proof/Todo/LemE1.lean:31` still says "by k_own ≤ L", while `formal/work/p3/s5.md:31` records k_own ≤ L/2 + 1.
- **Evidence:** `formal/EG/Lib/Lend/Standing.lean:97-98`; `formal/work/p3/s3.md:42-43`.

### D25. s3/s5 probabilistic constructions realized on product spaces; E1(a) uses a smaller event

- **Manuscript location:** `s3.tex:792-909` (`s3:thmT16s`); `s3.tex:1453` ff. (`s3:lemCOL`(c)); `s5.tex:122` (`s5:lemE1`(a)).
- **Manuscript route:** the auxiliary colouring is "independent"; COL(c) conditions on the lending data; the E1(a) indicator is "no round-l zone".
- **Lean route:**
  - T16s: the product space of the colouring with μ, via `prob_prod_snd` (`formal/EG/Lib/Prob/Basic.lean:920`; `formal/EG/Lib/Link/T16sProof.lean:15-19`; `t16s` at `:90`).
  - COL(c): `IsRSubset.map_pair_eq_prod` together with `prob_compProd_le_of_forall` (`formal/work/p2b/P4B.md:417-418`).
  - E1(a): the Lean statement keeps the TeX event, `zonePhase ω.zone l u = none`, i.e. no round-l zone (`formal/EG/Proof/Todo/LemE1.lean:117`). Only the proof bounds it from below via the smaller event choice(u) = none (`iIndepFun_edge_zone`).
- **Why:** independence must be realized concretely in `FinDist`.
- **Effect:** none; the bounds are the same.
- **Evidence:** `formal/EG/Proof/Todo/LemE1.lean:28-35`; `formal/work/p3/s5.md:29-35`, `:60-61`.

---

## E. Section 4: vortices, and determinism of stage 3

### D26. Vortex lemmas TPV, PV, VX+: different per-step accounting and minor route changes

- **Manuscript location:** `s4.tex:374` (132\|P\| ≤ 169\|P\|); `s4.tex:619` (304\|Pl\| ≤ 369\|Pl\|); `s4.tex:788` (19\|U_j\|); `s4.tex:119-130` ((B)/(MC)); `s4.tex:173-174`.
- **Manuscript route:** per-step counts giving 132\|P\| (TPV), 304\|Pl\| (PV) and 19\|U_j\| per step (VX+).
- **Lean route:**
  - TPV: each class costs 3\|P_{j,c}\| + \|W_j\|, which is at most 12\|P ∩ U_j\| per step. The total is 12·8\|P\| + 48\|P\| = 144\|P\| ≤ 169\|P\| (`formal/EG/Lib/Vortex/TPVRun.lean:20`; core at `:119`). This is looser than the manuscript's 132\|P\|.
  - PV: 28·8\|Pl\| + 64\|Pl\| + 8\|Pl_J\| ≤ 296\|Pl\| (`formal/EG/Lib/Vortex/PVRunMain.lean:18`, `:151`, `:178`), which is sharper than 304.
  - VX+: 4\|W_j\| + 9\|U_j\| ≤ 13\|U_j\| per step, sharper than 19. The total is 26.26N + 13N (`formal/work/p3/s4.md:53`, `:64-65`).
  - (B) is proved in Chernoff form, and PV(b) comes from the engine's vertex clause. All vertices of Z draw levels.
- **Why:** the three lemmas share the P4A step engine, and Chernoff is already in Lib.
- **Effect:** none; the stated constants 169 and 369 and the VX+ bound are kept, and all three counts are within them.
- **Evidence:** `formal/EG/Lib/Vortex/VXRun.lean:123`; `formal/work/p3/s4.md:25-27`, `:36-42`, `:113`, `:124-130`.

### D27. T0-stage3-det: stage 3 deterministic (TPV, PV/lemChild, VX+/lemDemoted, K-RED); lemOneOutcome split

- **Manuscript location:** `s4.tex:159-195` (`lemTPV`), `:400` (`lemPV`), `:645` (`thmVXp`); `s5.tex:163-212` (`lemChild`), `:326` (`lemDemoted`), `:337` (`lemKRED`); `s7.tex:1196-1215` (`lemOneOutcome`).
- **Manuscript route:** each vortex lemma has a good event over the stage-3 labels, with a probability bound. The assembly fixes one stage-3 outcome that lies in all good events. `lemOneOutcome` picks the stage-1 outcome, the stage-3 labels and the ξ_l.
- **Lean route:**
  - The Specs are deterministic existence forms. `formal/EG/Spec/Vortex/TPV.lean:43-50` ("Deterministic form") argues that this is equivalent to the TeX under its hypotheses. The determinism of TPV/PV/VX+ is the TRIAGE decision TPV-DET-SPEC (`TPV.lean:40-42`).
  - `formal/EG/Spec/Light/Child.lean:62`, `Demoted.lean:45` and `KRED.lean:59` quantify ∀ ω ∈ supp, ∀ admissible H_0/E, ∃ decomposition.
  - The good events are internal (`exists_good`, `formal/EG/Lib/Vortex/TPVProb.lean:105`).
  - OneOutcome is split into three parts:
    - `OneOutcomeStage1Statement`;
    - stage 3, which has no Lean content (OO-PROCEDURAL);
    - `OneOutcomeRoundStatement`, whose ξ_l is `Rules.xiChosen` (`formal/EG/Defs/Quot/Round.lean:678`; `xiChosen_spec` at `formal/EG/Lib/Quot/Round.lean:252`; `xiChosen_markovEvent` at `formal/EG/Lib/Quot/RoundExist.lean:48`).
- **Why:** the TeX conclusions are free of labels, and MIX-C applies stage 3 once per part at the final H_0.
- **Effect:** this is weaker than the TeX's uniformity ("there is an outcome that works for all H_0"), but it suffices for every consumer. The main theorem is unaffected.
- **Evidence:** `formal/CONVENTIONS.md:100` (the T0-stage3-det row names lemChild, lemDemoted, lemKRED); `formal/EG/Spec/Vortex/TPV.lean:40-52`; `formal/EG/Spec/Quot/OneOutcome.lean:8-50`; `formal/work/p3/s5.md:47-48`; `formal/work/p2s/s6b.md:127` (T0-mixc-stage3); TRIAGE §2.8.

---

## F. Section 5: light parts

### D28. T0-kred-causality: the "depends only on" clauses of lemParent/K-RED dropped; K-RED is pure existence

- **Manuscript location:** `s5.tex:213-325` (`s5:lemParent`); `s5.tex:337` (`s5:lemKRED`); `s5.tex:399-402` (`remConstants`: c^exact = 739, c_KRED = 745).
- **Manuscript route:** round procedures with "depends only on" clauses. K-RED is itemized with c^exact = 739 and stated with 745, and cap_l is existential.
- **Lean route:**
  - `LemKREDStatement` (`formal/EG/Spec/Light/KRED.lean:59`): for every ω ∈ supp and every Lext with `LentExtHyp`, there is a D that decomposes E(G) \ K_std \ ⋃Lext, with length ≤ (D_*/2 + 745 + ε_K)n + 80·dem + 369·lp.
  - `LemParentStatement` (`formal/EG/Spec/Light/Parent.lean:78`) holds for every arc with `ArcHyp` and has a per-round cap bound.
  - `LemParentSumStatement` (`:106`) sums 4·14(J̄+1)M(M+1)ν_l + 14(J̄+1)n/(102 log_2 λ_{l−2})². Only the cap_l summand is replaced by an explicit bound; the 4·14(J̄_l+1)M_l(M_l+1)ν_l term is kept as in the TeX.
  - The procedure is internal: `KHyp.exists_decomp` (`formal/EG/Lib/Light/KREDStep.lean:433`), with invariant `KInv`.
- **Why:** no consumer reads the causality clauses.
- **Effect:** none on the stated bounds. The proof gives (D_*/2 + 739 + ε_ch)n + 80·dem + 369·lp (`formal/work/p3/s5.md:47`).
- **Evidence:** `formal/CONVENTIONS.md:101`; `formal/EG/Spec/Light/KRED.lean:20-68`; `formal/EG/Spec/Light/Parent.lean:78-115`; `formal/work/p3/s5.md:41-48`; TRIAGE §2.8, §2.12; `formal/APPROVALS/2026-09-30-P2-specs.md` watch item (2).

---

## G. Section 6: junction systems and the MIX-C assembly

### D29. JS-LC Steps 4–5 simplified (no S_0 system; cherries grouped first-fit)

- **Manuscript location:** `s6.tex:442-452` (the statement of `s6:lemJSLC`: 126n/M_l + 1.5 Σ_giant m_{Y,l}); Step 4 at `s6.tex:498-519`; Step 5 at `s6.tex:521-543`; Step 8 at `s6.tex:598-609` (15n/M_l + Σ_giant sco_{Y,l}).
- **Manuscript route:**
  - The non-giant components of R_Y become clusters in S_0(Y,l). They are oriented by MED, layered by EQ-LPT and padded (eqSzeroCost: ≤ 1.5ΣΦ/K^JS + 5γ_l).
  - Only the giant components get the cherry split, with a greedy colouring into cherry classes (eqCherryCost).
  - Step 8 gives ≤ 15n/M_l + Σ_giant sco_{Y,l} with sco ≤ 1.5m, and the lemma is stated with 126 and 1.5.
- **Lean route:**
  - Every component of R_Y is split into cherries. This is possible because after Step 2 every centre has even R_Y-degree.
  - Cherries are grouped first-fit into groups of at most K^JS_l = M_l² pairwise vertex-disjoint cherries, one cherry per layer, with load 1 and no padding (`formal/EG/Proof/Chain/JSLCGroups.lean:11-19`; `exists_grouping` at `:112`).
  - S_0, MED, EQ-LPT and the padding are never built.
  - Per class, \|used Y\| ≤ m_{Y,l} + 2M_l + \|R_Y\|/K^JS_l (`card_used_le_real`, `formal/EG/Proof/Chain/JSLCBound.lean:49`). Non-giant classes have m_{Y,l} ≤ 2γ_l (`sum_mY_le`, `:94`, via `C.mY_le_of_not_isGiant`).
  - `step8_arith` (`:123`) proves g + ν(2γ + 2x) + nx/x² ≤ 126n/x + 1.5g, where g is the sum of m over giant pairs.
  - Step 8 is assembled in `EG.jslc` (`formal/EG/Proof/Chain/JSLC.lean:36`, `:47-80`).
- **Why:** a simpler proof of an existential Spec. Because a simpler proof of the weakest link can signal a Spec that is too weak, a consumer audit was run. Its verdict was "sufficient".
- **Effect:**
  - The stated result is unchanged: the count conjunct of the Spec is exactly the TeX constant, 126n/M_l + 1.5 Σ_giant m_{Y,l} (`formal/EG/Spec/Chain/JSLC.lean:109-131`).
  - The Lean construction actually yields ≤ 11.96n/M_l + Σ_giant m_{Y,l}: ν_l·2γ_l ≤ 5.48n/M_l, ν_l·2M_l ≤ 5.48n/M_l, and n(M_l − 1)/M_l² ≤ n/M_l. The manuscript's corresponding term is ν_l·5γ_l ≤ 13.7n/M_l.
  - MED, EQ-LPT and PAR-in-S_0 are not on the Lean critical path for JS-LC. As a side effect, the T1 findings F2 and F5 of `formal/work/p2b/P2E.audit.md:285`, `:288` lie in machinery that Lean never builds. Those findings are the M_l = 1 edge case and the empty-S_0 case, and both are listed as open errata.
- **Evidence:** `formal/work/p2b/P2J.md:465` (bound), `:467-477` (deviation); `formal/work/p2b/P2J.consumer-audit.md:12` (VERDICT sufficient), `:19`, `:130-136` (count re-derived), `:222-226` (T0-7); `STATE.md:482-484`, `:490-492`.

### D30. JS-LC / J+ interface: the "no class edge used" hypothesis dropped; J+ facts re-encoded

- **Manuscript location:** `s6.tex:446` (the hypothesis); `s6.tex:620-660` (`s6:lemJplus`; (J2) at `:638`, (v) at `:655`).
- **Manuscript route:** JS-LC assumes that no JS class edge has been used. J+ asserts that J_l is exactly the set of Step 2 deletions "for every choice", and J+(v) (independence of edge colours) is item (v) of the lemma.
- **Lean route:**
  - `JSLCStatement` (`formal/EG/Spec/Chain/JSLC.lean:109`) has no "not used" hypothesis (T0-1).
  - J+ is split into three parts:
    - The J-dependent part ((i) exhaustive, J1, J2, (ii)) is the conjunct `JPlusProps` of `JSLCStatement` (`formal/EG/Defs/Chain/JSet.lean:128`).
    - The J-independent items (J3, exclusivity, (iii), (iv)) form the separate, proved Spec `JplusFactsStatement` (`formal/EG/Spec/Chain/JPlus.lean:56`).
    - (v) comes from the stage-1 law (T0-3; `formal/EG/Spec/Chain/JPlusV.lean`).
  - "Exactly the deletions of Step 2" is not encoded (T0-2). `J2card` is J.card ≤ G.card·(M − 1), without the factor 1.37 (`JSet.lean:150`).
  - LentJS is restricted to lendGoodAnc classes, and the partition is `IsDecomp` of ((⋃B ∪ LentJS) \ J).
  - The obligation from the dropped hypothesis is that LentJS is disjoint from earlier output, including LU ∩ LJS = ∅. It is discharged in the assembly:
    - MIX-C builds the standalone chain and then applies K-RED once with Lent_ext ⊆ lentJSJV.
    - K-RED's conclusion decomposes E(G) \ K_std \ ⋃Lent_ext.
    - LU ∩ LJS = ∅ is `disjoint_LU_lentJSJV` in the K-RED support library (`formal/EG/Lib/Light/KREDAux.lean:57`).
    - MIX-C discharges the rest through ORDER-DECOUPLE and K-RED's exclusion of Lent_ext (`formal/work/p3/s6.md:26-30`).
- **Why:** the TeX uses the hypothesis only in claim (d). Dropping it makes JS-LC easier to apply, and the obligation is discharged once in the assembly.
- **Effect:** none on stated results. For every consumer the Spec is at least as strong as the TeX, and the moved obligation is proved in the MIX-C/K-RED assembly.
- **Evidence:** `formal/EG/Spec/Chain/JSLC.lean:50` (JSLC-USED), `:60-80`; `formal/EG/Defs/Chain/JSet.lean:39` (1.37 vestigial), `:128-150`; `formal/work/p2b/P2J.consumer-audit.md:195-226` (T0-1…T0-7; T1 "None"); `formal/work/p2/TRIAGE.md:210-224` (§2.9); `formal/APPROVALS/2026-09-30-P2-specs.md` watch item (5); `formal/EG/Lib/Chain/MixCSets.lean`; `formal/EG/Lib/Chain/MixCAssembly.lean:10-21`; `formal/EG/Spec/Light/KRED.lean:59-68`.

### D31. T0-glob-input: the HCCglob hypothesis stated at the input level

- **Manuscript location:** `s6.tex:221-225` (`s6:lemHCCglob`, second paragraph); JS-LC Step 7 at `s6.tex:580-596`.
- **Manuscript route:** the hypothesis names HCC-P outputs, F_j ⊆ E(P_j) ("their beads together with their sets F_j").
- **Lean route:** `HccGlobStatement` (`formal/EG/Spec/Chain/HCCP.lean:107`) assumes `Disjoint (beads ∪ allPathEdges)` across systems. This is stronger, since F_j ⊆ pathEdges. The conclusion adds that every cycle is a cycle of G.
- **Why:** read literally, the hypothesis is not well formed on inputs. The input-level form is exactly what Step 7 checks.
- **Effect:** none. The optional rewording ("their beads and their path edges are pairwise disjoint") is listed as open erratum T0-glob-input.
- **Evidence:** `formal/EG/Spec/Chain/HCCP.lean:95-125`; `formal/CONVENTIONS.md:99`; `formal/work/p2b/P2E.audit.md:284` (F1, T0); `formal/work/p2s/s6a.md:90`; TRIAGE §1b GLOB-OUTPUT-LEVEL-HYP.

### D32. HCC-P Step 3: only \|W\| ≤ Φ used

- **Manuscript location:** `s6.tex:140-219` (`s6:lemHCCP`; Step 3 near `:214`; Step 4 at `:216`, "at most \|W\| = Φ cycles").
- **Manuscript route:** asserts \|W\| = Φ.
- **Lean route:** bounds \|W\| ≤ Σ d^− ≤ Σ dem^+ = Φ. GATE needs only the inequality.
- **Why:** only the inequality is needed.
- **Effect:** none. The audit re-verifies the equality.
- **Evidence:** `formal/work/p2b/P2E.audit.md:286` (F3); `formal/EG/Spec/Chain/HCCP.lean:70` (`HccpStatement`); `formal/EG/Proof/Chain/HCCP.lean:110` (`hccp`).

### D33. MIX-C assembly order: the standalone chain R..1 first, then K-RED once (ORDER-DECOUPLE)

- **Manuscript location:** `s6.tex:680-712` (`s6:consOrder`); `s6.tex:759` (`s6:thmMIXC`).
- **Manuscript route:** one interleaved pass over the rounds R..1 (TPV; light parts, child vortex and lemParent; JS-LC; the J-consumer), with the Lent sets defined recursively.
- **Lean route:**
  - `chain_exists` (`formal/EG/Lib/Chain/MixCRound.lean:260`) builds the standalone chain from `round_exists` (`:155`): TPV on E_l(Z) \ F, JS-LC with B_Z = E^Q(Z), and the consumer `C.out l J_l`.
  - K-RED is then applied once, with Lent_ext := LentAll ∩ lentJSJV (`formal/EG/Lib/Chain/MixCAssembly.lean:10-21`; `mixc_of_specs` at `:52`).
  - The JS-LC cost is summed as 126n Σ 1/M_l ≤ 126n(2/D_*) = 252n/D_* (`MixCAssembly.lean:468-512`). The giant sum is bounded by the full sum via `filter_subset` (`:473-475`).
- **Why:** TRIAGE checked that steps (1), (3) and (4) of round l never read an output of the light-part step.
- **Effect:** none; the decomposition and the cost bound are the same. `s6:lemLent` is internal to the proof.
- **Evidence:** `formal/EG/Lib/Chain/MixCRound.lean:10-25`; `formal/EG/Proof/Todo/MixC.lean:35`; `formal/work/p3/s6.md:26-30`; `formal/work/p2/TRIAGE.md:85`, `:220`.

### D34. MIX-C statement shape: Option B′ and restricted consumer and outcome classes

- **Manuscript location:** `s6.tex:759-830` (`s6:thmMIXC`); `s6.tex:667-678` (`s6:defJconsumer`).
- **Manuscript route:** any J-consumer and any stage-1 outcome; the consumer cost is stated in terms of the chain's own J_l.
- **Lean route:**
  - `MixCStatement` (`formal/EG/Spec/Chain/MixC.lean:118`) takes ω ∈ supp, `C : JConsumer run G δ (stageOf ω)`, and a bound b with ∀ l J, `JPlusProps` → \|C.out l J\| ≤ b l J.
  - It concludes ∃ Js with `JPlusProps` and ∃ D decomposing E(G) with length ≤ … + Σ_{l=3}^R b l (Js l).
  - The m_{Y,l} term sums over all (Y,l) with l ∈ [1,R], not only giant pairs (T0-mixc-sums).
  - The TPV bullet is not a conjunct. It is the separate, proved Spec `MixCTPVApplicableStatement`, with the concrete parameters (2^−5, s_l/4) / (2^−5, s_l) (`MixC.lean:140-160`).
- **Why:** this is the consumer-form interface that `s7:propCost` needs.
- **Effect:** weaker than the TeX but sufficient: the obligation of propCost (bounds uniform over `JPlusProps` sets) is met. No effect on the main theorem.
- **Evidence:** `formal/EG/Spec/Chain/MixC.lean:118-135`; `formal/work/p2s/s6b.md:120-131`; TRIAGE §2.9; `formal/EG/Spec/Quot/Cost.lean:56-59`.

---

## H. Section 7: quotient rounds and costs

### D35. s7 counts use n(M_l − 1) instead of the manuscript's deliberately loose 1.37nM_l (X_pool without propOV; CC copies)

- **Manuscript location:** `s7.tex:1072-1073`, `:1088` (`s7:lemEXprime`: Σ_Z \|Z^0\| ≤ 1.37n by propOV); `s7.tex:750-752`, `:844` (`s7:lemCC`: 2.74nM_l).
- **Manuscript route:** Σ_h c^agg_{h,l} ≤ 1.37nM_l via propOV, and Σ \|S_w\| ≤ 2.74nM_l.
- **Lean route:**
  - `formal/EG/Lib/Quot/Xpool.lean` uses that the classed-port sets are disjoint, so Σ_Z \|Q_Z\| ≤ n (`sum_card_classed_le`, `:52`).
  - It follows that Σ_h c^agg ≤ (M_l − 1)Σ\|Q_Z\| (`sum_cAgg_le`, `:61`) and Σ ω_l ≤ (M_l − 1)n + M_l n (`sum_poolWeight_le`, `:90`).
  - CCCopies uses Σ_{κ,w} \|S_w\| ≤ 2\|parObjs\| ≤ 2n(M_l − 1) (`formal/EG/Proof/Todo/CCCopies.lean:25`, `:170`).
- **Why:** a tighter count that is direct in Lean. It removes the dependence on propOV for this step.
- **Effect:** the stated results are unchanged, and the proofs have extra slack. The claim "no propOV" is local to the pooled-weights step. Other parts of s7 still cite propOV in the TeX, e.g. `s7.tex:948-950` (Σ_w mult_r(w) ≤ 1.37n). That part was not re-audited here.
- **Evidence:** `formal/EG/Lib/Quot/Xpool.lean:5-20`; `formal/EG/Proof/Todo/EXprime.lean:41`, `:153`; `formal/work/p3/s7.md:20-22`, `:35-38`.

### D36. s7 round step: "the past" as an abstract parameter; `ofPast_valid` proved as a Lib theorem; JVps validity from Hcd > 0

- **Manuscript location:** `s7.tex:231-431` (`s7:consRound`); `s7.tex:1366` (`s7:thmJVps`).
- **Manuscript route:** the round step reads the past of the run directly.
- **Lean route:**
  - The round step takes a `RoundInput V` with a `.Valid` predicate.
  - `EG.Quot.ofPast_valid` (`formal/EG/Lib/Quot/OfPastValid.lean:74`) proves `(RoundInput.ofPast run G δ S π l J).Valid` from `RunHyp`, the designation, `S.Coherent` and `JPlusProps`. `formal/EG/Proof/Todo/Cost.lean` and `formal/EG/Lib/Quot/LiftUniv.lean` use it.
  - JVps uses `RoundInput.chosenRules_valid_of_Hcd_pos` (`formal/EG/Lib/Quot/RoundExist.lean:59`; `formal/EG/Proof/Todo/JVps.lean:33`).
- **Why:** decouples the s7 round lemmas from the s2–s6 run model.
- **Effect:** none. Once `ofPast_valid` is proved, the run-level Specs are unconditional.
- **Evidence:** `formal/EG/Lib/Quot/OfPastValid.lean:70-80`; `formal/EG/Proof/Todo/JVps.lean:19`; `formal/work/p3/s7.md:102-103`; TRIAGE §2.10.

---

## Candidates checked and not confirmed

None. All 36 candidate deviations were confirmed against the Lean sources and the notes.

Several candidates cited notes incorrectly, and the entries above use the corrected citations and wording:

- `formal/work/p3/s6.md:125-136` does not exist, because the file has 48 lines. The correct citation is `s6.md:26-30`.
- `formal/work/p3/MAIN.md:117-119` and `:113-136` do not exist, because the file has 63 lines. The correct citations are `MAIN.md:12-15` and `:10-40`.
- The "used only through Cor 22" sentence is at `s1.tex:1500-1501`, not `:1512-1513`.
- There is no declaration `xiChosen_mem`.
- `GammaCondExistsStatement` is not the "for every real N_0" form; that form is `GammaSatStatement`.
- The 65534 ≤ 65536 margin belongs to `lemCap`(i), not (ii).
- The TPV accounting is looser than the manuscript's (144 versus 132), not sharper.
