# Correspondence: manuscript v6.1 ↔ Lean formalization

> **Status: candidate proof, AI-generated and AI-reviewed; a Lean 4 proof of the formal-conjectures statement Erdos184.erdos_184 passes the project's acceptance checks (GitHub release run 36767721300, 2026-09-30: comparator in release mode, strict FinalCheck and three kernel replays all passed); not yet reviewed by human experts.**


This file maps every node of the candidate manuscript to the Lean formalization: each theorem,
lemma, proposition, corollary, fact, definition, cited result, remark and convention. For each
node it gives the Lean statement (a `def …Statement : Prop` in `formal/EG/Spec/`) and the Lean
theorem that proves it (in `formal/EG/Proof/` or `formal/EG/Lib/`). All Lean paths are relative to
`formal/`. Manuscript labels are the `\label{…}` keys of `proofs/manuscript/s1.tex` … `s7.tex`
(version 6.1). Numbers are those of the v6.1 PDF as compiled from `proofs/manuscript/ms.tex`; they
may change in later versions, so the labels are the stable reference. Version 6.2
(the arXiv version; its sources are not part of this repository), which applies the 21 errata still open in v6.1, has the
same labels and the same statement numbers (checked on the `.aux` files of both builds).

**What this table is and is not.** Only the upstream statement `Erdos184.erdos_184`, together with
the definitions it unfolds to (pinned by `closure-sha256`), is trusted; comparator checks the final
theorem against it (see `README.md` and `formal/TRUST.md` §2 items 3-5). The
`EG/Spec` statements below are the project's own reading of the manuscript. They are **not** part
of the trusted base, and nothing checks mechanically that they match the TeX. A mismatch cannot make
the final theorem false. It would make this correspondence, the claim that the Lean proof follows
the manuscript, inaccurate. Each `EG/Spec` file quotes the manuscript text. Most `EG/Spec` files
(113 of 122) have a "Formal reading" section that explains the encoding decisions; the numeric and
assembly files `Num/{CC,L17s,OV,StarInputs}`, `Gamma/{Sat,N0}`, `Main` and
`Chain/{JSLCSteps,EngineMult}` explain their reading in the docstrings. Read those sections and
docstrings to judge fidelity. Where the Lean route departs from the manuscript, see
`formal/work/p4/DEVIATIONS.md`. For errors in the manuscript, see
`proofs/manuscript/ERRATA_v6.1.md`. Both were committed in `fbe6379` of the development
repository.

Contents:

* Part 1: the end-to-end chain from the manuscript's Main Theorem to `Erdos184.erdos_184`.
* Part 2: the external (classical and cited) results proved in Lean.
* Part 3: the node-by-node tables, one per manuscript section.
* Part 4: how this table was built and checked.

---

## Part 1. The end-to-end chain

| Step | Lean declaration | File | Manuscript |
|---|---|---|---|
| upstream target (unchanged) | `Erdos184.erdos_184` | `comparator/Challenge.lean` (byte-identical to formal-conjectures `2424bb48…` `FormalConjectures/ErdosProblems/184.lean`) | Theorem 1.1 (`s1:thmMain`), "in particular" part |
| comparator's Solution | `Erdos184.erdos_184` := bridge applied to `EG.Proof.mainInternal` | `comparator/Solution.lean` | — |
| second artifact (FinalCheck, `leanchecker --fresh`) | `EGCheck.erdos_184 : type_of% @_root_.Erdos184.erdos_184.{u}` := `EGCheck.Bridge.solution` | `EGCheck/Final.lean`, `EGCheck/Bridge.lean` | — |
| bridge (internal ⇒ upstream) | `EGCheck.Bridge.of_mainInternal_unfolded` | `EGCheck/BridgeCore.lean`, helper lemmas in `EGCheck/BridgeLemmas.lean` | — (the objects `EG.Obj`/`EG.IsDecomp` of `s1:defObject` become `Finset G.Subgraph`/`SimpleGraph.IsDecomposition`) |
| internal main theorem | `EG.Spec.MainInternal` → `EG.Proof.mainInternal` | `EG/Spec/Main.lean`, `EG/Proof/Main.lean` | Theorem 1.1 via Corollary 7.22 (`s7:thmMainProof`) |
| hypothesis of HI″ | `EG.Proof.hiHyp_of_gammaCond : N0Cond N0 → GammaCond N0 D → Spec.HIHyp D N0 (Quot.C0 D) (Quot.thetaQ D)` | `EG/Proof/Main.lean` | proof of Corollary 7.22 |
| constants `N_0`, `D_*` exist | `EG.exists_gammaCond : Spec.GammaCondExistsStatement` | `EG/Proof/Gamma/Sat.lean` | Lemma 7.21 (`s7:lemGammaSat`) |
| a valid run exists | `EG.Todo.ExistsRun : Spec.ExistsRunStatement` | `EG/Proof/Todo/ExistsRun.lean` | Proposition 2.15 (`s2:propExists`) |
| a designation exists | `EG.Chain.exists_isDesignation` | `EG/Lib/Chain/Design.lean` | Definition 6.8 (`s6:defDesign`) |
| quotients `Q_3, …, Q_R` | `EG.Todo.JVps : Spec.JVpsStatement` | `EG/Proof/Todo/JVps.lean` | Theorem 7.19 (`s7:thmJVps`) |
| layered quotient induction | `EG.hi : Spec.HIStatement`; `EG.mainInternal_of_hiHyp` | `EG/Proof/Quot/HI.lean`, `EG/Proof/Quot/HIMain.lean` | Theorem 7.20 (`s7:thmHI`) |

The assembly record is `formal/work/p3/MAIN.md`. Its axiom scan dates from before the last stubs
were proved; the current scan (0 `sorryAx`) is in `formal/work/p3/ACCEPT.md`.

## Part 2. External results proved in Lean

None of these is assumed. Each is a `Prop` in `EG/Spec`, proved in the project without `sorry`.
Bibliographic data are copied from the reference list of Bucić–Montgomery (arXiv:2211.07689v2,
checked against its text) where possible. The other entries come from the manuscript's bibliography
and are marked [CHECK].

"In closure" means that the proof lies in the import closure of `EG/Proof/Main.lean`, so the final
theorem can use it. "No" means the final theorem does not use that Lean theorem. The mathematics may
still enter through a library lemma: for example, Hall's theorem is available directly from Mathlib.

| Result | Source | Manuscript | Lean statement | Lean proof | In closure |
|---|---|---|---|---|---|
| Lovász: every `n`-vertex graph decomposes into at most `n/2` paths and cycles | L. Lovász, *On covering of graphs*, in Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic Press, New York, 1968, pp. 231–236 (as cited in [BM, ref. 43]) | Cited result 1.21 (`s1:citThm21`) = [BM, Theorem 21] | `EG.Spec.LovaszStatement` (`EG/Spec/Ext/Lovasz.lean`) | `EG.LovaszC.lovasz` (`EG/Lib/Ext/LovaszThm.lean`), from Lovász's construction `EG.LovaszC.lovasz_construction` (`EG/Lib/Ext/LovaszCons.lean`) by strong induction on the number of edges; wrapper `EG.Todo.Lovasz` | yes |
| Every graph decomposes into paths with each vertex an end of at most two of them | [BM, Corollary 22] | Cited result 1.22 (`s1:citCor22`) | `EG.Spec.Cor22Statement` | `EG.cor22` (`EG/Proof/Ext/Cor22.lean`; `EG/Lib/Ext/Cor22.lean`), from Lovász's theorem | yes |
| Haxell's condition for an `𝓧`-saturating matching in a hypergraph | P. E. Haxell, *A condition for matchability in hypergraphs*, Graphs Combin. 11 (1995), 245–248 [CHECK: from the manuscript's bibliography, not verified against the paper] | Cited result 1.29 (`s1:citHaxell`) | `EG.Spec.HaxellStatedForm` (the stated form) and `EG.Spec.HaxellStatement` (the `q²`-form used by Lemma 3.7) (`EG/Spec/Ext/Haxell.lean`) | `EG.haxell_stated`, `EG.haxell`, and `EG.haxellStatement_of_statedForm` (`EG/Proof/Ext/Haxell.lean`): the alternating-tree argument written out in `s1.tex` | `HaxellStatement`: yes |
| Long cycle in an `(ε,0)`-expander, explicit form `ε² m / (18 log⁴ m)` | [BM, Lemma 25] (stated there with `Ω(·)`; the explicit constant is the manuscript's) | Cited result 1.23 (`s1:citLem25`) | `EG.Spec.BMLemma25Statement` (`EG/Spec/Ext/BMLemma25.lean`) | `EG.bmLemma25` (`EG/Proof/Ext/BMLemma25.lean`; DFS lemmas in `EG/Lib/Ext/DFS.lean`, `EG/Lib/Ext/DFSCycle.lean`). Hypothesis `2 ≤ m`, found necessary during the formalization, added in v6 (`d6f3c49`) and present in v6.1 (`m ≥ max(2, 2^30/ε²)`); `EG.bmLemma25_literal_false` shows the reading without it is false at `m = 1` | yes |
| One pair out of `2t − 1` | [BM, Proposition 8] | Cited result 1.10 (`s1:citProp8`) | `EG.Spec.BMProp8Statement` | `EG.Todo.BMProp8`, from `EG.BM8.bmProp8` (`EG/Lib/Ext/BMProp8.lean`) | yes |
| Expansion or a `d`-fold neighbourhood | [BM, Proposition 12] | Cited result 1.13 (`s1:citProp12`) | `EG.Spec.BMProp12Statement` | `EG.Todo.BMProp12`, from `EG.FGraph.IsExpander.bmProp12` (`EG/Lib/Ext/BMProp12.lean`) | yes |
| Remark after the definition of `(ε,s)`-expanders | [BM, Definition 11] | Cited result 1.12 (`s1:citDef11`) | `EG.Spec.ExpanderMinDegStatement`, `EG.Spec.ExpanderEpsZeroStatement` | `EG.Todo.ExpanderMinDeg`, `EG.Todo.ExpanderEpsZero` | no |
| Chernoff's bound for `Bin(n,p)` | [BM, Theorem 4] | Cited result 1.8 (`s1:citChernoff`) | `EG.Spec.ChernoffBinomialStatement` | `EG.Todo.ChernoffBinomial` (from `EG.FinDist.chernoffGen_upper` and `…_lower`, `EG/Lib/Prob/Chernoff.lean`) | no |
| Chernoff bounds for sums of independent indicators | [JLR00, Theorems 2.1 and 2.8] (S. Janson, T. Łuczak, A. Ruciński, 2000) [CHECK: complete reference] | Cited result 1.25 (`s1:citChernoffGen`) | `EG.Spec.ChernoffGenStatement`, `…GenMeanStatement`, `…GenTailStatement` | `EG.Todo.ChernoffGen`, `EG.Todo.ChernoffGenMean`, `EG.Todo.ChernoffGenTail` | `ChernoffGen`: yes |
| Markov's inequality and its two uses | standard | Cited result 1.26 (`s1:citMarkov`) | `EG.Spec.MarkovStatement`, `…AStatement`, `…BStatement`, `…CondStatement` | `EG.Todo.Markov` (from `EG.FinDist.prob_le_expect_div`), `EG.Todo.MarkovA`, `EG.Todo.MarkovB`, `EG.Todo.MarkovCond` | no |
| Bernstein-type inequality for bounded differences | standard (proved in full in the manuscript) | Lemma 1.27 (`s1:lemBBD`) | `EG.Spec.BBDStatement`, `EG.Spec.BBDRVStatement` | `EG.bbd`, `EG.bbdRV` (`EG/Proof/Found/BBD.lean`) | yes |
| Hall's theorem | P. Hall, *On representatives of subsets*, J. London Math. Soc. 10 (1935), 26–30 [CHECK: from the manuscript's bibliography] | Cited result 1.28 (`s1:citHall`) | `EG.Spec.HallStatement` | `EG.Todo.Hall`, from Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective` | no |
| `T`-joins in spanning trees; Euler circuits in even (multi)graphs | standard | Cited result 1.30 (`s1:citEuler`) (a), (b) | `EG.Spec.EulerTreeTJoinStatement`, `EG.Spec.EulerMultiStatement` | `EG.eulerTreeTJoin`, `EG.eulerMulti` (`EG/Proof/Found/`) | `EulerMulti`: yes |
| The elementary `O(n log n)` bound by iterated removal of a long cycle | manuscript Fact 1.6 (attributed there to Erdős and Gallai [EG66]); the introduction of [BM] describes this bound as "observed by Erdős and Gallai", via iterative removal of a longest cycle | Fact 1.6 (`s1:factEG0`) | `EG.Spec.FactEG0aStatement`, `…aFnumStatement`, `…bStatement` | `EG.factEG0a`, `EG.factEG0aFnum`, `EG.factEG0b` (`EG/Proof/Found/EG0.lean`) | yes |

[BM] = M. Bucić and R. Montgomery, *Towards the Erdős–Gallai cycle decomposition conjecture*,
arXiv:2211.07689; Advances in Mathematics 437 (2024), 109434. The journal data are taken from
reference [15] of R. Montgomery, *Recent progress in graph theory using expansion*,
arXiv:2607.26049.

The B–M results cited only for their proof structure (Lemmas 9, 14, 17, 19; Propositions 13, 18)
and those not used (Lemma 15, Theorem 16) are not formalized as such. The manuscript restates and
proves the versions it needs (Part 3, Section 1).

## Part 3. Node-by-node tables

There is one row per blueprint node (`formal/work/p2/nodes_s*.json`, 127 nodes). Column **F**:

* **S**: the node has at least one Lean statement, and every one is proved;
* **D**: the node is realised by definitions only (in `EG/Defs`);
* **P**: the node is proof-internal (a construction inside another Lean proof; no statement of its
  own);
* **—**: not formalized (remarks without mathematical content, notation, and cited results used
  only for their proof structure or not used).

In "Lean statement → proof", statements are in namespace `EG.Spec`, and proofs carry their full
names. "defs:" lists the main definitions, not all of them. "aux. defs" are auxiliary `def`s that
live in a `Spec` file.

**○** marks a statement whose proof lies **outside the import closure** of `EG/Proof/Main.lean`
(and of `EGCheck/BridgeCore.lean`). Such a Lean theorem is proved and kernel-checked by
`leanchecker EG`, but the final theorem does not use it. Often the mathematics still enters through
a library lemma that the consumer calls directly. For example, `EG.Todo.HS` (Lemma HS) is not
imported, while `EG.Todo.HSCor`, which calls the same library lemma `EG.HB.hs_expander`, is used.
In other cases the Lean route does not need the statement. This table does not record why each ○
statement is unused. Some cases are explained by a route difference in
`formal/work/p4/DEVIATIONS.md` (e.g. D10 for `EulerTreeTJoin`); the rest follow from the consumer
calling a library lemma directly. Statements without ○ lie in the closure. That only means the final theorem *can* use them. This table does not compute the exact
dependency cone, which would need Lean.

### 3.1 Manuscript Section 1 (`s1.tex`): conventions, cited inputs, constants

| Label | No. (v6.1) | Result | F | Lean files | Lean statement → proof | Notes |
|---|---|---|---|---|---|---|
| `s1:thmMain` | 1.1 | Theorem: Main Theorem (candidate) | S | EG/Spec/Main.lean | `MainInternal` → `EG.Proof.mainInternal` | Lean target: `MainInternal`: ∃ c : ℕ, every simple graph on a finite `V : Type` has a decomposition into ≤ c·|V| objects (the "in particular f(n) = O(n)" part). Proved by `EG.Proof.mainInternal` following s7:thmMainProof; transported to `Erdos184.erdos_184` by `EGCheck.Bridge.of_mainInternal_unfolded` (Part 1). The explicit constant c_EG is the separate statement `CorJVpsEGStatement` (row s7:thmMainProof). |
| `s1:remStatus` | 1.2 | Remark: status of this manuscript | — | — | — | No mathematical content; not formalized. |
| `s1:convGraphs` | 1.3 | Convention: graphs, logarithms, neighbourhoods, balls | D | EG/Defs/Log.lean<br>EG/Defs/Walk.lean<br>EG/Defs/Graph.lean | defs: `EG.logIter`, `EG.logStar`, `EG.IsThrough`, `EG.ball`, `EG.FGraph`, `EG.edgesAt`, … (18 in all) | Definitions only (finite simple graphs `EG.FGraph`, degrees, balls, log, log*). |
| `s1:defObject` | 1.4 | Definition: objects and f | D | EG/Defs/Objects.lean<br>EG/Defs/Fnum.lean | defs: `EG.Obj`, `EG.Obj.WF`, `EG.IsDecomp`, `EG.fnum`, `EG.fmax`, `EG.Obj.isEdge` | The internal statement uses `EG.Obj`/`EG.IsDecomp`; `EGCheck/BridgeLemmas.lean` converts them to `Finset G.Subgraph` and `SimpleGraph.IsDecomposition` of the upstream statement. |
| `s1:factAdd` | 1.5 | Fact: elementary properties of f | S | EG/Spec/Found/FactAdd.lean | `FactAddAStatement` → `EG.Todo.FactAddA` ○<br>`FactAddBStatement` → `EG.Todo.FactAddB` ○<br>`FactAddCStatement` → `EG.Todo.FactAddC` ○<br>`FactAddDStatement` → `EG.Todo.FactAddD` ○<br>`FactAddDMonoStatement` → `EG.Todo.FactAddDMono` ○ |  |
| `s1:factEG0` | 1.6 | Fact: the long-cycle bound | S | EG/Spec/Found/EG0.lean | `FactEG0aStatement` → `EG.factEG0a`<br>`FactEG0aFnumStatement` → `EG.factEG0aFnum`<br>`FactEG0bStatement` → `EG.factEG0b` |  |
| `s1:citNotation` | 1.7 | Cited result: [BM, §2.1, §2.6] (notation) | — | — | — | Notation only; realised by the Defs of s1:convGraphs. |
| `s1:citChernoff` | 1.8 | Cited result: [BM, Theorem 4] (Chernoff) | S | EG/Spec/Found/Chernoff.lean | `ChernoffBinomialStatement` → `EG.Todo.ChernoffBinomial` ○ |  |
| `s1:citDef7` | 1.9 | Cited result: [BM, Definition 7] | D | EG/Defs/Expander.lean | defs: `EG.FGraph.IsPathConnected` | Definition only. |
| `s1:citProp8` | 1.10 | Cited result: [BM, Proposition 8] | S | EG/Spec/Ext/BMProp8.lean | `BMProp8Statement` → `EG.Todo.BMProp8` | Underlying proof: `EG.BM8.bmProp8` (EG/Lib/Ext/BMProp8.lean). |
| `s1:citLem9` | 1.11 | Cited result: [BM, Lemma 9] | — | — | — | Not formalized as such: cited for its proof structure; the version used, s3:lemL9rho, is stated and proved in full. |
| `s1:citDef11` | 1.12 | Cited result: [BM, Definition 11] | S | EG/Defs/Expander.lean<br>EG/Spec/Ext/BMDef11.lean | defs: `EG.FGraph.IsExpander`<br>`ExpanderMinDegStatement` → `EG.Todo.ExpanderMinDeg` ○<br>`ExpanderEpsZeroStatement` → `EG.Todo.ExpanderEpsZero` ○ | Definition `EG.FGraph.IsExpander`; the remark after it is the two statements shown. |
| `s1:citProp12` | 1.13 | Cited result: [BM, Proposition 12] | S | EG/Spec/Ext/BMProp12.lean | `BMProp12Statement` → `EG.Todo.BMProp12` | Underlying proof: `EG.FGraph.IsExpander.bmProp12` (EG/Lib/Ext/BMProp12.lean). |
| `s1:citProp13` | 1.14 | Cited result: [BM, Proposition 13] | — | — | — | Not formalized as such (proof-structure citation); s3:propP13s is stated and proved in full. |
| `s1:citLem14` | 1.15 | Cited result: [BM, Lemma 14] | — | — | — | Not formalized as such (proof-structure citation); the needed statements are s2:lemOVgeneric, s2:lem14tau, s2:defHBtp. |
| `s1:citLem15` | 1.16 | Cited result: [BM, Lemma 15] | — | — | — | Not used by the route (replaced by s3:lemL15p); not formalized. |
| `s1:citThm16` | 1.17 | Cited result: [BM, Theorem 16] | — | — | — | Not used as a black box (s3:thmT16s is proved in full); not formalized. |
| `s1:citLem17` | 1.18 | Cited result: [BM, Lemma 17] | — | — | — | Not formalized as such (proof-structure citation); s3:lemL17s is proved in full. |
| `s1:citProp18` | 1.19 | Cited result: [BM, Proposition 18] | — | — | — | Not formalized as such (proof-structure citation); s3:lemP18s (i) is proved in full. |
| `s1:citLem19` | 1.20 | Cited result: [BM, Lemma 19] | — | — | — | Not formalized as such (proof-structure citation); s3:lemP18s (ii) is proved in full. |
| `s1:citThm21` | 1.21 | Cited result: [BM, Theorem 21] (Lovász [Lov68]) | S | EG/Spec/Ext/Lovasz.lean | `LovaszStatement` → `EG.LovaszC.lovasz` (wrapper `EG.Todo.Lovasz`) | Lovász's theorem, proved in Lean (not assumed): `EG.LovaszC.lovasz` (EG/Lib/Ext/LovaszThm.lean) by Lovász's construction `EG.LovaszC.lovasz_construction` (EG/Lib/Ext/LovaszCons.lean) and strong induction on the number of edges; `EG.Todo.Lovasz` is the wrapper consumers import. |
| `s1:citCor22` | 1.22 | Cited result: [BM, Corollary 22] | S | EG/Spec/Ext/Cor22.lean | `Cor22Statement` → `EG.cor22` | Derived from Lovász's theorem as in [BM]. |
| `s1:citLem25` | 1.23 | Cited result: [BM, Lemma 25], explicit form | S | EG/Spec/Ext/BMLemma25.lean | `BMLemma25Statement` → `EG.bmLemma25` | Hypothesis `2 ≤ m` (the bound is undefined at m = 1; without it the Lean reading is false, proved as `EG.bmLemma25_literal_false`). Found during the formalization; added in v6 (`d6f3c49`) and present in v6.1 (`m ≥ max(2, 2^30/ε²)`), while the docstring of the Spec file quotes the earlier wording. The only use (s2:lemCap (ii)) has m ≥ 2^40. |
| `s1:remBMused` | 1.24 | Remark: where the results of [BM] are used | — | — | — | No mathematical content; not formalized. |
| `s1:citChernoffGen` | 1.25 | Cited result: Chernoff bounds for sums of independent indicators [JLR00, Thms 2.1, 2.8] | S | EG/Spec/Found/Chernoff.lean | `ChernoffGenStatement` → `EG.Todo.ChernoffGen`<br>`ChernoffGenMeanStatement` → `EG.Todo.ChernoffGenMean` ○<br>`ChernoffGenTailStatement` → `EG.Todo.ChernoffGenTail` ○ |  |
| `s1:citMarkov` | 1.26 | Cited result: Markov's inequality and its two uses | S | EG/Spec/Found/Markov.lean | `MarkovStatement` → `EG.Todo.Markov` ○<br>`MarkovAStatement` → `EG.Todo.MarkovA` ○<br>`MarkovBStatement` → `EG.Todo.MarkovB` ○<br>`MarkovCondStatement` → `EG.Todo.MarkovCond` ○ |  |
| `s1:lemBBD` | 1.27 | Lemma BBD: Bernstein inequality for bounded differences | S | EG/Spec/Found/BBD.lean | `BBDStatement` → `EG.bbd`<br>`BBDRVStatement` → `EG.bbdRV` |  |
| `s1:citHall` | 1.28 | Cited result: Hall's theorem [Hal35] | S | EG/Spec/Found/Hall.lean | `HallStatement` → `EG.Todo.Hall` ○ | Proved from Mathlib's Hall theorem. |
| `s1:citHaxell` | 1.29 | Cited result: Haxell's condition for matchability [Hax95] | S | EG/Spec/Ext/Haxell.lean | `HaxellStatedForm` → `EG.haxell_stated`<br>`HaxellStatement` → `EG.haxell` | Both the stated form and the q²-form used by s3:lemL9rho are proved (Haxell's alternating-tree argument as written out in s1.tex); `EG.haxellStatement_of_statedForm` relates them. |
| `s1:citEuler` | 1.30 | Cited result: T-joins and Euler circuits | S | EG/Spec/Found/EulerMulti.lean<br>EG/Spec/Found/EulerTreeTJoin.lean | `EulerMultiStatement` → `EG.eulerMulti`<br>`EulerTreeTJoinStatement` → `EG.eulerTreeTJoin` ○ | Parts (a), (b); part (c) is not used and not formalized. |
| `s1:defConstants` | 1.31 | Definition: the constants | S | EG/Defs/Constants.lean<br>EG/Defs/Gamma/Full.lean<br>EG/Defs/Quot/Constants.lean<br>EG/Defs/Main/Gamma.lean<br>EG/Spec/Gamma/N0.lean | defs: `EG.epsC`, `EG.sigmaC`, `EG.Cp`, `EG.Aexp`, `EG.N0Cond`, `EG.Quot.C0`, … (9 in all)<br>`VortexEventuallySizeStatement` → `EG.vortexEventuallySize` (wrapper `EG.Todo.VortexEventuallySize`)<br>`N0EventuallyStatement` → `EG.eventually_N0Cond` (wrapper `EG.Todo.N0Eventually`)<br>`N0ExistsStatement` → `EG.exists_N0` (wrapper `EG.Todo.N0Exists`) |  |
| `s1:remOrder` | 1.32 | Remark: order of the constants | — | — | — | No statement; realised by the quantifier structure of the Lean proof. |
| `s1:condGamma` | 1.33 | Condition: the galactic conditions Γ1–Γ4 on D_* | S | EG/Defs/Main/GammaCond.lean<br>EG/Defs/Gamma/Full.lean<br>EG/Defs/Gamma/Core.lean<br>EG/Defs/Lend/COLTable.lean<br>EG/Defs/Main/Gamma.lean<br>EG/Spec/Gamma/Cond.lean | defs: `EG.GammaCond`, `EG.Gamma1`, `EG.Gamma1core`, `EG.Gamma1Items`, `EG.COLTable.col3`, `EG.Gamma4`, … (14 in all)<br>`Gamma1dOfABStatement` → `EG.Todo.Gamma1dOfAB` ○<br>`Gamma1UpwardStatement` → `EG.Todo.Gamma1Upward` ○<br>`Gamma1LogbStatement` → `EG.Todo.Gamma1Logb` ○<br>`Gamma1TransferStatement` → `EG.Todo.Gamma1Transfer` ○<br>`Gamma2aOfGamma1Statement` → `EG.Todo.Gamma2aOfGamma1` ○ | Γ2(b),(c) are consequences, not conditions; Γ2(a) is derived from Γ1 (`Gamma2aOfGamma1Statement`). |
| `s1:remNotUsed` | 1.34 | Remark: not used on this route | — | — | — | No content (exclusion list). |

### 3.2 Manuscript Section 2 (`s2.tex`): the hierarchy HB*^{τ+}

| Label | No. (v6.1) | Result | F | Lean files | Lean statement → proof | Notes |
|---|---|---|---|---|---|---|
| `s2:defWitness` | 2.1 | Definition: witness and its minimal part | S | EG/Defs/HB/Witness.lean<br>EG/Spec/HB/TauRules.lean | defs: `EG.HB.IsWitness`, `EG.HB.witN`, `EG.HB.witF0`<br>`WitnessExistsStatement` → `EG.witnessExists` ○<br>`WitnessFactStatement` → `EG.witnessFact` ○ |  |
| `s2:defTauRules` | 2.2 | Definition: the τ-rules and the split | S | EG/Defs/HB/Witness.lean<br>EG/Spec/HB/TauRules.lean | defs: `EG.HB.tauHout`, `EG.HB.tauU1`, `EG.HB.tauN1`, `EG.HB.tauF1`, `EG.HB.tauHin`, `EG.HB.tauN2`, … (9 in all)<br>`TauEqSplitStatement` → `EG.tauEqSplit` ○<br>`TauFactAStatement` → `EG.tauFactA` ○<br>`TauFactBStatement` → `EG.tauFactB` ○<br>`TauFactCStatement` → `EG.tauFactC` ○ |  |
| `s2:lemSEP` | 2.3 | Lemma SEP | S | EG/Defs/HB/SplitTree.lean<br>EG/Defs/HB/Witness.lean<br>EG/Spec/HB/SEP.lean | defs: `EG.HB.STree`, `EG.HB.STree.leafAddrs`, `EG.HB.STree.graphAtD`, `EG.HB.STree.delAt`, `EG.HB.STree.WF`, `EG.HB.STree.leafMass`, … (11 in all)<br>`SEP0Statement` → `EG.sep0` ○<br>`SEPMonoStatement` → `EG.sepMono` ○<br>`SEPiStatement` → `EG.sepI` ○<br>`SEPiiStatement` → `EG.sepII` ○<br>`SEPiiiStatement` → `EG.sepIII` ○ |  |
| `s2:lemThinCut` | 2.4 | Lemma: thin cut | S | EG/Spec/HB/ThinCut.lean | `ThinCutStatement` → `EG.thinCut`<br>`ThinCutEdgeStatement` → `EG.thinCutEdge` |  |
| `s2:lemOVgeneric` | 2.5 | Lemma: generic overlap bound, Lemma OV | S | EG/Spec/Num/OV.lean<br>EG/Spec/HB/Overlap.lean | `NumOVChargeSumStatement` → `EG.numOVChargeSum` ○<br>`NumOVLogFourThirdsStatement` → `EG.numOVLogFourThirds` ○<br>`NumOVConstStatement` → `EG.numOVConst` ○<br>`NumOVRearrangeStatement` → `EG.numOVRearrange` ○<br>`NumOVInstanceStatement` → `EG.numOVInstance` ○<br>`OVStatement` → `EG.ov`<br>`OVInstanceStatement` → `EG.ovInstance` |  |
| `s2:lem14tau` | 2.6 | Lemma 14^τ | S | EG/Spec/Num/OV.lean<br>EG/Spec/HB/Lemma14Tau.lean | `NumLem14tauConstStatement` → `EG.numLem14tauConst` ○<br>`L14SplitStatement` → `EG.l14Split`<br>`L14TermStatement` → `EG.l14Term`<br>`L14GlobalStatement` → `EG.l14Global`<br>`L14OVStatement` → `EG.l14OV`<br>`L14ThinStatement` → `EG.l14Thin` | Repair T1 `L14-C-TAU0`: the two bounds of (c) carry the added hypothesis 0 < τ (false as stated at n₀ = 1, τ = 0; `EGTest.ProbeP3A.lem14tau_c_literal_false`). Holds in every application. Manuscript v6.2 adds `τ > 0` to the bound of (c). |
| `s2:defHBtp` | 2.7 | Definition: the hierarchy HB*^{τ+} | S | EG/Defs/HB/SplitTree.lean<br>EG/Defs/HB/Run.lean<br>EG/Defs/HB/Round.lean<br>EG/Spec/HB/HBtpFacts.lean | defs: `EG.HB.STree.graft`, `EG.HB.STree.StopsAt`, `EG.HB.Run`, `EG.HB.Run.R`, `EG.HB.Run.graph`, `EG.HB.Run.d`, … (78 in all)<br>`HBMCeilStatement` → `EG.Todo.HBMCeil` ○<br>`HBTwoLevelStatement` → `EG.Todo.HBTwoLevel`<br>`HBStdStatement` → `EG.Todo.HBStd` ○<br>`HBStep1Statement` → `EG.Todo.HBStep1` | Run model (`EG.HB.Run`, rounds, validity); the facts recorded in the definition are the statements shown. |
| `s2:defAncestors` | 2.8 | Definition: ancestors, typing, multiplicities | S | EG/Defs/Quot/Round.lean<br>EG/Defs/HB/Run.lean<br>EG/Defs/HB/Round.lean<br>EG/Spec/HB/HBtpFacts.lean | defs: `EG.Quot.RoundInput.multAt`, `EG.HB.Run.mu`, `EG.HB.Run.ancestors`, `EG.HB.Run.ancVerts`, `EG.HB.Run.ancGraph`, `EG.HB.Run.ancEps`, … (20 in all)<br>`AncestorFactsStatement` → `EG.Todo.AncestorFacts` ○ |  |
| `s2:lemCap` | 2.9 | Lemma: Lemma-25 size cap | S | EG/Spec/HB/CapPrePart.lean<br>EG/Spec/HB/Cap.lean<br>EG/Spec/HB/CapRound.lean | `CapPrePartStatement` → `EG.capPrePart`<br>`CapStatement` → `EG.cap`<br>`CapUniformStatement` → `EG.cap_uniform`<br>`CapGraphStatement` → `EG.cap_graph`<br>`CapRoundStatement` → `EG.Todo.CapRound`<br>`CapRunTauStatement` → `EG.Todo.CapRunTau` ○ |  |
| `s2:lemHS` | 2.10 | Lemma HS | S | EG/Spec/HB/HS.lean | `HSStatement` → `EG.Todo.HS` ○<br>`HSCorStatement` → `EG.Todo.HSCor` |  |
| `s2:propStructure` | 2.11 | Proposition: structure of a valid run | S | EG/Spec/HB/Structure.lean<br>EG/Spec/HB/StructureHY.lean<br>EG/Spec/HB/StructureLight.lean | `StructureExpStatement` → `EG.Todo.StructureExp`<br>`StructurePartitionStatement` → `EG.Todo.StructurePartition`<br>`StructureVertexStatement` → `EG.structureVertex`<br>`StructureHYStatement` → `EG.structureHY`<br>`StructureLightStatement` → `EG.structureLight` |  |
| `s2:lemEL` | 2.12 | Lemma: edge laminarity, EL | S | EG/Spec/HB/EL.lean | `ELStatement` → `EG.edgeLaminarity` |  |
| `s2:propOV` | 2.13 | Proposition: overlap constants on HB*^{τ+}; (K1)–(K3), (F11) | S | EG/Spec/Num/OV.lean<br>EG/Spec/HB/OVRun.lean<br>EG/Spec/HB/OVRunK.lean | `NumPropOVConstStatement` → `EG.numPropOVConst` ○<br>`OVRoundStatement` → `EG.Todo.OVRound`<br>`OVRunStatement` → `EG.Todo.OVRun`<br>`OVK1Statement` → `EG.ovK1`<br>`OVK3Statement` → `EG.ovK3` |  |
| `s2:propDegRec` | 2.14 | Proposition: degree recursion | S | EG/Spec/HB/DegRec.lean | `DegRecRoundStatement` → `EG.Todo.DegRecRound`<br>`DegRecKindsRoundStatement` → `EG.Todo.DegRecKindsRound`<br>`DegRecStatement` → `EG.Todo.DegRec`<br>`DegRecKindsStatement` → `EG.Todo.DegRecKinds` ○ |  |
| `s2:propExists` | 2.15 | Proposition: existence and termination | S | EG/Spec/HB/Exists.lean | `RoundStepsStatement` → `EG.Todo.RoundSteps` ○<br>`RoundTauTermStatement` → `EG.Todo.RoundTauTerm`<br>`RoundExistsStatement` → `EG.Todo.RoundExists`<br>`RunTerminatesStatement` → `EG.Todo.RunTerminates` ○<br>`ExistsRunStatement` → `EG.Todo.ExistsRun` | The Γ-hypotheses are explicit: `RunTerminatesStatement`/`ExistsRunStatement` assume `Gamma1core D_*`, `RoundTauTerm`/`RoundExists` assume Γ2(a) (the statement is false without a condition on D_*). |
| `s2:lemLacunary` | 2.16 | Lemma: tower-lacunary sums | S | EG/Spec/HB/LacunaryGeom.lean<br>EG/Spec/HB/Lacunary.lean | `LacunaryGeomStatement` → `EG.HB.lacGeom` (also `EG.lacunaryGeom`)<br>`LacunaryMonoStatement` → `EG.Todo.LacunaryMono` ○<br>`LacunaryIIStatement` → `EG.Todo.LacunaryII` ○<br>`LacunarySeqStatement` → `EG.Todo.LacunarySeq` ○<br>`LacunaryRunStatement` → `EG.Todo.LacunaryRun`<br>`LacunaryExamplesStatement` → `EG.Todo.LacunaryExamples`<br>`LacunaryStatement` → `EG.Todo.Lacunary` ○ |  |
| `s2:lemTower` | 2.17 | Lemma: tower facts | S | EG/Defs/HB/Run.lean<br>EG/Spec/HB/TowerA.lean<br>EG/Spec/HB/TowerB.lean<br>EG/Spec/HB/TowerC.lean<br>EG/Spec/HB/TowerBLate.lean<br>EG/Spec/HB/Tower.lean<br>EG/Spec/HB/TowerBM.lean | defs: `EG.HB.epsA`, `EG.HB.psiPool`<br>`TowerAStatement` → `EG.towerA`<br>`TowerBRoundStatement` → `EG.towerBRound`<br>`TowerCStatement` → `EG.towerC`<br>`TowerBLateStatement` → `EG.towerBLate`<br>`TowerBRestStatement` → `EG.Todo.TowerBRest`<br>`TowerDStatement` → `EG.Todo.TowerD`<br>`TowerEStatement` → `EG.Todo.TowerE`<br>`TowerStatement` → `EG.Todo.Tower` ○<br>`TowerBMStatement` → `EG.towerBM` |  |
| `s2:lemGC` | 2.18 | Lemma: rule GC | S | EG/Spec/HB/GC.lean | `GCDefStatement` → `EG.gcDef` ○<br>`GCStatement` → `EG.gc` ○<br>`GCThetaStatement` → `EG.gcTheta` ○ |  |
| `s2:propOrigin` | 2.19 | Proposition: ORIGIN^τ | S | EG/Spec/HB/Origin.lean | `OriginTypesStatement` → `EG.originTypes`<br>`OriginThinStatement` → `EG.originThin`<br>`OriginGuestCapStatement` → `EG.originGuestCap` |  |
| `s2:propParentless` | 2.20 | Proposition: fresh and parentless mass | S | EG/Spec/HB/Parentless.lean | `FreshStatement` → `EG.Todo.Fresh`<br>`AdmissibleParentStatement` → `EG.Todo.AdmissibleParent` ○<br>`ParentlessCountStatement` → `EG.Todo.ParentlessCount` |  |
| `s2:remTauConstants` | 2.21 | Remark: constants of HB*^{τ+} versus plain HB* | — | — | — | No mathematical content used downstream; not formalized. |

### 3.3 Manuscript Section 3 (`s3.tex`): linking through random sets; stage-1 lending data

| Label | No. (v6.1) | Result | F | Lean files | Lean statement → proof | Notes |
|---|---|---|---|---|---|---|
| `s3:lemMonotone` | 3.1 | Lemma: monotonicity and the for-all property | S | EG/Spec/Link/Monotone.lean | `MonotoneStatement` → `EG.Todo.Monotone` ○ |  |
| `s3:lemL15p` | 3.2 | Lemma 15⁺: random splitting without loss | S | EG/Spec/Link/L15.lean | `L15pStatement` → `EG.l15p` |  |
| `s3:remMultiset` | 3.3 | Remark: multisets | S | EG/Spec/Link/Multiset.lean | `MultisetCountStatement` → `EG.Todo.MultisetCount` | The multiset reading is definitional in `EG.FGraph.IsPathConnected` (indexed families); the counting step is the statement shown. |
| `s3:eqStar` | (3.2) | Equations: local parameters of Theorem 16* and facts (S1)–(S6) | S | EG/Spec/Link/Star.lean<br>EG/Spec/Num/StarInputs.lean | `StarS1Statement` → `EG.Todo.StarS1` ○<br>`StarS2PStatement` → `EG.Todo.StarS2P` ○<br>`StarUnionLawStatement` → `EG.Todo.StarUnionLaw`<br>`StarS4Statement` → `EG.Todo.StarS4`<br>`StarS5Statement` → `EG.Todo.StarS5`<br>`StarS6Statement` → `EG.Todo.StarS6`<br>`StarP13sParamsStatement` → `EG.Todo.StarP13sParams`<br>`StarS2NumStatement` → `EG.starS2Num`<br>`StarS3Statement` → `EG.starS3`<br>`NumStarS3MarginStatement` → `EG.numStarS3Margin` |  |
| `s3:propP13s` | 3.4 | Proposition 13*: stars or bipartite | S | EG/Spec/Link/P13s.lean | `P13sStatement` → `EG.Todo.P13s` |  |
| `s3:lemL17s` | 3.5 | Lemma 17*: sprinkling at density ρ | S | EG/Spec/Link/L17s.lean<br>EG/Spec/Num/L17s.lean | `L17sStatement` → `EG.Todo.L17s`<br>`NumL17sStep0Statement` → `EG.numL17sStep0`<br>`NumL17sCaseAConstStatement` → `EG.numL17sCaseAConst`<br>`NumL17sCaseASigmaStatement` → `EG.numL17sCaseASigma`<br>`NumL17sCaseAExponentStatement` → `EG.numL17sCaseAExponent`<br>`NumL17sBernsteinMarginStatement` → `EG.numL17sBernsteinMargin`<br>`NumL17sBernsteinExponentStatement` → `EG.numL17sBernsteinExponent`<br>`NumL17sCaseBMeanStatement` → `EG.numL17sCaseBMean`<br>`NumL17sCaseBGrowthStatement` → `EG.numL17sCaseBGrowth`<br>`NumL17sCaseBSmallPConstStatement` → `EG.numL17sCaseBSmallPConst`<br>`NumL17sCaseBLargePConstStatement` → `EG.numL17sCaseBLargePConst`<br>`NumL17sCaseBExponentStatement` → `EG.numL17sCaseBExponent`<br>`NumL17sStep3Statement` → `EG.numL17sStep3`<br>`NumL17sStep4Statement` → `EG.numL17sStep4`<br>`NumL17sStep5Statement` → `EG.numL17sStep5` |  |
| `s3:lemP18s` | 3.6 | Lemma: Proposition 18* and Lemma 19* | S | EG/Spec/Link/P18s.lean | `P18sStatement` → `EG.Todo.P18s` |  |
| `s3:lemL9rho` | 3.7 | Lemma 9_ρ: multiset linking from ball expansion | S | EG/Spec/Link/L9rho.lean | `L9rhoStatement` → `EG.Todo.L9rho` |  |
| `s3:thmT16s` | 3.8 | Theorem 16*: linking through random sets; for-all multiset form | S | EG/Spec/Link/T16s.lean<br>EG/Spec/Link/T16sForced.lean | `T16sStatement` → `EG.t16s`<br>`T16sForcedStatement` → `EG.Todo.T16sForced` |  |
| `s3:lemHB` | 3.9 | Lemma HB: candidate sets of bounded multiplicity | S | EG/Spec/Link/HB.lean | `HBStatement` → `EG.Todo.HB` |  |
| `s3:defCOL` | 3.10 | Definition: stage-1 lending data: the two-stage colouring COL-JV and the JS labels | D | EG/Defs/Stage1/COL.lean<br>EG/Defs/Stage1/Law.lean<br>EG/Defs/Chain/Lending.lean<br>EG/Defs/Prob/FinDist.lean | defs: `EG.Stage1.LentTag`, `EG.Stage1.lateRounds`, `EG.Stage1.KJS`, `EG.Stage1.rhoJS`, `EG.Stage1.tJS`, `EG.Stage1.Tslot`, … (42 in all) |  |
| `s3:tabCOLJV` | Table 6 | Table: the COL-JV table | D | EG/Defs/Lend/COLTable.lean | defs: `EG.COLTable.lam`, `EG.COLTable.Mbar`, `EG.COLTable.kbar`, `EG.COLTable.row`, `EG.COLTable.triple` | Table only; its rows are the `COLJVRow*` statements of s3:lemCOLJV. |
| `s3:lemCOLJV` | 3.11 | Lemma: the COL-JV table (lemma) | S | EG/Spec/Lend/COLJVRows.lean<br>EG/Spec/Lend/COLJV.lean<br>EG/Spec/Lend/COLJVCount.lean | `COLJVRow4Statement` → `EG.colJVRow4`<br>`COLJVRow7Statement` → `EG.colJVRow7`<br>`COLJVRow8Statement` → `EG.colJVRow8`<br>`COLJVCol3Statement` → `EG.Todo.COLJVCol3` ○<br>`COLJVRow1Statement` → `EG.Todo.COLJVRow1` ○<br>`COLJVRow2Statement` → `EG.Todo.COLJVRow2` ○<br>`COLJVRow3Statement` → `EG.Todo.COLJVRow3`<br>`COLJVRow5Statement` → `EG.Todo.COLJVRow5`<br>`COLJVRow6Statement` → `EG.Todo.COLJVRow6`<br>`COLJVRow9Statement` → `EG.Todo.COLJVRow9`<br>`COLJVRow11Statement` → `EG.Todo.COLJVRow11` ○<br>`COLJVRow12Statement` → `EG.Todo.COLJVRow12` ○<br>`COLJVRow13Statement` → `EG.Todo.COLJVRow13` ○<br>`COLJVStatement` → `EG.Todo.COLJV` ○<br>`COLJVCountStatement` → `EG.colJVCount` |  |
| `s3:lemCOLJVev` | 3.12 | Lemma: eventual form of the COL-JV table | S | EG/Spec/Lend/COLJVev.lean<br>EG/Spec/Gamma/Sat.lean | `COLJVevTypeEStatement` → `EG.Todo.COLJVevTypeE` ○<br>`COLJVevRowsStatement` → `EG.Todo.COLJVevRows` ○<br>`COLJVevEventuallyRowStatement` → `EG.Todo.COLJVevEventuallyRow` ○<br>`COLJVevStatement` → `EG.Todo.COLJVev` ○<br>`Col3EventuallyStatement` → `EG.col3_eventually` (wrapper `EG.Todo.Col3Eventually`) |  |
| `s3:lemCOL` | 3.13 | Lemma COL | S | EG/Spec/Stage1/COL.lean<br>EG/Spec/Stage1/COLc.lean<br>EG/Spec/Stage1/COLa.lean | `COLStatement` → `EG.Todo.COL`<br>`COLLemmaStatement` → `EG.Todo.COLLemma` ○<br>`COLcIndexStatement` → `EG.colcIndex`<br>`COLcStatement` → `EG.colc`<br>`COLaProbStatement` → `EG.colaProb` |  |

### 3.4 Manuscript Section 4 (`s4.tex`): vortices (TPV, PV, VX⁺)

| Label | No. (v6.1) | Result | F | Lean files | Lean statement → proof | Notes |
|---|---|---|---|---|---|---|
| `s4:convVortex` | 4.1 | Convention: vortex-local notation | S | EG/Defs/Vortex.lean<br>EG/Spec/Vortex/Observations.lean | defs: `EG.Vortex.L`<br>`TrailSplitStatement` → `EG.trailSplit` ○<br>`TrailRepInnerStatement` → `EG.trailRepInner` ○<br>`PathEndsParityStatement` → `EG.pathEndsParity` ○<br>`PathEndsCountStatement` → `EG.pathEndsCount` ○<br>`ClosingStatement` → `EG.closing` ○ | The five elementary observations of §4.1 ((S) trail splitting, (E) path ends, (C) closing) are the statements shown. |
| `s4:lemTPV` | 4.2 | Lemma TPV (transparent P-vortex) | S | EG/Spec/Vortex/TPV.lean | `TPVStatement` → `EG.Todo.TPV` | Deterministic form (the conclusion does not mention the labels); see the module docstring. |
| `s4:lemPV` | 4.3 | Lemma PV (the four-phase P-vortex) | S | EG/Spec/Vortex/PV.lean<br>EG/Spec/Vortex/PVCore.lean | `PVStatement` → `EG.pvLemma`<br>`PVStepPhaseStatement` → `EG.pvStepPhase`<br>`PVStepCostStatement` → `EG.pvStepCost`<br>`PVtStatement` → `EG.pvT`<br>`PVStripStatement` → `EG.pvStrip`<br>`PVFinishStatement` → `EG.pvFinish`<br>`PVArcEndsDegStatement` → `EG.pvArcEndsDeg` | Deterministic form; the step equations s4:eqPVt, s4:eqPVstep are separate statements. |
| `s4:thmVXp` | 4.4 | Theorem VX⁺ (sharpened vortex absorption with arbitrary extra edges) | S | EG/Spec/Vortex/VX.lean | `VXStatement` → `EG.Todo.VX` | Deterministic form. |
| `s4:remTPVVX` | 4.5 | Remark: Lemma TPV as a vortex-absorption statement; not used | — | — | — | Not used by the main argument (as the manuscript says); not formalized. |

### 3.5 Manuscript Section 5 (`s5.tex`): light parts

| Label | No. (v6.1) | Result | F | Lean files | Lean statement → proof | Notes |
|---|---|---|---|---|---|---|
| `s5:defZones` | 5.1 | Definition: vertex choice, sublabels and zones; stage 1b | S | EG/Defs/Stage1/Zones.lean<br>EG/Spec/Light/Setting.lean | defs: `EG.Stage1.ZIdx`, `EG.Stage1.zp`, `EG.Stage1.availParts`, `EG.Stage1.zpSum`, `EG.Stage1.zoneWeight`, `EG.Stage1.zoneLabelLaw`, … (9 in all)<br>`EqLYStatement` → `EG.eqLY`<br>`EqZpStatement` → `EG.Todo.EqZp` |  |
| `s5:lemZones` | 5.2 | Lemma: zones | S | EG/Spec/Light/Zones.lean | `LemZonesStatement` → `EG.lemZones` |  |
| `s5:defStages` | 5.3 | Definition: stage-2 statuses of light parts | S | EG/Defs/Light/Stages.lean<br>EG/Spec/Light/Stages.lean | defs: `EG.Light.vm`, `EG.Light.vb`, `EG.Light.AY`, `EG.Light.E1`, `EG.Light.demoted`, `EG.Light.parentBad`, … (14 in all)<br>`StagesHBStatement` → `EG.stagesHB`<br>`EqPlStatement` → `EG.Todo.EqPl` |  |
| `s5:lemE1` | 5.4 | Lemma: bad probabilities | S | EG/Spec/Light/E1.lean<br>EG/Spec/Light/ParentRun.lean | `LemE1Statement` → `EG.Todo.LemE1`<br>`ParentBadProbStatement` → `EG.parentBadProb` |  |
| `s5:lemExpect` | 5.5 | Lemma: expected demotion and lost-parent mass | S | EG/Defs/Light/Constants.lean<br>EG/Spec/Light/Expect.lean | defs: `EG.Light.epsU`<br>`LemExpectStatement` → `EG.Todo.LemExpect`<br>`LemExpectLimitStatement` → `EG.Todo.LemExpectLimit` ○ |  |
| `s5:lemChild` | 5.6 | Lemma: child side | S | EG/Spec/Light/Child.lean | `LemChildStatement` → `EG.lemChild` |  |
| `s5:lemParent` | 5.7 | Lemma: parent side: multi-parent chaining over U-bundles | S | EG/Spec/Light/Parent.lean<br>EG/Spec/Light/ParentRun.lean<br>EG/Spec/Light/ParentSteps.lean | `LemParentStatement` → `EG.lemParent` (wrapper `EG.Todo.LemParent`)<br>`LemParentSumStatement` → `EG.lemParentSum`<br>`LemParentAvailDisjointStatement` → `EG.lemParentAvailDisjoint`<br>`LemParentLimitStatement` → `EG.Todo.LemParentLimit` ○<br>`BundleEndCountStatement` → `EG.bundleEndCount`<br>`MlTyStatement` → `EG.mlTy`<br>`EtaHalvingStatement` → `EG.etaHalving`<br>`ArcClassEulerStatement` → `EG.arcClassEuler` (wrapper `EG.Todo.ArcClassEuler`)<br>`TransitionClaimStatement` → `EG.transitionClaim`<br>`VisitCapStatement` → `EG.visitCap` (wrapper `EG.Todo.VisitCap`)<br>`TransitionCountStatement` → `EG.transitionCount`<br>`ConnectorCycleStatement` → `EG.connectorCycle` |  |
| `s5:lemDemoted` | 5.8 | Lemma: fallback for demoted light parts | S | EG/Spec/Light/Demoted.lean | `LemDemotedStatement` → `EG.Todo.LemDemoted` |  |
| `s5:lemKRED` | 5.9 | Lemma K-RED | S | EG/Defs/Probe/S5/KRED.lean<br>EG/Defs/Chain/Constants.lean<br>EG/Spec/Light/KRED.lean | defs: `EG.Light.Kstd`, `EG.Light.lentJSJV`, `EG.Light.LentExtHyp`, `EG.Chain.epsK`<br>`LemKREDStatement` → `EG.Todo.LemKRED` |  |
| `s5:remConstants` | 5.10 | Remark: the constants 369 and 745 | — | — | — | No Spec: (a) is internal to s4:lemPV (its Spec states 369); (b) is numeric; (c) is commentary. |

### 3.6 Manuscript Section 6 (`s6.tex`): chaining and the assembly MIX-C

| Label | No. (v6.1) | Result | F | Lean files | Lean statement → proof | Notes |
|---|---|---|---|---|---|---|
| `s6:lemGATE` | 6.1 | Lemma GATE, forward direction | S | EG/Spec/Chain/Gate.lean | `GateStatement` → `EG.gate`<br>`GatePreciseStatement` → `EG.gate_precise` |  |
| `s6:defCluster` | 6.2 | Definition: clusters | D | EG/Defs/Chain/Cluster.lean | defs: `EG.Chain.Cluster`, `EG.Chain.exc`, `EG.Chain.excPos`, `EG.Chain.excNeg`, `EG.Chain.Cluster.verts`, `EG.Chain.Cluster.portBeads`, … (14 in all) |  |
| `s6:lemMED` | 6.3 | Lemma MED | S | EG/Spec/Chain/MED.lean | `MedStatement` → `EG.med` ○<br>`MedExcStatement` → `EG.medExc` ○ |  |
| `s6:lemEQLPT` | 6.4 | Lemma EQ-LPT | S | EG/Spec/Chain/EqLpt.lean | `EqLptExistsStatement` → `EG.eqLptExists` ○<br>`EqLptStatement` → `EG.eqLpt` ○ |  |
| `s6:lemPAR` | 6.5 | Lemma PAR, port–port parity | S | EG/Spec/Chain/PAR.lean | `ParExistsStatement` → `EG.parExists`<br>`ParStatement` → `EG.par` | 'Bipartite with sides V_a, V_b' is encoded with an explicit `Disjoint Va Vb` (T0, TRIAGE PAR-SIDES-DISJOINT). A Lean reading without it would be false. |
| `s6:lemHCCP` | 6.6 | Lemma HCC-P, layered hub-cluster chaining with path junctions | S | EG/Spec/Chain/HCCP.lean | `HccpStatement` → `EG.hccp` |  |
| `s6:lemHCCglob` | 6.7 | Lemma: union of systems | S | EG/Spec/Chain/HCCP.lean | `HccUnionStatement` → `EG.hccUnion` ○<br>`HccGlobStatement` → `EG.hccGlob` ○ |  |
| `s6:defDesign` | 6.8 | Definition: designation and class data; 𝒱 = ∅ | D | EG/Defs/Chain/Design.lean | defs: `EG.Chain.IsDesignation`, `EG.Chain.classedPorts`, `EG.Chain.classDeg`, `EG.Chain.mY`, `EG.Chain.dStar`, `EG.Chain.alphaY`, … (13 in all) |  |
| `s6:thmCONC` | 6.9 | Theorem CONC, standalone ancestors | S | EG/Spec/Chain/CONC.lean<br>EG/Spec/Chain/ConcTower.lean | `ConcIStatement` → `EG.concI`<br>`ConcIIStatement` → `EG.concII`<br>`ConcIIIStatement` → `EG.concIII`<br>`ConcTauSumStatement` → `EG.concTauSum`<br>`ConcDStarSumStatement` → `EG.concDStarSum`<br>`LogStarFactsStatement` → `EG.logStarFacts`<br>`KStarStatement` → `EG.kStar`<br>`TowerHalfStatement` → `EG.towerHalf`<br>`TowerEndStatement` → `EG.towerEnd` |  |
| `s6:thmCONCL` | 6.10 | Theorem CONC-L (hub concentration) | S | EG/Defs/Chain/Constants.lean<br>EG/Spec/Chain/CONCL.lean | defs: `EG.Chain.epsCONC`<br>`ConcLIStatement` → `EG.concLI`<br>`ConcLIIStatement` → `EG.concLII`<br>`ConcLIIIStatement` → `EG.concLIII`<br>`ConcLAlphaStatement` → `EG.concLAlpha`<br>`ConcLPerAncestorStatement` → `EG.concLPerAncestor`<br>`ConcLGCSumStatement` → `EG.concLGCSum`<br>`ConcLSumStatement` → `EG.concLSum`<br>`EpsCONCTendstoStatement` → `EG.epsCONC_tendsto` ○ |  |
| `s6:defLending` | 6.11 | Definition: stage-2 lending statuses, retirement sets and the functional X_U | D | EG/Defs/Probe/S7b/Outcome.lean<br>EG/Defs/Chain/StageInst.lean<br>EG/Defs/Chain/Lending.lean | defs: `EG.Quot.stageOf`, `EG.Quot.XUOf`, `EG.Chain.StageData.ofOutcome`, `EG.Chain.lendBad`, `EG.Chain.lendGoodAnc`, `EG.Chain.lost`, … (11 in all) |  |
| `s6:lemLost` | 6.12 | Lemma: lost ports; the constant (K6) | S | EG/Spec/Chain/Lost.lean | `LostStatement` → `EG.Todo.Lost` |  |
| `s6:lemJSLC` | 6.13 | Lemma JS-LC (one round l ≥ 3; cherry split for giant pairs) | S | EG/Spec/Chain/JSLCSteps.lean<br>EG/Spec/Chain/JSLC.lean<br>EG/Spec/Chain/EngineMult.lean<br>EG/Spec/Chain/JSLCRouting.lean | `JslcTypesStatement` → `EG.jslcTypes`<br>`JslcStep2Statement` → `EG.jslcStep2`<br>`JslcStep7DisjStatement` → `EG.jslcStep7Disj`<br>`JSLCStatement` → `EG.jslc`<br>`HccpEndMultStatement` → `EG.hccpEndMult` ○<br>`JsMultNumStatement` → `EG.jsMultNum` ○<br>`JslcPairsBalanceStatement` → `EG.jslcPairsBalance`<br>`JslcPairsDistinctStatement` → `EG.jslcPairsDistinct`<br>`JslcJointMultStatement` → `EG.jslcJointMult`<br>`JslcRoutingStatement` → `EG.jslcRouting` |  |
| `s6:remStar` | 6.14 | Remark: the star split is not used | — | — | — | Nothing to formalize (the star split is not used). |
| `s6:lemJplus` | 6.15 | Lemma J⁺: the J-interface | S | EG/Defs/Quot/Round.lean<br>EG/Defs/Chain/Lending.lean<br>EG/Defs/Chain/JSet.lean<br>EG/Spec/Chain/JPlus.lean<br>EG/Spec/Chain/JPlusV.lean | defs: `EG.Quot.RoundInput.Valid`, `EG.Chain.freshCentres`, `EG.Chain.qsRound`, `EG.Chain.IsJparEdge`, `EG.Chain.IsJhubEdge`, `EG.Chain.IsJfrEdge`, … (12 in all)<br>`JplusFactsStatement` → `EG.jplusFacts` ○<br>`JplusVStatement` → `EG.Todo.JplusV` ○ | The J-interface is a conjunct of `JSLCStatement` (structure in EG/Defs/Chain/JSet.lean); the run-level facts are the statements shown. |
| `s6:defJconsumer` | 6.16 | Definition: round-l J-consumer | D | EG/Defs/Chain/JConsumer.lean | defs: `EG.Chain.JC1`, `EG.Chain.JC2`, `EG.Chain.JC3`, `EG.Chain.JConsumer` |  |
| `s6:consOrder` | 6.17 | Construction: the processing order R, R−1, …, 1, and the Lent sets | P | — | — | Proof-internal: the standalone chain `EG.Chain.MixCA.chain_exists` (EG/Lib/Chain/MixCRound.lean, descending induction on the rounds), used by `EG.Chain.MixCA.mixc_of_specs`. |
| `s6:lemLent` | 6.18 | Lemma: Lent sets | P | — | — | Proof-internal lemmas of the MIX-C proof (e.g. `EG.Chain.MixCA.lent_subset_goodLent`, `EG.Chain.MixCA.mem_goodLent`, EG/Lib/Chain/MixCRound.lean); no Spec. |
| `s6:thmMIXC` | 6.19 | Theorem MIX-C: the assembly with 𝒱 = ∅, deterministic form | S | EG/Spec/Chain/MixC.lean | `MixCStatement` → `EG.Todo.MixC`<br>`MixCConcStatement` → `EG.Todo.MixCConc`<br>`MixCTPVApplicableStatement` → `EG.Todo.MixCTPVApplicable` | Proved via `EG.Chain.MixCA.mixc_of_specs` (EG/Lib/Chain/MixCAssembly.lean). |

### 3.7 Manuscript Section 7 (`s7.tex`): quotients, HI″ and the proof of the Main Theorem

| Label | No. (v6.1) | Result | F | Lean files | Lean statement → proof | Notes |
|---|---|---|---|---|---|---|
| `s7:defPool` | 7.1 | Definition: Round-split pool labels | S | EG/Defs/Stage1/Pool.lean<br>EG/Spec/Stage1/Pool.lean | defs: `EG.Stage1.poolIdx`, `EG.Stage1.qPool`, `EG.Stage1.piPool`, `EG.Stage1.poolMass`, `EG.Stage1.plabWeight`, `EG.Stage1.poolLabelLaw`, … (10 in all)<br>`PoolLawStatement` → `EG.Todo.PoolLaw` ○ |  |
| `s7:defCand` | 7.2 | Definition: Candidates and JV-bad ports | S | EG/Defs/Quot/Cand.lean<br>EG/Defs/Quot/Round.lean<br>EG/Spec/Quot/CandDef.lean | defs: `EG.Quot.HcdOf`, `EG.Quot.Hcd`, `EG.Quot.cand`, `EG.Quot.candMean`, `EG.Quot.JVBad`, `EG.Quot.RoundInput.Hcd`, … (7 in all)<br>`CandSubsetStatement` → `EG.Todo.CandSubset` ○ |  |
| `s7:lemCand` | 7.3 | Lemma: Candidate counts | S | EG/Spec/Quot/Cand.lean | `CandCountStatement` → `EG.Todo.CandCount` |  |
| `s7:defSchedule` | 7.4 | Definition: The randomness schedule | D | EG/Defs/Quot/Schedule.lean<br>EG/Defs/Stage1/Law.lean | defs: `EG.Quot.Xi`, `EG.Quot.subset3Law`, `EG.Quot.listsLaw`, `EG.Quot.ordersLaw`, `EG.Quot.roundLaw`, `EG.Stage1.Outcome`, … (7 in all) | Definitions of the probability spaces (finite distributions `EG.FinDist`). |
| `s7:consRound` | 7.5 | Construction: the JV⁺* round step at round l ≥ 3; the J-consumer | S | EG/Defs/Quot/Schedule.lean<br>EG/Defs/Quot/Cand.lean<br>EG/Defs/Quot/Round.lean<br>EG/Defs/Probe/S7b/Outcome.lean<br>EG/Spec/Quot/RoundStep.lean<br>EG/Spec/Quot/Lift.lean | defs: `EG.Quot.inOrder`, `EG.Quot.thultOf`, `EG.Quot.thult`, `EG.Quot.RoundInput`, `EG.Quot.RoundInput.J`, `EG.Quot.RoundInput.thult`, … (55 in all)<br>`RoundRulesExistStatement` → `EG.Todo.RoundRulesExist` ○<br>`RoundListsLawStatement` → `EG.Todo.RoundListsLaw` ○<br>`RoundInjectionStatement` → `EG.Todo.RoundInjection` ○<br>`RoundMarkovStatement` → `EG.Todo.RoundMarkov` ○<br>aux. defs: `layerSubLayer`, `juncEnds` |  |
| `s7:lemWellDef` | 7.6 | Lemma: The round step is well defined | S | EG/Spec/Quot/WellDef.lean<br>EG/Spec/Num/WellDef.lean | `WellDefParStatement` → `EG.wellDefPar` ○<br>`WellDefListsStatement` → `EG.wellDefLists` ○<br>`CuckooSDRStatement` → `EG.cuckooSDR` ○<br>`WellDefE1Statement` → `EG.wellDefE1` ○<br>`WellDefE2Statement` → `EG.wellDefE2` ○<br>`NumWellDefSDRSeriesStatement` → `EG.numWellDefSDRSeries`<br>`NumWellDefSDRUseStatement` → `EG.numWellDefSDRUse`<br>`NumWellDefSDRRatioStatement` → `EG.numWellDefSDRRatio`<br>`NumWellDefSDRConstStatement` → `EG.numWellDefSDRConst`<br>aux. defs: `numSDRTerm` |  |
| `s7:lemMULT` | 7.7 | Lemma MULT | S | EG/Spec/Quot/MULT.lean | `MultStatement` → `EG.mult`<br>`MultSublayerStatement` → `EG.multSublayer`<br>`ParMultSublayerStatement` → `EG.parMultSublayer`<br>`MultRunStatement` → `EG.multRun`<br>aux. defs: `subLayerRanks` |  |
| `s7:lemSimple` | 7.8 | Lemma: Q_l is simple | S | EG/Spec/Quot/Simple.lean | `QuotSimpleStatement` → `EG.quotSimple` ○ |  |
| `s7:lemLift` | 7.9 | Lemma JV-L: the lift | S | EG/Spec/Quot/Lift.lean | `LiftRolesStatement` → `EG.liftRoles`<br>`LiftDecompStatement` → `EG.liftDecomp`<br>`LiftAccountingStatement` → `EG.liftAccounting`<br>`LiftJConsumerStatement` → `EG.liftJConsumer`<br>`LiftJConsumerRunStatement` → `EG.liftJConsumerRun`<br>aux. defs: `layerHasPortEnd`, `layerItems`, `ItemInQEdge` |  |
| `s7:lemCC` | 7.10 | Lemma CC: PAR copies | S | EG/Spec/Quot/CC.lean<br>EG/Spec/Num/CC.lean | `CCPartnerStatement` → `EG.Todo.CCPartner`<br>`CCMaxStatement` → `EG.Todo.CCMax`<br>`CCCopiesStatement` → `EG.Todo.CCCopies`<br>`NumCCConstStatement` → `EG.numCCConst`<br>`NumCCTwoPowStatement` → `EG.numCCTwoPow`<br>`NumCCCombineStatement` → `EG.numCCCombine`<br>aux. defs: `parObjsOfColour`, `ccAtom`, `ccS`, `ccPartner`, `parCopies` |  |
| `s7:lemUltra` | 7.11 | Lemma: Ultra-hub copies | S | EG/Spec/Quot/Ultra.lean | `UltraIndepStatement` → `EG.Todo.UltraIndep`<br>`UltraMaxStatement` → `EG.Todo.UltraMax`<br>`UltraCopiesStatement` → `EG.Todo.UltraCopies`<br>`UltraSumStatement` → `EG.Todo.UltraSum`<br>aux. defs: `ultraItems`, `hubCopies` |  |
| `s7:lemVstar` | 7.12 | Lemma: the stage-1 weight X_V | S | EG/Spec/Quot/Vstar.lean | `VstarStatement` → `EG.Todo.Vstar` |  |
| `s7:lemPay` | 7.13 | Lemma: Payments | S | EG/Spec/Quot/Pay.lean | `PayStatement` → `EG.Todo.Pay`<br>`PayGlobalStatement` → `EG.Todo.PayGlobal` |  |
| `s7:defXprime` | 7.14 | Definition: the stage-1 functional X' | D | EG/Defs/Quot/Xprime.lean<br>EG/Defs/Probe/S7b/Outcome.lean | defs: `EG.Quot.jvBadPorts`, `EG.Quot.Xpool`, `EG.Quot.Xprime`, `EG.Quot.XpoolOf`, `EG.Quot.XprimeOf` |  |
| `s7:lemEXprime` | 7.15 | Lemma: expectation of X' | S | EG/Defs/Quot/Constants.lean<br>EG/Spec/Quot/EXprime.lean | defs: `EG.Quot.epsX`<br>`EXprimeStatement` → `EG.Todo.EXprime` |  |
| `s7:lemUHsplit` | 7.16 | Lemma UH*-split: quotient size | S | EG/Defs/Quot/Constants.lean<br>EG/Spec/Quot/UHsplit.lean<br>EG/Spec/Num/CC.lean | defs: `EG.Quot.detl`, `EG.Quot.FQ`, `EG.Quot.eps2`<br>`UHsplitRoundStatement` → `EG.Todo.UHsplitRound`<br>`UHsplitSumStatement` → `EG.Todo.UHsplitSum`<br>`UHsplitDetStatement` → `EG.Todo.UHsplitDet`<br>`UHsplitThetaStatement` → `EG.Todo.UHsplitTheta`<br>`NumUHsplitConstStatement` → `EG.numUHsplitConst` |  |
| `s7:lemOneOutcome` | 7.17 | Lemma: One joint outcome exists | S | EG/Spec/Quot/OneOutcome.lean | `OneOutcomeStage1Statement` → `EG.Todo.OneOutcomeStage1`<br>`OneOutcomeRoundStatement` → `EG.Todo.OneOutcomeRound` | Split into a stage-1 part and a per-round part. |
| `s7:propCost` | 7.18 | Proposition: Cost on the chosen outcome | S | EG/Defs/Quot/Constants.lean<br>EG/Spec/Quot/Cost.lean | defs: `EG.Quot.eps1`, `EG.Quot.C0`<br>`CostStatement` → `EG.Todo.Cost`<br>`CostC0Statement` → `EG.Todo.CostC0` ○ |  |
| `s7:thmJVps` | 7.19 | Theorem JV⁺* | S | EG/Spec/Quot/JVps.lean | `JVpsStatement` → `EG.Todo.JVps` |  |
| `s7:thmHI` | 7.20 | Theorem HI'' (layered quotient induction) | S | EG/Spec/Quot/HI.lean | `HIStatement` → `EG.hi` (wrapper `EG.Todo.HI`)<br>`HIHyp` (hypothesis predicate of HI″) |  |
| `s7:lemGammaSat` | 7.21 | Lemma: The galactic conditions are satisfiable | S | EG/Spec/Gamma/Sat.lean | `GammaSatItemsStatement` → `EG.gammaSat_items` (wrapper `EG.Todo.GammaSatItems`)<br>`GammaSatEpsStatement` → `EG.gammaSat_eps` (wrapper `EG.Todo.GammaSatEps`)<br>`GammaSatStatement` → `EG.gammaSat` (wrapper `EG.Todo.GammaSat`)<br>`GammaCondExistsStatement` → `EG.exists_gammaCond` (wrapper `EG.Todo.GammaCondExists`) |  |
| `s7:thmMainProof` | 7.22 | Corollary JV⁺*-EG; proof of the Main Theorem | S | EG/Spec/Main/CorJVpsEG.lean | `CorJVpsEGStatement` → `EG.Todo.CorJVpsEG` ○ | The chain to the upstream theorem uses `EG.Proof.mainInternal` (row s1:thmMain), which follows this proof; `CorJVpsEGStatement` is the explicit-constant form f(G) ≤ c_EG·n, also proved, not used by that chain. |
| `s7:remNonCirc` | 7.23 | Remark: why the argument is not circular | — | — | — | No Lean statement; realised by the structure (ε₁, ε₂, C₀ are functions of D_* only). |

## Part 4. How this table was built and checked

Built on 2026-09-30 from the tree at commit `f7398e12758c1898ca60614263a2455a9f1dc78f`, the trust
commit of release run 2. Up to `7375ac6`, the only later change under `formal/` is to the inert
acceptance record `formal/work/p3/ACCEPT.md`. Later commits changed the trusted zone, but not the
Lean sources this table is built from: `fc15866` (applied by the user) changed the pinned
`formal/TRUST.md` (§8 items 1 and 2 marked RESOLVED; approval
`formal/APPROVALS/2026-09-30-trust-s8-resolved.md`), and the re-pin of `formal/scripts/pristine.sh`
for it, pending when this table was built, was committed in `19d0754` (new gate SHA-256
`e8e10825…`, recorded in that approval file). A commit at or after `fc15866` therefore fails the
gate with `--trust-ref f7398e1`; the trust commit of a release is `19d0754` or later. This
repository was exported from a later commit of the development repository with the trusted zone of
`19d0754` unchanged; its own trust commit and release run are recorded in `README.md`.

1. **Nodes.** The 127 nodes are those of the P2 blueprints (`formal/work/p2/nodes_s1.json` …
   `nodes_s7b.json`, with the prose in `blueprint_s*.md`). Every label was found in the `ms.aux`
   produced by compiling `proofs/manuscript/ms.tex` with pdflatex (twice; `ms.aux` is not tracked),
   which also gives the numbers.
2. **Statements.** All 335 declarations in `formal/EG/Spec/**` were extracted, with their namespaces
   and docstrings. A statement is assigned to the node named by the first `[sN:label]` in its
   docstring. Sub-labels are folded into their parent node:
   * `s1:condG1`–`G4` into `s1:condGamma`;
   * `s2:eqSplit` into `s2:defTauRules`;
   * `s2:eqDupComposite` into `s2:propOV`;
   * `s3:eqS1`–`S6` into `s3:eqStar`;
   * `s4:eqSplit`, `s4:eqEnds`, `s4:eqClose` into `s4:convVortex` (the observations of §4.1);
   * `s4:eqPVt`, `s4:eqPVstep` into `s4:lemPV`;
   * `s5:eqLY`, `s5:eqZp` into `s5:defZones`;
   * `s5:eqPl` into `s5:defStages`;
   * `s6:eqTowerHalf`, `s6:eqTowerEnd` into `s6:thmCONC`;
   * `s6:eqJbound` into `s6:lemJSLC`.

   Four declarations have no bracketed label. `MainInternal` goes to `s1:thmMain`, `layerItems` to
   `s7:lemLift`, and `subLayerRanks` and `ParMultSublayerStatement` to `s7:lemMULT`.
3. **Proofs.** A theorem is listed as the proof of `XStatement` if its declared type is exactly
   `XStatement` (possibly qualified, possibly with universe arguments). The search covered every
   theorem in `formal/EG` and `formal/EGCheck` (not `EGTest`). Each of the 320 statements has at least
   one such theorem. The 335 declarations are these 320 statements, 14 auxiliary definitions, and
   the hypothesis predicate `HIHyp`. `formal/work/p3_todo_registry.md` (the P3 stub registry)
   agrees for every `EG.Todo.*` entry.
4. **No `sorry`.** This table does not establish it. The evidence is the axiom scan (11,056
   constants of `EG`, `EGTest`, `EGCheck`, 0 `sorryAx`, in the local run; 11,057 in release run 2),
   the release runs, and `leanchecker EG`, which replays every module of `EG` in the kernel. The
   difference of one constant is explained by the target `EGCheck.Final`: the release command adds
   it, and it declares the one constant `EGCheck.erdos_184` (inferred from the commands,
   `formal/work/p3/ACCEPT.md` l. 17 vs `release.yml`; the per-constant lists were not compared).
   The local command also omitted `--cross-check`.
5. **Names.** Every Lean name in this file was checked against the source in two ways. A parser
   that tracks `namespace … end` blocks confirmed each fully qualified name. A `grep` for a
   `theorem`/`def`/`structure`/… declaration of its last component found each one. No name failed
   either check.
6. **Import closure (○).** This was computed from the `import`/`public import` lines, starting at
   `EG.Proof.Main`, `EGCheck.BridgeCore` and `EGCheck.BridgeLemmas`. The closure contains 481 of the
   601 `EG` modules. 103 of the 320 statements have all their proofs outside it.

**Limitations.**

* The assignment of statements to nodes follows the docstrings. A statement that serves two nodes
  appears under one of them.
* The "defs" lists are indicative, not complete.
* The notes summarise the "Formal reading" sections of the `EG/Spec` files and the P2 blueprints;
  those sections are authoritative.
* The table says nothing about whether a statement is faithful to the TeX. That needs a human
  reader.
