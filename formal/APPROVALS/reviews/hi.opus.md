# Clean-room review: group `hi`, reviewer `opus`

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent clean-room agent. I reviewed from
scratch. I read the design note `work/p1b/hi.md` because the task names it. I did not read or
rely on earlier approvals of this group. I changed no repository file; this review is the one file
I wrote.

Scratch file (compiled with `lake env lean` from `formal/`):
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/HITest.lean`.
It compiles with 0 errors. The one warning is an unused simp argument in my own test. It:
* prints both definitions with `pp.numericTypes`;
* checks `example : EG.Spec.HIStatement := EG.hi`;
* checks two parse and elaboration facts with `Iff.rfl` / `norm_num`. First, the hypothesis's
  conclusion is `(f ≤ Cn + 2·Σ f(Q_i)) ∧ (Σ|Q_i| ≤ ϑn)`, with the `∑` bodies ending before `∧` and
  `≤`. Second, `1 / 2` is the real number `0.5`, not `ℕ` division;
* proves `¬ HIHyp 0 0 0 0`, via K₂;
* proves that the `n = 0` instance of the hypothesis is always satisfiable with `k = 0`;
* proves that the conclusion is contentful: on K₂ it forces `1 ≤ 2c`;
* instantiates the manuscript's use, `C = D_*/2 + 1085 + ε₁` and `0 ≤ ϑ_Q ≤ 1/4`, into
  `EG.mainInternal_of_hiHyp`;
* runs `#print axioms` on `EG.hi`, `EG.mainInternal_of_hiHyp` and
  `EG.mainInternal_iff_exists_hiHyp`. Each gives only `[propext, Classical.choice, Quot.sound]`.

Other checks:
* `lake env lean` on `EG/Spec/Quot/HI.lean`, `EG/Proof/Quot/HI.lean` and
  `EG/Proof/Quot/HIMain.lean`: all exit 0 with no messages, so 0 errors and 0 warnings.
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Spec.Quot.HI EG.Proof.Quot.HI
  EG.Proof.Quot.HIMain`: "inspected 559 constants under [EG]; 0 use sorryAx; 0 violations".
* `python3 scripts/lint.py`: 0 findings.
* The modules are imported in `EG.lean` (lines 26, 27, 33). `HIHyp` and `HIStatement` are not yet
  in `LOCK.json`, as expected before the lock. No other file uses them yet.

Scope: `EG/Spec/Quot/HI.lean` (`EG.Spec.HIHyp`, `EG.Spec.HIStatement`). I also checked the proof
`EG/Proof/Quot/HI.lean` (`EG.hi`) and the link `EG/Proof/Quot/HIMain.lean`
(`EG.mainInternal_of_hiHyp`, `EG.mainInternal_iff_exists_hiHyp`). I re-read the dependencies to
interpret the statements: `EG.FGraph`, `FGraph.card` (`EG/Defs/Graph.lean`), `EG.fnum`
(`EG/Defs/Fnum.lean`), `EG.Obj` and `EG.IsDecomp` (`EG/Defs/Objects.lean`) and
`EG.Spec.MainInternal` (`EG/Spec/Main.lean`).

**Overall verdict: APPROVE, with notes.** Both statements match Theorem HI″ in every quantifier,
inequality, constant and edge case. The proof proves exactly the Spec. The link to
`MainInternal` is correct, and the fidelity equivalence rules out a vacuous hypothesis. The notes
N1–N7 record conventions and harmless generalisations. None of them is a defect.

---

## Manuscript text

`s7.tex` l. 1354–1367, Theorem HI″ [s7:thmHI]:

> Let $C\ge\Dstar/2$ and $\vartheta\in[0,1/2)$ be constants with the following property. Every
> graph $G$ without isolated vertices, with $n\ge\Nzero$ vertices and $d_1=2|E(G)|/n\ge\Dstar$,
> admits finitely many simple graphs $Q_1,\dots,Q_k$ ($k\ge0$) such that
> $\f(G)\le C\,n+2\sum_{i=1}^{k}\f(Q_i)$ and $\sum_{i=1}^{k}|V(Q_i)|\le\vartheta\,n$.
> Then $\f(G)\le c\,|V(G)|$ for every graph $G$, where
> $c\defeq\max\bigl(C/(1-2\vartheta),\,\Nzero/2\bigr)$.
> \deps{s1:factAdd, s1:defObject}

Context used for interpretation:
* [s1:convGraphs](a): "Graphs are finite and simple … $G$ always denotes the input graph and
  $n\defeq|V(G)|$. For any graph $H$ we write $|H|\defeq|V(H)|$."
* [s1:defObject]: "f(F) is the least number of objects in a decomposition of F (so f(∅) = 0);
  f(H) := f(E(H))".
* [s1:defConstants](ii): "$\Nzero$ is an absolute constant … with $\Nzero\ge2^{40}$". There is
  no integrality requirement. (vi): "$\cEG\defeq\max\{\Czero/(1-2\thetaQ),\Nzero/2\}$".
* `s2.tex` l. 499–502: "Put $G_1\defeq G$ … $d_l\defeq2|E(G_l)|/n$", so $d_1 = 2|E(G)|/n$, as
  written inline in HI″.
* Producer, [s7:thmJVps] (l. 1317ff.): "Let $G$ be a graph with $n\ge\Nzero$ vertices and
  $d_1\ge\Dstar$ … Then there are simple graphs $Q_3,\dots,Q_R$ without isolated vertices such
  that (1) $\f(G)\le\Czero n+2\sum_{l=3}^{R}\f(Q_l)$ … (2) $\sum_{l=3}^{R}|V(Q_l)|\le\thetaQ\,n$,
  where $\thetaQ=\epsTwo(\Dstar)\le1/4$."
* Consumer, [s7:thmMainProof] (l. 1440ff.): "We apply Theorem s7:thmHI with $C\defeq\Czero$ and
  $\vartheta\defeq\thetaQ$ … $\Czero\ge\Dstar/2$ … $0\le\thetaQ\le1/4<1/2$ … gives
  $\f(G)\le\cEG|V(G)|$ for every graph $G$. In particular $\f(n)\le\cEG n$ … $\f(n)=O(n)$."

---

## `EG.Spec.HIHyp Dstar N₀ C ϑ`

Elaborated form (`#print`, `pp.numericTypes`):
```
∀ (V : Type) (G : FGraph V),
  (∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e) →
  N₀ ≤ ↑G.card →
  Dstar ≤ (2 : ℝ) * ↑G.edges.card / ↑G.card →
  ∃ k W Q, ↑(fnum G.edges) ≤ C * ↑G.card + (2 : ℝ) * ∑ i, ↑(fnum (Q i).edges)
           ∧ ∑ i, ↑(Q i).card ≤ ϑ * ↑G.card
```
with `k : ℕ`, `W : Fin k → Type` and `Q : (i : Fin k) → FGraph (W i)`.

Back-translation: for every finite simple graph G (vertex set `G.verts`, loopless edge set
`G.edges`) such that every vertex lies on an edge, |V(G)| ≥ N₀ and D_* ≤ 2|E(G)|/|V(G)| (real
division), there are k ≥ 0 and finite simple graphs Q_1,…,Q_k with
f(G) ≤ C·n + 2·Σ f(Q_i) and Σ |V(Q_i)| ≤ ϑ·n, where n = |V(G)|.

Item-by-item comparison:
| Manuscript | Lean | Check |
|---|---|---|
| "graph G" (finite, simple) | `G : FGraph V`, `V : Type` | FGraph is finite and loopless with ends in `verts` (structure fields). OK |
| "without isolated vertices" | `∀ v ∈ G.verts, ∃ e ∈ G.edges, v ∈ e` | Equivalent to `deg v ≠ 0` (`FGraph.noIsolated_iff_deg_ne_zero`, proved). OK |
| "n ≥ N₀ vertices" | `N₀ ≤ (G.card : ℝ)`, `card = verts.card` | Non-strict, correct direction. OK |
| "d₁ = 2\|E(G)\|/n ≥ D_*" | `Dstar ≤ 2 * E / n` in ℝ | Non-strict; the parse is `(2*E)/n`. At n = 0, see N2. OK |
| "admits finitely many simple graphs Q₁..Q_k (k ≥ 0)" | `∃ k W Q`, `Fin k`, own vertex types | k = 0 allowed. Q depends on G (∃ inside ∀ G). OK |
| "f(G) ≤ Cn + 2Σ f(Q_i)" | `fnum G.edges ≤ C*n + 2*∑ fnum (Q i).edges` | Non-strict; cast ℕ→ℝ is exact; loopless sets, so `fnum` = f. OK |
| "Σ\|V(Q_i)\| ≤ ϑn" | `∑ (Q i).card ≤ ϑ * n` | Non-strict. OK |

Strength relative to the manuscript. The downstream work must prove `HIHyp` from JV⁺*, so it
must not demand more than the manuscript's hypothesis. It does not:
* G ranges only over `V : Type`. That is a weaker demand, and every finite graph has a copy on
  `Fin n`.
* Q_i must live in `Type`. That is formally a stronger demand but not really one: the producer's
  quotients are built from `V : Type` or `Fin m`, and every finite graph can be moved to `Fin m`.
* The Q_i need not be free of isolated vertices, and need not be smaller than G. JVps gives both;
  HI″ does not need them.
* The one place where Lean's hypothesis applies to *more* graphs than the manuscript's is the
  empty graph (n = 0), when N₀ ≤ 0 and D_* ≤ 0 (`2*0/0 = 0`). That instance is always
  satisfiable with k = 0 (proved in the scratch file). So it adds no real demand (N2).

For the manuscript's constants (N₀ ≥ 2^40 > 0, D_* ≥ 2^117 > 0) the Lean hypothesis and the
manuscript's hypothesis are literally the same condition on every graph.

Non-vacuity: `¬ HIHyp 0 0 0 0` (scratch, via K₂), so the hypothesis is not trivially true.
`EG.mainInternal_iff_exists_hiHyp` shows that `HIHyp` holds for some admissible constants iff
`MainInternal` holds, so it is not unsatisfiable either unless the conjecture fails.

## `EG.Spec.HIStatement`

Elaborated form:
```
∀ (Dstar N₀ C ϑ : ℝ), Dstar / 2 ≤ C → 0 ≤ ϑ → ϑ < (1 / 2 : ℝ) → HIHyp Dstar N₀ C ϑ →
  ∀ (V : Type) (G : FGraph V), ↑(fnum G.edges) ≤ max (C / (1 - 2 * ϑ)) (N₀ / 2) * ↑G.card
```
Back-translation: for all real D_*, N₀, C, ϑ with C ≥ D_*/2 and 0 ≤ ϑ < 1/2, if the property
`HIHyp` holds, then every finite simple graph G satisfies f(G) ≤ max(C/(1−2ϑ), N₀/2)·|V(G)|.

* The order of quantifiers is the manuscript's: the constants come first, then the property
  (∀G ∃Q), then ∀G. c is written inline as a function of C, ϑ and N₀ only, so "C and ϑ do not
  depend on c" holds by construction.
* Every inequality has the manuscript's direction and strictness: `Dstar/2 ≤ C`, `0 ≤ ϑ`,
  `ϑ < 1/2` (real 1/2, checked), and conclusion `≤`.
* `1 - 2ϑ > 0` under the hypotheses, so the division is genuine. `N₀ / 2` is real division.
  `max` is the real maximum, and `max (…) (…) * n` parses as `(max …) * n` (checked).
* The conclusion is over every graph: with or without isolated vertices, with n < N₀ or
  d₁ < D_*, and n = 0, where the bound reads 0 ≤ 0.
* There are no typeclass assumptions: `FGraph`, `card`, `fnum` and `Finset.sum` over `Fin k` need
  no `DecidableEq`/`Fintype` on `V` or `W i`. There are no `ℕ` subtractions and no logarithms.
* The constants are universally quantified over ℝ with no sign conditions. This is a
  generalisation of the manuscript, where N₀ and D_* are fixed positive constants. The theorem is
  therefore at least as strong, and the proof covers it (N1).

Non-triviality: the conclusion is contentful. With the hypothesis, K₂ forces c ≥ 1/2 (scratch).
Also, `HIStatement` plus a proof of `HIHyp` gives `MainInternal`.

## Proof and link (`EG/Proof/Quot/HI.lean`, `EG/Proof/Quot/HIMain.lean`)

* `theorem hi : Spec.HIStatement` proves exactly the Spec, with no auxiliary weakening. It
  instantiates `hi_induction` with c = max(C/(1−2ϑ), N₀/2). `N₀/2 ≤ c` is `le_max_right`, and
  `C ≤ c(1−2ϑ)` is `div_le_iff₀`.
* `hi_induction` is a strong induction on n, over all `V : Type`, following steps (1)–(5) of the
  manuscript. Step (1) uses factAdd(d), deleting an isolated vertex. Step (2) uses
  2|E| ≤ n(n−1) and n < N₀. Step (3) uses the trivial bound f ≤ |E| < D_* n/2 ≤ Cn ≤ cn. Steps
  (4)–(5) use the hypothesis, |V(Q_i)| ≤ ϑn < n, and the induction hypothesis on each Q_i (the
  Q_i live in `Type`, so the induction hypothesis applies).
* The one step beyond the manuscript is `hi_const_nonneg`, c ≥ 0. It is needed only because of
  the generalisation in N1, and is shown by applying the hypothesis to K₂ when C < 0 and N₀ < 0.
  I checked the argument: Σ|V(Q_i)| ≤ 2ϑ < 1 forces all Q_i to be empty, so 1 ≤ 2C < 0.
* `EG.mainInternal_of_hiHyp (hC : Dstar/2 ≤ C) (hϑ0 : 0 ≤ ϑ) (hϑ : ϑ < 1/2) (h : HIHyp …) :
  Spec.MainInternal` has the constant ⌈c⌉₊ (MainInternal wants c : ℕ). The route is
  `hi` → `f(G) ≤ ⌈c⌉₊·|V(G)|` on `FGraph.ofSimpleGraph G` → `fnum_edgeFinset_le_iff`, which gives
  a decomposition list of that length for `G.edgeSet`. This is correct and matches
  [s7:thmMainProof]'s "in particular f(n) ≤ c_EG n". The manuscript's parameters C₀ ≥ D_*/2 and
  0 ≤ ϑ_Q ≤ 1/4 fit these hypotheses (scratch).
* `EG.mainInternal_iff_exists_hiHyp`: → uses k = 0, C = c (the MainInternal constant) and
  D_* = N₀ = ϑ = 0. ← is the link above. This is a sound fidelity check.
* The helpers `hiHyp_of_fintype_index` (Fintype-indexed families → `Fin k`) and `hi_simpleGraph`
  are correct and do not change the Spec.
* Axioms: only `propext`, `Classical.choice` and `Quot.sound`. The scan found 0 `sorryAx` and 0
  violations in 559 constants.

---

## Notes

* **N1 (generalised constants).** D_*, N₀, C and ϑ are arbitrary reals. The manuscript's are
  fixed, with N₀ ≥ 2^40, D_* ≥ 2^117 and N₀ not required to be an integer. This makes the theorem
  stronger. The nonnegativity of c, which is obvious in the manuscript, is proved in Lean
  (`hi_const_nonneg`). There is no wording consequence for the manuscript.
* **N2 (d₁ at n = 0).** The real division `2|E|/n` has the value 0 at n = 0, a case the manuscript
  does not consider. The hypothesis then applies to the empty graph only if N₀ ≤ 0 and D_* ≤ 0,
  and that instance is always satisfiable with k = 0. The division form is the right choice. The
  multiplied-out form `D_* n ≤ 2|E|` would apply to the empty graph whenever N₀ ≤ 0, whatever
  the sign of D_*. Since that instance is trivially satisfiable, either form is harmless.
* **N3 (universes).** G, the Q_i and the conclusion are all in `Type`, like
  `EG.Spec.MainInternal`. The producer of `HIHyp` (s7:thmJVps) must build its quotients on a
  vertex type in `Type`. This is automatic for subtypes or sums of `V : Type`, or for `Fin m`.
* **N4 (index set).** The quotients are indexed by `Fin k`. The rounds `l = 3..R` of s7:thmJVps
  (possibly an empty range) convert through `EG.hiHyp_of_fintype_index`.
* **N5 (graph representation for the producer).** `HIHyp` is stated for `G : FGraph V`. If the
  JVps Spec is stated for a Mathlib `SimpleGraph`, an adapter will be needed on the producer side,
  as the design note says. This affects no statement here.
* **N6 (`0 ≤ ϑ`).** This hypothesis is kept as in the manuscript ("ϑ ∈ [0,1/2)"). It is harmless;
  the manuscript's ϑ_Q = ε₂(D_*) ≥ 0 satisfies it.
* **N7 (naming).** `EG.hiK2` is a public `@[expose] def` in namespace `EG` in a Proof file. A later
  fixture could clash with the name. This is not a statement issue.

No blocking issues.
