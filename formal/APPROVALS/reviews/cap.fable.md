# Clean-room review: group `cap`, reviewer `fable`

Date: 2026-09-26. Reviewer: Claude (Fable 5.1), independent clean-room agent. Reviewed from
scratch against the manuscript and the B–M source text; earlier approvals (`work/p1b/cap.review1.md`,
`cap.review2.md`) were read only to know what had been claimed, and every claim below was
re-derived or re-run by me. No repository file other than this one was written; all scratch files
are in the session scratchpad.

Scope:
* `EG/Spec/HB/Cap.lean`: `EG.Spec.CapStatement` ([s2:lemCap] (i)), `EG.Spec.CapUniformStatement`
  (the remark's uniform form), `EG.Spec.CapGraphStatement` (the graph-level step of the proof
  of (ii)); proved in `EG/Proof/HB/Cap.lean` (`EG.cap`, `EG.cap_uniform`, `EG.cap_graph`).
* `EG/Spec/Ext/BMLemma25.lean`: `EG.Spec.BMLemma25Statement` ([s1:citLem25], B–M Lemma 25 in
  explicit form) with the T0 deviation **T0-cap-1** (extra hypothesis `2 ≤ m`); `EG.bmLemma25` is
  `sorry` by design, `EG.bmLemma25_literal_false` is the sorry-free refutation of the literal form.

Dependencies read to interpret the statements (reviewed in other groups, not re-verdicted here):
`EG.FGraph`, `FGraph.card`, `FGraph.nbrSet`, `FGraph.deleteEdges` (`EG/Defs/Graph.lean`);
`FGraph.IsExpander` (`EG/Defs/Expander.lean`); `EG.cycleEdges`, `EG.Obj`, `EG.Obj.WF`
(`EG/Defs/Objects.lean`).

Manuscript passages compared (quoted below): s2.tex l.622–677 ([s2:lemCap] statement, remark,
proof); s1.tex l.716–734 ([s1:citLem25]); s1.tex l.321–331 ([s1:convGraphs] (a), (b));
s2.tex l.505–517 ((R1)–(R3)); s1.tex l.995–998 (Γ2(a)); s1.tex l.913 ([s1:defConstants]
`ε := 2^{-5}`); B–M `papers/2211.07689.txt` l.584–586 (Definition 11), l.1502–1558 (Lemma 25 and
its proof), l.141 ("All our logarithms have base two").

Machine checks run (all from `formal/`, `LEAN_NUM_THREADS=2`):
* `scratchpad/CapPrintFable.lean`: `#print` of the four Specs and of `IsExpander`, `cycleEdges`,
  `Obj.WF` with `pp.parens`, `pp.numericTypes`, `pp.universes`, `pp.coercions`; type ascriptions
  `(EG.cap : CapStatement)`, `(EG.cap_uniform : CapUniformStatement)`,
  `(EG.cap_graph.{0,3} : CapGraphStatement.{0,3})`, `(EG.bmLemma25.{0,2} : BMLemma25Statement.{0,2})`;
  `#print axioms` of all five theorems and of `cap_remark_counterexample`. 0 errors.
* `scratchpad/CapReviewFable.lean`: my own tests (§4 below). 0 errors, 0 warnings.
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.HB.Cap EG.Proof.Ext.BMLemma25
  EG.Spec.HB.Cap EG.Spec.Ext.BMLemma25 EG.Lib.Found.LogMono`: "inspected 150 constants under
  [EG]; 2 use sorryAx; 0 violations"; the two are `EG.bmLemma25` (allowed) and `EG.cap_graph`
  (depends on it).
* `lake env lean EGTest/Cap.lean`: 0 errors, 0 warnings. `python3 scripts/lint.py`: 0 findings.
* `grep sorry` over the four Lean files: the only non-docstring occurrence is
  `EG/Proof/Ext/BMLemma25.lean:24` (`EG.bmLemma25`).

**Overall verdict: APPROVE.** All four statements back-translate to exactly the manuscript
text (or, for `CapGraphStatement`, to exactly the proof step it names), with the right
quantifier order, strictness, constants and log base, and no Lean convention changes their
meaning. The single deviation, `2 ≤ m` in `BMLemma25Statement`, is necessary (the literal form
is false, machine-checked), minimal, and harmless for the only consumer. Notes N1–N5 are
non-blocking.

---

## 1. Pretty-printed parse (what is actually locked)

With `pp.parens`/`pp.numericTypes` every numeral is `(k : ℝ)` and every exponent is a `ℕ`
literal except the `zpow` `(2:ℝ)^((-5):ℤ)`:
* `18432 * T * Real.logb 2 m ^ 4` parses as `((18432 * T) * ((logb 2 m) ^ 4))`, i.e.
  `18432 · T · (log₂ m)^4`;
* `2 ^ 16 * T * Real.logb 2 T ^ 4` as `((2^16 * T) * ((logb 2 T)^4))`;
* `(Real.logb 2 T + 40) ^ 4` as `((logb 2 T + 40)^4)`;
* `ε ^ 2 * (G.card : ℝ) / (18 * Real.logb 2 (G.card : ℝ) ^ 4)` as
  `((ε^2 * ↑m) / (18 * ((logb 2 ↑m)^4)))`;
* `(2 : ℝ) ^ 30 / ε ^ 2` as `((2^30) / (ε^2))`;
* `2 ≤ G.card` is in `ℕ`; `2 ^ 40 ≤ (G.card : ℝ)`, `2 ^ 117 ≤ T`, `(c.length : ℝ) < T` are in `ℝ`.

`log⁴ m` in the manuscript is a power, not an iterate: [s1:convGraphs] (b) writes iterates as
`log^{[k]}`. `log = log₂` by [s1:convGraphs] (b) ("`\log=\log_2` throughout, as in [BM, l. 141]"),
and B–M l.141 confirms "All our logarithms have base two", so `Real.logb 2` is right for both
the manuscript statements and the cited B–M lemma (whose Definition 11 also uses `log² n`).

## 2. `EG.Spec.CapStatement` vs [s2:lemCap] (i)

Manuscript (s2.tex l.624–625): "(i) If $m\ge2^{40}$, $T\ge2^{117}$ and $m<18432\,T\log^4m$,
then $m\le2^{16}T\log^4T$."

Lean: `∀ m T : ℝ, 2^40 ≤ m → 2^117 ≤ T → m < 18432*T*(logb 2 m)^4 → m ≤ 2^16*T*(logb 2 T)^4`.

Back-translation: for all real `m, T`, if `m ≥ 2^40`, `T ≥ 2^117` and `m < 18432 T (log₂ m)^4`,
then `m ≤ 2^16 T (log₂ T)^4`. This is the manuscript verbatim:
* the one strict (`<`) and three non-strict (`≥`, `≥`, `≤`) inequalities agree;
* constants `2^40`, `2^117`, `18432 = 18·2^10`, `2^16` agree;
* both variables are real. The manuscript leaves the type of `m` open; the only consumer,
  (ii), applies it to `m = |𝒫| ∈ ℕ` and to the real `T = d_l log² d_l`. The real statement
  implies the natural one (scratch `cap_nat`), so real `m` is the stronger, safe reading.
* Lean conventions: `logb 2 m` is only evaluated at `m ≥ 2^40 > 1`, so `Real.log 0 = 0` and
  `log |x|` never enter. No subtraction, no division.
* Non-vacuity: `EGTest/Cap.lean` shows the hypotheses are satisfiable (`m = 2^40`, `T = 2^117`),
  that dropping `m < 18432 T log⁴ m` makes it false (`m = 2^200`), and that weakening
  `T ≥ 2^117` to `T ≥ 2^20` makes it false (the remark's `T = 2^20`, `m = 2^55`). I checked the
  remark's numbers by hand: `18432·2^20·55^4 = 2^{14.17+20+23.13} = 2^{57.3}`,
  `2^36·20^4 = 2^{36+17.29} = 2^{53.29}`.

The hypothesis `m ≥ 2^40` is never used in the proof (the manuscript's argument does not use it
either); `EG.cap_of_T_ge` proves (i) without it. Keeping it in the locked Spec is the right
choice (verbatim), and the stronger lemma is available for consumers. Verdict: **approve**.

## 3. `EG.Spec.CapUniformStatement` vs the remark

Manuscript (s2.tex l.632–635): "*Remark (not used).* Part (i) is false for small $T$: [...] The
uniform form $m\le\max\bigl(2^{40},2^{16}T(\log T+40)^4\bigr)$ holds for all $T\ge1$." The proof
of the remark (l.651–657) makes the implicit hypothesis explicit: "$m>\max(2^{40},B')$ would
give $\chi(m)>\chi(B')\ge18432\,T$" contradicting "$\chi(m)<18432\,T$", i.e. the hypothesis is
`m < 18432 T log⁴ m`, with the other hypotheses of (i) replaced by `T ≥ 1`.

Lean: `∀ m T : ℝ, 1 ≤ T → m < 18432*T*(logb 2 m)^4 → m ≤ max (2^40) (2^16*T*(logb 2 T + 40)^4)`.

The hypothesis `m ≥ 2^40` is dropped. I proved in the scratch file (`uniform_equiv`) that the
Spec is logically equivalent to the version with `2^40 ≤ m` (for `m < 2^40` the conclusion holds
through the `max`). So this is exactly the remark's claim.
* Lean conventions: `m` is now an arbitrary real. For `m ≤ 0`, `Real.logb 2 m = logb 2 |m|`
  (or `0` at `m = 0`); the hypothesis `m < 18432 T (…)^4` then either fails (`m = 0`:
  `0 < 0`) or holds with a trivially true conclusion (`m < 0 ≤ 2^40`). For `0 < m < 1` the
  conclusion is again trivial. None of this changes the meaning.
* Non-vacuity: the test file shows the hypothesis is load-bearing (`m = 2^200`, `T = 1`).
* This statement is marked "not used" in the manuscript; nothing downstream will depend on it.
  Locking it is harmless. Verdict: **approve**.

## 4. `EG.Spec.CapGraphStatement` vs the proof step of [s2:lemCap] (ii)

This is not a manuscript *statement* but a named step of the manuscript's proof (part (ii)
itself needs the s2 hierarchy, which is not yet defined). Manuscript (s2.tex l.660–669): "Let
$l\le R$ and $T\defeq\tHB_ld_l=d_l\log^2d_l$. By Γ2(a), $d_l\ge\Dstar\ge2^{117}$, so
$\log^2d_l\ge1$ and $T\ge2^{117}$ [...]. Let $\piece$ be an $s=0$ piece and $m\defeq|\piece|$. If
$m<2^{40}$ then $m\le M_l$. Otherwise the graph of $\piece$ is an $(\eps,0)$-expander (the
stopping rule in (R3)) with $\eps=2^{-5}$ on $m\ge2^{40}=2^{30}/\eps^2$ vertices, so by Cited
result [s1:citLem25] it contains a cycle of length at least $\eps^2m/(18\log^4m)=m/(18432\log^4m)$.
This cycle lies in $G'_l$, which has no cycle of length at least $T$ by (R1). Hence
$m<18432\,T\log^4m$, and (i) gives $m\le2^{16}T\log^4T\le M_l$."

Lean: for every `V : Type u`, `[DecidableEq V]`, `G : FGraph V`, `T : ℝ`: if `2^117 ≤ T`,
`2^40 ≤ |V(G)|`, `G.IsExpander (2^(-5:ℤ)) 0`, and every vertex list `c` with `c.Nodup`,
`3 ≤ |c|` and all edges `c₀c₁, …, c_{k-1}c₀ ∈ E(G)` has `|c| < T`, then
`|V(G)| ≤ 2^16 T (log₂ T)^4`.

Checks:
* **ε.** [s1:defConstants] (s1.tex l.913): "$\eps\defeq2^{-5}$"; (R3) stops "exactly at
  $(\eps,0)$-expanders". `(2:ℝ)^(-5:ℤ) = 1/32` (scratch, `norm_num`). ✓
* **Threshold on T.** Γ2(a) (s1.tex l.997): "$\Dstar\ge2^{117}$; hence $\log_2(\tHB_ld_l)\ge117$
  in every round". So `T ≥ 2^117` is exactly what the consumer will have. ✓
* **`m ≥ 2^40`.** The "Otherwise" branch. ✓ (`2^40 = 2^30/ε²`, scratch `norm_num`.)
* **"No cycle of length at least T".** (R1) (s2.tex l.508–509): "Thus $G'_l$ has no cycle of
  length at least $\tHB_ld_l$", with `T = t^HB_l d_l` real. Negated correctly to "every cycle has
  length `< T`" as a real comparison. The Spec puts the hypothesis on `G` (the piece's graph),
  not on `G'_l`: since a cycle of `G ≤ G'_l` is a cycle of `G'_l` (edge-set monotonicity of the
  encoding), the Spec's hypothesis is *weaker* than (R1), so the Spec is at least as strong as
  the manuscript step needs. ✓
* **Cycle encoding.** A cycle of a simple graph is a cyclic sequence of ≥ 3 distinct vertices
  with consecutive vertices adjacent; `Obj.WF (cycle c) ∧ ∀ e ∈ cycleEdges c, e ∈ G.edges` is
  exactly this: `cycleEdges c = zipWith s(·,·) c (c.rotate 1)` includes the closing edge
  (`EGTest/Cap.lean`: `cycleEdges [1,2,3] = [s(1,2), s(2,3), s(3,1)]` by `decide`), has exactly
  `c.length` entries (scratch `length_cycleEdges`), and its vertices lie in `V(G)` automatically
  (scratch `cycle_verts_sub`, via `FGraph.edge_verts`), so no `∀ v ∈ c, v ∈ G.verts` is needed.
  Lists of length 1 or 2 are excluded by `3 ≤ c.length`; they would encode a loop (never in
  `E(G)`) or an edge traversed twice, neither a cycle. So the hypothesis ranges over exactly the
  genuine cycles — quantifying over more lists would have made the hypothesis stronger and the
  Spec weaker, which does not happen. Length = number of vertices = number of edges = `c.length`. ✓
* **Conclusion.** `(G.card : ℝ) ≤ 2^16 T (log₂ T)^4`, matching "(i) gives $m\le2^{16}T\log^4T$";
  the further `≤ M_l` belongs to (ii) proper. ✓
* **Universe / typeclass.** Universe-polymorphic in `V`; `DecidableEq V` is only used by
  `Finset` operations inside `IsExpander` and does not affect the truth value (Decidable is a
  subsingleton). ✓
* **Non-vacuity.** `EGTest/Cap.lean`: `K_{2^40}` on `Fin (2^40)` is a `(2^{-5},0)`-expander
  proved through Definition 11, and all its cycles have length `≤ 2^40 < 2^117`, so the
  hypotheses are jointly satisfiable; `K_{2^200}` shows the no-long-cycle hypothesis is
  load-bearing. ✓

Verdict: **approve**.

## 5. `EG.Spec.BMLemma25Statement` vs [s1:citLem25] and B–M Lemma 25

Manuscript (s1.tex l.717–719): "Let $\varepsilon\ge2^{-5}$ and $m\ge2^{30}/\varepsilon^2$ (so
$m\ge2^{40}$ suffices at $\varepsilon=2^{-5}$). Every $m$-vertex $(\varepsilon,0)$-expander
contains a cycle of length at least $\varepsilon^2m/(18\log^4m)$."

B–M (l.1508–1509): "Lemma 25. Any n-vertex (ε, 0)-expander, with ε ≥ 2^{-5} and n ≥ 2^{30}/ε²,
contains a cycle of length Ω(n/log⁴ n)."

Lean: for every `V : Type u`, `[DecidableEq V]`, `G : FGraph V`, `ε : ℝ`: if `2^{-5} ≤ ε`,
`2^30/ε² ≤ |V(G)|`, `2 ≤ |V(G)|` and `G.IsExpander ε 0`, then there is a vertex list `c` with
`c.Nodup`, `3 ≤ |c|`, all cycle edges in `E(G)`, and `ε²·|V(G)| / (18 (log₂ |V(G)|)^4) ≤ |c|`.

| Item | Lean | Manuscript | OK |
|---|---|---|---|
| ε range | `2^(-5:ℤ) ≤ ε` (real) | `ε ≥ 2^{-5}` | yes, non-strict |
| size | `2^30/ε^2 ≤ ↑G.card` | `m ≥ 2^{30}/ε²` | yes, non-strict; `ε > 0` so no `/0` |
| `m`-vertex | `m = G.card = \|V(G)\|` | `\|G\| := \|V(G)\|` ([s1:convGraphs] (a)) | yes |
| expander | `G.IsExpander ε 0` | `(ε,0)`-expander, Def. 11, `log₂` of `\|G\|` | yes; with `s = 0`, `F` is forced empty (scratch `expander_zero_F_empty`), as in B–M |
| cycle | `Obj.WF` + all `cycleEdges c ∈ G.edges` | "contains a cycle" | yes (§4) |
| length | `(c.length : ℝ)` | number of edges (= vertices) | yes |
| bound | `ε²m/(18 (log₂ m)^4) ≤ \|c\|` | "length at least `ε²m/(18 log⁴ m)`" | yes, non-strict, `log₂` |
| **extra** | `2 ≤ G.card` | absent | **T0-cap-1**, judged below |

**Is the explicit constant 18 faithful to B–M?** The manuscript's "explicit form" is its own
extraction from the B–M proof; the Spec locks it, so I re-derived it from B–M l.1514–1558. At
the DFS moment with `|U| = |R|`: `|P| = n − 2|U| ≥ |N(U)| ≥ ε|U|/log² n`, hence
`|P| ≥ εn/(3 log² n)` (the case `|P| ≥ n/3` needs `ε ≤ log² n`, which holds for every
`(ε,0)`-expander on `n ≥ 2` vertices — take `U` of size `⌈n/2⌉ ≤ 2n/3`, whose neighbourhood has
at most `⌊n/2⌋ ≤ |U|` vertices). B–M then choose `ε²n/(18 log⁴ n) ≤ |Y| < ε²n/(9 log⁴ n)`, the
cycle "contains each vertex in Y", so its length is `≥ |Y| ≥ ε²n/(18 log⁴ n)`; the contradiction
branch uses `|N(X')| ≥ ε|P|/(3 log² n) ≥ ε²n/(9 log⁴ n) > |Y|`. The constant 18 is exactly what
the B–M proof yields. ✓

### The deviation T0-cap-1 (`2 ≤ m`): necessary and harmless

*Necessary.* At `m = 1`, `log₂ 1 = 0`, so the manuscript's bound `ε²m/(18 log⁴ m)` is undefined;
in Lean it is `x/0 = 0`. With `ε = 2^{15}` every hypothesis of the literal statement holds for
the one-vertex graph: `2^{30}/ε² = 1 ≤ 1`, and Definition 11 is vacuous (no `U` with
`1 ≤ |U| ≤ 2/3`). There is no cycle. So the literal Lean statement is **false**;
`EG.bmLemma25_literal_false` proves this for every universe, sorry-free (axioms
`propext, Classical.choice, Quot.sound`; its statement is, character for character,
`BMLemma25Statement` with the `2 ≤ G.card` hypothesis deleted — I compared the `#print`
outputs). No other repair avoids an extra hypothesis: writing the conclusion multiplied out
(`ε² m ≤ 18 log⁴ m · |c|`) is equally false at `m = 1`, and an upper bound on `ε` would be an
unmotivated deviation from a statement that has none. `m = 0` is already excluded by
`m ≥ 2^{30}/ε² > 0`. So `2 ≤ m` excludes exactly the one degenerate value and is the minimal
repair; with it the denominator is positive (scratch `denom_pos`) and Lean's `x/0` never occurs.

*Encoding class.* The manuscript's statement is undefined rather than false at `m = 1` (and
B–M's `Ω(n/log⁴ n)` is asymptotic, so `n = 1` is meaningless there); the failure is created by
Lean's total division. T0 is the right class (PLAN §7). The entry is recorded in
`formal/CONVENTIONS.md` (T0 record, `T0-cap-1`) with the wording "Let ε ≥ 2^{-5} and
m ≥ max(2, 2^{30}/ε²)", which is the correct manuscript fix.

*Harmless.* The only use is [s2:lemCap] (ii) with `ε = 2^{-5}` and `m ≥ 2^40`; `EG.cap_graph`
derives `2 ≤ G.card` from `2^40 ≤ G.card` with no other change. Restricted to `m ≥ 2` the
repaired Spec *is* the literal statement, so the two differ only at `m = 1`.
Moreover, for `m ≥ 2` the remaining hypotheses are unsatisfiable for small `m` anyway: scratch
`eps_le_of_expander` gives `ε ≤ m log² m` from a singleton `U` (the sharper `ε ≤ log² m` above
by hand), so with `ε²m ≥ 2^30` one gets `m log⁴ m ≥ 2^30`, `m ≳ 2^{14.6}`.

*Plausibility of the locked (sorry'd) statement.* Since a false locked statement would be
serious even with `sorry`, I re-derived B–M's DFS argument for every instance of the Spec.
The hypotheses force `ε ≤ log² m` and `ε² m ≥ 2^{30}`, so the target length
`a := ε²m/(18 log⁴ m)` is `≥ 23.3` (at `m ≤ 2^40`: `≥ 2^{30}/(18·40^4)`; at `m ≥ 2^40`:
`≥ m/(18432 log⁴ m)`, increasing, `≥ 2^{40}/(18432·40^4)`; both `= 23.3`), and
`|P|/3 ≥ εm/(9 log² m) ≥ 2a`, so an integer `|Y| ∈ [a, 2a)` with `|X|, |Z| ≥ |P|/3` exists.
Connectivity of `G` follows from expansion (a component of size `≤ m/2` would have empty
neighbourhood, impossible as `ε|U|/log² m > 0` for `m ≥ 2`). In the cycle branch the shortest
`X`–`Z` path in `G − Y` has interior outside `P`, so the cycle is a Nodup list of
`≥ |Y| + 2 ≥ 25` vertices with all edges in `E(G)`: `Obj.WF` holds and `|c| ≥ |Y| ≥ a`. In the
other branch, the smaller side `S` (`1 ≤ |S| ≤ m/2 ≤ 2m/3`) has `N(S) ⊆ Y`, giving
`2a ≤ ε|P|/(3 log² m) ≤ |N(S)| ≤ |Y| < 2a`. I see no obstruction; the statement is true as far
as a hand proof can tell.

Verdict: **approve** (with the recorded T0 deviation).

## 6. The proof files prove exactly the Specs

* `EG.cap : EG.Spec.CapStatement`, `EG.cap_uniform : EG.Spec.CapUniformStatement`,
  `EG.cap_graph.{u} : EG.Spec.CapGraphStatement.{u}`, `EG.bmLemma25.{u} : EG.Spec.BMLemma25Statement.{u}`:
  type ascriptions checked at universes 0, 2, 3 (`CapPrintFable.lean`). No auxiliary
  definition stands between a theorem and its Spec; the Specs mention only `Real.logb`, `max`,
  and the foundation objects, so no weakening can hide.
* Axioms: `cap`, `cap_uniform`, `bmLemma25_literal_false`, `cap_remark_counterexample` use only
  `propext, Classical.choice, Quot.sound`; `bmLemma25` and `cap_graph` add `sorryAx`
  (allowed: `bmLemma25` is the designated later task, `cap_graph` depends on it). The axiom scan
  over the five modules reports 0 violations.
* I checked the proof of (i) by hand against the manuscript's argument: `cap_core` is the
  monotonicity step for `χ(y) = y/log⁴ y` (needs `ln B ≥ 4`, from `B ≥ 2^16`);
  `cap_numeric` proves `16 + x + 4 log₂ x ≤ 1.37317 x` for `x ≥ 117` from the concavity bound
  `log₂ x ≤ log₂ 117 + (x−117)/(117 ln 2)`, `log₂ 117 ≤ 55/8` (`117^8 ≤ 2^55`) and
  `117 ln 2 ≥ 80` — margin at `x = 117`: `160.66` vs `160.5`, as the manuscript's `43.66` vs
  `43.48`; `cap_const`: `18432·1.37317^4 ≈ 65534.8 ≤ 65536` (tight, `norm_num`). `cap_graph`
  clears the denominator with `log₂ m > 0` and rewrites `(2^{-5})²/18 = 1/18432`. The proof
  file's `cap_uniform` uses the same argument with `B' = 2^16 T (x+40)^4`.

## 7. Hygiene

* Both Spec files: `module`, `public import`, `@[expose] public section`; both Proof files:
  `public section`. Every formalizing declaration has a docstring starting with its label
  (`[s2:lemCap]`, `[s1:citLem25]`), and the quoted manuscript text in the docstrings is
  accurate (compared with s2.tex l.622–669 and s1.tex l.716–719).
* No `set_option`, no `maxHeartbeats`, no forbidden constructs (`lint.py`: 0 findings).
* Roots: `EG.lean` imports `EG.Spec.HB.Cap`, `EG.Spec.Ext.BMLemma25`, `EG.Proof.HB.Cap`,
  `EG.Proof.Ext.BMLemma25`, `EG.Lib.Found.LogMono`; `EGTest.lean` imports `EGTest.Cap`.
* `LOCK.json` has no entry yet for the two Spec files (expected: locking follows approval).
* CONVENTIONS.md's T0 record contains T0-cap-1 with the correct content.

## 8. Notes (non-blocking)

* **N1.** `CapStatement` keeps the unused hypothesis `m ≥ 2^40` verbatim; consumers who lack it
  can use `EG.cap_of_T_ge` (Proof file, same conclusion without it). Correct choice for a locked
  statement.
* **N2.** `CapUniformStatement` is "(Remark, not used)"; nothing downstream should cite it.
* **N3.** For the later `bmLemma25` proof task: the two facts the B–M text leaves implicit and
  the Lean proof will need are `ε ≤ log² m` for any `(ε,0)`-expander on `m ≥ 2` vertices (via
  `|U| = ⌈m/2⌉`), and `a = ε²m/(18 log⁴ m) ≥ 23` under the hypotheses (§5). Integer rounding in
  the `X, Y, Z` split has ample slack (`|P|/3 ≥ 2a ≥ a + 23`).
* **N4.** Part (ii) of [s2:lemCap] is correctly not formalized here; when the hierarchy exists,
  (ii) is `cap_graph` applied to the piece's graph plus `2^16 T log⁴ T ≤ M_l` from (R2), the
  transport of a cycle of the piece to `G'_l` (edge-set inclusion), and Γ2(a) for `T ≥ 2^117`.
* **N5.** The docstring of `CapGraphStatement` says "no cycle of length at least `T` is said of
  the expander `G` itself"; this is the weaker hypothesis (§4), so the direction is safe.
