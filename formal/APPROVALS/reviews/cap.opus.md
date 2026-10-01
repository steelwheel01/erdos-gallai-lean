# Clean-room review: group `cap`, reviewer `opus`

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent clean-room agent. I reviewed from
scratch. I read only repository files and edited none; this review is the one file I wrote. I
formed my verdict before skimming the first 80 lines of `work/p1b/cap.review1.md` as a
cross-check, and nothing in this review depends on it.

Scratch files (compiled with `lake env lean` from `formal/`, both with 0 errors and 0 warnings):
* `/tmp/capreview/Print.lean` prints the four Spec definitions with `pp.parens`, `pp.universes`
  and `pp.funBinderTypes`, checks the types of `EG.cap`, `EG.cap_uniform`, `EG.cap_graph` and
  `EG.bmLemma25`, and prints the axioms of `cap`, `cap_uniform`, `bmLemma25_literal_false`,
  `cap_graph`.
* `/tmp/capreview/Extra.lean` holds the independent tests (a)–(h) listed in §5.

Scope:
* `EG/Spec/HB/Cap.lean`: `EG.Spec.CapStatement` (s2:lemCap (i)), `EG.Spec.CapUniformStatement`
  (the remark after s2:lemCap), `EG.Spec.CapGraphStatement` (graph-level step of the proof of
  s2:lemCap (ii)); proofs in `EG/Proof/HB/Cap.lean`.
* `EG/Spec/Ext/BMLemma25.lean`: `EG.Spec.BMLemma25Statement` (s1:citLem25), with the T0
  deviation T0-cap-1 (extra hypothesis `2 ≤ m`); proof `EG.bmLemma25` is `sorry` by design.
* Dependencies re-read to interpret the statements (reviewed in other groups): `EG.FGraph`,
  `FGraph.card`, `nbrSet`, `deleteEdges` (`EG/Defs/Graph.lean`), `FGraph.IsExpander`
  (`EG/Defs/Expander.lean`), `EG.cycleEdges`, `EG.Obj.WF` (`EG/Defs/Objects.lean`).

**Overall verdict: APPROVE, with notes.** All four statements match the manuscript text they
formalize, including edge cases, log base, strict/non-strict inequalities and constants. The one
deviation, `2 ≤ m` in `BMLemma25Statement`, is necessary (the literal reading is false, proved in
Lean) and harmless (it removes exactly the instances with `m = 1`, and it is implied by the other
hypotheses whenever `ε < 2^15`, in particular at the only use `ε = 2^{-5}`). I also checked that
`BMLemma25Statement` is true (§3.4), so the `sorry` can be filled. The notes N1–N5 are not
defects.

---

## 1. Manuscript text

* `s1.tex` l. 328, Convention s1:convGraphs (b): "$\log=\log_2$ throughout, as in [BM, l. 141].
  We put $\log^{[0]}x\defeq x$ and $\log^{[k]}x\defeq\log(\log^{[k-1]}x)$". So `log⁴ m` is the
  4th power (iterates are written `log^{[k]}`). (a): "$|H|\defeq|V(H)|$".
* `s1.tex` l. 497–509, s1:citDef11: "An $n$-vertex graph $G$ is an $(\varepsilon,s)$-expander if
  for every $U\subseteq V(G)$ and every $F\subseteq E(G)$ with $1\le|U|\le2n/3$ and $|F|\le
  s|U|$ we have $|\Nbr_{G-F}(U)|\ge\varepsilon|U|/\log^2n$."
* `s1.tex` l. 716–719, s1:citLem25: "Let $\varepsilon\ge2^{-5}$ and $m\ge2^{30}/\varepsilon^2$
  (so $m\ge2^{40}$ suffices at $\varepsilon=2^{-5}$). Every $m$-vertex
  $(\varepsilon,0)$-expander contains a cycle of length at least
  $\varepsilon^2m/(18\log^4m)$." The following paragraph (l. 721–733) sketches the DFS proof
  with segments $X,Y,Z$, $|X|,|Z|\ge|P|/3$,
  $\varepsilon^2m/(18\log^4m)\le|Y|<\varepsilon^2m/(9\log^4m)$.
* B–M, `papers/2211.07689.txt` l. 1510–1511: "Lemma 25. Any n-vertex (ε, 0)-expander, with
  ε ≥ 2−5 and n ≥ 230/ε2, contains a cycle of length Ω(n/log4 n)." Proof l. 1512–1558 (I
  re-derived it, §3.4).
* `s2.tex` l. 622–637, s2:lemCap: "(i) If $m\ge2^{40}$, $T\ge2^{117}$ and $m<18432\,T\log^4m$,
  then $m\le2^{16}T\log^4T$. (ii) In every round $l\le R$ of a valid $\HBtp$ run, every $s=0$
  piece $\piece$ satisfies $|\piece|\le M_l$. […] *Remark (not used).* Part (i) is false for
  small $T$: for $T=2^{20}$ and $m=2^{55}$ […]. The uniform form
  $m\le\max(2^{40},2^{16}T(\log T+40)^4)$ holds for all $T\ge1$."
* `s2.tex` l. 662–669, proof of (ii): "Let $\piece$ be an $s=0$ piece and $m\defeq|\piece|$. If
  $m<2^{40}$ then $m\le M_l$. Otherwise the graph of $\piece$ is an $(\eps,0)$-expander (the
  stopping rule in (R3)) with $\eps=2^{-5}$ on $m\ge2^{40}=2^{30}/\eps^2$ vertices, so by Cited
  result s1:citLem25 it contains a cycle of length at least
  $\eps^2m/(18\log^4m)=m/(18432\log^4m)$. This cycle lies in $G'_l$, which has no cycle of length
  at least $T$ by (R1). Hence $m<18432\,T\log^4m$, and (i) gives $m\le2^{16}T\log^4T\le M_l$."
* v6 work notes (`proofs/manuscript/v6work/R6.md` l. 411): "s2.tex:622–674, s2:lemCap. […]
  Unchanged." No v6 change touches s1:citLem25's statement.

## 2. Parsed Lean statements (`pp.parens`)

* `CapStatement`: `∀ m T : ℝ, 2^40 ≤ m → 2^117 ≤ T → m < (18432 * T) * (logb 2 m)^4 →
  m ≤ (2^16 * T) * (logb 2 T)^4`.
* `CapUniformStatement`: `∀ m T : ℝ, 1 ≤ T → m < (18432 * T) * (logb 2 m)^4 →
  m ≤ max (2^40) ((2^16 * T) * (logb 2 T + 40)^4)`.
* `CapGraphStatement.{u}`: `∀ (V : Type u) [DecidableEq V] (G : FGraph V) (T : ℝ), 2^117 ≤ T →
  2^40 ≤ (↑G.card : ℝ) → G.IsExpander (2^(-5 : ℤ)) 0 → (∀ c : List V, (Obj.cycle c).WF →
  (∀ e ∈ cycleEdges c, e ∈ G.edges) → (↑c.length : ℝ) < T) → ↑G.card ≤ (2^16 * T) * (logb 2 T)^4`.
* `BMLemma25Statement.{u}`: `∀ (V : Type u) [DecidableEq V] (G : FGraph V) (ε : ℝ),
  2^(-5 : ℤ) ≤ ε → 2^30 / ε^2 ≤ ↑G.card → 2 ≤ G.card (in ℕ) → G.IsExpander ε 0 →
  ∃ c : List V, (Obj.cycle c).WF ∧ (∀ e ∈ cycleEdges c, e ∈ G.edges) ∧
  (ε^2 * ↑G.card) / (18 * (logb 2 ↑G.card)^4) ≤ ↑c.length`.

All numerals are real; `2^(-5 : ℤ)` is the real zpow `1/32`; function application binds tighter
than `^`, so every `logb 2 x ^ 4` is `(log₂ x)^4`.

## 3. Back-translation and comparison

### 3.1 `CapStatement` vs s2:lemCap (i)

Back-translation: for all real numbers `m, T`, if `m ≥ 2^40`, `T ≥ 2^117` and
`m < 18432·T·(log₂ m)^4`, then `m ≤ 2^16·T·(log₂ T)^4`.

| Item | Lean | Manuscript | OK |
|---|---|---|---|
| domain of `m`, `T` | `ℝ` | unspecified numbers (in (ii): `m = |𝒫| ∈ ℕ`, `T = d_l log² d_l ∈ ℝ`) | yes; real `m` covers the integer use |
| `m ≥ 2^40` | `2^40 ≤ m` | non-strict | yes |
| `T ≥ 2^117` | `2^117 ≤ T` | non-strict | yes |
| hypothesis | `m < 18432*T*logb 2 m^4` | strict `<` | yes |
| conclusion | `m ≤ 2^16*T*logb 2 T^4` | non-strict `≤` | yes |
| log | `Real.logb 2`, 4th power | `log = log₂`, `log⁴` a power | yes |
| Lean conventions | `m, T ≥ 2^40 > 1`, so `logb` is at positive arguments > 1; no `ℕ` subtraction, no division | — | no effect |

Verbatim. Non-vacuity: hypotheses satisfiable (`m = 2^40`, `T = 2^117`; `EGTest/Cap.lean`), the
hypothesis `m < 18432 T log⁴ m` is load-bearing (`m = 2^200`), and the threshold `T ≥ 2^117`
is load-bearing (with `T ≥ 2^20` the statement is false by `cap_remark_counterexample`). The
proof `EG.cap` is sorry-free and proves exactly `EG.Spec.CapStatement` (via `cap_of_T_ge`,
which drops the unused `m ≥ 2^40`; that is a strengthening inside the proof, not a change of
the Spec).

### 3.2 `CapUniformStatement` vs the Remark

The remark says "the uniform form `m ≤ max(2^40, 2^16 T (log T + 40)^4)` holds for all
`T ≥ 1`", implicitly under the hypothesis `m < 18432 T log⁴ m` of (i) (and possibly
`m ≥ 2^40`). Lean: for all real `m, T` with `1 ≤ T` and `m < 18432 T log⁴ m`,
`m ≤ max(2^40, 2^16 T (log₂ T + 40)^4)`.

Omitting `m ≥ 2^40` gives a logically equivalent statement: for `m < 2^40` the conclusion is
trivial. I proved the equivalence in Lean (test (h)). For `m ≤ 0`, `Real.logb 2 m` is
`log₂ |m|` (and `0` at `m = 0`), but these `m` are in the trivial range, so Lean's conventions do
not change the meaning. `T ≥ 1` makes `log₂ T ≥ 0`. Hypotheses satisfiable (`m = 2^30`, `T = 1`,
test (d)); hypothesis load-bearing (`EGTest/Cap.lean`, `m = 2^200`, `T = 1`). `EG.cap_uniform`
is sorry-free. (The remark is marked "not used"; this Spec is harmless either way.)

### 3.3 `CapGraphStatement` vs the graph step of s2:lemCap (ii)

Back-translation: for every finite simple graph `G` (explicit vertex set, any type, any
universe) with `m = |V(G)| ≥ 2^40` that is a `(2^{-5},0)`-expander (Def 11, `log₂`, `n = m`),
and every real `T ≥ 2^117` such that every cycle of `G` has length `< T`, we have
`m ≤ 2^16 T (log₂ T)^4`.

* "cycle of `G`": a vertex list `c`, `Nodup`, `|c| ≥ 3`, with all edges
  `c₀c₁, …, c_{k-1}c₀` in `E(G)`. For such `c` the `k = |c|` edges are distinct non-loops, so
  this is exactly a cycle subgraph of length `k`, and `c.length` is its length. The closing edge
  is included (`EGTest/Cap.lean` checks `cycleEdges [1,2,3]`).
* "no cycle of length at least `T`" ↔ "every cycle has length `< T`": correct negation, strict.
* The manuscript's hypothesis is on `G'_l ⊇` the graph of `𝒫`; stating it for `G` itself is the
  weaker hypothesis the argument actually needs, and it follows from the `G'_l` version by
  `E(G) ⊆ E(G'_l)` (see N3).
* The case `m < 2^40` of (ii) is handled in the manuscript by `M_l ≥ 2^40`, so requiring
  `m ≥ 2^40` matches "Otherwise".
* `ε = 2^{-5}`: `2^30/ε² = 2^40` exactly (checked by `norm_num` in the proof).

This is precisely the manuscript's chain "Lemma 25 ⇒ `m < 18432 T log⁴ m` ⇒ (i)". I re-proved
`BMLemma25Statement ∧ CapStatement → CapGraphStatement` independently in test (g), so the Spec
asks for nothing beyond those two inputs. Non-vacuity: hypotheses jointly satisfiable
(`K_{2^40}`, `T = 2^117`) and the no-long-cycle hypothesis load-bearing (`K_{2^200}`), both in
`EGTest/Cap.lean`. `EG.cap_graph` proves exactly `CapGraphStatement.{u}` for every `u`; it
depends on `sorryAx` only through `EG.bmLemma25`.

### 3.4 `BMLemma25Statement` vs s1:citLem25

| Item | Lean | Manuscript | OK |
|---|---|---|---|
| `ε` | real, `2^(-5:ℤ) ≤ ε` | `ε ≥ 2^{-5}` | yes |
| size | `2^30/ε^2 ≤ G.card` | `m ≥ 2^{30}/ε²` | yes (`ε > 0`, no division by 0) |
| `m`-vertex | `m = G.card = |verts|` | `|G| = |V(G)|` | yes |
| expander | `G.IsExpander ε 0` | `(ε,0)`-expander | yes (`s = 0` forces `F = ∅`) |
| cycle, length | `Obj.WF` + edges in `E(G)`, `c.length` | "contains a cycle of length …" | yes (vertices lie in `V(G)` by `edge_verts`) |
| bound | `ε^2*m/(18*logb 2 m^4) ≤ c.length` | "at least `ε²m/(18 log⁴m)`" | yes (non-strict) |
| log | `Real.logb 2`, 4th power | `log₂`, power | yes |
| **extra** | `2 ≤ G.card` | absent | T0-cap-1, see below |

**Is the deviation necessary?** Yes. At `m = 1` the manuscript's bound has `log 1 = 0` and is
undefined. With `ε = 2^15`: `2^30/ε² = 1 ≤ m`, the one-vertex graph is vacuously an
`(ε,0)`-expander (no `U` with `1 ≤ |U| ≤ 2/3`), and it has no cycle. Any encoding of "contains
a cycle" is then false, whatever value the bound takes (Lean's `x/0 = 0`, `+∞`, or the
multiplied-out `ε²m ≤ 18 log⁴m · |c|`). `EG.bmLemma25_literal_false` proves the literal Lean
version false in every universe; `#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound`.

**Is it minimal and harmless?** Yes.
* `m = 0` is excluded by `2^30/ε² ≤ m` (`ε > 0`), so the hypotheses force `m ≥ 1` (test (a)).
  So `2 ≤ m` removes exactly the instances with `m = 1`. Test (c) proves that
  `BMLemma25Statement` is equivalent to the literal statement with the hypothesis `m ≠ 1`.
* For `ε < 2^15`, `2^30/ε² > 1`, so `2 ≤ m` follows from the other hypotheses (test (b)). In
  particular at `ε = 2^{-5}`, the only use (s2:lemCap (ii); `s1.tex` l. 764 "Lemma 25 …
  Lemma s2:lemCap"), the added hypothesis is redundant. `cap_graph` discharges it from
  `m ≥ 2^40`.
* The B–M original (`Ω(n/log⁴n)`) is equally undefined at `n = 1`; the deviation does not
  change the mathematical content.
* The T0 entry in `formal/CONVENTIONS.md` ("T0-cap-1 | s1:citLem25 | `BMLemma25Statement` adds
  `2 ≤ m` … | 'Let ε ≥ 2^{-5} and m ≥ max(2, 2^{30}/ε²)'") matches the Lean and the docstrings.

**Is the fixed statement true?** The `sorry` must be fillable, so I re-derived the B–M proof
with the explicit constant. Write `L = log₂ m`, `a = ε²m/(18L⁴)`, and assume `m ≥ 2`.
1. `ε ≤ L²`: take `U ⊆ V(G)` with `|U| = ⌈m/2⌉ ≤ 2m/3` and `F = ∅`. Then
   `εU/L² ≤ |N(U)| ≤ m − ⌈m/2⌉ ≤ |U|`.
2. `a ≥ 23.3`: from `ε²m ≥ 2^30`, `a ≥ 2^30/(18L⁴)`; from `ε ≥ 2^{-5}`,
   `a ≥ 2^{L−10}/(18L⁴)`. The first bound decreases in `L` and the second increases for
   `L > 4/ln 2`, and both equal `2^30/(18·40⁴) ≈ 23.30` at `L = 40`.
3. `G` is connected (a component of size `≤ m/2` has empty neighbourhood, contradicting
   expansion with `ε > 0`, `L > 0`). Run the DFS. At the moment `|U| = |R| = k`,
   `N(U) ⊆ P` and `|P| = m − 2k`. If `k ≥ m/3`, expansion gives `|P| ≥ εk/L² ≥ εm/(3L²)`. If
   `k < m/3` (including `k = 0`), `|P| > m/3 ≥ εm/(3L²)` by step 1.
4. `a = (ε/(6L²))·εm/(3L²) ≤ |P|/6`. Take `|X| = ⌈|P|/3⌉`, `|Y| = ⌈a⌉`, `Z` the rest. Then
   `a ≤ |Y| < a + 1 ≤ 2a`, and `|Z| ≥ |P|/3` because `|P|/3 ≥ 2a ≥ a + 2`.
5. If a shortest `X–Z` path `Q` exists in `G − Y`, its interior avoids `P`, and `Q` plus the
   segment of `P` between its ends is a cycle of length `≥ |Y| + 2 > a`. Otherwise there is a
   split `V(G)∖Y = X' ∪ Z'` with no edges between the parts, `X ⊆ X'`, `Z ⊆ Z'`. WLOG
   `|X'| ≤ m/2`. Then `N(X') ⊆ Y` and `|N(X')| ≥ ε|X|/L² ≥ ε|P|/(3L²) ≥ ε²m/(9L⁴) = 2a > |Y|`,
   a contradiction.

So the Lean statement (with `2 ≤ m`) is true. Non-vacuity: hypotheses jointly satisfiable
(`ε = 2^{-5}`, `K_{2^40}`, `EGTest/Cap.lean`). For `m ≥ 2` and `ε > 0` the bound is strictly
positive (test (f)), so a genuine cycle is required, and at `K_{2^40}` it is `> 23` (test (e)).

## 4. Lean conventions, implicit assumptions, hygiene

* `[DecidableEq V]` is universally quantified; `DecidableEq` is a subsingleton, so the choice of
  instance does not matter. `V : Type u` is arbitrary (possibly infinite); only `verts` matters.
* Universe polymorphism: `CapGraphStatement.{u}` and `BMLemma25Statement.{u}` are proved for
  every `u` (`EG.cap_graph.{u_1}`, `EG.bmLemma25.{u_1}`).
* `IsExpander ε 0` with `ε ≥ 2^{-5} > 0` and `m ≥ 2`: CONVENTIONS' caveats ("trivially true for
  `ε ≤ 0` and for `n ≤ 1`") are respected in both graph statements.
* No `ℕ` subtraction and no `ℕ` division occur. The only real divisions have positive
  denominators (`ε² > 0`; `18 log⁴ m > 0` for `m ≥ 2`).
* The Spec files import only `EG.Defs.Expander` and `EG.Defs.Objects`, and use `@[expose] public
  section`.
* `lake build --no-build` on the five modules and `EGTest.Cap`: all targets up to date (the only
  warning is the allowed `sorry` at `EG/Proof/Ext/BMLemma25.lean:23`).
* Axiom scan: `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.HB.Cap
  EG.Proof.Ext.BMLemma25 EG.Spec.HB.Cap EG.Spec.Ext.BMLemma25 EG.Lib.Found.LogMono` gives
  "inspected 150 constants under [EG]; 2 use sorryAx; 0 violations". The two are `EG.bmLemma25`
  (by design) and `EG.cap_graph` (through it). `EG.cap`, `EG.cap_uniform`,
  `EG.bmLemma25_literal_false`: `propext`, `Classical.choice`, `Quot.sound` only.
* `python3 scripts/lint.py`: 0 findings. All five modules are in `EG.lean`; `EGTest.Cap` is in
  `EGTest.lean`.

## 5. Scratch tests (`/tmp/capreview/Extra.lean`, all compile)

* (a) The hypotheses of `BMLemma25Statement` without `2 ≤ m` imply `1 ≤ m`.
* (b) If also `ε < 2^15`, they imply `2 ≤ m`.
* (c) `BMLemma25Statement.{0}` ↔ the literal statement with the extra hypothesis `m ≠ 1`.
* (d) `CapUniformStatement`'s hypotheses are satisfiable (`m = 2^30`, `T = 1`).
* (e) At `K_{2^40}`, `ε = 2^{-5}`, the required cycle length is `> 23`.
* (f) For `m ≥ 2`, `ε > 0`, the bound `ε²m/(18 log⁴m)` is `> 0`.
* (g) `BMLemma25Statement.{0} → CapStatement → CapGraphStatement.{0}`, re-proved independently.
* (h) `CapUniformStatement` ↔ its reading with the extra hypothesis `2^40 ≤ m`.

## 6. Notes (none is a defect)

* **N1.** The Spec docstrings describe the statements accurately. The docstring of
  `EG/Spec/Ext/BMLemma25.lean` still points to `formal/work/p1b/cap.md` "for the central T0
  record". The central record is now `formal/CONVENTIONS.md` (entry T0-cap-1 is there). This is
  cosmetic and does not affect the locked `def`.
* **N2.** The explicit constant `18` in s1:citLem25 comes from the manuscript's reading of the
  B–M proof, not from the B–M statement (`Ω(n/log⁴n)`). I checked it (§3.4). The later proof
  task needs the rounding facts `ε ≤ log²m` and `a ≥ 23.3` from steps 1–2, which B–M leave
  implicit.
* **N3.** For the future formalization of s2:lemCap (ii): (R1) must be stated with the same cycle
  notion (`Obj.cycle` list cycles with edges in `E(G'_l)`), or a bridge lemma must convert it,
  to discharge `CapGraphStatement`'s cycle hypothesis by `E(graph of 𝒫) ⊆ E(G'_l)`. It also
  needs `T = d_l log² d_l ≥ 2^117` from Γ2(a)/G2(a). Neither affects the present statements.
* **N4.** `CapStatement` keeps the unused hypothesis `m ≥ 2^40` verbatim; `CapUniformStatement`
  drops it (equivalent, test (h)). Both choices are faithful.
* **N5.** `CapStatement` and `CapUniformStatement` quantify over real `m`, which is more general
  than the integer `m = |𝒫|` of (ii) and is the natural reading of (i) as a numerical lemma.

## 7. Verdicts

| Statement | Verdict |
|---|---|
| `EG.Spec.CapStatement` | approve |
| `EG.Spec.CapUniformStatement` | approve |
| `EG.Spec.CapGraphStatement` | approve |
| `EG.Spec.BMLemma25Statement` (with T0-cap-1) | approve-with-notes (N1, N2) |

Overall: **APPROVE, with notes.** No blocking issue.
