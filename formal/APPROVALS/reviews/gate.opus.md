# Clean-room review: group `gate`, reviewer `opus`

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent clean-room agent. I reviewed from
scratch. I did not read earlier approvals or `work/p1b/gate*.md`. I only read repository files;
this review is the one file I wrote.

Scratch files (compiled with `lake env lean` from `formal/`):
* `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/GatePrint.lean`
  prints every definition and both statements with `pp.fullNames`, `pp.parens`, `pp.coercions`
  and `pp.universes`, checks the types of `EG.gate` / `EG.gate_precise`, and prints their axioms.
* `/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/GateReviewOpus.lean`
  holds independent tests. It compiles with 0 errors and 0 warnings. `#print axioms` on its
  theorems gives only `propext`, `Classical.choice` and `Quot.sound`.

Scope:
* `EG/Defs/Orient.lean`: `cycleArcs`, `IsOrientation`, `outDeg`, `inDeg`, `IsBalanced`,
  `walkArcs`, `IsDirPathIn`, `IsDirCycle`, `IsAcyclic`, and the two `Decidable` instances.
* `EG/Spec/Chain/Gate.lean`: `EG.Spec.GateStatement`, `EG.Spec.GatePreciseStatement`.
* A skim of `EG/Proof/Chain/Gate.lean`.

Dependencies used but outside this scope (reviewed in other groups): `EG.FGraph`
(`EG/Defs/Graph.lean`), `EG.Obj`, `EG.Obj.edges`, `EG.Obj.WF`, `EG.cycleEdges`, `EG.IsDecomp`
(`EG/Defs/Objects.lean`). I re-read them to interpret the statements.

**Overall verdict: APPROVE, with notes.** Every definition and both statements match the
manuscript, including in the edge cases. The notes (N1 to N8 at the end) are redundancies and
conventions for later `Spec` authors. None of them is a defect.

---

## Manuscript text

* `s6.tex` l. 12 (preamble of Section 6): "Throughout, $G$ is the input graph
  (Convention~\ref{s1:convGraphs}). Orientations, directed paths and directed cycles are those of
  digraphs obtained by orienting edges of $G$; each edge receives exactly one direction. A digraph
  is \emph{acyclic} if it has no directed cycle."
* `s6.tex` l. 16–19, Lemma GATE [s6:lemGATE]: "Let $F\subseteq E(G)$ and let $\vec F$ be an
  orientation of $F$ with $d^+_{\vec F}(v)=d^-_{\vec F}(v)$ at every vertex $v$. Let $\mathcal W$
  be a set of arcs of $\vec F$ such that $\vec F-\mathcal W$ is acyclic. Then $F$ decomposes into
  at most $|\mathcal W|$ cycles of $G$. More precisely, $\vec F$ is the arc-disjoint union of
  directed cycles, each of length at least $3$, each the orientation of a cycle of $G$, and each
  containing an arc of $\mathcal W$; there are at most $|\mathcal W|$ of them."
  `\deps{\ref{s1:defObject}}`.
* Proof of GATE (l. 21–33): "let $v_0\to v_1\to\dots\to v_k$ ($k\ge1$) be a directed path in
  $\vec F$ with pairwise distinct vertices … So $C:=v_i\to\dots\to v_k\to v_i$ is a directed
  cycle with distinct vertices, of length $k-i+1\ge2$. … the arcs $v_{k-1}\to v_k$ and
  $v_k\to v_{k-1}$. These arcs come from two distinct edges of $F$ with the same ends, which is
  impossible since $G$ is simple. … Their underlying cycles partition $F$, so they form a
  decomposition of $F$ into cycles in the sense of Definition~\ref{s1:defObject}. … The $C_i$
  are arc-disjoint, so $p\le|\mathcal W|$."
* `s1.tex` [s1:defObject]: "An \emph{object} is a cycle (of length at least $3$) or a single
  edge. A \emph{decomposition} of an edge set $F$ is a partition of $F$ into the edge sets of
  objects".
* Consumer, `s6.tex` l. 216 ([s6:lemHCCP] Step 4): "By Lemma~\ref{s6:lemGATE}, $F$ decomposes
  into at most $|\mathcal W|=\Phi$ cycles of $G$. Each of them is the orientation of a directed
  cycle $C$ of $\vec F$ of length at least $3$ containing an arc of $\mathcal W$."

---

## `EG/Defs/Orient.lean`

Elaborated forms (from `GatePrint.lean`) agree with the source. All definitions are universe
polymorphic in `V : Type u_1`; only `outDeg`, `inDeg` and `IsBalanced` take `[DecidableEq V]`.

### `cycleArcs c := List.zip c (c.rotate 1)`
* Back-translation: for `c = [c₀, …, c_{k-1}]`, the list
  `[(c₀,c₁), (c₁,c₂), …, (c_{k-2},c_{k-1}), (c_{k-1},c₀)]`: the arcs of the closed directed walk
  `c₀ → c₁ → … → c_{k-1} → c₀`. `c.rotate 1 = [c₁, …, c_{k-1}, c₀]` has the same length, so `zip`
  drops nothing.
* Edge cases: `[] ↦ []`, `[v] ↦ [(v,v)]` (a loop), `[u,v] ↦ [(u,v),(v,u)]`.
* Consistency: `cycleEdges c = (cycleArcs c).map (fun a => s(a.1,a.2))`, so the undirected
  cycle of the vertex list `c` is exactly the underlying edge list of its arcs.
* Tests: `cycleArcs [1,2,3] = [(1,2),(2,3),(3,1)]`, `cycleArcs [5] = [(5,5)]`,
  `cycleArcs [] = []` (all `decide`); the `cycleEdges` identity is proved for all `c`.
* Verdict: **approve**.

### `IsOrientation F A`
* Back-translation: the arc set `A ⊆ V × V` satisfies (i) no arc is a loop; (ii) every arc
  `(u,v) ∈ A` has `{u,v} ∈ F`; (iii) for every `e ∈ F` there is exactly one arc `a ∈ A` with
  underlying edge `e`.
* Manuscript: "an orientation of $F$", "each edge receives exactly one direction". (ii) and
  (iii) say that `a ↦ s(a.1,a.2)` is a bijection `A → F`, so `A` picks exactly one of
  `(u,v)`, `(v,u)` for every edge `uv ∈ F` and nothing else. That is the manuscript notion.
* Multiplicities: `A` is a `Finset`, so two parallel arcs cannot occur. For an orientation of an
  edge set of the simple graph `G` there are none anyway (distinct edges have distinct pairs of
  ends).
* Loops: (i) is redundant when `F` is loopless (every `F ⊆ G.edges` is). When `F` contains a
  loop, `IsOrientation F A` is unsatisfiable (test: `¬ IsOrientation {s(0,0)} A` for every `A`).
  This is consistent with "orienting edges of $G$", since $G$ is loopless.
* Tests: the cyclic triangle `{(0,1),(1,2),(2,0)}` is an orientation of
  `{s(0,1),s(1,2),s(2,0)}` on `Fin 3`; `{(0,1),(1,0)}` (both directions) is not an orientation of
  `{s(0,1)}`; `∅` is not an orientation of `{s(0,1)}`; `{(0,1),(1,2)}` (arc outside `F`) is not
  an orientation of `{s(0,1)}`.
* Verdict: **approve**.

### `outDeg A v := #{a ∈ A | a.1 = v}`, `inDeg A v := #{a ∈ A | a.2 = v}`
* Back-translation: `d⁺(v)` is the number of arcs with tail `v`, `d⁻(v)` the number with head
  `v`. Arcs are distinct elements of a `Finset`, so each arc is counted once. A loop `(v,v)`
  would count once in each (irrelevant: orientations have no loops).
* The `DecidableEq V` instance only feeds `Finset.filter`; the cardinality does not depend on
  which instance is used.
* Tests: `outDeg triA 0 = 1 ∧ inDeg triA 0 = 1`; for `{(0,1),(0,2)}`, `outDeg _ 0 = 2` and
  `inDeg _ 0 = 0` (direction is the right way round).
* Verdict: **approve**.

### `IsBalanced A := ∀ v, outDeg A v = inDeg A v`
* Back-translation: `d⁺(v) = d⁻(v)` for every `v : V`.
* Manuscript: "$d^+_{\vec F}(v)=d^-_{\vec F}(v)$ at every vertex $v$". The formal version
  quantifies over all of `V`, not only `V(G)`. That is harmless: I proved (test §7) that if
  `F ⊆ G.edges`, `IsOrientation F A` and `v ∉ G.verts`, then `outDeg A v = inDeg A v = 0`.
* Tests: the cyclic triangle is balanced; after erasing one arc it is not.
* Verdict: **approve**.

### `walkArcs p := List.zip p p.tail`
* Back-translation: for `p = [v₀, …, v_k]`, the list `[(v₀,v₁), …, (v_{k-1},v_k)]`; empty when
  `p` has at most one vertex. It is the directed counterpart of `walkEdges`.
* Tests: `walkArcs [1,2,3] = [(1,2),(2,3)]`, `walkArcs [1] = []`, `walkArcs [] = []`.
* Verdict: **approve**.

### `IsDirPathIn A p := p ≠ [] ∧ p.Nodup ∧ ∀ a ∈ walkArcs p, a ∈ A`
* Back-translation: `p = v₀ … v_k` is a directed path of the digraph `A`: at least one vertex,
  pairwise distinct vertices, and every arc `v_j → v_{j+1}` is in `A`. Its length is `k`.
* Manuscript: the standard notion. The GATE proof uses "a directed path in $\vec F$ with
  pairwise distinct vertices". The definition matches, and it allows the trivial path `[v]`.
* Edge case (documented in the docstring): `IsDirPathIn A [v]` holds for every `A` and every `v`,
  also when `v` meets no arc. Test: `IsDirPathIn ∅ [7]`. Also: `[0,1]` is a path of `{(0,1)}`,
  `[1,0]` is not (direction matters), `[0,1,0]` is not a path of `{(0,1),(1,0)}` (repeated
  vertex), and `[]` is never a path.
* No statement in `EG/Spec/**` uses it at present (grep), so it cannot currently change the
  meaning of any locked statement.
* Verdict: **approve** (see N5).

### `IsDirCycle A c := c ≠ [] ∧ c.Nodup ∧ ∀ a ∈ cycleArcs c, a ∈ A`
* Back-translation: `c = c₀ … c_{k-1}`, `k ≥ 1`, pairwise distinct vertices, all arcs
  `c₀ → c₁ → … → c_{k-1} → c₀` in `A`. The length is `k`.
* Manuscript: "directed cycle" in the standard sense ("a directed cycle with distinct vertices").
  Formally a loop `[v]` (if `(v,v) ∈ A`) and a 2-cycle `[u,v]` (if both `(u,v), (v,u) ∈ A`) are
  directed cycles. That is the usual digraph convention. It does not matter for orientations:
  test §8 proves that every directed cycle of any `B ⊆ A`, where `A` is an orientation, has
  length `≥ 3`. So for `A \ W` the formal and the manuscript notion of "directed cycle" coincide.
* A cycle has several list representations (rotations). This is harmless: `IsAcyclic`
  quantifies over all lists, and GATE's conclusions are existential.
* Tests: `[0,1]` is a directed cycle of `{(0,1),(1,0)}`; `[0]` of `{(0,0)}`; `[1,2,0]` of the
  cyclic triangle, but `[0,2,1]` (wrong direction) is not; `[0,1,2,0]` (repeated vertex) is not;
  `[]` is not.
* Verdict: **approve**.

### `IsAcyclic A := ∀ c, ¬ IsDirCycle A c`
* Back-translation: `A` has no directed cycle (of any length `≥ 1`).
* Manuscript: "A digraph is \emph{acyclic} if it has no directed cycle." This is the literal
  definition. Requiring distinct vertices in the cycle does not change the notion, since a
  digraph with a closed directed walk has a directed cycle. The quantifier ranges over all
  `c : List V`, including vertices that meet no arc. That is harmless, since a non-empty `c`
  whose arcs lie in `A` only uses ends of arcs.
* Non-vacuity: `IsAcyclic (triA \ {(2,0)})` is proved (with an independent potential argument:
  if every arc strictly increases `φ : V → ℕ`, then `A` is acyclic), and `¬ IsAcyclic triA`
  (witness `[0,1,2]`).
* Verdict: **approve**.

### `Decidable` instances
* Both are `inferInstanceAs (Decidable (_ ∧ _ ∧ _))` on the literal bodies, so they carry no
  semantic content. They reduce under `decide` (the tests above use them).
* Verdict: **approve**.

---

## `EG/Spec/Chain/Gate.lean`

Both statements are `Prop`-valued `def`s with one universe parameter `u`. They quantify over
`V : Type u`, an arbitrary `DecidableEq V` instance, `G : FGraph V`, `F : Finset (Sym2 V)` and
`A W : Finset (V × V)`. All names resolve to the intended constants (checked with
`pp.fullNames`: `EG.IsOrientation`, `EG.IsBalanced`, `EG.IsAcyclic`, `EG.IsDecomp`,
`EG.Obj.cycle`, `EG.Obj.edges`, `EG.FGraph.edges`, `EG.IsDirCycle`, `EG.Obj.WF`,
`EG.cycleEdges`, `EG.cycleArcs`; `A \ W` is `SDiff.sdiff A W`; `(F : Set _)` is the `Finset`
coercion).

### Hypotheses (shared by both statements)

| manuscript | formal | comment |
|---|---|---|
| $F\subseteq E(G)$ | `F ⊆ G.edges` | exact |
| $\vec F$ an orientation of $F$ | `IsOrientation F A` | exact (see above) |
| $d^+_{\vec F}(v)=d^-_{\vec F}(v)$ at every vertex | `IsBalanced A` | over all `v : V`; equivalent (test §7) |
| $\mathcal W$ a set of arcs of $\vec F$ | `W ⊆ A` | exact (not needed by the proof, see N3) |
| $\vec F-\mathcal W$ acyclic | `IsAcyclic (A \ W)` | exact; no loops or 2-cycles possible (test §8) |

No hypothesis is stronger than the manuscript's, so the formal statement is at least as strong
as the lemma. No hypothesis is missing (the manuscript's $G$ is a finite simple graph, which
`FGraph` is).

### `GateStatement`
* Back-translation: under the hypotheses there is a list `D` of objects such that `D` is a
  decomposition of `F` in the sense of `IsDecomp` (every object well formed; the edge lists of
  the objects are pairwise disjoint and duplicate free; their union is exactly `F`), `|D| ≤ |W|`,
  and every object of `D` is a cycle `Obj.cycle c` all of whose edges are edges of `G`.
* Manuscript: "Then $F$ decomposes into at most $|\mathcal W|$ cycles of $G$", with
  "decomposes" from [s1:defObject]. For `Obj.cycle c`, `WF` is `c.Nodup ∧ 3 ≤ c.length`, so each
  object is a cycle of length at least 3 with distinct vertices. Its edges are in `E(G)`, and
  their ends are in `V(G)` by `FGraph.edge_verts`: this is a cycle of `G`. "At most
  $|\mathcal W|$" is `D.length ≤ W.card`. Duplicate objects are impossible, since the
  concatenated edge list is duplicate free and every cycle has at least 3 edges. So `D.length` is
  the number of cycles.
* The conjunct `∀ e ∈ o.edges, e ∈ G.edges` follows from `IsDecomp` and `F ⊆ G.edges` (N2). It
  is harmless.
* Edge cases: `F = ∅` forces `A = ∅` (by `IsOrientation.mem`) and `W = ∅`; the conclusion holds
  with `D = []`, as in the manuscript (0 cycles). No ℕ subtraction, division, logarithm or
  rounding occurs.
* Non-vacuity (tests §5): on the cyclic triangle (`triG`, `triF`, `triA`, `W = {(2,0)}`) all
  five hypotheses are proved. `EG.gate` then yields a decomposition, and I derive that it has
  exactly one object. I also prove that `triF` has no decomposition into `≤ 0` objects, so the
  bound `≤ |W|` is not trivially satisfiable. With `W = ∅` the hypotheses fail on the triangle
  (`¬ IsAcyclic triA`), as they must.
* Verdict: **approve**.

### `GatePreciseStatement`
* Back-translation: under the hypotheses there is a list `cs` of vertex lists such that
  (a) every `c ∈ cs` is a directed cycle of `A`, has length `≥ 3`, is a well-formed cycle object,
  has all its undirected edges `cycleEdges c` in `G.edges`, and contains an arc of `W`;
  (b) the concatenation of the arc lists `cycleArcs c` (`c ∈ cs`) is duplicate free;
  (c) that concatenation contains exactly the arcs of `A`; (d) `cs.length ≤ W.card`.
* Manuscript: "$\vec F$ is the arc-disjoint union of directed cycles" is (b) + (c), where (b)
  also covers arc-disjointness inside one cycle, which follows from `c.Nodup` anyway. "Each of
  length at least 3" is `3 ≤ c.length`. "Each the orientation of a cycle of $G$": `c` is a cycle
  object of `G` (well formed, edges in `E(G)`) and its arcs are the arcs `cycleArcs c ⊆ A`, whose
  underlying edges are exactly `cycleEdges c` (identity checked above). So the directed cycle is
  an orientation of that cycle of `G`. "Each containing an arc of $\mathcal W$" is
  `∃ w ∈ W, w ∈ cycleArcs c`. "At most $|\mathcal W|$ of them" is (d); `cs` has no repeated
  entry by (b), so `cs.length` is the number of cycles.
* The statement is exactly the "More precisely" sentence. It also gives what [s6:lemHCCP] Step 4
  needs ("the orientation of a directed cycle $C$ of $\vec F$ of length at least $3$ containing
  an arc of $\mathcal W$"). The decomposition of `F` follows from (b), (c) and `IsOrientation`;
  the proof file does this in `isDecomp_map_cycle_of_arcs` and offers `gate_with_cycles`.
* `(EG.Obj.cycle c).WF` repeats `c.Nodup` (in `IsDirCycle`) and `3 ≤ c.length` (N1). It is
  harmless.
* Non-vacuity (tests §5): on the cyclic triangle, `EG.gate_precise` yields `cs` with exactly one
  member, and that member contains the arc `(2,0)`.
* Verdict: **approve**.

---

## `EG/Proof/Chain/Gate.lean` (skim)

* `theorem gate_precise : EG.Spec.GatePreciseStatement` and
  `theorem gate : EG.Spec.GateStatement` state the `Spec` constants themselves, with no
  auxiliary restatement. With `pp.fullNames`, `EG.gate.{u_1} : EG.Spec.GateStatement.{u_1}` and
  `EG.gate_precise.{u_1} : EG.Spec.GatePreciseStatement.{u_1}`; there is no `EG.EG.*` or
  `EG.Spec.EG.*` shadowing (grep).
* `gate_with_cycles` is an extra convenience theorem. It is stronger than `GateStatement` (it
  adds the directed cycles), not a weakening.
* Axioms of `EG.gate`, `EG.gate_precise`, `EG.gate_with_cycles`: `propext`, `Classical.choice`,
  `Quot.sound`. There is no `sorryAx`. `grep sorry` finds nothing in the Defs, Spec, Proof and
  `EG/Lib/Found/Orient.lean` files. `python3 scripts/lint.py`: 0 findings.
* The proof follows the manuscript: `exists_dirCycle_decomp` (balanced, loopless, no antiparallel
  arcs, so an arc-disjoint union of directed cycles of length `≥ 3`); each cycle meets `W` by
  acyclicity of `A \ W`; a private counting lemma gives `≤ |W|`; `isDecomp_map_cycle_of_arcs`
  gives the decomposition. The hypothesis `W ⊆ A` is not used (N3).

---

## Notes (non-blocking)

* **N1.** In `GatePreciseStatement`, `(Obj.cycle c).WF` is implied by `IsDirCycle A c` and
  `3 ≤ c.length`. It is redundant but harmless.
* **N2.** In `GateStatement`, `∀ e ∈ o.edges, e ∈ G.edges` is implied by `IsDecomp` and
  `F ⊆ G.edges`. It is redundant but harmless, and makes "cycles of `G`" explicit.
* **N3.** `W ⊆ A` is not used by the proof: the bound holds for any finite `W`, since each cycle
  contains an arc of `W ∩ A`. Keeping the hypothesis follows the manuscript, and it only weakens
  the formal statement relative to one that omits it, never relative to the manuscript.
* **N4.** `IsDirCycle` counts a loop `[v]` and a 2-cycle `[u,v]` as directed cycles, which is the
  standard digraph convention. For arc subsets of orientations these cannot occur (test §8).
  A future `Spec` that applies `IsAcyclic` to an arc set that is not a subset of an orientation
  should keep this convention in mind.
* **N5.** `IsDirPathIn A [v]` holds for every `v`, also one that meets no arc (documented). A
  statement about a possibly trivial directed path must restrict its vertex separately.
* **N6.** Arc sets are `Finset (V × V)`, so parallel arcs cannot be represented. Unions of
  orientations are orientations only for disjoint edge sets (documented). This is faithful to
  every use in s6 (HCC-P Step 2 checks "These are distinct edges of $G$").
* **N7.** `IsBalanced` is a global condition (all `v : V`). [s6:defCluster]'s "admissible
  orientation" requires balance only at hubs. A `Spec` for clusters must use `outDeg`/`inDeg`
  pointwise and not `IsBalanced`. This is a point for later statements, not for these
  definitions.
* **N8.** The statements are universe-monomorphic per instance (`V : Type u` for the one
  parameter `u`). The proofs are universe polymorphic, so any consumer can instantiate at its
  universe.

## Verdicts

| item | verdict |
|---|---|
| `EG.cycleArcs` | approve |
| `EG.IsOrientation` | approve |
| `EG.outDeg`, `EG.inDeg` | approve |
| `EG.IsBalanced` | approve |
| `EG.walkArcs` | approve |
| `EG.IsDirPathIn` | approve (N5) |
| `EG.IsDirCycle` | approve (N4) |
| `EG.IsAcyclic` | approve |
| `Decidable` instances | approve |
| `EG.Spec.GateStatement` | approve (N2, N3) |
| `EG.Spec.GatePreciseStatement` | approve (N1, N3) |
| `EG/Proof/Chain/Gate.lean` proves exactly the Spec | confirmed |
