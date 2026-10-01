# Clean-room review: group `gate`, reviewer `fable`

Date: 2026-09-26. Reviewer: Claude (Fable 5.1), independent clean-room agent. Reviewed from
scratch against the manuscript; earlier approvals were not relied on. No repository file other
than this one was written.

Scope:
* `EG/Defs/Orient.lean`: `cycleArcs`, `IsOrientation`, `outDeg`, `inDeg`, `IsBalanced`,
  `walkArcs`, `IsDirPathIn`, `IsDirCycle`, `IsAcyclic`, two `Decidable` instances.
* `EG/Spec/Chain/Gate.lean`: `EG.Spec.GateStatement`, `EG.Spec.GatePreciseStatement`.
* Skim of `EG/Proof/Chain/Gate.lean` (does it prove exactly the Spec?).

Dependencies read to interpret the statements (reviewed in other groups, not re-verdicted here):
`EG.FGraph` (`EG/Defs/Graph.lean`), `EG.Obj`, `EG.Obj.edges`, `EG.Obj.WF`, `EG.cycleEdges`,
`EG.IsDecomp` (`EG/Defs/Objects.lean`), `EG.walkEdges`, `EG.IsPathIn` (`EG/Defs/Walk.lean`).

Scratch files (all under the session scratchpad, compiled with `lake env lean` from `formal/`):
* `.../scratchpad/GatePrintFable.lean`: `#print` of every definition and both statements with
  `pp.fullNames`, `pp.universes`, `pp.parens`, `pp.coercions`; `#check` of `EG.gate`,
  `EG.gate_precise`, `EG.gate_with_cycles`; `#print axioms` of the three.
* `.../scratchpad/GateReviewFable.lean`: independent tests (sections 1 to 9 below). Compiles with
  0 errors and 0 warnings.

Also run: `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Chain.Gate`
("inspected 286 constants under [EG]; 0 use sorryAx; 0 violations"); `python3 scripts/lint.py`
(0 findings); `grep sorry` over Defs/Spec/Proof/Lib files (none).

**Overall verdict: APPROVE.** Every definition and both statements back-translate to exactly the
manuscript notion, including in all edge cases I could find. The notes N1 to N7 are
non-blocking observations for future `Spec` authors.

---

## Manuscript text used

* `s6.tex` l. 12 (Section 6 preamble): "Throughout, $G$ is the input graph
  (Convention~\ref{s1:convGraphs}). Orientations, directed paths and directed cycles are those
  of digraphs obtained by orienting edges of $G$; each edge receives exactly one direction. A
  digraph is \emph{acyclic} if it has no directed cycle."
* `s6.tex` l. 16–19, [s6:lemGATE] (forward direction): "Let $F\subseteq E(G)$ and let $\vec F$
  be an orientation of $F$ with $d^+_{\vec F}(v)=d^-_{\vec F}(v)$ at every vertex $v$. Let
  $\mathcal W$ be a set of arcs of $\vec F$ such that $\vec F-\mathcal W$ is acyclic. Then $F$
  decomposes into at most $|\mathcal W|$ cycles of $G$. More precisely, $\vec F$ is the
  arc-disjoint union of directed cycles, each of length at least $3$, each the orientation of a
  cycle of $G$, and each containing an arc of $\mathcal W$; there are at most $|\mathcal W|$ of
  them." `\deps{s1:defObject}`.
* Proof of GATE, l. 21–31: "a directed path in $\vec F$ with pairwise distinct vertices",
  "$C:=v_i\to\dots\to v_k\to v_i$ is a directed cycle with distinct vertices", "the arcs
  $v_{k-1}\to v_k$ and $v_k\to v_{k-1}$ ... come from two distinct edges of $F$ with the same
  ends, which is impossible since $G$ is simple", "Their underlying cycles partition $F$, so they
  form a decomposition of $F$ into cycles in the sense of Definition~\ref{s1:defObject}",
  "The $C_i$ are arc-disjoint, so $p\le|\mathcal W|$."
* `s1.tex` [s1:defObject]: "An \emph{object} is a cycle (of length at least $3$) or a single
  edge. A \emph{decomposition} of an edge set $F$ is a partition of $F$ into the edge sets of
  objects".
* `s1.tex` [s1:convGraphs] (a): "Graphs are finite and simple".
* `s1.tex` [s1:citEuler] (c): "a directed graph without loops in which every vertex has
  in-degree equal to out-degree is an arc-disjoint union of directed cycles" (the standard fact
  behind the proof; no different convention appears).
* Consumer `s6.tex` l. 216 ([s6:lemHCCP] Step 4): "By Lemma~\ref{s6:lemGATE}, $F$ decomposes
  into at most $|\mathcal W|=\Phi$ cycles of $G$. Each of them is the orientation of a directed
  cycle $C$ of $\vec F$ of length at least $3$ containing an arc of $\mathcal W$."

---

## `EG/Defs/Orient.lean`

The `#print` output agrees with the source text in every case. All definitions are
universe-polymorphic in `V : Type u_1`; only `outDeg`, `inDeg`, `IsBalanced` take
`[DecidableEq V]`. Representation: an arc `u → v` is `(u, v) : V × V`, a digraph is its arc set
`A : Finset (V × V)`; no vertex set is carried.

### `cycleArcs (c : List V) : List (V × V) := List.zip c (c.rotate 1)`
* Back-translation: for `c = [c₀, …, c_{k-1}]`, `c.rotate 1 = [c₁, …, c_{k-1}, c₀]` (same
  length, so `zip` drops nothing; test `length_cycleArcs`), hence the list
  `[(c₀,c₁), …, (c_{k-2},c_{k-1}), (c_{k-1},c₀)]`: the arcs of the closed directed walk
  `c₀ → … → c_{k-1} → c₀`.
* Edge cases: `[] ↦ []`; `[v] ↦ [(v,v)]` (loop); `[u,v] ↦ [(u,v),(v,u)]`. All tested by
  `decide`.
* Consistency with `cycleEdges`: I proved independently
  `cycleEdges c = (cycleArcs c).map (fun a => s(a.1, a.2))` (`cycleEdges_eq_map`), so the
  undirected cycle of `c` is exactly the list of underlying edges of its arcs. This is what makes
  "the orientation of a cycle of $G$" literal in the Spec.
* Verdict: **approve**.

### `IsOrientation (F : Finset (Sym2 V)) (A : Finset (V × V)) : Prop`
Fields: `loopless : ∀ a ∈ A, a.1 ≠ a.2`; `mem : ∀ a ∈ A, s(a.1, a.2) ∈ F`;
`existsUnique : ∀ e ∈ F, ∃! a, a ∈ A ∧ s(a.1, a.2) = e`.
* Back-translation: `a ↦ s(a.1, a.2)` maps `A` into `F` (`mem`) and is a bijection `A → F`
  (`existsUnique` gives surjectivity and injectivity onto `F`); no arc is a loop. I.e. for every
  edge `uv ∈ F` exactly one of `(u,v)`, `(v,u)` is in `A`, and `A` contains nothing else.
* Manuscript: "orientation of $F$ ... each edge receives exactly one direction" and, in the
  proof, "two distinct edges of $F$ with the same ends ... impossible since $G$ is simple". The
  formal definition is exactly this. Because `A` is a `Finset`, two parallel arcs `u → v` cannot
  be represented; for an orientation of an edge set of a simple graph they cannot occur anyway
  (distinct edges have distinct pairs of ends). See N6.
* Loops: `loopless` is redundant when `F` is loopless (every `F ⊆ G.edges` is, by
  `FGraph.loopless`). If `F` contains a loop `s(v,v)`, `IsOrientation F A` is unsatisfiable for
  every `A` (test `not_orient_loop`): consistent with "orienting edges of $G$", $G$ simple.
* Negative tests: both directions of one edge (`not_orient_both`), an edge left unoriented
  (`not_orient_empty`), an arc whose edge is outside `F` (`not_orient_extra`) are all rejected.
  Positive: the cyclic triangle (`tri_orient`) and a single arc (`e01_orient`), with the `∃!`
  checked by `decide` after `simp only [ExistsUnique]`.
* Verdict: **approve**.

### `outDeg A v := (A.filter (fun a => a.1 = v)).card`, `inDeg A v := (A.filter (fun a => a.2 = v)).card`
* Back-translation: `d⁺(v)` = number of arcs with tail `v`; `d⁻(v)` = number with head `v`. A
  `Finset` has no multiplicities, so each arc counts once. (A loop would count once in each;
  irrelevant for orientations.)
* Direction check: for `{(0,1),(0,2)}`, `outDeg _ 0 = 2` and `inDeg _ 0 = 0` (`decide`).
* The `DecidableEq V` instance only feeds `Finset.filter`; `Decidable` is a subsingleton, so
  the value does not depend on which instance is used.
* Verdict: **approve**.

### `IsBalanced A := ∀ v, outDeg A v = inDeg A v`
* Back-translation: `d⁺(v) = d⁻(v)` for every `v : V`.
* Manuscript: "$d^+_{\vec F}(v)=d^-_{\vec F}(v)$ at every vertex $v$". The manuscript's "every
  vertex" ranges over $V(G)$ (or the vertices of $\vec F$); the formal version ranges over all
  of `V`. Equivalent under the GATE hypotheses: I proved (`degs_eq_zero_of_not_mem_verts`,
  `isBalanced_of_forall_verts`) that if `F ⊆ G.edges` and `IsOrientation F A`, every
  `v ∉ G.verts` has `outDeg A v = inDeg A v = 0`, so balance on `V(G)` implies `IsBalanced A`.
  Hence the formal hypothesis is not stronger than the manuscript's.
* Tests: the cyclic triangle is balanced; the triangle minus an arc, and the single arc, are not.
* Verdict: **approve** (see N4 for a later-Spec caveat).

### `walkArcs p := List.zip p p.tail`
* Back-translation: for `p = [v₀, …, v_k]`, the list `[(v₀,v₁), …, (v_{k-1},v_k)]`, empty when
  `p` has at most one vertex. Independent proof that
  `walkEdges p = (walkArcs p).map (fun a => s(a.1, a.2))` (`walkEdges_eq_map`): the exact
  directed counterpart of `walkEdges`, as the docstring claims.
* Verdict: **approve**.

### `IsDirPathIn A p := p ≠ [] ∧ p.Nodup ∧ ∀ a ∈ walkArcs p, a ∈ A`
* Back-translation: a non-empty vertex list with pairwise distinct vertices whose consecutive
  arcs all lie in `A`: "a directed path in $\vec F$ with pairwise distinct vertices" (GATE
  proof). Direction matters (`[1,0]` is not a path of `{(0,1)}`), repeated vertices are
  excluded (`[0,1,0]` is not a path of `{(0,1),(1,0)}`), `[]` never is. `[v]` is a trivial path of
  every `A`, even when `v` meets no arc (`IsDirPathIn ∅ [1]`), exactly as `IsPathIn` does for
  edge sets and as the docstring warns. Not used by any `Spec` (grep).
* Verdict: **approve** (N5).

### `IsDirCycle A c := c ≠ [] ∧ c.Nodup ∧ ∀ a ∈ cycleArcs c, a ∈ A`
* Back-translation: `c = c₀ … c_{k-1}` with `k ≥ 1`, pairwise distinct vertices, and all arcs
  `c₀ → c₁ → … → c_{k-1} → c₀` in `A`. Length `k = c.length`.
* Manuscript: "directed cycle" in the usual sense ("a directed cycle with distinct vertices").
  For a general arc set the formal notion admits a loop `[v]` (when `(v,v) ∈ A`) and a 2-cycle
  `[u,v]` (when `(u,v),(v,u) ∈ A`), which is the standard digraph convention. For any arc set
  `B ⊆ A` with `A` an orientation, neither can occur: proved `3 ≤ c.length`
  (`three_le_of_sub_orient`, via the Lib lemmas). So for `A \ W` in GATE the formal and the
  manuscript notion coincide exactly.
* Several lists represent one cycle (rotations); harmless: `IsAcyclic` quantifies over all
  lists, and the GATE conclusions are existential with arc-disjointness ruling out repeats.
* Tests: `[0,1,2]` and `[1,2,0]` are directed cycles of the cyclic triangle, `[0,2,1]` (wrong
  direction), `[0,1,2,0]` (repeat) and `[]` are not; `[0]` of `{(0,0)}`, `[0,1]` of
  `{(0,1),(1,0)}` are.
* Verdict: **approve** (N3).

### `IsAcyclic A := ∀ c : List V, ¬ IsDirCycle A c`
* Back-translation: `A` has no directed cycle. Literal manuscript definition: "A digraph is
  \emph{acyclic} if it has no directed cycle." Restricting to cycles with distinct vertices
  loses nothing (a closed directed walk contains a directed cycle). Quantifying over all
  `c : List V` (including vertices meeting no arc) is harmless: a non-empty `c` with all arcs in
  `A` only uses ends of arcs of `A`.
* Non-vacuity: `¬ IsAcyclic triA` (witness `[0,1,2]`), `IsAcyclic (triA \ {(2,0)})` (potential
  argument), `IsAcyclic {(1,0)}`.
* Verdict: **approve**.

### `Decidable` instances
`inferInstanceAs (Decidable (_ ∧ _ ∧ _))` on the literal bodies; no semantic content. They do
evaluate under `decide` (used throughout my tests). Note `IsBalanced` has no instance (my tests
`unfold IsBalanced` first); irrelevant to meaning.
* Verdict: **approve**.

---

## `EG/Spec/Chain/Gate.lean`

Both are `Prop`-valued `def`s with one universe parameter `u`, quantifying over `V : Type u`, an
arbitrary `[DecidableEq V]`, `G : EG.FGraph V`, `F : Finset (Sym2 V)`, `A W : Finset (V × V)`.
With `pp.fullNames` every constant is the intended one (`EG.IsOrientation`, `EG.IsBalanced`,
`EG.IsAcyclic`, `EG.IsDecomp`, `EG.Obj.cycle`, `EG.Obj.edges`, `EG.Obj.WF`, `EG.cycleEdges`,
`EG.cycleArcs`, `EG.IsDirCycle`, `EG.FGraph.edges`); `A \ W` is `SDiff.sdiff` on `Finset`;
`(F : Set (Sym2 V))` is the `Finset`-to-`Set` coercion `↑F`. No other declaration of these names
exists in the repository (grep), so nothing is shadowed.

### Hypotheses (shared)

| manuscript | formal | assessment |
|---|---|---|
| $F\subseteq E(G)$, $G$ finite simple | `G : FGraph V`, `F ⊆ G.edges` | exact; `FGraph` is finite, loopless, `Sym2` edges |
| $\vec F$ an orientation of $F$ | `IsOrientation F A` | exact (above) |
| $d^+=d^-$ at every vertex | `IsBalanced A` | over all `v : V`; equivalent (test §4) |
| $\mathcal W$ a set of arcs of $\vec F$ | `W ⊆ A` | exact (N1) |
| $\vec F-\mathcal W$ acyclic | `IsAcyclic (A \ W)` | exact; loops/2-cycles impossible in `A \ W` (test §5) |

No hypothesis is stronger than the manuscript's and none is missing (no `Fintype V`,
`Nonempty V`, or similar). Lean conventions (ℕ subtraction, division, `logb`, rounding) do not
occur anywhere in these statements.

### `GateStatement`
* Back-translation: under the hypotheses there is a list `D` of objects with (i)
  `IsDecomp (↑F) D`: every object well formed (`Obj.cycle c` well formed iff `c.Nodup ∧ 3 ≤
  c.length`), the concatenated edge lists duplicate free, their union exactly `F`; (ii)
  `D.length ≤ |W|`; (iii) every `o ∈ D` is `Obj.cycle c` for some `c`, all of whose edges are in
  `E(G)`.
* Manuscript: "Then $F$ decomposes into at most $|\mathcal W|$ cycles of $G$", decomposition per
  [s1:defObject] (partition of $F$ into edge sets of objects). "Cycles of $G$": a cycle of length
  `≥ 3` with distinct vertices all of whose edges are edges of `G` (ends automatically in `V(G)`
  by `FGraph.edge_verts`). All objects are cycles, as the manuscript says. "At most
  $|\mathcal W|$": `D.length` counts list entries; the edge lists are duplicate free and every
  cycle has `≥ 3` edges, so no object appears twice and `D.length` is the number of cycles.
* Redundancy (N2): (iii)'s edge condition follows from (i) and `F ⊆ G.edges`; harmless.
* Edge cases: `F = ∅` forces `A = ∅` (`orient_empty_forces`), hence `W = ∅`; `D = []` works, as
  in the manuscript. Empty `V` is the same.
* Non-vacuity (test §6): the cyclic triangle with `W = {(2,0)}` satisfies all five hypotheses
  (each proved), and `EG.gate` yields a `D` with `D.length = 1` exactly, so the bound is tight
  and the conclusion is not trivially satisfiable.
* Load-bearing hypotheses (test §7): with every other hypothesis holding, the conclusion is
  false when balance is dropped (single arc, `W = ∅`), when acyclicity is dropped (triangle,
  `W = ∅`), and when the orientation hypothesis is dropped (balanced 2-cycle `{(0,1),(1,0)}`,
  `W = {(0,1)}`: `{01}` has no decomposition into cycles at all). So the statement is not
  trivially true, and the simplicity of `G` enters exactly through `IsOrientation`, as in the
  manuscript proof.
* Verdict: **approve**.

### `GatePreciseStatement`
* Back-translation: under the hypotheses there is a list `cs` of vertex lists such that
  (a) every `c ∈ cs` is a directed cycle of `A`, has length `≥ 3`, is a well-formed cycle
  object, has all its undirected edges `cycleEdges c` in `E(G)`, and contains an arc of `W`;
  (b) the concatenation of the `cycleArcs c` is duplicate free; (c) it contains exactly the arcs
  of `A`; (d) `cs.length ≤ |W|`.
* Manuscript: "$\vec F$ is the arc-disjoint union of directed cycles" = (b)+(c) (the union is
  `A`, the cycles are pairwise arc-disjoint); "each of length at least $3$" = `3 ≤ c.length`;
  "each the orientation of a cycle of $G$": `c` is a well-formed cycle whose edges are in `E(G)`,
  and its arcs `cycleArcs c ⊆ A` have exactly the underlying edges `cycleEdges c`
  (`cycleEdges_eq_map`), so the directed cycle is literally an orientation of that cycle of
  `G`; "each containing an arc of $\mathcal W$" = `∃ w ∈ W, w ∈ cycleArcs c`; "at most
  $|\mathcal W|$ of them" = (d), where (b) rules out repeated entries (also repeated rotations of
  one cycle), so `cs.length` is the number of cycles.
* It also provides exactly what [s6:lemHCCP] Step 4 quotes from GATE.
* Redundancy (N2): `(Obj.cycle c).WF` repeats `c.Nodup` (in `IsDirCycle`) and `3 ≤ c.length`.
* Non-vacuity (test §6): on the triangle `EG.gate_precise` gives `cs.length = 1` and the one
  cycle contains `(2,0)`.
* Verdict: **approve**.

---

## `EG/Proof/Chain/Gate.lean` (skim)

* `theorem gate_precise : EG.Spec.GatePreciseStatement` and `theorem gate : EG.Spec.GateStatement`
  have the `Spec` constants themselves as their types (`#check`:
  `EG.gate.{u_1} : EG.Spec.GateStatement.{u_1}`,
  `EG.gate_precise.{u_1} : EG.Spec.GatePreciseStatement.{u_1}`). No auxiliary restatement, no
  weakening; both specialise to universe `0` (test §9).
* `gate_with_cycles` is an additional theorem combining both conclusions (decomposition
  `cs.map Obj.cycle` plus the directed cycles); it is stronger than the Spec, not a substitute.
* Axioms of all three: `propext`, `Classical.choice`, `Quot.sound` only; no `sorryAx`. The
  axiom scan of `EG.Proof.Chain.Gate` reports 0 `sorryAx` and 0 violations over 286 constants;
  lint reports 0 findings.
* Proof structure follows the manuscript: `exists_dirCycle_decomp` (balanced + loopless + no
  antiparallel arcs, the last from `IsOrientation.not_mem_swap`, i.e. simplicity of `G`); each
  cycle meets `W` since `A \ W` is acyclic; a private counting lemma gives `≤ |W|`;
  `isDecomp_map_cycle_of_arcs` gives the decomposition of `F`. The hypothesis `W ⊆ A` is not
  used (N1).

---

## Notes (non-blocking)

* **N1.** `W ⊆ A` is not needed by the proof (the bound holds for any finite `W`, since each
  cycle contains an arc of `W ∩ A`). Keeping it is faithful to the manuscript ("a set of arcs of
  $\vec F$") and only makes the formal statement weaker than a version without it, never weaker
  than the manuscript. Consumers always have it.
* **N2.** Two redundant conjuncts: `∀ e ∈ o.edges, e ∈ G.edges` in `GateStatement` (implied by
  `IsDecomp` and `F ⊆ G.edges`) and `(Obj.cycle c).WF` in `GatePreciseStatement` (implied by
  `IsDirCycle A c` and `3 ≤ c.length`). Harmless; they make "cycle of `G`" explicit.
* **N3.** For a general arc set, `IsDirCycle` admits loops `[v]` and 2-cycles `[u,v]`, so
  `IsAcyclic` is (correctly, by the standard convention) stronger there than "no cycle of length
  `≥ 3`". For arc subsets of an orientation the notions coincide (test §5). All uses in s6
  (`MED`, `D'_j`, `F⃗ - W`) are on orientations of edge sets of `G`, so no issue arises; a
  future `Spec` applying `IsAcyclic` to a non-orientation should keep this in mind.
* **N4.** `IsBalanced` is global (all `v : V`). The "admissible orientation" of [s6:defCluster]
  requires `d⁺ = d⁻` only at hubs; a `Spec` for clusters must use `outDeg`/`inDeg` pointwise, not
  `IsBalanced`. Not a defect of these definitions.
* **N5.** `IsDirPathIn A [v]` holds for every `v`, also one meeting no arc (documented). A
  statement about a possibly trivial directed path must restrict `v` separately, as for
  `IsPathIn`.
* **N6.** Arc sets are `Finset (V × V)`: parallel arcs are unrepresentable, and a union of
  orientations is an orientation only for disjoint edge sets (documented in the module
  docstring). Faithful to every use in s6 (HCC-P Step 2 explicitly asserts "These are distinct
  edges of $G$").
* **N7.** `IsBalanced` has no `Decidable` instance (my tests `unfold` it before `decide`);
  ergonomics only.

## Verdicts

| item | verdict |
|---|---|
| `EG.cycleArcs` | approve |
| `EG.IsOrientation` | approve |
| `EG.outDeg`, `EG.inDeg` | approve |
| `EG.IsBalanced` | approve (N4) |
| `EG.walkArcs` | approve |
| `EG.IsDirPathIn` | approve (N5) |
| `EG.IsDirCycle` | approve (N3) |
| `EG.IsAcyclic` | approve (N3) |
| `Decidable` instances | approve |
| `EG.Spec.GateStatement` | approve (N1, N2) |
| `EG.Spec.GatePreciseStatement` | approve (N1, N2) |
| `EG/Proof/Chain/Gate.lean` proves exactly the Spec | confirmed |
