# Clean-room review: group `bridge`, reviewer `opus`

Date: 2026-09-26. Reviewer: Claude Opus 5.5, an independent clean-room agent. I reviewed from
scratch and did not read any earlier review or approval of the bridge. No `bridge.*.md` file
existed when I started. This review is the only file I wrote in the repository. I ran no git
command that changes anything.

Scratch files, compiled with `lake env lean` from `formal/`, all under
`/tmp/claude-0/-home-user-Erdos-Proof/ab92a43f-e615-5aab-870d-cceae4796e61/scratchpad/`:
* `Check1.lean` re-runs the meta-check of `EGCheck/Final.lean` on a copy of the final theorem,
  without the `#guard_msgs`. It also checks that the type of `of_mainInternal` is exactly
  `MainInternal → <upstream type>`, and prints the axioms of the bridge constants.
* `Check2.lean` holds non-vacuity tests for `IsDecomp` and `MainInternal`. It has 0 errors.
* `Check3.lean` lists the constants that occur in the upstream statement and its two
  definitions, to confirm they are plain Mathlib notions.

**Overall verdict: APPROVE, with notes.**
* The statement is exactly `type_of% @Erdos184.erdos_184`.
* The proof uses only `MainInternal` and the three standard axioms.
* The only `sorryAx` comes through `EG.Proof.mainInternal`.
* `MainInternal` is mathematically *equivalent* to the upstream statement. It is not stronger,
  so it is not false while the conjecture is true. It is not weaker, so the bridge is not
  vacuous. It is exactly `s1:thmMain` with the constant existentially quantified.

The notes (N1 to N5 at the end) are not defects.

---

## 0. Scope and files read

* `EGCheck/Bridge.lean`: `EGCheck.Bridge.of_mainInternal` and `EGCheck.Bridge.solution`.
* `EGCheck/BridgeLemmas.lean`: the helper definitions `toSub`, `chainEdges`, `lastOf`,
  `listWalk`, `cycleWalk` and `objMap`, and the lemmas `exists_finset_of_isDecomp`,
  `isDecomp_comap_symm` and the others.
* Target: `.lake/packages/formal_conjectures/FormalConjectures/ErdosProblems/184.lean`
  (`Erdos184.IsCycleOrEdge`, `Erdos184.erdos_184`) and
  `.lake/packages/formal_conjectures/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`
  (`SimpleGraph.IsDecomposition`).
* Hypothesis: `EG/Spec/Main.lean` (`EG.Spec.MainInternal`), which uses `EG/Defs/Objects.lean`
  (`EG.Obj`, `EG.Obj.edges`, `EG.Obj.WF`, `EG.cycleEdges`, `EG.IsDecomp`).
* Also read: `EGCheck/Final.lean`, `EG/Proof/Main.lean`, `TRUST.md`, `LOCK.json`,
  `scripts/Axioms.lean`, and manuscript `s1.tex` (Introduction, `s1:thmMain`, `s1:convGraphs`,
  `s1:defObject`) and `s7.tex` (`s7:thmMainProof`).

Integrity checks:
* `sha256sum` of the two upstream files matches `TRUST.md`:
  `9f36e4e0…` for `184.lean` and `86bf339a…` for `Decomposition.lean`.
* The checked-out commit of `formal_conjectures` is `2424bb480c59…`, the pinned one.
* `EG/Spec/Main.lean`, `EG/Defs/Objects.lean` and `EGCheck/Final.lean` match the file hashes in
  `LOCK.json`.
* `lake build EGCheck.Bridge --no-build` reports all targets up to date, so the `.olean` files
  used by the scan match the sources.
* `python3 scripts/lint.py` reports 0 findings.
* A grep of both bridge files finds no `sorry`, `instance`, `attribute`, `notation`, `macro`,
  `set_option` or `local` declaration. Nothing in them can change how imported statements
  elaborate.

## 1. The upstream target, back-translated

`Erdos184.erdos_184.{u}` (under `open scoped Classical`) says:

> There is a function f : ℕ → ℝ with f = O(n) as n → ∞ such that the following holds. For every
> type V in universe u with a `Fintype` and a `DecidableEq` instance, and for every simple graph
> G on V, there is a finite set D of subgraphs of G such that:
> (i) every H ∈ D, viewed as a graph on its own vertex set `H.verts`, is either connected and
> 2-regular, or has exactly one edge;
> (ii) the edge sets of the members of D are pairwise disjoint and their union is E(G);
> (iii) |D| ≤ f(|V|).

This is the Erdős–Gallai conjecture f(n) = O(n) in the form of the manuscript's Introduction:
"let f(G) be the least number of cycles and single edges that partition E(G) … conjectured
that f(n)=O(n)".

Points I checked:
* A connected 2-regular finite graph is a cycle of length at least 3 (Mathlib's `Connected`
  includes `Nonempty`, and simple graphs have no loops).
* A member H with one edge may also have isolated vertices. That only makes the upstream
  statement *easier*, so it is harmless.
* `Check3.lean` shows that the type uses only Mathlib constants (`Asymptotics.IsBigO`,
  `Filter.atTop`, `Subgraph.coe`, `Subtype.fintype`, `Classical.propDecidable`, …) plus
  `Erdos184.IsCycleOrEdge` and `SimpleGraph.IsDecomposition`. There is no custom notation.
* The `Fintype H.verts` instance inside `IsCycleOrEdge H.coe` is
  `Subtype.fintype … Classical.propDecidable`. The bridge proves the property for *every*
  instance (`∀ inst : Fintype H.verts, …`), so the choice of instance cannot matter.

## 2. `EG.Spec.MainInternal`, back-translated and compared with the manuscript

```
def MainInternal : Prop :=
  ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∃ D : List (EG.Obj V), EG.IsDecomp G.edgeSet D ∧ D.length ≤ c * Fintype.card V
```

In plain mathematics:

> There is a natural number c such that every finite simple graph G on a vertex set V
> (V in universe 0) has a list D of objects with two properties. First, the objects are well
> formed. Second, their edge lists, concatenated, are duplicate-free and consist exactly of the
> edges of G. The length of D is at most c·|V|.

Unfolding `IsDecomp` and `Obj.WF`:
* An object `edge e` must have e not a loop.
* An object `cycle c` must have c duplicate-free with |c| ≥ 3. Its edges are
  c₀c₁, …, c_{k−1}c₀, which are k distinct non-loop edges, so it is a genuine cycle of
  length k ≥ 3.
* A duplicate-free concatenation means each object's edges are distinct and different objects
  have disjoint edge sets.
* Every well-formed object has at least one edge, so D cannot list the same object twice.
  Hence `D.length` is exactly the number of parts of the partition.

So `IsDecomp G.edgeSet D` says precisely that D is a decomposition in the sense of
`s1:defObject`:

> "An *object* is a cycle (of length at least 3) or a single edge. A *decomposition* of an edge
> set F is a partition of F into the edge sets of objects".

Manuscript `s1:thmMain`:

> "Then every graph G on n vertices satisfies f(G) ≤ c_EG n. In particular f(n)=O(n)."

`s1:convGraphs`(a) adds: "Graphs are finite and simple … n := |V(G)|".

Comparison:
* **Quantifiers.** The manuscript fixes an explicit real c_EG and asserts f(G) ≤ c_EG·n for
  every graph. `MainInternal` asks for some natural c with a decomposition of size ≤ c·n. Take
  c := ⌈c_EG⌉, so the manuscript theorem implies `MainInternal`. The explicit formula for c_EG
  is deliberately dropped (see N3). Nothing downstream needs it.
* **Strict vs non-strict.** Both are `≤`.
* **Casts and arithmetic.** Only ℕ multiplication is used: no subtraction, division, logarithm
  or rounding.
* **"Finite and simple".** `[Fintype V]` and `SimpleGraph`.
* **n.** n = `Fintype.card V`. All `Fintype` instances give the same cardinality.
* **Edge cases.**
  * n = 0 and n = 1: G has no edges, so `D = []` works for every c.
  * n = 2: `⊤` needs one object, so c ≥ 1 is needed. `Check2.lean` proves that c = 0 fails
    on `⊤ : SimpleGraph (Fin 2)`.
  * No loops can occur because `G.edgeSet` is loop-free.
* **Extra binders.** `[DecidableEq V]` is an extra *hypothesis* inside a `∀`. It weakens what
  must be proved and is harmless. The bridge supplies `instDecidableEqFin`.
* **Universe.** `V : Type` (universe 0), whereas the upstream uses `Type u`. The bridge
  transports along `Fintype.equivFin`. `MainInternal` stays in `Prop` by impredicativity.

## 3. `of_mainInternal`: exact statement

```
theorem of_mainInternal (h : EG.Spec.MainInternal) : type_of% @Erdos184.erdos_184.{u}
theorem solution : type_of% @Erdos184.erdos_184.{u} := of_mainInternal EG.Proof.mainInternal
```

The statement type is exact, by three checks:
* **`solution` check.** In `Check1.lean` I copied the meta-program of `EGCheck/Final.lean`. It
  instantiates the upstream universe parameter and compares with `Expr.equal`, which also
  compares binder names and binder info. I applied it to a theorem defined as
  `EGCheck.Bridge.solution`, and separately to `solution` itself. Both are equal, with one
  universe parameter on each side.
* **`of_mainInternal` check.** The type of `of_mainInternal` is a `forallE` whose domain is
  `EG.Spec.MainInternal` and whose body has no loose bound variables. The body is `Expr.equal`
  to the upstream type. So `of_mainInternal` has **no hypothesis other than `MainInternal`**.
  Bridge.lean declares no section `variable`, so nothing is auto-bound.
* **`Final.lean` itself.** `lake env lean EGCheck/Final.lean` (which writes no output) shows
  exactly one error: the expected `#guard_msgs` mismatch, because `sorryAx` is still present.
  The `run_cmd` syntactic-equality check passes.

## 4. Axioms

`lake env lean --run scripts/Axioms.lean --prefix EGCheck EGCheck.Bridge`:

```
SORRY EGCheck.Bridge.solution (EGCheck.Bridge)
inspected 66 constants under [EGCheck]; 1 use sorryAx; 0 violations
```

`#print axioms` in `Check1.lean`:
* `EGCheck.Bridge.of_mainInternal`, `exists_finset_of_isDecomp` and `isDecomp_comap_symm` use
  only `propext`, `Classical.choice` and `Quot.sound`.
* `EG.Proof.mainInternal` and `EGCheck.Bridge.solution` use those three plus `sorryAx`.

`solution` is literally `of_mainInternal EG.Proof.mainInternal`, and `of_mainInternal` is free of
`sorryAx`. So the only `sorryAx` comes through `EG.Proof.mainInternal`, as required.

The upstream `erdos_184` is itself `sorry`. It enters only through `type_of%`, which reads its
type and not its value, and the axiom lists above confirm that its proof is not used.

## 5. The proof and the helper definitions

These helpers are untrusted. They are kernel-checked, and a wrong helper could only make the
bridge fail to compile. It could never change what `Final.lean` asserts. I still checked that
they mean what they say.

* `toSub G o` is the subgraph whose vertices are the ends of the edges of `o` and whose
  adjacency is `s(a,b) ∈ o.edges ∧ G.Adj a b`. For an object of a decomposition of `E(G)`,
  its edge set is exactly `o.edges` (`mem_edgeSet_toSub`).
* `chainEdges`, `lastOf`, `listWalk`, `cycleWalk` build the closed walk
  a, l₀, …, l_{k−2}, a from `cycle (a :: l)`.
  * `cycleEdges_cons` shows its edge list equals `EG.cycleEdges (a :: l)` (via
    `rotate 1 = l ++ [a]`).
  * `isCycle_cycleWalk` derives `Walk.IsCycle` from the three facts `WF` gives: duplicate-free
    edges, duplicate-free vertices and length ≥ 3.
  * `toSub_cycle_eq` identifies `toSub` with `Walk.toSubgraph`. Mathlib then gives connectivity
    and 2-regularity (`ncard_neighborSet_toSubgraph_eq_two`).
  * The degree and edge-count lemmas are proved for an arbitrary `Fintype` instance.
* `exists_finset_of_isDecomp` takes `(D.map (toSub G)).toFinset`.
  * **Disjointness.** Two different members come from objects o₁ and o₂. A shared edge would
    force o₁ = o₂ by `eq_of_mem_of_nodup_flatMap`, and then the two members would be equal.
  * **Union.** From the membership clause of `IsDecomp`.
  * **Card.** `toFinset` has card ≤ length.
* `objMap e.symm` and `isDecomp_comap_symm` move a decomposition of `G.comap e.symm` (a copy of
  G on `Fin n`) back to V. Well-formedness is preserved because `e.symm` is injective; this is
  the only place injectivity matters, and it holds for an equivalence. Duplicate-freeness is
  preserved because `Sym2.map` of an injective map is injective. The membership clause holds
  via `Sym2.map_map` and `e ∘ e.symm = id`.
* In `of_mainInternal`:
  * f := n ↦ c·n, and f = O(n) by `isBigO_refl.const_mul_left`.
  * `card D ≤ length(D₀.map …) = length D₀ ≤ c · card (Fin (card V)) = c · card V`, cast to ℝ.
    The `Fintype.card V` in the goal uses the bound instance, which is the same one that
    `Fintype.equivFin V` uses.

## 6. Strength: the bridge is not vacuous, and `MainInternal` is not too strong

* **`MainInternal` ⇒ upstream (all universes).** This is the theorem `of_mainInternal`. So
  `MainInternal` is at least as strong as needed.
* **Upstream (universe 0) ⇒ `MainInternal`.** I argue this on paper; it is not formalized.
  * The upstream gives C and N with |f(n)| ≤ C·n for n ≥ N. Each member H is a cycle
    (connected, 2-regular, finite) or has one edge. Turning each H into an `Obj` gives a list
    satisfying `IsDecomp` with length |D| ≤ ⌈C⌉·n.
  * For n < N, the single-edge decomposition has |E| ≤ n(n−1)/2 ≤ N·n objects.
  * So c := max(⌈C⌉, N) works.
  * Hence `MainInternal` is mathematically **equivalent** to the conjecture. It is not a
    strictly stronger internal target that might be false while the conjecture is true, and the
    bridge is not vacuous. It is also implied by `s1:thmMain` (§2).
* **Non-triviality**, from `Check2.lean`, which compiles:
  * **Positive cases.**
    * `IsDecomp ⊤ (Fin 3)` holds for `[cycle [0,1,2]]`.
    * `IsDecomp ⊤ (Fin 4)` holds for `[cycle [0,1,2,3], edge s(0,2), edge s(1,3)]`.
    * Every graph has the single-edge decomposition.
    * The graph `⊥` with `D = []` meets any bound, including n = 0.
  * **Negative cases.**
    * Two triangles sharing an edge are rejected.
    * A 2-vertex "cycle", a loop edge and a closed walk with a repeated vertex are each not
      `WF`.
    * A list that misses an edge is rejected.
    * An edge not in G is rejected.
    * `MainInternal` with c = 0 is false.
  * So `IsDecomp` is neither trivially satisfiable nor trivially unsatisfiable. The only content
    left in `MainInternal` is the linear bound, which is the conjecture itself.

## 7. Per-item verdicts

| Item | Verdict |
|---|---|
| `EG.Spec.MainInternal` (as the bridge's hypothesis; strength and faithfulness to `s1:thmMain`) | approve |
| `EGCheck.Bridge.of_mainInternal` (type exactly `MainInternal → type_of% @Erdos184.erdos_184.{u}`, axioms standard) | approve |
| `EGCheck.Bridge.solution` (type equal to upstream; only `sorryAx` via `EG.Proof.mainInternal`) | approve |
| `BridgeLemmas`: `toSub`, `chainEdges`, `lastOf`, `listWalk`, `cycleWalk`, `objMap` (helper definitions) | approve |
| `BridgeLemmas`: `exists_finset_of_isDecomp`, `isDecomp_comap_symm` and the supporting lemmas | approve |

## 8. Notes (not defects)

* **N1.** `EGCheck/Final.lean` triggers a style-linter warning: "more than one module
  docstring" (the second `/-! … -/` before the `run_cmd`). It is cosmetic and does not affect
  the checks. The file is protected, so I did not touch it.
* **N2 (stage α).** `TRUST.md` / PLAN §1 allow the internal main theorem, in stage α, to take
  `Prop` hypotheses for Lovász, Haxell and Euler. The locked `MainInternal` is unconditional,
  and it should stay that way: any such hypotheses belong on `EG.Proof.mainInternal`, and they
  must be discharged before `solution` and `Final.lean` can compile without `sorry`. Adding
  them to `MainInternal` itself would be a statement change that needs re-approval.
* **N3.** `MainInternal` forgets the explicit formula for c_EG in `s1:thmMain`. This is
  intended (galactic constants are handled by eventualities) and loses nothing needed for the
  upstream statement.
* **N4.** The `[DecidableEq V]` binder in `MainInternal` is superfluous, since `IsDecomp` is
  stated on a `Set`, but it is harmless (§2).
* **N5.** `EGCheck/Bridge.lean` and `EGCheck/BridgeLemmas.lean` are not in `LOCK.json`. That is
  fine: `Final.lean` (which is locked) re-checks the type syntactically and demands exactly the
  three standard axioms, so no later edit of the bridge could make the final claim wrong without
  `Final.lean` failing.
