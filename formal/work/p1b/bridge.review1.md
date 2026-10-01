# Review 1 (clean room): task [bridge], `EG.Spec.MainInternal ⇒ Erdos184.erdos_184`

Reviewer: clean-room agent, round 1. No Lean file in the repo was edited. Scratch files were kept
outside the repo, in the session scratchpad under `/tmp/claude-0/...`.

**Verdict: APPROVE.** I found no major or minor issues, only cosmetic and usability remarks
(listed below).

## Files reviewed
- `EGCheck/Bridge.lean`. The diff against the scaffold (`d8d9e86`) adds
  `import EGCheck.BridgeLemmas`, a docstring paragraph and the proof of `of_mainInternal`.
  `solution` is unchanged.
- `EGCheck/BridgeLemmas.lean` (new, plain file, 336 lines).
- Unchanged since P0 (`git log`): `EG/Spec/Main.lean`, `EG/Defs/Objects.lean`,
  `EG/Proof/Main.lean` and `EGCheck/Final.lean`.
- Upstream: `FormalConjectures/ErdosProblems/184.lean` and
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`.
- Manuscript: `s1.tex`, [s1:defObject] and [s1:thmMain].

## 1. Fidelity

### Statement proved
`of_mainInternal (h : EG.Spec.MainInternal) : type_of% @Erdos184.erdos_184.{u}`.

A scratch `run_cmd` confirmed the following:
- The elaborated type of `of_mainInternal` is a single `∀` binder whose domain is exactly the
  constant `EG.Spec.MainInternal`.
- Its body is `Expr.equal` to the type of `Erdos184.erdos_184`, after renaming `u_1 ↦ u`.

So there are no extra hypotheses, no weakened quantifiers and no changed instances. Re-running the
`Final.lean` identity check on a copy of `solution` also passes.

The statement is universe-polymorphic: `#check @of_mainInternal.{0}` and `.{5}` both elaborate.

### Back-translation of the upstream target
There is a function f : ℕ → ℝ with f = O(n) such that the following holds. For every finite type
V (any universe, with its given `Fintype` / `DecidableEq`) and every simple graph G on V, there is
a finite set D of subgraphs of G with three properties:
- each member's coe is either connected and 2-regular, or has exactly one edge (classical
  instances);
- the members' edge sets are pairwise disjoint and their union is E(G);
- |D| ≤ f(|V|).

### Back-translation of `MainInternal` (Spec, not in scope)
There is c ∈ ℕ such that every simple graph on a finite `V : Type` has a list of well-formed
objects satisfying three properties:
- each object is a non-loop edge, or a vertex list with no repeats and length ≥ 3;
- the concatenated edge lists have no repeats;
- the concatenated edge lists contain exactly E(G), and the list has length at most c·|V|.

This matches [s1:defObject]: "An *object* is a cycle (of length at least 3) or a single edge. A
*decomposition* of an edge set F is a partition of F into the edge sets of objects". It also
matches [s1:thmMain], "every graph G on n vertices satisfies f(G) ≤ c_EG n", with c_EG rounded up
to a natural number.

### Proof, back-translated
1. Take `f n = c·n`. Then f = O(n) by `isBigO_refl.const_mul_left`.
2. Transport G along `Fintype.equivFin V` to `Fin |V| : Type` and apply `MainInternal` there.
3. Map the objects back with `objMap e.symm`, which applies `Sym2.map` to an edge and `List.map`
   to a cycle.
4. `isDecomp_comap_symm` checks that the result is a decomposition:
   - well-formedness is preserved by injectivity;
   - `Nodup` is preserved by `Sym2.map.injective`;
   - coverage follows from `mem_edgeSet_comap`.
5. Send each object o to `toSub G o`, whose vertices are the endpoints of o's edges and whose
   adjacency is `s(a,b) ∈ o.edges ∧ G.Adj a b`.
6. Edge object: the subgraph's edge set is `{e}`, so its coe has exactly one edge. This is
   transported by the injectivity of `Sym2.map Subtype.val` and `Subgraph.image_coe_edgeSet_coe`.
7. Cycle object `a :: l`: `toSub` equals the `toSubgraph` of the closed walk
   `a, l₀, …, a`. That walk is a Mathlib `IsCycle`:
   - trail, because the object's edge list is `Nodup` (from `IsDecomp`);
   - not nil, because its length is at least 3;
   - `support.tail = (a::l).rotate 1` is `Nodup`.

   Mathlib's `toSubgraph_connected` and `IsCycle.ncard_neighborSet_toSubgraph_eq_two` then give
   connected and 2-regular.
8. Distinct members have disjoint edge sets by `eq_of_mem_of_nodup_flatMap`. The union is E(G).
   Finally |toFinset| ≤ length ≤ c·|V|.

This is exactly the intended argument, and every step is sound.

### Edge cases
- **n = 0.** D = [] and the bound 0 is fine. The transport through `Fin 0` is uniform.
- **Loops.** `Obj.WF` excludes diagonal edges. `SimpleGraph` has no loops, so coverage alone
  would exclude them anyway.
- **Duplicate subgraphs.** Two objects mapping to the same subgraph only lower `card`. Disjointness
  concerns only distinct members, and it is proved through the objects.
- **Classical instances.** `IsCycleOrEdge H.coe` uses a `Fintype H.verts` instance chosen under
  `open scoped Classical`. The helpers are stated for an arbitrary instance
  (`∀ inst : Fintype H.verts, @IsCycleOrEdge _ inst H.coe`), through `degree_eq_ncard` and
  `card_edgeFinset_eq_ncard`. This is robust: no instance-defeq or `convert` fragility.

### Docstrings
The `BridgeLemmas` module docstring quotes [s1:defObject] verbatim, and it matches `s1.tex`
lines 354–357. No declaration in these files formalizes a new manuscript notion. `toSub`,
`cycleWalk` and the other helpers are glue.

## 2. Vacuity and triviality
The bridge is an implication with an exact upstream conclusion, so it cannot be vacuous on the
output side. On the input side, `MainInternal` is a frozen Spec. It is not trivially true: for
K_n, any `IsDecomp` has a length that grows with the number of edges unless the objects are real
cycles. It is not contradictory either: the empty graph on n = 0 is satisfied by `D = []`.

Scratch probes, all of which compile against the built modules:
- `IsDecomp (⊤ : SimpleGraph (Fin 3)).edgeSet [.cycle [0,1,2]]` is provable. Fed to
  `exists_finset_of_isDecomp`, it yields an upstream decomposition with `card ≤ 1`. So the
  hypotheses of the helper are satisfiable by genuine data.
- `(toSub ⊤ (.cycle [0,1,2])).Adj 0 1`: the produced subgraph is not degenerate.
- `¬ (Obj.cycle [0,1]).WF`, `¬ (Obj.edge s(0,0)).WF`, and
  `¬ IsDecomp (⊤ : Fin 3).edgeSet [.edge s(0,1)]`: bad objects and bad decompositions are
  rejected.

I found no route to `False`, and no trivial proof of any statement involved.

## 3. Soundness hygiene
- `lake build EGCheck.Bridge`: success (a replay). The only warning is the expected `sorry` in
  `EG/Proof/Main.lean`. `BridgeLemmas` and `Bridge` have no warnings.
- `python3 scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EGCheck EGCheck.Bridge` inspected 66
  constants. It reports 1 `sorryAx` user (`EGCheck.Bridge.solution`) and 0 violations.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `of_mainInternal`,
  `exists_finset_of_isDecomp` and `isDecomp_comap_symm`. For `solution` it gives the same plus
  `sorryAx`, which comes only through `EG.Proof.mainInternal`.
- `lake env lean EGCheck/Final.lean` (elaboration only, no build):
  - the statement-identity `run_cmd` passes;
  - `#guard_msgs` fails only because `sorryAx` appears. This is expected before P4.
- No trust-boundary or protected file changed. `git log` shows `EG/Spec/Main.lean`,
  `EG/Defs/Objects.lean`, `EG/Proof/Main.lean` and `EGCheck/Final.lean` unchanged since `fc2f8ff`.
  `FormalConjectures` is imported only under `EGCheck/`.

## 4. Usability
The bridge is terminal, so downstream code never uses it. The remarks below are about reuse
only.

- **(cosmetic) Move general lemmas into `EG/Lib`.** Several lemmas do not depend on
  `FormalConjectures`:
  - `objMap`, `edges_objMap`, `cycleEdges_map`, `wf_objMap`;
  - `length_cycleEdges`, `eq_of_mem_of_nodup_flatMap`;
  - `cycleWalk`, `isCycle_cycleWalk`.

  The proof side (s5 to s7 decomposition gluing, induced subgraphs on subtypes) will need
  transport of `IsDecomp` along injective maps and concatenation of decompositions of disjoint
  edge sets. `EG` cannot import `EGCheck`, so these lemmas would otherwise be duplicated.
  Suggestion: when the first proof node needs them, move them into an `EG/Lib/Found/Objects.lean`
  module. At the same time, generalize `isDecomp_comap_symm` to an injective `f`:
  `IsDecomp E D → IsDecomp (Sym2.map f '' E) (D.map (objMap f))`, and add `IsDecomp_append`.
  This is not needed for this task.
- **(cosmetic) PLAN wording.** PLAN §3 decision 8 still writes `IsDecomp (edgeFinset G) D`. The
  frozen Spec uses `G.edgeSet`, as the design note says. The integrator may want to align the
  PLAN text. This has no effect on the Lean side.
- **(cosmetic) Missing label.** The `of_mainInternal` docstring could cite [s1:thmMain], since
  `MainInternal` formalizes it, per the convention of tagging with manuscript labels. This is
  optional, because the bridge itself is not a manuscript statement.
