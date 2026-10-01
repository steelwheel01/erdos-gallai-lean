# P1b: bridge `EG.Spec.MainInternal ⇒ Erdos184.erdos_184`: design note

Task [bridge]. Status: `EGCheck.Bridge.of_mainInternal` is proved with 0 sorry. Both files compile
with 0 errors and 0 warnings, and the lint is clean. The axiom scan
(`lake env lean --run scripts/Axioms.lean --prefix EGCheck EGCheck.Bridge`) inspects 66 constants
and finds 0 violations. The only constant that uses `sorryAx` is `EGCheck.Bridge.solution`, and
it gets it through `EG.Proof.mainInternal`. `of_mainInternal`, `exists_finset_of_isDecomp` and
`isDecomp_comap_symm` depend only on `propext`, `Classical.choice` and `Quot.sound`.

`EGCheck/Final.lean` was compiled but not edited. Its statement-identity `run_cmd` check passes.
Its `#guard_msgs` fails, as expected before P4: the axiom list contains `sorryAx`, which comes
from `mainInternal`.

## Files
| File | Contents |
|---|---|
| `EGCheck/BridgeLemmas.lean` (new, plain file; imports `EG.Defs.Objects` and `FormalConjectures.ErdosProblems.«184»`) | all helper definitions and lemmas (below) |
| `EGCheck/Bridge.lean` (edited) | added `import EGCheck.BridgeLemmas`; proved `of_mainInternal`. `solution` is unchanged. |

The new module to add to the `EGCheck` root is `EGCheck.BridgeLemmas`. `Bridge.lean` already
imports it, so nothing else is needed.

## Construction
1. **`toSub G o : G.Subgraph`** is the subgraph spanned by the edge list of an object. Its
   vertices are `{v | ∃ e ∈ o.edges, v ∈ e}`, and `a ~ b` holds iff `s(a,b) ∈ o.edges ∧ G.Adj a b`.
   The function is total, with no proof arguments, so the `Finset` is simply
   `(D.map (toSub G)).toFinset`. `mem_edgeSet_toSub` gives
   `e ∈ (toSub G o).edgeSet ↔ e ∈ o.edges ∧ e ∈ G.edgeSet`.
2. **Cycles.**
   - `listWalk G a l h` is the walk `a, l₀, l₁, …`. Its endpoint is the custom `lastOf a l`,
     because `List.getLastD` does not reduce definitionally on `cons`.
   - `cycleWalk G a l h : G.Walk a a` is `listWalk G a (l ++ [a])` after a `copy` along the
     endpoint.
   - The edges of `cycleWalk` are exactly `EG.cycleEdges (a :: l)` (`cycleEdges_cons`, via
     `rotate 1`), and its support is `a :: l ++ [a]`.
   - `isCycle_cycleWalk` uses `Walk.isCycle_def`:
     - trail: the edge list is `Nodup`. This comes from `IsDecomp`, not from a new lemma about
       `cycleEdges`.
     - not nil: the length is at least 3.
     - `support.tail = (a :: l).rotate 1` is `Nodup`.
   - `toSub_cycle_eq` proves `toSub G (cycle (a :: l)) = (cycleWalk …).toSubgraph` with
     `Subgraph.ext`, `Walk.mem_support_iff_exists_mem_edges_of_not_nil` and
     `Walk.adj_toSubgraph_iff_mem_edges`.
   - Mathlib then supplies connectivity (`Walk.toSubgraph_connected`) and 2-regularity
     (`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`, together with
     `Subgraph.coeNeighborSetEquiv`).
3. **Edges.** `(toSub G (edge e)).edgeSet = {e}`. The coe's edge count is transported with
   `Subgraph.image_coe_edgeSet_coe` and the injectivity of `Sym2.map Subtype.val`.
4. **Classical instances.** The upstream `IsCycleOrEdge H.coe` contains a `Fintype H.verts`
   instance chosen by `open scoped Classical`, and its body uses classical `LocallyFinite` and
   `Fintype edgeSet` instances. All helper lemmas therefore take the `Fintype H.verts` instance as
   an **explicit** argument, `(inst : Fintype H.verts) → @IsCycleOrEdge _ inst H.coe`. They go
   through `degree_eq_ncard` and `card_edgeFinset_eq_ncard`, which hold for an arbitrary
   instance. No `Subsingleton` or `convert` argument is needed.
5. **`exists_finset_of_isDecomp`.**
   - Pairwise disjointness: distinct members come from distinct objects, whose edge lists are
     disjoint by `eq_of_mem_of_nodup_flatMap`, a small induction on the `Nodup` of the
     concatenation.
   - Union: `List.mem_flatMap` together with the `↔` clause of `IsDecomp`.
   - Size: `card ≤ length` by `List.toFinset_card_le`.
6. **Transport (universes).**
   - `objMap f` maps an edge to `Sym2.map f` of it, and a cycle list to `List.map f` of it.
     `edges_objMap` states `(objMap f o).edges = o.edges.map (Sym2.map f)`.
   - `isDecomp_comap_symm` takes `e : V ≃ W` and a decomposition of `G.comap e.symm`, and gives
     a decomposition of `G` by mapping along `e.symm`.
   - In `of_mainInternal`, `W = Fin (Fintype.card V) : Type` and `V : Type u`, and
     `f := fun n ↦ (c : ℝ) * (n : ℝ)`. `f =O[atTop] id` holds by `isBigO_refl.const_mul_left`.

## Deviations from the plan
- The plan's cycle subgraph is `Walk.IsCycle.toSubgraph`. The bridge uses one uniform
  `toSub`, which it proves equal to the cycle walk's `toSubgraph`, so the object-to-subgraph map
  needs no dependent proofs.
- `MainInternal` is stated with `G.edgeSet`, not `edgeFinset G` as PLAN decision 8 writes. This
  makes no difference to the bridge.
- The helper file is a plain Lean file, as the task allows. It is not a module.

## Open questions and remarks
- None blocking. `EG.Obj.WF` together with the `Nodup` of the concatenated edges is exactly
  enough. The bridge never needs "`c.Nodup` and `3 ≤ length` imply `(cycleEdges c).Nodup`",
  because `IsDecomp` already provides edge `Nodup`.
- The internal statement is at least as strong as needed. `c : ℕ` is uniform over all
  `V : Type`, and `Fintype.card (Fin n) = n` is used with the canonical `Fin` instances.
