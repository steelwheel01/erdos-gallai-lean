# Clean-room review, round 1: task [gate] (Lemma GATE, s6:lemGATE)

Reviewer: clean-room agent (round 1). I did not edit any Lean file. Scratch checks were done in a
file outside the repo (session scratchpad, `GateReview.lean`, importing `EG.Proof.Chain.Gate`).

**Verdict: APPROVE.** There are no fidelity, vacuity or soundness defects. The formal statement is
equivalent to the manuscript statement, and its conclusion is slightly stronger. The open items
below are usability points for later consumers (HCC-P, MED, the J-set/cluster code), plus
cosmetics. One sentence in the design note is inaccurate about what HCC-P needs.

Files reviewed:
- `EG/Defs/Orient.lean`
- `EG/Spec/Chain/Gate.lean`
- `EG/Lib/Found/Orient.lean`
- `EG/Proof/Chain/Gate.lean`
- `EGTest/Gate.lean`
- the design note `work/p1b/gate.md`

Manuscript sources: s6.tex, which has the preamble (line 12), Lemma GATE and its proof (lines
16–35), the HCC-P proof (Steps 1–4, lines 165–218) and line 502. From s1.tex: `s1:defObject`.

## 1. Fidelity: back-translation

### Definitions (`EG.Defs.Orient`)

| Lean | Plain mathematics | Manuscript | OK? |
|---|---|---|---|
| `cycleArcs c` | For `c = c₀…c_{k-1}`: the arcs `(c₀,c₁),…,(c_{k-2},c_{k-1}),(c_{k-1},c₀)`. For `[v]` this is `[(v,v)]`; for `[]` it is empty. | (auxiliary) | yes |
| `IsOrientation F A` | Every arc `(u,v) ∈ A` has `u ≠ v` and `uv ∈ F`, and every `e ∈ F` is `uv` for exactly one `(u,v) ∈ A`. | Preamble: "Orientations … are those of digraphs obtained by orienting edges of `G`; each edge receives exactly one direction." | yes. `loopless` follows from `mem` whenever `F` has no loops (as in GATE, where `F ⊆ E(G)`). If `F` has a loop, the predicate is false, which is the right answer: a loop cannot be oriented as an arc `u→v` with `u≠v`. |
| `outDeg A v`, `inDeg A v` | `\|{(v,w) ∈ A}\|`, `\|{(u,v) ∈ A}\|` | `d⁺_{F⃗}(v)`, `d⁻_{F⃗}(v)` | yes |
| `IsBalanced A` | `d⁺(v) = d⁻(v)` for all `v : V` | "with `d⁺(v)=d⁻(v)` at every vertex `v`" | yes. Quantifying over all of `V`, not only over `V(G)` or the vertices of `F⃗`, is equivalent, because both degrees are `0` off the arcs. |
| `IsDirCycle A c` | `c` is non-empty, has no repeated vertex, and all arcs `c₀→c₁→…→c_{k-1}→c₀` lie in `A` (`k ≥ 1`) | "directed cycle" | yes. For `k=1` it is a loop and for `k=2` a digon. Neither occurs in a subset of an orientation, so on every digraph the manuscript considers ("obtained by orienting edges of `G`") this agrees with every convention for "directed cycle". |
| `IsAcyclic A` | no `c` with `IsDirCycle A c` | "A digraph is *acyclic* if it has no directed cycle." | yes. This is the literal notion the task asked for. |

### Statements (`EG.Spec.Chain.Gate`)

Printed with `#print EG.Spec.GateStatement`:

```
∀ (V : Type u) [DecidableEq V] (G : FGraph V) (F : Finset (Sym2 V)) (A W : Finset (V × V)),
  F ⊆ G.edges → IsOrientation F A → IsBalanced A → W ⊆ A → IsAcyclic (A \ W) →
  ∃ D, IsDecomp ↑F D ∧ D.length ≤ W.card ∧ ∀ o ∈ D, (∃ c, o = Obj.cycle c) ∧ ∀ e ∈ o.edges, e ∈ G.edges
```

Plain reading: let `G` be a finite simple graph, `F ⊆ E(G)`, and `A` an orientation of `F` with
`d⁺ = d⁻` everywhere. Let `W ⊆ A` be such that `A \ W` has no directed cycle. Then there is a list `D`
of objects with these properties:
- each object is well formed;
- the edge lists of the objects are pairwise disjoint and duplicate free, with union exactly `F`;
- `|D| ≤ |W|`;
- every object is a cycle (by `Obj.WF`, it has `≥ 3` distinct vertices) all of whose edges are in `E(G)`.

Manuscript [s6:lemGATE]: "Let `F⊆E(G)` and let `F⃗` be an orientation of `F` with
`d⁺_{F⃗}(v)=d⁻_{F⃗}(v)` at every vertex `v`. Let `𝒲` be a set of arcs of `F⃗` such that `F⃗−𝒲`
is acyclic. Then `F` decomposes into at most `|𝒲|` cycles of `G`." A decomposition is defined in
[s1:defObject]: "a partition of `F` into the edge sets of objects", where an object is "a cycle (of
length at least 3) or a single edge".

| Point | Check |
|---|---|
| Quantifiers | `G` is an arbitrary finite simple graph, not only "the input graph", so the statement is more general. `V` is universe polymorphic. `[DecidableEq V]` is universally quantified, so any instance can be supplied. |
| Hypotheses | They are exactly `F ⊆ E(G)`, orientation, balance, "set of arcs of `F⃗`" (`W ⊆ A`), and "`F⃗−𝒲` acyclic" (`A \ W`). There are no extra hypotheses. The `loopless` field and the `k = 1, 2` cycles in `IsAcyclic` add nothing, as explained in the table above. |
| Inequality | "at most `\|𝒲\|`": `D.length ≤ W.card` (non-strict). Correct. |
| Multiplicity | `IsDecomp` requires `(D.flatMap edges).Nodup` and exact coverage of `F`, which is a partition. |
| "cycles of `G`" | Every object is `Obj.cycle c` with `c.Nodup ∧ 3 ≤ c.length` (from `IsDecomp`) and all edges in `E(G)`. The cycle's vertices lie in `V(G)` by `FGraph.edge_verts`. Correct. |
| Edge cases | For `F = ∅` we get `D = []`, which is fine. For `W = ∅` the hypothesis forces `A` to be acyclic, hence empty (checked below), and then the conclusion `D = []` is consistent. |

`GatePreciseStatement` gives `∃ cs : List (List V)` such that every `c ∈ cs` satisfies all of:
- `IsDirCycle A c` and `3 ≤ c.length`;
- `(Obj.cycle c).WF`;
- `cycleEdges c ⊆ E(G)`;
- `∃ w ∈ W, w ∈ cycleArcs c`.

Moreover, `cs.flatMap cycleArcs` is duplicate free and has exactly the arcs of `A`, and
`cs.length ≤ |W|`.

This matches the manuscript sentence "`F⃗` is the arc-disjoint union of directed cycles, each of
length at least 3, each the orientation of a cycle of `G`, and each containing an arc of `𝒲`; there
are at most `|𝒲|` of them." The `WF` conjunct duplicates the `Nodup` and length conjuncts, which is
harmless.

Proof-level fidelity: the Lib argument mirrors the manuscript's maximal path. It extends a directed
path backwards through an in-arc of its first vertex, instead of forwards through an out-arc of its
last vertex. It excludes length 1 by looplessness and length 2 by "no antiparallel arcs"
(`IsOrientation.not_mem_swap`), as in the manuscript. The induction on the number of arcs, the
"each `C_i` meets `𝒲`" step and the counting step (`length_le_card_of_pairwise_disjoint`) are
exactly the manuscript's.

## 2. Vacuity and triviality (scratch file, outside the repo)

All of the following checks compile:
- **Non-vacuous hypotheses.** On the bowtie (two cyclically oriented triangles `0-1-2`, `0-3-4` on
  `Fin 5`, with `W = {(0,1),(0,3)}`) all five hypotheses hold. `A \ W` is acyclic via
  `isAcyclic_of_potential`, and `gate` yields a decomposition of the 6 edges into `≤ 2` cycles.
  `EGTest/Gate.lean` also has the triangle instance.
- **The acyclicity hypothesis has teeth.** For the bowtie with `W = {(0,1)}`, `¬ IsAcyclic (A \ W)`
  (the witness is `[0,3,4]`). For the triangle with `W = ∅` it also fails (in EGTest).
- **`IsAcyclic` is not trivially true or false.** `IsAcyclic ∅` holds. `¬ IsAcyclic {(0,1),(1,0)}`
  (digon) and `¬ IsAcyclic {(0,0)}` (loop).
- **The conclusion is not trivially satisfiable.** `IsDecomp` requires exact coverage, and the
  EGTest triangle example derives `D.length = 1` from `gate`.
- `gate` instantiates at `V : Type 1` with a classical `DecidableEq` instance.

I could not prove `False` or the statement trivially, and I see no route to either.

## 3. Soundness hygiene

- `python3 scripts/lint.py`: 0 findings.
- `lake build EG.Proof.Chain.Gate`: success. `scripts/check.sh EGTest/Gate.lean`: 0 errors, 0 sorry
  warnings.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Chain.Gate EG.Lib.Found.Orient
  EG.Spec.Chain.Gate EG.Defs.Orient`: 167 constants, 0 use `sorryAx`, 0 violations.
  `#print axioms EG.gate` and `#print axioms EG.gate_precise` give `[propext, Classical.choice, Quot.sound]`.
- Module headers follow AGENTS.md: `@[expose] public section` in Defs and Spec, `public section` in
  Lib and Proof. The Spec imports only Defs.
- Bridge: not applicable to this task.

## 4. Usability (for HCC-P, MED, cluster code)

1. **(minor) The converse potential direction is needed downstream, and the design note says
   otherwise.** `gate.md` §Definitions 6 says `isAcyclic_of_potential` is "the direction MED (a)
   and HCC-P use". But HCC-P Step 3 (s6 line 201) uses the converse: "One exists because the
   orientation is acyclic: take the position in a topological order …", and "a numbering
   `tp_j : T_j → {1,…,|T_j|}` that increases along the arcs of the acyclic digraph `D'_j[T_j]`".
   s6 line 502 ("an acyclic orientation with an arc has a source") needs the same direction.
   GATE itself does not need it. Before HCC-P, add to `EG.Lib.Found.Orient`:
   - `IsAcyclic.exists_source`: a non-empty acyclic `A` has a vertex with `inDeg = 0` and
     `outDeg > 0`;
   - `IsAcyclic.exists_potential`: on a finite vertex set `S` containing `arcVerts A`, there is an
     injective `f : V → ℕ` with `f` values in `1..|S|` on `S` that strictly increases along the arcs.

   Both follow from the path-extension argument already in the Lib, run forwards. Please also
   correct the sentence in `gate.md`.
2. **(minor) Combination lemmas for orientations.** HCC-P Step 2 builds `F⃗` as the union of cluster
   orientations and the `D'_j`. MED needs balance only at hubs. Useful additions:
   - `IsOrientation.union` for disjoint edge sets;
   - `IsOrientation.mono`/`sdiff`: `A' ⊆ A` orients its image;
   - `outDeg_union`/`inDeg_union` for disjoint arc sets;
   - a constructor `IsOrientation.of_subset_edges (hF : F ⊆ G.edges) mem existsUnique`, which
     derives `loopless`.
3. **(minor) Expose the decomposition behind the precise form.** HCC-P Step 4 needs both "`F`
   decomposes into `≤ |𝒲|` cycles" and, for each cycle, its directed version: it must contain a
   `W`-arc and have length `≥ k`. `gate` builds `D = cs.map Obj.cycle` inline. Factor this out as a
   named theorem, e.g. `isDecomp_map_cycle_of_arcs : IsOrientation F A → (cs.flatMap cycleArcs).Nodup
   → (∀ a, a ∈ cs.flatMap cycleArcs ↔ a ∈ A) → (∀ c ∈ cs, (Obj.cycle c).WF) → IsDecomp ↑F (cs.map
   Obj.cycle)`. Consumers could then use `gate_precise` alone.
4. **(cosmetic) Directed paths.** For the future `IsDirPath` (open question 1), mirror
   `EG.Defs.Walk`: `walkArcs p := List.zip p p.tail` and `IsDirPathIn A p := p ≠ [] ∧ p.Nodup ∧ ∀ a
   ∈ walkArcs p, a ∈ A`, plus `walkEdges p = (walkArcs p).map (fun a => s(a.1, a.2))`. This keeps
   undirected and directed paths transportable, as `cycleEdges_eq_map_cycleArcs` already does for
   cycles.
5. **(cosmetic) Multi-arcs.** Arc sets are `Finset (V × V)`, so parallel arcs cannot be
   represented. This is faithful to "each edge receives exactly one direction". But HCC-P's `D_j`
   (a union of paths of `𝒫_j`) is a digraph only if those paths are edge-disjoint. Check this
   when HCC-P is formalized. `IsDirCycle` including digons is helpful there for the cancellation
   of Step 1.

## 5. Cosmetic

- Generic lemma names in the root `EG` namespace may clash with later Lib files:
  `length_le_card_of_nodup`, `forall_mem_zip_of_isChain`, `length_le_card_of_pairwise_disjoint`,
  `flatMap_edges_map_cycle`. Consider a sub-namespace, e.g. `EG.Orient`, or `private` for
  the purely internal ones. `flatMap_edges_map_cycle` has no docstring.
- EGTest: the docstring "Non-vacuity: the hypothesis of GATE fails for `𝒲 = ∅` (so the bound
  `|𝒲|` is not trivially satisfiable with fewer arcs)" is really a "the acyclicity hypothesis has
  teeth" test. Consider rewording it.
