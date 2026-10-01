# Clean-room review, round 2: task [gate] (Lemma GATE, s6:lemGATE)

Reviewer: clean-room agent (round 2). I did not edit any Lean file. Scratch checks ran in files
outside the repository (session scratchpad: `GateReview2.lean`, `GateReview2b.lean`,
`GateReview2c.lean`), elaborated with `lake env lean` from `formal/`.

**Verdict: APPROVE.** I found no defect in fidelity, vacuity or soundness. The two statements are
faithful to [s6:lemGATE]. The definitions in `EG.Defs.Orient` are faithful to the s6 preamble,
including the two definitions added in fix round 1 (`walkArcs`, `IsDirPathIn`). The proof is
complete (0 `sorry`, standard axioms only). The open items are one minor usability gap (the link
between `outDeg`/`inDeg` and `degE`, which MED (b) needs) and several cosmetics.

Files reviewed:
- `EG/Defs/Orient.lean`
- `EG/Spec/Chain/Gate.lean`
- `EG/Lib/Found/Orient.lean`
- `EG/Proof/Chain/Gate.lean`
- `EGTest/Gate.lean`
- the design note `work/p1b/gate.md`
- the round-1 review `work/p1b/gate.review1.md`

Manuscript passages checked:
- s6.tex line 12 (preamble) and lines 16–31 (Lemma GATE and its proof);
- lines 41–87 (clusters, MED and its proof);
- lines 179–218 (HCC-P Steps 1–4);
- line 502 ("an acyclic orientation with an arc has a source");
- s1.tex `s1:defObject` (line 354), `s1:convGraphs` (line 321) and `s1:citEuler` (line 881).

The v6 revision work (`proofs/manuscript/v6work/`) does not change GATE or the s6 preamble. R7 §6.9
notes that `s1:citEuler`(c) has no user, so the formalization does not need it.

## 1. Fidelity: back-translation

### Definitions (`EG.Defs.Orient`)

| Lean | Plain mathematics | Manuscript text | Faithful? |
|---|---|---|---|
| `cycleArcs c` = `zip c (c.rotate 1)` | the arcs `c₀→c₁, …, c_{k-2}→c_{k-1}, c_{k-1}→c₀`; `[v] ↦ [(v,v)]`, `[] ↦ []` | auxiliary | yes (`cycleEdges_eq_map_cycleArcs` links it to `EG.cycleEdges`) |
| `IsOrientation F A` | every arc `(u,v) ∈ A` has `u ≠ v` and `uv ∈ F`, and each `e ∈ F` is `uv` for exactly one `(u,v) ∈ A`. So `a ↦ s(a.1,a.2)` is a bijection `A → F`. | [s6:sec] preamble: "Orientations … are those of digraphs obtained by orienting edges of `G`; each edge receives exactly one direction." | yes. If `F` contains a loop, the predicate is false. That is correct, and checked below. |
| `outDeg A v`, `inDeg A v` | `\|{(v,w) ∈ A}\|`, `\|{(u,v) ∈ A}\|` | `d⁺_{F⃗}(v)`, `d⁻_{F⃗}(v)` | yes |
| `IsBalanced A` | `d⁺(v) = d⁻(v)` for every `v : V` | "`d⁺_{F⃗}(v)=d⁻_{F⃗}(v)` at every vertex `v`" | yes. Both degrees are `0` off the arcs, so quantifying over all of `V` is equivalent. |
| `walkArcs p` = `zip p p.tail` (new) | the arcs `v₀→v₁, …, v_{k-1}→v_k`; empty for `[]` and `[v]` | auxiliary | yes (`walkEdges_eq_map_walkArcs`) |
| `IsDirPathIn A p` (new) | `p` is non-empty, has no repeated vertex, and all its consecutive arcs lie in `A` | preamble: "directed paths … are those of digraphs obtained by orienting edges of `G`"; the GATE proof: "a directed path in `F⃗` with pairwise distinct vertices" | yes. It mirrors `EG.IsPathIn` exactly, including the length-0 path `[v]`. See cosmetic C1. |
| `IsDirCycle A c` | `c` is non-empty, has no repeated vertex, and all arcs `c₀→…→c_{k-1}→c₀` lie in `A`, for any `k ≥ 1` | "directed cycle" | yes. `k = 1` (a loop) and `k = 2` (a digon) cannot occur in a subset of an orientation (`IsDirCycle.three_le_length_of_isOrientation`), so on every digraph the manuscript considers, this agrees with any convention. |
| `IsAcyclic A` | no `c` with `IsDirCycle A c` | "A digraph is *acyclic* if it has no directed cycle." | yes. This is the literal notion. As a hypothesis it is implied by "no closed directed walk", so the statement is at least as strong as under that reading. |

Parallel arcs cannot be represented, because an arc set is a `Finset (V × V)`. This is faithful:
distinct edges of a simple graph have distinct ends, and each edge gets one direction. The module
docstring says so.

### Statements (`EG.Spec.Chain.Gate`)

`#print EG.Spec.GateStatement` (verified):

```
∀ (V : Type u) [DecidableEq V] (G : FGraph V) (F : Finset (Sym2 V)) (A W : Finset (V × V)),
  F ⊆ G.edges → IsOrientation F A → IsBalanced A → W ⊆ A → IsAcyclic (A \ W) →
  ∃ D, IsDecomp ↑F D ∧ D.length ≤ W.card ∧ ∀ o ∈ D, (∃ c, o = Obj.cycle c) ∧ ∀ e ∈ o.edges, e ∈ G.edges
```

**Plain reading.** Let `G` be a finite simple graph with `F ⊆ E(G)`. Let `A` be an orientation of
`F` with `d⁺ = d⁻` at every vertex, and let `W ⊆ A` be such that `A \ W` has no directed cycle.
Then there is a list `D` of objects with these properties:
- each object is well formed (a cycle has `≥ 3` distinct vertices);
- their edge lists are pairwise disjoint, have no duplicates, and together cover exactly `F`;
- `|D| ≤ |W|`;
- every object is a cycle all of whose edges are edges of `G`.

**Manuscript [s6:lemGATE].** "Let `F⊆E(G)` and let `F⃗` be an orientation of `F` with
`d⁺_{F⃗}(v)=d⁻_{F⃗}(v)` at every vertex `v`. Let `𝒲` be a set of arcs of `F⃗` such that `F⃗−𝒲` is
acyclic. Then `F` decomposes into at most `|𝒲|` cycles of `G`."

[s1:defObject]: "An *object* is a cycle (of length at least 3) or a single edge. A
*decomposition* of an edge set `F` is a partition of `F` into the edge sets of objects."

| Point | Check |
|---|---|
| Quantifiers | `G` is any finite simple graph, not only the input graph, so the statement is more general. `V` is universe polymorphic: `EG.gate` instantiates at `GateStatement.{0}` and `GateStatement.{1}` (checked). `[DecidableEq V]` is universally quantified, so any instance works, including a classical one (checked). |
| Hypotheses | Exactly the manuscript's: `F ⊆ E(G)`; the orientation; balance; "a set of arcs of `F⃗`" (`W ⊆ A`); "`F⃗ − 𝒲` acyclic" (`A \ W`). There are no hidden extra hypotheses. `W ⊆ A` is the manuscript's own hypothesis. It is dispensable, since `A \ W = A \ (W ∩ A)` and `\|W ∩ A\| ≤ \|W\|`, but keeping it is faithful. |
| Inequality | "at most `\|𝒲\|`" is `D.length ≤ W.card`, non-strict. Correct. |
| Multiplicity | `IsDecomp` means a duplicate-free concatenation with exact coverage, i.e. a partition. |
| "cycles of `G`" | `Obj.cycle c` with `c.Nodup ∧ 3 ≤ c.length`, all edges in `E(G)`. Each vertex of `c` is an end of an edge of `c`, so `FGraph.edge_verts` puts it in `V(G)`. |
| Edge cases | For `F = ∅`: `D = []`. For `W = ∅`: the statement says a balanced acyclic orientation is empty. I derived this from `gate` in the scratch file (`balanced_acyclic_empty`), so the statement has real content. |

`#print EG.Spec.GatePreciseStatement` (verified) concludes `∃ cs : List (List V)` such that:
- every `c ∈ cs` satisfies `IsDirCycle A c`, `3 ≤ c.length`, `(Obj.cycle c).WF`, `cycleEdges c ⊆ E(G)` and
  `∃ w ∈ W, w ∈ cycleArcs c`;
- `(cs.flatMap cycleArcs).Nodup`;
- `∀ a, a ∈ cs.flatMap cycleArcs ↔ a ∈ A`;
- `cs.length ≤ W.card`.

This is the manuscript's "More precisely, `F⃗` is the arc-disjoint union of directed cycles, each of
length at least 3, each the orientation of a cycle of `G`, and each containing an arc of `𝒲`; there
are at most `|𝒲|` of them." Nothing is missing. The `WF` conjunct repeats `Nodup`/`3 ≤ length`,
which is harmless.

`EG.gate_with_cycles` (Proof) combines both conclusions. It returns the decomposition
`cs.map Obj.cycle` together with the per-cycle directed data. This is the form that HCC-P Step 4
needs ("Each of them is the orientation of a directed cycle `C` of `F⃗` of length at least 3
containing an arc of `𝒲`"; then "Take a maximal subpath of `C` that contains no arc of `𝒲`").

**Proof fidelity.** The Lib argument runs the manuscript's maximal-path argument backwards. It
extends a directed path through an in-arc of its first vertex (possible because `d⁺ ≤ d⁻`) until
the path closes. It excludes length 1 by looplessness and length 2 by "no antiparallel arcs". The
latter is `IsOrientation.not_mem_swap`, the formal content of "two distinct edges of `F` with the
same ends, impossible since `G` is simple". The rest is as in the manuscript:
- induction on the arc set, deleting a cycle (`IsBalanced.sdiff_cycleArcs`);
- "each `C_i` contains an arc of `𝒲`";
- the counting step `p ≤ |𝒲|`.

The round-1 fixes are in place and correct. The lemmas added in fix round 1 have correct
docstrings and cite the right lines:
- `IsAcyclic.exists_source` matches s6 line 502: a source has `d⁻ = 0 < d⁺`, which "must be a port
  of positive excess";
- `IsAcyclic.exists_potential` matches HCC-P Step 3: `tp_j : T_j → {1,…,|T_j|}`, with `S = T_j`
  for the arcs of `D'_j[T_j]`;
- `isAcyclic_of_potential` matches MED (a) and HCC-P Step 3.

## 2. Vacuity and triviality (scratch files outside the repository)

Everything below elaborates without errors (`GateReview2.lean`):
- **The statement has content.** From `gate` with `W = ∅`: every orientation of `F ⊆ E(G)` that is
  balanced and acyclic has `F = ∅`. This is the non-trivial fact that every non-empty balanced
  orientation has a directed cycle.
- **The bound is attained.** A directed 4-cycle with `W = {3→0}` satisfies all the hypotheses.
  `A \ W` is acyclic by a potential, and with `W = ∅` it is not. So `|D| = 1 = |W|` is forced.
- **`IsAcyclic` is not trivial.**
  - The transitive triangle `{0→1, 1→2, 0→2}` is acyclic but not balanced.
  - The digon `{0→1, 1→0}` is not acyclic.
  - `IsDirCycle A₃` holds for the rotations `[1,2,0]` and `[2,0,1]`, and fails for the reversal
    `[0,2,1]`, for `[]` and for `[0,1]`.
- **`IsOrientation` is not trivial.** No arc set orients `{s(1,1)}` (a loop). EGTest checks the
  antiparallel pair, the missing edge, and the loop arc.
- **`IsDirPathIn` is not trivial.** `[2,0,1]` is a directed path of `A₃`, and `[]` is not.
  `IsDirPathIn ∅ [2]` holds; see cosmetic C1.
- **The hypotheses are jointly satisfiable in non-degenerate cases.** EGTest has the triangle (one
  `W`-arc) and the bowtie (two `W`-arcs, built with `of_subset_edges` and `union`).
- I found no way to prove `False` or the statement trivially. All the definitions are plain
  `def`/`structure` with no axioms.

## 3. Soundness hygiene

- `lake build EG.Proof.Chain.Gate`: success (781 jobs).
- `scripts/check.sh EGTest/Gate.lean`: rc=0, 0 errors, 0 sorry warnings.
- `python3 scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Chain.Gate EG.Lib.Found.Orient
  EG.Spec.Chain.Gate EG.Defs.Orient`: 239 constants inspected, 0 use `sorryAx`, 0 violations.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `EG.gate`, `EG.gate_precise`,
  `EG.gate_with_cycles` and `EG.IsAcyclic.exists_potential`.
- There is no `set_option` in any of the five files.
- Module headers follow AGENTS.md:
  - `@[expose] public section` in Defs and Spec, `public section` in Lib and Proof;
  - the Spec imports only Defs (`EG.Defs.Graph`, `EG.Defs.Orient`);
  - EGTest is a plain file.
- Bridge: not applicable to this task.

## 4. Usability (MED, HCC-P, and the source argument at s6 line 502)

The representation fits the downstream uses well:
- An admissible orientation is `IsOrientation B A ∧ IsAcyclic A ∧ ∀ h ∈ hubs, outDeg A h =
  inDeg A h`.
- `exc(u)` is `(outDeg A u : ℤ) - inDeg A u`.
- HCC-P's `D_j` is `(𝒫_j.flatMap walkArcs).toFinset`.
- HCC-P's `F⃗` is built with `IsOrientation.union` and `IsBalanced.union`.
- `Ψ` is a real potential, handled by `isAcyclic_of_potential`.

### U1 (minor): no lemma links directed degrees to `degE`

There is no lemma `outDeg A v + inDeg A v = degE F v` for an orientation `A` of `F`. MED (b) needs
it three times:
- "`exc(u)` is a sum of ±1 over the `deg_{B_𝒦}(u)` beads at `u`", which gives `|exc(u)| ≤ deg`
  and the parity claim;
- "`d⁻(h) = deg_{B_𝒦}(h)/2` at every hub";
- MED (a), "Every hub of degree `2d` has exactly `d` in-arcs and `d` out-arcs".

This is the only bridge between the directed degrees of `EG.Defs.Orient` and the undirected
`EG.degE` of `EG.Defs.Graph`. I proved it in the scratch file (`GateReview2c.lean`, about 25
lines, using `loopless`, `IsOrientation.inj` and `exists_mem`), so it follows from the current API.
Suggested addition to `EG.Lib.Found.Orient`:
`IsOrientation.outDeg_add_inDeg (hA : IsOrientation F A) (v : V) : outDeg A v + inDeg A v = degE F v`.

### U2 (cosmetic): helpers for HCC-P

These are not needed for GATE. HCC-P will need them, and they are cheap now:
- `IsDirPathIn.isPathIn (hA : IsOrientation F A) : IsDirPathIn A p → IsPathIn F p`, and the same
  for `IsDirCycle` to a cycle of `F`. Both follow from `walkEdges_eq_map_walkArcs` and
  `cycleEdges_eq_map_cycleArcs`.
- `IsDirCycle.rotate`: `IsDirCycle A c → IsDirCycle A (c.rotate n)`, with `cycleArcs (c.rotate n)` a
  rotation of `cycleArcs c`. HCC-P Step 4 starts `C` "at the head of a `𝒲`-arc".
- An orientation of a path: `p.Nodup → IsOrientation (walkEdges p).toFinset (walkArcs p).toFinset`.
  HCC-P Step 1 needs it: "Orient every path of `𝒫_j` from its first to its last vertex".
- A cancellation lemma for HCC-P Step 1 ("Delete directed cycles from `D_j` one at a time until
  no directed cycle remains"): for every finite `A` there are arc-disjoint directed cycles
  `cs ⊆ A` with `IsAcyclic (A \ ⋃ cycleArcs)`. It is the same strong induction as
  `exists_dirCycle_decomp`. The design note lists it as open.
- A constructor that avoids the `∃!` bookkeeping, for MED's "Every bead is oriented exactly once"
  and for the EGTest pattern `revert a; decide`:
  `isOrientation_iff : IsOrientation F A ↔ (∀ a ∈ A, a.1 ≠ a.2) ∧ A.image (fun a => s(a.1, a.2)) = F ∧ Set.InjOn (fun a => s(a.1, a.2)) A`.

## 5. Cosmetic

- **C1.** The `IsDirPathIn` docstring says "`[v]` is a directed path of length `0`". Unlike
  `EG.IsPathIn`, it does not warn that this holds in every arc set, even when `v` is not an end of
  any arc (`IsDirPathIn ∅ [2]`, checked). Copy the `IsPathIn` warning. The docstring also cites
  "[s1:convGraphs] (d)" for `IsPathIn`, but (d) defines "path through `V`", not paths. That
  citation is loose.
- **C2.** `EG.arcVerts` is a public `def` in `public section` (Lib) without `@[expose]`, and it
  appears in the statement of the public theorem `EG.exists_dirCycle_aux`. A module that imports it
  cannot unfold it: `unfold arcVerts` fails and `decide` gets stuck (checked in
  `GateReview2b.lean`). There is also no `mem_arcVerts` iff lemma, only the two introduction
  lemmas. Either add `@[expose]` or a `@[simp] mem_arcVerts`, or make `exists_dirCycle_aux` and
  `arcVerts` private.
- **C3.** `exists_dirCycle_aux` has no docstring.

## Summary of issues

| # | Severity | Location | Issue |
|---|---|---|---|
| U1 | minor | `EG/Lib/Found/Orient.lean` | no `outDeg + inDeg = degE` for orientations (needed by MED (a), (b)) |
| U2 | cosmetic | `EG/Lib/Found/Orient.lean` | HCC-P helpers (dirPath → path, cycle rotation, orienting a path, cancellation, `isOrientation_iff`) |
| C1 | cosmetic | `EG/Defs/Orient.lean` (`IsDirPathIn` docstring) | missing warning about the length-0 path `[v]`; loose citation |
| C2 | cosmetic | `EG/Lib/Found/Orient.lean` (`arcVerts`) | not exposed and no membership iff lemma |
| C3 | cosmetic | `EG/Lib/Found/Orient.lean` (`exists_dirCycle_aux`) | no docstring |

None of these affects the correctness or fidelity of `GateStatement`, `GatePreciseStatement` or
their proofs.
