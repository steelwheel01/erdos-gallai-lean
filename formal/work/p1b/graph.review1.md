# Clean-room review, round 1: task [graph]

Reviewer: clean-room agent (round 1). I did not edit any Lean file. Scratch checks were done in a
file outside the repo (session scratchpad, `GraphReview.lean`, importing `EG.Lib.Found.Graph`).

**Verdict: APPROVE.** There are no fidelity or vacuity defects. There is one minor usability and
design point that should be settled before the Defs freeze (`t : ℕ` in Def 7), plus cosmetic items.

Files reviewed:
- `EG/Defs/Graph.lean`
- `EG/Defs/Walk.lean`
- `EG/Defs/Expander.lean`
- `EG/Lib/Found/Graph.lean`
- `EGTest/Found.lean`
- the design note `work/p1b/graph.md`

Manuscript sources: s1.tex (convGraphs, citNotation, citDef7, citDef11), s2.tex (defWitness), s3.tex
(conventions, lemMonotone, remMultiset, lemL9rho, thmT16s, proof of propP13s) and s4.tex (the
parameters `𝗍`).

## 1. Fidelity: back-translation

Each definition is restated in plain mathematics and compared with the manuscript.

| Lean | Plain mathematics | Manuscript | OK? |
|---|---|---|---|
| `FGraph` | A finite vertex set `V(H)` and a finite set `E(H)` of unordered pairs. Every end of an edge lies in `V(H)`, and no edge is a loop. | s1:convGraphs(a): "Graphs are finite and simple" | yes |
| `card` | `\|V(H)\|` | "(a) `\|H\| := \|V(H)\|`" | yes |
| `Adj u v` | `uv ∈ E(H)` | standard | yes |
| `nbrs v` | `{w ∈ V(H) : vw ∈ E(H)}` | "(c) `N_H(v)` is its set of neighbours" | yes |
| `deg v` | `\|N_H(v)\|`, which equals the number of edges at `v` (`deg_eq_degE`) | "(c) `d_H(v)=deg_H(v)` its degree" | yes |
| `minDeg`, `maxDeg` | min and max of `d_H` over `V(H)`; 0 on the graph with no vertices | "(c) `δ(H)`, `Δ(H)`" | yes (the value on the empty graph is a harmless convention) |
| `edgesAt F v`, `degE F v` | `{e ∈ F : v ∈ e}` and its size | "(c) `deg_F(v)` is the number of edges of `F` at `v`" | yes |
| `nbrSet U` | `{v ∈ V(H)\U : ∃u∈U, uv ∈ E(H)}` | "(c) For `U ⊆ V(H)`, `Nbr_H(U)` is the set of vertices of `V(H)\U` that have a neighbour in `U`." | yes. It is also defined for `U ⊄ V(H)`, which is harmless. |
| `induce U` | vertices `V(H) ∩ U`; the edges of `H` with both ends in `U` | "(c) `H[U]` is the induced subgraph" | yes (for `U ⊆ V(H)`) |
| `deleteVerts U` | `H[V(H)\U]` | "(c) `H−U` and `H\U` both denote `H[V(H)\U]`" | yes |
| `deleteEdges F` | vertices `V(H)`, edges `E(H)\F` | "(c) for `F ⊆ E(H)`, `H−F` ... (keeping all vertices)" | yes. It is total: only `F ∩ E(H)` matters. |
| `edgesBetween A B` | the edges `ab ∈ E(H)` with `a∈A`, `b∈B` | "(c) For disjoint `A,B ⊆ V(H)`, `E_H(A,B)` is the set of edges with one end in `A` and the other in `B`" | yes for disjoint `A`, `B`. The manuscript uses it only for disjoint sets (s2:defWitness `E_H(U,V(H)\(U∪N))`, s2 `E_X(U,W)` with `U ⊆ V(X)\W`; s3 `e_X(U,𝒩\𝒯)`). |
| `ofSimpleGraph` | `(univ, G.edgeFinset)` | task | yes |
| `walkEdges`, `pathLength` | the consecutive pairs of `v₀…v_k`, and `k` | "length" = number of edges | yes |
| `IsPathIn E p` | `p` is non-empty, has no repeated vertex, and every consecutive pair is in `E` | a path | yes |
| `IsPathBetween E x y p` | as above, with first vertex `x` and last vertex `y` | "`xy`-path" | yes |
| `IsThrough W p` | every vertex of `p.tail.dropLast` (the interior) lies in `W` | "(d) A *path through* `V` is a path all of whose interior vertices lie in `V`; its ends are unrestricted." | yes. I checked the cases `k = 0, 1, 2`. |
| `ball H i U W` | `{w ∈ W : ∃u∈U, ∃` a `uw`-path in `H` through `W` with length `≤ i}` | "(d) ... `B^i_H(U,V)` is the set of vertices of `V` that can be reached by a path through `V` of length at most `i` starting at a vertex of `U` (the starting vertex need not lie in `V`)" | yes. The radius `i : ℕ` matches "integer `i ≥ 0`"; `ℓ_* = ⌊2^{10}L^3⌋` is an integer. |
| `IsExpander G ε s` | For all `U ⊆ V(G)` and `F ⊆ E(G)` with `1 ≤ \|U\|`, `\|U\| ≤ 2n/3` (in ℝ) and `\|F\| ≤ s\|U\|` (in ℝ): `ε\|U\|/(log₂ n)² ≤ \|Nbr_{G−F}(U)\|`, where `n = \|V(G)\|`. | s1:citDef11, quoted verbatim in the docstring | yes |
| `IsPathConnected G ℓ t W` | For every finite index type `ι` and every family `P : ι → V×V` in which each `P i` is a pair of distinct vertices of `G` and each vertex `v` is an entry of at most `t` indices: there are paths `Q i`, each a `(P i).1–(P i).2` path in `G` through `W` of length `≤ ℓ`, with pairwise disjoint edge lists for `i ≠ j`. | s1:citDef7 together with its multiset clause and s1:convGraphs(e) | yes |

I checked `IsExpander` against its pretty-printed form (`set_option pp.parens true`):
`((ε * ↑U.card) / ((Real.logb 2 ↑G.card) ^ 2)) ≤ ↑((G.deleteEdges F).nbrSet U).card`.
So `log² n` is the square of `log₂ n`, and `n` is `G.card` cast to ℝ, as intended. For `n ≤ 1`
the definition is vacuous, because no `U` satisfies `1 ≤ |U| ≤ 2n/3`. That agrees with the
manuscript's remark in s2:defWitness ("Then `m ≥ 2`, since a graph on one vertex has no set `U`
...").

- **Log base.** In the scratch file I proved that the single edge `K2` (`n = 2`, `log₂ 2 = 1`) is a
  `(1, 1/2)`-expander but not a `(2, 0)`-expander. With the natural log, `1/ln²2 ≈ 2.08 > 1`, so
  `K2` would not be a `(1,1/2)`-expander. The tests therefore depend on the base being 2.
- **Multiplicity.** The degree hypothesis counts indices, i.e. occurrences, and the conclusion
  gives one path per index. This matches "a pair occurring `k` times receives `k` pairwise
  edge-disjoint paths, and the bound `t` counts occurrences". The test `K2` not
  `(ℓ,2)`-connected shows the clause matters.
- **Through `V ⊆ V(G)`.** The manuscript requires `V ⊆ V(G)`; the formal `W` is arbitrary. A path
  with at least one edge has all its vertices in `V(G)`, and every pair consists of distinct
  vertices. So `IsPathConnected G ℓ t W ↔ IsPathConnected G ℓ t (W ∩ V(G))`. This is a total
  extension, not a change of meaning.
- **B–M remark.** `IsExpander.lt_deg` and `lt_minDeg` prove `s < d_G(v)` and `s < δ(G)` under the
  hypotheses `2 ≤ |G|` and `0 < ε`. The extra hypothesis `0 < ε` is necessary. For `ε ≤ 0`
  every graph is an expander (`isExpander_of_nonpos`), and `(pathGraph 5).IsExpander 0 100` holds
  although `δ = 1`. So the manuscript sentence in s1:citDef11 is literally false without it. This
  is a manuscript wording issue, not a formalization issue. Every use of the remark has
  `ε' ∈ (0,1]`: s3 conventions, and "Taking `U={v}` ... minimum degree greater than `s`" in the
  proof of s3:propP13s/T16*.
- **s3:lemMonotone (i) and (ii).** `IsExpander.of_le`, `IsExpander.mono` and
  `IsPathConnected.mono` have exactly the manuscript hypotheses. (ii) drops `V' ⊆ V(G)`, which
  makes it more general.
- **Bridge.** It is not part of this task. `EGCheck/Bridge.lean` does not import these modules.

## 2. Vacuity and triviality

- **Invariants.** The invariants of `FGraph` are consistent: `P3`, `K4`, `K2` and `pathGraph n`
  are built with `ofEdges` and `ofSimpleGraph`.
- **`IsExpander`** is neither trivially true nor trivially false:
  - `K4` is a `(1,0)`-expander, and my scratch `K2` is a `(1,1/2)`-expander (so the case `s > 0` is
    also non-vacuous);
  - `pathGraph 60` is not a `(1,0)`-expander (checked directly from Def 11), and my scratch `K2`
    is not a `(2,0)`-expander.
- **`IsPathConnected`** is neither trivially true nor trivially false. Complete graphs are
  `(1,1)`-path connected for every index type. `P3` is not `(1,1)`, and `K2` is not `(ℓ,2)` for
  any `ℓ, W`. The only trivial case is `t = 0`: then every graph is `(ℓ,0)`-path connected. I
  proved this in the scratch file: every index would need a vertex in 0 pairs. The manuscript
  behaves the same way, and it only uses `t ≥ 1`.
- **`ball`** is not trivial: tests show `2 ∉ B^1(0,{1,2})` and `2 ∉ B^5(0,{2})`.
- **`IsPathIn`, `IsThrough`** reject repeated vertices and non-edges, and "through" really
  constrains the interior (`P3_path_0_2`).
- **Attempts to prove `False`.** I found nothing: no contradictory fields, and no Prop that is
  always true.

## 3. Soundness hygiene

- `python3 scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EG --no-sorry EG.Defs.Graph EG.Defs.Walk
  EG.Defs.Expander EG.Lib.Found.Graph`: 247 constants, 0 use sorryAx, 0 violations. `#print
  axioms` on `lt_minDeg` and `exists_paths` gives `[propext, Classical.choice, Quot.sound]`.
- `scripts/check.sh EGTest/Found.lean`: rc=0, 0 errors, 0 sorry warnings.
- No `sorry` and no `set_option`.
- The module headers follow AGENTS.md: `@[expose] public section` in Defs and `public section` in
  Lib.

## 4. Issues and suggestions

### M1 (minor, usability and design, to settle before the Defs freeze): `t : ℕ` in Def 7

The design note says: "Nothing in s3–s6 seems to need [a real `t`]." That is not correct.

- s4 uses Def 7 with a real multiplicity `𝗍 := 2^{10}L^8` (s4.tex:104) and `𝗍 := 2^9L^8`
  (s4.tex:331), where `L = log₂ N`.
- These values are passed as `t := 𝗍` to Theorem 16* (s3:thmT16s: "Let `ρ ∈ (0,1]` and
  `t ≥ 1`"). That theorem's hypotheses and bounds use `t` as a real number
  (`s ≥ 2^{135} t L^{28} ρ^{-5}`, `1 − 2^{86} t L^{19}ρ^{-3}N^{-3}`, `s̄_* = 2^{28}tL^8/ρ`).

The formal definition is still faithful up to `⌊t⌋₊`: for real `t ≥ 0`, "at most `t` pairs" is
equivalent to "at most `⌊t⌋₊` pairs", and for `t < 0` both versions are vacuous. The cost falls on
later work: the Spec of T16* and the s4 statements would have to write
`IsPathConnected X ℓ ⌊t⌋₊ V` and explain the floor in their docstrings. There are two fixes:

- **(a), preferred while Defs are still editable:** make `t : ℝ`, with hypothesis
  `((univ.filter …).card : ℝ) ≤ t`. This is literally the manuscript wording.
- **(b):** keep `t : ℕ`, and add to `EG.Lib.Found.Graph` a documented lemma or wrapper
  `IsPathConnectedR G ℓ (t : ℝ) W :↔ IsPathConnected G ℓ ⌊t⌋₊ W` together with
  `card ≤ t ↔ card ≤ ⌊t⌋₊`. Also correct the sentence in the design note.

### C1 (cosmetic, manuscript side): B–M remark needs `ε > 0`

s1:citDef11 should say "for `ε > 0`" (or "`0 < ε ≤ 1`"). This is already flagged in the design
note and should be forwarded to the v6 revision.

### C2 (cosmetic): zero-length paths are not tied to `V(H)`

`IsPathIn E [v]` holds for every `v`, even `v ∉ V(H)`. So `ball H i U W ⊇ U ∩ W` also contains
non-vertices when `U, W ⊄ V(H)`. This is outside the manuscript's domain (`U, V ⊆ V(H)`), but a
downstream "path in `H`" that may have length 0 must add `v ∈ V(H)` by hand. Suggestion: add
`ball_subset_verts (hW : W ⊆ H.verts)` (it is trivial from `ball_subset`), and a one-line warning
in the `IsPathIn` docstring. The existing sentence "a path with at least one edge automatically has
all its vertices in `V(H)`" half-covers this.

### C3 (cosmetic, tests)

The existing tests do not pin down the log base: `K4` and `pathGraph 60` behave the same way with
`ln`. Consider adding the `K2` `(1, 1/2)`-expander example (proof in my scratch file, about 20
lines). It fixes `log₂` and also gives a non-vacuity witness with `s > 0`.

### C4 (usability, optional)

- A converse `FGraph.toSimpleGraph` (`Adj := H.Adj`), with a round-trip lemma, will help the Ext
  layer (long cycles, Lovász, Haxell) and the bridge when citing Mathlib results. Also useful: a
  bridge from `IsPathBetween` to `SimpleGraph.Walk.IsPath` or `Walk.toSubgraph`.
- Joint routing (s3:lemMonotone (iii)) through `Σ k, ι_k` is left to the s3 agent. This is
  acceptable, but a ready-made `IsPathConnected.exists_paths_sigma` would prevent duplicated work.
- `IsPathConnected` and `IsExpander` take the ambient `[DecidableEq V]`. Downstream proofs that
  work classically may need `convert` or `Subsingleton.elim` on instances. This is standard and
  needs no change.

## 5. Summary

The definitions match the manuscript text in quantifiers, strictness (`≥` for Nbr, `≤` for
`|U|`, `|F|`, length and multiplicity), log base (`logb 2`), multiplicity (indexed families) and
edge cases (`n ≤ 1` vacuous, no loops, ends of "through" paths unrestricted). They are non-vacuous,
and the hygiene checks are clean. The only item worth acting on before the freeze is M1 (the type of
`t` in Def 7).
