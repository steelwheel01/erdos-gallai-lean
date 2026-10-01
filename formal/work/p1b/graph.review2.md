# Clean-room review, round 2: task [graph]

Reviewer: clean-room agent (round 2). I did not edit any Lean file. Scratch checks were done in
`GraphReview2.lean` in the session scratchpad, outside the repo, importing `EG.Lib.Found.Graph`.

**Verdict: APPROVE.** I found no fidelity, vacuity or soundness defects. Every round-1 item was
handled correctly. What remains is one manuscript-side wording item (still open) and a few optional
API lemmas.

Files reviewed (current working tree, after fix round 1):
- `EG/Defs/Graph.lean`, `EG/Defs/Walk.lean`, `EG/Defs/Expander.lean`
- `EG/Lib/Found/Graph.lean`
- `EGTest/Found.lean`
- `work/p1b/graph.md` and `work/p1b/graph.review1.md`

Manuscript passages compared:
- s1.tex:321–345: s1:convGraphs (a)–(e)
- s1.tex:402–418: s1:citNotation
- s1.tex:441–456: s1:citDef7
- s1.tex:497–509: s1:citDef11
- s3.tex:27–111: the s3 conventions and s3:lemMonotone
- s3.tex:173–196: s3:remMultiset
- s3.tex:694–790: s3:lemL9rho and s3:thmT16s, for how balls and path connectivity are used
- v6work: no revision touches citDef7, citDef11 or convGraphs.

## 1. Fidelity: back-translation

I read the pretty-printed definitions (`#print` with `pp.parens`), not only the source.

| Lean | Plain mathematics | Manuscript text | Match |
|---|---|---|---|
| `FGraph V` | A finite set `V(H) ⊆ V` and a finite set `E(H)` of unordered pairs. Every end of an edge lies in `V(H)`, and no edge is a loop. | (a) "Graphs are finite and simple" | yes |
| `card` | `\|V(H)\|` | (a) "`\|H\| := \|V(H)\|`" | yes |
| `Adj u v` | `s(u,v) ∈ E(H)` | standard | yes |
| `nbrs v`, `deg v` | `{w ∈ V(H) : vw ∈ E(H)}` and its size. `deg_eq_degE` shows the size equals the number of edges at `v`. | (c) "`N_H(v)` is its set of neighbours and `d_H(v)=deg_H(v)` its degree" | yes |
| `minDeg`, `maxDeg` | `min` / `max` of `d_H` over `V(H)`, and `0` if `V(H) = ∅` | (c) "`δ(H)` and `Δ(H)`" | yes. The value on the empty graph is a convention the manuscript never uses. |
| `edgesAt F v`, `degE F v` | `{e ∈ F : v ∈ e}` and its size | (c) "`deg_F(v)` is the number of edges of `F` at `v`" | yes |
| `nbrSet U` | `{v ∈ V(H) \ U : ∃ u ∈ U, uv ∈ E(H)}` | (c) "For `U ⊆ V(H)`, `Nbr_H(U)` is the set of vertices of `V(H)\U` that have a neighbour in `U`" | yes |
| `induce U` | vertices `V(H) ∩ U`; the edges of `H` with both ends in `U` | (c) "`H[U]` is the induced subgraph" | yes |
| `deleteVerts U` | `H[V(H) \ U]` | (c) "`H−U` and `H\U` both denote `H[V(H)\U]`" | yes |
| `deleteEdges F` | vertices `V(H)`, edges `E(H) \ F` | (c) "for `F ⊆ E(H)`, `H−F` ... (keeping all vertices)" | yes. It is total: only `F ∩ E(H)` matters. |
| `edgesBetween A B`, `eBetween` | `{ab ∈ E(H) : a ∈ A, b ∈ B}` and its size | (c) "For disjoint `A,B ⊆ V(H)`, `E_H(A,B)` is the set of edges with one end in `A` and the other in `B`" | yes for disjoint `A`, `B`, the only case the manuscript uses |
| `ofSimpleGraph`, `toSimpleGraph` | `(univ, G.edgeFinset)`; conversely the `SimpleGraph` on `V` with adjacency `Adj` | task | yes. The round trips are proved. |
| `walkEdges`, `pathLength` | consecutive pairs of `v₀…v_k`, and `k` | "length" = number of edges | yes |
| `IsPathIn E p`, `IsPathBetween E x y p` | `p` is non-empty, has no repeated vertex, and every consecutive pair lies in `E`. `IsPathBetween` adds: `p` starts at `x` and ends at `y`. | a path / an `xy`-path | yes |
| `IsThrough W p` | every vertex of `p.tail.dropLast` lies in `W` | (d) "A *path through* `V` is a path all of whose interior vertices lie in `V`; its ends are unrestricted." | yes |
| `ball H i U W` (`i : ℕ`) | `{w ∈ W : ∃ u ∈ U, ∃` a `uw`-path in `E(H)` through `W` of length `≤ i}` | (d) "For `U,V ⊆ V(H)` and an integer `i ≥ 0`, `B^i_H(U,V)` is the set of vertices of `V` that can be reached by a path through `V` of length at most `i` starting at a vertex of `U` (the starting vertex need not lie in `V`)" | yes. Every radius used downstream is an integer (`ℓ_* = ⌊2^{10}L^3⌋`, s3.tex:227). |
| `IsExpander G ε s` | For all `U ⊆ V(G)` and `F ⊆ E(G)` with `1 ≤ \|U\|`, `\|U\| ≤ 2n/3` and `\|F\| ≤ s\|U\|` (both in ℝ): `ε\|U\| / (log₂ n)² ≤ \|Nbr_{G−F}(U)\|`, where `n = \|V(G)\|`. | s1:citDef11, quoted verbatim | yes |
| `IsPathConnected G ℓ t W` (`ℓ t : ℝ`) | Take any finite index type `ι` and any family `P : ι → V×V` of pairs of distinct vertices of `G` in which every vertex `v` is an entry of at most `t` indices. Then there are paths `Q i`, where `Q i` is a `(P i).1–(P i).2` path in `E(G)` through `W` of length `≤ ℓ`, and `Q i`, `Q j` have disjoint edge lists for `i ≠ j`. | s1:citDef7 with its multiset clause, and (e) "Families of pairs of vertices are *multisets* ... 'every vertex lies in at most `t` pairs' counts occurrences" | yes |

Point checks:

- **Quantifiers and strictness.**
  - Def 11: `1 ≤ |U|`, `|U| ≤ 2n/3`, `|F| ≤ s|U|`, and the conclusion `ε|U|/log²n ≤ |Nbr|` all
    match "≥".
  - Def 7: "at most `t`" and "length at most `ℓ`" are both `≤`.
  - Ball: "at most `i`" is `≤`.
  - The remark: `s < d(v)` and `s < δ(G)`, strict as in "`δ(G) > s`".
- **Log base and parsing.** The pretty-printed term is
  `((ε * ↑U.card) / ((Real.logb 2 ↑G.card) ^ 2))`: the square of `log₂ n`, with `n` the vertex
  count cast to ℝ. `EGTest.K2_isExpander` pins the base to 2: with `ln` the test would fail.
- **Multiplicity.** The count is over indices (occurrences). The conclusion gives one path per
  index, and the paths are pairwise edge-disjoint across indices. So "a pair occurring `k` times
  receives `k` pairwise edge-disjoint paths". The test "`K2` is not `(ℓ,2)`-path connected" shows
  the clause has force.
- **Real `t` (the round-1 M1 fix).** The hypothesis is now literally "`count ≤ t`" in ℝ, as the s4
  uses with `𝗍 = 2^{10}L^8` need.
  - `isPathConnected_natFloor_iff` (for `t ≥ 0`, `t` may be replaced by `⌊t⌋₊`) is correct.
  - `isPathConnected_of_lt_one` (the property is trivial for `t < 1`) agrees with the literal
    manuscript definition.
- **Universe of `ι`.** `ι : Type` is not a restriction. `exists_paths` reindexes any finite index
  type in any universe along `Fintype.equivFin`, so the definition is equivalent to the
  universe-polymorphic reading.
- **Edge cases.**
  - For `n ≤ 1`, Def 11 is vacuous (`isExpander_of_card_le_one`). This is the manuscript's own
    remark in s3:lemL15p ("If `N=1`, then no set `U` satisfies ... every graph on one vertex is an
    expander for all parameters").
  - For `s < 0` it is also vacuous. I proved this in scratch probe P1. It matches the literal
    text, since no `F` satisfies `|F| ≤ s|U| < 0`.
  - Loops are excluded by `loopless`.
  - The ends of "through" paths are unrestricted.
  - `B^0_H(U,W) = U ∩ W` (probe P4). `w ∈ B^1_H(U,W) ↔ w ∈ W ∧ (w ∈ U ∨ ∃ u ∈ U, uw ∈ E(H))`
    (probe P5). So the start vertex need not lie in `W`, and the end must.
- **Total extensions outside the manuscript's domain.** The formal `W` in Def 7 is arbitrary,
  while the manuscript has `V ⊆ V(G)`. Probe P3 proves
  `IsPathConnected G ℓ t W ↔ IsPathConnected G ℓ t (W ∩ V(G))`, so this does not change the
  meaning. `ball`, `nbrSet`, `induce` and `edgesBetween` are total in the same harmless way.
- **Lib statements against the manuscript.**
  - `IsExpander.of_le` and `IsExpander.mono` are exactly s3:lemMonotone (i).
  - `IsPathConnected.mono` is s3:lemMonotone (ii). It drops `V' ⊆ V(G)`, so it is more general.
  - `IsPathConnected.exists_paths_sigma` is the joint-routing sentence of (iii). The union
    multiplicity is the sum over `k` of the counts, and the paths are pairwise disjoint over all
    `(k,i) ≠ (k',j)`.
- **B–M remark after Def 11 (`IsExpander.lt_deg`, `lt_minDeg`).** Both prove `s < d_G(v)` and
  `s < δ(G)` from `2 ≤ |G|` together with the extra hypothesis `0 < ε`.
  - The extra hypothesis is necessary. `isExpander_of_nonpos` shows every graph is an
    `(ε,s)`-expander when `ε ≤ 0`, and the test `(pathGraph 5).IsExpander 0 100` has `δ = 1`.
  - So the manuscript sentence is literally false without `ε > 0`. This is not a weakening of the
    formal statement.
  - Every use has `ε' ∈ (0,1]` (s3 conventions) or `ε' ∈ [2^{-7},1]` (s3:thmT16s).
- **Bridge.** Not in scope. `EGCheck/Bridge.lean` imports only `EG.Proof.Main` and
  `EGCheck.BridgeLemmas`, and none of the graph modules.

## 2. Vacuity and triviality

- **`FGraph`.** The invariants are consistent: `P3`, `K2`, `K4` and `pathGraph n` are
  constructed.
- **`IsExpander`** is neither always true nor always false. True cases: `K4` is a
  `(1,0)`-expander and `K2` is a `(1,1/2)`-expander. False cases: `pathGraph 60` is not a
  `(1,0)`-expander (checked directly from Def 11), and `K2` is not a `(2,0)`- or
  `(1,1)`-expander. The only trivial regimes (`n ≤ 1`, `ε ≤ 0`, `s < 0`) are trivial in the
  manuscript too.
- **`IsPathConnected`** is neither always true nor always false.
  - True: complete graphs are `(1,1)`-path connected for every index type.
  - False: `P3` is not `(1,1)`-path connected. `K2` is not `(ℓ,t)`-path connected for any `ℓ` and
    any `t ≥ 2`. `K2` is not `(−1,1)`-path connected (probe P6, a negative length bound).
  - Trivial only for `t < 1`, which matches the literal definition. The manuscript uses `t ≥ 1`.
- **`ball`, `IsThrough`, `IsPathIn`** constrain what they should: the tests reject repeated
  vertices and non-edges, and show `2 ∉ B^1_{P3}(0,{1,2})` and `2 ∉ B^5_{P3}(0,{2})`.
- **Attempts to prove `False` or the definitions trivially.** None succeeded: I found no
  contradictory fields and no Prop that is always true.
- **Scratch probes (all compile, 0 errors).** Each probe confirms the intended meaning:

| Probe | Statement |
|---|---|
| P1 | `s < 0` makes Def 11 vacuous |
| P2 | `s < \|G\|` for an `(ε,s)`-expander with `ε > 0`, `\|G\| ≥ 2`; this is the "because `s < N`" of s3:thmT16s(b) |
| P3 | the `W ↔ W ∩ V(G)` equivalence for Def 7 |
| P4 | `B^0 = U ∩ W` |
| P5 | the characterization of `B^1` |
| P6 | `K2` is not `(−1,1)`-path connected |
| P7 | `2.5 < δ(K4)`, so the remark does not refute `K4` being a `(1, 2.5)`-expander |

## 3. Soundness hygiene

- `python3 scripts/lint.py`: 0 findings.
- `lake env lean --run scripts/Axioms.lean --prefix EG --no-sorry EG.Defs.Graph EG.Defs.Walk
  EG.Defs.Expander EG.Lib.Found.Graph`: 270 constants inspected, 0 use `sorryAx`, 0 violations.
  The oleans are newer than the sources.
- `scripts/check.sh EGTest/Found.lean 900` with `LEAN_NUM_THREADS=2`: rc=0, 0 errors, 0 sorry
  warnings.
- No `sorry` or `set_option` in the five files.
- Module headers follow AGENTS.md: `@[expose] public section` in `EG/Defs/**` and `public section`
  in `EG/Lib/**`.
- `ball` is `noncomputable` with a classical `DecidablePred`. This is fine, and `mem_ball` is the
  API.
- The docstrings of the manuscript-facing declarations start with the label and quote the text.

## 4. Usability

The design serves downstream work well.
- A path of `H − F` is `IsPathIn (H.deleteEdges F).edges p`, with no transport.
- The colour classes of s3:lemL15p are `restrictEdges`, and the `H−F` of Def 11 is literal.
- Balls take an `FGraph`, so `B^{ℓ_*}_{G−F}(U,V)` is `ball (G.deleteEdges F) ℓ_* U V`.
- Def 7 over indexed families is what s3:lemL9rho's proof does ("index the pairs by `i ∈ [r]`").
- Real `ℓ, t, ε, s` avoid floor bookkeeping in s3 and s4.
- The Mathlib bridge (`toSimpleGraph`, `IsPathBetween.exists_walk`, `isPathBetween_support`)
  is in place for the Ext layer.

Optional additions. None blocks anything, and each takes at most 15 lines; the proofs are in my
scratch file:
- `IsExpander.lt_card` (`s < |G|`), used in s3:thmT16s(b);
- `ball_zero` (`B^0 = U ∩ W`) and `mem_ball_one`;
- `isPathConnected_inter_verts` (`W ↔ W ∩ V(G)`), useful when a consumer's `V` is not visibly
  inside `V(G)`.

Later, not for this task: s3:lemL9rho needs the hypergraph `ℋ_i` of all `x_iy_i`-paths of length
`≤ h` through `V`. That is a `Finset` of such paths, or of their edge sets. The Link layer should
build it once, in `EG/Lib` next to `IsPathBetween`, rather than per proof.

## 5. Issues

| # | Severity | Item |
|---|---|---|
| C1 | cosmetic, manuscript side, still open | s1:citDef11 (s1.tex:503–506) still reads "hence `δ(G) > s` for every `(ε,s)`-expander `G` on at least two vertices". It needs "with `ε > 0`". The Lean side is correct (`lt_deg` assumes `0 < ε`, and `isExpander_of_nonpos` shows this is necessary). I found no record in STATE.md or in the v6 revision files (R1–R7) that this was forwarded. The orchestrator should add it to the v6 wording fixes. |
| C2 | cosmetic, usability | The optional API lemmas of §4: `IsExpander.lt_card`, `ball_zero`/`mem_ball_one`, `isPathConnected_inter_verts`. |
| C3 | cosmetic, plan tracking | PLAN §3 lists walks, trails, cycles and the s4 observations (S), (E), (C) under Found.Graph `Walk`. This task asked only for paths, and the design note records the deviation. The orchestrator should keep a follow-up task for them before the s4 work starts. |

## 6. Summary

The definitions are faithful to s1:convGraphs (a)–(e), s1:citDef7 (multiset clause, real `t`) and
s1:citDef11 (`log₂`, real `2n/3`, `|F| ≤ s|U|`, `≥ ε|U|/log²n`). This covers quantifiers,
strictness, log base, multiplicity and edge cases. The definitions are non-vacuous and the hygiene
checks are clean. The B–M remark is proved with the necessary extra hypothesis `ε > 0`, and the
matching manuscript wording fix (C1) is still pending.
