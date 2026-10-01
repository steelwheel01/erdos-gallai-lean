# Design note: Fact EG0, the long-cycle bound (s1:factEG0, new in v6), task [eg0]

Targets (Spec `EG/Spec/Found/EG0.lean`, proof `EG/Proof/Found/EG0.lean`):
* `EG.factEG0a : EG.Spec.FactEG0aStatement` — (a), decomposition with `≤ h(log h + 1)` objects,
  `≤ h − 1` single edges;
* `EG.factEG0aFnum : EG.Spec.FactEG0aFnumStatement` — (a) "In particular `f(H) ≤ h(log h + 1)`";
* `EG.factEG0b : EG.Spec.FactEG0bStatement` — (b), the relative form for an edge set with ends
  in `W`.

Manuscript: s1.tex l. 635-708 (statement l. 636-645, proof l. 657-708). Consumers: s4.tex
l. 371, 595, 790 (s4:thmVXp and the vortex runs, β = 48, 64, 13) and s5.tex l. 400.

## 1. Encoding decisions (Spec)

* **Graphs.** "graph `H` with `h` vertices" is `H : EG.FGraph V` (finite, simple, loopless),
  `h = H.card = H.verts.card`, hypothesis `1 ≤ H.card`. Universe-polymorphic `V : Type u`, any
  `DecidableEq V`.
* **log.** `log = log₂` (s1:convGraphs (b)): `Real.logb 2`.
* **Real-valued bounds (blueprint EG0-REAL).** The bounds `h(log h + 1)` and `βα` are compared in
  `ℝ` with `(D.length : ℝ)`; `N`, `α`, `β` are reals, as in the manuscript ("let α and β be real
  numbers"), and `|W| ≤ βα/L` is `(W.card : ℝ) ≤ β * α / Real.logb 2 N`.
* **Decompositions.** "a decomposition of `E(H)` (of `F`)" is `EG.IsDecomp ↑H.edges D`
  (`EG.IsDecomp ↑F D`): a list of well-formed objects (s1:defObject), edge-disjoint, covering
  exactly the edge set. `f(H)` is `EG.fnum H.edges` (`H.edges` is loopless, as CONVENTIONS
  requires for `fnum`).
* **Inlined single-edge match (blueprint EG0-ISEDGE / OBJ-ISEDGE).** "the number of single edges
  of `D`" is `D.countP (fun o => o matches .edge _)`. This is definitionally the same predicate as
  `EG.Obj.isEdge` of `EG/Lib/Found/Fnum.lean`, but it is written out in the Spec so that the Spec
  depends on `EG/Defs` only (no Lib import in a Spec, and no change to Defs needed). The proof
  converts with `List.countP_congr … by cases o <;> exact Iff.rfl`. The single-edge counts are
  kept in both (a) and (b) because s4:thmVXp uses them ("N + o(N) single edges").
* **T0-eg0-loop (CONVENTIONS.md, blueprint EG0-LOOP).** (b) is stated for an edge set
  `F : Finset (Sym2 V)` with `∀ e ∈ F, ¬ e.IsDiag`: the manuscript's "`F` is the edge set of a
  (simple) graph, so that `F` has no loops and no parallel edges" (a `Finset` cannot contain
  parallel edges, so only the loop condition is written). The hypothesis is necessary: `{s(0,0)}`
  on `Fin 1` has no `IsDecomp` at all (checked by the reviewer in Lean).
* **W.** "every edge of `F` has both ends in a set `W`" is `W : Finset V` with
  `∀ e ∈ F, ∀ v ∈ e, v ∈ W`; `W` is not tied to any graph's vertex set (as in the manuscript), so
  the s4 consumers instantiate (b) directly.
* `h − 1` is ℕ-subtraction `H.card - 1`; harmless since `h ≥ 1`.

## 2. Proof structure (`EG/Proof/Found/EG0.lean`, namespace `EG.EG0`)

1. `exists_prefix_last`, `cycleEdges_subset_of_chain`: list lemmas (a prefix ending at the last
   element with a property; closing a chain `v₀ … vᵢ` with `vᵢv₀` into a cycle of `G`).
2. `IsPth`, `exists_longest` (blueprint EG0-LONGESTPATH): paths as duplicate-free chains of
   vertices in `V(G)`; a longest one exists since lengths are bounded by `|V(G)|`.
3. `exists_long_cycle_of_deg`: in a graph of minimum degree `d ≥ 2` with a vertex, a longest
   path `v₀ … v_r`, closed at the neighbour of `v₀` of largest index, is a cycle of length
   `≥ d + 1` (manuscript: "the largest index `i` with `v₀vᵢ ∈ E(H*)` satisfies `i ≥ d`").
4. `exists_core` (the peeling): deleting vertices of degree `≤ d − 1` from `S` with
   `(|S| − 1)(d − 1) < e(H[S])` stops at a non-empty `T ⊆ S` with `δ(H[T]) ≥ d`. Proved by
   induction on `|S|` via `card_induce_edges_le_erase` (deleting `v` loses at most `d_{H[S]}(v)`
   edges). This is the manuscript's counting "m' ≤ (h − 1)(d − 1)" in contrapositive, one
   deletion at a time.
5. `exists_cycle_of_card_le` (the Claim): `h ≥ 1` vertices and `m' ≥ h` edges give a cycle of
   length `ℓ` with `m' < h ℓ` (strict; the manuscript's "length at least `m'/h`").
   `exists_cycle_of_edges`: the same for an edge set `E` (no loops, ends in `W`) via
   `FGraph.ofEdges W E`.
6. `one_sub_inv_pow_le_half`: `(1 − 1/h)^h ≤ 1/2` for `h ≥ 1`.
7. `block`: `j` rounds of "remove a long cycle given by the Claim": leaves `E' ⊆ E` and at most `j`
   cycles decomposing `E \ E'`, with `|E'| < h` (stopped) or `|E'| ≤ (1 − 1/h)^j |E|`.
8. `decomp_of_card_lt`: `|E| < 2^q h` ⇒ a decomposition into `≤ q h` cycles and `≤ h − 1`
   single edges (induction on `q`, one `block` of `h` rounds per halving).
9. `exists_decomp_log`: (a) for an edge set with ends in `W`, `h = |W| ≥ 1`: with
   `q = ⌊log₂ h⌋`, `|E| < 2^q h`, so `≤ q h + h − 1 ≤ h(log h + 1)` objects.
10. `factEG0a` (`W = V(H)`), `factEG0aFnum` (via `fnum_le_of_isDecomp`), `factEG0b` (the
    manuscript's reduction: `W = ∅` ⇒ `F = ∅`; otherwise `h ≤ βα/L ≤ βN/L ≤ N/4`, so
    `log h ≤ L − 2` and `h(log h + 1) ≤ h(L − 1) ≤ hL ≤ βα`).

## 3. Departures from the manuscript text (none changes a statement)

* **`d = max(2, ⌊m'/h⌋)` instead of `max(2, ⌈m'/h⌉)`** (in `exists_cycle_of_card_le`). The floor
  avoids a real/ceiling detour in ℕ. It gives the same strict conclusion: the peeling hypothesis
  `(h − 1)(d − 1) < m'` holds (if `⌊m'/h⌋ ≥ 2` then `(d − 1)h < ⌊m'/h⌋ h ≤ m'`; otherwise
  `d − 1 = 1` and `(h − 1) < h ≤ m'`), and the cycle length `ℓ ≥ d + 1 ≥ ⌊m'/h⌋ + 1` satisfies
  `m' < h ℓ`, i.e. `ℓ > m'/h`.
* **`(1 − 1/h)^h ≤ e⁻¹ ≤ 1/2` instead of the binomial argument** (`(1−x)^h(1+x)^h ≤ 1`,
  `(1+x)^h ≥ 2`). Mathlib's `Real.one_sub_div_pow_le_exp_neg` and `e ≥ 2`
  (`Real.add_one_le_exp`) give it directly, including `h = 1`.
* **`|E| < C(h+1, 2) ≤ 2^⌊log h⌋ h` instead of `m ≤ C(h, 2) ≤ h²/2`.** Since `E` has no loops and
  its ends are in `W`, `E ⊊ W.sym2` (a diagonal `s(v,v)`, `v ∈ W`, is missing), and
  `|W.sym2| = C(h+1, 2)` (`Finset.card_sym2`). This avoids the FGraph lemma
  `two_mul_card_edges_le` (which sits in `EG/Proof/Quot/HI.lean`, not in Lib). Then
  `C(h+1, 2) = (h+1)h/2 ≤ 2^q h` with `q = ⌊log₂ h⌋` since `h + 1 ≤ 2^{q+1}`.
* **Counting.** The manuscript writes `t − 1 = qh + r'` and derives `q + 1 ≤ log h`; the Lean
  proof instead fixes `q = ⌊log₂ h⌋` up front and shows (by induction on `q`, `decomp_of_card_lt`)
  that `|E| < 2^q h` edges are decomposed into `≤ qh` cycles plus `≤ h − 1` single edges. Same
  count `qh + h − 1 ≤ h log h + h`.
* **The Claim is used for edge sets** (`FGraph.ofEdges W E`) rather than for subgraphs `H_i` of
  `H`, so that the removal loop runs on `Finset (Sym2 V)` directly; in (b) it is applied with the
  vertex set `W`, as in the manuscript ("applied to the graph with vertex set `W` and edge set
  `F`").

## 4. Status

* No `sorry`; axioms of `EG.factEG0a`, `EG.factEG0aFnum`, `EG.factEG0b`:
  `[propext, Classical.choice, Quot.sound]`; `python3 scripts/lint.py`: 0 findings.
* Clean-room review round 1 (`eg0.review1.md`): APPROVE.

## Fix round 1

Review `formal/work/ext/eg0.review1.md`, two issues.

1. **(minor, process) Missing author notes `formal/work/ext/eg0.md`.** Valid: the file did not
   exist. Fixed: this file, recording the encoding decisions (T0-eg0-loop, the inlined
   single-edge match, the real-valued bounds; §1) and the proof's departures from the manuscript
   (`d = max(2, ⌊m'/h⌋)`, `(1 − 1/h)^h ≤ e⁻¹`, `|E| < C(h+1, 2)`; §3). No Lean change.
2. **(cosmetic, integrator) `EG.Spec.Found.EG0` not in LOCK.json; blueprint row s1:factEG0 still
   "risk (EG0-UNREVIEWED)".** Valid, but assigned to the integrator by the review ("The
   integrator should lock the Spec and update the blueprint status after this review round").
   Not changed here: LOCK.json and the blueprint are integrator-owned. Recommended integrator
   action: add `EG/Spec/Found/EG0.lean` to LOCK.json and set the blueprint row s1:factEG0 to
   done / reviewed (EG0-UNREVIEWED resolved by review round 1).

Lean files unchanged in this round (`EG/Spec/Found/EG0.lean`, `EG/Proof/Found/EG0.lean`).
Build check: a first `lake build EG.Proof.Found.EG0` in this round failed upstream in
`EG/Defs/Graph.lean` (a concurrent, uncommitted edit by another task, P2-D, since fixed there by
`noncomputable`), not in the EG0 files. Re-run after that fix: `lake build EG.Proof.Found.EG0`
succeeds (2039 jobs); `python3 scripts/lint.py`: 0 findings.
