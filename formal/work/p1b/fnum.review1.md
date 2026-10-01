# Clean-room review, round 1: task [fnum] (f and Fact s1:factAdd)

Reviewer: clean-room agent. I edited no Lean file. Files reviewed: `EG/Defs/Fnum.lean`,
`EG/Lib/Found/Fnum.lean`, `EGTest/Fnum.lean`, the design note `work/p1b/fnum.md`, and
`EG/Defs/Objects.lean` (the dependency). Manuscript: `proofs/manuscript/s1.tex` l. 354–391
(s1:defObject, s1:factAdd with its proof), s1:convGraphs(a), and the uses in s6:lemHCCglob,
s7:thmHI and s5 ("f(E) ≤ 80N"). v6work only changes `\deps` lines of the users of factAdd, not
the statements.

**Verdict: approve.** Every definition and statement is faithful, and several are stronger than
the manuscript. Hygiene is clean, and the non-vacuity checks pass, including a new f(K₄) = 3
proof. All issues below are minor or cosmetic usability suggestions. None blocks.

## 1. Fidelity (back-translation)

### Definitions
| Lean | Plain mathematics | Manuscript | Match |
|---|---|---|---|
| `Obj`, `Obj.WF`, `cycleEdges` (Objects.lean) | An object is `edge e` with e not a loop, or `cycle c` with c a list of ≥ 3 distinct vertices. The edges of `cycle c` are c₀c₁, …, c_{k−1}c₀. | "An object is a cycle (of length at least 3) or a single edge." | yes |
| `IsDecomp E D` | Every object of D is well formed. The concatenated edge lists have no duplicates, which gives pairwise edge-disjoint objects and no repeated edge within a cycle. The set of edges of D is exactly E. | "a partition of F into the edge sets of objects" | yes. Each WF object has ≥ 1 edge, so there are no empty blocks and no object is repeated. |
| `fnum F := sInf {k \| ∃ D, IsDecomp (↑F \ diagSet) D ∧ D.length = k}` | f(F) = the least number of objects in a decomposition of the non-loop part of F. | "f(F) is the least number of objects in a decomposition of F (so f(∅)=0)" | Identical for loopless F. Since s1:convGraphs(a) makes graphs simple, the manuscript takes f only of loopless sets. The set is never empty (single edges, `exists_isDecomp_sdiff_diagSet`), so `sInf` is a genuine minimum (`fnum_spec`). |
| `fnum H.edgeFinset` | f(H) := f(E(H)) | "f(H) := f(E(H))" | yes. `exists_isDecomp_edgeSet_length_eq_fnum` and `fnum_edgeFinset_le_iff` connect it to `IsDecomp G.edgeSet`, which is the form of `EG.Spec.MainInternal`. |
| `fmax n := univ.sup (fun H : SimpleGraph (Fin n) => fnum H.edgeFinset)` (classical instances) | f(n) = the maximum of f over the graphs on Fin n | "f(n) := max{f(H) : \|V(H)\| = n}" | yes. `fnum_le_fmax` covers every graph on any `Fintype V` with `card V = n` and any instances. `exists_fnum_eq_fmax` shows the maximum is attained. The value does not depend on instances, because a Finset is extensional. n = 0 gives 0, matching the graph with no vertices. |

**Loop convention.** Loops are ignored, so `fnum F = f(F \ diagSet)`. For loopless F this is
literally the manuscript's f. For looped F the manuscript's minimum would be over ∅. This is the
safest of the three options the author considered. A junk value of 0 would make `fnum F ≤ k`
vacuous for looped F. With this convention, `fnum F ≤ k` still says the non-loop part decomposes
into ≤ k objects. The convention is documented in the Defs docstring, together with the caveat
for statement authors. `FGraph` (EG/Defs/Graph.lean) carries a `loopless` field, and
`SimpleGraph.edgeFinset` is loopless (`loopless_edgeFinset`), so every manuscript use is
covered.

### Statements (s1:factAdd)
- **(a)** `fnum_le_card : fnum F ≤ F.card` holds for all F. The manuscript says "for every edge
  set F", so this is the same statement, or stronger because it has no looplessness condition.
- **(b)** `fnum_union_le [DecidableEq V] (hd : Disjoint F₁ F₂) : fnum (F₁ ∪ F₂) ≤ fnum F₁ + fnum F₂`.
  The manuscript has the same hypothesis ("disjoint edge sets") and the same conclusion.
  `fnum_biUnion_le` is the q-fold version used in s6:lemHCCglob.
- **(c)** `fnum_union_eq_of_vertexDisjoint (hvd : ∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ v ∈ e₁, v ∉ e₂)` gives
  equality. The manuscript says "H is the vertex-disjoint union of H₁, H₂". The Lean hypothesis
  only asks that no vertex is incident to edges of both sets, so isolated vertices may be shared.
  That is a weaker hypothesis and hence a stronger statement. The graph form
  `fnum_edgeFinset_sup_of_disjoint_support` uses `Disjoint H₁.support H₂.support`, also the
  weakest faithful hypothesis.
- **(d)** In the Lean model, "f depends only on E(H)" holds by definition. The vertex-type changes
  are covered by `fnum_map` (relabelling along any embedding, which covers adding isolated
  vertices) and `fnum_edgeFinset_induce_of_support_subset` (deleting isolated vertices: the form
  of s7:thmHI step (1)). "f(n) non-decreasing" is `fmax_mono : Monotone fmax`.
- **Optimal decompositions**: `fnum_spec`, `exists_isDecomp_length_eq_fnum` (loopless F),
  `fnum_le_iff` / `le_fnum_iff` (loopless F: the exact characterisation of the minimum),
  `fnum_le_of_isDecomp` (no hypothesis needed, because a decomposable F is loopless).
- **Required IsDecomp lemmas**: `IsDecomp.append` (disjoint sets), `isDecomp_singletons`,
  `IsDecomp.map` and `isDecomp_map_iff` (injective relabelling) are all present and correct.

None of these statements has extra hypotheses. The `[DecidableEq V]` in (b) and (c) is only
needed to form `∪`.

**Bridge.** Not applicable to this task. Neither `EGCheck/Bridge.lean` nor `EG.Spec.MainInternal`
uses `fnum`/`fmax`. The link to the spec's `IsDecomp G.edgeSet D ∧ D.length ≤ …` form is
`fnum_edgeFinset_le_iff`, which is proved.

**Objects.lean.** I checked it independently and agree with the author: it is faithful and needs
no change.

## 2. Vacuity / triviality

I wrote scratch files outside the repo, in the session scratchpad under /tmp, importing
`EG.Lib.Found.Fnum`. They compile with no errors and no sorry.
- **f(K₄) = 3**, proved from the definition's API as a new test. The upper bound uses the
  4-cycle 0123 plus the two diagonals. The lower bound goes as follows. Every object on `Fin 4`
  has 1, 3 or 4 edges. A decomposition with ≤ 2 objects must therefore be two triangles, and two
  triangles in K₄ always share an edge (`decide` over `Fin 4`). This exercises the case where
  cycles are usable but cannot be used optimally, so the value lies strictly between the trivial
  bounds. It is the lower-bound check that the author's tests lack; see suggestion S5.
- f(C₄) = 1 (a cycle of length 4); f(path with 2 edges) = 2; `2 ≤ fmax 3` (P₃ on Fin 3).
- The following are all rejected by `IsDecomp`: the degenerate "cycles" `[0,1]` (too short) and
  `[0,1,0]` (repeated vertex), and a repeated edge `[edge s(0,1), edge s(1,0)]`.
- Nothing trivialises: `fnum_singleton` (= 1) and `fnum_star` (= k) rule out f ≡ 0, and
  `fnum_K3` (= 1) rules out f = |F|.

## 3. Soundness hygiene
- `python3 scripts/lint.py`: 0 findings.
- `lake build EG.Lib.Found.Fnum`: success (up to date).
- `scripts/check.sh EG/Lib/Found/Fnum.lean` and `scripts/check.sh EGTest/Fnum.lean`: 0 errors,
  0 sorry warnings, and no other warnings.
- `lake env lean --run scripts/Axioms.lean --no-sorry --prefix EG EG.Defs.Fnum EG.Lib.Found.Fnum`:
  193 constants inspected, 0 sorryAx, 0 violations. Only propext, Classical.choice and
  Quot.sound are used.
- The module headers are correct. Defs uses `@[expose] public section`. Lib uses
  `public section`, and its only `def`, `Obj.map`, is marked `@[expose]`. EGTest is a non-module
  file.
- Name collisions: there are none in namespace `EG`. `EGCheck.Bridge.length_cycleEdges`,
  `EGCheck.Bridge.cycleEdges_map` and `EGCheck.Bridge.objMap` duplicate lemmas here, but they
  live in a different namespace, so they do not clash (see S3).

## 4. Usability / suggestions (none blocking)
- **S1 (minor): FGraph-facing lemmas.** Downstream statements will write `fnum H.edges` for
  `H : FGraph V`. Add these in a file importing both `EG.Lib.Found.Graph` and
  `EG.Lib.Found.Fnum`:
  - `fnum_le_iff` / `exists_isDecomp_length_eq_fnum` specialised to `H.edges`, using `H.loopless`;
  - `fnum H.edges ≤ fmax H.card`, needed if anyone states results via f(n);
  - (c) for a vertex-disjoint union of FGraphs;
  - "deleting an isolated vertex keeps `edges`", the FGraph form of s7:thmHI step (1).
- **S2 (minor): list-level iterated union.** s6:lemHCCglob says "E₁ ∪ … ∪ E_q decomposes into
  Σ aᵢ objects", which is a decomposition, not an f-bound. A lemma
  `IsDecomp.flatMap`/`isDecomp_biUnion` would transport this without going through `fnum`:
  given pairwise disjoint `E i` with `IsDecomp (E i) (D i)`, it gives
  `IsDecomp (⋃ E i) (flatMap D)` with length Σ (D i).length. `IsDecomp.append` is the binary
  case.
- **S3 (cosmetic): duplicate helpers.** `EGCheck/BridgeLemmas.lean` defines `objMap`,
  `length_cycleEdges`, `cycleEdges_map` and `wf_objMap`, and `EG/Proof/Chain/Gate.lean` defines
  small list helpers. These duplicate `EG.Obj.map`, `EG.length_cycleEdges`,
  `EG.cycleEdges_map` and `EG.Obj.wf_map_iff`. The integrator can dedupe them later.
- **S4 (minor): state the loop caveat in AGENTS.md "Conventions".** For a raw
  `F : Finset (Sym2 V)` that is not known to be loopless, `fnum F ≤ k` does not assert that F
  itself decomposes. Statement authors should use `FGraph.edges` / `edgeFinset` or add
  `∀ e ∈ F, ¬ e.IsDiag`. The Defs docstring already says this, but statement authors may not
  read it.
- **S5 (optional): add the f(K₄) = 3 test.** It is the only test above that pins a value strictly
  between the trivial bounds. The proof is about 60 lines and uses only `decide` on `Fin 4`. It is
  in the reviewer's scratch file and I can hand it over if wanted.
- **S6 (cosmetic): Finset form of `IsDecomp.map`.** A version
  `IsDecomp ↑(F.map φ.sym2Map) (D.map (Obj.map φ))` would save the `coe_map_sdiff_diagSet`
  transport for loopless F.
