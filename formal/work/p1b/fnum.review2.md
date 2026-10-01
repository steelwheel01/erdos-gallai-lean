# Clean-room review, round 2: task [fnum] (f and Fact s1:factAdd)

Reviewer: clean-room agent, round 2. I edited no Lean file.

Files reviewed:
- `EG/Defs/Fnum.lean` (unchanged since round 1)
- `EG/Lib/Found/Fnum.lean`
- `EG/Lib/Found/FGraphFnum.lean` (new in fix round 1)
- `EGTest/Fnum.lean`
- the design note `work/p1b/fnum.md` and review 1 (`work/p1b/fnum.review1.md`)
- the dependencies `EG/Defs/Objects.lean` and `EG/Defs/Graph.lean` (`FGraph`)

Manuscript passages checked:
- `proofs/manuscript/s1.tex` l. 321–391 (s1:convGraphs(a), s1:defObject, s1:factAdd and its proof)
- s6:lemHCCglob (s6.tex l. 221–232)
- s7:thmHI (s7.tex l. 1355–1395)
- the uses of f in s4 (l. 588), s5 (l. 332) and s7 (Q_l)
- v6work: R1 adds Fact EG0 after factAdd, and R7 changes only `\deps` lines. s1:defObject and s1:factAdd are
  unchanged in v6.

**Verdict: approve.** Every definition and statement is faithful to the manuscript. Some are stronger, with no
hidden hypotheses. All three fix-round-1 additions are correct:
- the FGraph lemmas;
- the iterated-union lemmas;
- the f(K₄) = 3 test.

Hygiene is clean. The scratch checks outside the repo confirm the definitions are not vacuous. They include a new
proof that `EG.Spec.MainInternal ↔ ∃ c, ∀ n, fmax n ≤ c * n`, which shows that `fmax` matches the internal spec
exactly. I have only cosmetic or minor usability notes, and none of them blocks.

## 1. Fidelity (back-translation)

### Definitions

| Lean | Plain mathematics | Manuscript | Match |
|---|---|---|---|
| `fnum F := sInf {k \| ∃ D, IsDecomp (↑F \ diagSet) D ∧ D.length = k}` | f(F) is the least number of objects in a partition of the non-loop edges of F into edge sets of objects (cycles of length ≥ 3 given as duplicate-free vertex lists, or single non-loop edges). | [s1:defObject] "f(F) is the least number of objects in a decomposition of F (so f(∅)=0)" | Yes, for loopless F, which is every F the manuscript uses. By s1:convGraphs(a) graphs are simple. The set being minimised over is never empty, so `sInf` is a real minimum (`fnum_spec`). |
| `fnum H.edges` (`H : FGraph V`) and `fnum G.edgeFinset` (`SimpleGraph`) | f(H) = f(E(H)) | "f(H) := f(E(H))" | Yes. `FGraph.loopless` and `loopless_edgeFinset` mean the loop convention never applies here. |
| `fmax n := univ.sup (fun H : SimpleGraph (Fin n) => fnum H.edgeFinset)` | f(n) is the maximum of f(H) over the graphs H on n labelled vertices | "f(n) := max{f(H) : \|V(H)\| = n}" | Yes. The upper bound is `fnum_le_fmax` (any `Fintype V` with card n) and `FGraph.fnum_edges_le_fmax` (`fmax H.card`). The maximum is attained (`exists_fnum_eq_fmax`). fmax 0 = fmax 1 = 0 (checked in scratch). |

**Objects and IsDecomp** (`EG/Defs/Objects.lean`, dependency). These say:
- an object is either an edge e with e not a loop, or a cycle c with c duplicate-free and |c| ≥ 3, whose edges are
  c₀c₁, …, c_{k−1}c₀;
- `IsDecomp E D` means the objects are well formed, the concatenated edge list has no duplicates, and its members
  are exactly E.

That is a partition of E into the edge sets of objects. A well-formed object has at least one edge, so no block is
empty and D.length counts the blocks. Every partition into objects can be written this way. I agree with the
author and with round 1: the file is faithful.

**Loop convention.** `fnum F` ignores loops, so `fnum F = f(F \ diagSet)`. This is Mathlib's `fromEdgeSet`
convention. For loopless F it is the manuscript's f word for word (`fnum_le_iff`, `le_fnum_iff`,
`exists_isDecomp_length_eq_fnum`). For F with a loop, the manuscript's f is undefined, since the minimum would be
over ∅. The convention is documented in the Defs docstring together with the caveat for statement authors. I
checked the caveat in scratch: `fnum {s(0,0)} ≤ 0` holds, yet `{s(0,0)}` has no decomposition. A statement written
as `fnum F ≤ k` for a raw F that may contain loops is therefore weaker than the manuscript's. The FGraph API
removes this risk for the normal usage `fnum H.edges`. See U1.

### Statements (s1:factAdd)

- **(a)** "f(F) ≤ |F| for every edge set F". Lean: `fnum_le_card F : fnum F ≤ F.card`, for all F with no side
  condition. FGraph form: `FGraph.fnum_edges_le_card_edges`. Faithful.
- **(b)** "If F₁, F₂ are disjoint edge sets, then f(F₁ ∪ F₂) ≤ f(F₁) + f(F₂)". Lean:
  `fnum_union_le [DecidableEq V] (hd : Disjoint F₁ F₂)`, same hypothesis and same conclusion. Other forms:
  - iterated: `fnum_biUnion_le` (pairwise disjoint finset-indexed family);
  - FGraph: `FGraph.fnum_edges_le_deleteEdges_add` (F ⊆ E(H) ⇒ f(H) ≤ f(H − F) + f(F));
  - list/decomposition: `IsDecomp.append`, `isDecomp_flatMap`, `isDecomp_biUnion`, `isDecomp_finset_biUnion`.
- **s6:lemHCCglob, first sentence** (`exists_isDecomp_biUnion`). The manuscript says "Let E₁,…,E_q ⊆ E(G) be
  pairwise disjoint, and suppose each E_i decomposes into a_i objects. Then E₁ ∪ … ∪ E_q decomposes into Σ a_i
  objects." The Lean statement: `(s : Set ι).PairwiseDisjoint Es` and, for each i ∈ s, `IsDecomp (Es i) (Ds i)`,
  give `∃ D, IsDecomp (⋃ i ∈ s, Es i) D ∧ D.length = Σ_{i∈s} (Ds i).length`. It drops the hypothesis E_i ⊆ E(G), so
  it is stronger. The equality "into Σ a_i objects" is kept exactly. Faithful.
- **(c)** "If H is the vertex-disjoint union of graphs H₁ and H₂, then f(H) = f(H₁) + f(H₂)". Lean has three forms:
  - Edge-set form `fnum_union_eq_of_vertexDisjoint (hvd : ∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ v ∈ e₁, v ∉ e₂)`. It only asks
    that no vertex lies on an edge of both sets, which is a weaker hypothesis and hence a stronger statement.
  - SimpleGraph form `fnum_edgeFinset_sup_of_disjoint_support`.
  - FGraph forms `FGraph.fnum_union_edges_of_disjoint_verts` and `FGraph.fnum_edges_eq_add_of_disjoint_verts`
    (`E(H) = E(H₁) ∪ E(H₂)` and `Disjoint V(H₁) V(H₂)`), which are literally "vertex-disjoint union". There is also
    the split form `fnum_edges_eq_induce_add_deleteVerts`.

  All are faithful. The proof uses connectivity of objects (`Obj.edges_mem_of_vertexDisjoint`, via propagation
  around the cycle), as in the manuscript proof.
- **(d)** "Adding or deleting isolated vertices does not change f. In particular f(n) is non-decreasing in n."
  In the model, f is a function of the edge set by construction. The Lean statements are:
  - `fnum_map` (any embedding `V ↪ W`);
  - `fnum_edgeFinset_induce_of_support_subset`;
  - FGraph: `fnum_edges_deleteVerts_of_forall_not_mem` and
    `fnum_edges_deleteVerts_singleton_of_deg_eq_zero`, which is literally s7:thmHI step (1): "If v were isolated,
    then f(G−v) = f(G)". It comes with `card_deleteVerts_singleton` (|G − v| = |G| − 1).

  Monotonicity is `fmax_mono : Monotone fmax`. Faithful.
- **Optimal decomposition**: `fnum_spec`, `exists_isDecomp_length_eq_fnum`, `FGraph.exists_isDecomp_edges`, and
  the exact characterisations `fnum_le_iff`, `le_fnum_iff`, `FGraph.fnum_edges_le_iff`,
  `FGraph.le_fnum_edges_iff`. The link to the spec is `fnum_edgeFinset_le_iff`
  (`fnum G.edgeFinset ≤ k ↔ ∃ D, IsDecomp G.edgeSet D ∧ D.length ≤ k`). All correct.
- **IsDecomp API asked for by the task**: append (`IsDecomp.append`), singletons (`isDecomp_singletons`) and map
  along an injective function (`IsDecomp.map`, `isDecomp_map_iff`, finset forms) are all present.

No statement has an extra hypothesis. `[DecidableEq V]` appears only where `∪` or `biUnion` needs it.

**Bridge.** Not applicable. Neither `EGCheck/Bridge.lean` nor any `EG/Spec` file uses `fnum` or `fmax`. The grep
over `EG`, `EGCheck`, `EGTest` and `staging` finds no use outside the four files of this task.

## 2. Vacuity / triviality

Scratch files are in the session scratchpad under /tmp, outside the repo. They import `EG.Lib.Found.Fnum`,
`EG.Lib.Found.FGraphFnum` and `EG.Spec.Main`. All compile with 0 errors and no `sorry`.
- **f(K₅) = 2.** The upper bound uses the two edge-disjoint Hamiltonian cycles 01234 and 02413. The lower bound:
  a single object on Fin 5 has at most 5 < 10 edges. This covers cycles longer than 4 and a decomposition made
  only of cycles, which the tests do not cover.
- **f is not monotone**: f(P₃) = 2 > 1 = f(K₃), with P₃ ⊆ K₃. This is the expected mathematical behaviour. It
  shows f is not accidentally |F| or a monotone surrogate.
- **Edge cases**:
  - empty vertex type ⇒ `fnum F = 0`;
  - `fmax 0 = 0`, `fmax 1 = 0`, `2 ≤ fmax 3`;
  - loop plus (c): `fnum ({s(0,0)} ∪ {s(1,2)}) = 0 + 1`;
  - a loop set has `fnum ≤ 0` but no decomposition, which confirms the documented caveat.
- **Spec equivalence**: `EG.Spec.MainInternal ↔ ∃ c : ℕ, ∀ n, fmax n ≤ c * n`, proved in 15 lines from
  `exists_fnum_eq_fmax`, `fnum_le_fmax` and `fnum_edgeFinset_le_iff`. It says `fnum`/`fmax` are neither too
  strong nor too weak relative to the frozen internal spec: "f(n) = O(n)" in the manuscript's sense is exactly
  `MainInternal`.
- The existing tests pin non-trivial values on both sides:
  - f(star_k) = k for all k, which rules out a bounded f;
  - f(K₃) = 1, which rules out f = |F|;
  - f(K₄) = 3, strictly between the trivial bounds.

  The definitions are plain `def`s with no hypotheses to contradict, so nothing can be made vacuous.

## 3. Soundness hygiene

- `python3 scripts/lint.py`: 0 findings.
- `lake build EG.Lib.Found.FGraphFnum` (builds `EG.Defs.Fnum` and `EG.Lib.Found.Fnum` too): success.
- `scripts/check.sh` on `EG/Defs/Fnum.lean`, `EG/Lib/Found/Fnum.lean`, `EG/Lib/Found/FGraphFnum.lean` and
  `EGTest/Fnum.lean`: rc 0, 0 errors, 0 sorry warnings, and no other messages.
- `lake env lean --run scripts/Axioms.lean --no-sorry --prefix EG EG.Defs.Fnum EG.Lib.Found.Fnum
  EG.Lib.Found.FGraphFnum`: 501 constants inspected, 0 use `sorryAx`, 0 violations. Only propext,
  Classical.choice and Quot.sound are used.
- No `set_option`, `native_decide` or `decide +…` in any of the files. `EGTest/Fnum.lean` uses plain `decide` only
  on small `Fin`/ℕ goals.
- Module headers:
  - Defs: `@[expose] public section`.
  - Lib files: `public section`. The only Lib `def`, `Obj.map`, is `@[expose]`. `FGraphFnum` has no defs.
  - EGTest: non-module.
- `EG/Defs/Fnum.lean` is unchanged since it was committed (`git diff` is empty). Fix round 1 only added lemmas, as
  the note says.
- Name collisions: I re-ran a base-name grep of every declaration in the two Lib files over `EG`, `EGCheck`,
  `EGTest` and `staging`. The only hits are in other namespaces, so none is a real clash:
  - `EG.FinDist.map` and `EG.FinDist.map_map`;
  - `EG.IsPathIn.nodup`;
  - `EGCheck.Bridge.length_cycleEdges` and `EGCheck.Bridge.cycleEdges_map`, duplicates noted in round 1, to be
    deduped by the integrator.

## 4. Usability (none blocking)

- **U1 (minor, still open with the integrator, carried over from round 1 S4).** The loop caveat line for
  AGENTS.md "Conventions" was proposed in `fnum.md` but is not in AGENTS.md yet. The author correctly left
  AGENTS.md alone. Once statement freeze approaches, it matters for anyone writing `fnum F` for a raw
  `F : Finset (Sym2 V)`. v6 Fact EG0(b) ("If every edge of an edge set F has both ends in W … F has a
  decomposition …") is exactly such a raw-F statement. It must be stated with `IsDecomp` plus a looplessness
  hypothesis, or with F coming from an `FGraph`.
- **U2 (cosmetic).** Add the spec equivalence `mainInternal_iff_fmax : EG.Spec.MainInternal ↔ ∃ c, ∀ n,
  fmax n ≤ c * n` (scratch proof, 15 lines) to a Lib or Proof file that may import `EG.Spec.Main`. It is the
  formal form of s7:thmMainProof's last step ("In particular f(n) ≤ c n for every n, so f(n) = O(n)"). It also
  serves as a permanent fidelity check of `fmax`. An FGraph variant (`∀ H : FGraph V, fnum H.edges ≤ c * H.card`
  ⇒ `MainInternal`, via `ofSimpleGraph`) would be what the s7:thmHI endgame actually needs.
- **U3 (cosmetic, out of this task's scope; for the integrator / Objects owner).** v6 Fact EG0(a),(b) and the
  vortex finishes count single-edge objects: "at most h − 1 of which are single edges". There is no
  `Obj.IsEdge` / `Obj.isEdge : Obj V → Bool` yet, and no `countP` lemmas for append/flatMap/map. Adding them
  once, next to `IsDecomp.append`, would avoid ad-hoc encodings in s1/s4.
- **U4 (cosmetic).** `exists_isDecomp_biUnion` carries the tag `[s6:lemHCCglob]` although it lives in the s1
  foundation layer. That is fine, since no script parses the tags. When s6 is formalized, the s6 file should cite
  this lemma rather than re-prove it.
