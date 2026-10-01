# P1b pilot: Lemma GATE (s6:lemGATE): design note

Task [gate]. Status: proved with 0 sorry. All five files compile with 0 errors and 0 warnings, and
the lint is clean. After fix round 2 (section at the end), the axiom scan (`lake env lean --run
scripts/Axioms.lean --prefix EG EG.Proof.Chain.Gate EG.Lib.Found.Orient EG.Spec.Chain.Gate
EG.Defs.Orient`) inspects 286 constants and finds 0 violations and 0 uses of `sorryAx`
(239 after fix round 1).

## Files and modules
| File | Module | Contents |
|---|---|---|
| `EG/Defs/Orient.lean` | `EG.Defs.Orient` | `walkArcs`, `IsDirPathIn` (added in fix round 1), `cycleArcs`, `IsOrientation`, `outDeg`, `inDeg`, `IsBalanced`, `IsDirCycle`, `IsAcyclic` (+ `Decidable` instances for `IsDirCycle`, `IsDirPathIn`) |
| `EG/Spec/Chain/Gate.lean` | `EG.Spec.Chain.Gate` | `EG.Spec.GateStatement` (the first conclusion), `EG.Spec.GatePreciseStatement` (the "More precisely" sentence) |
| `EG/Lib/Found/Orient.lean` (new, not named in the task) | `EG.Lib.Found.Orient` | orientation API, the directed-cycle decomposition of balanced digraphs, and (fix round 2) helpers for MED and HCC-P (below) |
| `EG/Proof/Chain/Gate.lean` | `EG.Proof.Chain.Gate` | `EG.gate : GateStatement`, `EG.gate_precise : GatePreciseStatement`, `EG.gate_with_cycles` (both conclusions at once) |
| `EGTest/Gate.lean` | `EGTest.Gate` | the cyclic triangle with `𝒲` = one arc; the bowtie with `𝒲` = two arcs; directed paths, sources, potentials; negative tests |

The orchestrator should add these root imports: `EG.Defs.Orient`, `EG.Spec.Chain.Gate`,
`EG.Lib.Found.Orient` and `EG.Proof.Chain.Gate` to `EG`, and `EGTest.Gate` to `EGTest`.

## Definitions (EG.Defs.Orient)
Manuscript source: the preamble of s6 ("Orientations, directed paths and directed cycles are those
of digraphs obtained by orienting edges of `G`; each edge receives exactly one direction. A digraph
is *acyclic* if it has no directed cycle.") and the statement of s6:lemGATE.

1. **Arcs** are pairs `(u, v) : V × V`, read `u → v`. A digraph obtained by orienting edges is its
   arc set `A : Finset (V × V)`. Its vertex set plays no role. `F⃗ - 𝒲` is `A \ W`.
2. **`IsOrientation F A`** is a structure with three fields:
   - `loopless`: no arc is a loop;
   - `mem`: `s(a.1, a.2) ∈ F` for every arc `a`;
   - `existsUnique`: every `e ∈ F` has exactly one arc `a ∈ A` with `s(a.1, a.2) = e`.

   The task asked for the `loopless` field. In GATE it is redundant, because `F ⊆ E(G)` and an
   `FGraph` has no loops, but it keeps the definition self-contained for later users (clusters,
   MED). A consequence (`IsOrientation.not_mem_swap`) is that an orientation never contains both
   `u → v` and `v → u`. This is the formal content of the manuscript's "the two arcs come from two
   distinct edges of `F` with the same ends, impossible since `G` is simple".
3. **`outDeg A v`, `inDeg A v`** are the cardinalities of `A.filter (·.1 = v)` and
   `A.filter (·.2 = v)`. **`IsBalanced A`** is `∀ v, outDeg A v = inDeg A v`: "at every vertex",
   over all of `V`, which is equivalent because vertices off the arcs have both degrees `0`.
4. **`cycleArcs c`** is `List.zip c (c.rotate 1)`, the arcs `c₀ → c₁ → … → c_{k-1} → c₀`. It is the
   directed counterpart of `EG.cycleEdges`, and `cycleEdges_eq_map_cycleArcs` states that the
   underlying edges are exactly `cycleEdges c`.
5. **`IsDirCycle A c`** is `c ≠ [] ∧ c.Nodup ∧ ∀ a ∈ cycleArcs c, a ∈ A`: a directed cycle with
   distinct vertices, of any length `k ≥ 1` (`k = 1` is a loop). **`IsAcyclic A`** is
   `∀ c, ¬ IsDirCycle A c`, the literal "no directed cycle".
   - As a hypothesis this is the weakest reading. "No closed directed walk" implies it, and the
     two are equivalent for finite digraphs, but the equivalence is not needed.
   - Counting `k = 1` (loops) as cycles changes nothing on the loopless arc sets of
     orientations, such as `A \ W` in GATE.
   - `k = 2` (`u → v → u`) is a directed cycle in every convention.
6. **Potentials.** Both directions are proved in Lib. GATE needs neither.
   - `isAcyclic_of_potential`: a potential `V → β` (`β` any linear order) that increases strictly
     along every arc forces acyclicity. MED (a) uses this direction ("`pot` strictly increases
     along every arc, and `MED(≺)` has no directed cycle"), and so does the end of HCC-P Step 3
     ("every arc outside `𝒲` increases `Ψ`, so `F⃗ − 𝒲` is acyclic").
   - The converse is used by HCC-P Step 3 ("One exists because the orientation is acyclic: take
     the position in a topological order"; the numbering `tp_j` of the acyclic `D'_j[T_j]`) and
     by s6 line 502 ("an acyclic orientation with an arc has a source"). Added in fix round 1:
     `IsAcyclic.exists_source`, `IsAcyclic.exists_potential` (a numbering injective on a finite
     `S ⊇` ends of arcs, with values in `1..|S|`, increasing along arcs) and
     `isAcyclic_iff_exists_potential`. (The first version of this note wrongly said that MED (a)
     and HCC-P only use the first direction.)
7. **Directed paths** (added in fix round 1). `walkArcs p := List.zip p p.tail` (the arcs
   `v₀ → v₁ → … → v_k`) and `IsDirPathIn A p := p ≠ [] ∧ p.Nodup ∧ ∀ a ∈ walkArcs p, a ∈ A`. They
   mirror `EG.walkEdges` / `EG.IsPathIn` of `EG.Defs.Walk`. Lib proves
   `walkEdges_eq_map_walkArcs` and `isDirPathIn_iff_isChain`. Source: the s6 preamble ("directed
   paths ... are those of digraphs obtained by orienting edges of `G`") and the GATE proof ("a
   directed path in `F⃗` with pairwise distinct vertices").
8. **Parallel arcs.** An arc set cannot hold two parallel arcs `u → v`. This is faithful to "each
   edge receives exactly one direction", because distinct edges of a simple graph have distinct
   ends. A union of oriented edge sets is again an arc set only when the edge sets are disjoint
   (`IsOrientation.union` takes that hypothesis). The Defs docstring now says so.

## Statements (EG.Spec.Chain.Gate)
Both statements are universe polymorphic (`V : Type u`) and take `[DecidableEq V]`,
`G : EG.FGraph V`, `F : Finset (Sym2 V)` and `A W : Finset (V × V)`. The hypotheses are
`F ⊆ G.edges`, `IsOrientation F A`, `IsBalanced A`, `W ⊆ A` and `IsAcyclic (A \ W)`.
- `GateStatement` concludes: `∃ D : List (EG.Obj V)` with `EG.IsDecomp ↑F D`,
  `D.length ≤ W.card`, and every `o ∈ D` of the form `Obj.cycle c` with all its edges in
  `G.edges`. "Cycles of `G`" is therefore stated explicitly, although it also follows from
  `F ⊆ E(G)`.
- `GatePreciseStatement` concludes: `∃ cs : List (List V)` such that
  - every `c ∈ cs` is an `IsDirCycle A c` of length `≥ 3`, with `(Obj.cycle c).WF`, all of
    `cycleEdges c` in `G.edges`, and an arc of `W` in `cycleArcs c`;
  - `(cs.flatMap cycleArcs).Nodup` (the cycles are arc-disjoint);
  - `∀ a, a ∈ cs.flatMap cycleArcs ↔ a ∈ A` (their union is `F⃗`);
  - `cs.length ≤ W.card`.

  I added this second statement because HCC-P needs structural information about the cycles
  (its conclusion wants length `≥ max(3, k)`, which comes from where the cycles run), and the
  first conclusion does not provide it.

## Proof
- **Lib** (`EG.Lib.Found.Orient`):
  - `exists_dirCycle_of_balanced` finds the cycle for the first step. Hypotheses: `A` non-empty,
    no loops, no antiparallel arcs, and `d⁺ ≤ d⁻` everywhere. It finds a directed cycle with
    distinct vertices and length `≥ 3`. Since fix round 1 it is split in two steps, as in the
    manuscript. `exists_isDirCycle_of_forall_inDeg_pos` finds a directed cycle (any length) in a
    non-empty digraph where every vertex with an out-arc has an in-arc.
    `IsDirCycle.three_le_length` then excludes lengths 1 and 2.
    - The manuscript takes a maximal directed path and follows an out-arc of its last vertex.
      The formal proof runs the mirror image. It keeps a directed path `u w t…` as a list and
      takes an in-arc `x → u` of its first vertex. That in-arc exists because `u` has an out-arc
      and `d⁺ ≤ d⁻`. Either `x` is off the path, and the path extends to `x u w t…`, or `x` is on
      the path, and `u … x u` is a directed cycle.
    - Extending at the head keeps list manipulation trivial.
    - Termination uses strong induction on `|arcVerts A| - length`. Paths have no repeated
      vertex and lie in the finite set of arc ends.
    - Length `2` is excluded by `no antiparallel arcs`, and length `1` by `no loops`, exactly
      as in the manuscript (`IsDirCycle.three_le_length`).
  - `exists_dirCycle_decomp` gives the arc-disjoint union of directed cycles of length `≥ 3`. It
    uses `Finset.strongInduction` on `A`: delete the arcs of the cycle found, then apply
    `IsBalanced.sdiff_cycleArcs`. The out- and in-degrees of `cycleArcs c` are both `c.count v`.
- **Proof** (`EG.Proof.Chain.Gate`):
  - Every cycle meets `W`, because otherwise it would be a directed cycle of `A \ W`.
  - A private counting lemma (`length_le_card_of_pairwise_disjoint`) gives `cs.length ≤ |W|`. It
    is a list induction that erases the chosen `W`-arc at each step. Arc-disjointness comes from
    `List.nodup_flatMap`.
  - `gate` maps `cs` to `Obj.cycle`. The decomposition property is the Lib theorem
    `isDecomp_map_cycle_of_arcs`: the edge list is the image of the arc list under
    `a ↦ s(a.1, a.2)`, which is injective on `A` (`IsOrientation.inj`) and onto `F`.
  - `gate_with_cycles` returns both at once: `∃ cs, IsDecomp ↑F (cs.map Obj.cycle) ∧
    cs.length ≤ |W| ∧` every `c ∈ cs` is a directed cycle of `A` of length `≥ 3`, with edges in
    `E(G)` and an arc of `W`. This is the form HCC-P Step 4 needs.

## Deviations from the plan
- The plan's layer table lists "`Orientation`" under Found.Graph. The definitions went to
  `EG/Defs/Orient.lean` as the task specified. The lemmas went to `EG/Lib/Found/Orient.lean`, a
  file the task did not name. It holds general facts that MED, EQ-LPT, PAR and HCC-P will reuse,
  so it should not live under `Proof/Chain`.
- No `Ext/DirectedCycles` citation is needed. The manuscript proves the directed-cycle
  decomposition itself, and so does the formalization.

## Open questions
1. (Resolved in fix rounds 1 and 2.) `IsDirPathIn` and `walkArcs` are in `EG.Defs.Orient`
   (review 2 approved them). The cancellation lemma of HCC-P Step 1 is in Lib since fix round 2
   (`exists_cancel_dirCycles`, `exists_balanced_sdiff_acyclic`). Still to note: HCC-P's `D_j` (the
   union of the oriented paths of `𝒫_j`) is an arc set only if these paths are edge-disjoint. The
   manuscript states this ("The paths are edge-disjoint"), so HCC-P must carry it as a
   hypothesis (and uses `isOrientation_walkArcs` with `IsOrientation.union`).
2. HCC-P uses real-valued potentials (`3j + 1 + rank/(|T_j|+1)`). `isAcyclic_of_potential`
   accepts any `LinearOrder`, so `ℝ` works directly.
3. MED's "admissible orientation" is an orientation of `B_K` with balance only at hubs.
   `IsBalanced` is global. MED will need a per-vertex version: `outDeg A h = inDeg A h` for
   `h ∈ A_K` can be stated directly with the existing `outDeg` and `inDeg`. The per-vertex degree
   lemmas added in fix round 1 (`outDeg_union`, `inDeg_union`, `outDeg_sdiff`, `inDeg_sdiff`,
   `sum_outDeg_eq_card`, `sum_inDeg_eq_card`) are stated vertex by vertex for this reason.

## Fix round 1 (review `work/p1b/gate.review1.md`, verdict APPROVE)
I checked each of the seven points against the manuscript and the code. All seven are valid.
Six are fixed. The seventh asks for no change now and is recorded for HCC-P.

1. **(minor) The converse potential direction is needed downstream.** Valid: HCC-P Step 3 (s6
   line 201) and s6 line 502 use "acyclic ⇒ topological order / source". **Fixed.** Added to
   `EG.Lib.Found.Orient`:
   - `IsAcyclic.exists_source`: `IsAcyclic A → A.Nonempty → ∃ v, inDeg A v = 0 ∧ 0 < outDeg A v`;
   - `IsAcyclic.exists_potential`: for a finite `S` containing both ends of every arc, there is
     `f : V → ℕ`, injective on `S`, with `1 ≤ f v ≤ |S|` on `S`, strictly increasing along every
     arc;
   - `isAcyclic_iff_exists_potential` (ℕ-valued potentials).

   The source lemma reuses the path-extension argument, generalised to
   `exists_isDirCycle_of_forall_inDeg_pos`. It runs backwards (through in-arcs), which is the
   right direction for a source. `exists_potential` numbers a source `1` and recurses on
   `S.erase v`. Also added: `IsDirCycle.inDeg_pos` and `IsDirCycle.outDeg_pos` ("a directed
   cycle cannot pass through a source or a sink", HCC-P Step 1). The sentence in §Definitions 6
   is corrected.
2. **(minor) Combination lemmas for orientations.** Valid. **Fixed.** Added:
   - `IsOrientation.of_subset_edges`: derives `loopless` from `F ⊆ G.edges`;
   - `IsOrientation.union`: disjoint edge sets;
   - `IsOrientation.subset`: `B ⊆ A` orients `B.image (s(·.1, ·.2))`;
   - `IsOrientation.sdiff`: `A \ B` orients `F \ F'` when `B ⊆ A` orients `F'`;
   - `IsOrientation.disjoint`, `.image_eq`, `.card_eq`, `.exists_mem`, `IsOrientation.empty`;
   - `outDeg_union`, `inDeg_union`, `IsBalanced.union` (disjoint arc sets), `outDeg_mono`,
     `inDeg_mono`, `outDeg_eq_zero_iff`, `inDeg_eq_zero_iff`, `exists_mem_of_outDeg_pos`,
     `inDeg_pos_of_mem`, `sum_outDeg_eq_card`, `sum_inDeg_eq_card` (the last two are the
     handshake count of MED (b)).

   The bowtie test in `EGTest/Gate.lean` builds its orientation with `of_subset_edges` and
   `union`, then applies `gate`.
3. **(minor) Expose the decomposition behind the precise form.** Valid. **Fixed.**
   - `EG.isDecomp_map_cycle_of_arcs` (Lib) has the suggested signature:
     `IsOrientation F A → (cs.flatMap cycleArcs).Nodup → (∀ a, a ∈ cs.flatMap cycleArcs ↔
     a ∈ A) → (∀ c ∈ cs, (Obj.cycle c).WF) → IsDecomp ↑F (cs.map Obj.cycle)`.
   - `gate` now uses it.
   - `EG.gate_with_cycles` (Proof) returns the decomposition `cs.map Obj.cycle` together with
     the per-cycle directed data (directed cycle of `A`, length `≥ 3`, edges in `E(G)`, a
     `W`-arc). This is the form HCC-P Step 4 needs.
4. **(cosmetic) Directed paths.** Valid. **Fixed** in `EG.Defs.Orient`, which this task owns and
   which is not yet in `LOCK.json`.
   - Added `walkArcs` and `IsDirPathIn`, with a `Decidable` instance, exactly as suggested.
   - Added to Lib: `walkEdges_eq_map_walkArcs`, `forall_mem_walkArcs_iff_isChain`,
     `isDirPathIn_iff_isChain`, and `walkArcs` simp lemmas.
   - Tests: `EGTest/Gate.lean` has positive and negative `IsDirPathIn` examples.
   - These two definitions are new since review 1. The next review (the approval procedure for
     `EG/Defs/**`) must cover them. No existing definition changed.
5. **(cosmetic) Generic names in the root namespace.** Valid. **Fixed.**
   - `length_le_card_of_nodup` and `forall_mem_zip_of_isChain` (Lib) and
     `length_le_card_of_pairwise_disjoint` (Proof) are now `private`.
   - `flatMap_edges_map_cycle` moved to Lib as `EG.Obj.flatMap_edges_map_cycle`, with a
     docstring.
   - No other file used these names (checked with grep).
6. **(cosmetic) EGTest docstring.** Valid. **Fixed.** The docstring now reads "The acyclicity
   hypothesis of GATE has teeth: it fails on the triangle for `𝒲 = ∅`."
7. **(cosmetic) Multi-arcs.** Valid as a remark. It asks for no change now, and the representation
   is faithful. **Not an issue for GATE.** Recorded instead:
   - in the `EG.Defs.Orient` module docstring (a documentation-only change);
   - in §Definitions 8;
   - in Open question 1, as a hypothesis HCC-P must carry (its paths are edge-disjoint, which
     the manuscript states).

Unchanged: `EG.Spec.Chain.Gate` (both statements), and the existing definitions in
`EG.Defs.Orient`. `exists_dirCycle_of_balanced` and `exists_dirCycle_decomp` keep their
statements. The internal lemmas `dirCycle_or_extend` and `exists_dirCycle_aux` now take the
weaker hypothesis "out-arc ⇒ in-arc" in place of loops, antiparallel arcs and balance. Their
conclusion is `∃ c, IsDirCycle A c`, and `IsDirCycle.three_le_length` gives the length.

Checks after the fixes:
- `lake build EG.Proof.Chain.Gate`: OK.
- `scripts/check.sh EGTest/Gate.lean`: 0 errors, 0 warnings.
- `scripts/check.sh` on the Lib and Proof files: 0 errors, 0 warnings.
- `python3 scripts/lint.py`: 0 findings.
- Axiom scan over the four EG modules: 239 constants, 0 `sorryAx`, 0 violations.

## Fix round 2 (review `work/p1b/gate.review2.md`, verdict APPROVE)
I checked each point against the code and the manuscript (s6 lines 12–31 GATE, 41–87 MED,
179–218 HCC-P). All five are valid. All five are fixed. No statement (`EG.Spec.Chain.Gate`) and no
definition body in `EG.Defs.Orient` changed; the only change in `EG.Defs.Orient` is the
`IsDirPathIn` docstring.

1. **U1 (minor) No link between `outDeg`/`inDeg` and `degE`.** Valid: MED (b) ("`exc(u)` is a sum
   of `±1` over the `deg_{B_𝒦}(u)` beads at `u`", "`d⁻(h) = deg_{B_𝒦}(h)/2`") and MED (a) ("every
   hub of degree `2d` has exactly `d` in-arcs and `d` out-arcs") need it, and nothing in the API
   provided it. **Fixed.** Added
   `IsOrientation.outDeg_add_inDeg (hA : IsOrientation F A) (v : V) : outDeg A v + inDeg A v =
   degE F v`, with the suggested proof (the two filters are disjoint by `loopless`; their union
   maps injectively, by `IsOrientation.inj`, onto `edgesAt F v`). EGTest checks it on the triangle.
2. **U2 (cosmetic) Helpers for HCC-P.** Valid: each helper corresponds to a sentence of HCC-P
   Step 1 or Step 4, or to MED's "every bead is oriented exactly once". **Fixed.** Added to
   `EG.Lib.Found.Orient`:
   - `IsDirPathIn.isPathIn (hp : IsDirPathIn A p) (hF : ∀ a ∈ A, s(a.1, a.2) ∈ F) : IsPathIn F p`
     and, for cycles, `IsDirCycle.forall_mem_cycleEdges` (edges in `F`) and
     `IsDirCycle.wf_of_isOrientation` (`(Obj.cycle c).WF`). They take `hA.mem` rather than the
     whole orientation, so they also apply to sub-digraphs.
   - Rotation: `cycleArcs_rotate` (`cycleArcs (c.rotate n) = (cycleArcs c).rotate n`),
     `mem_cycleArcs_rotate`, `IsDirCycle.rotate`, `exists_rotate_eq_cons`,
     `eq_of_mem_cycleArcs_of_fst_eq` / `_snd_eq` (in a cycle without repeated vertex an arc is
     determined by its tail, or by its head), `cycleArcs_cons` (a closed walk is the walk plus its
     closing arc), and `IsDirCycle.exists_rotate_eq_cons_of_mem`: for an arc `a` of a directed
     cycle `c`, some rotation of `c` is `a.2 :: t`, its last vertex is `a.1`, its arcs are
     `walkArcs (a.2 :: t) ++ [a]`, and `a.2 :: t` is a directed path of `A`. This is HCC-P
     Step 4's "start `C` at the head of a `𝒲`-arc".
   - Orientation of a path: `isOrientation_walkArcs (hp : p.Nodup) : IsOrientation
     (walkEdges p).toFinset (walkArcs p).toFinset` (HCC-P Step 1, "Orient every path of `𝒫_j`
     from its first to its last vertex"), with `walkArcs_loopless`, `walkArcs_not_mem_swap`,
     `fst_mem_of_mem_walkArcs`, `snd_mem_of_mem_walkArcs`, `walkArcs_subset_cycleArcs`.
   - Cancellation (HCC-P Step 1, "Delete directed cycles from `D_j` one at a time until no
     directed cycle remains"): `exists_cancel_dirCycles A : ∃ cs, (∀ c ∈ cs, IsDirCycle A c) ∧
     (cs.flatMap cycleArcs).Nodup ∧ IsAcyclic (A \ (cs.flatMap cycleArcs).toFinset)`, by the
     same strong induction as `exists_dirCycle_decomp`; and the arc-set form
     `exists_balanced_sdiff_acyclic A : ∃ R ⊆ A, IsBalanced R ∧ IsAcyclic (A \ R)`. Supporting
     lemmas: `isBalanced_flatMap_cycleArcs` (arc-disjoint cycles form a balanced arc set),
     `IsBalanced.sdiff`, `IsDirCycle.mono`, and `IsBalanced.degs_eq_zero_of_source` /
     `_of_sink` (a balanced `R ⊆ A` has no arc at a source or a sink of `A`; this is how HCC-P's
     "touches no arc at a port" follows, since ports are sources or sinks of `D_j`).
   - `isOrientation_iff : IsOrientation F A ↔ (∀ a ∈ A, a.1 ≠ a.2) ∧ A.image (fun a => s(a.1,
     a.2)) = F ∧ Set.InjOn (fun a => s(a.1, a.2)) A`, the constructor without `∃!` bookkeeping.
     `isOrientation_walkArcs` uses it.

   EGTest has one example each for the path orientation, `IsDirPathIn.isPathIn`,
   `exists_rotate_eq_cons_of_mem` (the triangle started at the head of the `𝒲`-arc `0 → 1`) and
   `exists_cancel_dirCycles` (on the directed triangle the list of deleted cycles is non-empty).
3. **C1 (cosmetic) `IsDirPathIn` docstring.** Valid: `IsDirPathIn ∅ [2]` holds (EGTest now checks
   it), and [s1:convGraphs] (d) defines "path through `V`", not paths (the manuscript uses the
   standard notion without defining it). **Fixed**, documentation only: the docstring now carries
   the same Warning paragraph as `EG.IsPathIn` and cites PLAN §3 design decision 1 and the GATE
   proof's "a directed path in `F⃗` with pairwise distinct vertices" in place of
   [s1:convGraphs] (d). The definition body is unchanged.
4. **C2 (cosmetic) `arcVerts` not exposed, no membership lemma.** Valid: it was a plain `def` in a
   `public section` of a Lib module and occurs in the statement of the public
   `exists_dirCycle_aux`. **Fixed** both ways: `arcVerts` is now `@[expose]`, and
   `@[simp] mem_arcVerts : v ∈ arcVerts A ↔ ∃ a ∈ A, a.1 = v ∨ a.2 = v` is added. EGTest checks
   `arcVerts A3 = Finset.univ` by `decide` (which needs the exposed body) and uses `mem_arcVerts`.
5. **C3 (cosmetic) `exists_dirCycle_aux` has no docstring.** Valid. **Fixed**: it now has a
   docstring (the iteration of `dirCycle_or_extend`, by induction on `|arcVerts A| - length`). It
   stays public, since `arcVerts` is now usable downstream.

Checks after the fixes:
- `lake build EG.Proof.Chain.Gate`: OK (781 jobs).
- `scripts/check.sh EG/Lib/Found/Orient.lean` and `scripts/check.sh EGTest/Gate.lean`: 0 errors,
  0 warnings.
- `python3 scripts/lint.py`: 0 findings.
- Axiom scan over the four EG modules: 286 constants, 0 `sorryAx`, 0 violations.
- `EG/Lib/Found/Orient.lean` has 1087 lines (limit 1500).
