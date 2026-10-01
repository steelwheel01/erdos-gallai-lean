# P1b task [fnum]: the decomposition number f and Fact s1:factAdd (design note)

## Files and modules
- `EG/Defs/Fnum.lean` (module `EG.Defs.Fnum`, protected Defs): `EG.fnum`, `EG.fmax`.
- `EG/Lib/Found/Fnum.lean` (module `EG.Lib.Found.Fnum`): cycle-edge lemmas, `EG.Obj.map`, the
  `IsDecomp` API, [s1:factAdd] (a)–(d), optimal decompositions, `fmax` facts, stars.
- `EG/Lib/Found/FGraphFnum.lean` (module `EG.Lib.Found.FGraphFnum`, added in fix round 1):
  `fnum H.edges` for `H : FGraph V`.
- `EG/Lib/Found/FnumMain.lean` (module `EG.Lib.Found.FnumMain`, added in fix round 2):
  `EG.Spec.MainInternal ↔ f(n) = O(n)` (`mainInternal_iff_fmax`, FGraph forms).
- `EGTest/Fnum.lean` (module `EGTest.Fnum`): unit tests.
All three compile with 0 errors and 0 warnings. `scripts/lint.py`: 0 findings. Axiom scan of
`EG.Lib.Found.Fnum` (prefix EG): 0 sorryAx, 0 violations. No `sorry`.

## Definitions
- `fnum (F : Finset (Sym2 V)) : ℕ :=
   sInf {k | ∃ D : List (Obj V), IsDecomp (↑F \ Sym2.diagSet) D ∧ D.length = k}`.
  Manuscript [s1:defObject]: "f(F) is the least number of objects in a decomposition of F (so
  f(∅)=0)". No `DecidableEq V` in the definition (the value does not depend on instances).
- `fmax n := Finset.univ.sup fun H : SimpleGraph (Fin n) => fnum H.edgeFinset` (classical
  instances, only to form the finite max). Manuscript: "f(n) := max{f(H) : |V(H)| = n}".
  Justified by `fnum_le_fmax` (every graph on any `Fintype V` with `card V = n` has
  `f ≤ fmax n`) and `exists_fnum_eq_fmax` (attained on `Fin n`, for every `Fintype` instance).
- f(H) := f(E(H)) is written `fnum H.edgeFinset`; no separate definition (avoids a second
  instance-dependent constant). Bridge to the internal spec: `exists_isDecomp_edgeSet_length_eq_fnum`,
  `fnum_edgeFinset_le_iff` (`fnum G.edgeFinset ≤ k ↔ ∃ D, IsDecomp G.edgeSet D ∧ D.length ≤ k`).

## Loop convention (T0 encoding) — the one real design decision
The manuscript only takes f of loopless sets. A loop lies in no well-formed object, so a set
with a loop has no decomposition and the manuscript's minimum would be over ∅. Options:
1. `sInf` junk value 0 on looped sets: then (c) fails for looped sets, monotonicity-type facts
   need side conditions, and `f(F) ≤ k` for looped F is vacuous.
2. `ℕ∞`-valued, ⊤ on looped sets: most "honest", but (a) needs a hypothesis and all downstream
   arithmetic (bounds like f(G) ≤ c·n) becomes ENat arithmetic.
3. **Chosen: loops are ignored** — f(F) is the least number of objects decomposing the non-loop
   part `↑F \ Sym2.diagSet`. This is exactly Mathlib's convention for `SimpleGraph.fromEdgeSet`
   (`edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ Sym2.diagSet`), so fnum F = f(fromEdgeSet F).
   The infimum is always over a nonempty set (single edges), (a), (b), (c), (d) hold with no
   looplessness side conditions, and for loopless F the definition is literally the manuscript's
   (`coe_sdiff_diagSet_of_loopless`, `fnum_le_iff`, `le_fnum_iff`, `exists_isDecomp_length_eq_fnum`).
   Caveat for statement authors: for a set with loops, `fnum F ≤ k` says nothing about F's loops;
   to extract a decomposition of F itself, looplessness is required (it holds for `G.edgeFinset`,
   `loopless_edgeFinset`, and for any F with `IsDecomp ↑F D`, `loopless_of_isDecomp`).

## Formalized facts (EG/Lib/Found/Fnum.lean)
- (a) `fnum_le_card : fnum F ≤ F.card` (all F; loops ignored).
- (b) `fnum_union_le [DecidableEq V] (hd : Disjoint F₁ F₂) : fnum (F₁ ∪ F₂) ≤ fnum F₁ + fnum F₂`;
  iterated: `fnum_biUnion_le` for pairwise disjoint families (the form used in s6:lemHCCglob).
- (c) `fnum_union_eq_of_vertexDisjoint (hvd : ∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ v ∈ e₁, v ∉ e₂) :
  fnum (F₁ ∪ F₂) = fnum F₁ + fnum F₂`; graph form `fnum_edgeFinset_sup_of_disjoint_support`
  (`Disjoint H₁.support H₂.support`). Key lemma: `Obj.edges_mem_of_vertexDisjoint` (objects are
  connected), via `forall_mem_of_cycleEdges` (propagation of a vertex property around a cycle).
- (d) `fnum_map (φ : V ↪ W) : fnum (F.map φ.sym2Map) = fnum F` (relabelling / adding isolated
  vertices); `fnum_edgeFinset_map`; `fnum_edgeFinset_induce_of_support_subset` (deleting isolated
  vertices, the form used in s7:thmHI step (1)); `fmax_mono : Monotone fmax`.
- Optimal decomposition: `fnum_spec` (non-loop part, any F), `exists_isDecomp_length_eq_fnum`
  (loopless F), `fnum_le_of_isDecomp`, `fnum_le_length`, `le_fnum`, `fnum_le_iff`, `le_fnum_iff`.
- Misc: `fnum_empty`, `fnum_eq_zero_iff`, `fnum_pos_iff`, `fnum_singleton`, `fnum_cycleEdges`,
  `fnum_eq_card_of_no_cycle`, `fnum_eq_card_of_forall_mem` (stars), `fnum_filter_not_isDiag`,
  `fnum_congr_sdiff_diagSet`.
- IsDecomp API: `IsDecomp.wf/.nodup/.mem_iff/.eq_setOf/.congr/.mem_of_mem_edges/.not_isDiag`,
  `isDecomp_nil(_iff)`, `IsDecomp.eq_nil_of_empty`, `IsDecomp.append` (disjoint sets),
  `isDecomp_edge`, `isDecomp_cycle`, `isDecomp_map_edge`, `isDecomp_singletons`,
  `IsDecomp.sublist`, `IsDecomp.map` + `isDecomp_map_iff` (injective relabelling),
  `IsDecomp.length_flatMap` (= |F|), `IsDecomp.length_le_card`.
- Objects/cycles: `Obj.map` (`@[expose]`), `Obj.edges_map`, `Obj.map_map`, `Obj.map_id'`,
  `Obj.map_congr`, `Obj.wf_map_iff`, `Obj.WF.not_isDiag`, `Obj.WF.length_edges_pos`,
  `Obj.WF.nodup_edges`; `length_cycleEdges`, `getElem_cycleEdges`, `mem_cycleEdges`,
  `mk_mem_cycleEdges`, `mem_of_mem_cycleEdges`, `exists_mem_cycleEdges_of_mem`, `cycleEdges_map`,
  `not_isDiag_of_mem_cycleEdges`, `nodup_cycleEdges`.

## Tests (EGTest/Fnum.lean)
f(∅)=0 (library and directly from the definition); f(⊥ on Fin 5)=0; f(single edge)=1 (Finset and
K₂ as `⊤ : SimpleGraph (Fin 2)`); f(K₃)=1 (Finset and `⊤ : SimpleGraph (Fin 3)`); the explicit
one-object decomposition of K₃; f(star with k edges)=k for **all k** (`fnum_star`), and the
explicit 3-star; f(two disjoint triangles)=2; loop convention (f{loop}=0, f{loop, edge}=1, a set
with a loop has no decomposition); fmax 2 = 1.

## Deviations from the plan / open questions
- Plan §3 lists `fnum` in module `Found.Graph.Objects`; here it is `EG/Defs/Fnum.lean` (definition)
  plus `EG/Lib/Found/Fnum.lean` (facts), as the task specified.
- `EG/Defs/Objects.lean` (`IsDecomp`) reviewed: faithful to "partition of F into the edge sets of
  objects" (well-formed objects; `Nodup` of the concatenated edge lists gives pairwise disjointness
  and no repeated edge inside a cycle; membership gives union = F). No change needed.
- Name-collision risk: generic names in namespace `EG` (`IsDecomp.append`, `mem_cycleEdges`,
  `Obj.map`, …). If another P1b agent (Walk / Bridge) declares the same names, the integrator
  must merge them.
- Open: should statement authors write f(H) for an FGraph (plan's `EdgeSet` layer) as
  `fnum H.edges`? That works directly since `fnum` is defined on `Finset (Sym2 V)`.

## Fix round 1 (review: `work/p1b/fnum.review1.md`)

New module: `EG.Lib.Found.FGraphFnum` (`EG/Lib/Found/FGraphFnum.lean`, imports `EG.Lib.Found.Graph`
and `EG.Lib.Found.Fnum`); the orchestrator should add it to `EG.lean`. `EGTest/Fnum.lean` now also
imports it. No definition changed (`EG/Defs/Fnum.lean` untouched in this round); only lemmas added.
After the round: `scripts/check.sh` on `EG/Lib/Found/Fnum.lean`, `EG/Lib/Found/FGraphFnum.lean`,
`EGTest/Fnum.lean`: 0 errors, 0 warnings, no `sorry`; `lake build EG.Lib.Found.FGraphFnum` OK;
`scripts/lint.py`: 0 findings; axiom scan (`--no-sorry --prefix EG EG.Lib.Found.Fnum
EG.Lib.Found.FGraphFnum`): 478 constants, 0 sorryAx, 0 violations.

1. **(minor) FGraph-facing lemmas — fixed.** New file `EG/Lib/Found/FGraphFnum.lean`, namespace
   `EG.FGraph`, all using `H.loopless` (so the loop convention plays no role for `fnum H.edges`):
   - optimal decompositions: `exists_isDecomp_edges`, `fnum_edges_le_iff`, `le_fnum_edges_iff`,
     `coe_edges_sdiff_diagSet`;
   - (a) `fnum_edges_le_card_edges`; (b) `fnum_edges_le_deleteEdges_add` (`F ⊆ E(H)` ⇒
     `f(H) ≤ f(H - F) + f(F)`);
   - `fnum_edges_le_fmax : fnum H.edges ≤ fmax H.card` (via the `SimpleGraph` on `↥H.verts` and
     `fnum_map`), `fnum_edges_le_fmax_of_card_le`;
   - (c) `fnum_union_edges_of_disjoint_verts` (`Disjoint H₁.verts H₂.verts`),
     `fnum_edges_eq_add_of_disjoint_verts` (`E(H) = E(H₁) ∪ E(H₂)`), split form
     `fnum_edges_eq_induce_add_deleteVerts` (no edge leaves `A` ⇒ `f(H) = f(H[A]) + f(H - A)`);
   - (d) `deg_eq_zero_iff`, `edges_induce_of_forall_mem`, `edges_deleteVerts_of_forall_not_mem`,
     `fnum_edges_deleteVerts_of_forall_not_mem`, and the s7:thmHI step (1) form
     `fnum_edges_deleteVerts_singleton_of_deg_eq_zero` with `card_deleteVerts_singleton`
     (`|G - v| = |G| - 1`).
   There is no union operation on `FGraph` in `EG/Defs/Graph.lean`, so (c) is stated through edge
   sets (`E(H) = E(H₁) ∪ E(H₂)`, disjoint vertex sets); I did not add a definition.
2. **(minor) list-level iterated union — fixed.** In `EG/Lib/Found/Fnum.lean`, section
   `IsDecomp`/`Iterated`: `isDecomp_flatMap` (list index, `l.Pairwise (Disjoint on Es)`),
   `isDecomp_biUnion` (finset index, `(s : Set ι).PairwiseDisjoint Es`, decomposes
   `⋃ i ∈ s, Es i` by `s.toList.flatMap Ds`), `length_flatMap_toList`
   (`= ∑ i ∈ s, (Ds i).length`), `exists_isDecomp_biUnion` (tagged [s6:lemHCCglob], first
   sentence: exact decomposition into `∑ a_i` objects), `isDecomp_finset_biUnion` (finite edge sets,
   `↑(s.biUnion Fs)`). Test: the two disjoint triangles via `exists_isDecomp_biUnion`.
3. **(minor) loop caveat in AGENTS.md — valid, forwarded to the integrator (not applied by me).**
   `AGENTS.md` is the shared guide for all agents and outside this task's file scope; the reviewer
   addressed the fix to the integrator. Proposed line for AGENTS.md "Conventions":
   "- `EG.fnum F` ignores loops (`fnum F = f(F \ diagSet)`). In statements apply `fnum` only to
   loopless sets: `H.edges` for `H : FGraph V` (lemmas in `EG.Lib.Found.FGraphFnum`),
   `G.edgeFinset`, or add the hypothesis `∀ e ∈ F, ¬ e.IsDiag`."
   The caveat is already in the docstring of `EG/Defs/Fnum.lean`, and the new FGraph lemmas remove
   the need for statement authors to deal with loops.
4. **(cosmetic) duplicate helpers in `EGCheck/BridgeLemmas.lean` / `EG/Proof/Chain/Gate.lean` —
   not an issue for this task (other agents' files, outside my scope).** Checked: `BridgeLemmas`
   lives in `EGCheck.Bridge` (`objMap`, `length_cycleEdges`, `cycleEdges_map`, `wf_objMap`), and
   `Gate.lean` declares `EG.length_le_card_of_pairwise_disjoint`, `EG.flatMap_edges_map_cycle`,
   which do not clash with any name in `EG.Lib.Found.Fnum` / `EG.Lib.Found.FGraphFnum` (grep over
   `EG`, `EGTest`, `EGCheck`, `staging` for every new name: no duplicate). Dedupe is left to the
   integrator (import `EG.Lib.Found.Fnum` and use `EG.Obj.map`, `EG.length_cycleEdges`,
   `EG.cycleEdges_map`, `EG.Obj.wf_map_iff`).
5. **(cosmetic) f(K₄) = 3 test — fixed.** Added to `EGTest/Fnum.lean` (`two_triangles_K4`,
   `obj_cases_fin4`, `fnum_K4`), adapted from the reviewer's scratch proof; lower bound by `decide`
   on `Fin 4` (plain `decide`, no native evaluation).
6. **(cosmetic) finset form of `IsDecomp.map` — fixed.** `coe_map_sym2Map`,
   `IsDecomp.map_finset : IsDecomp ↑F D → IsDecomp ↑(F.map φ.sym2Map) (D.map (Obj.map φ))`, and
   `isDecomp_map_finset_iff`, in `EG/Lib/Found/Fnum.lean` (section `Map`).

Additional tests (EGTest/Fnum.lean): `FGraph` example `triPlus` (triangle plus an isolated vertex):
f = 1, deleting the isolated vertex keeps f and lowers |H| by one, `1 ≤ fmax 4` via
`fnum_edges_le_fmax`, optimal decomposition via `fnum_edges_le_iff`.

## Fix round 2 (review: `work/p1b/fnum.review2.md`, verdict "approve")

New module: `EG.Lib.Found.FnumMain` (`EG/Lib/Found/FnumMain.lean`, imports `EG.Spec.Main` and
`EG.Lib.Found.FGraphFnum`); the orchestrator should add it to `EG.lean`. `EGTest/Fnum.lean` now
also imports it. No definition changed. After the round: `lake build EG.Lib.Found.FnumMain` OK
(builds `EG.Defs.Fnum`, `EG.Lib.Found.Fnum`, `EG.Lib.Found.FGraphFnum`); `scripts/check.sh` on
`EG/Defs/Fnum.lean`, `EG/Lib/Found/Fnum.lean`, `EG/Lib/Found/FGraphFnum.lean`,
`EG/Lib/Found/FnumMain.lean`, `EGTest/Fnum.lean`: 0 errors, 0 warnings, no `sorry`;
`scripts/lint.py`: 0 findings; axiom scan (`--no-sorry --prefix EG EG.Defs.Fnum EG.Lib.Found.Fnum
EG.Lib.Found.FGraphFnum EG.Lib.Found.FnumMain`): 527 constants, 0 sorryAx, 0 violations.
Name-collision grep of every new name over `EG`, `EGTest`, `EGCheck`, `staging`: no clash.

1. **(minor) loop caveat in AGENTS.md — valid; AGENTS.md is outside my file scope, forwarded to
   the integrator again; mitigated within scope.** Checked the reviewer's example: `fnum {s(0,0)} ≤ 0`
   holds and `{s(0,0)}` has no decomposition (now a test in `EGTest/Fnum.lean`). v6 Fact EG0(b)
   ("every edge of F has both ends in W …") is indeed false for a raw F with a loop `s(w, w)`,
   `w ∈ W`, if read as `IsDecomp ↑F D`, and too weak if read as `fnum F ≤ k`; its statement needs
   `∀ e ∈ F, ¬ e.IsDiag` (or F = `H.edges`). Changes in my scope:
   - `EG/Defs/Fnum.lean`: **comment-only** addition to the module docstring, paragraph "Caveat for
     statement authors" (the example above, the three safe usages, and the EG0(b) advice). The
     definitions `fnum`, `fmax` and their docstrings are unchanged (`git diff`: 7 comment lines
     added in the `/-! … -/` block).
   - `EGTest/Fnum.lean`: the caveat example (`fnum {s(0,0)} ≤ 0 ∧ ¬ ∃ D, IsDecomp {s(0,0)} D`).
   Line for the integrator to add to AGENTS.md "Conventions" (unchanged proposal):
   "- `EG.fnum F` ignores loops (`fnum F = f(F \ diagSet)`). In statements apply `fnum` only to
   loopless sets: `H.edges` for `H : FGraph V` (lemmas in `EG.Lib.Found.FGraphFnum`),
   `G.edgeFinset`, or add the hypothesis `∀ e ∈ F, ¬ e.IsDiag`. State 'F decomposes' for a raw F
   (e.g. Fact EG0(b)) with `IsDecomp` plus that hypothesis."
2. **(cosmetic) `mainInternal_iff_fmax` — fixed.** New file `EG/Lib/Found/FnumMain.lean`:
   - `mainInternal_iff_fmax : EG.Spec.MainInternal ↔ ∃ c : ℕ, ∀ n, fmax n ≤ c * n`
     ([s7:thmMainProof], last step);
   - FGraph forms: `mainInternal_of_fnum_edges_le (c) (h : ∀ n (H : FGraph (Fin n)),
     fnum H.edges ≤ c * H.card) : MainInternal` (via `FGraph.ofSimpleGraph`, the s7:thmHI endgame
     form; hypothesis only on `Fin n`), `fnum_edges_le_of_mainInternal : MainInternal →
     ∃ c, ∀ (V : Type u) (H : FGraph V), fnum H.edges ≤ c * H.card` (any universe), and
     `mainInternal_iff_fnum_edges` (the iff, any universe `u`; `←` transports along
     `Fin n ↪ ULift (Fin n)` with `fnum_map`).
   Tests: the two forms agree; under `MainInternal`, `1 ≤ c * 4` from `triPlus`; the unconditional
   trivial bound `fmax n ≤ n * n` (`fmax_le_sq`) for contrast.
3. **(cosmetic) `Obj.isEdge` and countP API — fixed** (in `EG/Lib/Found/Fnum.lean`, my file, next
   to `IsDecomp.append` / `isDecomp_flatMap`; nothing in `EG/Defs/Objects.lean` changed):
   - `@[expose] def Obj.isEdge : Obj V → Bool` (tag [s1:defObject]), `isEdge_edge`, `isEdge_cycle`,
     `isEdge_iff`, `isEdge_eq_false_iff`, `isEdge_map`, `length_edges_of_isEdge`;
   - `countP_isEdge_append`, `countP_isEdge_cons`, `countP_isEdge_map` (relabelling),
     `countP_isEdge_map_edge` (= length), `countP_isEdge_map_cycle` (= 0),
     `countP_isEdge_singletons` (= |F|), `length_eq_countP_isEdge_add` (edges + cycles),
     `countP_isEdge_le_length`, `IsDecomp.countP_isEdge_le_card`, `countP_isEdge_flatMap`,
     `countP_isEdge_flatMap_toList` (= Σ), `exists_isDecomp_biUnion_countP` (s6:lemHCCglob first
     sentence with single edges counted).
   Note for the integrator: `Obj.isEdge` is a Lib definition. If a locked Spec statement (e.g.
   Fact EG0 "at most h − 1 of which are single edges") needs it, it should move to
   `EG/Defs/Objects.lean` (two-line definition; the lemmas stay in Lib). Tests: countP of the K₄
   decomposition (= 2), of the star decomposition (= k), under relabelling, and of the
   two-triangle union (= 0).
4. **(cosmetic) tag of `exists_isDecomp_biUnion` — fixed.** Its docstring now says that it is
   only the first sentence of s6:lemHCCglob, placed in the s1 layer as [s1:factAdd](b) iterated,
   that the s6 formalization should cite it (and `isDecomp_biUnion`,
   `countP_isEdge_flatMap_toList`) rather than re-prove it, and that the second paragraph of
   s6:lemHCCglob (systems of s6:lemHCCP) belongs to the s6 files.
