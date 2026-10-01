# P3 progress note: `EG.Todo.Lovasz` (s1:citThm21, Lovász 1968)

## Round 1 (2026-09-30)

### Proof source (found)
The proof previously listed as missing (work/p3/s1.md, "Stuck") is Lovász's own construction, as
reproduced in L. Yan, *On path decompositions of graphs*, PhD thesis, Arizona State University 1998,
Section 2.1 "Lovász construction" (pp. 7–11), and used there for "Lovász theorem, by induction on
Δ(G) = 2m − n". Copy obtained from `raw.githubusercontent.com/jayyhk/jayyhk.github.io/main/papers/yan1998.pdf`
(the only reachable host). The construction and the whole induction below were re-checked in Python
on ~10^4 random graphs (n ≤ 14, all densities, random non-optimal path-cycle decompositions for the
construction) and on K_1..K_11: every output is a valid path-cycle decomposition of the right size.

### The proof (as formalized)
**Lemma LC (Lovász construction).** Let `F` be an edge set, `x` a vertex, `Z` a set of vertices with
`x ∉ Z` and `s(x,z) ∉ F` for `z ∈ Z`. Let `(P, C)` be a path-cycle decomposition of `F` such that every
vertex of `N := Z ∪ N_F(x)` is an end of some path of `P`. Then `F ∪ {xz : z ∈ Z}` has a path-cycle
decomposition with `|P| + |C|` members.

Construction. Fix for each `v ∈ N` a designated path `des v ∈ P` ending at `v`. Let `next v` be the
vertex preceding `x` on `des v` traversed from `v` (undefined if `x ∉ des v`). Let `S` be the set of
vertices reachable from `Z` by iterating `next`. Facts: `Z ⊆ S ⊆ N`; `S` is closed under `next`;
`next v ∉ Z` (as `s(x, next v) ∈ F`); `next` is injective (the edge `s(x, next v)` determines the path
`des v`, and from its two ends one reaches the two different neighbours of `x`); every `b ∈ S \ Z`
is `next a` for some `a ∈ S`. For a path `U = P[i]` with ends `e1` (head), `e2` (last) put
`lab_k := e_k ∈ S ∧ des e_k = i`.
* `x ∈ U`: write `U = A ++ x :: B` (`x ∉ A`); output the path
  `(if lab1 then A.reverse else A) ++ x :: (if lab2 then B.reverse else B)`
  (edges: `E(U) − {x·next e_k : lab_k} + {x·e_k : lab_k}`);
* `x ∉ U`: output `x :: U` / `U ++ [x]` (one label), the cycle `U ++ [x]` (two labels), `U` (none).
Cycles of `C` are kept. Edge bookkeeping: removed edges are `{xb : b ∈ S \ Z} ⊆ F`, added edges are
`{xa : a ∈ S}`, so the union is `F ∪ xZ`, and the outputs are pairwise edge-disjoint.

**Theorem.** Strong induction on `|E(H)|` (for all vertex types of the universe at once).
* Case 0: some vertex `a` has even degree `≥ 2`. Take `x` a neighbour of `a`, `Z` = even-degree
  neighbours of `x`, `F = E(H) \ xZ` (fewer edges, same vertex set). In `F` every neighbour of `x` in
  `H` has odd degree, hence (parity, `Cor22.even_degE_add_pathEndCount`) ends a path of any
  decomposition. Induction + LC.
* Case 1: every vertex has odd degree or degree 0. If all degrees are ≤ 1, `H` is a matching (single
  edges). Otherwise take `x` of degree `≥ 3`, `y ∼ x`; restrict to the non-isolated vertices `V₀`
  (`|V₀|` even, handshake) and form `T'` on `Option V`: vertices `some V₀ ∪ {none}`, edges
  `E(H) − xy` plus the pendant edge `(none, some y)`. `T'` has `|E(H)|` edges and the even vertex
  `some x` of degree `≥ 2`, so Case 0 applies to it (its recursive call has fewer edges), giving
  `≤ (|V₀|+1)/2 = |V₀|/2` members. Delete the leaf `none` (`drop_leaf`): this gives a decomposition
  of `E(H) − xy` on `V` with at most as many members, where either `y` ends a path (then LC with
  pivot `x`, `Z = {y}`: all other neighbours of `x` are odd in `E(H) − xy`), or the pendant path was
  the single edge `(none, some y)` and one member was lost (then add the path `[x, y]`).

### Lean files (new, all sorry-free, 0 warnings)
* `EG/Lib/Ext/LovaszLists.lean` (205 l.): `pre`/`post` (split a list at `x`), `reroute`, membership in
  `walkEdges` of `x :: l`, `l ++ [x]`, `A ++ x :: B`, reverses, `cycleEdges (U ++ [x])`.
* `EG/Lib/Ext/LovaszCons.lean` (772 l.): `EG.LovaszC.lovasz_construction` (Lemma LC). Definitions
  `orient`, `nxt`, `iter`, `Reach`, `Lab₁`, `Lab₂`, `out`, `oedges`, structure `Hyp`; key lemmas
  `Hyp.nxt_inj`, `Hyp.reach_pred`, `Hyp.mem_oedges_out` (edges of one output),
  `Hyp.out_disj`, `Hyp.out_disj_cyc`, `Hyp.out_cover`, `split_perm`.
* `EG/Lib/Ext/LovaszThm.lean` (699 l.): `exists_end_of_odd` (parity), `degE_sdiff_star`, `case0`,
  `unmap`/`drop_leaf` (delete a pendant `none` on `Option V`), `add_edge_path`, `degE_erase`,
  `matching_concl`, `case1`, `concl_of_card` (strong induction on `|E|`), and
  `EG.LovaszC.lovasz : EG.Spec.LovaszStatement.{u}`.
* `EG/Proof/Todo/Lovasz.lean`: `EG.Todo.Lovasz := EG.LovaszC.lovasz` (docstring "Proved in P3.").

### Proved
`EG.Todo.Lovasz` (s1:citThm21). Consequently `EG.cor22` (`EG/Proof/Ext/Cor22.lean`) is sorry-free too.

### Remaining
None for this stub. (Note: another agent worked in parallel on a different route in
`EG/Lib/Ext/LovaszBasic.lean`, `LovaszForest.lean`, `LovaszAttach.lean`; those files are not imported
by the proof above and were not touched by this agent.)

### Checks
* `scripts/check.sh` on the three Lib files and on `EG/Proof/Todo/Lovasz.lean`: 0 errors, 0 sorry.
* `lake build EG.Proof.Todo.Lovasz EG.Proof.Ext.Cor22`: OK.
* `python3 -I scripts/lint.py`: 0 findings.
* `lake env lean --run scripts/Axioms.lean --prefix EG EG.Proof.Todo.Lovasz`: 828 constants, 0 use
  `sorryAx`, 0 violations. `#print axioms EG.Todo.Lovasz` and `EG.cor22`: `[propext,
  Classical.choice, Quot.sound]`.
